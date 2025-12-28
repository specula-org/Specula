import subprocess
import time
import sys
import socket
import json
import os

# --- DAP Client ---
class DebugClient:
    def __init__(self, port=4712):
        self.port = port
        self.sock = None
        self.seq = 1

    def connect(self):
        start = time.time()
        print("Connecting to TLC debugger...")
        while time.time() - start < 30:
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.connect(('127.0.0.1', self.port))
                return True
            except ConnectionRefusedError:
                print(".", end="", flush=True)
                time.sleep(1.0)
        print("")
        return False

    def send(self, type_, command=None, args=None):
        msg = {"seq": self.seq, "type": type_}
        if command: msg["command"] = command
        if args: msg["arguments"] = args
        body = json.dumps(msg)
        full = f"Content-Length: {len(body)}\r\n\r\n{body}"
        self.sock.sendall(full.encode('utf-8'))
        self.seq += 1
        return self.seq - 1

    def receive(self):
        try:
            head = b""
            while b"\r\n\r\n" not in head:
                chunk = self.sock.recv(1)
                if not chunk: return None
                head += chunk
            content_len = int(head.decode().split("Content-Length: ")[1].strip())
            body = b""
            while len(body) < content_len:
                chunk = self.sock.recv(content_len - len(body))
                if not chunk: return None
                body += chunk
            return json.loads(body)
        except Exception as e:
            print(f"Receive error: {e}")
            return None

    def request(self, command, args=None):
        req_seq = self.send("request", command, args)
        while True:
            msg = self.receive()
            if not msg: return None
            if msg.get("type") == "response" and msg.get("request_seq") == req_seq:
                return msg
            # Handle events if needed, but for simple request-response, just skip

# --- Main Logic ---
def run_phase2():
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    
    # Paths from user's command
    tla_jar = "/home/ubuntu/specula/lib/tla2tools.jar"
    community_jar = "/home/ubuntu/specula/lib/CommunityModules-deps.jar"
    classpath = f"{tla_jar}:{community_jar}"
    
    spec_file = "Traceetcdraft_progress.tla"
    cfg_file = "Traceetcdraft_progress.cfg"
    
    # Environment variables
    env = os.environ.copy()
    env["JSON"] = "../traces/confchange_disable_validation.ndjson"
    
    # Breakpoint Config
    # Stopping at 29 because 30 is where failure likely occurs (based on user input l=29)
    bp_line = 518  # TraceNext ==
    bp_cond = 'TLCGet("level") = 29'
    
    print(f">>> Starting TLC Debugger for {spec_file}...")
    cmd = [
        "java", 
        "-XX:+UseParallelGC", "-Xmx4G",
        "-cp", classpath,
        "tlc2.TLC",
        "-debugger", "port=4712",
        "-config", cfg_file,
        spec_file
    ]
    
    import threading

    def read_stdout(pipe):
        for line in iter(pipe.readline, ''):
            # print(f"[TLC] {line.strip()}") # Optional: print to see progress
            pass
        pipe.close()

    proc = subprocess.Popen(
        cmd,
        cwd=work_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=env
    )

    client = DebugClient()
    
    try:
        # 1. Wait for Debugger Ready (Main thread does this initial wait)
        print("Waiting for TLC stdout...")
        while True:
            line = proc.stdout.readline()
            if not line:
                print("TLC stdout closed prematurely.")
                break
            # print(f"[TLC] {line.strip()}")
            if "Debugger is listening" in line:
                print(">>> TLC Debugger is ready!")
                break
        
        # Start background thread to drain stdout
        t = threading.Thread(target=read_stdout, args=(proc.stdout,))
        t.daemon = True
        t.start()
        
        # 2. Connect & Init
        if not client.connect():
            print("❌ Connection failed")
            return

        client.request("initialize", {"adapterID": "tlc"})
        
        # 3. Set Breakpoints
        print(f">>> Setting Breakpoints and Filters...")
        # Unsatisfied Breakpoint (The most important one for capturing the failure)
        client.request("setExceptionBreakpoints", {
            "filters": [],
            "filterOptions": [
                {"filterId": "UnsatisfiedBreakpointsFilter", "condition": "TRUE"}
            ]
        })

        # Source Breakpoint as a trigger (TraceNext entry)
        bp_line = 522 
        # Additional breakpoints for "Carpet Bombing" strategy inside TraceNextReceiveActions
        # Based on grep, TraceNextReceiveActions is at 512. Let's cover 513-516
        inner_bps = [513, 514, 515, 516]
        
        all_bps = [{"line": bp_line, "condition": bp_cond}]
        for line in inner_bps:
            all_bps.append({"line": line}) # Unconditional breakpoints for inner actions

        client.request("setBreakpoints", {
            "source": {"name": spec_file, "path": os.path.join(work_dir, spec_file)},
            "breakpoints": all_bps
        })
        
        client.request("configurationDone", {})
        client.request("continue", {})
        
        # 4. Monitor Loop
        print(">>> Running... Waiting for breakpoint hit...")
        
        step_count = 0
        max_steps = 15 # Limit step-ins to avoid infinite loops if stuck
        
        while True:
            msg = client.receive()
            if msg is None:
                print(">>> Connection closed by TLC.")
                break
            
            # DEBUG: Print every event
            if msg.get("type") == "event":
                evt = msg.get("event")
                # print(f"  [Event] {evt}") 
                
                if evt == "stopped":
                    reason = msg["body"]["reason"]
                    print(f"\n✅ STOPPED! Reason: {reason}")
                    
                    # Get Stack Trace
                    stack_resp = client.request("stackTrace", {"threadId": 0})
                    frames = stack_resp["body"]["stackFrames"]
                    
                    if frames:
                        top_frame = frames[0]
                        frame_id = top_frame["id"]
                        print(f"   📍 At: {top_frame['source']['name']}:{top_frame['line']}")
                        
                        # --- INSPECT VARIABLES AT EACH STEP ---
                        # This proves we can see local variables/parameters inside the action
                        scopes_resp = client.request("scopes", {"frameId": frame_id})
                        if scopes_resp and 'body' in scopes_resp:
                            for scope in scopes_resp["body"]["scopes"]:
                                # We are interested in Locals (often scope #1 or named 'Locals')
                                # But let's print everything non-empty to see what we get
                                vref = scope["variablesReference"]
                                if vref > 0:
                                    vars_resp = client.request("variables", {"variablesReference": vref})
                                    if vars_resp and 'body' in vars_resp:
                                        vars_list = vars_resp["body"]["variables"]
                                        if vars_list:
                                            # Print only the first few to avoid spamming, or specific interesting ones
                                            print(f"      [Scope: {scope['name']}]")
                                            for v in vars_list[:5]: # Limit to 5 for brevity
                                                print(f"         {v['name']} = {v['value']}")
                        # --------------------------------------

                        if step_count < max_steps:
                            print(f">>> 🦶 Stepping In (Step {step_count + 1}/{max_steps})...")
                            client.request("stepIn", {"threadId": 0})
                            step_count += 1
                            # Loop back to wait for next stopped event
                            continue 
                        else:
                            print(">>> Reached max steps. Stopping.")
                            # Inspect variables at the final point
                            # ... (Variable inspection code can go here if needed) ...
                            client.request("disconnect", {})
                            break
                    
                elif evt == "terminated":
                    print("❌ TERMINATED without stopping.")
                    break

    except Exception as e:
        print(f"Error: {e}")
    finally:
        if client.sock: client.sock.close()
        proc.terminate()

if __name__ == "__main__":
    run_phase2()