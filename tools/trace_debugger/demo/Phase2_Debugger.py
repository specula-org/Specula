import subprocess
import time
import sys
import socket
import json
import os
import threading

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

# --- Main Logic ---
def run_phase2():
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    tla_jar = "/home/ubuntu/specula/lib/tla2tools.jar"
    community_jar = "/home/ubuntu/specula/lib/CommunityModules-deps.jar"
    classpath = f"{tla_jar}:{community_jar}"
    spec_file = "Traceetcdraft_progress.tla"
    cfg_file = "Traceetcdraft_progress.cfg"
    
    # Environment variables
    env = os.environ.copy()
    env["JSON"] = "../traces/confchange_disable_validation.ndjson"
    
    # Breakpoint Config
    bp_line = 522  # TraceNext line
    bp_cond = 'TLCGet("level") = 29'
    
    print(f">>> Starting TLC Debugger for {spec_file}...")
    cmd = [
        "java", "-XX:+UseParallelGC", "-Xmx4G",
        "-cp", classpath,
        "tlc2.TLC",
        "-debugger", "port=4712",
        "-config", cfg_file,
        spec_file
    ]
    
    proc = subprocess.Popen(
        cmd,
        cwd=work_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=env
    )

    def read_stdout(pipe):
        for line in iter(pipe.readline, ''):
            pass # Drain
        pipe.close()

    client = DebugClient()
    
    try:
        # 1. Wait for Debugger Ready
        print("Waiting for TLC stdout...")
        while True:
            line = proc.stdout.readline()
            if not line: break
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
        print(f">>> Setting Breakpoint at {spec_file}:{bp_line} with condition '{bp_cond}'...")
        client.request("setBreakpoints", {
            "source": {"name": spec_file, "path": os.path.join(work_dir, spec_file)},
            "breakpoints": [{"line": bp_line, "condition": bp_cond}]
        })
        
        client.request("configurationDone", {})
        client.request("continue", {})
        
        # 4. Monitor Loop
        print(">>> Running... Waiting for breakpoint hit...")
        step_count = 0
        max_steps = 15
        
        while True:
            msg = client.receive()
            if msg is None: break
            
            if msg.get("type") == "event":
                evt = msg.get("event")
                if evt == "stopped":
                    print(f"\n✅ STOPPED! Reason: {msg['body'].get('reason')}")
                    
                    # Inspect State
                    stack_resp = client.request("stackTrace", {"threadId": 0})
                    if not stack_resp or "body" not in stack_resp:
                        continue
                    frames = stack_resp["body"]["stackFrames"]
                    if frames:
                        top_frame = frames[0]
                        frame_id = top_frame["id"]
                        print(f"   At: {top_frame['source']['name']}:{top_frame['line']}")
                        
                        # Inspect Variables
                        scopes_resp = client.request("scopes", {"frameId": frame_id})
                        if scopes_resp and "body" in scopes_resp:
                            for scope in scopes_resp["body"]["scopes"]:
                                vref = scope["variablesReference"]
                                if vref > 0:
                                    vars_resp = client.request("variables", {"variablesReference": vref})
                                    if vars_resp and "body" in vars_resp:
                                        print(f"\n--- Scope '{scope['name']}' ---")
                                        for v in vars_resp["body"]["variables"][:10]:
                                            print(f"   {v['name']} = {v['value']}")
                        
                        if step_count < max_steps:
                            print(f">>> 🦶 Stepping In ({step_count+1})...")
                            client.request("stepIn", {"threadId": 0})
                            step_count += 1
                            continue
                    
                    client.request("disconnect", {})
                    break
                elif evt == "terminated":
                    print("❌ TERMINATED")
                    break
    except Exception as e:
        print(f"Error during execution: {e}")
    finally:
        if client.sock: client.sock.close()
        proc.terminate()

if __name__ == "__main__":
    run_phase2()