import subprocess
import time
import socket
import json
import os
import threading

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

def run_breakpoint_experiment():
    work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
    tla_jar = "/home/ubuntu/specula/lib/tla2tools.jar"
    community_jar = "/home/ubuntu/specula/lib/CommunityModules-deps.jar"
    classpath = f"{tla_jar}:{community_jar}"
    spec_file = "Traceetcdraft_progress.tla"
    cfg_file = "Traceetcdraft_progress.cfg"

    env = os.environ.copy()
    env["JSON"] = "../traces/confchange_disable_validation.ndjson"

    print("="*70)
    print("PHASE 3: Multi-Breakpoint Diagnosis")
    print("Goal: Find where SendAppendEntriesRequest fails at l=29")
    print("="*70)

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
            pass
        pipe.close()

    client = DebugClient()

    try:
        # Wait for TLC ready
        print("\n>>> Waiting for TLC...")
        while True:
            line = proc.stdout.readline()
            if not line: break
            if "Debugger is listening" in line:
                print(">>> TLC Ready!")
                break

        t = threading.Thread(target=read_stdout, args=(proc.stdout,))
        t.daemon = True
        t.start()

        if not client.connect():
            print("❌ Connection failed")
            return

        client.request("initialize", {"adapterID": "tlc"})

        # Define breakpoints with l=29 condition
        spec_path = os.path.join(work_dir, spec_file)
        breakpoints_def = [
            (522, "TraceNext entry (main branch)"),
            (489, "SendAppendEntriesRequest MsgApp branch"),
            (323, "AppendEntriesIfLogged entry"),
            (327, "AppendEntries call"),
            (328, "ValidateAfterAppendEntries call"),
            (510, "StepToNextTrace (exit)"),
        ]

        print("\n>>> Setting Breakpoints (all with condition: l = 29):")
        breakpoints = []
        for line, desc in breakpoints_def:
            breakpoints.append({"line": line, "condition": "l = 29"})
            print(f"    Line {line:3d}: {desc}")

        client.request("setBreakpoints", {
            "source": {"name": spec_file, "path": spec_path},
            "breakpoints": breakpoints
        })

        client.request("configurationDone", {})
        client.request("continue", {})

        print("\n>>> Running... Waiting for breakpoints to hit...")
        print("="*70)

        hit_count = 0
        max_hits = 20  # Limit to avoid infinite loops

        while hit_count < max_hits:
            msg = client.receive()
            if msg is None:
                print("\n❌ Connection lost")
                break

            if msg.get("type") == "event":
                evt = msg.get("event")

                if evt == "stopped":
                    hit_count += 1
                    reason = msg.get("body", {}).get("reason", "")

                    # Get current location
                    stack_resp = client.request("stackTrace", {"threadId": 0})
                    if stack_resp and "body" in stack_resp:
                        frames = stack_resp["body"]["stackFrames"]
                        if frames:
                            frame = frames[0]
                            line = frame["line"]

                            # Find breakpoint description
                            desc = "unknown"
                            for bp_line, bp_desc in breakpoints_def:
                                if bp_line == line:
                                    desc = bp_desc
                                    break

                            print(f"\n✅ Hit #{hit_count}: Line {line:3d} - {desc}")
                            print(f"   Reason: {reason}")

                            # Continue to next breakpoint
                            if hit_count < max_hits:
                                print("   Continuing to next breakpoint...")
                                client.request("continue", {})

                elif evt == "terminated":
                    print(f"\n❌ TERMINATED after {hit_count} breakpoint hits")
                    break

        print("\n" + "="*70)
        print(f"SUMMARY: Hit {hit_count} breakpoint(s)")

        if hit_count == 0:
            print("\n⚠️  No breakpoints hit! This means:")
            print("   - Either l never reached 29 (unlikely)")
            print("   - Or the execution path didn't go through these lines")
        elif hit_count < len(breakpoints_def):
            print(f"\n⚠️  Only {hit_count}/{len(breakpoints_def)} breakpoints hit")
            print("   The execution stopped before reaching later breakpoints")
            print("   This tells us WHERE the failure occurred!")

        print("="*70)

        client.request("disconnect", {})

    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
    finally:
        if client.sock: client.sock.close()
        proc.terminate()

if __name__ == "__main__":
    run_breakpoint_experiment()
