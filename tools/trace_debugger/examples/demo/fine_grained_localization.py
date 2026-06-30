import json
import os
import socket
import subprocess
import threading
import time


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
                self.sock.connect(("127.0.0.1", self.port))
                return True
            except ConnectionRefusedError:
                print(".", end="", flush=True)
                time.sleep(1.0)
        print("")
        return False

    def send(self, type_, command=None, args=None):
        msg = {"seq": self.seq, "type": type_}
        if command:
            msg["command"] = command
        if args:
            msg["arguments"] = args
        body = json.dumps(msg)
        full = f"Content-Length: {len(body)}\r\n\r\n{body}"
        self.sock.sendall(full.encode("utf-8"))
        self.seq += 1
        return self.seq - 1

    def receive(self):
        try:
            head = b""
            while b"\r\n\r\n" not in head:
                chunk = self.sock.recv(1)
                if not chunk:
                    return None
                head += chunk
            content_len = int(head.decode().split("Content-Length: ")[1].strip())
            body = b""
            while len(body) < content_len:
                chunk = self.sock.recv(content_len - len(body))
                if not chunk:
                    return None
                body += chunk
            return json.loads(body)
        except Exception as e:
            print(f"Receive error: {e}")
            return None

    def request(self, command, args=None):
        req_seq = self.send("request", command, args)
        while True:
            msg = self.receive()
            if not msg:
                return None
            if msg.get("type") == "response" and msg.get("request_seq") == req_seq:
                return msg


def get_specula_root():
    """Auto-detect Specula root directory."""
    # Try environment variable first
    specula_root = os.environ.get("SPECULA_ROOT")
    if specula_root:
        return specula_root
    # Calculate relative to this file: tools/trace_debugger/examples/demo/xxx.py
    # Go up to specula root: ../../../../
    this_file = os.path.abspath(__file__)
    demo_dir = os.path.dirname(this_file)  # .../demo
    examples_dir = os.path.dirname(demo_dir)  # .../examples
    trace_debugger_dir = os.path.dirname(examples_dir)  # .../trace_debugger
    tools_dir = os.path.dirname(trace_debugger_dir)  # .../tools
    return os.path.dirname(tools_dir)  # .../Specula


def run_inspection():
    specula_root = get_specula_root()
    work_dir = os.path.join(specula_root, "data/workloads/etcdraft/scenarios/progress_inflights/spec")
    tla_jar = os.path.join(specula_root, "lib/tla2tools.jar")
    community_jar = os.path.join(specula_root, "lib/CommunityModules-deps.jar")
    classpath = f"{tla_jar}:{community_jar}"
    spec_file = "Traceetcdraft_progress.tla"
    cfg_file = "Traceetcdraft_progress.cfg"

    # 注意：AppendEntriesInRangeToPeer 在 etcdraft_progress.tla，不是 Traceetcdraft_progress.tla
    spec_file_base = "etcdraft_progress.tla"

    env = os.environ.copy()
    env["JSON"] = "../traces/confchange_disable_validation.ndjson"

    print("=" * 70)
    print("PHASE 4: Deep Dive into AppendEntries")
    print("=" * 70)

    cmd = [
        "java",
        "-XX:+UseParallelGC",
        "-Xmx4G",
        "-cp",
        classpath,
        "tlc2.TLC",
        "-debugger",
        "port=4712",
        "-config",
        cfg_file,
        spec_file,
    ]

    proc = subprocess.Popen(cmd, cwd=work_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)

    def read_stdout(pipe):
        for line in iter(pipe.readline, ""):
            pass
        pipe.close()

    client = DebugClient()

    try:
        # Wait for TLC ready
        print("\n>>> Waiting for TLC...")
        while True:
            line = proc.stdout.readline()
            if not line:
                break
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

        # 在 AppendEntriesInRangeToPeer 内部打多个断点
        spec_path_trace = os.path.join(work_dir, spec_file)
        spec_path_base = os.path.join(work_dir, spec_file_base)

        # 定义断点位置（在 etcdraft_progress.tla 中）
        breakpoints_def = [
            # AppendEntriesIfLogged 相关
            (spec_file, 323, "AppendEntriesIfLogged entry"),
            (spec_file, 327, "AppendEntries call"),
            # AppendEntries 函数（在 etcdraft_progress.tla 的 Line 516）
            (spec_file_base, 517, "AppendEntriesInRangeToPeer call"),
            # AppendEntriesInRangeToPeer 内部关键点
            (spec_file_base, 435, "AppendEntriesInRangeToPeer entry"),
            (spec_file_base, 436, "Condition: i /= j"),
            (spec_file_base, 437, "Condition: range[1] <= range[2]"),
            (spec_file_base, 438, "Condition: state[i] = Leader"),
            (spec_file_base, 439, "Condition: j in Config U Outgoing U Learners"),
            (spec_file_base, 443, "Condition: heartbeat or ~IsPaused"),
            (spec_file_base, 444, "LET block start"),
            (spec_file_base, 474, "Send operation"),
            (spec_file_base, 489, "inflights update branch"),
            (spec_file_base, 493, "msgAppFlowPaused update"),
            (spec_file_base, 496, "nextIndex update"),
        ]

        print("\n>>> Setting Breakpoints (all with condition: l = 29):")

        # 按文件分组设置断点
        breakpoints_by_file = {}
        for file, line, desc in breakpoints_def:
            if file not in breakpoints_by_file:
                breakpoints_by_file[file] = []
            breakpoints_by_file[file].append({"line": line, "condition": "l = 29"})
            print(f"    {file:30s} Line {line:3d}: {desc}")

        # 设置每个文件的断点
        for file, breakpoints in breakpoints_by_file.items():
            path = spec_path_trace if file == spec_file else spec_path_base
            client.request("setBreakpoints", {"source": {"name": file, "path": path}, "breakpoints": breakpoints})

        client.request("configurationDone", {})
        client.request("continue", {})

        print("\n>>> Running... Waiting for breakpoints to hit...")
        print("=" * 70)

        hit_count = 0
        max_hits = 50  # 增加限制，看更多断点
        hits_summary = {}

        while hit_count < max_hits:
            msg = client.receive()
            if msg is None:
                print("\n❌ Connection lost")
                break

            if msg.get("type") == "event":
                evt = msg.get("event")

                if evt == "stopped":
                    hit_count += 1

                    # Get current location
                    stack_resp = client.request("stackTrace", {"threadId": 0})
                    if stack_resp and "body" in stack_resp:
                        frames = stack_resp["body"]["stackFrames"]
                        if frames:
                            frame = frames[0]
                            line = frame["line"]
                            source = frame.get("source", {}).get("name", "unknown")

                            # Find breakpoint description
                            desc = "unknown"
                            for bp_file, bp_line, bp_desc in breakpoints_def:
                                if bp_line == line and bp_file == source:
                                    desc = bp_desc
                                    break

                            # Track hits
                            key = f"{source}:{line}"
                            hits_summary[key] = hits_summary.get(key, 0) + 1

                            print(f"Hit #{hit_count:3d}: {source:30s} Line {line:3d} - {desc}")

                    # Continue
                    client.request("continue", {})

                elif evt == "terminated":
                    print(f"\n>>> TLC Terminated after {hit_count} breakpoint hits")
                    break

        print("\n" + "=" * 70)
        print(f"SUMMARY: Hit {hit_count} breakpoint(s)")
        print("=" * 70)

        print("\nBreakpoint Hit Summary:")
        for bp_file, bp_line, bp_desc in breakpoints_def:
            key = f"{bp_file}:{bp_line}"
            count = hits_summary.get(key, 0)
            status = "✅" if count > 0 else "❌"
            print(f"  {status} {bp_file:30s} Line {bp_line:3d}: {count:3d} hits - {bp_desc}")

        print("\n💡 分析：")
        print("  - 被命中的行：条件满足，代码执行到了")
        print("  - 未命中的行：代码从未执行到，说明前面某个条件失败了")

        client.request("disconnect", {})

    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback

        traceback.print_exc()
    finally:
        if client.sock:
            client.sock.close()
        proc.terminate()


if __name__ == "__main__":
    run_inspection()
