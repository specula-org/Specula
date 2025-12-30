import subprocess, time, socket, json, os, threading

class DebugClient:
    def __init__(self, port=4712):
        self.port, self.sock, self.seq = port, None, 1
    def connect(self):
        start = time.time()
        while time.time() - start < 30:
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.connect(('127.0.0.1', self.port))
                return True
            except ConnectionRefusedError:
                time.sleep(1.0)
        return False
    def send(self, type_, command=None, args=None):
        msg = {"seq": self.seq, "type": type_}
        if command: msg["command"] = command
        if args: msg["arguments"] = args
        body = json.dumps(msg)
        self.sock.sendall(f"Content-Length: {len(body)}\r\n\r\n{body}".encode('utf-8'))
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
        except: return None
    def request(self, command, args=None):
        req_seq = self.send("request", command, args)
        while True:
            msg = self.receive()
            if not msg: return None
            if msg.get("type") == "response" and msg.get("request_seq") == req_seq:
                return msg

def evaluate_expression(client, frame_id, expr):
    resp = client.request("evaluate", {"expression": expr, "frameId": frame_id, "context": "watch"})
    if resp and resp.get("success"):
        return resp["body"].get("result")
    return None

def get_variable_value(client, frame_id, var_name):
    scopes_resp = client.request("scopes", {"frameId": frame_id})
    if scopes_resp and "body" in scopes_resp:
        for scope in scopes_resp["body"]["scopes"]:
            vref = scope["variablesReference"]
            if vref > 0:
                vars_resp = client.request("variables", {"variablesReference": vref})
                if vars_resp and "body" in vars_resp:
                    for v in vars_resp["body"]["variables"]:
                        if v["name"] == var_name:
                            return v["value"]
    return None

work_dir = "/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec"
env = os.environ.copy()
env["JSON"] = "../traces/confchange_disable_validation.ndjson"

print("检查 Line 438 处，i 和 j 的值，以及 Line 439 条件是否满足...")

proc = subprocess.Popen([
    "java", "-XX:+UseParallelGC", "-Xmx4G",
    "-cp", f"{work_dir}/../../../../../../lib/tla2tools.jar:{work_dir}/../../../../../../lib/CommunityModules-deps.jar",
    "tlc2.TLC", "-debugger", "port=4712",
    "-config", "Traceetcdraft_progress.cfg", "Traceetcdraft_progress.tla"
], cwd=work_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)

def read_stdout(pipe):
    for line in iter(pipe.readline, ''): pass
    pipe.close()

client = DebugClient()

try:
    while True:
        line = proc.stdout.readline()
        if not line or "Debugger is listening" in line: break
    
    t = threading.Thread(target=read_stdout, args=(proc.stdout,))
    t.daemon = True
    t.start()
    
    if not client.connect():
        print("Connection failed")
        exit(1)
    
    client.request("initialize", {"adapterID": "tlc"})
    spec_path = os.path.join(work_dir, "etcdraft_progress.tla")
    
    # 断点在 Line 438（state[i] = Leader 检查通过后）
    client.request("setBreakpoints", {
        "source": {"name": "etcdraft_progress.tla", "path": spec_path},
        "breakpoints": [{"line": 438, "condition": "l = 29"}]
    })
    
    client.request("configurationDone", {})
    client.request("continue", {})
    
    checked_combinations = set()
    hit_count = 0
    
    print("\n检查所有在 Line 438 的 (i, j) 组合：\n")
    
    while hit_count < 20:  # Check first 20 hits
        msg = client.receive()
        if msg is None: break
        if msg.get("type") == "event" and msg.get("event") == "stopped":
            hit_count += 1
            
            stack_resp = client.request("stackTrace", {"threadId": 0})
            if not stack_resp or "body" not in stack_resp:
                client.request("continue", {})
                continue
            
            frames = stack_resp["body"]["stackFrames"]
            if not frames:
                client.request("continue", {})
                continue
            
            frame_id = frames[0]["id"]
            
            i_val = get_variable_value(client, frame_id, "i")
            j_val = get_variable_value(client, frame_id, "j")
            
            if (i_val, j_val) not in checked_combinations:
                checked_combinations.add((i_val, j_val))
                
                # Check Line 439 condition
                j_in_set_expr = f'"{j_val}" \\in GetConfig("{i_val}") \\union GetOutgoingConfig("{i_val}") \\union GetLearners("{i_val}")'
                j_in_set = evaluate_expression(client, frame_id, j_in_set_expr)
                
                status = "✅" if j_in_set == "TRUE" else "❌"
                print(f"  {status} i={i_val}, j={j_val}: Line 439 condition = {j_in_set}")
                
                if j_in_set != "TRUE":
                    # 查看具体的集合
                    get_config = evaluate_expression(client, frame_id, f'GetConfig("{i_val}")')
                    get_outgoing = evaluate_expression(client, frame_id, f'GetOutgoingConfig("{i_val}")')
                    get_learners = evaluate_expression(client, frame_id, f'GetLearners("{i_val}")')
                    union = evaluate_expression(client, frame_id, f'GetConfig("{i_val}") \\union GetOutgoingConfig("{i_val}") \\union GetLearners("{i_val}")')
                    
                    print(f"       GetConfig({i_val}) = {get_config}")
                    print(f"       GetOutgoingConfig({i_val}) = {get_outgoing}")
                    print(f"       GetLearners({i_val}) = {get_learners}")
                    print(f"       Union = {union}")
                    print(f"       j={j_val} not in Union!")
            
            client.request("continue", {})
    
    print(f"\n检查了 {len(checked_combinations)} 个不同的 (i, j) 组合")
    
    client.request("disconnect", {})

except Exception as e:
    print(f"Error: {e}")
    import traceback
    traceback.print_exc()
finally:
    if client.sock: client.sock.close()
    proc.terminate()
