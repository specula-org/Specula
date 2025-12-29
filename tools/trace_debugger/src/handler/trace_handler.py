import os
import logging
import time
import json
from ..client.dap_client import DAPClient
from ..executor.tlc_process import TLCExecutor

logger = logging.getLogger(__name__)

class TraceDebugger:
    """
    High-level controller for TLA+ Trace Debugging.
    Designed for automated interaction by AI Agents.
    """
    def __init__(self, tla_jar, community_jar=None, port=4712):
        self.port = port
        self.executor = TLCExecutor(tla_jar, community_jar)
        self.client = DAPClient(port=port)
        self.is_debugging = False

    def start(self, spec_file, config_file, trace_file, cwd=None):
        """Starts TLC process and establishes DAP connection."""
        try:
            self.executor.start(spec_file, config_file, trace_file, cwd, self.port)
            if not self.client.connect():
                return False

            # 1. Initialize session
            self.client.request("initialize", {"adapterID": "tlc"})

            # 2. Enable essential filters for trace validation
            self.client.request("setExceptionBreakpoints", {
                "filters": [],
                "filterOptions": [
                    {"filterId": "UnsatisfiedBreakpointsFilter", "condition": "TRUE"},
                    {"filterId": "InvariantBreakpointsFilter", "condition": "TRUE"}
                ]
            })

            # 3. Consume the initial "session ready" stopped event
            # TLC sends this after setExceptionBreakpoints
            while True:
                msg = self.client.receive()
                if msg and msg.get("type") == "event" and msg.get("event") == "stopped":
                    logger.info("Consumed initial stop event (session ready)")
                    break

            self.is_debugging = True
            return True
        except Exception as e:
            logger.error(f"TraceDebugger start error: {e}")
            self.stop()
            return False

    def stop(self):
        """Cleanly shuts down the debugger session and TLC process."""
        self.client.disconnect()
        self.executor.stop()
        self.is_debugging = False

    def add_breakpoint(self, file_path, line, condition=None):
        """Adds a source breakpoint with optional TLA+ condition."""
        abs_path = os.path.abspath(file_path)
        name = os.path.basename(abs_path)
        bp = {"line": line}
        if condition: bp["condition"] = condition
            
        args = {
            "source": {"name": name, "path": abs_path},
            "breakpoints": [bp]
        }
        resp = self.client.request("setBreakpoints", args)
        return resp and resp.get("success", False)

    def continue_execution(self):
        """Resumes TLC execution."""
        self.client.request("configurationDone", {})
        self.client.send("request", "continue", {"threadId": 0})

    def step_in(self):
        """Steps into the next expression or sub-action."""
        self.client.send("request", "stepIn", {"threadId": 0})

    def wait_for_stop(self, timeout=60):
        """
        Blocks until TLC stops at a breakpoint or exception.
        Returns the stopped event message.
        """
        start_time = time.time()

        while time.time() - start_time < timeout:
            msg = self.client.receive()
            if not msg: continue

            if msg.get("type") == "event" and msg.get("event") == "stopped":
                reason = msg.get("body", {}).get("reason", "")
                logger.info(f"Execution halted. Reason: '{reason}' (empty is normal for breakpoints)")
                return msg

            elif msg.get("type") == "event" and msg.get("event") == "terminated":
                logger.info("TLC execution terminated.")
                return None
        return None

    def get_stack_frame(self):
        """Retrieves the current execution location."""
        # Small settle time to ensure TLC has populated the stack
        time.sleep(0.3)
        resp = self.client.request("stackTrace", {"threadId": 0})
        if resp and resp.get("success"):
            frames = resp["body"].get("stackFrames", [])
            if frames: return frames[0]
        return None

    def get_variables(self, frame_id=None):
        """
        Retrieves all variables from all available scopes.
        Returns a flattened dictionary of variables.
        """
        if not frame_id:
            frame = self.get_stack_frame()
            if not frame: return {}
            frame_id = frame["id"]

        all_vars = {}
        scope_resp = self.client.request("scopes", {"frameId": frame_id})
        if scope_resp and scope_resp.get("success"):
            for scope in scope_resp["body"]["scopes"]:
                vref = scope["variablesReference"]
                if vref > 0:
                    var_resp = self.client.request("variables", {"variablesReference": vref})
                    if var_resp and var_resp.get("success"):
                        for v in var_resp["body"]["variables"]:
                            # We store name -> value
                            all_vars[v["name"]] = v["value"]
        return all_vars

    def evaluate(self, expression, frame_id=None):
        """Evaluates a TLA+ expression in the current context."""
        if not frame_id:
            frame = self.get_stack_frame()
            if not frame: return None
            frame_id = frame["id"]

        resp = self.client.request("evaluate", {
            "expression": expression,
            "frameId": frame_id
        })
        return resp.get("body", {}).get("result") if resp and resp.get("success") else None