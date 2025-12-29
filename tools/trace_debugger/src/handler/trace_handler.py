import os
import logging
import time
from collections import deque
from ..client.dap_client import DAPClient
from ..executor.tlc_process import TLCExecutor

logger = logging.getLogger(__name__)

class TraceDebugger:
    """
    High-level controller for TLA+ Trace Debugging.
    """
    def __init__(self, port=4712):
        self.port = port
        self.executor = TLCExecutor()
        self.client = DAPClient(port=port)
        self.is_debugging = False
        
        # State Management
        self.event_queue = deque()
        self.pending_responses = {}
        self.breakpoints = {} # Key: file_path, Value: List[dict]

    def start(self, spec_file, config_file, trace_file, cwd=None):
        """Starts the debugging session."""
        try:
            # 1. Start Process
            self.executor.start(spec_file, config_file, trace_file, cwd, self.port)
            
            # 2. Connect Client
            if not self.client.connect():
                raise RuntimeError("Failed to connect to TLC Debugger")
            
            # 3. Initialize Protocol
            init_seq = self.client.send_request("initialize", {"adapterID": "tlc"})
            self._wait_for_response(init_seq)
            
            # 4. Default Configuration (Enable Unsatisfied Breakpoints)
            # Note: TLC's DAP implementation might not send a response for this specific request 
            # if not strictly compliant, but we should try to wait.
            config_seq = self.client.send_request("setExceptionBreakpoints", {
                "filters": [],
                "filterOptions": [
                    {"filterId": "UnsatisfiedBreakpointsFilter", "condition": "TRUE"},
                    {"filterId": "InvariantBreakpointsFilter", "condition": "TRUE"}
                ]
            })
            # Wait with a short timeout and ignore failure/timeout for this specific request
            self._wait_for_response(config_seq, timeout=2.0)
            
            self.is_debugging = True
            logger.info("Trace Debugger started successfully.")
            return True
        except Exception as e:
            logger.error(f"Failed to start debugger: {e}")
            self.stop()
            return False

    def stop(self):
        """Stops the session."""
        try:
            self.client.disconnect()
        except:
            pass
        self.executor.stop()
        self.is_debugging = False

    def add_breakpoint(self, file_path, line, condition=None):
        """Adds a breakpoint, preserving existing ones for the file."""
        if file_path not in self.breakpoints:
            self.breakpoints[file_path] = []
            
        bp = {"line": line}
        if condition:
            bp["condition"] = condition
            
        # Avoid duplicates
        if bp not in self.breakpoints[file_path]:
            self.breakpoints[file_path].append(bp)
            
        args = {
            "source": {"name": os.path.basename(file_path), "path": file_path},
            "breakpoints": self.breakpoints[file_path]
        }
        
        req_seq = self.client.send_request("setBreakpoints", args)
        resp = self._wait_for_response(req_seq)
        return resp and resp.get("success", False)

    def continue_execution(self):
        """Continues execution."""
        # configurationDone is usually sent once after initial setup, but safe to send.
        cd_seq = self.client.send_request("configurationDone", {})
        self._wait_for_response(cd_seq)
        
        cont_seq = self.client.send_request("continue", {"threadId": 0})
        resp = self._wait_for_response(cont_seq)
        return resp and resp.get("success", False)

    def step_in(self):
        """Performs a step-in operation."""
        step_seq = self.client.send_request("stepIn", {"threadId": 0})
        resp = self._wait_for_response(step_seq)
        return resp and resp.get("success", False)

    def _read_and_dispatch(self, timeout=0.1):
        """Reads a message from the client and dispatches it to events or responses."""
        msg = self.client.receive_message(timeout=timeout)
        if not msg:
            return None
            
        mtype = msg.get("type")
        if mtype == "event":
            self.event_queue.append(msg)
        elif mtype == "response":
            req_seq = msg.get("request_seq")
            if req_seq:
                self.pending_responses[req_seq] = msg
        return msg

    def _wait_for_response(self, request_seq, timeout=10):
        """Waits for a specific response sequence, buffering events."""
        start = time.time()
        while time.time() - start < timeout:
            if request_seq in self.pending_responses:
                return self.pending_responses.pop(request_seq)
            
            # Read wire
            self._read_and_dispatch(timeout=0.1)
            
        logger.error(f"Timeout waiting for response to request {request_seq}")
        return None

    def wait_for_stop(self, timeout=60):
        """Waits for a 'stopped' event in the queue or from the wire."""
        start = time.time()
        while time.time() - start < timeout:
            # Check queue first
            for i, msg in enumerate(self.event_queue):
                if msg.get("event") == "stopped":
                    # Remove this event and return it. 
                    # Note: modifying list while iterating is bad, but we return immediately.
                    del self.event_queue[i]
                    return msg
                if msg.get("event") == "terminated":
                    logger.info("TLC terminated.")
                    del self.event_queue[i]
                    return None
            
            # Read wire
            msg = self._read_and_dispatch(timeout=0.5)
            if not msg and not self.client.connected:
                # Connection closed
                return None
                
        return None

    def get_stack_frame(self):
        """Gets the top stack frame."""
        resp_id = self.client.send_request("stackTrace", {"threadId": 0})
        resp = self._wait_for_response(resp_id)
        if resp and resp.get("success"):
            frames = resp["body"]["stackFrames"]
            if frames:
                return frames[0]
        return None

    def get_variables(self, frame_id=None):
        """Retrieves all variables from all scopes for the given frame."""
        if not frame_id:
            frame = self.get_stack_frame()
            if not frame: return {}
            frame_id = frame["id"]

        variables = {}
        
        # 1. Get Scopes
        scope_req = self.client.send_request("scopes", {"frameId": frame_id})
        scope_resp = self._wait_for_response(scope_req)
        
        if scope_resp and scope_resp.get("success"):
            for scope in scope_resp["body"]["scopes"]:
                scope_name = scope["name"]
                vref = scope["variablesReference"]
                if vref > 0:
                    # 2. Get Variables for Scope
                    var_req = self.client.send_request("variables", {"variablesReference": vref})
                    var_resp = self._wait_for_response(var_req)
                    if var_resp and var_resp.get("success"):
                        scope_vars = {}
                        for v in var_resp["body"]["variables"]:
                            scope_vars[v["name"]] = v["value"]
                        variables[scope_name] = scope_vars
        
        return variables

    def evaluate(self, expression, frame_id=None):
        """Evaluates an expression."""
        if not frame_id:
            frame = self.get_stack_frame()
            if not frame: return None
            frame_id = frame["id"]

        req_id = self.client.send_request("evaluate", {
            "expression": expression,
            "frameId": frame_id
        })
        resp = self._wait_for_response(req_id)
        if resp and resp.get("success"):
            return resp.get("body", {}).get("result")
        return None