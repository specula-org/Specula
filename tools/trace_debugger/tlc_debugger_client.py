#!/usr/bin/env python3
"""
Minimal TLC Debugger Client for Trace Validation
Based on Debug Adapter Protocol (DAP)

This is a "hack" - we only implement what we need to capture unsatisfied breakpoints.
"""
import socket
import json
import sys
import time
from typing import Dict, Any, Optional

class TLCDebuggerClient:
    def __init__(self, port=4712):
        self.port = port
        self.sock: Optional[socket.socket] = None
        self.seq = 1
        self.verbose = True

    def log(self, msg: str):
        if self.verbose:
            print(f"[CLIENT] {msg}", file=sys.stderr)

    def connect(self, timeout=10):
        """Connect to TLC debugger"""
        self.log(f"Connecting to localhost:{self.port}...")

        start_time = time.time()
        while time.time() - start_time < timeout:
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.connect(('127.0.0.1', self.port))
                self.log("✓ Connected")
                return True
            except ConnectionRefusedError:
                self.sock = None
                time.sleep(0.5)

        self.log("✗ Connection failed")
        return False

    def send_message(self, msg_type: str, command: str = None, arguments: Dict = None) -> int:
        """Send a DAP message"""
        msg = {
            "seq": self.seq,
            "type": msg_type,
        }

        if command:
            msg["command"] = command
        if arguments:
            msg["arguments"] = arguments

        request_seq = self.seq
        self.seq += 1

        # Serialize to JSON
        body = json.dumps(msg)

        # Create DAP header
        header = f"Content-Length: {len(body)}\r\n\r\n"

        # Send
        full_msg = header.encode('utf-8') + body.encode('utf-8')
        self.sock.sendall(full_msg)

        if command:
            self.log(f"→ {command}")
        else:
            self.log(f"→ {msg_type}")

        return request_seq

    def receive_message(self, timeout=None) -> Optional[Dict[str, Any]]:
        """Receive a DAP message"""
        if timeout:
            self.sock.settimeout(timeout)

        try:
            # Read headers
            headers = {}
            buf = b""

            while True:
                char = self.sock.recv(1)
                if not char:
                    return None

                buf += char

                if buf.endswith(b"\r\n\r\n"):
                    # End of headers
                    header_text = buf[:-4].decode('utf-8')
                    for line in header_text.split("\r\n"):
                        if ": " in line:
                            key, value = line.split(": ", 1)
                            headers[key] = value
                    break

            # Read body
            content_length = int(headers.get("Content-Length", 0))
            body = b""

            while len(body) < content_length:
                chunk = self.sock.recv(content_length - len(body))
                if not chunk:
                    return None
                body += chunk

            # Parse JSON
            msg = json.loads(body.decode('utf-8'))

            msg_type = msg.get("type")
            if msg_type == "event":
                event = msg.get("event")
                self.log(f"← event: {event}")
            elif msg_type == "response":
                cmd = msg.get("command")
                success = msg.get("success", False)
                self.log(f"← response: {cmd} ({'✓' if success else '✗'})")
            else:
                self.log(f"← {msg_type}")

            return msg

        except socket.timeout:
            return None
        finally:
            if timeout:
                self.sock.settimeout(None)

    def wait_for_response(self, request_seq: int, timeout=30) -> Optional[Dict]:
        """Wait for response to a specific request"""
        start_time = time.time()

        while time.time() - start_time < timeout:
            msg = self.receive_message(timeout=1.0)
            if not msg:
                continue

            if msg.get("type") == "response" and msg.get("request_seq") == request_seq:
                return msg

            # Handle events while waiting
            if msg.get("type") == "event":
                self.handle_event(msg)

        self.log(f"✗ Timeout waiting for response to seq={request_seq}")
        return None

    def handle_event(self, msg: Dict):
        """Handle events (can be overridden)"""
        pass

    def initialize(self) -> bool:
        """Initialize the debug session"""
        self.log("\n=== Initialize ===")

        seq = self.send_message("request", "initialize", {
            "clientID": "tlc-trace-validator",
            "clientName": "TLC Trace Validator",
            "adapterID": "tlc",
            "locale": "en-US",
            "linesStartAt1": True,
            "columnsStartAt1": True,
            "pathFormat": "path",
            "supportsVariableType": True,
            "supportsVariablePaging": False,
            "supportsRunInTerminalRequest": False
        })

        resp = self.wait_for_response(seq)
        if not resp or not resp.get("success"):
            self.log("✗ Initialize failed")
            return False

        # Wait for initialized event
        self.log("Waiting for 'initialized' event...")
        start_time = time.time()
        while time.time() - start_time < 5:
            msg = self.receive_message(timeout=1.0)
            if msg and msg.get("type") == "event" and msg.get("event") == "initialized":
                self.log("✓ Received 'initialized' event")
                return True

        self.log("✓ Initialize complete (no 'initialized' event)")
        return True

    def set_exception_breakpoints(self, filters=None, filter_options=None) -> bool:
        """Set exception breakpoints

        IMPORTANT: TLC Debugger ignores the 'filters' field and only reads 'filterOptions'.
        This method automatically converts filters to filterOptions format.
        """
        self.log("\n=== Set Exception Breakpoints ===")

        # TLC Debugger bug/quirk: it ignores 'filters' and only reads 'filterOptions'
        # So we need to convert filters to filterOptions
        final_filter_options = filter_options or []
        if filters and not final_filter_options:
            for f in filters:
                final_filter_options.append({"filterId": f, "condition": "TRUE"})

        args = {
            "filters": filters or [],
            "filterOptions": final_filter_options
        }

        seq = self.send_message("request", "setExceptionBreakpoints", args)
        resp = self.wait_for_response(seq)

        if not resp or not resp.get("success"):
            self.log("✗ setExceptionBreakpoints failed")
            return False

        self.log("✓ Exception breakpoints set")
        return True

    def configuration_done(self) -> bool:
        """Signal that configuration is complete"""
        self.log("\n=== Configuration Done ===")

        seq = self.send_message("request", "configurationDone", {})
        resp = self.wait_for_response(seq)

        if not resp or not resp.get("success"):
            self.log("✗ configurationDone failed")
            return False

        self.log("✓ Configuration complete")
        return True

    def continue_execution(self, thread_id=0) -> bool:
        """Continue execution"""
        self.log("\n=== Continue ===")

        seq = self.send_message("request", "continue", {"threadId": thread_id})
        resp = self.wait_for_response(seq)

        if not resp or not resp.get("success"):
            self.log("✗ continue failed")
            return False

        self.log("✓ Continuing execution")
        return True

    def get_stack_trace(self, thread_id=0, levels=10) -> Optional[list]:
        """Get stack trace"""
        seq = self.send_message("request", "stackTrace", {
            "threadId": thread_id,
            "startFrame": 0,
            "levels": levels
        })

        resp = self.wait_for_response(seq)
        if not resp or not resp.get("success"):
            return None

        return resp.get("body", {}).get("stackFrames", [])

    def close(self):
        """Close connection"""
        if self.sock:
            self.sock.close()
            self.log("\n✓ Disconnected")


def test_connection():
    """Test basic connection to TLC debugger"""
    client = TLCDebuggerClient()

    try:
        # Connect
        if not client.connect():
            print("Failed to connect to TLC debugger")
            print("Make sure TLC is running with: -debugger port=4712")
            return False

        # Initialize
        if not client.initialize():
            print("Failed to initialize")
            return False

        # Set unsatisfied breakpoint
        if not client.set_exception_breakpoints(
            filters=[],
            filter_options=[
                {
                    "filterId": "UnsatisfiedBreakpointsFilter",
                    "condition": "TRUE"
                }
            ]
        ):
            print("Failed to set breakpoints")
            return False

        # Configuration done
        if not client.configuration_done():
            print("Failed to complete configuration")
            return False

        # Continue execution
        if not client.continue_execution():
            print("Failed to continue")
            return False

        # Wait for events
        print("\n=== Listening for events ===")
        stop_count = 0

        while stop_count < 5:  # Capture first 5 stops
            msg = client.receive_message(timeout=30.0)

            if not msg:
                print("Timeout or connection closed")
                break

            if msg.get("type") == "event":
                event = msg.get("event")

                if event == "stopped":
                    stop_count += 1
                    body = msg.get("body", {})
                    reason = body.get("reason", "unknown")
                    text = body.get("text", "")

                    print(f"\n🔴 STOPPED #{stop_count}: {reason}")
                    if text:
                        print(f"   Details: {text}")

                    # Get stack trace
                    frames = client.get_stack_trace()
                    if frames:
                        frame = frames[0]
                        source = frame.get("source", {})
                        print(f"   📍 {source.get('name', '?')}:{frame.get('line', '?')}:{frame.get('column', '?')}")
                        print(f"   📝 {frame.get('name', '?')}")

                    # Continue
                    client.continue_execution()

                elif event == "terminated":
                    print("\n✓ TLC terminated")
                    break

                elif event == "output":
                    output = msg.get("body", {}).get("output", "")
                    if "Progress" in output:
                        print(f"   {output.strip()}")

        print(f"\n✓ Test complete - captured {stop_count} stops")
        return True

    except Exception as e:
        print(f"\n✗ Error: {e}")
        import traceback
        traceback.print_exc()
        return False

    finally:
        client.close()


if __name__ == "__main__":
    success = test_connection()
    sys.exit(0 if success else 1)
