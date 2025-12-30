import socket
import json
import time
import logging
from collections import deque

logger = logging.getLogger(__name__)

class DAPClient:
    """
    High-performance DAP client with an internal event queue.
    Ensures no events are lost while waiting for responses.
    """
    def __init__(self, host='127.0.0.1', port=4712, timeout=30):
        self.host = host
        self.port = port
        self.timeout = timeout
        self.sock = None
        self.seq = 1
        self.connected = False
        self._buffer = b""
        self.event_queue = deque()
        self.pending_responses = {}

    def connect(self):
        start_time = time.time()
        while time.time() - start_time < self.timeout:
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.connect((self.host, self.port))
                self.connected = True
                return True
            except ConnectionRefusedError:
                time.sleep(0.5)
        return False

    def disconnect(self):
        if self.sock: self.sock.close()
        self.connected = False

    def send(self, type_, command=None, args=None):
        msg = {"seq": self.seq, "type": type_}
        if command: msg["command"] = command
        if args: msg["arguments"] = args
        body = json.dumps(msg)
        full = f"Content-Length: {len(body)}\r\n\r\n{body}"
        self.sock.sendall(full.encode('utf-8'))
        self.seq += 1
        return self.seq - 1

    def _read_once(self, timeout=None):
        """Reads one message and dispatches it to the appropriate queue."""
        if not self.connected: return None
        if timeout: self.sock.settimeout(timeout)
        else: self.sock.settimeout(None)

        try:
            while b"\r\n\r\n" not in self._buffer:
                chunk = self.sock.recv(4096)
                if not chunk: return None
                self._buffer += chunk
            
            header_part, self._buffer = self._buffer.split(b"\r\n\r\n", 1)
            content_length = 0
            for line in header_part.decode('utf-8').split("\r\n"):
                if line.startswith("Content-Length:"):
                    content_length = int(line.split(":")[1].strip())
            
            while len(self._buffer) < content_length:
                chunk = self.sock.recv(4096)
                if not chunk: return None
                self._buffer += chunk
            
            body = self._buffer[:content_length]
            self._buffer = self._buffer[content_length:]
            msg = json.loads(body.decode('utf-8'))
            
            if msg.get("type") == "event":
                self.event_queue.append(msg)
                # Heartbeat for UI
                if msg.get("event") == "output":
                    print(".", end="", flush=True)
            elif msg.get("type") == "response":
                self.pending_responses[msg.get("request_seq")] = msg
            
            return msg
        except socket.timeout:
            return None
        except Exception as e:
            self.connected = False
            return None

    def request(self, command, args=None):
        """Synchronous request that processes events while waiting."""
        req_seq = self.send("request", command, args)
        start_time = time.time()
        while time.time() - start_time < 10: # 10s timeout per request
            if req_seq in self.pending_responses:
                return self.pending_responses.pop(req_seq)
            self._read_once(timeout=0.1)
        return None

    def get_event(self):
        """Non-blocking pop from event queue."""
        if self.event_queue:
            return self.event_queue.popleft()
        self._read_once(timeout=0.1)
        return self.event_queue.popleft() if self.event_queue else None
