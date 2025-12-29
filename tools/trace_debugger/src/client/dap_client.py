import socket
import json
import time
import logging

logger = logging.getLogger(__name__)

class DAPClient:
    """
    A simple, robust DAP client based on the successful Phase2 implementation.
    Uses blocking receive to ensure synchronous message handling.
    """
    def __init__(self, host='127.0.0.1', port=4712, timeout=30):
        self.host = host
        self.port = port
        self.timeout = timeout
        self.sock = None
        self.seq = 1
        self.connected = False

    def connect(self):
        start_time = time.time()
        logger.info(f"Connecting to DAP server at {self.host}:{self.port}...")
        while time.time() - start_time < self.timeout:
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.connect((self.host, self.port))
                self.connected = True
                logger.info("Connected to DAP server.")
                return True
            except ConnectionRefusedError:
                time.sleep(0.5)
        return False

    def disconnect(self):
        if self.sock:
            self.sock.close()
        self.connected = False
        self.sock = None

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
        """Blocking receive of a single message."""
        try:
            head = b""
            while b"\r\n\r\n" not in head:
                chunk = self.sock.recv(1)
                if not chunk: return None
                head += chunk
            
            content_len_str = head.decode('utf-8').split("Content-Length: ")[1].split("\r\n")[0]
            content_len = int(content_len_str.strip())
            
            body = b""
            while len(body) < content_len:
                chunk = self.sock.recv(content_len - len(body))
                if not chunk: return None
                body += chunk
            
            msg = json.loads(body.decode('utf-8'))
            logger.info(f"<-- [DAP] {msg.get('type')} {msg.get('command') or msg.get('event') or ''}")
            return msg
        except Exception as e:
            logger.error(f"Receive error: {e}")
            return None

    def request(self, command, args=None):
        """Sends a request and blocks until the matching response is received."""
        req_seq = self.send("request", command, args)
        while True:
            msg = self.receive()
            if not msg: return None
            if msg.get("type") == "response" and msg.get("request_seq") == req_seq:
                return msg
            # Note: Events are ignored here but will be handled by the caller's main loop
            # if they call receive() directly.

