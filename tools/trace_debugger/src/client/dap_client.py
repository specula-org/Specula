import socket
import json
import time
import threading
import logging

logger = logging.getLogger(__name__)

class DAPClient:
    """
    A low-level client for the Debug Adapter Protocol (DAP).
    Handles socket communication, message framing, and request/response correlation.
    """
    def __init__(self, host='127.0.0.1', port=4712, timeout=30):
        self.host = host
        self.port = port
        self.timeout = timeout
        self.sock = None
        self.seq = 1
        self.connected = False
        self._buffer = b""
        self._lock = threading.Lock()

    def connect(self):
        """Attempts to connect to the DAP server with retries."""
        start_time = time.time()
        logger.info(f"Connecting to DAP server at {self.host}:{self.port}...")
        
        while time.time() - start_time < self.timeout:
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.settimeout(5.0) # Socket-level timeout
                self.sock.connect((self.host, self.port))
                self.connected = True
                logger.info("Connected to DAP server.")
                return True
            except (ConnectionRefusedError, socket.timeout):
                time.sleep(0.5)
            except Exception as e:
                logger.error(f"Connection error: {e}")
                time.sleep(0.5)
        
        logger.error("Failed to connect to DAP server within timeout.")
        return False

    def disconnect(self):
        """Closes the connection."""
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
        self.connected = False
        self.sock = None
        logger.info("Disconnected from DAP server.")

    def send_request(self, command, args=None):
        """Sends a DAP request and returns the sequence number."""
        if not self.connected:
            raise RuntimeError("Client not connected")

        with self._lock:
            seq = self.seq
            self.seq += 1

        msg = {
            "seq": seq,
            "type": "request",
            "command": command
        }
        if args:
            msg["arguments"] = args

        self._send_message(msg)
        return seq

    def _send_message(self, msg_dict):
        """Encodes and sends a message dictionary."""
        body = json.dumps(msg_dict)
        content = f"Content-Length: {len(body)}\r\n\r\n{body}"
        try:
            self.sock.sendall(content.encode('utf-8'))
            # logger.debug(f"--> SENT: {msg_dict.get('command') or msg_dict.get('type')}")
        except Exception as e:
            logger.error(f"Send error: {e}")
            self.connected = False
            raise

    def receive_message(self, timeout=None):
        """
        Reads the next complete message from the socket.
        Returns a dict or None if connection closed/timed out.
        """
        if not self.connected:
            return None

        # Temporarily adjust timeout if needed
        # Note: In a real async loop, we wouldn't block like this, 
        # but for this script, blocking read is fine.
        if timeout:
            self.sock.settimeout(timeout)
        else:
            self.sock.settimeout(None)

        try:
            # 1. Read Headers
            while b"\r\n\r\n" not in self._buffer:
                chunk = self.sock.recv(4096)
                if not chunk:
                    self.connected = False
                    return None
                self._buffer += chunk

            header_part, self._buffer = self._buffer.split(b"\r\n\r\n", 1)
            content_length = 0
            
            headers = header_part.decode('utf-8').split('\r\n')
            for h in headers:
                if h.startswith("Content-Length:"):
                    content_length = int(h.split(':')[1].strip())

            # 2. Read Body
            while len(self._buffer) < content_length:
                chunk = self.sock.recv(4096)
                if not chunk:
                    self.connected = False
                    return None
                self._buffer += chunk

            body_part = self._buffer[:content_length]
            self._buffer = self._buffer[content_length:]

            msg = json.loads(body_part.decode('utf-8'))
            # logger.debug(f"<-- RECV: {msg.get('type')} {msg.get('command') or msg.get('event') or ''}")
            return msg

        except socket.timeout:
            return None
        except Exception as e:
            logger.error(f"Receive error: {e}")
            self.connected = False
            return None
