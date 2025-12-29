import subprocess
import threading
import os
import logging

logger = logging.getLogger(__name__)

class TLCExecutor:
    """
    Manages the TLC subprocess.
    Handles startup, environment setup, and stdout monitoring.
    """
    def __init__(self, tla_jar_path=None, community_jar_path=None):
        self.process = None
        self.stdout_thread = None
        self.tla_jar_path = tla_jar_path
        self.community_jar_path = community_jar_path
        self.is_ready = False

    def start(self, spec_file, config_file, trace_file=None, cwd=None, port=4712):
        """Starts TLC in debugger mode."""
        if not self.tla_jar_path or not os.path.exists(self.tla_jar_path):
            raise FileNotFoundError(f"tla2tools.jar not found at {self.tla_jar_path}")

        # Setup Classpath
        classpath = self.tla_jar_path
        if self.community_jar_path and os.path.exists(self.community_jar_path):
            classpath += f":{self.community_jar_path}"

        # Setup Env (for Trace Validation)
        env = os.environ.copy()
        if trace_file:
            env["JSON"] = trace_file

        cmd = [
            "java",
            "-XX:+UseParallelGC", "-Xmx4G",
            "-cp", classpath,
            "tlc2.TLC",
            "-debugger", f"port={port}",
            "-config", config_file,
            spec_file
        ]

        logger.info(f"Starting TLC in {cwd or '.'}...")
        
        self.process = subprocess.Popen(
            cmd,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=env
        )

        # Monitor stdout for "Debugger is listening"
        self._wait_for_debugger_ready()
        
        # Start draining stdout to prevent blocking
        self.stdout_thread = threading.Thread(target=self._drain_stdout, args=(self.process.stdout,))
        self.stdout_thread.daemon = True
        self.stdout_thread.start()

    def _wait_for_debugger_ready(self):
        """Reads stdout line by line until debugger is ready."""
        while True:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError("TLC process exited prematurely")
            
            if "Debugger is listening" in line:
                logger.info("TLC Debugger is listening.")
                self.is_ready = True
                break

    def _drain_stdout(self, pipe):
        """Continuously reads stdout to prevent buffer filling."""
        for line in iter(pipe.readline, ''):
            # In a real tool, we might want to route this to a log file or a callback
            pass
        pipe.close()

    def stop(self):
        """Terminates the process."""
        if self.process:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()
            self.process = None