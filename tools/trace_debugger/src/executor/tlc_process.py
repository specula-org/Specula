import subprocess
import threading
import os
import time
import logging

logger = logging.getLogger(__name__)

class TLCExecutor:
    """
    Manages the TLC subprocess.
    Handles startup, environment setup, and stdout monitoring.
    """
    def __init__(self, tla_jar_path=None):
        self.process = None
        self.stdout_thread = None
        self.tla_jar_path = tla_jar_path or self._find_tla_jar()
        self.is_ready = False

    def _find_tla_jar(self):
        # Default locations to check
        candidates = [
            "/home/ubuntu/specula/lib/tla2tools.jar",
            "../../../../lib/tla2tools.jar",
            "tla2tools.jar"
        ]
        for c in candidates:
            if os.path.exists(c):
                return os.path.abspath(c)
        return None

    def start(self, spec_file, config_file, trace_file=None, cwd=None, port=4712):
        """Starts TLC in debugger mode."""
        if not self.tla_jar_path:
            raise FileNotFoundError("tla2tools.jar not found")

        # Setup Classpath
        # Note: Assuming CommunityModules-deps.jar is in the same dir as tla2tools.jar or standard lib
        lib_dir = os.path.dirname(self.tla_jar_path)
        community_jar = os.path.join(lib_dir, "CommunityModules-deps.jar")
        classpath = f"{self.tla_jar_path}"
        if os.path.exists(community_jar):
            classpath += f":{community_jar}"

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

        logger.info(f"Starting TLC: {' '.join(cmd)}")
        if cwd:
            logger.info(f"Working Directory: {cwd}")

        self.process = subprocess.Popen(
            cmd,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, # Merge stderr into stdout for simpler monitoring
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
        logger.info("Waiting for TLC debugger to initialize...")
        while True:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError("TLC process exited prematurely")
            
            logger.info(f"[TLC] {line.strip()}")
            if "Debugger is listening" in line:
                logger.info("TLC Debugger is ready.")
                self.is_ready = True
                break

    def _drain_stdout(self, pipe):
        """Continuously reads stdout to prevent buffer filling."""
        for line in iter(pipe.readline, ''):
            pass
            # We could log this if verbose logging is enabled
        pipe.close()

    def stop(self):
        """Terminates the process."""
        if self.process:
            logger.info("Terminating TLC process...")
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
            self.process = None
