import subprocess
import threading
import os
import logging
import time

logger = logging.getLogger(__name__)

class TLCExecutor:
    def __init__(self, tla_jar_path=None, community_jar_path=None):
        self.process = None
        self.tla_jar_path = tla_jar_path
        self.community_jar_path = community_jar_path
        self.ready_event = threading.Event()
        # Signal when TLC exits before debugger readiness
        self.failed_event = threading.Event()
        self.exit_code = None

    def _cleanup_zombie_processes(self, port=4712):
        """Kill any existing TLC debugger processes to prevent port conflicts."""
        try:
            # Find and kill processes matching: java + tlc2.TLC + -debugger + port=<port>
            import psutil
            killed_count = 0
            for proc in psutil.process_iter(['pid', 'name', 'cmdline']):
                try:
                    cmdline = proc.info.get('cmdline', [])
                    if not cmdline:
                        continue

                    cmdline_str = ' '.join(cmdline)
                    # Check if it's a TLC debugger process on our port
                    if ('tlc2.TLC' in cmdline_str and
                        '-debugger' in cmdline_str and
                        f'port={port}' in cmdline_str):
                        logger.warning(f"Found zombie TLC process (PID {proc.pid}), killing...")
                        proc.kill()
                        proc.wait(timeout=3)
                        killed_count += 1
                except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.TimeoutExpired):
                    pass

            if killed_count > 0:
                logger.info(f"Killed {killed_count} zombie TLC process(es)")
                time.sleep(0.5)  # Brief pause to let OS release the port

        except ImportError:
            # If psutil is not available, fall back to pkill
            logger.warning("psutil not available, using pkill fallback")
            try:
                subprocess.run(['pkill', '-9', '-f', f'tlc2.TLC.*-debugger.*port={port}'],
                             stderr=subprocess.DEVNULL, check=False)
                time.sleep(0.5)
            except Exception as e:
                logger.warning(f"Could not cleanup zombie processes: {e}")

    def start(self, spec_file, config_file, trace_file=None, cwd=None, port=4712):
        # Clean up any zombie TLC processes before starting
        self._cleanup_zombie_processes(port)

        classpath = f"{self.tla_jar_path}:{self.community_jar_path}"
        env = os.environ.copy()
        if trace_file: env["JSON"] = trace_file

        cmd = ["java", "-XX:+UseParallelGC", "-Xmx4G", "-cp", classpath,
               "tlc2.TLC", "-debugger", f"port={port}", "-config", config_file, spec_file]

        logger.info(f"Launching TLC: {' '.join(cmd)}")
        self.process = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)

        def drain_and_watch():
            """Drain TLC stdout and signal readiness or failure.

            - Sets ready_event when debugger announces readiness.
            - If the process terminates before readiness, sets failed_event
              and records the exit_code to allow the main thread to react
              immediately instead of timing out.
            """
            while True:
                line = self.process.stdout.readline()
                if not line:
                    break

                # REAL-TIME LOGGING: See exactly what TLC is doing
                logger.debug(f"  [TLC] {line.strip()}")

                if "Debugger is listening" in line:
                    logger.info(">>> SUCCESS: TLC Debugger is now listening.")
                    self.ready_event.set()

            # EOF reached, capture exit status and signal failure if not ready
            try:
                self.exit_code = self.process.poll()
            except Exception:
                self.exit_code = None

            self.process.stdout.close()

            if not self.ready_event.is_set():
                logger.error("TLC process terminated before debugger became ready")
                self.failed_event.set()

        t = threading.Thread(target=drain_and_watch, daemon=True)
        t.start()

        # Robust wait loop: respond to readiness or immediate failure
        start_time = time.time()
        timeout = 60

        while time.time() - start_time < timeout:
            if self.ready_event.is_set():
                return True

            # If drain thread detected premature termination, fail fast
            if self.failed_event.is_set():
                if self.exit_code is not None:
                    logger.error(f"TLC process exited prematurely with code {self.exit_code}")
                else:
                    logger.error("TLC process exited prematurely before debugger was ready")
                return False

            # Defensive: also check process status in case drain thread hasn't signaled yet
            if self.process.poll() is not None:
                self.exit_code = self.process.returncode
                self.failed_event.set()

            time.sleep(0.1)

        logger.error(f"Timed out waiting for TLC debugger readiness after {timeout}s")
        return False

    def stop(self):
        if self.process:
            self.process.terminate()
            try:
                # Wait up to 1 second for graceful termination
                self.process.wait(timeout=1)
                logger.info("TLC process terminated gracefully")
            except subprocess.TimeoutExpired:
                # Force kill if process doesn't respond
                logger.warning("Process didn't terminate gracefully, killing forcefully...")
                self.process.kill()
                self.process.wait()
            self.process = None
