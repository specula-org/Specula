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
            # Using a simpler iteration to ensure we don't miss lines
            while True:
                line = self.process.stdout.readline()
                if not line: break
                
                # REAL-TIME LOGGING: See exactly what TLC is doing
                print(f"  [TLC] {line.strip()}")
                
                if "Debugger is listening" in line:
                    logger.info(">>> SUCCESS: TLC Debugger is now listening.")
                    self.ready_event.set()
            self.process.stdout.close()

        t = threading.Thread(target=drain_and_watch, daemon=True)
        t.start()

        # 30 second timeout for TLC debugger to start
        is_ready = self.ready_event.wait(timeout=30)
        if not is_ready:
            logger.error("Timed out waiting for TLC signal after 30s. TLC might be struggling with spec complexity.")
            return False
        return True

    def stop(self):
        if self.process:
            self.process.terminate()
            try:
                # Wait up to 5 seconds for graceful termination
                self.process.wait(timeout=5)
                logger.info("TLC process terminated gracefully")
            except subprocess.TimeoutExpired:
                # Force kill if process doesn't respond
                logger.warning("Process didn't terminate gracefully, killing forcefully...")
                self.process.kill()
                self.process.wait()
            self.process = None
