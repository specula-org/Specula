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

    def start(self, spec_file, config_file, trace_file=None, cwd=None, port=4712):
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

        # Increased timeout to 300s (5 minutes) for the massive etcd-raft spec
        is_ready = self.ready_event.wait(timeout=300)
        if not is_ready:
            logger.error("Timed out waiting for TLC signal after 300s. TLC might be struggling with spec complexity.")
            return False
        return True

    def stop(self):
        if self.process:
            self.process.terminate()
            self.process = None
