#!/usr/bin/env python3
"""
Test debugger with real trace validation command
Based on user's working command
"""
import sys
import subprocess
import threading
import time
import os
sys.path.insert(0, '/home/ubuntu/specula/tools/trace_debugger')

from tlc_debugger_client import TLCDebuggerClient


def start_tlc_with_debugger():
    """Start TLC with debugger using the real command format"""

    env = os.environ.copy()
    env['JSON'] = '../traces/confchange_disable_validation.ndjson'  # This trace FAILS validation

    cmd = [
        'java',
        '-XX:+UseParallelGC',
        '-Xmx4G',
        '-cp', '/home/ubuntu/specula/lib/tla2tools.jar:/home/ubuntu/specula/lib/CommunityModules-deps.jar',
        'tlc2.TLC',
        '-debugger', 'nosuspend,port=4712',  # Added debugger
        '-config', 'Traceetcdraft_progress.cfg',
        'Traceetcdraft_progress.tla',
        '-lncheck', 'final',
        '-metadir', '/tmp/tlc_state_debug'
    ]

    print("=== Starting TLC with debugger ===")
    print(f"Command: {' '.join(cmd)}")
    print(f"JSON: {env['JSON']}")

    proc = subprocess.Popen(
        cmd,
        cwd='/home/ubuntu/specula/data/workloads/etcdraft/scenarios/progress_inflights/spec',
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1
    )

    # Monitor output
    def print_output():
        for line in proc.stdout:
            print(f"[TLC] {line.rstrip()}")

    threading.Thread(target=print_output, daemon=True).start()
    return proc


def test_debugger():
    # Start TLC
    tlc_proc = start_tlc_with_debugger()

    # Wait for debugger server to start (reduced to connect faster)
    print("\nWaiting for debugger server...")
    time.sleep(2)

    # Connect client
    client = TLCDebuggerClient()
    client.verbose = True

    try:
        print("\n=== Connecting ===")
        if not client.connect(timeout=10):
            print("✗ Failed to connect")
            return False

        print("✓ Connected")

        if not client.initialize():
            print("✗ Failed to initialize")
            return False
        print("✓ Initialized")

        # Set UNSATISFIED breakpoint
        print("\n=== Setting breakpoint ===")
        if not client.set_exception_breakpoints(
            filters=["UnsatisfiedBreakpointsFilter"]
        ):
            print("✗ Failed to set breakpoints")
            return False
        print("✓ Breakpoint set")

        if not client.configuration_done():
            print("✗ Failed to configure")
            return False

        if not client.continue_execution():
            print("✗ Failed to continue")
            return False

        # Listen for events
        print("\n=== Monitoring for breakpoints ===")
        stop_count = 0
        timeout_count = 0
        max_timeouts = 5

        while timeout_count < max_timeouts:
            msg = client.receive_message(timeout=30.0)

            if not msg:
                timeout_count += 1
                print(f"[Timeout {timeout_count}/{max_timeouts}]")
                continue

            msg_type = msg.get("type")

            if msg_type == "event":
                event = msg.get("event")

                if event == "stopped":
                    stop_count += 1
                    body = msg.get("body", {})
                    reason = body.get("reason", "unknown")
                    text = body.get("text", "")

                    print(f"\n{'='*60}")
                    print(f"🔴 BREAKPOINT HIT #{stop_count}")
                    print(f"{'='*60}")
                    print(f"Reason: {reason}")
                    if text:
                        print(f"Text: {text}")

                    # Get stack trace
                    frames = client.get_stack_trace()
                    if frames:
                        print(f"\nStack trace ({len(frames)} frames):")
                        for i, frame in enumerate(frames[:3]):  # Show top 3
                            source = frame.get("source", {})
                            print(f"  [{i}] {source.get('name', '?')}:{frame.get('line', '?')}")
                            print(f"      {frame.get('name', '?')}")

                    # Continue
                    print("\nContinuing...")
                    client.continue_execution()

                elif event == "terminated":
                    print("\n✓ TLC terminated")
                    break

                elif event == "output":
                    output = msg.get("body", {}).get("output", "")
                    if any(kw in output for kw in ["Error", "violation", "Progress(", "Finished"]):
                        print(f"[OUTPUT] {output.strip()}")

        print(f"\n{'='*60}")
        print(f"{'✓' if stop_count > 0 else '✗'} Test complete: {stop_count} breakpoint(s) captured")
        print(f"{'='*60}")
        return stop_count > 0

    except Exception as e:
        print(f"\n✗ Exception: {e}")
        import traceback
        traceback.print_exc()
        return False

    finally:
        client.close()
        time.sleep(2)
        if tlc_proc.poll() is None:
            print("\nTerminating TLC...")
            tlc_proc.terminate()
            tlc_proc.wait(timeout=10)


if __name__ == "__main__":
    success = test_debugger()
    sys.exit(0 if success else 1)
