#!/usr/bin/env python3
"""
Simple debugger client that connects to TLC and monitors for breakpoints
"""
import sys
import time
sys.path.insert(0, '/home/ubuntu/specula/tools/trace_debugger')
from tlc_debugger_client import TLCDebuggerClient

def main():
    print("=== TLC Debugger Monitor ===\n")

    client = TLCDebuggerClient(port=4712)

    print("Connecting to TLC debugger on port 4712...")
    if not client.connect():
        print("✗ Failed to connect. Make sure TLC is running with -debugger port=4712")
        return 1

    print("✓ Connected\n")

    print("Initializing debug session...")
    if not client.initialize():
        print("✗ Initialization failed")
        return 1
    print("✓ Initialized\n")

    print("Setting exception breakpoints (UnsatisfiedBreakpointsFilter)...")
    if not client.set_exception_breakpoints(['UnsatisfiedBreakpointsFilter']):
        print("✗ Failed to set breakpoints")
        return 1
    print("✓ Breakpoints set\n")

    print("Sending configuration done...")
    if not client.configuration_done():
        print("✗ Configuration failed")
        return 1
    print("✓ Configuration done\n")

    print("Continuing execution...")
    if not client.continue_execution():
        print("✗ Failed to continue")
        return 1
    print("✓ TLC is now running\n")

    print("=" * 60)
    print("Monitoring for breakpoints and events...")
    print("=" * 60)
    print()

    # Monitor for events with timeout
    start_time = time.time()
    timeout = 120  # 2 minutes
    breakpoint_count = 0
    stopped_count = 0

    try:
        while time.time() - start_time < timeout:
            msg = client.receive_message(timeout=5)
            if msg is None:
                continue

            msg_type = msg.get('type')

            if msg_type == 'event':
                event = msg.get('event')
                print(f"[EVENT] {event}")

                if event == 'stopped':
                    stopped_count += 1
                    reason = msg.get('body', {}).get('reason', 'unknown')
                    print(f"  └─ Reason: {reason}")
                    print(f"  └─ Thread: {msg.get('body', {}).get('threadId', 'unknown')}")

                    if reason == 'exception':
                        breakpoint_count += 1
                        print(f"\n🔴 BREAKPOINT #{breakpoint_count} TRIGGERED!")
                        print(f"  Details: {msg.get('body', {})}")
                        print()

                elif event == 'terminated' or event == 'exited':
                    print("\n✓ TLC execution finished")
                    break

                elif event == 'output':
                    output = msg.get('body', {}).get('output', '')
                    if output.strip():
                        print(f"  └─ Output: {output.strip()}")

    except KeyboardInterrupt:
        print("\n\n⚠ Monitoring interrupted by user")
    except Exception as e:
        print(f"\n\n✗ Error during monitoring: {e}")

    print("\n" + "=" * 60)
    print(f"Summary:")
    print(f"  - Stopped events: {stopped_count}")
    print(f"  - Breakpoints triggered: {breakpoint_count}")
    print("=" * 60)

    client.close()
    return 0

if __name__ == '__main__':
    sys.exit(main())
