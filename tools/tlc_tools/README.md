# TLC task tools

`specula setup` installs the tool dependencies. Specula registers `start_tlc` and `wait_tlc` automatically for ordinary and incremental Agent runs. Codex, Claude Code, Copilot CLI and OpenCode use MCP; Pi uses an extension calling the same Python implementation. No global Agent configuration or skill changes are required.

- `start_tlc(work_dir, spec_file, config_file, options)` starts the existing resource-budgeted TLC wrapper and returns a task ID, evidence paths and a waiting hint. `options` is an argument list, not a shell command. Model checking and simulation use the wrapper's existing flags and resource policy.
- `wait_tlc(task_ids, timeout_seconds=3600, mode="any")` waits inside the tool. Use `mode="all"` to collect all listed tasks. A wait timeout or cancelled request does not cancel TLC; reuse the same IDs. Logs stay on disk instead of repeatedly entering the model context.

Each task retains its request, worker identity, logs and exit receipt under the run's `.tlc-tasks/jobs/`. A tool-server reconnection can read the same task. The owning phase's teardown stops its outstanding tasks; workers also stop when their launcher disappears. Lost workers are reported as interrupted, never successful. This does not provide TLC checkpoint recovery across machine restarts.

Results describe process execution, not verification correctness. Invariant violations, infrastructure errors and the wrapper's normal budget exit remain distinguishable through the exit code and logs. In particular, exit 124 is not automatically CI failure or proof of safety. Checking methodology is unchanged.

## Development

Run `uv run pytest tests/unit/test_tlc_tasks.py -q`. These tests use real subprocesses and MCP transports with a fake JVM; they do not call a paid model. Native-client acceptance should additionally check that a wait exceeding the client's ordinary timeout produces no intervening model requests.

The implementation follows the background-job separation used by [OpenClaw](https://docs.openclaw.ai/gateway/background-process) and the create/wait hints in [codex-monitor](https://github.com/naowalrahman/codex-monitor/blob/2daa275e08fdb1c604c76eaf8d7cf56bfcdd7c88/src/server.ts). Client timeouts are set using [Codex configuration](https://learn.chatgpt.com/docs/config-file/config-reference), [Copilot MCP configuration](https://docs.github.com/en/copilot/reference/copilot-cli-reference/cli-command-reference#local-server-configuration-fields) and OpenCode's local-server timeout. Claude Code uses its native MCP execution timeout; an explicitly shortened `MCP_TOOL_TIMEOUT` can still interrupt a wait without stopping TLC.
