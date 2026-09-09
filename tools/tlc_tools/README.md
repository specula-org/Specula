# TLC task tools

After `specula setup`, these tools are available to all supported agents in one-shot and incremental runs.

- `start_tlc(work_dir, spec_file, config_file, options)` starts TLC model checking or simulation and returns a task ID and log paths. Pass existing wrapper flags as an argument list in `options`.
- `wait_tlc(task_ids, timeout_seconds=3600, mode="any")` waits up to one hour for any listed task to finish. Use `mode="all"` to wait for all tasks. Reuse the same IDs to continue waiting.

Task records, logs and exit codes are saved under `.tlc-tasks/jobs/` in the run's working directory.

## Tests

```bash
uv run pytest tests/unit/test_tlc_tasks.py -q
```
