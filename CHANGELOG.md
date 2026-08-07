# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [1.0.0] - 2026-08-01

### Added

- Linked the first public Specula paper from the README and added its BibTeX citation.
- Added a durable repair-confirmation checkpoint tied to the exact committed `findings.json`, allowing interrupted runs to finish the correct scoped result pass before resuming upstream phases.

### Changed

- Scoped repair-loop result handling to the findings in the current `findings.json` while retaining full trace validation and model checking for affected configurations.
- Preserved evidence from repaired findings by recording resolved `PENDING REPAIR` artifacts as `FALSE POSITIVE` without rerunning the finding agent.

### Fixed

- Corrected the bundled TLC wrapper so `-D` enables deadlock checking.
- Bound Codex usage accounting to the exact native root session and its descendants, including current cache-token fields, without guessing between concurrent sessions or failing successful runs when usage is unavailable.

See the [v1.0.0 release notes](https://github.com/specula-org/Specula/releases/tag/v1.0.0) for upgrade instructions and known limitations.

## [0.3.0] - 2026-07-26

### Added

- Added run-level and per-target human-readable output indexes that surface confirmation and severity reports first.
- Added `--keep-original` to run against a private copy of the target checkout and produce a Git-format `changes.patch` while leaving the original unchanged.
- Added JSON `--agent-config` routing for assigning different agents, models, and effort levels to individual phases.
- Added OpenCode and Pi adapters alongside Claude Code, Codex, and Copilot CLI.
- Added run-wide TLC memory and optional worker budgets, with pre-launch rejection when a run would exceed its configured resources.
- Added configurable recovery for provider policy blocks and transient capacity, transport, and 5xx failures, including exact native-session resume where supported.

### Changed

- Renamed `--skip-validation` to `--skip-validate`; the old spelling is no longer accepted.
- Moved final reports from `.specula-output/spec/confirmed-bugs.md` and `.specula-output/spec/bug-severity.md` to `.specula-output/confirmed-bugs.md` and `.specula-output/bug-severity.md`.
- Replaced the modeling term **Bug Family** with **Scenario**. Findings schema version 2 uses `scenario`, and the bug-tracker helper uses `--scenario`.
- Limited setup prompts to agent CLIs available on `PATH` and expanded `~` in artifact paths.

### Fixed

- Hardened confirmation and repair handoffs, preserved still-valid invariant coverage during repairs, and recovered stale confirmation worktrees through fresh isolated paths.

See the [v0.3.0 release notes](https://github.com/specula-org/Specula/releases/tag/v0.3.0) for migration details, resource requirements, and known limitations.

## [0.2.0] - 2026-07-14

### Added

- Added the unified `specula` CLI for full runs, individual phases, batch execution, reviews, and setup.
- Added isolated, resumable runs under `runs/<run-id>/`, including summaries and audit metadata.
- Added streamed agent activity, file-change monitoring, structured activity logs, and visible failures when required deliverables are missing.
- Added a consistent `--model` and `--effort` interface for Claude Code, Codex, and Copilot CLI.
- Added composable skill installation, generated Codex plugin support, and automated Copilot MCP setup.
- Added an optional macOS and Linux sandbox for restricting workspace writes by agent processes and their children.
- Expanded the modeling workflow with distributed- and concurrent-system examples, specification-fidelity checks, fault-scenario guidance, and practical TLC guidance.

### Changed

- Made isolated output the default; `--no-isolate` retains the legacy output layout.
- Made parallel per-finding confirmation the default; `--legacy-confirm` retains the v0.1 confirmation flow.
- Moved core orchestration into tested Python components and added lint, type-checking, unit-test, and CLI dry-run CI gates.

### Removed

- Stopped shipping the internal `bug_recording` skill to users.

See the [v0.2.0 release notes](https://github.com/specula-org/Specula/releases/tag/v0.2.0) for installation instructions and known limitations.

## [0.1.0] - 2026-03-29

### Added

- Published the initial Specula skill-based workflow for code analysis, TLA+ specification generation, trace-harness generation, trace validation, model checking, and bug confirmation.
- Added interactive and scripted workflows for applying Specula to a target codebase.
- Added initial support for Claude Code, Codex, and Copilot CLI.
- Added the trace-debugger MCP tooling and curated methodology for validating model fidelity before interpreting model-checking results.

[Unreleased]: https://github.com/specula-org/Specula/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/specula-org/Specula/compare/v0.3.0...v1.0.0
[0.3.0]: https://github.com/specula-org/Specula/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/specula-org/Specula/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/specula-org/Specula/tree/v0.1.0
