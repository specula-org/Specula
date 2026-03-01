# Bug Recording Guide

Record confirmed bugs to the shared Google Sheet via `scripts/record_bug.py`.

## When to Record

- **DO** record: Bug is confirmed to cause real issues at runtime (via code evidence, TLC counterexample, or trace validation), OR smaller issues that can be 100% determined through code review alone (these may not manifest at runtime but are identifiable through experience and knowledge).
- **DON'T** record: Speculation, unverified suspicion, or spec-only issues.

## Sheets

| Sheet | `--sheet` value | Description |
|-------|-----------------|-------------|
| New bug + New bug (detailed) | `new` (default) | Bugs we discovered |
| Known bug + Known bug (detailed) | `known` | Bugs already reported by others that we reproduced or confirmed |

When you append or update with `--sheet new`, both "New bug" (simple) and "New bug (detailed)" are written simultaneously. Same for `--sheet known`.

## Fields

### Simple fields (written to all sheets)

| Field | Required | Description | Examples |
|-------|----------|-------------|----------|
| `--system` | Yes | Repository / project name | `etcd/raft`, `HashiCorp Raft`, `braft`, `sofa-jraft`, `Dragonboat`, `CometBFT` |
| `--protocol` | Yes | Protocol and language | `Raft (Go)`, `Raft (C++)`, `Raft (Java)`, `PBFT (Go)`, `Paxos (Go)`, `QBFT (Java)` |
| `--finding` | Yes | One-line bug description. Be specific: include function/component name and consequence. | `Missing resp.Term check in heartbeat() — stale leader holds lease indefinitely` |
| `--reference` | No | PR or Issue reference after filing upstream | `PR #381`, `Issue #666` |
| `--url` | No | Full GitHub URL of the PR/Issue | `https://github.com/etcd-io/raft/pull/381` |
| `--status` | No | Current upstream status | See status values below |
| `--notes` | No | Extra context | `Not yet opened`, `Reproduction test in PR #1242` |

### Detailed fields (written to detailed sheets only)

| Field | Required | Description | Examples |
|-------|----------|-------------|----------|
| `--severity` | No | Bug severity | `Critical`, `Medium`, `Minor` |
| `--bug-family` | No | Bug family / category | `Response Handler Inconsistency`, `Non-Atomic Persistence`, `Vote Extensions` |
| `--discovery-method` | No | How the bug was found | `MC-BFS`, `MC-Simulation`, `Trace Validation`, `Code Review` |
| `--root-cause` | No | Brief root cause description | `3 of 4 response handlers check resp.Term; onInstallSnapshotReturned does not` |
| `--affected-code` | No | Code locations | `Replicator.java:711-763`, `node.cpp:1705-1738` |

## Status Values

| Status | Meaning |
|--------|---------|
| *(empty)* | Not yet reported upstream |
| `Open` | Issue/PR filed, awaiting response |
| `Approved` | Maintainer acknowledged / PR approved |
| `Merged` | Fix merged |
| `Closed` | Closed by maintainer (wontfix, duplicate, etc.) |

When first recording a bug that hasn't been reported upstream yet, leave `--status` empty and put `Not yet opened` in `--notes`.

## Commands

### Append a new bug

```bash
python3 scripts/record_bug.py append \
  --system "sofa-jraft" \
  --protocol "Raft (Java)" \
  --finding "onInstallSnapshotReturned missing term check" \
  --severity "Critical" \
  --bug-family "Response Handler Inconsistency" \
  --discovery-method "Code Review" \
  --root-cause "3 of 4 handlers check resp.Term; this one does not" \
  --affected-code "Replicator.java:711-763" \
  --notes "Not yet opened"
```

### Append a known bug

```bash
python3 scripts/record_bug.py append --sheet known \
  --system "CometBFT" \
  --protocol "PBFT (Go)" \
  --finding "Vote Extension Deadlock" \
  --severity "Critical" \
  --discovery-method "MC-BFS" \
  --reference "Issue #5204" \
  --url "https://github.com/cometbft/cometbft/issues/5204" \
  --status "Open"
```

### Update an existing bug

```bash
python3 scripts/record_bug.py update \
  --number 5 \
  --status "Merged" \
  --reference "PR #999" \
  --url "https://github.com/..."
```

Update a known bug:

```bash
python3 scripts/record_bug.py update --sheet known \
  --number 1 \
  --status "Merged"
```

### List bugs

```bash
python3 scripts/record_bug.py list                    # New bug (simple)
python3 scripts/record_bug.py list --sheet new-detailed  # New bug (detailed)
python3 scripts/record_bug.py list --sheet known         # Known bug (simple)
python3 scripts/record_bug.py list --sheet known-detailed # Known bug (detailed)
```

## Workflow

1. After confirming a bug, **first run `list`** to check it's not already recorded.
2. **`append`** the new bug. Which fields to include depends on the user's prompt — always follow the user's instructions. At minimum, provide system, protocol, and finding, but the user may ask for more or fewer fields.
3. After filing a GitHub issue/PR, **`update`** with reference, url, and status.
