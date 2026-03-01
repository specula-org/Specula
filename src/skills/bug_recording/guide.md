# Bug Recording Guide

Record confirmed bugs to the shared Google Sheet via `scripts/record_bug.py`.

## When to Record

- **DO** record: Bug is confirmed (code evidence found, or TLC counterexample produced).
- **DON'T** record: Speculation, unverified suspicion, or spec-only issues.

## Fields

| Field | Required | Description | Examples |
|-------|----------|-------------|----------|
| `system` | Yes | Repository / project name | `etcd/raft`, `HashiCorp Raft`, `braft`, `sofa-jraft`, `Dragonboat`, `CometBFT` |
| `protocol` | Yes | Protocol and language | `Raft (Go)`, `Raft (C++)`, `Raft (Java)`, `PBFT (Go)`, `Paxos (Go)`, `QBFT (Java)` |
| `finding` | Yes | One-line description of the bug. Be specific: include the function/component name and the consequence. | `Missing resp.Term check in heartbeat() — stale leader holds lease indefinitely during disk IO stall` |
| `reference` | No | PR or Issue reference after filing upstream | `PR #381`, `Issue #666` |
| `url` | No | Full GitHub URL of the PR/Issue | `https://github.com/etcd-io/raft/pull/381` |
| `status` | No | Current upstream status | See status values below |
| `notes` | No | Extra context | `Not yet opened`, `Reproduction test in PR #1242` |

## Status Values

| Status | Meaning |
|--------|---------|
| *(empty)* | Not yet reported upstream |
| `Open` | Issue/PR filed, awaiting response |
| `Approved` | Maintainer acknowledged / PR approved |
| `Merged` | Fix merged |
| `Closed` | Closed by maintainer (wontfix, duplicate, etc.) |

When first recording a bug that hasn't been reported upstream yet, leave `status` empty and put `Not yet opened` in `notes`.

## Commands

### Append a new bug

```bash
python3 scripts/record_bug.py append \
  --system "etcd/raft" \
  --protocol "Raft (Go)" \
  --finding "Description of the bug" \
  --reference "PR #123" \
  --url "https://github.com/..." \
  --status "Open" \
  --notes "optional notes"
```

Only `--system`, `--protocol`, and `--finding` are required. The `#` is auto-assigned.

### Update an existing bug

```bash
python3 scripts/record_bug.py update \
  --number 5 \
  --status "Merged" \
  --reference "PR #999" \
  --url "https://github.com/..."
```

### List all bugs

```bash
python3 scripts/record_bug.py list
```

## Workflow

1. After confirming a bug, **first run `list`** to check it's not already recorded.
2. **`append`** the new bug with at least system, protocol, and finding.
3. After filing a GitHub issue/PR, **`update`** with reference, url, and status.
