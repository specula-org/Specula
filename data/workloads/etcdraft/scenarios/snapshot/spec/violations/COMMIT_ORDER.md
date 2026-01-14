# Violation Commits Order

This document records the commit order from the `run` branch of tangruize's fork.

## Base Commits (Merged to Parent spec/ Folder)

The following three commits have been merged into the parent `spec/` folder:

| # | Commit | Description | Modified Files |
|---|--------|-------------|----------------|
| 1 | `e0ea20a` | MaxTimeoutLimit | MCetcdraft.cfg, MCetcdraft.tla |
| 2 | `abff276` | request | MCetcdraft.tla |
| 3 | `225788d` | value | MCetcdraft.cfg, MCetcdraft.tla |

## Violation Commits (This Folder)

The following commits are listed in chronological order (oldest to newest). The complete final state is preserved in this `violations/` folder:

| # | Commit | Description | New File |
|---|--------|-------------|----------|
| 4 | `ac00391` | changed view, but not used | *(only .tla/.cfg changes)* |
| 5 | `24c9692` | monotonic prop: find violation (probably false positive) | `MonotonicTermProp.violated` |
| 6 | `f96f8dd` | QuorumLogInv violated | `QuorumLogInv.violated` |
| 7 | `ca98eb0` | LearnersVotersDisjointInv violated | `LearnersVotersDisjointInv.violated` |
| 8 | `c9a7ca6` | ConfigNonEmptyInv violated | `ConfigNonEmptyInv.violated` |
| 9 | `164c433` | MonotonicMatchIndexProp violated | `MonotonicMatchIndexProp.violated` |
| 10 | `f35a36b` | JointConfigNonEmptyInv violated | `JointConfigNonEmptyInv.violated` |
| 11 | `f4942a8` | tlc exception | `tlc-exception1.out` |
| 12 | `ee24484` | PendingConfIndexValidInv violated | `PendingConfIndexValidInv.violated` |
| 13 | `f13a390` | DurableStateConsistency violated | `DurableStateConsistency.violated` |
| 14 | `6a494ce` | HistoryLogLengthInv violated | `HistoryLogLengthInv.violated` |
| 15 | `7133127` | LogMatchingInv violated | `LogMatchingInv.violated` |
| 16 | `affe9e5` | CurrentTermAtLeastLogTerm violated | `CurrentTermAtLeastLogTerm.violated` |

## Violation Files (Discovery Order)

1. `MonotonicTermProp.violated` - possibly false positive
2. `QuorumLogInv.violated`
3. `LearnersVotersDisjointInv.violated`
4. `ConfigNonEmptyInv.violated`
5. `MonotonicMatchIndexProp.violated`
6. `JointConfigNonEmptyInv.violated`
7. `tlc-exception1.out` - TLC exception
8. `PendingConfIndexValidInv.violated`
9. `DurableStateConsistency.violated`
10. `HistoryLogLengthInv.violated`
11. `LogMatchingInv.violated`
12. `CurrentTermAtLeastLogTerm.violated`

## Source Information

- Repository: https://github.com/tangruize/Specula
- Branch: `run`
- Latest commit: `affe9e5`
- Pulled on: 2026-01-14
