| Run | Runs learned | Out-of-focus steps that change the view | EnvUpdate keeps | Check |
|---|---:|---|---:|---|
| joint-autoleave | 6 | MCLose: quality.votes; MCTransfer: raft.elapsed | 21 of 23 | held on 3 runs |
| joint-explicit | 6 | MCTransfer: raft.elapsed | 22 of 23 | held on 6 runs |
| joint-snapshot-recovery | 5 | MCLose: quality.votes | 22 of 23 | violated by part 24 |
| learner-vote | 13 | MCLose: quality.votes; MCReportUnreachable: quality.votes; MCTransfer: raft.elapsed; ReadIndex: quality.votes | 21 of 23 | held on 13 runs |
| membership-snapshots | 2 | MCTransfer: raft.elapsed | 22 of 23 | held on 2 runs |
| node-lifecycle | 107 | - | 23 of 23 | held on 115 runs |
| outgoing-snapshot-restore | 8 | MCLose: quality.votes; MCTransfer: raft.elapsed | 21 of 23 | held on 7 runs |
| partition-batching | 2 | MCTransfer: raft.elapsed | 22 of 23 | held on 2 runs |
| raw-elections-reads-recovery | 4 | MCLose: quality.votes; MCTransfer: raft.elapsed | 21 of 23 | held on 5 runs |
| ready-intervening-output | 57 | MCLose: quality.votes; MCReportUnreachable: quality.votes; MCTransfer: quality.votes, raft.elapsed | 21 of 23 | held on 74 runs |
| same-batch-replay | 17 | MCTransfer: raft.elapsed | 22 of 23 | violated by part 34 |

All runs together:

- MCLose: quality.votes
- MCReportUnreachable: quality.votes
- MCTransfer: quality.votes, raft.elapsed
- ReadIndex: quality.votes
