| Run | Arm | Transition | Outcome | decision.json | USD | Seconds | Turns | Score |
|---|---|---|---|---|---:|---:|---:|---|
| `A0-V01-r1` | A0 | V01 | success | yes | 6.23 | 1208 | 57 | 3 detected + 1 correct retention; bug A named |
| `A0-V02-r1` | A0 | V02 | success | yes | 4.10 | 744 | 49 | 3 detected + 1 correct retention; bug A named |
| `A0-V03-r1` | A0 | V03 | success | yes | 5.07 | 935 | 47 | 3 detected, 1 incorrect (auto-leave guard copied); bug B named |
| `A1-V01-r1` | A1 | V01 | success | yes | 6.02 | 1262 | 45 | 3 detected + 1 correct retention; bug A named |
| `A1-V02-r1` | A1 | V02 | success | yes | 4.30 | 866 | 40 | 3 detected + 1 correct retention (strengthened); bug A named |
| `A1-V03-r1` | A1 | V03 | success | yes | 5.01 | 1020 | 43 | 4 detected; bug B named and encoded in AutoLeaveAdvance |
| `A2-V01-r1` | A2 | V01 | success | yes | 9.73 | 2130 | 88 | 2 detected + 1 correct retention + 1 missed (AckPreservation kept without evidence); bug A confirmed in code |
| `A2-V02-r1` | A2 | V02 | success | yes | 13.08 | 4986 | 137 | 3 detected + 1 correct retention; bug A found by simulation and confirmed in real code (re-verified) |
| `A2-V03-r1` | A2 | V03 | success | yes | 10.52 | 3000 | 107 | 4 detected; bug B confirmed in real code (re-verified) |
| `A3-V01-r1` | A3 | V01 | success | yes | 11.49 | 2523 | 80 | 3 detected + 1 correct retention; fixed the AckPreservation miss of A2; bug A observed in code but left as requirement-unknown |
| `A3-V02-r1` | A3 | V02 | success | yes | 10.22 | 2264 | 99 | 3 detected + 1 correct retention; bug A not named |
| `A3-V03-r1` | A3 | V03 | success | yes | 10.30 | 1863 | 91 | 4 detected; bug B confirmed in real code as a bug-candidate cell with non-implementation requirement evidence |
