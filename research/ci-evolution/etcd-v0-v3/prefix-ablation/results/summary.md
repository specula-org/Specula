| Run | Version | Start | Checks | Budget | Outcome | Distinct states | Depth | Wall time |
|---|---|---|---|---:|---|---:|---:|---:|
| `probe-v03` | V03 | prefix | progress properties | 600 s | liveness violation | 3156 | 673 | 134.5 s |
| `probe-v02` | V02 | prefix | progress properties | 600 s | completed, no error | 3177 | 706 | 116.04 s |
| `probe-safety-v03` | V03 | prefix | safety invariants | 600 s | completed, no error | 3272 | 715 | 27.97 s |
| `free-153-v03` | V03 | prefix | progress properties | 600 s | liveness violation | 3272 | 715 | 135.74 s |
| `free-151-v03` | V03 | prefix to event 151 | progress properties | 600 s | budget exhausted, no error | 17007 | 314 | 600.02 s |
| `free-151-v03-3600s` | V03 | prefix to event 151 | progress properties | 3600 s | liveness violation | 80882 | 665 | 3274.68 s |
| `free-41-v03` | V03 | prefix to event 41 | progress properties | 600 s | budget exhausted, no error | 17878 | 218 | 600.02 s |
| `free-1-v03` | V03 | Init | progress properties | 600 s | budget exhausted, no error | 20445 | 217 | 600.02 s |
| `free-1-v03-3600s` | V03 | Init | progress properties | 3600 s | budget exhausted, no error | 103850 | 453 | 3600.03 s |
| `free-151-v02-5400s` | V02 | prefix to event 151 | progress properties | 5400 s | completed, no error | 90301 | 822 | 3199.73 s |
| `ordinary-v03` | V03 | Init | safety invariants | 600 s | budget exhausted, no error | 2788752 | 3 | 600.04 s |
| `ordinary-v2-v03` | V03 | Init | safety invariants | 600 s | budget exhausted, no error | 3031196 | 3 | 600.02 s |
