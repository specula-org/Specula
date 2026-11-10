# StepHup 双向测试初试

本轮先验证测试管线能够暴露此前已知的模型不忠实问题。此案例用于开发与校准，不算盲测新发现。

测试直接执行 Go 的 raft.Step(MsgHup) 与已有 TLA+ 的 StepHup。输入维度：Normal/legacy conf/V2 conf，applied=3/4，PreVote=false/true，learner=false/true；V00 无 V2，共 16 组，其余 24 组。两个生成方向覆盖同一组输入，不能相加称作 48 个独立场景。TLC 生成的是有限域中的局部输入与输出，尚不是完整系统的可达轨迹生成。

| 版本/模型 | 唯一输入 | 代码输入路线不一致 | TLC 输入路线不一致 | 两路线总执行秒数 |
|---|---:|---:|---:|---:|
| V00 valid-payload-baseline | 16 | 0 | 0 | 3.36 |
| V01 valid-payload-baseline | 24 | 2 | 2 | 3.41 |
| V01 valid-payload-repaired | 24 | 0 | 0 | 2.71 |
| V02 valid-payload-baseline | 24 | 0 | 0 | 3.41 |

V01 的两项差异均为：普通 voter、applied=3、commit=4，第 4 项是 V2 配置；PreVote 两种取值各一项。代码分别产生 Candidate+MsgVote 或 PreCandidate+MsgPreVote，原模型保持 Follower、不发消息。根因是模型扫描 ConfKinds（含 V2），代码 numOfPendingConf 只扫描 EntryConfChange。仅在实验副本中改为 LegacyConfKinds，保留 correctness invariant 不变，24 组全部一致。

V01 最终两组结果已补齐实际 protobuf 配置 payload，避免将日志类型测试误当成完整有效记录测试。最早 baseline/repaired 两组曾用空 payload，只作为启动诊断保留，正式局部结论引用 valid-payload 两组。V00/V02 也已使用完整 protobuf 配置 payload 重测，结果一致。

比较 role、term、vote、leader、applied、commit、last index 和消息的 type/from/to/term/index/logTerm。未观察全部内部字段，人工 snapshot 前状态也未证明在全系统中可达，因此结果仅是这个局部投影的一致性证据。耗时包含 Go/TLC 启动，不包含适配器开发时间；不能据此给出整个流程的成本结论。

修正后的 V01 模型也通过了 8 条历史 traces（4,629 个事件）的完整对应回归，使用原 TraceCorrespondence.cfg（保留其 ConfigurationOrigin 排除）。这不是新一轮场景生成，也不是所有 correctness properties 均通过的声明。对应日志与每条 trace 哈希在 trace-V01-campaign-repair/。
