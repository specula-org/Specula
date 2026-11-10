# V00–V03 演化方案实验（进行中）

顺序：model 演化 → inv 演化 → 状态空间探索。A、B 为必达目标；其他发现单列回归。主要模型 GPT-6 Astra，后续复现 GPT-5.5；本轮无费用上限。所有修改仅在本实验目录，尚未集成 Specula。

## 当前已验证

V01 的通用 JSON 协议/runner 与 Go/TLA 适配器已完成首轮。105 个代码侧场景、43 个 TLC 生成场景，共 122 个不同的语义输入。18 次基线不一致对应三个模型错误：空 V2 的 transition 判断、pending V2 的竞选扫描、Advance 零 cursor 的 auto-leave。修复只改行为模型的三处定义，未改实现或 inv。

独立复核测试器时，发现复用 TLC 输出目录可读取旧后继。修复为独占新目录、失败命令输出不参与比较，并让无后继动作保留输入/前状态证据、明确返回 disabled。真实 Go/TLC 负对照和比较器检查均通过；四条基线/修复路线在新目录复跑，修复后 148 次比较全部一致。

最终三处修复后的模型再次通过 8 条历史 trace、4,629 个事件的对应回归，使用原 TraceCorrespondence.cfg；其既有 ConfigurationOrigin 排除保留。这是历史轨迹复播，并非新的轨迹生成或全部性质通过。

V02 已通过 239 个代码侧和 103 个模型侧场景，通用 runner/schema/comparator 不变；新增 learner vote、Ready/Advance 间新输出和实际 Node 通道循环。独立新目录重跑和 239 个 Go 场景的 race detector 检查通过。21 个旧版本对照也匹配，6 个非法 ConfState 输入单列范围诊断。V02 历史模型继承的两个旧缺陷得到同样修复；另扩大 RawNode 空 Ready 的 API 建模范围，后续检查其对搜索的影响。V03 从当前修复后的 V02 实际演化，479 个代码侧、174 个模型侧实例全部匹配；独立重跑和全部 479 个 Go 场景的 race detector 检查通过。继承模型有 178 次不一致，包含版本变化及旧模型错误，不能直接当作 178 个 bug。

V03 又暴露了四个既有模型错误：删除再添加 learner 的 Progress 生命周期、Node 自移除后的提议通道、复用旧 DropQuota 观察值、panic 后仍继续修改状态。已补回 V01/V02 并运行完整 653 个实例的回归；V01 另补 RawNode 空 Ready。最终两版本这批实例均原始匹配。曾出现的终止 panic 前内部消息缓冲顺序差异保留为显式观察边界，见 control/terminal-panic-observation.md。

inv 的独立初判已启动，输入不含新版本性质、模型侧修复报告、gold 标签或其他调用的答案。

## 尚未得出结论

- 未完成 AI 对 inv 是否应修改的独立判断实验，尚不能选择判断或重写策略。
- 未完成基于状态差分的 inv 修改验证。
- 未开始本轮完整/定向协议探索或 GPT-5.5 复现，A/B 尚未达到最终验收。局部行为不一致不计为自主发现真实系统 bug。
- 局部构造状态的结构/映射检查不等于从完整协议 Init 可达；语言适配目前仅实测 Go。

## 主要证据

- 输入版本与授权：control/manifest.json
- V01 Astra 原始结果：agent-runs/model-V01/out/report.md、out/results.json
- 复核后框架：agent-runs/model-V01-hardened/out/framework/
- 独立复跑：agent-runs/model-V01-hardened/out/coordinator-rerun.json
- 测试器负对照：agent-runs/model-V01-hardened/out/negative-controls/results.json
- 最终 V01 trace 回归：results/trace-V01-all-action-repairs/summary.json
- AI 调用及用量：logs/*.receipt.json、*.jsonl
- 当前进度：control/progress.json

最终 backward repairs 后的历史 trace 回归也已完成：V01 为 8/8、4,629 事件，V02 为 11/11、5,778 事件，全部绑定当前模型 SHA。V01 的独立 inv 初判覆盖四项事先列出的核心义务，候选公式尚待执行验证。
