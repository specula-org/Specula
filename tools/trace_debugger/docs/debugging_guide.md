# Trace Validation 调试指南

本文档描述如何系统化地调试 TLA+ Trace Validation 失败的问题。

## 核心原则

**分层调试：从粗到细，逐层深入**

不要试图一次性找到根本原因。应该：
1. 先粗粒度定位问题范围
2. 再细粒度深入问题细节
3. 最后检查具体的失败原因

**工具使用原则：**
- 工具不应该"自动分层"或"自动打断点"
- Agent 应该根据当前的发现，主动决定下一步在哪里打断点
- 每一层的调试都是为了回答一个具体的问题

---

## 第一步：理解问题

### 1.1 解读 TLC 输出

```
Example TLC output:
"29 states generated, 0 states left on queue"
Error: Invariant TraceMatched is violated
```

**关键问题：**
- TLC 生成了多少个状态？（例如：29 个）
- 这意味着什么？
  - State 0: l=1
  - State 28: l=29
  - 尝试从 l=29 生成 l=30 失败
- **失败的是验证哪一行？**
  - 答案：TraceLog[29]（不是 TraceLog[30]！）

### 1.2 检查 Trace 文件

```bash
# 查看失败的那一行（例如第 29 行）
sed -n '29p' trace.ndjson | jq .

# 查看前后几行，了解上下文
sed -n '27,31p' trace.ndjson | jq -c .
```

**理解：**
- 这一行的事件是什么？（SendAppendEntriesRequest, Commit, etc.）
- 涉及哪些节点？（from, to）
- 有什么关键参数？（index, entries, term）

---

## 第二步：粗粒度定位（找到相关的代码分支）

### 2.1 目标

回答问题：**在 Spec 中，是哪个分支/函数负责验证这一行？**

### 2.2 方法

**在关键的入口和分支打断点：**

```python
# 示例：假设失败在 l=29
breakpoints = [
    (522, "TraceNext entry"),           # TraceNext 的入口
    (480, "TraceNextNonReceiveActions"),  # 非接收消息分支
    (512, "TraceNextReceiveActions"),     # 接收消息分支

    # 具体的事件分支
    (489, "SendAppendEntriesRequest branch"),
    (487, "Commit branch"),
    (483, "BecomeLeader branch"),
]

# 所有断点使用相同的条件
condition = "l = 29"
```

**运行后检查：**
- 哪些断点被命中了？
- 哪些断点没被命中？

**结论：**
- 被命中的分支 = 相关的代码路径
- 没被命中的分支 = 不相关，可以忽略

### 2.3 示例

```
结果：
  Line 522 (TraceNext entry):              1 hit  ✅
  Line 480 (TraceNextNonReceiveActions):   1 hit  ✅
  Line 489 (SendAppendEntriesRequest):     1 hit  ✅
  Line 487 (Commit branch):                0 hits ❌
  Line 512 (TraceNextReceiveActions):      0 hits ❌

结论：
  问题在 SendAppendEntriesRequest 分支中
```

---

## 第三步：细粒度定位（找到失败的具体条件）

### 3.1 目标

回答问题：**在相关的代码分支中，是哪个条件失败了？**

### 3.2 方法

**在相关分支的每个条件语句打断点：**

假设第二步确定问题在 `AppendEntriesIfLogged` 函数（Line 323-328）：

```tla
AppendEntriesIfLogged(i, j, range) ==
    /\ LoglineIsMessageEvent("SendAppendEntriesRequest", i, j)  -- 323
    /\ logline.event.msg.type = "MsgApp"                        -- 324
    /\ range[1] = logline.event.msg.index + 1                   -- 325
    /\ range[2] = range[1] + logline.event.msg.entries          -- 326
    /\ AppendEntries(i, j, range)                               -- 327
    /\ ValidateAfterAppendEntries(i, j)                         -- 328
```

**设置断点：**
```python
breakpoints = [
    (323, "AppendEntriesIfLogged entry"),
    (327, "AppendEntries call"),
    (328, "ValidateAfterAppendEntries call"),
]
```

**运行后检查：**
```
结果：
  Line 323: 18 hits  ✅
  Line 327: 0 hits   ❌
  Line 328: 0 hits   ❌

结论：
  - Line 323 被调用了 18 次（18 种不同的 i,j,range 组合）
  - Line 327 从未执行（所有 18 次尝试都在 Line 323-326 失败了）
  - 问题在 Line 323-326 的某个条件中
```

**重要：** 如果 Line 327 是一个函数调用（如 AppendEntries），而它从未被命中，这意味着：
- 要么 Line 323-326 的条件失败
- 要么需要进一步深入 Line 327 调用的函数内部

---

## 第四步：深入函数内部（如果需要）

### 4.1 何时需要深入

如果第三步发现某个**函数调用**从未执行成功（如 Line 327 的 `AppendEntries(i, j, range)`），而前面的条件都满足，那么需要深入这个函数内部。

### 4.2 方法

**在被调用函数的内部打断点：**

假设 `AppendEntries` 调用 `AppendEntriesInRangeToPeer`（在 etcdraft_progress.tla 中）：

```tla
AppendEntriesInRangeToPeer(subtype, i, j, range) ==
    /\ i /= j                                                   -- 436
    /\ range[1] <= range[2]                                     -- 437
    /\ state[i] = Leader                                        -- 438
    /\ j \in GetConfig(i) \union GetOutgoingConfig(i) \union ... -- 439
    /\ (subtype = "heartbeat" \/ ~IsPaused(i, j))               -- 443
    /\ LET ... IN /\ Send(...) /\ ...                           -- 444-502
```

**设置断点：**
```python
# 注意：这个函数在不同的文件中（etcdraft_progress.tla）
breakpoints = [
    ("etcdraft_progress.tla", 436, "i /= j"),
    ("etcdraft_progress.tla", 437, "range[1] <= range[2]"),
    ("etcdraft_progress.tla", 438, "state[i] = Leader"),
    ("etcdraft_progress.tla", 439, "j in Config/Learners"),
    ("etcdraft_progress.tla", 443, "heartbeat or ~IsPaused"),
    ("etcdraft_progress.tla", 474, "Send operation"),
]
```

**运行后检查：**
```
结果：
  Line 436: 10 hits  ✅
  Line 437: 5 hits   ✅
  Line 438: 3 hits   ✅
  Line 439: 0 hits   ❌  ← 第一个从未被命中的行
  Line 443: 0 hits   ❌
  Line 474: 0 hits   ❌

结论：
  - 有些尝试在 Line 436 失败（i = j）
  - 有些尝试在 Line 437 失败（range[1] > range[2]）
  - 有些尝试在 Line 438 失败（state[i] /= Leader）
  - 所有尝试都在 Line 439 失败（没有任何尝试通过 Line 439）
  - 问题在 Line 439
```

### 4.3 关键规律

**断点命中模式：**
```
Line A: 100 hits
Line B: 50 hits
Line C: 20 hits
Line D: 0 hits   ← 第一个 0 hits 的行
Line E: 0 hits
Line F: 0 hits
```

**结论：**
- 问题在 Line C 和 Line D 之间
- Line D 的条件从未满足
- 应该在 Line C 处检查变量，看为什么 Line D 的条件不满足

---

## 第五步：检查失败原因

### 5.1 目标

回答问题：**为什么这个条件失败了？相关变量的值是什么？**

### 5.2 方法

**在失败条件的前一行打断点，检查变量值：**

假设第四步确定问题在 Line 439（`j \in GetConfig(i) \union GetOutgoingConfig(i) \union GetLearners(i)`），我们应该在 Line 438 打断点：

```python
# 在 Line 438 断点（Line 439 的前一行）
breakpoint = {
    "line": 438,
    "condition": "l = 29"
}

# 当断点命中时，检查变量
i_val = get_variable_value(frame_id, "i")
j_val = get_variable_value(frame_id, "j")

# 评估 Line 439 的条件
config = evaluate_expression(frame_id, f'GetConfig("{i_val}")')
outgoing = evaluate_expression(frame_id, f'GetOutgoingConfig("{i_val}")')
learners = evaluate_expression(frame_id, f'GetLearners("{i_val}")')
union = evaluate_expression(frame_id,
    f'GetConfig("{i_val}") \\union GetOutgoingConfig("{i_val}") \\union GetLearners("{i_val}")')

# 检查 j 是否在集合中
j_in_set = evaluate_expression(frame_id,
    f'"{j_val}" \\in GetConfig("{i_val}") \\union ...')

print(f"i={i_val}, j={j_val}")
print(f"GetConfig({i_val}) = {config}")
print(f"GetOutgoingConfig({i_val}) = {outgoing}")
print(f"GetLearners({i_val}) = {learners}")
print(f"Union = {union}")
print(f"j in Union? {j_in_set}")
```

### 5.3 示例输出

```
i=1, j=2
GetConfig(1) = {"1"}
GetOutgoingConfig(1) = {}
GetLearners(1) = {}
Union = {"1"}
j in Union? FALSE  ❌

问题：j=2 不在 Union 集合中！
```

**发现根本原因：**
- 当 l=29 时，GetConfig(1) 只包含节点 1 自己
- j=2 不在集合中，所以条件失败
- 这是配置状态的问题

---

## 第六步：验证和扩展

### 6.1 验证假设

找到一个可能的原因后，应该验证：

**比对成功和失败的情况：**
```python
# 检查 l=28（成功）时的 GetConfig(1)
# vs l=29（失败）时的 GetConfig(1)

# 在 l=28 和 l=29 分别检查
for level in [28, 29]:
    # 设置断点条件：l = level
    # 检查 GetConfig(1) 的值
    # 比较差异
```

**检查多个不同的 (i, j) 组合：**
```python
# 不只检查 i=1, j=2
# 也检查 i=1, j=3; i=2, j=1 等

# 看是否所有组合都失败
# 还是只有特定组合失败
```

### 6.2 扩展调查

如果需要了解"为什么 GetConfig(1) 只有 {1}"，可能需要：
- 检查更早的状态（l=1, l=2, ...）
- 查看配置是如何被修改的
- 检查 ChangeConf, ApplyConfChange 等事件

---

## 方法学总结

### 通用调试流程

```
1. 理解问题
   ├─ 解读 TLC 输出（失败在哪个 l 值？）
   ├─ 查看 Trace 文件（这一行是什么事件？）
   └─ 明确要回答的问题

2. 粗粒度定位
   ├─ 在主要分支的入口打断点
   ├─ 确定哪个分支被执行
   └─ 缩小问题范围

3. 细粒度定位
   ├─ 在相关分支的每个条件打断点
   ├─ 找到"最后一个成功"和"第一个失败"的行
   └─ 确定具体的失败点

4. 深入函数（如果需要）
   ├─ 如果失败点是函数调用，进入函数内部
   ├─ 重复步骤 3（在函数内部打断点）
   └─ 找到函数内部的失败点

5. 检查失败原因
   ├─ 在失败条件的前一行打断点
   ├─ 检查所有相关变量的值
   ├─ 评估失败条件的表达式
   └─ 理解为什么条件为 FALSE

6. 验证和扩展
   ├─ 比对成功和失败的情况
   ├─ 检查多个不同的参数组合
   └─ 如果需要，追溯更早的状态
```

### 关键技巧

#### 1. 使用断点统计而非单步执行

**不推荐：**
```python
# 一步一步 step_in
for i in range(1000):
    step_in()
    check_location()
```

**推荐：**
```python
# 一次性设置多个断点，运行，收集统计
breakpoints = [(323, ...), (327, ...), (328, ...)]
run_and_collect_statistics()

# 输出：
# Line 323: 18 hits
# Line 327: 0 hits   ← 直接看出问题在这里
```

**原因：**
- 单步执行太慢，信息密度低
- 断点统计一次性给出全局视图
- 更容易发现模式和规律

#### 2. 分层而不是一次性深入

**不要：**
```python
# 一次性在所有可能的地方打断点
breakpoints = [
    (323, ...), (327, ...), (328, ...),  # Layer 1
    (436, ...), (437, ...), (438, ...), (439, ...),  # Layer 2
    (474, ...), (489, ...), (493, ...),  # Layer 3
]
```

**应该：**
```python
# 第一轮：只在 Layer 1 打断点
breakpoints_layer1 = [(323, ...), (327, ...), (328, ...)]
result1 = run_and_check()

# 如果 Line 327 没命中，说明问题在 323-327 之间
# 第二轮：深入到 Line 327 调用的函数内部（Layer 2）
breakpoints_layer2 = [(436, ...), (437, ...), (438, ...), (439, ...)]
result2 = run_and_check()

# 如果 Line 439 没命中，说明问题在 438-439 之间
# 第三轮：在 Line 438 检查变量
```

**原因：**
- 每一层回答一个明确的问题
- 避免信息过载
- 根据上一层的结果决定下一层的策略

#### 3. 条件断点过滤噪音

**场景：**
- 同一行代码在不同 l 值下执行
- 同一函数用不同参数调用多次

**解决：**
```python
# 只关注 l=29 的情况
condition = "l = 29"

# 只关注特定参数组合
condition = 'l = 29 /\\ i = "1" /\\ j = "2"'

# 组合多个条件
condition = 'l = 29 /\\ i = "1" /\\ range = <<6, 7>>'
```

#### 4. 检查变量而非假设

**不要假设：**
```python
# "Line 438 被命中了，所以 state[i] = Leader 肯定是 TRUE"
# ❌ 错误！断点命中不代表条件为 TRUE
```

**应该验证：**
```python
# 在 Line 438 断点处
i_val = get_variable_value(frame_id, "i")
state_i = evaluate_expression(frame_id, f'state["{i_val}"]')
condition = (state_i == "StateLeader")

print(f"state[{i_val}] = {state_i}, condition = {condition}")
```

---

## 常见陷阱

### 陷阱 1：误解 l 的语义

❌ **错误理解：** "l=29 表示已经验证了 29 行，现在在验证第 30 行"

✅ **正确理解：** "l=29 表示正在验证第 29 行（TraceLog[29]）"

**后果：** 查看了错误的 trace 行，导致整个调试方向错误。

### 陷阱 2：混淆断点命中和条件满足

❌ **错误理解：** "Line 323 命中了 18 次，说明条件通过了 18 次"

✅ **正确理解：** "Line 323 命中了 18 次，说明 TLC 尝试了 18 次，但可能全部失败"

**后果：** 误以为条件满足，不去检查后续失败的原因。

### 陷阱 3：假设顺序执行

❌ **错误理解：** "代码按顺序执行：Line 323 → 324 → 325 → 326 → 327"

✅ **正确理解：** "所有行必须同时为 TRUE；TLC 可能以任何顺序评估"

**后果：** 对执行流程的错误预期，导致设置错误的断点位置。

### 陷阱 4：过早深入细节

❌ **错误做法：** 一开始就在函数内部的每一行打断点

✅ **正确做法：** 先粗粒度定位到相关分支，再逐层深入

**后果：** 信息过载，无法抓住重点，浪费时间。

---

## 实战检查清单

开始调试前，确认你已经：

- [ ] 理解了 l 的语义（l=N 表示正在验证 TraceLog[N]）
- [ ] 知道 logline 是定义，不是变量
- [ ] 知道 TraceLog 索引从 1 开始
- [ ] 会解读 TLC 输出（"M states generated" 表示什么）
- [ ] 理解合取是同时满足，不是顺序执行
- [ ] 知道断点命中不代表条件为 TRUE
- [ ] 准备好分层调试，而不是一次性深入

每一层调试时，确认你：

- [ ] 明确这一层要回答的问题
- [ ] 设置了合适的条件断点（过滤掉噪音）
- [ ] 收集了断点统计（而不是单步执行）
- [ ] 识别出了"最后成功"和"第一个失败"的位置
- [ ] 检查了相关变量的实际值（而不是假设）
- [ ] 理解了为什么某个条件失败
- [ ] 决定了下一步是深入还是扩展调查

---

## 总结

**核心思想：分层调试**
- 不要试图一次性找到根本原因
- 每一层回答一个明确的问题
- 根据当前层的发现决定下一层的策略

**关键工具：断点统计**
- 一次性设置多个断点
- 收集命中统计
- 识别"第一个失败"的位置

**必备技能：变量检查**
- 不要假设变量的值
- 在关键位置检查实际值
- 理解为什么条件为 FALSE

**最重要的：**
- 保持耐心，系统化地逐层深入
- 一层层剥开，总会找到不一致的地方
- 让数据（断点统计、变量值）指导你的下一步行动
