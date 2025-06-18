# TLA+ 规范生成器使用模式说明

本系统支持两种TLA+规范生成模式：

## 1. 直接模式 (Direct Mode)

**工作流程**：源代码 → TLA+ 规范

直接从源代码生成TLA+规范，适用于结构清晰、逻辑相对简单的代码。

### 特点
- 流程简单，生成速度快
- 适合小型系统或单一功能模块
- 依赖LLM对源代码的直接理解能力

### 使用方法

```bash
# 基本用法
python3 src/core/iispec_generator.py input.go output/

# 明确指定直接模式
python3 src/core/iispec_generator.py input.go output/ --mode direct
```

## 2. 草稿模式 (Draft-based Mode)

**工作流程**：源代码 → 自然语言分析草稿 → TLA+ 规范

首先生成结构化的自然语言分析，然后基于分析结果和源代码生成TLA+规范。这种两步式方法提供了更好的可控性和准确性。

### 特点
- 两步式生成，提高复杂系统的准确性
- 生成中间分析文档，便于理解和调试
- 特别适合分布式系统（如Raft共识算法）
- 确保领导者选举和日志复制等核心功能的平衡实现

### 使用方法

```bash
# 使用草稿模式
python3 src/core/iispec_generator.py input.go output/

# 明确指定草稿模式  
python3 src/core/iispec_generator.py input.go output/ --mode draft-based
```

### 输出文件
草稿模式会额外生成：
- `draft_analysis.txt`: 结构化的自然语言分析
- `generation_summary.json`: 生成过程摘要

## 配置和参数

### 模式设置
在 `config.yaml` 中设置默认模式：
```yaml
generation:
  mode: "draft-based"  # 或 "direct"
```

### 命令行参数
```bash
python3 src/core/iispec_generator.py input.go output/ \
  --mode draft-based \
  --model claude-3-5-sonnet-20241022 \
  --max-tokens 32000 \
  --temperature 0.1 \
  --log-level INFO
```

## 适用场景建议

### 直接模式适用于：
- 单一功能的算法实现
- 数据结构操作
- 简单的并发控制逻辑
- 快速原型验证

### 草稿模式适用于：
- 分布式系统协议（如Raft、Paxos）
- 复杂的并发算法
- 多组件交互系统
- 需要高质量规范的生产系统

## 系统平衡原则

对于分布式系统，两种模式都强调：
- **平衡实现**：确保领导者选举和日志复制等核心功能得到同等重视
- **完整性**：实现所有识别出的关键功能模块
- **一致性**：保持各子系统间的逻辑一致性

## 🎯 生成模式概述

系统支持两种生成模式：

### 1. **直接模式 (Direct Mode)**
- **特点**：直接从源代码生成 TLA+ 规范
- **适用场景**：简单代码、快速原型、已经很清楚抽象策略的情况
- **优势**：速度快，一次调用完成
- **劣势**：对复杂代码可能抽象不够精确

### 2. **草稿模式 (Draft-Based Mode)**
- **特点**：先生成分析草稿，再基于草稿生成 TLA+ 规范
- **适用场景**：复杂代码、需要精确控制抽象层次、高质量规范要求
- **优势**：生成质量高，抽象策略清晰，可审查中间过程
- **劣势**：需要两次 LLM 调用，耗时较长

## 🚀 使用方法

### 模式 1：直接模式

**配置文件设置：**
```yaml
generation:
  mode: "direct"
```

**命令行调用：**
```bash
# 使用配置文件中的默认设置
python3 src/iispec_generator.py input.go output/

# 明确指定直接模式
python3 src/iispec_generator.py input.go output/ --mode direct
```

### 模式 2：草稿模式

**配置文件设置：**
```yaml
generation:
  mode: "draft-based"
```

**命令行调用：**
```bash
# 使用配置文件中的设置
python3 src/iispec_generator.py input.go output/

# 明确指定草稿模式
python3 src/iispec_generator.py input.go output/ --mode draft-based
```

## 📊 输出文件对比

### 直接模式输出
```
output/
├── Generated.tla              # 生成的 TLA+ 规范
├── Generated_corrected.tla    # 错误修正后的规范（如有）
└── generation_summary.json    # 生成摘要
```

### 草稿模式输出
```
output/
├── draft_analysis.txt         # 📝 自然语言分析草稿
├── Generated.tla              # 生成的 TLA+ 规范
├── Generated_corrected.tla    # 错误修正后的规范（如有）
└── generation_summary.json    # 生成摘要
```

## 📝 草稿分析示例

草稿模式会生成类似这样的分析文件：

```
### 1. FUNCTION CLASSIFICATION

**CORE LOGIC FUNCTIONS:**
- becomeLeader: 节点成为领导者的核心逻辑
- campaign: 发起选举的核心逻辑
- stepFollower: 跟随者状态处理逻辑

**HELPER FUNCTIONS:**
- send: 消息发送功能，应抽象为状态变更
- reset: 重置功能，合并到状态初始化中

**INFRASTRUCTURE FUNCTIONS:**
- logger: 日志记录，应完全省略
- debug: 调试功能，应完全省略

### 2. CORE LOGIC ANALYSIS

**becomeLeader:**
- Purpose: 将节点状态从候选者转换为领导者
- Key Logic: 更新 state = Leader, 重置 electionElapsed
- State Changes: state, electionElapsed, leadTransferee
- TLA+ Mapping: 对应 BecomeLeader 动作

...
```

## 🎛️ 质量优化建议

### 对于复杂系统（推荐草稿模式）
```yaml
llm:
  model: "claude-sonnet-4-20250514"
  max_tokens: 32000
  temperature: 0.1

generation:
  mode: "draft-based"
  max_correction_attempts: 5
```

### 对于简单系统（可用直接模式）
```yaml
llm:
  model: "claude-3-5-sonnet-20241022"  
  max_tokens: 16000
  temperature: 0.2

generation:
  mode: "direct"
  max_correction_attempts: 3
```

## 🔍 选择指南

| 代码特征 | 推荐模式 | 理由 |
|---------|---------|------|
| 函数 < 10 个，逻辑简单 | Direct | 直接翻译效率高 |
| 函数 > 20 个，包含复杂状态 | Draft-Based | 需要精确分析和抽象 |
| 分布式系统，协议实现 | Draft-Based | 抽象层次要求高 |
| 并发控制，锁机制 | Draft-Based | 需要仔细分析关键路径 |
| 工具类，算法实现 | Direct | 逻辑相对独立 |

## 🐛 故障排除

### 草稿模式问题
1. **草稿生成失败**：降低复杂度，分段处理源代码
2. **草稿与规范不匹配**：检查 prompt 模板，确保一致性
3. **质量不如预期**：增加 max_tokens，降低 temperature

### 性能优化
1. **生成速度慢**：使用直接模式进行初步验证
2. **Token 超限**：减少源代码规模，分模块处理
3. **成本过高**：先用直接模式，确认方向后再改草稿模式

## 📈 使用建议

1. **初次使用**：从直接模式开始，了解基本效果
2. **质量追求**：对重要系统使用草稿模式
3. **迭代优化**：先草稿模式分析，再根据草稿调整直接模式
4. **混合使用**：简单部分直接模式，复杂部分草稿模式

---

**记住**：草稿模式的核心价值在于**可控的抽象过程**，让你能够审查和理解 LLM 的抽象决策，从而获得更高质量的 TLA+ 规范。 