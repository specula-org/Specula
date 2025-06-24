# Spectrace Generator 测试文档

## 功能概述

`spectrace_generator.py` 现在支持两种工作模式：

### 1. 基于现有配置文件生成（原有功能增强）

```bash
python3 -m src.core.spectrace_generator --config examples/etcd/spec/step5/raft_config.yaml output_dir
```

**新增支持的配置文件格式特性：**
- 支持 `interactions` 字段（用于中间状态处理）
- 智能处理变量与常量的参数源（如 `messages` 变量）
- 改进的多行语句处理

### 2. 自动生成配置文件（新功能）

```bash
python3 -m src.core.spectrace_generator \
    --tla examples/etcd/spec/step4/Raft.tla \
    --cfg examples/etcd/spec/step4/Raft.cfg \
    --auto-config auto_generated_config.yaml \
    output_dir
```

此模式会：
1. 读取 TLA+ 规约文件和配置文件
2. 使用大模型（基于 `src/prompts/step5_trace_config_generation.txt` 提示词）自动分析并生成配置
3. 可选保存自动生成的配置文件
4. 继续生成 specTrace.tla 和 specTrace.cfg

## 配置文件格式示例

```yaml
spec_name: Raft
constants:
- name: Server
  value: '{"n1", "n2", "n3"}'
- name: Value  
  value: '{"v1", "v2", "v3"}'
variables:
- name: currentTerm
  default_value: '[s \\in Server |-> 0]'
- name: messages
  default_value: '{}'
actions:
- name: HandletickElection
  parameters:
  - name: s
    source: Server  # 常量源
  stmt: HandletickElection(s)
- name: Step
  parameters:
  - name: s
    source: Server
  - name: m
    source: messages  # 变量源，会自动识别
  stmt: |
    /\ pc = Nil
    /\ Step(s, m) 
    /\ UNCHANGED <<pc, info, stack>>
interactions:  # 新功能：中间状态处理
- name: HandletickElection_1
- name: HandletickHeartbeat_1
```

## 关键改进

1. **智能参数源识别**：自动区分变量和常量作为参数源
2. **Interactions 支持**：生成 `IsInter` 谓词处理中间状态
3. **多行语句处理**：正确格式化复杂的 action 语句
4. **LLM 集成**：使用大模型自动从 TLA+ 文件生成配置

## 生成的文件

### specTrace.tla
- 包含所有 action predicates (Is*)
- 如果有 interactions，会生成 IsInter 谓词
- 正确的 TraceNextImpl 定义

### specTrace.cfg  
- 标准的 TLC 配置
- 包含所有常量和配置项 