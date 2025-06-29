#!/usr/bin/env python3

import json
import sys
from collections import defaultdict
from datetime import datetime

def analyze_traces(filename):
    """分析 raft trace 文件并生成报告"""
    
    with open(filename, 'r') as f:
        traces = [json.loads(line.strip()) for line in f if line.strip()]
    
    print("=== Raft Core Algorithm Trace Analysis ===\n")
    
    # 基本统计
    print(f"总事件数: {len(traces)}")
    print(f"时间跨度: {(traces[-1]['timestamp'] - traces[0]['timestamp']) / 1e9:.2f} 秒\n")
    
    # 按动作分类
    action_counts = defaultdict(int)
    node_events = defaultdict(list)
    state_transitions = []
    
    for trace in traces:
        action = trace['action']
        action_counts[action] += 1
        
        # 按节点分组
        if 'data' in trace and 'node_id' in trace['data']:
            node_id = trace['data']['node_id']
            node_events[node_id].append(trace)
        
        # 记录状态转换
        if action in ['become_follower', 'become_candidate', 'become_leader']:
            state_transitions.append({
                'timestamp': trace['timestamp'],
                'node_id': trace['data']['node_id'],
                'action': action,
                'term': trace['data']['term']
            })
    
    # 打印事件统计
    print("=== 事件类型统计 ===")
    for action, count in sorted(action_counts.items()):
        print(f"  {action}: {count}")
    print()
    
    # 节点行为分析
    print("=== 各节点行为分析 ===")
    for node_id in sorted(node_events.keys()):
        events = node_events[node_id]
        print(f"\n节点 {node_id}:")
        print(f"  总事件数: {len(events)}")
        
        # 最后状态
        last_state_event = None
        for event in reversed(events):
            if event['action'] in ['become_follower', 'become_candidate', 'become_leader']:
                last_state_event = event
                break
        
        if last_state_event:
            state = last_state_event['action'].replace('become_', '')
            term = last_state_event['data']['term']
            print(f"  最终状态: {state} (Term {term})")
        
        # 选举尝试次数
        election_attempts = sum(1 for e in events if e['action'] == 'Step' and 
                              'data' in e and 'MsgHup' in str(e['data']))
        print(f"  选举尝试次数: {election_attempts}")
        
        # tick 事件统计
        tick_events = [e for e in events if e['action'] == 'tickElection']
        print(f"  选举 tick 次数: {len(tick_events)}")
    
    # 状态转换时间线
    if state_transitions:
        print("\n=== 状态转换时间线 ===")
        start_time = traces[0]['timestamp']
        
        for transition in state_transitions:
            relative_time = (transition['timestamp'] - start_time) / 1e9
            state = transition['action'].replace('become_', '').upper()
            print(f"  {relative_time:6.2f}s: 节点{transition['node_id']} -> {state} (Term {transition['term']})")
    
    # 分析 raft 算法关键行为
    print("\n=== Raft 算法行为分析 ===")
    
    # 1. 选举超时检测
    election_timeouts = []
    for trace in traces:
        if (trace['action'] == 'Step' and 'data' in trace and 
            'receive_message' in str(trace).lower() and 'msghup' in str(trace).lower()):
            election_timeouts.append(trace)
    
    print(f"检测到选举超时事件: {len(election_timeouts)}")
    
    # 2. PreVote 机制
    prevote_events = [t for t in state_transitions if 'PreCandidate' in str(t)]
    print(f"PreVote 状态转换: {len(prevote_events)}")
    
    # 3. 领导者选举
    leader_elections = [t for t in state_transitions if t['action'] == 'become_leader']
    print(f"成功的领导者选举: {len(leader_elections)}")
    
    if leader_elections:
        print("领导者选举详情:")
        for election in leader_elections:
            relative_time = (election['timestamp'] - start_time) / 1e9
            print(f"  {relative_time:6.2f}s: 节点{election['node_id']} 成为领导者 (Term {election['term']})")
    
    # 4. 消息传递分析
    message_events = [t for t in traces if t['action'] in ['send_message', 'receive_message']]
    print(f"总消息传递事件: {len(message_events)}")
    
    if message_events:
        message_types = defaultdict(int)
        for msg in message_events:
            if 'data' in msg and 'msg_type' in msg['data']:
                message_types[msg['data']['msg_type']] += 1
        
        print("消息类型分布:")
        for msg_type, count in sorted(message_types.items()):
            print(f"  {msg_type}: {count}")
    
    print(f"\n=== 分析完成 ===")
    print("这些 trace 数据展示了真实的 Raft 算法执行过程:")
    print("- 节点初始化和状态转换")
    print("- 选举超时机制")
    print("- PreVote 预选举协议") 
    print("- 消息传递和协调")
    print("- 分布式一致性算法的关键时序")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("用法: python trace_analyzer.py <trace_file>")
        print("示例: python trace_analyzer.py core_raft_trace.ndjson")
        sys.exit(1)
    
    trace_file = sys.argv[1]
    try:
        analyze_traces(trace_file)
    except Exception as e:
        print(f"分析失败: {e}")
        sys.exit(1) 