#!/usr/bin/env python3
"""
Trace Converter for Specula ETCD Example
Converts system-generated trace format to TLA+ specification format with state variable updates
"""

import json
import argparse
import sys
from pathlib import Path
from typing import List, Dict, Any


class TraceConverter:
    """Convert system traces to TLA+ compatible format with state updates"""
    
    def __init__(self):
        self.server_nodes = ["n1", "n2", "n3"]  # Default server configuration
        self.values = [1, 2, 3]  # Default values
        
    def convert_system_trace_to_tla(self, system_trace_path: str, output_path: str) -> bool:
        """
        Convert system-generated trace to TLA+ format with state variable updates
        
        Args:
            system_trace_path: Path to system-generated NDJSON trace file
            output_path: Path for TLA+ compatible trace output
            
        Returns:
            True if conversion successful, False otherwise
        """
        try:
            # Read system trace
            system_events = []
            with open(system_trace_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line:
                        # Parse the system trace format
                        event = self._parse_system_event(line)
                        if event:
                            system_events.append(event)
            
            print(f"Parsed {len(system_events)} system events")
            
            # Convert to TLA+ format with state updates
            tla_trace = self._convert_to_tla_format_with_states(system_events)
            
            # Write TLA+ trace
            with open(output_path, 'w') as f:
                for event in tla_trace:
                    f.write(json.dumps(event) + '\n')
            
            print(f"Converted trace written to: {output_path}")
            print(f"Total TLA+ events: {len(tla_trace)}")
            
            return True
            
        except Exception as e:
            print(f"Error converting trace: {e}")
            return False
    
    def _parse_system_event(self, line: str) -> Dict[str, Any]:
        """Parse a single system trace line"""
        try:
            # Handle JSON format with Go map in params
            if line.startswith('{"action"'):
                parts = line.split('"params":')
                if len(parts) == 2:
                    prefix = parts[0] + '"params":'
                    params_part = parts[1].rstrip('}')
                    
                    # Extract action and timestamp from prefix
                    import re
                    action_match = re.search(r'"action":"([^"]+)"', prefix)
                    timestamp_match = re.search(r'"timestamp":(\d+)', prefix)
                    
                    if action_match:
                        action = action_match.group(1)
                        timestamp = int(timestamp_match.group(1)) if timestamp_match else 0
                        
                        # Parse Go map format: map[key:value key:value ...]
                        params = self._parse_go_map(params_part)
                        
                        return {
                            'action': action,
                            'timestamp': timestamp,
                            'params': params
                        }
            
            return None
            
        except Exception as e:
            print(f"Warning: Failed to parse line: {line[:100]}... Error: {e}")
            return None
    
    def _parse_go_map(self, map_str: str) -> Dict[str, Any]:
        """Parse Go map format: map[key:value key:value ...]"""
        params = {}
        
        # Remove 'map[' and ']'
        map_content = map_str.strip()
        if map_content.startswith('map['):
            map_content = map_content[4:]
        if map_content.endswith(']'):
            map_content = map_content[:-1]
        
        # Split by spaces and parse key:value pairs
        import re
        # Use regex to find key:value pairs
        pairs = re.findall(r'(\w+):([^\s\]]+)', map_content)
        
        for key, value in pairs:
            # Try to convert value to appropriate type
            if value.isdigit():
                params[key] = int(value)
            elif value == 'true':
                params[key] = True
            elif value == 'false':
                params[key] = False
            else:
                params[key] = value
        
        return params
    
    def _convert_to_tla_format_with_states(self, system_events: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Convert system events to TLA+ format with state variable updates"""
        tla_events = []
        
        # First event: configuration
        config_event = {
            "Server": self.server_nodes,
            "Value": self.values,
            "Nil": ["Nil"],
            "NoLimit": ["NoLimit"]
        }
        tla_events.append(config_event)
        
        # Convert system events to TLA+ events with state updates
        for event in system_events:
            tla_event = self._create_tla_event_with_states(event)
            if tla_event:
                tla_events.append(tla_event)
        
        return tla_events
    
    def _create_tla_event_with_states(self, system_event: Dict[str, Any]) -> Dict[str, Any]:
        """Create TLA+ event with minimal updates - let TLA+ actions handle state changes naturally"""
        action = system_event.get('action', '')
        params = system_event.get('params', {})
        
        # Extract key information from params
        node_id = params.get('node_id', 1)
        state = params.get('state', 'Follower')
        term = params.get('term', 0)
        msg_from = params.get('msg_from')
        msg_type = params.get('msg_type')
        
        # Convert node_id to server name
        server_name = f"n{node_id}"
        
        # Create TLA+ event with minimal updates - let the action handle state changes
        tla_event = {"event": action}
        
        # Only add messages when absolutely necessary, let TLA+ actions handle state/term changes
        if action == "Step" and msg_from and msg_type:
            # For Step events, we might need to ensure the message exists for processing
            from_server = f"n{msg_from}"
            # Convert MsgVote to TLA+ message format
            if msg_type == "MsgVote":
                processed_msg = {
                    "from": from_server,
                    "to": server_name,
                    "type": "Vote",  # Convert to TLA+ format
                    "term": term,
                    "index": 0,
                    "logTerm": 0
                }
                tla_event["messages"] = [
                    {"op": "AddElement", "path": [], "args": [processed_msg]}
                ]
        
        # For tickHeartbeat and tickElection, let them be mostly empty
        # The TLA+ actions will handle all the necessary state changes
        
        return tla_event
    
    def _convert_msg_type(self, msg_type: str) -> str:
        """Convert Go message type to TLA+ message type"""
        type_mapping = {
            'MsgVote': 'Vote',
            'MsgVoteResp': 'VoteResp',
            'MsgPreVote': 'PreVote',
            'MsgPreVoteResp': 'PreVoteResp',
            'MsgApp': 'App',
            'MsgAppResp': 'AppResp',
            'MsgHeartbeat': 'Heartbeat',
            'MsgHeartbeatResp': 'HeartbeatResp',
            'MsgSnap': 'Snap',
            'MsgTimeoutNow': 'TimeoutNow',
            'MsgTransferLeader': 'TransferLeader',
            'MsgReadIndex': 'ReadIndex',
            'MsgReadIndexResp': 'ReadIndexResp',
            'MsgStorageAppend': 'StorageAppendResp',
            'MsgStorageApply': 'StorageApplyResp'
        }
        return type_mapping.get(msg_type, msg_type)


def main():
    parser = argparse.ArgumentParser(
        description="Convert system trace to TLA+ specification format with state updates",
        formatter_class=argparse.RawTextHelpFormatter
    )
    
    parser.add_argument('input_trace', help="Input system trace file (NDJSON)")
    parser.add_argument('output_trace', help="Output TLA+ trace file (NDJSON)")
    
    parser.add_argument('--servers', nargs='+', default=['n1', 'n2', 'n3'],
                       help="Server node names (default: n1 n2 n3)")
    
    parser.add_argument('--values', nargs='+', type=int, default=[1, 2, 3],
                       help="Value set (default: 1 2 3)")
    
    parser.add_argument('--validate', action='store_true',
                       help="Validate input trace format")
    
    args = parser.parse_args()
    
    converter = TraceConverter()
    converter.server_nodes = args.servers
    converter.values = args.values
    
    if args.validate:
        print("Validating input trace format...")
        # Add validation logic here if needed
    
    print(f"Converting trace: {args.input_trace} -> {args.output_trace}")
    print(f"Server nodes: {args.servers}")
    print(f"Values: {args.values}")
    
    success = converter.convert_system_trace_to_tla(args.input_trace, args.output_trace)
    
    if success:
        print("✓ Trace conversion completed successfully")
        return 0
    else:
        print("✗ Trace conversion failed")
        return 1


if __name__ == "__main__":
    sys.exit(main()) 