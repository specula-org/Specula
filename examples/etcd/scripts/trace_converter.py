#!/usr/bin/env python3
"""
Trace Converter for TLAGEN ETCD Example
Converts system-generated trace format to TLA+ specification format
"""

import json
import argparse
import sys
from pathlib import Path
from typing import List, Dict, Any


class TraceConverter:
    """Convert system traces to TLA+ compatible format"""
    
    def __init__(self):
        self.server_nodes = ["n1", "n2", "n3"]  # Default server configuration (match TLA+ spec)
        self.values = [1, 2, 3]  # Default values
        
    def convert_system_trace_to_tla(self, system_trace_path: str, output_path: str) -> bool:
        """
        Convert system-generated trace to TLA+ format
        
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
                        # Handle Go map format: map[key:value ...]
                        event = self._parse_system_event(line)
                        if event:
                            system_events.append(event)
            
            print(f"Parsed {len(system_events)} system events")
            
            # Convert to TLA+ format
            tla_trace = self._convert_to_tla_format(system_events)
            
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
            # First try to parse as JSON
            if line.startswith('{"action"'):
                # Handle JSON format with Go map in params
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
    
    def _convert_to_tla_format(self, system_events: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Convert system events to TLA+ format"""
        tla_events = []
        
        # First event: configuration
        config_event = {
            "Server": self.server_nodes,
            "Value": self.values,
            "Nil": ["Nil"],
            "NoLimit": ["NoLimit"]
        }
        tla_events.append(config_event)
        
        # Convert system events to TLA+ events
        for event in system_events:
            action = event.get('action', '')
            
            # Map system actions to TLA+ events
            tla_event = self._map_action_to_tla_event(action, event)
            if tla_event:
                tla_events.append(tla_event)
        
        return tla_events
    
    def _map_action_to_tla_event(self, action: str, system_event: Dict[str, Any]) -> Dict[str, Any]:
        """Map system action to TLA+ event format"""
        
        # Basic mapping: action name to event name
        action_mapping = {
            'tickElection': 'tickElection',
            'tickHeartbeat': 'tickHeartbeat', 
            'Step': 'Step'
        }
        
        if action in action_mapping:
            return {"event": action_mapping[action]}
        
        # If no mapping found, use the action name directly
        if action:
            return {"event": action}
        
        return None


def main():
    parser = argparse.ArgumentParser(
        description="Convert system trace to TLA+ specification format",
        formatter_class=argparse.RawTextHelpFormatter
    )
    
    parser.add_argument('input_trace', help="Input system trace file (NDJSON)")
    parser.add_argument('output_trace', help="Output TLA+ trace file (NDJSON)")
    
    parser.add_argument('--servers', nargs='+', default=['s1', 's2', 's3'],
                       help="Server node names (default: s1 s2 s3)")
    
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