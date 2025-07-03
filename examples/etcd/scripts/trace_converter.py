import json
import os
import sys
import argparse

class TraceConverter:
    def __init__(self, mode):
        self.mode = mode

    def convert_trace(self, input_trace):
        try:
            # Skip lines that aren't valid JSON or contain map[] notation (Go format)
            if "map[" in input_trace:
                return None
                
            action = json.loads(input_trace)
            
            if self.mode == "simple":
                output = {
                    "event": action["action"]
                }
            elif self.mode == "complete":
                # Extract terms and states for each node
                cluster_state = action.get("cluster_state", {})
                term_n1 = cluster_state.get("node_1", {}).get("term", 0)
                term_n2 = cluster_state.get("node_2", {}).get("term", 0)
                term_n3 = cluster_state.get("node_3", {}).get("term", 0)
                state_n1 = cluster_state.get("node_1", {}).get("state", "Follower")
                state_n2 = cluster_state.get("node_2", {}).get("state", "Follower")
                state_n3 = cluster_state.get("node_3", {}).get("state", "Follower")

                output = {
                    "currentTerm": [{
                        "op": "Update",
                        "path": [],
                        "args": [{"n1": term_n1, "n2": term_n2, "n3": term_n3}]
                    }],
                    "state": [{
                        "op": "Update",
                        "path": [],
                        "args": [{"n1": state_n1, "n2": state_n2, "n3": state_n3}]
                    }],
                    "event": action["action"]
                }
            else:
                raise ValueError(f"Unsupported mode: {self.mode}")

            return json.dumps(output)
        except json.JSONDecodeError:
            # Skip lines that aren't valid JSON
            return None
        except KeyError as e:
            print(f"Error: Missing key in JSON: {e}")
            return None
        except Exception as e:
            print(f"Error processing trace: {e}")
            return None

def main():
    parser = argparse.ArgumentParser(description='Trace Converter')
    parser.add_argument('-output', type=str, required=True, help='Output directory for converted traces')
    parser.add_argument('-mode', type=str, choices=['simple', 'complete'], required=True, help='Mode for trace conversion')
    parser.add_argument('-input', type=str, required=True, help='Input file containing traces to convert')
    
    args = parser.parse_args()

    # Ensure output directory exists
    os.makedirs(args.output, exist_ok=True)

    # Check if input file exists
    if not os.path.isfile(args.input):
        print(f"Error: Input file '{args.input}' does not exist.")
        sys.exit(1)

    # Create a TraceConverter instance
    converter = TraceConverter(args.mode)
    
    # Generate output filename based on input filename
    input_basename = os.path.basename(args.input)
    output_filename = f"{input_basename}"
    output_file_path = os.path.join(args.output, output_filename)
    
    # Fixed initialization configuration
    init_config = {"Server": ["n1", "n2", "n3"], "Value": [1, 2, 3], "Nil": ["Nil"], "NoLimit": ["NoLimit"]}
    
    # Read the input file and convert each valid line
    converted_lines = [json.dumps(init_config)]  # Start with the initialization config
    
    try:
        with open(args.input, 'r') as input_file:
            for line_num, line in enumerate(input_file, 1):
                line = line.strip()
                if not line:  # Skip empty lines
                    continue
                
                # Skip the first line if it contains server configuration
                if line_num == 1 and "Server" in line:
                    continue
                
                converted_trace = converter.convert_trace(line)
                if converted_trace:
                    converted_lines.append(converted_trace)
        
        # Write the converted traces to the output file
        with open(output_file_path, 'w') as output_file:
            for line in converted_lines:
                output_file.write(line + '\n')
        
        print(f"Converted {len(converted_lines)-1} traces (plus initialization config).")
        print(f"Converted traces saved to: {output_file_path}")
    
    except Exception as e:
        print(f"Error processing file: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
