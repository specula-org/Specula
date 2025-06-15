import os
import yaml
import subprocess
import re

def tla_sany(file_path):
    # Run tla_sany command
    result = subprocess.run(['tla_sany', file_path], capture_output=True, text=True)
    output = result.stdout + result.stderr
    print(output)
    return output
    
def process_actions(yaml_file_path: str, output_dir: str):
    # Read yaml file
    with open(yaml_file_path, 'r') as f:
        yaml_data = yaml.safe_load(f)
    
    # Get yaml filename (without extension) as directory name
    base_name = os.path.splitext(os.path.basename(yaml_file_path))[0]
    # Create action directory
    action_dir = os.path.join(output_dir, f"{base_name}_actions")
    # Create output directory
    os.makedirs(action_dir, exist_ok=True)
    file_name = []
    # Process each action
    for action in yaml_data.get('code', []):
        # Split into lines
        lines = action.strip().split('\n')                  
        
        # Safe filtering (list comprehension)
        lines = [line for line in lines 
                if line.strip() not in {'```tla+', '```tla', '```'}  # Remove code block markers
                and not line.strip().startswith('\\*')]  # Remove escaped comments
        
        if len(lines) == 0:
            continue
        # Get action name (content before first == in first line)
        action_name = lines[0].split('==')[0].strip()
        
        add_Module(action_name.split('(')[0], lines)

        # Write to file
        action_file = os.path.join(action_dir, f"{action_name.split('(')[0]}.tla")
        with open(action_file, 'w') as f:
            f.write('\n'.join(lines))
        file_name.append(base_name + "_actions/" + action_name.split('(')[0] + ".tla")
    return file_name

def add_Module(module_name: str, lines: list):
    # Check if exists before inserting
    ext_flag = False
    module_flag = False
    end_flag = False
    for line in lines:
        if line.startswith("EXTENDS"):
            ext_flag = True
        elif line.startswith("----MODULE"):
            module_flag = True
        elif line.startswith("====\n"):
            end_flag = True
    if not ext_flag:
        lines.insert(0, "EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals")
    if not module_flag:
        lines.insert(0, f"----MODULE {module_name} ----")
    if not end_flag:
        lines.append("====\n")

def add_var_func(file_path: str):
    add_var(file_path)
    add_func(file_path)

def add_var(file_path: str):
    # Use regular expression to extract variable names after Unknown operator
    output = tla_sany(file_path)
    pattern = r"Unknown operator: `([^']*)'."
    matches = re.findall(pattern, output)
    
    # Convert to set for deduplication
    var_set = set(matches)
    
    if var_set:
        # Read original file content
        with open(file_path, 'r') as f:
            lines = f.readlines()
        
        # Check if VARIABLES declaration already exists
        var_line_idx = -1
        for i, line in enumerate(lines):
            if line.startswith("VARIABLES"):
                var_line_idx = i
                break
                
        # Construct new VARIABLES declaration
        var_str = "VARIABLES " + ", ".join(var_set) + "\n"
        
        # Replace if exists, otherwise insert at line 2
        if var_line_idx >= 0:
            lines[var_line_idx] = var_str
        else:
            lines.insert(2, var_str)
        
        # Write back to file
        with open(file_path, 'w') as f:
            f.writelines(lines)
    else :
        # Write empty line at line 3
        with open(file_path, 'r') as f:
            lines = f.readlines()
            lines.insert(2, "\n")
        # Write back to file
        with open(file_path, 'w') as f:
            f.writelines(lines)

def add_func(file_path: str):
    # Use regular expression to extract function names that require 0 arguments
    output = tla_sany(file_path)
    pattern = r"The operator ([^\s]*) requires 0 arguments"
    matches = re.findall(pattern, output)
    # Deduplicate matches
    matches = list(set(matches))
    if matches:
        # Read original file content
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # Find VARIABLES line
        for i, line in enumerate(lines):
            if line.startswith("VARIABLES"):
                # Get all variables
                vars = [v.strip() for v in line[9:].strip().split(",")]
                # Remove matched function names
                vars = [v for v in vars if v not in matches]
                # Rewrite VARIABLES line
                if vars:
                    lines[i] = "VARIABLES " + ", ".join(vars) + "\n"
                else:
                    lines.pop(i)
                break
                
        # Insert function definitions at line 3
        # Check if same function definitions already exist
        existing_funcs = []
        for line in lines:
            if "==" in line:
                func_name = line.split("==")[0].strip()
                if "(" in func_name:
                    existing_funcs.append(func_name.split("(")[0].strip())
        func_defs = []
        for func in matches:
            # Check parameter count when function is called
            param_pattern = rf"{func}\((.*?)\)"
            param_matches = re.findall(param_pattern, "".join(lines))
            if param_matches:
                # Get parameter count from first call
                params = [p.strip() for p in param_matches[0].split(",") if p.strip()]
                param_count = len(params)
                # Generate parameter list based on parameter count
                param_list = ", ".join([f"x{i+1}" for i in range(param_count)])
                func_defs.append(f"{func}({param_list}) == UNCHANGED <<{param_list}>>\n")
            else:
                # error
                print(f"Error: {func} has no parameters")
        
        if func_defs and func_defs not in existing_funcs:
            lines[3:3] = func_defs
            
        # Write back to file
        with open(file_path, 'w') as f:
            f.writelines(lines)

def complete_actions(input_dir: str, output_dir: str):
    file_name = process_actions(input_dir, output_dir)
    for name in file_name:
        add_var_func(os.path.join(output_dir, name))
    
