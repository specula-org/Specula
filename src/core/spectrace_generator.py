#!/usr/bin/env python3
"""
Trace Validation Generator

Generates specTrace.tla and specTrace.cfg files based on a configuration file
that describes the spec's constants, variables, and actions.
Can also automatically generate configuration from TLA+ specification files using LLM.
"""

import os
import sys
import yaml
import argparse
import re
from typing import Dict, List, Any
from pathlib import Path
import re
# Import LLM client for automatic config generation
try:
    from ..llm.client import get_llm_client
    LLM_AVAILABLE = True
except ImportError:
    LLM_AVAILABLE = False


def _extract_yaml_from_response(response: str) -> str:
    """Extract YAML content from LLM response, handling markdown code blocks"""
    lines = response.split('\n')
    yaml_lines = []
    in_yaml_block = False
    
    for line in lines:
        # Look for YAML code block start - handle multiple backticks (3+ backticks)
        stripped_line = line.strip()
        if (stripped_line.startswith('```yaml') or stripped_line.startswith('```yml') or
            stripped_line.startswith('``````yaml') or stripped_line.startswith('``````yml') or
            re.match(r'^`{3,}ya?ml\s*$', stripped_line)):
            in_yaml_block = True
            continue
        # Look for code block end - handle multiple backticks
        elif (stripped_line == '```' or stripped_line == '``````' or 
              re.match(r'^`{3,}\s*$', stripped_line)) and in_yaml_block:
            break
        # If we're in a YAML block, collect the line
        elif in_yaml_block:
            yaml_lines.append(line)
        # If no code block found, look for YAML content directly
        elif line.strip().startswith('spec_name:') and not in_yaml_block:
            in_yaml_block = True
            yaml_lines.append(line)
    
    # If no YAML block was found, try to extract everything that looks like YAML
    if not yaml_lines:
        # Remove any leading/trailing markdown artifacts
        content = response.strip()
        # Remove multiple backticks patterns - enhanced to handle 6+ backticks
        content = re.sub(r'^`{3,}\w*\s*', '', content, flags=re.MULTILINE)
        content = re.sub(r'`{3,}\s*$', '', content, flags=re.MULTILINE)
        return content.strip()
    
    return '\n'.join(yaml_lines).strip()


class TraceGenerator:
    def __init__(self, config_data: Dict[str, Any]):
        self.config = config_data
        self.spec_name = config_data.get('spec_name', 'spec')
        
    def generate_default_impl(self) -> str:
        """Generate DefaultImpl function based on variables"""
        lines = ["DefaultImpl(varName) =="]
        
        variables = self.config.get('variables', [])
        constants = self.config.get('constants', [])
        # Sort by length descending to avoid partial replacements (e.g. Server vs ServerId)
        const_names = sorted([c['name'] for c in constants if c['name'] != 'Nil'], key=len, reverse=True)
        
        for i, var in enumerate(variables):
            var_name = var['name']
            default_type = var.get('default_type', 'custom')
            
            if i == 0:
                prefix = "    CASE"
            else:
                prefix = "     []"
            
            if default_type == 'mutex_map_bool':
                lines.append(f'{prefix} varName = "{var_name}" -> [m \in TraceMutexes |-> FALSE]')
            elif default_type == 'mutex_map_sequence':
                lines.append(f'{prefix} varName = "{var_name}" -> [m \in TraceMutexes |-> <<>>]')
            elif default_type == 'mutex_map_int':
                lines.append(f'{prefix} varName = "{var_name}" -> [m \in TraceMutexes |-> 0]')
            elif default_type == 'node_map_bool':
                lines.append(f'{prefix} varName = "{var_name}" -> [n \in TraceNodes |-> FALSE]')
            elif default_type == 'node_map_sequence':
                lines.append(f'{prefix} varName = "{var_name}" -> [n \in TraceNodes |-> <<>>]')
            elif default_type == 'node_map_int':
                lines.append(f'{prefix} varName = "{var_name}" -> [n \in TraceNodes |-> 0]')
            elif default_type == 'set':
                lines.append(f'{prefix} varName = "{var_name}" -> {{}}')
            elif default_type == 'int':
                lines.append(f'{prefix} varName = "{var_name}" -> 0')
            elif default_type == 'bool':
                lines.append(f'{prefix} varName = "{var_name}" -> FALSE')
            else:
                # Custom default
                default_value = var.get('default_value', '0')
                
                # Fix escaped TLA+ operators from YAML (\\in -> \in, \\E -> \E, etc.)
                # Handle common TLA+ operators that get double-escaped in YAML
                default_value = re.sub(r'\\\\in\b', r'\\in', default_value)  # \\in -> \in
                default_value = re.sub(r'\\\\E\b', r'\\E', default_value)    # \\E -> \E
                default_value = re.sub(r'\\\\A\b', r'\\A', default_value)    # \\A -> \A
                default_value = re.sub(r'\\\\/', r'\\/', default_value)      # \\/ -> \/
                default_value = re.sub(r'\\\\\\\\', r'\\\\', default_value) # \\\\ -> \\
                
                # Replace constants with Trace<Constant>
                for const_name in const_names:
                    # Use word boundaries to avoid replacing parts of other words
                    default_value = re.sub(r'\b' + re.escape(const_name) + r'\b', f'Trace{const_name}', default_value)
                
                lines.append(f'{prefix} varName = "{var_name}" -> {default_value}')
        
        return '\n'.join(lines)
    
    def generate_update_variables(self) -> str:
        """Generate UpdateVariablesImpl function"""
        lines = ["UpdateVariablesImpl(t) =="]
        
        variables = self.config.get('variables', [])
        for var in variables:
            var_name = var['name']
            lines.append(f'    /\\ IF "{var_name}" \in DOMAIN t')
            lines.append(f'       THEN {var_name}\' = UpdateVariable({var_name}, "{var_name}", t)')
            lines.append(f'       ELSE TRUE')
        
        return '\n'.join(lines)
    
    def generate_action_predicates(self) -> str:
        """Generate action predicate functions"""
        lines = []
        
        actions = self.config.get('actions', [])
        for action in actions:
            action_name = action['name']
            parameters = action.get('parameters', [])
            
            # Determine event name - remove "Handle" prefix if present
            event_name = action_name
            if action_name.startswith('Handle'):
                event_name = action_name[6:]  # Remove "Handle" prefix
            
            lines.append(f"Is{event_name} ==")
            lines.append(f'    /\\ IsEvent("{event_name}")')
            
            if parameters:
                # Generate nested existential quantifiers for each parameter
                for i, param in enumerate(parameters):
                    param_name = param['name']
                    param_source = param['source']
                    
                    # Check if source is a variable (like messages) or a constant
                    if param_source in [var['name'] for var in self.config.get('variables', [])]:
                        # It's a variable, use it directly
                        trace_source = param_source
                    else:
                        # It's a constant, convert to Trace format
                        trace_source = f"Trace{param_source}"
                    
                    # Calculate indentation: each level adds 4 spaces
                    indent = "    " + "    " * i
                    lines.append(f'{indent}/\\ \\E {param_name} \in {trace_source} :')
                
                # Generate the action call with proper indentation
                call_indent = "    " + "    " * len(parameters)
                param_names = [p['name'] for p in parameters]
                if len(param_names) == 1:
                    lines.append(f'{call_indent}{action_name}({param_names[0]})')
                else:
                    param_str = ', '.join(param_names)
                    lines.append(f'{call_indent}{action_name}({param_str})')
            else:
                # Handle action statement format
                stmt = action.get('stmt', action_name)
                if stmt != action_name:
                    # Multi-line statement, preserve formatting
                    stmt_lines = stmt.split('\n')
                    for j, stmt_line in enumerate(stmt_lines):
                        if stmt_line.strip():  # Skip empty lines
                            if j == 0:
                                lines.append(f'    /\\ {stmt_line.strip()}')
                            else:
                                lines.append(f'       {stmt_line.strip()}')
                else:
                    lines.append(f'    /\\ {action_name}')
            
            lines.append("")
        
        return '\n'.join(lines[:-1])  # Remove last empty line
    
    def generate_interactions_predicate(self) -> str:
        """Generate IsInter predicate for interactions"""
        interactions = self.config.get('interactions', []) or self.config.get('Interactions', [])
        if not interactions:
            return ""
        
        lines = ["IsInter == "]
        lines.append("    /\\ pc # Nil")
        lines.append("    /\\ UNCHANGED <<l>>")
        
        for i, interaction in enumerate(interactions):
            interaction_name = interaction['name']
            if i == 0:
                lines.append(f"    /\\ \\/ {interaction_name}")
            else:
                lines.append(f"       \\/ {interaction_name}")
        
        return '\n'.join(lines)
    
    def generate_trace_next(self) -> str:
        """Generate TraceNextImpl function"""
        lines = ["TraceNextImpl =="]
        
        actions = self.config.get('actions', [])
        for i, action in enumerate(actions):
            action_name = action['name']
            # Determine event name - remove "Handle" prefix if present
            event_name = action_name
            if action_name.startswith('Handle'):
                event_name = action_name[6:]  # Remove "Handle" prefix
                
            if i == 0:
                lines.append(f"    \\/ Is{event_name}")
            else:
                lines.append(f"    \\/ Is{event_name}")
        
        # Add interactions if they exist
        interactions = self.config.get('interactions', []) or self.config.get('Interactions', [])
        if interactions:
            lines.append("    \\/ IsInter")
        
        return '\n'.join(lines)
    
    def generate_constants_section(self) -> str:
        """Generate CONSTANTS section for TLA file"""
        lines = ["CONSTANTS"]
        
        constants = self.config.get('constants', [])
        for constant in constants:
            const_name = constant['name']
            const_value = constant.get('value', '')
            if const_value:
                lines.append(f'    {const_name} = {const_value}')
            else:
                lines.append(f'    {const_name}')
        
        # Add trace-related constants
        lines.extend([
            '    \\* Trace configuration',
            '    Nil <- TraceNil',
            '    Vars <- vars',
            '    Default <- DefaultImpl',
            '    BaseInit <- Init',
            '    UpdateVariables <- UpdateVariablesImpl',
            '    TraceNext <- TraceNextImpl'
        ])
        
        return '\n'.join(lines)
    
    def generate_trace_sources(self) -> str:
        """Generate trace source definitions automatically from constants"""
        lines = []
        
        constants = self.config.get('constants', [])
        for constant in constants:
            const_name = constant['name']
            # Skip Nil as it's handled specially
            if const_name == 'Nil':
                continue
            trace_name = f"Trace{const_name}"
            lines.append(f"{trace_name} == ToSet(Trace[1].{const_name})")
        
        return '\n'.join(lines)
    
    def generate_tla_file(self) -> str:
        """Generate the complete TLA+ file"""
        action_predicates = self.generate_action_predicates()
        interactions_predicate = self.generate_interactions_predicate()
        
        # Combine action predicates and interactions predicate
        all_predicates = action_predicates
        if interactions_predicate:
            all_predicates += "\n\n" + interactions_predicate
        
        template = f"""--------------------------- MODULE specTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, {self.spec_name}, TraceSpec, TVOperators


TraceNil == "null"

(* Extract system configuration from first trace line *)
{self.generate_trace_sources()}

(* Default variable initialization *)
{self.generate_default_impl()}

(* State variable update logic *)
{self.generate_update_variables()}

(* Action event matching *)

{all_predicates}

(* State transition definition *)
{self.generate_trace_next()}


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\\ [][Next \\/ ComposedNext]_vars

=============================================================================

"""
        return template
    
    def generate_cfg_file(self) -> str:
        """Generate the TLC configuration file"""
        cfg_lines = ["CONSTANTS"]
        
        # Add user-defined constants with their values
        constants = self.config.get('constants', [])
        for constant in constants:
            const_name = constant['name']
            const_value = constant.get('value', '')
            if const_value:
                cfg_lines.append(f"    {const_name} = {const_value}")
            else:
                cfg_lines.append(f"    {const_name}")
        
        # Add base configuration constants (always present)
        cfg_lines.extend([
            "    Nil <- TraceNil",
            "    Vars <- vars",
            "    Default <- DefaultImpl", 
            "    BaseInit <- Init",
            "    UpdateVariables <- UpdateVariablesImpl",
            "    TraceNext <- TraceNextImpl"
        ])
        
        # Add other standard configuration
        cfg_lines.extend([
            "",
            "SPECIFICATION TraceSpec",
            "",
            "VIEW TraceView",
            "",
            "POSTCONDITION TraceAccepted",
            "",
            "CHECK_DEADLOCK FALSE"
        ])
        
        return '\n'.join(cfg_lines)
    
    def generate_files(self, output_dir: str):
        """Generate both TLA+ and CFG files"""
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Generate TLA+ file
        tla_content = self.generate_tla_file()
        tla_file = output_path / "specTrace.tla"
        with open(tla_file, 'w') as f:
            f.write(tla_content)
        
        # Generate CFG file
        cfg_content = self.generate_cfg_file()
        cfg_file = output_path / "specTrace.cfg"
        with open(cfg_file, 'w') as f:
            f.write(cfg_content)
        
        print(f"Generated files:")
        print(f"  - {tla_file}")
        print(f"  - {cfg_file}")


def generate_config_from_tla(tla_file: str, cfg_file: str, prompt_file: str = None, config_path: str = None) -> Dict[str, Any]:
    """
    Automatically generate configuration from TLA+ and CFG files using LLM
    
    Args:
        tla_file: Path to the TLA+ specification file
        cfg_file: Path to the TLC configuration file  
        prompt_file: Path to the prompt template file (optional)
        config_path: Path to the LLM configuration file (optional)
        
    Returns:
        Generated configuration as dictionary
    """
    if not LLM_AVAILABLE:
        raise ImportError("LLM client not available. Please install required dependencies.")
    
    # Read TLA+ and CFG files
    try:
        with open(tla_file, 'r') as f:
            tla_content = f.read()
    except Exception as e:
        raise Exception(f"Error reading TLA+ file {tla_file}: {e}")
    
    try:
        with open(cfg_file, 'r') as f:
            cfg_content = f.read()
    except Exception as e:
        raise Exception(f"Error reading CFG file {cfg_file}: {e}")
    
    # Read prompt template
    if prompt_file is None:
        # Use default prompt file from config
        from ..utils.config import get_config
        config = get_config(config_path)
        prompts_dir = config.get('paths', {}).get('prompts_dir', 'src/prompts')
        prompt_file = Path(prompts_dir) / "step4_trace_config_generation.txt"
    
    try:
        with open(prompt_file, 'r') as f:
            prompt_template = f.read()
    except Exception as e:
        raise Exception(f"Error reading prompt file {prompt_file}: {e}")
    
    # Prepare input content
    input_content = f"""TLA+ Specification (.tla file):
```tla
{tla_content}
```

TLC Configuration (.cfg file):
```cfg
{cfg_content}
```"""
    
    # Get LLM client and generate configuration
    try:
        llm_client = get_llm_client(config_path)
        response = llm_client.get_completion(prompt_template, input_content)
        
        # Parse YAML response
        # Extract YAML content from markdown code blocks
        yaml_content = _extract_yaml_from_response(response)
        
        # Validate YAML content before parsing
        if not yaml_content.strip():
            raise Exception("No YAML content extracted from LLM response")
        
        try:
            config_data = yaml.safe_load(yaml_content)
            return config_data
        except yaml.YAMLError as e:
            # Provide more detailed error information
            raise Exception(f"YAML parsing error: {e}\n\nExtracted YAML content:\n{yaml_content[:500]}...")
        
    except Exception as e:
        raise Exception(f"Error generating configuration with LLM: {e}")


def main():
    parser = argparse.ArgumentParser(description='Generate trace validation files')
    parser.add_argument('--config', help='Input configuration file (YAML)')
    parser.add_argument('--tla', help='Input TLA+ specification file (.tla)')
    parser.add_argument('--cfg', help='Input TLC configuration file (.cfg)')
    parser.add_argument('--prompt', help='Prompt template file (optional)')
    parser.add_argument('--llm-config', help='LLM configuration file (optional)')
    parser.add_argument('output_dir', help='Output directory for generated files')
    parser.add_argument('--auto-config', help='Output path for auto-generated config file (optional)')
    
    args = parser.parse_args()
    
    config_data = None
    
    # Check input method
    if args.config:
        # Load from existing configuration file
        try:
            with open(args.config, 'r') as f:
                config_data = yaml.safe_load(f)
        except Exception as e:
            print(f"Error loading config file: {e}")
            sys.exit(1)
    elif args.tla and args.cfg:
        # Generate configuration from TLA+ and CFG files using LLM
        if not LLM_AVAILABLE:
            print("Error: LLM client not available. Please install required dependencies or provide a config file.")
            sys.exit(1)
        
        try:
            print("Generating configuration from TLA+ and CFG files...")
            config_data = generate_config_from_tla(
                args.tla, 
                args.cfg, 
                args.prompt, 
                args.llm_config
            )
            print("Configuration generated successfully.")
            
            # Save auto-generated config if requested
            if args.auto_config:
                # Create directory if it doesn't exist
                config_path = Path(args.auto_config)
                config_path.parent.mkdir(parents=True, exist_ok=True)
                
                with open(config_path, 'w') as f:
                    yaml.dump(config_data, f, default_flow_style=False, allow_unicode=True)
                print(f"Auto-generated config saved to: {args.auto_config}")
                
        except Exception as e:
            print(f"Error generating configuration: {e}")
            sys.exit(1)
    else:
        print("Error: Must provide either --config file or both --tla and --cfg files")
        parser.print_help()
        sys.exit(1)
    
    # Generate files
    try:
        generator = TraceGenerator(config_data)
        generator.generate_files(args.output_dir)
    except Exception as e:
        print(f"Error generating files: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main() 