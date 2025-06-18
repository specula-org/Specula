#!/usr/bin/env python3
"""
Trace Validation Generator

Generates specTrace.tla and specTrace.cfg files based on a configuration file
that describes the spec's constants, variables, and actions.
"""

import os
import sys
import yaml
import argparse
from typing import Dict, List, Any
from pathlib import Path


class TraceGenerator:
    def __init__(self, config_data: Dict[str, Any]):
        self.config = config_data
        self.spec_name = config_data.get('spec_name', 'spec')
        
    def generate_default_impl(self) -> str:
        """Generate DefaultImpl function based on variables"""
        lines = ["DefaultImpl(varName) ==", "    CASE"]
        
        variables = self.config.get('variables', [])
        for i, var in enumerate(variables):
            var_name = var['name']
            default_type = var.get('default_type', 'custom')
            
            if i > 0:
                lines.append("     []")
            
            if default_type == 'mutex_map_bool':
                lines.append(f'        varName = "{var_name}" -> [m \\in TraceMutexes |-> FALSE]')
            elif default_type == 'mutex_map_sequence':
                lines.append(f'        varName = "{var_name}" -> [m \\in TraceMutexes |-> <<>>]')
            elif default_type == 'mutex_map_int':
                lines.append(f'        varName = "{var_name}" -> [m \\in TraceMutexes |-> 0]')
            elif default_type == 'set':
                lines.append(f'        varName = "{var_name}" -> {{}}')
            elif default_type == 'int':
                lines.append(f'        varName = "{var_name}" -> 0')
            elif default_type == 'bool':
                lines.append(f'        varName = "{var_name}" -> FALSE')
            else:
                # Custom default
                default_value = var.get('default_value', '0')
                lines.append(f'        varName = "{var_name}" -> {default_value}')
        
        return '\n'.join(lines)
    
    def generate_update_variables(self) -> str:
        """Generate UpdateVariablesImpl function"""
        lines = ["UpdateVariablesImpl(t) =="]
        
        variables = self.config.get('variables', [])
        for var in variables:
            var_name = var['name']
            lines.append(f'    /\\ IF "{var_name}" \\in DOMAIN t')
            lines.append(f'       THEN {var_name}\' = UpdateVariable({var_name}, "{var_name}", t)')
            lines.append(f'       ELSE TRUE')
        
        return '\n'.join(lines)
    
    def generate_action_predicates(self) -> str:
        """Generate action predicate functions"""
        lines = []
        
        actions = self.config.get('actions', [])
        for action in actions:
            action_name = action['name']
            event_name = action.get('event_name', action_name)
            parameters = action.get('parameters', [])
            
            lines.append(f"Is{action_name} ==")
            lines.append(f'    /\\ IsEvent("{event_name}")')
            
            if parameters:
                for param in parameters:
                    param_name = param['name']
                    param_source = param['source']
                    lines.append(f'    /\\ \\E {param_name} \\in {param_source} :')
                
                # Generate the action call
                param_names = [p['name'] for p in parameters]
                if len(param_names) == 1:
                    lines.append(f'        {action_name}({param_names[0]})')
                else:
                    param_str = ', '.join(param_names)
                    lines.append(f'        {action_name}({param_str})')
            else:
                lines.append(f'        {action_name}')
            
            lines.append("")
        
        return '\n'.join(lines[:-1])  # Remove last empty line
    
    def generate_trace_next(self) -> str:
        """Generate TraceNextImpl function"""
        lines = ["TraceNextImpl =="]
        
        actions = self.config.get('actions', [])
        for i, action in enumerate(actions):
            action_name = action['name']
            if i == 0:
                lines.append(f"    \\/ Is{action_name}")
            else:
                lines.append(f"    \\/ Is{action_name}")
        
        return '\n'.join(lines)
    
    def generate_constants_section(self) -> str:
        """Generate CONSTANTS section"""
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
        """Generate trace source definitions"""
        lines = []
        
        sources = self.config.get('trace_sources', [])
        for source in sources:
            source_name = source['name']
            source_field = source['field']
            lines.append(f"{source_name} == ToSet(Trace[1].{source_field})")
        
        return '\n'.join(lines)
    
    def generate_tla_file(self) -> str:
        """Generate the complete TLA+ file"""
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

{self.generate_action_predicates()}

(* State transition definition *)
{self.generate_trace_next()}


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\\ [][Next \\/ ComposedNext]_vars

-----------------------------------------------------------------------------
=============================================================================

{self.generate_constants_section()}

SPECIFICATION
    TraceSpec

VIEW
    TraceView

\\* PROPERTIES
\\*     \\* Verify mutual exclusion and type invariants
\\*     TypeInvariant


POSTCONDITION
    TraceAccepted

CHECK_DEADLOCK
    FALSE \\* Deadlock checking disabled due to stuttering

"""
        return template
    
    def generate_cfg_file(self) -> str:
        """Generate the TLC configuration file"""
        cfg_lines = []
        
        # Add constants with their values
        constants = self.config.get('constants', [])
        for constant in constants:
            const_name = constant['name']
            const_value = constant.get('value', '')
            if const_value:
                cfg_lines.append(f"CONSTANT {const_name} = {const_value}")
        
        # Add other standard configuration
        cfg_lines.extend([
            "",
            "SPECIFICATION TraceSpec",
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


def main():
    parser = argparse.ArgumentParser(description='Generate trace validation files')
    parser.add_argument('config', help='Input configuration file (YAML)')
    parser.add_argument('output_dir', help='Output directory for generated files')
    
    args = parser.parse_args()
    
    # Load configuration
    try:
        with open(args.config, 'r') as f:
            config_data = yaml.safe_load(f)
    except Exception as e:
        print(f"Error loading config file: {e}")
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