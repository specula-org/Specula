#!/usr/bin/env python3
"""
Specula Instrumentation Tool
Multi-language source code instrumentation for TLA+ trace generation

Supports: Go, Python, Rust
"""

import os
import re
import sys
import json
import argparse
import logging
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set

logger = logging.getLogger(__name__)

class LanguageHandler(ABC):
    """Abstract base class for language-specific instrumentation handlers"""
    
    @abstractmethod
    def detect_functions(self, source_code: str) -> Dict[str, List[Tuple[int, str]]]:
        """Detect functions in source code. Returns {function_name: [(line_number, full_match)]}"""
        pass
    
    @abstractmethod
    def instrument_function(self, source_lines: List[str], line_num: int, 
                          action_name: str, stub_code: str) -> List[str]:
        """Insert instrumentation code at specified line"""
        pass
    
    @abstractmethod
    def get_required_imports(self) -> List[str]:
        """Get required import statements for instrumentation"""
        pass
    
    def normalize_function_name(self, func_name: str, action_name: str) -> bool:
        """Check if function name matches action name with various naming conventions"""
        # Direct match
        if func_name.lower() == action_name.lower():
            return True
            
        # CamelCase variations
        camel_variations = [
            action_name,
            action_name.lower(),
            action_name.capitalize(),
            self._to_camel_case(action_name),
            self._to_snake_case(action_name),
            self._to_pascal_case(action_name)
        ]
        
        return func_name in camel_variations or func_name.lower() in [v.lower() for v in camel_variations]
    
    def _to_camel_case(self, name: str) -> str:
        """Convert to camelCase"""
        if '_' in name:
            parts = name.split('_')
            return parts[0].lower() + ''.join(word.capitalize() for word in parts[1:])
        return name[0].lower() + name[1:] if name else name
    
    def _to_snake_case(self, name: str) -> str:
        """Convert to snake_case"""
        result = re.sub('([A-Z]+)([A-Z][a-z])', r'\1_\2', name)
        result = re.sub('([a-z\\d])([A-Z])', r'\1_\2', result)
        return result.lower()
    
    def _to_pascal_case(self, name: str) -> str:
        """Convert to PascalCase"""
        if '_' in name:
            return ''.join(word.capitalize() for word in name.split('_'))
        return name.capitalize()

class GoHandler(LanguageHandler):
    """Go language instrumentation handler"""
    
    def detect_functions(self, source_code: str) -> Dict[str, List[Tuple[int, str]]]:
        functions = {}
        lines = source_code.split('\n')
        
        # Go function patterns
        patterns = [
            r'func\s+\(.*?\)\s+(\w+)\s*\([^)]*\)',  # Method with receiver
            r'func\s+(\w+)\s*\([^)]*\)',             # Regular function
        ]
        
        for i, line in enumerate(lines):
            for pattern in patterns:
                matches = re.finditer(pattern, line)
                for match in matches:
                    func_name = match.group(1)
                    if func_name not in functions:
                        functions[func_name] = []
                    functions[func_name].append((i + 1, match.group(0)))
        
        return functions
    
    def instrument_function(self, source_lines: List[str], line_num: int, 
                          action_name: str, stub_code: str) -> List[str]:
        # Find the opening brace
        brace_line = line_num - 1
        while brace_line < len(source_lines) and '{' not in source_lines[brace_line]:
            brace_line += 1
        
        if brace_line >= len(source_lines):
            return source_lines
        
        # Insert after opening brace
        insert_pos = brace_line + 1
        instrumented_stub = stub_code.replace("ACTION_NAME", action_name)
        
        # Add proper indentation
        indent = "\t"
        instrumented_lines = [indent + line for line in instrumented_stub.split('\n') if line.strip()]
        
        result = source_lines[:insert_pos] + instrumented_lines + source_lines[insert_pos:]
        return result
    
    def get_required_imports(self) -> List[str]:
        return []  # Template-based approach doesn't need hardcoded imports

class PythonHandler(LanguageHandler):
    """Python language instrumentation handler"""
    
    def detect_functions(self, source_code: str) -> Dict[str, List[Tuple[int, str]]]:
        functions = {}
        lines = source_code.split('\n')
        
        # Python function patterns
        patterns = [
            r'def\s+(\w+)\s*\([^)]*\):',  # Regular function/method
            r'@\w+.*?def\s+(\w+)\s*\([^)]*\):',  # Decorated function
        ]
        
        for i, line in enumerate(lines):
            for pattern in patterns:
                matches = re.finditer(pattern, line, re.DOTALL)
                for match in matches:
                    func_name = match.group(1)
                    if func_name not in functions:
                        functions[func_name] = []
                    functions[func_name].append((i + 1, match.group(0)))
        
        return functions
    
    def instrument_function(self, source_lines: List[str], line_num: int, 
                          action_name: str, stub_code: str) -> List[str]:
        # Find function definition line and get indentation
        func_line_idx = line_num - 1
        func_line = source_lines[func_line_idx]
        base_indent = len(func_line) - len(func_line.lstrip())
        
        # Insert after function definition
        insert_pos = line_num
        instrumented_stub = stub_code.replace("ACTION_NAME", action_name)
        
        # Add proper indentation (function body level)
        indent = " " * (base_indent + 4)
        instrumented_lines = [indent + line for line in instrumented_stub.split('\n') if line.strip()]
        
        result = source_lines[:insert_pos] + instrumented_lines + source_lines[insert_pos:]
        return result
    
    def get_required_imports(self) -> List[str]:
        return []

class RustHandler(LanguageHandler):
    """Rust language instrumentation handler"""
    
    def detect_functions(self, source_code: str) -> Dict[str, List[Tuple[int, str]]]:
        functions = {}
        lines = source_code.split('\n')
        
        # Rust function patterns
        patterns = [
            r'fn\s+(\w+)\s*\([^)]*\)(?:\s*->\s*[^{]+)?\s*{',      # Regular function
            r'pub\s+fn\s+(\w+)\s*\([^)]*\)(?:\s*->\s*[^{]+)?\s*{', # Public function
            r'async\s+fn\s+(\w+)\s*\([^)]*\)(?:\s*->\s*[^{]+)?\s*{', # Async function
        ]
        
        for i, line in enumerate(lines):
            for pattern in patterns:
                matches = re.finditer(pattern, line)
                for match in matches:
                    func_name = match.group(1)
                    if func_name not in functions:
                        functions[func_name] = []
                    functions[func_name].append((i + 1, match.group(0)))
        
        return functions
    
    def instrument_function(self, source_lines: List[str], line_num: int, 
                          action_name: str, stub_code: str) -> List[str]:
        # Find the opening brace
        brace_line = line_num - 1
        if '{' not in source_lines[brace_line]:
            # Look for opening brace in next few lines
            for j in range(1, 3):
                if brace_line + j < len(source_lines) and '{' in source_lines[brace_line + j]:
                    brace_line = brace_line + j
                    break
        
        # Insert after opening brace
        insert_pos = brace_line + 1
        instrumented_stub = stub_code.replace("ACTION_NAME", action_name)
        
        # Add proper indentation
        indent = "    "
        instrumented_lines = [indent + line for line in instrumented_stub.split('\n') if line.strip()]
        
        result = source_lines[:insert_pos] + instrumented_lines + source_lines[insert_pos:]
        return result
    
    def get_required_imports(self) -> List[str]:
        return []

class InstrumentationTool:
    """Main instrumentation tool"""
    
    def __init__(self):
        self.handlers = {
            'go': GoHandler(),
            'python': PythonHandler(),
            'rust': RustHandler(),
        }
    
    def detect_language(self, file_path: str) -> str:
        """Detect programming language from file extension"""
        ext = Path(file_path).suffix.lower()
        ext_map = {
            '.go': 'go',
            '.py': 'python',
            '.rs': 'rust',
        }
        return ext_map.get(ext, 'unknown')
    
    def load_config(self, config_path: str) -> Dict:
        """Load TLA+ action configuration"""
        with open(config_path, 'r') as f:
            return json.load(f) if config_path.endswith('.json') else __import__('yaml').safe_load(f)
    
    def load_stub_template(self, template_path: str) -> str:
        """Load instrumentation stub template"""
        with open(template_path, 'r') as f:
            return f.read().strip()
    
    def validate_instrumentation(self, config: Dict, source_file: str, language: str) -> Dict:
        """Validate that actions can be instrumented"""
        if language not in self.handlers:
            raise ValueError(f"Unsupported language: {language}")
        
        handler = self.handlers[language]
        
        with open(source_file, 'r') as f:
            source_code = f.read()
        
        detected_functions = handler.detect_functions(source_code)
        actions = config.get('actions', [])
        
        validation_result = {
            'total_actions': len(actions),
            'instrumentable_actions': 0,
            'missing_actions': [],
            'found_functions': {},
            'detected_functions': list(detected_functions.keys())
        }
        
        for action in actions:
            action_name = action['name']
            found = False
            
            for func_name in detected_functions:
                if handler.normalize_function_name(func_name, action_name):
                    validation_result['found_functions'][action_name] = func_name
                    validation_result['instrumentable_actions'] += 1
                    found = True
                    break
            
            if not found:
                validation_result['missing_actions'].append(action_name)
        
        return validation_result
    
    def instrument_source(self, config: Dict, source_file: str, stub_template: str, 
                         output_file: str, language: str) -> Dict:
        """Instrument source code with TLA+ action tracing"""
        if language not in self.handlers:
            raise ValueError(f"Unsupported language: {language}")
        
        handler = self.handlers[language]
        
        with open(source_file, 'r') as f:
            source_lines = f.readlines()
        
        # Remove newlines for easier processing
        source_lines = [line.rstrip('\n') for line in source_lines]
        
        detected_functions = handler.detect_functions('\n'.join(source_lines))
        actions = config.get('actions', [])
        
        instrumentation_result = {
            'instrumented_actions': [],
            'skipped_actions': [],
            'total_instrumentations': 0
        }
        
        # Sort actions by line number (descending) to avoid line number shifts
        instrumentations = []
        
        for action in actions:
            action_name = action['name']
            found = False
            
            for func_name, occurrences in detected_functions.items():
                if handler.normalize_function_name(func_name, action_name):
                    for line_num, _ in occurrences:
                        instrumentations.append((line_num, action_name, func_name))
                        found = True
                    break
            
            if found:
                instrumentation_result['instrumented_actions'].append(action_name)
            else:
                instrumentation_result['skipped_actions'].append(action_name)
        
        # Sort by line number (descending) to avoid conflicts
        instrumentations.sort(key=lambda x: x[0], reverse=True)
        
        # Apply instrumentations
        for line_num, action_name, func_name in instrumentations:
            logger.info(f"Instrumenting action '{action_name}' in function '{func_name}'")
            source_lines = handler.instrument_function(source_lines, line_num, action_name, stub_template)
            instrumentation_result['total_instrumentations'] += 1
        
        # Write instrumented code
        # Create output directory if it doesn't exist
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w') as f:
            f.write('\n'.join(source_lines) + '\n')
        
        return instrumentation_result

def main():
    parser = argparse.ArgumentParser(description='Specula Multi-language Instrumentation Tool')
    parser.add_argument('config', help='TLA+ action configuration file (YAML/JSON)')
    parser.add_argument('source', help='Source code file to instrument')
    parser.add_argument('--language', help='Programming language (auto-detect if not specified)')
    parser.add_argument('--stub-template', help='Instrumentation stub template file')
    parser.add_argument('--output', '-o', help='Output file for instrumented code')
    parser.add_argument('--validate-only', action='store_true', help='Only validate, do not instrument')
    parser.add_argument('--generate-template', help='Generate template file for specified language')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.basicConfig(level=logging.INFO)
    
    tool = InstrumentationTool()
    
    # Auto-detect language if not specified
    language = args.language or tool.detect_language(args.source)
    if language == 'unknown':
        print(f"Error: Could not detect language for {args.source}")
        sys.exit(1)
    
    # Load configuration
    try:
        config = tool.load_config(args.config)
    except Exception as e:
        print(f"Error loading config: {e}")
        sys.exit(1)
    
    # Generate template if requested
    if args.generate_template:
        template_content = {
            'go': 'traceAction("ACTION_NAME", map[string]interface{}{\n\t"node_id": r.id,\n\t"term": r.Term,\n\t"state": r.state.String(),\n})',
            'python': 'trace_action("ACTION_NAME", {\n    "node_id": self.node_id,\n    "state": self.state,\n    "term": self.term\n})',
            'rust': 'trace_action("ACTION_NAME", &TraceParams {\n    node_id: self.node_id,\n    state: self.state.clone(),\n    term: self.term,\n});'
        }.get(language, '')
        
        with open(args.generate_template, 'w') as f:
            f.write(template_content)
        print(f"Template generated: {args.generate_template}")
        return
    
    # Validation
    validation_result = tool.validate_instrumentation(config, args.source, language)
    
    print(f"Validation Results:")
    print(f"  Language: {language}")
    print(f"  Total actions: {validation_result['total_actions']}")
    print(f"  Instrumentable: {validation_result['instrumentable_actions']}")
    print(f"  Missing: {len(validation_result['missing_actions'])}")
    
    if validation_result['missing_actions']:
        print(f"  Missing actions: {', '.join(validation_result['missing_actions'])}")
    
    # If no stub template or output specified, default to validate-only mode
    if args.validate_only or not args.stub_template or not args.output:
        if not args.validate_only and (not args.stub_template or not args.output):
            print("Note: No stub template or output specified, running in validation-only mode.")
        return
    
    # Instrumentation
    
    try:
        stub_template = tool.load_stub_template(args.stub_template)
        result = tool.instrument_source(config, args.source, stub_template, args.output, language)
        
        print(f"Instrumentation complete. {result['total_instrumentations']} functions instrumented. Output: {args.output}")
        
    except Exception as e:
        print(f"Error during instrumentation: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main() 