#!/usr/bin/env python3
"""Concretize invariant templates to a specific TLA+ spec using claude CLI."""
import json, sys, re, subprocess, os

spec_path = sys.argv[1]
template_path = sys.argv[2]
output_path = sys.argv[3]

spec_content = open(spec_path).read()
templates_content = open(template_path).read()

prompt = f"""You are a TLA+ expert. Translate the invariant templates below to match the given TLA+ specification.

## Target Specification
{spec_content}

## Invariant Templates (from YAML)
{templates_content}

## Output Format
Output a JSON object where each key is the invariant name and each value is the TLA+ definition string.
Example: {{"LogInv": "LogInv == \\\\A i, j \\\\in Server : ...", "ElectionSafety": "ElectionSafety == ..."}}

Rules:
- Safety invariants: state predicates only (no primed vars, no temporal operators)
- Liveness invariants: use temporal operators ([], <>, ~>)
- Map template variable names to the spec's actual variable names
- If the spec lacks variables for an invariant, set value to "TRUE"
- Output ALL invariants from the templates"""

result = subprocess.run(
    ['claude', '--print', '--dangerously-skip-permissions', '--output-format', 'json'],
    input=prompt, capture_output=True, text=True, timeout=600
)

try:
    d = json.loads(result.stdout)
    text = d.get('result', '')
except:
    text = result.stdout

# Try to parse as JSON directly
invariants = {}
try:
    # Find JSON block in the text
    json_match = re.search(r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}', text, re.DOTALL)
    if json_match:
        invariants = json.loads(json_match.group())
except:
    pass

# Fallback: extract from code blocks
if not invariants:
    for match in re.finditer(r'```(?:tla\+?)?\n(.*?)```', text, re.DOTALL):
        content = match.group(1).strip()
        m = re.match(r'(\w+)\s*==', content)
        if m:
            invariants[m.group(1)] = content

    # Also try line-by-line
    for match in re.finditer(r'^(\w+)\s*==\s*\n((?:[ \t].*\n)*)', text, re.MULTILINE):
        name = match.group(1)
        body = match.group(0).strip()
        if name not in invariants:
            invariants[name] = body

json.dump(invariants, open(output_path, 'w'), indent=2)
print(f'Concretized {len(invariants)} invariants')
