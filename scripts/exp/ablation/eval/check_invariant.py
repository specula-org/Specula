#!/usr/bin/env python3
"""Check a single invariant against a spec using TLC simulation."""
import json, sys, os, subprocess, tempfile, re

spec_dir = sys.argv[1]
inv_file = sys.argv[2]  # JSON file with concretized invariants
inv_name = sys.argv[3]
tla2tools = sys.argv[4]
community = sys.argv[5]

invariants = json.load(open(inv_file))
inv_def = invariants.get(inv_name, 'TRUE')

if inv_def == 'TRUE':
    print('SKIP')
    sys.exit(0)

# Read MC.tla to find what module it extends
mc_path = os.path.join(spec_dir, 'MC.tla')
mc_content = open(mc_path).read()
extends_match = re.search(r'EXTENDS\s+(\w+)', mc_content)
base_module = extends_match.group(1) if extends_match else 'base'

# Write temporary check module
check_tla = os.path.join(spec_dir, '_InvCheck.tla')
check_cfg = os.path.join(spec_dir, '_InvCheck.cfg')

with open(check_tla, 'w') as f:
    f.write(f'---- MODULE _InvCheck ----\n')
    f.write(f'EXTENDS {base_module}\n\n')
    # MC module may define additional operators needed
    f.write(f'MCInv_{inv_name} ==\n')
    # Clean up the invariant definition - extract just the body
    body = inv_def
    # Remove the "Name ==" prefix if present
    body = re.sub(r'^\w+\s*==\s*', '', body, count=1).strip()
    f.write(f'  {body}\n')
    f.write(f'====\n')

# Copy MC.cfg and replace invariants
mc_cfg_content = open(os.path.join(spec_dir, 'MC.cfg')).read()
# Remove existing INVARIANT/INVARIANTS block
mc_cfg_content = re.sub(r'INVARIANTS?\s*\n(?:\s+\w+\s*\n)*', '', mc_cfg_content)
# Change SPECIFICATION to use MCSpec from MC module (need to extend MC instead)
# Actually, simpler: extend MC module which already extends base
with open(check_tla, 'w') as f:
    mc_module = re.search(r'MODULE\s+(\w+)', mc_content).group(1)
    f.write(f'---- MODULE _InvCheck ----\n')
    f.write(f'EXTENDS {mc_module}\n\n')
    f.write(f'MCInv_{inv_name} ==\n')
    body = re.sub(r'^\w+\s*==\s*', '', inv_def, count=1).strip()
    f.write(f'  {body}\n')
    f.write(f'====\n')

with open(check_cfg, 'w') as f:
    # Use MC.cfg but replace invariants
    for line in open(os.path.join(spec_dir, 'MC.cfg')):
        if line.strip().startswith('INVARIANT'):
            continue
        # Skip indented invariant names under INVARIANTS block
        if re.match(r'^\s+MC\w+|^\s+\w+Inv|^\s+\w+Safety|^\s+TypeOK', line):
            continue
        f.write(line)
    f.write(f'\nINVARIANT\n    MCInv_{inv_name}\n')

# Run TLC
try:
    result = subprocess.run(
        ['java', '-Xss8m', '-Xmx4g', '-XX:+UseParallelGC',
         '-cp', f'{tla2tools}:{community}',
         'tlc2.TLC', '_InvCheck.tla', '-config', '_InvCheck.cfg',
         '-deadlock', '-noTE', '-simulate', 'num=1000', '-workers', '1'],
        cwd=spec_dir, capture_output=True, text=True, timeout=30
    )
    output = result.stdout + result.stderr

    if 'Invariant' in output and 'violated' in output:
        print('VIOLATED')
    elif 'Error' in output and 'Semantic' in output:
        print('ERROR_PARSE')
    elif 'Error' in output:
        print('ERROR')
    elif 'Finished' in output or 'states' in output:
        print('PASS')
    else:
        print('UNKNOWN')
except subprocess.TimeoutExpired:
    print('TIMEOUT')
finally:
    # Cleanup
    for f in [check_tla, check_cfg]:
        try: os.remove(f)
        except: pass
