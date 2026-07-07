#!/usr/bin/env node
// Specula v0 sandbox self-test ("leak-probe").
//
// Given a sandbox.json, assert that everything the config claims to restrict
// actually holds INSIDE the sandbox. It reads the SAME config the backend uses
// (via loadConfig) and runs its checks THROUGH backend.mjs, so the probe and the
// real run can never drift. On the default posture it verifies the one default
// restriction (writes); it becomes load-bearing the moment a user tightens
// read.deny or switches network to allowlist.
//
// Exit 0 = every restriction held. Exit 1 = at least one LEAK. Exit 2 = probe error.
//
// Usage: leak-probe.mjs --workspace DIR [--config PATH]

import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { loadConfig, expandPlaceholders } from './backend.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const BACKEND = path.join(HERE, 'backend.mjs');
const shq = a => `'` + String(a).replaceAll(`'`, `'\\''`) + `'`;

function parseArgs(argv) {
  const out = { workspace: null, config: null };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--workspace') out.workspace = argv[++i];
    else if (a === '--config') out.config = argv[++i];
    else throw new Error(`unknown argument: ${a}`);
  }
  if (!out.workspace) throw new Error('--workspace DIR is required');
  return out;
}

const expandHome = p => (p.startsWith('~') ? path.join(os.homedir(), p.slice(1)) : p);

// Up to `limit` real files under a host path, so we can test their content is masked.
function sampleFiles(p, limit = 5) {
  const out = [];
  let st; try { st = fs.statSync(p); } catch { return out; }
  if (st.isFile()) return [p];
  if (!st.isDirectory()) return out;
  const stack = [p];
  while (stack.length && out.length < limit) {
    let names; const d = stack.pop();
    try { names = fs.readdirSync(d); } catch { continue; }
    for (const name of names) {
      if (out.length >= limit) break;
      const f = path.join(d, name);
      let s; try { s = fs.lstatSync(f); } catch { continue; }
      if (s.isFile()) out.push(f);
      else if (s.isDirectory()) stack.push(f);
    }
  }
  return out;
}

// Is `domain` covered by an allowlist entry (exact or "*.base")?
function domainCovered(domain, allow) {
  return allow.some(pat => {
    if (pat === domain) return true;
    if (pat.startsWith('*.')) {
      const base = pat.slice(2);
      return domain === base || domain.endsWith('.' + base);
    }
    return false;
  });
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  const workspace = path.resolve(args.workspace);
  const { cfg, source } = loadConfig(args.config, process.cwd());
  const expand = s => expandHome(expandPlaceholders(s, workspace));

  const lines = ['set -u'];
  const notes = [];

  // 1) read.deny — each denied path's file CONTENT must be unreadable inside the
  //    sandbox. Test content (head -c1), NOT `ls`: srt masks with an empty tmpfs,
  //    so `ls` on a denied directory succeeds with exit 0 (P0 lesson).
  for (const raw of (cfg.read?.deny ?? [])) {
    const files = sampleFiles(expand(raw));
    if (files.length === 0) { notes.push(`read.deny "${raw}" — no real file on host to test`); continue; }
    for (const f of files) {
      lines.push(`if head -c1 ${shq(f)} >/dev/null 2>&1; then echo "LEAK read: ${f}"; else echo "ok read: ${f}"; fi`);
    }
  }

  // 2) write — a canary OUTSIDE the allowed set must not be writable.
  const canary = path.join(os.homedir(), '.specula-leakprobe-canary');
  lines.push(`if touch ${shq(canary)} 2>/dev/null; then echo "LEAK write: ${canary}"; rm -f ${shq(canary)}; else echo "ok write-blocked: ${canary}"; fi`);

  // 3) network allowlist — a reachable domain NOT covered by the allowlist must be blocked.
  if ((cfg.network?.mode ?? 'open') === 'allowlist') {
    const allow = cfg.network?.allow ?? [];
    const canaryDomain = ['example.com', 'example.org', 'example.net'].find(d => !domainCovered(d, allow));
    if (canaryDomain) {
      lines.push(`code=$(curl -sS -o /dev/null -m 10 -w "%{http_code}" https://${canaryDomain} 2>/dev/null || true); ` +
        `if [ "$code" = "200" ]; then echo "LEAK net: ${canaryDomain} reachable"; else echo "ok net-blocked: ${canaryDomain} ($code)"; fi`);
    } else {
      notes.push('network allowlist covers all canary domains — skipped net check');
    }
  } else {
    notes.push('network mode=open — no network restriction to verify');
  }

  // Run the probe THROUGH backend.mjs against the SAME config. Keep the probe
  // script inside the workspace (always writable + readable) so a tightened
  // read.deny can't hide the probe itself.
  fs.mkdirSync(workspace, { recursive: true });
  const probePath = path.join(workspace, '.specula-leakprobe.sh');
  fs.writeFileSync(probePath, lines.join('\n') + '\n');
  const r = spawnSync('node', [BACKEND, '--workspace', workspace, '--config', source, '--', 'bash', probePath],
    { encoding: 'utf8' });
  fs.rmSync(probePath, { force: true });

  const out = r.stdout || '';
  process.stdout.write(out);
  if (r.stderr) process.stderr.write(r.stderr);
  for (const n of notes) process.stderr.write(`[leak-probe] note: ${n}\n`);

  const leaks = out.split('\n').filter(l => l.startsWith('LEAK'));
  const oks = out.split('\n').filter(l => l.startsWith('ok '));
  if (leaks.length > 0) {
    process.stderr.write(`[leak-probe] FAIL: ${leaks.length} leak(s) — config "${source}" does not hold\n`);
    process.exit(1);
  }
  if (r.status !== 0 || oks.length === 0) {
    process.stderr.write(`[leak-probe] ERROR: backend exited ${r.status} without producing checks\n`);
    process.exit(2);
  }
  process.stderr.write(`[leak-probe] PASS: ${oks.length} check(s) held for config "${source}"\n`);
  process.exit(0);
}

try { main(); }
catch (e) { process.stderr.write(`[leak-probe] error: ${e.message}\n`); process.exit(2); }
