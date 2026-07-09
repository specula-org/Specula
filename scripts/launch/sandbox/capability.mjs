#!/usr/bin/env node
// Specula v0 sandbox capability probe (M1.2).
//
// Decide whether srt can actually START a sandbox on THIS host. The ground truth
// is running a trivial command through the sandbox — not just a static dependency
// check — so it also catches missing unprivileged user namespaces and hardened
// kernels, which a dependency list cannot see.
//
// Scope: macOS + Linux. Windows is out (Pial owns WSL2). On unsupported platforms
// the probe reports "unsupported" so the caller can refuse rather than pretend.
//
// As a CLI: exit 0 and print "ok" when sandboxing works; exit 1 and print a
// one-line reason on stderr otherwise. backend.mjs runs this in a SEPARATE process
// (a probe would otherwise pin SandboxManager's global config to the probe run).

import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { loadSrt } from './backend.mjs';

// Returns { ok: true } | { ok: false, reason, hint? }.
export async function checkCapability() {
  let srt;
  try { srt = await loadSrt(); }
  catch (e) { return { ok: false, reason: e.message.split('\n')[0], hint: 'npm i -g @anthropic-ai/sandbox-runtime' }; }
  const { SandboxManager } = srt;

  if (SandboxManager.isSupportedPlatform && !SandboxManager.isSupportedPlatform()) {
    return { ok: false, reason: `platform "${process.platform}" is not supported by srt`,
      hint: 'on Windows, run Specula inside WSL2 (owned by Pial)' };
  }

  // Static dependency check (fast, precise reasons: bwrap / socat / ripgrep).
  if (SandboxManager.checkDependencies) {
    const { errors = [] } = SandboxManager.checkDependencies() || {};
    if (errors.length) {
      return { ok: false, reason: `missing sandbox dependencies: ${errors.join('; ')}`,
        hint: 'Ubuntu/Debian: sudo apt-get install bubblewrap socat ripgrep' };
    }
  }

  // Ground truth: run `true` through a minimal sandbox and see if it starts.
  const ws = fs.mkdtempSync(path.join(os.tmpdir(), 'specula-cap-'));
  try {
    await SandboxManager.initialize({
      network: {},
      filesystem: { allowWrite: [ws], denyWrite: [], denyRead: [], allowRead: [] },
    });
    const wrapped = await SandboxManager.wrapWithSandbox('true');
    const { code, stderr } = await new Promise(res => {
      let err = '';
      const c = spawn(wrapped, { shell: true, stdio: ['ignore', 'ignore', 'pipe'] });
      c.stderr.on('data', d => { err += d; });
      c.on('exit', (code, sig) => res({ code: sig ? 1 : (code ?? 1), stderr: err }));
      c.on('error', e => res({ code: 1, stderr: e.message }));
    });
    try { SandboxManager.cleanupAfterCommand(); } catch { /* ignore */ }
    if (code !== 0) {
      const last = stderr.trim().split('\n').filter(Boolean).pop() || `exit ${code}`;
      return { ok: false, reason: `sandbox failed to start: ${last}`,
        hint: 'check unprivileged user namespaces (Ubuntu 24.04+: sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0)' };
    }
    return { ok: true };
  } catch (e) {
    return { ok: false, reason: `sandbox failed to start: ${e.message.split('\n')[0]}` };
  } finally {
    fs.rmSync(ws, { recursive: true, force: true });
  }
}

const isCLI = process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (isCLI) {
  checkCapability().then(r => {
    if (r.ok) { process.stdout.write('ok\n'); process.exit(0); }
    process.stderr.write(`[specula-sandbox] capability check FAILED: ${r.reason}\n`);
    if (r.hint) process.stderr.write(`[specula-sandbox]   fix: ${r.hint}\n`);
    process.exit(1);
  }).catch(e => {
    process.stderr.write(`[specula-sandbox] capability check error: ${e.message}\n`);
    process.exit(1);
  });
}
