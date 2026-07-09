#!/usr/bin/env node
// Specula v0 sandbox backend — a thin Node shim over @anthropic-ai/sandbox-runtime (srt).
//
// Reads a user-editable sandbox.json (Specula's own schema), translates it into an
// srt runtime config, and runs the given command inside the srt sandbox.
//
// Why a Node shim and not the `srt` CLI: the default posture leaves the network
// FULLY OPEN, which srt's settings-file schema cannot express (it requires
// network.allowedDomains and rejects "*"). Only the library API can omit
// allowedDomains, which makes srt skip network isolation entirely. So we drive
// srt through SandboxManager here.
//
// Usage:
//   backend.mjs --workspace DIR [--config PATH] -- CMD [ARGS...]

import { spawn, spawnSync, execSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const TEMPLATE_PATH = path.join(HERE, 'sandbox.default.json');
const CAPABILITY = path.join(HERE, 'capability.mjs');
const USER_CONFIG_PATH = path.join(os.homedir(), '.specula', 'sandbox.json');

// Human-facing diagnostics — printed only when stderr is a real terminal. When
// this backend wraps an agent whose stdout+stderr the caller captures and parses
// (e.g. `claude --output-format json`, merged via 2>&1), a stray line here would
// corrupt that stream, so stay silent unless a human is watching. Hard failures
// (refuse / fatal) still write to stderr unconditionally.
function diag(msg) {
  if (process.stderr.isTTY) process.stderr.write(msg);
}

// ── Locate srt without hardcoding any machine path ──
export async function loadSrt() {
  // 1) normal resolution — srt is a local dependency or already on NODE_PATH.
  try { return await import('@anthropic-ai/sandbox-runtime'); } catch { /* fall through */ }
  // 2) global install — ask npm where global modules live, then import by file URL.
  let globalRoot;
  try { globalRoot = execSync('npm root -g', { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim(); } catch { /* ignore */ }
  if (globalRoot) {
    const entry = path.join(globalRoot, '@anthropic-ai', 'sandbox-runtime', 'dist', 'index.js');
    if (fs.existsSync(entry)) return import(pathToFileURL(entry).href);
  }
  throw new Error(
    'cannot find @anthropic-ai/sandbox-runtime — install it with:\n' +
    '  npm i -g @anthropic-ai/sandbox-runtime');
}

function parseArgs(argv) {
  const out = { workspace: null, config: null, cmd: [] };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--') { out.cmd = argv.slice(i + 1); break; }
    else if (a === '--workspace') out.workspace = argv[++i];
    else if (a === '--config') out.config = argv[++i];
    else throw new Error(`unknown argument: ${a}`);
  }
  if (!out.workspace) throw new Error('--workspace DIR is required');
  if (out.cmd.length === 0) throw new Error('no command given (expected: … -- CMD [ARGS...])');
  return out;
}

function readJson(p) {
  try { return JSON.parse(fs.readFileSync(p, 'utf8')); }
  catch (e) { throw new Error(`invalid JSON in ${p}: ${e.message}`); }
}

// Resolve the config file: explicit --config → repo-level .specula/ → user-level;
// first run writes the tracked default to the user-level path so there is something to edit.
export function loadConfig(explicit, cwd) {
  const candidates = explicit
    ? [explicit]
    : [path.join(cwd, '.specula', 'sandbox.json'), USER_CONFIG_PATH];
  for (const p of candidates) {
    if (fs.existsSync(p)) return { cfg: readJson(p), source: p };
  }
  const def = fs.readFileSync(TEMPLATE_PATH, 'utf8');
  fs.mkdirSync(path.dirname(USER_CONFIG_PATH), { recursive: true });
  fs.writeFileSync(USER_CONFIG_PATH, def);
  diag(`[specula-sandbox] wrote default config → ${USER_CONFIG_PATH} (edit it to tighten)\n`);
  return { cfg: JSON.parse(def), source: USER_CONFIG_PATH };
}

// Expand Specula placeholders (${WORKSPACE}, ${TMPDIR}) and a leading ~ in a
// config path. We expand ~ ourselves so a credential deny does not depend on
// srt's own tilde handling for this load-bearing path.
export function expandPlaceholders(s, workspace) {
  let out = String(s).replaceAll('${WORKSPACE}', workspace).replaceAll('${TMPDIR}', os.tmpdir());
  if (out === '~') out = os.homedir();
  else if (out.startsWith('~/')) out = path.join(os.homedir(), out.slice(2));
  return out;
}

// Specula sandbox.json → srt runtime config.
export function translate(cfg, workspace) {
  const expand = s => expandPlaceholders(s, workspace);
  const arr = x => (Array.isArray(x) ? x : []);
  // Run-specific write paths the launcher can inject without editing the config
  // file (e.g. the artifact source tree + build caches a full pipeline writes to).
  const extraWrite = (process.env.SPECULA_SANDBOX_EXTRA_WRITE || '')
    .split(path.delimiter).filter(Boolean).map(expand);
  const runtime = {
    filesystem: {
      allowWrite: [...arr(cfg.write?.allow).map(expand), ...extraWrite],
      denyWrite: arr(cfg.write?.deny).map(expand),
      denyRead: arr(cfg.read?.deny).map(expand),
      allowRead: arr(cfg.read?.allow).map(expand),
    },
    // network.mode:"open" (default) → leave allowedDomains UNDEFINED so srt skips
    // network isolation entirely (host network untouched, no proxy). srt still
    // needs a network object present (initialize reads network.parentProxy etc.).
    network: {},
  };
  const net = cfg.network ?? {};
  const mode = net.mode ?? 'open';
  if (mode === 'allowlist') {
    runtime.network.allowedDomains = arr(net.allow);
    runtime.network.deniedDomains = arr(net.deny);
  } else if (mode !== 'open') {
    throw new Error(`network.mode must be "open" or "allowlist", got "${mode}"`);
  }
  return runtime;
}

// Shell-quote each arg: on Linux srt runs the command via `bash -c`, so the argv
// must survive that re-parse.
const shq = a => `'` + String(a).replaceAll(`'`, `'\\''`) + `'`;

function runChild(command) {
  const child = spawn(command, { shell: true, stdio: 'inherit' });
  for (const sig of ['SIGINT', 'SIGTERM', 'SIGHUP']) {
    process.on(sig, () => { try { child.kill(sig); } catch { /* ignore */ } });
  }
  return child;
}

// Refuse to run unsandboxed unless the user explicitly asked (enabled:false).
// Probes in a SEPARATE process so SandboxManager's global config is not pinned to
// the probe run; the result is cached in SPECULA_SANDBOX_CAPABILITY so descendant
// runs in the same session skip the (re-)probe.
function ensureCapable(source) {
  const cached = process.env.SPECULA_SANDBOX_CAPABILITY;
  if (cached === 'ok') return;
  if (cached !== 'fail') {
    const r = spawnSync('node', [CAPABILITY], { encoding: 'utf8' });
    if (r.status === 0) { process.env.SPECULA_SANDBOX_CAPABILITY = 'ok'; return; }
    if (r.stderr) process.stderr.write(r.stderr);
  }
  process.env.SPECULA_SANDBOX_CAPABILITY = 'fail';
  process.stderr.write(
    `[specula-sandbox] refusing to run: the sandbox cannot start on this host and ` +
    `"enabled" is not false in ${source}.\n` +
    `[specula-sandbox]   → fix the cause above, or set "enabled": false to run WITHOUT the sandbox (no guardrail).\n`);
  process.exit(3);
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const workspace = path.resolve(args.workspace);
  const { cfg, source } = loadConfig(args.config, process.cwd());
  const command = args.cmd.map(shq).join(' ');

  if (cfg.enabled === false) {
    diag(`[specula-sandbox] enabled:false in ${source} → running WITHOUT sandbox\n`);
    runChild(command).on('exit', (code, signal) => process.exit(signal ? 1 : (code ?? 0)));
    return;
  }

  ensureCapable(source);

  const { SandboxManager } = await loadSrt();
  const runtimeConfig = translate(cfg, workspace);
  await SandboxManager.initialize(runtimeConfig);
  const wrapped = await SandboxManager.wrapWithSandbox(command);
  runChild(wrapped).on('exit', (code, signal) => {
    try { SandboxManager.cleanupAfterCommand(); } catch { /* ignore */ }
    process.exit(signal ? 1 : (code ?? 0));
  });
}

// Only run as a CLI when invoked directly (so leak-probe.mjs can import the
// helpers above without executing a sandbox run).
const isCLI = process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (isCLI) {
  main().catch(e => {
    process.stderr.write(`[specula-sandbox] error: ${e.message}\n`);
    process.exit(2);
  });
}
