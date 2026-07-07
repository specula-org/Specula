# Specula v0 sandbox

A thin guardrail that wraps each agent run so a fully-automatic agent can work on
a user's own machine without damaging their environment. It is a **guardrail, not
a hard boundary**: it protects against mistakes and prompt injection, not a
deliberately adversarial model (that needs a VM).

Engine: [`@anthropic-ai/sandbox-runtime`](https://www.npmjs.com/package/@anthropic-ai/sandbox-runtime)
(srt) — Linux = bubblewrap, macOS = Seatbelt. We drive it through its **library
API** (`backend.mjs`), not the `srt` CLI, because the default "network fully open"
posture cannot be expressed in srt's settings-file schema.

## Files

- `backend.mjs` — the shim. Reads `sandbox.json`, translates it to an srt runtime
  config, runs the command inside the sandbox.
- `sandbox.default.json` — the default config, copied to `~/.specula/sandbox.json`
  on first run.

## Requirements

- Node ≥ 20, and `srt` installed: `npm i -g @anthropic-ai/sandbox-runtime`
- Linux also needs `bubblewrap`, `socat`, `ripgrep`, and an unprivileged user
  namespace (Ubuntu 24.04+: `kernel.apparmor_restrict_unprivileged_userns=0`).

## Usage

```bash
backend.mjs --workspace DIR [--config PATH] -- CMD [ARGS...]
```

`--workspace` is the writable run directory (`${WORKSPACE}` in the config).
Config is resolved in order: `--config PATH` → `<cwd>/.specula/sandbox.json` →
`~/.specula/sandbox.json` (written from the default on first run).

## Config (`sandbox.json`)

**Default posture: only writes are restricted; reads and network are fully open.**
Tighten by editing this one file — no code changes.

```jsonc
{
  "enabled": true,                 // false = run WITHOUT sandbox (legacy behaviour)
  "write": {                       // the ONLY dimension restricted by default
    "allow": ["${WORKSPACE}", "${TMPDIR}"],  // placeholders expanded by Specula
    "deny":  []                    // carve-outs inside allowed paths (deny wins)
  },
  "read": {                        // open by default
    "deny":  [],                   // to protect credentials: ["~/.ssh","~/.aws","~/.config/gcloud","~/.netrc"]
    "allow": []                    // re-allow inside a denied region (allow wins)
  },
  "network": {                     // open by default
    "mode":  "open",               // "open" = no proxy, fully open; "allowlist" = deny-by-default, only `allow`
    "allow": [],                   // allowlist mode: ["*.github.com","pypi.org","registry.npmjs.org", …]
    "deny":  []                    // allowlist mode only (see constraint below)
  }
}
```

### Constraints (don't get surprised)

- **`open` vs `allowlist` is either/or — there is no "open but block a few".** In
  `open` mode srt runs no proxy, so there is no interception point; `network.deny`
  only takes effect in `allowlist` mode.
- **Linux paths are literal — no globs.** Use directories (e.g. `~/.ssh`), not
  `~/.ssh/id_*`. `~` expands to the home directory.
- srt always blocks writes to a built-in set (`.bashrc`, `.gitconfig`,
  `.git/hooks/`, `.claude/commands/`, `.mcp.json`, …) — free defense, but it only
  guards **writes**, not credential **reads**; protect reads via `read.deny`.

### Consequence of the default

With reads and network open by default, the only default protection is on writes.
A prompt-injected agent could read credentials or exfiltrate over the open
network. To defend against that, set `read.deny` (credentials) and switch
`network.mode` to `allowlist`.
