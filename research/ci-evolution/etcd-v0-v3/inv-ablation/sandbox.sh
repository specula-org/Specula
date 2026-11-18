#!/bin/bash
# Run a command with only its workspace, the TLC jars and an offline Go module cache visible.
#
#   sandbox.sh WORKSPACE -- command...
#
# Unprivileged user + mount namespaces (no bwrap needed):
#   - WORKSPACE is bind-mounted at /tmp/workspace, the command's working directory;
#   - TLC jars are copied to /tmp/tools; Go deps to /tmp/godeps (GOPROXY=off, GOFLAGS=-mod=mod);
#   - /tmp, $HOME, /proj, /mydata and /users/bingzhuo/Specula are replaced by empty tmpfs, so the
#     repository, experiment history, past transcripts, skills and memory are not readable;
#   - $HOME gets back only the Claude Code binary, its OAuth credentials, and ~/.claude.json
#     without its per-project history;
#   - the command runs as the invoking user (nested user namespace), not as namespace root.
# The network stays up because the agent needs the API; prompts forbid other network use and
# run.py audits every Bash command afterwards.
set -euo pipefail
WS=$(realpath "$1"); shift
[ "${1:-}" = "--" ] && shift
HERE=$(cd "$(dirname "$0")" && pwd)
SPECULA=$(cd "$HERE/../../../.." && pwd)
DEPS=${INV_ABLATION_WORK:-/mydata/bingzhuo/inv-ablation}/godeps
CLAUDE_BIN=$(readlink -f "$(command -v claude)")
STAGE=$(mktemp -d "${INV_ABLATION_WORK:-/mydata/bingzhuo/inv-ablation}/stage.XXXXXX")
trap 'chmod -R u+w "$STAGE"; rm -rf "$STAGE"' EXIT
cp "$SPECULA/lib/tla2tools.jar" "$SPECULA/lib/CommunityModules-deps.jar" "$STAGE/"
cp "$HOME/.claude/.credentials.json" "$STAGE/credentials.json"
python3 - "$HOME/.claude.json" "$STAGE/claude.json" <<'EOF'
import json, sys
d = json.load(open(sys.argv[1]))
for key in ("projects", "githubRepoPaths", "history"):
    d.pop(key, None)
json.dump(d, open(sys.argv[2], "w"))
EOF
cp -a "$DEPS" "$STAGE/godeps"
cp "$CLAUDE_BIN" "$STAGE/claude"

export SB_WS="$WS" SB_STAGE="$STAGE" SB_HOME="$HOME" SB_UID=$(id -u) SB_GID=$(id -g)
unshare -rm bash -s -- "$@" <<'INNER'
set -euo pipefail
mount -t tmpfs none /tmp
mkdir -p /tmp/workspace /tmp/tools /tmp/godeps /tmp/bin
mount --bind "$SB_WS" /tmp/workspace
cp "$SB_STAGE"/tla2tools.jar "$SB_STAGE"/CommunityModules-deps.jar /tmp/tools/
cp -a "$SB_STAGE"/godeps/. /tmp/godeps/
cp "$SB_STAGE"/claude /tmp/bin/claude
cp "$SB_STAGE"/credentials.json /tmp/credentials.json
cp "$SB_STAGE"/claude.json /tmp/claude.json
for d in /proj /mydata /users/bingzhuo/Specula "$SB_HOME"; do
  [ -d "$d" ] && mount -t tmpfs none "$d"
done
mkdir -p "$SB_HOME/.claude"
mv /tmp/credentials.json "$SB_HOME/.claude/.credentials.json"
mv /tmp/claude.json "$SB_HOME/.claude.json"
sed -i "s#__LEGACY_PKG__#/tmp/godeps/legacy-pkg#" /tmp/godeps/go.mod.template
cd /tmp/workspace
exec unshare --user --map-user="$SB_UID" --map-group="$SB_GID" \
  env PATH=/tmp/bin:/usr/local/go/bin:/usr/local/bin:/usr/bin:/bin HOME="$SB_HOME" \
      GOMODCACHE=/tmp/godeps/modcache GOFLAGS=-mod=mod GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local \
      GOCACHE=/tmp/gocache GOPATH=/tmp/gopath TMPDIR=/tmp CLAUDE_CODE_DISABLE_AUTO_MEMORY=1 \
      JAVA_TOOL_OPTIONS=-Xmx8g \
      TLA2TOOLS=/tmp/tools/tla2tools.jar COMMUNITY_MODULES=/tmp/tools/CommunityModules-deps.jar \
      "$@"
INNER
