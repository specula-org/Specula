#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "usage: $0 VERSION MODE [REPETITION]" >&2
  echo "  VERSION: V00, V01, V02, V03" >&2
  echo "  MODE: v2 or legacy" >&2
  exit 2
fi

version="$1"
mode="$2"
rep="${3:-1}"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
src="${repo_root}/versions/${version}/source"
case "${mode}" in
  v2)
    test_src="${repo_root}/out/repro/test_bugA_v2_pending_campaign_test.go"
    run_expr='TestBugA_V2PendingCampaignDisruptsLeader|TestControl_LegacyPendingConfBlocksCampaign'
    ;;
  legacy)
    test_src="${repo_root}/out/repro/test_bugA_legacy_control_test.go"
    run_expr='TestControl_LegacyPendingConfBlocksCampaign'
    ;;
  *)
    echo "unknown mode: ${mode}" >&2
    exit 2
    ;;
esac

if [[ ! -d "${src}" ]]; then
  echo "missing version source: ${src}" >&2
  exit 2
fi
if [[ ! -f "${test_src}" ]]; then
  echo "missing test source: ${test_src}" >&2
  exit 2
fi

work="${repo_root}/out/tmp/bugA-${version}-${mode}-${rep}"
rm -rf "${work}"
mkdir -p "${work}"
cp "${test_src}" "${work}/bugA_test.go"
cat > "${work}/go.mod" <<EOF
module bugA/repro

go 1.20

require (
  go.etcd.io/etcd/raft v0.0.0
  go.etcd.io/etcd/pkg v0.0.0
)

replace go.etcd.io/etcd/raft => ${src}
replace go.etcd.io/etcd/pkg => ${repo_root}/deps/legacy-pkg
EOF
cp "${src}/go.sum" "${work}/go.sum"

mkdir -p "${repo_root}/out/gocache" "${repo_root}/out/gotmp" "${repo_root}/out/gomodcache"
cd "${work}"
env \
  GOTOOLCHAIN=local \
  GOCACHE="${repo_root}/out/gocache" \
  GOTMPDIR="${repo_root}/out/gotmp" \
  GOMODCACHE="${GOMODCACHE:-${HOME}/go/pkg/mod}" \
  GOPROXY=off \
  /usr/local/go/bin/go test -mod=mod -count=1 -run "${run_expr}" -v .
