#!/usr/bin/env bash
# Build instrumented DPDK and run trace tests.
# Run from the case-study root: cd case-studies/dpdk-ring && bash harness/run.sh

set -euo pipefail

CASE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
DPDK_DIR="$CASE_DIR/artifact/dpdk"
HARNESS_DIR="$CASE_DIR/harness"
TRACE_DIR="$CASE_DIR/traces"
NPROC=$(nproc)

echo "================================================"
echo "  DPDK rte_ring — TLA+ Trace Harness"
echo "================================================"
echo "Case dir:  $CASE_DIR"
echo "DPDK dir:  $DPDK_DIR"
echo "Trace dir: $TRACE_DIR"
echo "CPUs:      $NPROC"
echo ""

# ---- Step 1: Apply instrumentation ----
bash "$HARNESS_DIR/apply.sh"

# ---- Step 2: Build instrumented DPDK ----
echo ""
echo "=== Building DPDK (instrumented) ==="
cd "$DPDK_DIR"

# Clean previous build if present
rm -rf build install

# Configure with trace instrumentation enabled
meson setup build \
    --default-library=shared \
    -Ddisable_drivers='*' \
    -Dexamples='' \
    -Dtests=false \
    -Dc_args='-DDPDK_TLA_TRACE' \
    --warnlevel=0 \
    2>&1 | tail -5

# Build
echo "Building..."
ninja -C build -j"$NPROC" 2>&1 | tail -3

# Install to local prefix
echo "Installing to local prefix..."
DESTDIR="$DPDK_DIR/install" ninja -C build install 2>&1 | tail -1

DPDK_INSTALL="$DPDK_DIR/install/usr/local"
DPDK_INCLUDE="$DPDK_INSTALL/include"
DPDK_LIB="$DPDK_INSTALL/lib/x86_64-linux-gnu"

echo "DPDK built and installed at $DPDK_INSTALL"

# ---- Step 3: Build test program ----
echo ""
echo "=== Building test program ==="

TEST_BIN="$HARNESS_DIR/test_ring_trace"

gcc -o "$TEST_BIN" \
    "$HARNESS_DIR/src/test_ring_trace.c" \
    -I"$DPDK_INCLUDE" \
    -I"$DPDK_DIR/lib/ring" \
    -include rte_config.h \
    -march=native \
    -DDPDK_TLA_TRACE \
    -L"$DPDK_LIB" \
    -Wl,-rpath,"$DPDK_LIB" \
    -Wl,--whole-archive \
    -lrte_ring -lrte_eal -lrte_telemetry -lrte_log \
    -lrte_kvargs -lrte_argparse -lrte_pmu \
    -Wl,--no-whole-archive \
    -lpthread -lnuma -lm -ldl

echo "Test binary: $TEST_BIN"

# ---- Step 4: Run tests ----
echo ""
echo "=== Running trace tests ==="

mkdir -p "$TRACE_DIR"
# Clean old traces
rm -f "$TRACE_DIR"/*.ndjson

export LD_LIBRARY_PATH="$DPDK_LIB"
export TRACE_DIR="$TRACE_DIR"

# Find first 3 available CPUs (respecting cgroup/taskset restrictions)
AVAIL_CPUS=$(python3 -c "
import os
cpus = []
for part in open('/proc/self/status').read().split('Cpus_allowed_list:\t')[1].split('\n')[0].split(','):
    if '-' in part:
        a,b = part.split('-')
        cpus.extend(range(int(a),int(b)+1))
    else:
        cpus.append(int(part))
print(','.join(str(x) for x in cpus[:3]))
")
echo "Using lcores: $AVAIL_CPUS"

"$TEST_BIN" --no-huge --lcores="$AVAIL_CPUS" --log-level=3

# ---- Step 5: Report results ----
echo ""
echo "=== Trace Results ==="
echo ""

for f in "$TRACE_DIR"/*.ndjson; do
    if [ -f "$f" ]; then
        lines=$(wc -l < "$f")
        name=$(basename "$f")
        echo "  $name: $lines events"
        # Spot-check: show first and last event
        echo "    first: $(head -1 "$f" | cut -c1-120)..."
        echo "    last:  $(tail -1 "$f" | cut -c1-120)..."
        echo ""
    fi
done

echo "================================================"
echo "  Done! Traces in $TRACE_DIR/"
echo "================================================"
