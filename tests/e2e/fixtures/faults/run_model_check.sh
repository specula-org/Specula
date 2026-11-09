#!/usr/bin/env bash
# Fixture model check behind the real start_background.sh: performs the
# resource-admission handshake, then runs until the test creates release-job.
set -euo pipefail
status="${SPECULA_TLC_ADMISSION_STATUS:?}"
printf 'admitted\n%s\nfixture admission\n' "$$" > "$status.$$.tmp"
mv -f "$status.$$.tmp" "$status"
echo "fixture model check running"
sleep 0.2  # a minimal run time, so start_background.sh hands back a live PID
while [ ! -f "${FIXTURE_JOB_DIR:?}/release-job" ]; do sleep 0.05; done
echo "Model checking completed. No error has been found."
echo "Finished in 1s"
