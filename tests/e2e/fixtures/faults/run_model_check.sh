#!/usr/bin/env bash
# Fixture model check behind the real start_background.sh: performs the
# resource-admission handshake, then runs until the test creates release-job.
set -euo pipefail
status="${SPECULAR_TLC_ADMISSION_STATUS:?}"
log=nohup.out
while [ $# -gt 0 ]; do
    case "$1" in
        -o | --output) log="$2"; shift 2 ;;
        *) shift ;;
    esac
done
printf 'admitted\n%s\nfixture admission\n' "$$" > "$status.$$.tmp"
mv -f "$status.$$.tmp" "$status"
echo "fixture model check running"
# Stay alive until start_background.sh hands back this PID (its PID file names
# it), so even an already released job is always returned as a live job.
until [ "$(cat "$log.pid" 2>/dev/null)" = "$$" ]; do sleep 0.05; done
while [ ! -f "${FIXTURE_JOB_DIR:?}/release-job" ]; do sleep 0.05; done
echo "Model checking completed. No error has been found."
echo "Finished in 1s"
