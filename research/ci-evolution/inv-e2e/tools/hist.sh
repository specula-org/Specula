#!/bin/sh
# Read-only history of the source, up to the base revision only.
# The repository at /work/history.git contains the base commit and its ancestors and nothing else.
#
#   hist.sh log [options] [-- paths]     e.g. hist.sh log -S'pendingIndex' --oneline -- raft.go
#   hist.sh show <commit>[:<path>]
#   hist.sh blame [-L a,b] <path>         (blames the base revision)
#   hist.sh grep <pattern> <commit>       (git grep in an older commit)
set -eu
GIT="/usr/bin/git --git-dir=/work/history.git"
[ $# -ge 1 ] || { sed -n '2,9p' "$0"; exit 2; }
cmd=$1; shift
for a in "$@"; do
  case "$a" in
    --all|--branches*|--tags*|--remotes*|--glob*|--reflog|--exec*|--ext-diff|--output*|-o) echo "hist.sh: option $a is not allowed" >&2; exit 2;;
  esac
done
case "$cmd" in
  log)   exec $GIT log base "$@";;
  show)  exec $GIT show "$@";;
  blame) exec $GIT blame base "$@";;
  grep)  exec $GIT grep "$@";;
  *) echo "hist.sh: only log, show, blame and grep are allowed" >&2; exit 2;;
esac
