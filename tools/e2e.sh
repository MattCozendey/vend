#!/usr/bin/env bash
# e2e.sh [<vend binary>]: build vend (unless a binary is given) and run a scenario on two data
# addresses in a fresh temporary folder. It prints each command and its reply; it checks nothing.
#   1. Node a alone owns a store: two writes, a branch, a merge with a clash, a resolve, the
#      status of each request, reads and views.
#   2. Nodes a and b own a second store together: each request needs both, so they sync both ways.
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
if [ $# -ge 1 ]; then
  vend="$1"
else
  vend="$tmp/vend"
  (cd "$repo" && bun run build --out "$vend")
fi

A="$tmp/a"
B="$tmp/b"
S=no-store-yet
T=no-store-yet
step() { echo; echo "# $*"; }
short() { sed -e "s|$tmp/||g" -e "s|$S|\$S|g" -e "s|$T|\$T|g"; }
run() {
  echo "\$ vend $*" | short
  "$vend" "$@" 2>&1 | short
}
store() { "$vend" "$@" | awk '{print $NF}'; }
file() { printf '%b' "$2" > "$tmp/$1"; echo "$tmp/$1"; }

step "two nodes, each on its own data address"
run "$A" init a
run "$B" init b
echo "(a second start on the same address)"
run "$A" init a || true

step "1. node a owns a store alone"
S=$(store "$A" w start s1 a)
echo "store \$S = $S"
run "$A" w group g1 "$S" core a
run "$A" w own o1 "$S" core
run "$A" w own o2 "$S:main" core
run "$A" w write w1 "$S:main" hello.txt "$(file v1 'hello\nworld\n')"
run "$A" w write w2 "$S:main" notes.txt "$(file v2 'first note\n')"
run "$A" w read "$S:main" 2 hello.txt
step "a branch: dev, moved to main@2, then both change one line"
run "$A" w own o3 "$S:dev" core
run "$A" w move m0 "$S:dev" "$S:main" 2
run "$A" w write w3 "$S:dev" hello.txt "$(file v3 'hello\nworld from dev\n')"
run "$A" w write w4 "$S:main" hello.txt "$(file v4 'hello\nworld from main\n')"
step "merge dev into main: the line clashes"
run "$A" w merge m1 "$S:dev" "$S:main"
run "$A" w answer clashes "$S:main" m1
run "$A" w resolve r1 m1 hello.txt "$(file v5 'hello\nworld from both\n')"
step "the status of each request"
for i in o2 w1 w2 w3 w4 m1 r1; do
  case $i in w3) l="$S:dev" ;; *) l="$S:main" ;; esac
  run "$A" w status "$l" "$i"
done
run "$A" w status "$S" s1
run "$A" w answer count "$S:main"
run "$A" w answer version "$S:main" 4
run "$A" w answer parents "$S:main" 4
run "$A" w view "$S:main" hello.txt
run "$A" w read "$S:main" 1 hello.txt
run "$A" w read "$S:dev" 2 hello.txt
run "$A" w affects "$S:main" 1 4 hello.txt -

step "2. nodes a and b own a store together"
T=$(store "$A" w start s2 a b)
echo "store \$T = $T"
run "$A" w group g2 "$T" core a b
run "$A" w status "$T" g2
run "$B" v sync "$A"
run "$A" w sync "$B"
run "$B" v sync "$A"
run "$A" w status "$T" g2
run "$A" w own o4 "$T" core
run "$A" w own o5 "$T:main" core
for k in 1 2; do run "$B" v sync "$A"; run "$A" w sync "$B"; done
run "$A" w status "$T" o5
step "a writes at a, v writes at b, then they sync both ways"
run "$A" w write x1 "$T:main" a.txt "$(file v6 'from a\n')"
run "$B" v write y1 "$T:main" b.txt "$(file v7 'from b\n')"
for k in 1 2 3; do run "$B" v sync "$A"; run "$A" w sync "$B"; done
run "$B" v sync "$A"
run "$A" w status "$T:main" x1
run "$A" w status "$T:main" v/y1
run "$B" v status "$T:main" w/x1
run "$B" v status "$T:main" y1
run "$A" w view "$T:main" b.txt
run "$B" v view "$T:main" a.txt
run "$A" w answer count "$T:main"
run "$B" v answer count "$T:main"
run "$A" w answer owners "$T:main" 2
run "$B" v liars
step "only one node runs on an address: a held lock refuses a second"
touch "$A/lock"
run "$A" w work || true
rm "$A/lock"
step "the state on disk"
ls -l "$A" | short
echo "parts: $(ls "$A/parts" | wc -l)"
run "$A" w drop
echo "parts: $(ls "$A/parts" | wc -l)"
