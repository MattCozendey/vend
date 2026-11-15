#!/usr/bin/env bash
# e2e.sh [<vend binary>]: build vend (unless a binary is given) and run a scenario on data
# addresses in a fresh temporary folder. It prints each command and its reply; it checks nothing.
# Each node is named by its label, '~' and its public key; the output shows the name of node a as
# $NA, and so on.
#   1. Node a alone owns a store: two writes, a branch, a merge with a clash, a resolve, the
#      status of each request, reads and views.
#   2. Nodes a and b own a second store together: each request needs both, so they sync both ways.
#   3. Nodes c and d own a third store together and sync over TCP on localhost: d serves, c
#      fetches; a write at c and a save in a folder that d watches both need both owners.
#   4. Mounts: c mounts a folder; each command reads it, and each save becomes a version.
#   5. Forged votes: a node that claims the name of a, and one whose name carries no key, cast
#      votes; a refuses them from a data address, and d refuses them over TCP.
#   6. A writer sends its commands to d over TCP, then reads its pending write at c after a sync.
#      A client that connects and sends nothing holds d for at most 2 s.
#   7. A node killed while it serves leaves its lock; the next command takes it over.
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'if [ -n "$pid" ]; then kill "$pid" 2>/dev/null || true; fi; rm -rf "$tmp"' EXIT
if [ $# -ge 1 ]; then
  vend="$1"
else
  vend="$tmp/vend"
  (cd "$repo" && bun run build --out "$vend")
fi

A="$tmp/a"
B="$tmp/b"
C="$tmp/c"
D="$tmp/d"
E="$tmp/e"
F="$tmp/f"
S=no-store-yet
T=no-store-yet
U=no-store-yet
V=no-store-yet
NA=no-node-yet
NB=no-node-yet
NC=no-node-yet
ND=no-node-yet
pid=
port=0
step() { echo; echo "# $*"; }
short() {
  sed -e "s|$tmp/||g" -e "s|$S|\$S|g" -e "s|$T|\$T|g" -e "s|$U|\$U|g" -e "s|$V|\$V|g" \
    -e "s|$NA|\$NA|g" -e "s|$NB|\$NB|g" -e "s|$NC|\$NC|g" -e "s|$ND|\$ND|g" \
    -e "s|127.0.0.1:$port|127.0.0.1:\$port|g" -e "s|process [0-9]*|process \$pid|g"
}
run() {
  echo "\$ vend $*" | short
  "$vend" "$@" 2>&1 | short
}
store() { "$vend" "$@" | awk '{print $NF}'; }
file() { printf '%b' "$2" > "$tmp/$1"; echo "$tmp/$1"; }

step "two nodes, each on its own data address, each with a key"
run "$A" init a
run "$B" init b
NA=$(cat "$A/name")
NB=$(cat "$B/name")
echo "names: \$NA = $NA, \$NB = $NB"
echo "(a second start on the same address; a label with '~')"
run "$A" init a || true
run "$tmp/z" init 'z~1' || true
echo "(the secret of a: its mode, and the next leaf number)"
ls -l "$A/secret" | awk 'NR > 1 {print $1, $NF}'
ls -ld "$A/secret" | awk '{print $1, "secret"}'

step "1. node a owns a store alone"
S=$(store "$A" w start s1 "$NA")
echo "store \$S = $S"
run "$A" w group g1 "$S" core "$NA"
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
T=$(store "$A" w start s2 "$NA" "$NB")
echo "store \$T = $T"
run "$A" w group g2 "$T" core "$NA" "$NB"
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
echo "$$" > "$A/lock"
run "$A" w work || true
rm "$A/lock"
step "the state on disk"
ls -l "$A" | awk 'NR > 1 {print $1, $NF}'
echo "log of a: $(wc -c < "$A/facts") bytes, log of b: $(wc -c < "$B/facts") bytes"
echo "leaves used: a $(cat "$A/secret/next"), b $(cat "$B/secret/next")"
echo "parts: $(ls "$A/parts" | wc -l)"
run "$A" w drop
echo "parts: $(ls "$A/parts" | wc -l)"

step "3. nodes c and d own a store together, and sync over TCP"
run "$C" init c
run "$D" init d
NC=$(cat "$C/name")
ND=$(cat "$D/name")
U=$(store "$C" x start s3 "$NC" "$ND")
echo "store \$U = $U"
mkdir -p "$tmp/notes"
printf 'first\n' > "$tmp/notes/todo.txt"
echo "(d watches the folder notes, at notes/ of \$U:main)"
run "$D" y mount "$tmp/notes" "$U:main" notes
port=$((20000 + RANDOM % 20000))
"$vend" "$D" serve "$port" > "$tmp/serve.out" 2>&1 &
pid=$!
for k in $(seq 1 100); do grep -q serves "$tmp/serve.out" 2>/dev/null && break; sleep 0.1; done
short < "$tmp/serve.out"
echo "(while d serves, it holds the lock of its address)"
run "$D" y work || true
run "$C" x group g3 "$U" core "$NC" "$ND"
for k in 1 2 3; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x own o6 "$U" core
run "$C" x own o7 "$U:main" core
for k in 1 2 3 4; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x status "$U" g3
run "$C" x status "$U:main" o7
step "a write at c needs the vote of d: c syncs, d works after each session"
run "$C" x write z1 "$U:main" c.txt "$(file v8 'from c\n')"
for k in 1 2 3; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x status "$U:main" z1
step "a save in the folder that d watches becomes a version, decided by both"
for k in 1 2 3; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x view "$U:main" notes/todo.txt
printf 'first\nsecond\n' > "$tmp/notes/todo.txt"
sleep 1.5
for k in 1 2 3; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x view "$U:main" notes/todo.txt
run "$C" x answer count "$U:main"

step "4. c mounts a folder: each command reads it"
mkdir -p "$tmp/site"
printf '<p>hello</p>\n' > "$tmp/site/index.html"
run "$C" x mount "$tmp/site" "$U:main" site
for k in 1 2 3 4 5 6; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x view "$U:main" site/index.html
printf '<p>hello again</p>\n' > "$tmp/site/index.html"
printf 'body {}\n' > "$tmp/site/style.css"
for k in 1 2 3 4 5 6; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x view "$U:main" site/index.html
run "$C" x view "$U:main" site/style.css
rm "$tmp/site/style.css"
for k in 1 2 3 4 5 6; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x view "$U:main" site/style.css
run "$C" x answer count "$U:main"
sed -e "s|$tmp/||g" -e "s|$U|\$U|g" "$C/mounts"
run "$C" x unmount "$tmp/site"
echo "mounts of c: $(wc -c < "$C/mounts") bytes"

step "5. forged votes are refused"
echo "(e claims the name of a: its key is not the key in that name)"
run "$E" init e
printf '%s' "$NA" > "$E/name"
run "$E" w sync "$A"
run "$E" w write f1 "$S:main" forged.txt "$(file v9 'forged\n')"
run "$E" w status "$S:main" f1
run "$A" w sync "$E"
run "$A" w status "$S:main" w/f1
run "$A" w view "$S:main" forged.txt
run "$A" w liars
echo "(f has a name with no key, owns a store alone, and votes)"
run "$F" init f
printf 'f' > "$F/name"
V=$(store "$F" w start s4 f)
run "$F" w group g4 "$V" core f
run "$F" w own o8 "$V" core
run "$A" w sync "$F"
echo "(over TCP: e claims the name of c, takes the store of c and d, votes, and syncs with d)"
printf '%s' "$NC" > "$E/name"
run "$E" x sync "$C"
run "$E" x write f2 "$U:main" forged.txt "$(file v10 'forged\n')"
run "$E" x sync "tcp:127.0.0.1:$port"
sleep 0.5
grep refused "$tmp/serve.out" | short
for k in 1 2 3 4; do run "$C" x sync "tcp:127.0.0.1:$port"; done
run "$C" x status "$U:main" f2
run "$C" x liars

step "6. a writer sends its commands to d over TCP"
R="tcp:127.0.0.1:$port"
run "$R" z write r1 "$U:main" remote.txt "$(file v11 'from z, at d\n')"
run "$R" z status "$U:main" r1
run "$R" z view "$U:main" remote.txt
run "$R" z answer count "$U:main"
run "$R" z work
run "$R" z read "$U:main" 1 c.txt
run "$R" z affects "$U:main" 1 2 c.txt -
echo "(mount, sync and drop are local only)"
run "$R" z mount "$tmp/notes" "$U:main" notes || true
run "$R" z sync "$A" || true
run "$R" z drop || true
echo "(the writer switches to node c: before c syncs, then after)"
run "$C" z view "$U:main" remote.txt
run "$C" x sync "$R"
run "$C" z view "$U:main" remote.txt
for k in 1 2 3 4; do run "$C" x sync "$R"; done
run "$C" z status "$U:main" r1
run "$R" z status "$U:main" r1
echo "(a client that sends nothing: d serves the next one after at most 2 s)"
sleep 4 | nc 127.0.0.1 "$port" > /dev/null 2>&1 &
sleep 0.2
t0=$(date +%s%N)
run "$C" x answer count "$U:main"
run "$R" z status "$U:main" r1
echo "(the remote status took $(( ($(date +%s%N) - t0) / 1000000 )) ms)"
grep "session failed" "$tmp/serve.out" | short || true

step "a node with a mount stops only when forced"
run "tcp:127.0.0.1:$port" x stop
run "tcp:127.0.0.1:$port" x stop --force
wait "$pid" || true
pid=
short < "$tmp/serve.out"
run "$D" y answer count "$U:main"
run "$D" y view "$U:main" c.txt
echo "log of c: $(wc -c < "$C/facts") bytes, log of d: $(wc -c < "$D/facts") bytes"

step "7. a node killed while it serves leaves its lock; the next command takes it over"
port=$((port + 1))
"$vend" "$B" serve "$port" > "$tmp/serve2.out" 2>&1 &
pid=$!
for k in $(seq 1 100); do grep -q serves "$tmp/serve2.out" 2>/dev/null && break; sleep 0.1; done
kill -9 "$pid"
wait "$pid" 2>/dev/null || true
pid=
echo "lock of b: $(test -f "$B/lock" && echo there || echo gone)"
run "$B" v answer count "$T:main"
echo "lock of b: $(test -f "$B/lock" && echo there || echo gone)"
