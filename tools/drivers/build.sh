#!/bin/bash
# build.sh <dir> [drivers...]: copy the live tree to fast8/<dir> and build the drivers (default 9 10 11)
S=/tmp/claude-0/-home-user-vend/81e8a202-f0c4-5985-90a6-38899f07a818/scratchpad/fast8
D=$S/$1; shift
ms=${@:-9 10 11}
rm -rf $D; mkdir -p $D; cp -r /home/user/vend/src $D/src
for m in $ms; do [ -f $S/main$m.bend ] && cp $S/main$m.bend $D/src/vend_node/ && (cd $D && bend src/vend_node/main$m.bend -o m$m 2>&1 | grep -v '^$' | tail -3) & done; wait
