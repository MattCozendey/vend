#!/bin/bash
# best.sh <bin> <n> <reps> <modes...>: min of 3 runs per mode, in us per call
B=$1; n=$2; R=$3; shift; shift; shift
for i in 1 2 3; do $B $n $R "$@"; done | awk -v R=$R '/^build/{split($3,a,"="); b=a[2]; if(bb==""||b<bb)bb=b} /^mode/{split($4,a,"="); if(!($2 in m)||a[2]<m[$2])m[$2]=a[2]; if(!($2 in o))ord[++k]=$2; o[$2]=1} END{printf "build=%dms", bb; for(i=1;i<=k;i++)printf " m%s=%dus", ord[i], m[ord[i]]*1000/R; print ""}'
