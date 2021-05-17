#!/bin/sh

exec docker run \
 --rm \
 --network host \
 --user `id -u` \
 --volume $HOME/.Xauthority:/home/guest/.Xauthority \
 --env DISPLAY=$DISPLAY \
 --volume `pwd`:/data \
 --workdir /data enum:1.3.0 prove --prover alt-ergo Blist.mlw

# "b_blist" is proved with z3
# "create_list" and "create_cursor" are proved with alt-ergo 
# but if we use z3 and alt-ergo in same time "b_blist" isn't proved
# even if we fixe goal and theory
