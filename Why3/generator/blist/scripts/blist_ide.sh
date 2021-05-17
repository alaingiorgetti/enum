#!/bin/sh

exec docker run \
 --rm \
 --network host \
 --user `id -u` \
 --volume $HOME/.Xauthority:/home/guest/.Xauthority \
 --env DISPLAY=$DISPLAY \
 --volume `pwd`:/data \
 --workdir /data enum:1.3.0 ide Blist.mlw