#!/bin/sh

exec docker run \
 --rm \
 --network host \
 --user `id -u` \
 --volume $HOME/.Xauthority:/home/guest/.Xauthority \
 --env DISPLAY=$DISPLAY \
 --volume `pwd`:/data \
 --workdir /data enum:1.3.0 extract \
  --driver ocaml64 -L ../blist Blist.mlw Blist.ml