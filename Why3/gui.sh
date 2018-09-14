# gui.sh
docker create -ti -e DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix \
  -v ~/enum-master:/home/opam/app/enum-master --name="proofctr" proofimg
