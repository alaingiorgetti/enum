# gui.sh
docker create -ti -e DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix \
  -v ~/gl18:/home/opam/app/gl18 --name="proof" proof
