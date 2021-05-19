Installation instructions
=========================

ENUM is currently developed and maintained only for Linux. We recommend to 
install and use it with Docker, as detailed below.

Installation with Docker
------------------------

1. If Docker is not installed, follow the instructions at
   [https://docs.docker.com/engine/install/debian/](https://docs.docker.com/engine/install/debian/)
   and 
   [https://docs.docker.com/engine/install/linux-postinstall/](https://docs.docker.com/engine/install/linux-postinstall/)
   to install Docker and run Docker commands without using sudo.

2. Build the Docker image (all Docker commands are encapsulated in Makefile entries):

     make build

   The Docker image will contain compatible releases of all the required tools.

   Warnings: The Docker image is a large file, its construction can be very long.
   A network connection is required. If you already have a Docker image with this
   name, either remove it or change the image name in Makefile.

3. Create the container:

     make ctr

   Warning: If you already have a Docker container with the same name, either
   remove it or change the container name in Makefile.

4. Start an interactive session in the container and move to the enum folder in it:

     make start
     cd enum

   Warning: Some of these folders (Why3/, Why3/generator/  etc.) are mounted in the container.
   So, any change in them in the container is actually done in their local version.

5. Finally, quit the container:

    exit

Successfully tested in May 2021 under Linux Debian 10 and Linux Ubuntu 18.04.5, with Docker 20.10.6.