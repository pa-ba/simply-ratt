FROM coqorg/base:latest


RUN ["/bin/bash", "--login", "-c", "set -x \
  && opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
  && opam update -y \
  && opam install -y coq.8.9.0 coq-stdpp.dev.2019-04-25.0.0f2d2c8a \
  && opam clean -a -s --logs \
  && opam config list && opam list"]
