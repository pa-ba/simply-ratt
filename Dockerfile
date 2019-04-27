FROM coqorg/base:latest


RUN ["/bin/bash", "--login", "-c", "set -x \
  && opam update -y \
  && opam install -y coq.8.9.0 coq-stdpp.1.2.0 \
  && opam clean -a -s --logs \
  && opam config list && opam list"]
