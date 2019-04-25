# Simply RaTT [![Build Status](https://travis-ci.org/pa-ba/simply-ratt.svg?branch=master)](https://travis-ci.org/pa-ba/simply-ratt)

Coq formalisation of [Simply RaTT](https://arxiv.org/abs/1903.05879).

## Prerequisites

- Coq version: 8.7.\*, 8.8.\*, 8.9.\*

- [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp): Installation via opam:

		opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
		opam install coq-stdpp

## Docker

The project can be typechecked using Docker as follows:

	docker run --rm -it -v "$PWD:$PWD" -w "$PWD" coqorg/coq:8.9 bash --login -c "
		opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
		opam install coq-stdpp.dev.2019-04-25.0.0f2d2c8a
		make"
