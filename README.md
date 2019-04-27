# Simply RaTT [![Build Status](https://travis-ci.org/pa-ba/simply-ratt.svg?branch=master)](https://travis-ci.org/pa-ba/simply-ratt)

Coq formalisation of [Simply RaTT](https://arxiv.org/abs/1903.05879).

## Prerequisites

- Coq version: 8.7.\*, 8.8.\*, 8.9.\*

- [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp): Installation via opam:

		opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
		opam install coq-stdpp

## Docker

The project can be typechecked using Docker in two ways:

### Using custom Docker image

You can typecheck the source files by executing the following command
in the root directory of this repo:
	
	docker run --rm -it -v "$PWD:$PWD" -w "$PWD" thepaba/coq_ratt bash --login -c "make"

### Using the coqorg Docker image

You can typecheck the source files by executing the following command
in the root directory of this repo:

	docker run --rm -it -v "$PWD:$PWD" -w "$PWD" coqorg/coq:8.9 bash --login -c "
		opam update -y
		opam install -y coq-stdpp.1.2.0
		make"

