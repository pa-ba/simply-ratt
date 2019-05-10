# Simply RaTT [![Build Status](https://travis-ci.org/pa-ba/simply-ratt.svg?branch=master)](https://travis-ci.org/pa-ba/simply-ratt)

Coq formalisation of [Simply RaTT](https://arxiv.org/abs/1903.05879).

## File structure

The source files are located in the [theories](theories) subdirectory.

### Main results

The main results are presented in the following three files:

- [FundamentalProperty.v](theories/FundamentalProperty.v) proves
  Theorem 6.3, the fundamental property of the logical relation.
- [Productivity.v](theories/Productivity.v) proves Theorem 3.1, i.e.
  the stream semantics is safe.
- [Causality.v](theories/Causality.v) proves Theorem 3.2, i.e. the
  stream transducer semantics is safe.

### Language definition

The following files define the Simply RaTT calculus (and prove some
auxiliary lemmas).

- [RawSyntax.v](theories/RawSyntax.v) defines the syntax of the
  calculus.
- [Substitutions.v](theories/Substitutions.v) defines substitutions of
  types and terms (only closed terms and types).
- [Typing.v](theories/Typing.v) defines the type system.
- [Reduction.v](theories/Reduction.v) defines the big-step operational
  semantics.
- [Streams.v](theories/Streams.v) defines the small-step operational
  semantics for streams and stream transducers.

### Logical relation

- [Heaps.v](theories/Heaps.v) defines heaps.
- [Worlds.v](theories/Worlds.v) defines the stores and the various
  order relations that are used in the logical relation.
- [LogicalRelation.v](theories/LogicalRelation.v) defines the logical
  relation and proves characterisation lemmas that correspond to the
  definition of the logical relation in the paper.
- [LogicalRelationAux.v](theories/LogicalRelationAux.v) proves lemmas
  about the logical relation that are used in the proof of the
  fundamental property.

### Misc

- [ClosedTerms.v](theories/ClosedTerms.v) defines closed terms and
  shows that substitutions work as expected with closed terms.
- [TypingClosed.v](theories/TypingClosed.v) a well-typed term is
  turned into a closed term by a suitable substitution.
- [Examples.v](theories/Examples.v) typechecks some example terms in
  the Simply RaTT calculus.
- [Tactics.v](theories/Tactics.v) defines tactics that are used in the
  proofs.
  
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

