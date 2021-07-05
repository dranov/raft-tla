# Raft TLA specification

TLA+ specifications for the [Raft consensus
algorithm](https://raftconsensus.github.io/).

This repository contains multiple specifications adapted by us (George Pîrlea
and Darius Foo) from three different existing Raft TLA specifications, which can
be found in the `thirdparty` folder:

- `raft_original.tla` is the Raft spec published by Diego Ongaro [in
2014](https://github.com/ongardie/raft.tla)

- `raft_membership.tla` is an extension of Ongaro's spec with cluster
membership changes, due to Brandom Amos and Huanchen Zhang; they developed it
as a [course project in
2015](https://www.cs.cmu.edu/~aplatzer/course/pls15/projects/bamos.pdf)

- `raft_dricketts.tla` is an extension of Ongaro's spec by Daniel Ricketts,
[developed in 2016]((https://github.com/dricketts/raft.tla)); it refactors
Ongaro's spec to make it more readable, adds some TLAPS proofs, and states some
properties (some of which are incorrect)

Our specifications (really, different versions of the same specification) are
as follows:

- `apalache_no_membership` -- a version of Ricketts' spec with annotations for
the [Apalache symbolic model checker](https://apalache.informal.systems/); this
folder also contains annotated versions of some TLA libraries used in our
specification; this version _does not_ have membership changes

- `tlc_membership` -- a version with _membership changes_ and extra properties;
we passed it to TLC to generate long traces via "punctuated search"; **if you
are not interested in Apalache, this is the version you want to look at**

- `apalache_membership_broken` -- an attempt to make the `membership` version
work with Apalache; abandoned after fighting with Apalache's type inference
algorithm for too long; if you make this work, please let us know!

## Attribution & Licensing

Our specifications are based on the spec written by [Diego
Ongaro](https://github.com/ongardie/raft.tla), with improvements due to [Daniel
Ricketts](https://github.com/dricketts/raft.tla), and the [addition of cluster
membership
changes](https://www.cs.cmu.edu/~aplatzer/course/pls15/projects/bamos.pdf) due
to Brandon Amos and Huanchen Zhang. We thank them for making these available
under a permissive license.

This work is licensed under the Creative Commons Attribution-4.0 International
License https://creativecommons.org/licenses/by/4.0/.