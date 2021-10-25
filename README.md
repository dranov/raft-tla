# TLA+ specifications for Raft, including membership changes

This repository contains a number of TLA+ specifications of the [Raft consensus protocol](https://raftconsensus.github.io/). Of particular interest are the following:

- `tlc_membership` -- a version of Raft with one-at-a-time **membership changes** (as described in [Ongaro's PhD disseration](https://web.stanford.edu/~ouster/cgi-bin/papers/OngaroPhD.pdf)). This includes a few "interesting" scenarios (properties) which can be passes to TLC to generate long traces via "punctuated search".

- `apalache_no_membership` -- a version of Ricketts' spec with **type annotations** for
the [Apalache symbolic model checker](https://apalache.informal.systems/). This
folder also contains annotated versions of some TLA libraries used in our
specification, but _does not_ model membership changes.

The `apalache_no_membership` spec is known to work with Apalache 0.16.5 build 417cf58.

## Original specs

This repository contains specifications adapted by us (George Pîrlea
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

## Abandoned effort to annotate membership changes

Besides the above, this repository also contains an abandoned effort to add type annotations to the version of the spec that includes membership changes.

- `apalache_membership_broken` -- an attempt to make the `membership` version
work with (an older version of) Apalache, abandoned after fighting with the
type inference algorithm for too long. If you make this work, please let us know by submiting a pull request.


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