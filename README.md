# Raft TLA specification

Formal TLA+ specification for the [Raft consensus
algorithm](https://raftconsensus.github.io/).

This specification includes type annotations, so it can be model-checked via
the [Apalache symbolic model checker](https://apalache.informal.systems/). (It
can also be model-checked in the usual fashion with TLC.)

The specification combines three different Raft TLA specifications, which can
be found in the `thirdparty` folder.

Daniel Ricketts' specification includes some
[TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) proofs (removed
from this version) that you might find interesting.

## Attribution & Licensing

The specification is based on the spec written by [Diego
Ongaro](https://github.com/ongardie/raft.tla), with improvements due to
[Daniel Ricketts](https://github.com/dricketts/raft.tla), and the addition of
cluster membership changes due to Brandon Amos and Huanchen Zhang.

This work is licensed under the Creative Commons Attribution-4.0 International
License https://creativecommons.org/licenses/by/4.0/.