# StructTact
StructTact is a library of "structural tactics" (`StructTactics.v`) and
a library of lemmas about lists (`Util.v`) that uses the tactics library.
These files were originally developed in the context of [Verdi](http://github.com/uwplse/verdi),
but have since been factored out to make them easier to use in other projects.

If you are interested in using StructTact in a project that does not already
manage its dependencies, we recommend using [`coqproject.sh`](https://github.com/dwoos/coqproject).

## Structural Tactics
Structural tactics are named by analogy to the structural properties of
simple type systems: weakening, exchange, and contraction.
In the context of proof assistants, these are analogous to the ability to add
new hypotheses in the context, reorder existing hypotheses, and delete
unused hypotheses. Theoretically, Coq inherits these properties from the
underlying type system, but in practice, automatically generated hypothesis
names cause proof scripts to break when the context is adjusted in seemingly
irrelevant ways.

Structural tactics restore these properties at the level of Ltac by enabling a
style of proof where hypothesis names are never mentioned. When automatically
generated names change during proof development, structural tactics still work.

## Util
This file contains definitions and lemmas about lists that were useful in other
projects. Most of the file consists of the following definitions and associated lemmas.
* association lists: get, set, delete
* `dedup`: remove duplicates from a list using decidable equality
* `subseq`: relation capturing when one list is a subsequence of another
* `fin`: an alternative definition of a type isomorphic to `Fin.t`
* `Prefix`: relation capturing when one list is a prefix of another
* `filterMap`: useful helper function that maps a partial function and ignores failures
* `before`: relation capturing when an element appears before another in a list
* `remove_all`: removes all elements of one list from another; set subtraction

