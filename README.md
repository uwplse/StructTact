# StructTact
StructTact is a library of "structural tactics" (`StructTactics.v`) as well as
libraries containing lemmas about lists (`Util.v`) and finite types (`Fin.v`)
that use the tactics library.
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
This file collects definitions and lemmas about lists, booleans, and propositions
that were useful in other projects. Notably, the following files are exported:
* BoolUtil: general boolean lemmas, tactics, and definitions
* PropUtil: general lemmas about propositions and sum types
* ListTactics: tactics operating on contexts with `map`, `NoDup`, and `In`
* ListUtil: general list lemmas, involving, e.g., `NoDup`, `map`, and `filter`
* Assoc: association lists with get, set, and delete functions
* Before: relation `before` capturing when an element appears before another in a list
* Dedup: function `dedup` remove duplicates from a list using decidable equality
* FilterMap: function `filterMap` that maps a partial function on a list and ignores failures
* Nth: relation `Nth` capturing the element at some position in a list
* Prefix: relation `Prefix` capturing when one list is a prefix of another
* RemoveAll: function `remove_all` which removes all elements of one list from another; set subtraction
* Subseq: relation `subseq` capturing when one list is a subsequence of another
* Take: function `take` returning a prefix of some given size of a list

## Fin
This file contains an definitions and lemmas related to `fin n`, a type with `n` elements,
isomorphic to `Fin.t n` from the standard library, but with a slightly different
definition that is more convenient to work with.
The following constructions are defined on `fin`:
* `fin_eq_dec`: decidable equality
* `all_fin n`: list of all elements of `fin n`
* `fin_to_nat`: convert a `fin n` to a `nat`
* `fin_lt`: an ordering on `fin n`, implemented using `fin_to_nat`
* implementations of `OrderedType` of both kinds: legacy (for use with `FMap`) and new
  (for use with `MSet`)
