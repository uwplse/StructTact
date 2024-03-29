<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# StructTact

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/uwplse/StructTact/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/uwplse/StructTact/actions/workflows/docker-action.yml




StructTact is a Coq library of structural tactics as well as lemmas about
lists, finite types, and orders on strings that use the tactics.
The structural tactics enable a style of proof where hypothesis names
are never mentioned. When automatically generated names change during
proof development, structural tactics will still work.

## Meta

- Author(s):
  - Ryan Doenges
  - Karl Palmskog
  - Keith Simmons (initial)
  - James R. Wilcox (initial)
  - Doug Woos (initial)
- License: [BSD 2-Clause "Simplified" license](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `StructTact`
- Related publication(s):
  - [Verdi: A Framework for Implementing and Verifying Distributed Systems](https://homes.cs.washington.edu/~mernst/pubs/verify-distsystem-pldi2015.pdf) doi:[10.1145/2737924.2737958](https://doi.org/10.1145/2737924.2737958)

## Building and installation instructions

The easiest way to install StructTact is via
[OPAM](https://opam.ocaml.org/doc/Install.html):
```shell
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-struct-tact
```

To instead build and install manually, do:
``` shell
git clone https://github.com/uwplse/StructTact.git
cd StructTact
make   # or make -j <number-of-cores-on-your-machine>
make install
```

## Documentation

StructTact consists mainly of files originally developed as part of
the [Verdi framework][verdi-link], which have here been adapted for easier
reuse in other projects.

### Structural tactics

The structural tactics are found in the file `StructTactics.v`,
and are named by analogy to the structural properties of
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

For tactic documentation, see the inline comments in `StructTactics.v`.

### Utility definitions and lemmas

The file `Util.v` collects definitions, lemmas, and tactics about lists, booleans, propositions, and
functions that were useful in other projects. Notably, the following files are exported:

- `BoolUtil.v`: general boolean lemmas, tactics, and definitions
- `PropUtil.v`: general lemmas about propositions and sum types
- `Update.v`: function `update` that modifies a function to return a new value for a specific argument
- `Update2.v`: function `update2` that modifies a function to return a new value for specific pair of arguments
- `ListTactics.v`: tactics operating on contexts with `map`, `NoDup`, and `In`
- `ListUtil.v`: general list lemmas, involving, e.g., `NoDup`, `map`, `filter`, and `firstn`
- `Assoc.v`: association lists with get, set, and delete functions
- `Before.v`: relation `before` capturing when an element appears before another in a list
- `Dedup.v`: function `dedup` remove duplicates from a list using decidable equality
- `FilterMap.v`: function `filterMap` that maps a partial function on a list and ignores failures
- `Nth.v`: relation `Nth` capturing the element at some position in a list
- `Prefix.v`: relation `Prefix` capturing when one list is a prefix of another
- `RemoveAll.v`: function `remove_all` which removes all elements of one list from another; set subtraction
- `Subseq.v`: relation `subseq` capturing when one list is a subsequence of another

### Finite types

The file `Fin.v` contains definitions and lemmas related to `fin n`, a type with `n` elements,
isomorphic to `Fin.t n` from the standard library, but with a slightly different
definition that is more convenient to work with.

The following constructions are defined on `fin`:

- `fin_eq_dec`: decidable equality
- `all_fin n`: list of all elements of `fin n`
- `fin_to_nat`: convert a `fin n` to a `nat`
- `fin_lt`: an ordering on `fin n`, implemented using `fin_to_nat`
- `fin_OT_compat`: legacy `OrderedType` module for `fin n` (for use with `FMap`)
- `fin_OT`: modern `OrderedType` module for `fin n` (for use with `MSet`)
- `fin_of_nat`: convert a `nat` to a `fin n`, when possible

### String orders

The file `StringOrders.v` contains some order relations on strings, in particular a total lexicographic order.

The following modules are defined:

- `string_lex_as_OT_compat`: legacy `OrderedType` module for `string` (for use with `FMap`)
- `string_lex_as_OT`: modern `OrderedType` module for `string` (for use with `MSet`)

[verdi-link]: https://github.com/uwplse/verdi
