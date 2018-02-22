#!/usr/bin/env bash

set -ev

export DOWNSTREAM=$1

eval $(opam config env)

opam repo add proofengineering-dev http://opam-dev.proofengineering.org

opam update

opam pin add StructTact . --yes --verbose

case ${DOWNSTREAM} in
verdi-raft)
  opam install verdi-raft --yes --verbose
  ;;
esac
