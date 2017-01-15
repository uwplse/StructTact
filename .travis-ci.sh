set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq $COQ_VERSION --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi-raft)
  opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
  opam install coq-mathcomp-ssreflect.$SSREFLECT_VERSION InfSeqExt verdi-runtime --yes --verbose
  pushd ..
    git clone 'https://github.com/uwplse/verdi.git'
    pushd verdi
      StructTact_PATH=../StructTact ./build.sh
    popd
    git clone 'https://github.com/uwplse/verdi-raft.git'
    pushd verdi-raft
      StructTact_PATH=../StructTact Verdi_PATH=../verdi ./build.sh
    popd
  popd
  ;;
esac
