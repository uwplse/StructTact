set -e

opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.$COQ_VERSION --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi)
  opam install coq-mathcomp-ssreflect.$SSREFLECT_VERSION --yes --verbose

  pushd ..
    git clone 'https://github.com/DistributedComponents/InfSeqExt.git'
    pushd InfSeqExt
      ./build.sh
    popd

    git clone 'https://github.com/uwplse/verdi.git'
    pushd verdi
      ./build.sh
    popd

    git clone 'https://github.com/uwplse/verdi-raft.git'
    pushd verdi-raft
      ./build.sh
    popd
  popd
  ;;
esac

