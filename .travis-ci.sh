set -e

pushd ..
wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
tar xf coq-8.5-build-local.tgz
export PATH=$PWD/coq-8.5/bin:$PATH
popd

./build.sh

case $DOWNSTREAM in
verdi)
  pushd ..
    git clone 'http://github.com/uwplse/verdi'
    pushd verdi
      ./build.sh
    popd

    git clone 'http://github.com/uwplse/verdi-raft'
    pushd verdi-raft
      ./build.sh
    popd
  popd
  ;;
esac

