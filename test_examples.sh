#!/usr/bin/env bash
SOURIR="../sourir"

# Move into examples directory
pushd examples > /dev/null 2>&1

# Create a temp directory
TEMPDIR=`mktemp -d`

# Confirm that we created the directory
if [[ ! "$TEMPDIR" || ! -d "$TEMPDIR" ]]; then
  echo "Could not create temp dir!"
  exit 1
fi

# Always delete temp dir and its contents
function cleanup {
  rm -rf "$TEMPDIR"
  popd > /dev/null 2>&1
}
trap cleanup EXIT

function runonetest {
  TEST=$1
  OPT=$2
  INP=$3
  yes $INP | timeout 20 $SOURIR "$TEST" --quiet > $TEMPDIR/$1.out
  yes $INP | timeout 20 $SOURIR "$TEST" --quiet --opt $OPT > $TEMPDIR/$1.opt.out
  diff $TEMPDIR/$1.out $TEMPDIR/$1.opt.out > /dev/null
  if [[ $? -ne 0 ]]; then
    echo "Test $TEST with optimizations $OPT and input $INP differed in output"
    return 1
  fi
}

# Test file $1
function runtest {
  TEST=$1
  runonetest "$TEST" all 0 && \
    runonetest "$TEST" all 1 && \
    runonetest "$TEST" all 3 && \
    runonetest "$TEST" prune 0 && \
    runonetest "$TEST" prune,const_fold 0 && \
    runonetest "$TEST" prune,min_live,const_fold 0 && \
    runonetest "$TEST" prune,min_live,hoist_drop 0 && \
    runonetest "$TEST" const_fold 0 && \
    runonetest "$TEST" hoist_assign 0 && \
    runonetest "$TEST" hoist_drop 0 && \
    runonetest "$TEST" min_live 0 && \
    runonetest "$TEST" min_live 1
}

# Iterate over examples in directory
ALL_OK=0
for f in *.sou; do
  runtest $f
  if [[ $? -ne 0 ]]; then
    echo "Example $f failed!"
    ALL_OK=127
  fi
done

exit $ALL_OK
