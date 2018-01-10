#!/bin/bash

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
INCLUDE_DIR=$THIS_DIR/../examples/include

source $THIS_DIR/../../../env.sh

set -x

for num_switches in `seq 20 10 200`; do
    $THIS_DIR/../../../tools/bootstrap.sh $THIS_DIR/../ovn.m4.ccn nodl
    OVSHOME=$THIS_DIR/../../../../ovs/
    export OVSHOME
    SWITCHES=`seq -s " " 11 1 $num_switches`
    export SWITCHES
    LOGFILE=$THIS_DIR/../ovn/test$num_switches.log
    export LOGFILE
    rm $LOGFILE
    export COCOON_PATH
    pushd $OVSHOME
    ./tests/testsuite -C tests AUTOTEST_PATH="::" 2324 -v
    popd
done
