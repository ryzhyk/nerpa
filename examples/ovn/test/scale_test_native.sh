#!/bin/bash

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/../../../env.sh

set -x

for num_switches in `seq 20 10 200`; do
    OVSHOME=$THIS_DIR/../../../../ovs/
    rm $OVSHOME/ovn-nbctl
    rm $OVSHOME/ovn-controller
    rm $OVSHOME/ovs-vsctl
    export OVSHOME
    SWITCHES=`seq -s " " 11 1 $num_switches`
    export SWITCHES
    pushd $OVSHOME
    ./tests/testsuite -C tests AUTOTEST_PATH="utilities:vswitchd:ovsdb:vtep:tests::ovn/controller-vtep:ovn/northd:ovn/utilities:ovn/controller" 2324 -v
    popd
done
