#!/bin/bash

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/env.sh

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

TESTS=(vlan_virt.m4 vxlan_virt.m4 isdx.m4 stags b4 f10)

for t in ${TESTS[@]}; do
        printf "${GREEN}Starting test: ${t}${NC}\n"
        if [[ ${t} == *.m4 ]]
        then
            m4 -I examples examples/${t}.ccn > examples/${t%%.*}.ccn
        fi
        ${COCOON_PATH} examples/${t%%.*}.ccn 15
        if [ $? -eq 0 ]
        then
            $THISDIR/tools/run_corral.sh examples/${t%%.*}/boogie
        fi
        printf "\n"
done
