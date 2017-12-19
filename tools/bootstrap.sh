#!/bin/bash

# bootstrap a Cocoon network

set -x
set -e

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
INCLUDE_DIR=$THIS_DIR/../examples/include

source $THIS_DIR/../env.sh

filename=$(basename "$1")
dir=$(dirname "$1")

if [ ${filename: -7} == ".m4.ccn" ];
then
    specname=$(basename "$1" ".m4.ccn")
    ccnname=$dir/$specname.ccn
    echo "Preprocessing $1"
    m4 --include=$INCLUDE_DIR $1 > $ccnname
else
    specname=$(basename "$1" ".ccn")
    ccnname=$1
fi

workdir=$dir/$specname

echo "Compiling $specname"

(set +x; echo Generating  SQL schema)
$COCOON_PATH -i $ccnname --action=sql

(set +x; echo Generating Datalog rules)
$COCOON_PATH -i $ccnname --action=dl --no-constraints

if (( $# > 1 )) && [ $2 = "nodl" ];
then
    (set +x; echo Skipping Datalog compilation)
else
    (set +x; echo Compiling Datalog rules)
    pushd $workdir
    cargo build
    pushd $popd
fi

# kill cocoon controller and CLI (if any)
set +e
sudo killall -qw -9 cocoon
set -e

(set +x; echo Initializing SQL DB)
set +e
sudo sudo -u postgres createuser -d root
set -e

sudo psql postgres -f $workdir/$specname.schema

(set +x; echo Starting Cocoon controller)
sudo $COCOON_PATH -i $ccnname --action=controller --no-constraints
