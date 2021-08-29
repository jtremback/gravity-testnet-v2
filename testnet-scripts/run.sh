#!/bin/bash
# Number of validators to start
NODES=$1
set -eux

# this directy of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Stop any currently running gravity and eth processes
pkill gravityd || true # allowed to fail

# Wipe filesystem changes
for i in $(seq 1 "$NODES");
do
    rm -rf "/validator$i"
done

/bin/bash "$DIR/setup-validators.sh" "$NODES"
/bin/bash "$DIR/start-validators.sh" "$NODES"

# This keeps the script open to prevent Docker from stopping the container
# immediately if the nodes are killed by a different process
read -p "Press Return to Close..."