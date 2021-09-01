# Gravity Bridge MBT Testnet

This repo allows you to run MBT tests on the Gravity Bridge Cosmos Module. It does not test the Gravity.sol Ethereum contract, or the Gravity Orchestrator off chain binary. Both of these elements will need to be modeled by the MBT tests to properly test the module.

## Usage

Use `bash run-testnet.sh` to start a 3 node Cosmos testnet with the Gravity module installed. This runs in a Docker container for portability, and exposes the necessary ports.

Use `bash run-tests.sh` to run the rust MBT tests on the testnet. This command copies the keys of the validators in the testnet out of the Docker container and into this directory. Then, the tests pick up these keys and can use them to send messages into the Cosmos mempool, as if they were signed by the validators.

These tests are located in the `rust` directory, and the accompanying TLA+ specifications are in the `tla` directory. 
