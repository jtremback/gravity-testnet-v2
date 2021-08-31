--------------------------- MODULE GravityMBT ---------------------------

(*
This spec is intended to model the behaviors of several different actors interacting with a gravity bridge,
in order to test the Gravity Cosmos Module:

- Cosmos and Ethereum users.
- The Gravity.sol Solidity contract and the Ethereum blockchain.
- "Orchestrator" binaries run by the validators of the Cosmos chain.
*)

\* This early version just sends cosmos coins onto Ethereum.

EXTENDS Integers

CONSTANTS
    \* @type: Set(Int)
    validators

VARIABLES
    \* @type: [ actionType: Str, validator: Int, sendAmount: Int ]
    action

Init ==
    action = [ actionType |-> "Init" ]

SendToEthereum ==
    \E v \in validators:
        action' = [ actionType |-> "SendToEthereum", validator |-> v, sendAmount |-> 1 ]

Next ==
    SendToEthereum
===============================================================================