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
    \* @type: Int -> Int
    validators

VARIABLES
    (* @type: [
        actionType: Str,
        SendToEthereum: [ flag: Int, validator: Int, sendAmount: Int ]
    ]*)
    action,
    \* @type: Bool
    erc20Deployed

Init ==
    /\  action = [ actionType |-> "Init" ]
    /\  erc20Deployed = FALSE

SendToEthereum ==
    /\  erc20Deployed = TRUE
    /\  \E v \in validators:
            action' = [ actionType |-> "SendToEthereum", SendToEthereum |-> [ validator |-> v, sendAmount |-> 1 ] ]
    /\  UNCHANGED <<erc20Deployed>>

DeployERC20 ==
    /\  erc20Deployed' = TRUE
    /\  action' = [  actionType |-> "Erc20DeployedEvent" ]

Next ==
    \/  SendToEthereum
    \/  DeployERC20
===============================================================================