------------------------------ MODULE GravityMBTTests --------------------------------

EXTENDS GravityMBT

SentToEthereumTest ==
    /\ action.actionType = "SendToEthereum"

Neg == ~SentToEthereumTest

===============================================================================