mod utils;

use crate::utils::*;
use clarity::{constants::ZERO_ADDRESS, Address as EthAddress};
use cosmos_gravity::send::send_to_eth;

fn main() {
    let vitaliks_eth_address =
        EthAddress::parse_and_validate("0xAb5801a7D398351b8bE11C439e05C5B3259aeC9B").unwrap();

    let keys = get_keys();

    send_to_eth(
        keys[0].validator_key,
        vitaliks_eth_address,
        amount,
        bridge_fee,
        fee,
        contact,
    );
}
