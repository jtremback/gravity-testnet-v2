mod utils;

use crate::utils::*;
use async_std::task::block_on;
use clarity::{constants::ZERO_ADDRESS, Address as EthAddress};
use cosmos_gravity::send::send_to_eth;
use deep_space::coin::Coin;
use deep_space::Address as CosmosAddress;
use deep_space::Contact;
use std::{env, time::Duration};

fn main() {
    let denom: String = "footoken".into();
    let vitaliks_eth_address =
        EthAddress::parse_and_validate("0xAb5801a7D398351b8bE11C439e05C5B3259aeC9B").unwrap();

    let keys = get_keys();

    let contact = Contact::new(
        "http://localhost:9090".into(),
        Duration::from_secs(30),
        CosmosAddress::DEFAULT_PREFIX,
    )
    .unwrap();

    block_on(send_to_eth(
        keys[0].validator_key,
        vitaliks_eth_address,
        Coin {
            denom: denom.clone(),
            amount: 1_000_000u64.into(),
        },
        Coin {
            denom: denom.clone(),
            amount: 1u64.into(),
        },
        Coin {
            denom: denom.clone(),
            amount: 1u64.into(),
        },
        &contact,
    ))
    .unwrap();
}
