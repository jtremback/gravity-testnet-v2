mod utils;

use crate::utils::*;
use anyhow::{anyhow, Result};
use async_std::task::block_on;
use clarity::Address as EthAddress;
use cosmos_gravity::send::send_to_eth;
use cosmos_gravity::utils::wait_for_cosmos_online;
use deep_space::coin::Coin;
use deep_space::Address as CosmosAddress;
use deep_space::Contact;
use modelator::ModelatorRuntime;
use modelator::StepRunner;
use serde::{Deserialize, Serialize};
use serde_json;
use std::time::Duration;

fn main() {
    // mbtTest();
    manualTest()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Step {
    action: Action,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "actionType")]
enum Action {
    Init,
    SendToEthereum(SendToEthereum),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SendToEthereum {
    validator: Option<u32>,
    sendAmount: Option<u32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TestRunner {}

impl StepRunner<Step> for TestRunner {
    fn initial_step(&mut self, step: Step) -> Result<(), String> {
        dbg!(step);
        Ok(())
    }

    fn next_step(&mut self, step: Step) -> Result<(), String> {
        dbg!(step.clone());
        match step.action {
            Action::Init => {
                Err("The action should never be in the init state, after the init step".into())
            }
            Action::SendToEthereum(action) => {
                dbg!(action);
                Ok(())
            }
        }
    }
}

fn mbtTest() {
    let tla_tests_file = "../tla/GravityMBT.tla";
    let tla_config_file = "../tla/GravityMBT.cfg";

    let runtime = modelator::ModelatorRuntime::default();
    let mut system = TestRunner {};
    runtime
        .run_tla_steps(tla_tests_file, tla_config_file, &mut system)
        .unwrap();
}

fn manualTest() {
    let denom: String = "footoken".into();
    let vitaliks_eth_address =
        EthAddress::parse_and_validate("0xAb5801a7D398351b8bE11C439e05C5B3259aeC9B").unwrap();

    let contact = Contact::new(
        "http://localhost:9090".into(),
        Duration::from_secs(30),
        CosmosAddress::DEFAULT_PREFIX,
    )
    .unwrap();

    let keys = get_keys();

    for key in keys.clone() {
        let pk = key.validator_key;
        let addr = pk.to_address(&contact.get_prefix()).unwrap();
        dbg!(addr);
    }

    block_on(wait_for_cosmos_online(&contact, Duration::from_secs(30)));

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
