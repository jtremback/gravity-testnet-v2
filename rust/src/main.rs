mod utils;

use crate::utils::*;
use anyhow::Result;
use async_std::task::block_on;
use clarity::Address as EthAddress;
use cosmos_gravity::send::send_to_eth;
use cosmos_gravity::utils::wait_for_cosmos_online;
use deep_space::coin::Coin;
use deep_space::Address as CosmosAddress;
use deep_space::Contact as DeepSpaceContact;
use modelator::StepRunner;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::Deref;
use std::time::Duration;

fn main() {
    mbt_test();
    // manual_test()
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
    validator: usize,
    sendAmount: usize,
}

#[derive(Clone)]
struct Contact(DeepSpaceContact);

impl fmt::Debug for Contact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Contact").finish()
    }
}

impl Deref for Contact {
    type Target = DeepSpaceContact;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
struct TestRunner {
    contact: Contact,
    keys: Vec<ValidatorKeys>,
}

impl StepRunner<Step> for TestRunner {
    fn initial_step(&mut self, step: Step) -> Result<(), String> {
        dbg!(step);
        Ok(())
    }

    fn next_step(&mut self, step: Step) -> Result<(), String> {
        dbg!(step.clone());
        match step.action {
            Action::Init => {
                Err("The action should never be in the init state after the init step".into())
            }
            Action::SendToEthereum(action) => {
                let denom: String = "footoken".into();
                let vitaliks_eth_address =
                    EthAddress::parse_and_validate("0xAb5801a7D398351b8bE11C439e05C5B3259aeC9B")
                        .unwrap();

                // keys array is 0-indexed, everything else is 1-indexed
                let validator_key = self.keys[action.validator - 1].validator_key;

                dbg!(block_on(send_to_eth(
                    validator_key,
                    vitaliks_eth_address,
                    Coin {
                        denom: denom.clone(),
                        amount: 1000u64.into(),
                    },
                    Coin {
                        denom: denom.clone(),
                        amount: 2u64.into(),
                    },
                    Coin {
                        denom: denom.clone(),
                        amount: 3u64.into(),
                    },
                    &self.contact,
                ))
                .unwrap());

                Ok(())
            }
        }
    }
}

fn mbt_test() {
    let contact = Contact(
        DeepSpaceContact::new(
            "http://localhost:9090".into(),
            Duration::from_secs(30),
            CosmosAddress::DEFAULT_PREFIX,
        )
        .unwrap(),
    );

    block_on(wait_for_cosmos_online(&*contact, Duration::from_secs(30)));

    let keys = get_keys();

    for key in keys.clone() {
        let pk = key.validator_key;
        let addr = pk.to_address(&contact.get_prefix()).unwrap();
        dbg!(addr);
    }

    let tla_tests_file = "../tla/GravityMBTTests.tla";
    let tla_config_file = "../tla/GravityMBTTests.cfg";

    let runtime = modelator::ModelatorRuntime::default();
    let mut system = TestRunner { contact, keys };
    runtime
        .run_tla_steps(tla_tests_file, tla_config_file, &mut system)
        .unwrap();
}
