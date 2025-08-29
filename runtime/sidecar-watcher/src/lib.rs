// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

pub mod assumption;
pub mod break_glass;
pub mod broker;
pub mod cert_v1;
pub mod declassify;
pub mod dfa;
pub mod effects;
pub mod egress_cert;
pub mod events;
pub mod label_witness;
pub mod ni_monitor;
pub mod permit_enforcement;
pub mod policy_adapter;
pub mod queue_manager;
pub mod ratelimit;
pub mod replay;
pub mod revocation;
pub mod scheduler;

use anyhow::Result;
use assumption::{Assumption, AssumptionMonitor};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
pub struct Action {
    #[serde(rename = "action")]
    pub action_type: String,
    pub spam_score: Option<f64>,
    pub usd_amount: Option<f64>,
}

pub struct JsonProcessor {
    assumption_monitor: AssumptionMonitor,
    budget_limit: f64,
    spam_score_limit: f64,
    running_spend: f64,
}

impl JsonProcessor {
    pub fn new(budget_limit: f64, spam_score_limit: f64) -> Self {
        Self {
            assumption_monitor: AssumptionMonitor::new(),
            budget_limit,
            spam_score_limit,
            running_spend: 0.0,
        }
    }

    pub fn process_json_line(&mut self, line: &str) -> Result<bool> {
        // Process action messages
        if line.contains("\"action\":") {
            if let Ok(action) = serde_json::from_str::<Action>(line) {
                return self.process_action(&action);
            }
        }

        // Process assumption messages
        if line.contains("\"assumption\":") {
            if let Ok(assumption) = serde_json::from_str::<Assumption>(line) {
                return self.process_assumption(assumption);
            }
        }

        Ok(true)
    }

    fn process_action(&mut self, action: &Action) -> Result<bool> {
        // Check spam score
        if let Some(score) = action.spam_score {
            if score > self.spam_score_limit {
                return Ok(false);
            }
        }

        // Check budget
        if let Some(amount) = action.usd_amount {
            self.running_spend += amount;
            if self.running_spend > self.budget_limit {
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn process_assumption(&mut self, assumption: Assumption) -> Result<bool> {
        self.assumption_monitor.process_assumption(assumption)
    }
}
