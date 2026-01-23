// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::MeterResult;

pub trait Meter {
    type Error;
    fn visit_nodes(&mut self, num_nodes: usize) -> MeterResult<(), Self::Error>;
    fn visit_edges(&mut self, total_edge_size: usize) -> MeterResult<(), Self::Error>;
}

pub struct DummyMeter;

impl Meter for DummyMeter {
    type Error = ();

    fn visit_nodes(&mut self, _num_nodes: usize) -> MeterResult<(), Self::Error> {
        Ok(())
    }

    fn visit_edges(&mut self, _total_edge_size: usize) -> MeterResult<(), Self::Error> {
        Ok(())
    }
}
