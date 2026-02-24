/*
 * Copyright (c) 2026, Saleem Adat<saleemadat@gmail.com>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Host {
    pub value: String,
}

impl Host {
    pub fn new(value: String) -> Self {
        Self { value }
    }
}
