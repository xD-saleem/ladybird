/*
 * Copyright (c) 2026, Saleem Adat<saleemadat@gmail.com>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

use super::{host::Host, origin::Origin};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Url {
    pub scheme: String,
    pub username: String,
    pub password: String,
    pub host: Option<Host>,
    pub port: Option<u16>,
    pub paths: Vec<String>,
    pub query: Option<String>,
    pub fragment: Option<String>,
    pub opaque_path: bool,
}

impl Url {
    pub fn origin(&self) -> Origin {
        Origin::from_url(self)
    }
}
