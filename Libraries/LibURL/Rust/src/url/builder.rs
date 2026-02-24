/*
 * Copyright (c) 2026, Saleem Adat<saleemadat@gmail.com>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

use super::core::Url;
use super::host::Host;

#[derive(Default)]
pub struct UrlBuilder {
    scheme: Option<String>,
    username: Option<String>,
    password: Option<String>,
    host: Option<Host>,
    port: Option<u16>,
    paths: Vec<String>,
    query: Option<String>,
    fragment: Option<String>,
    opaque_path: bool,
}

impl UrlBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn scheme(mut self, v: impl Into<String>) -> Self {
        self.scheme = Some(v.into());
        self
    }

    pub fn host(mut self, v: impl Into<String>) -> Self {
        self.host = Some(Host::new(v.into()));
        self
    }

    pub fn push_path(mut self, v: impl Into<String>) -> Self {
        self.paths.push(v.into());
        self
    }

    pub fn build(self) -> Url {
        Url {
            scheme: self.scheme.unwrap_or_default(),
            username: self.username.unwrap_or_default(),
            password: self.password.unwrap_or_default(),
            host: self.host,
            port: self.port,
            paths: self.paths,
            query: self.query,
            fragment: self.fragment,
            opaque_path: self.opaque_path,
        }
    }
}
