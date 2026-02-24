/*
 * Copyright (c) 2026, Saleem Adat<saleemadat@gmail.com>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

use super::core::Url;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin {
    pub scheme: String,
    pub host: Option<String>,
    pub port: Option<u16>,
    pub opaque: bool,
}

impl Origin {
    pub fn from_url(url: &Url) -> Self {
        match url.scheme.as_str() {
            "ftp" | "http" | "https" | "ws" | "wss" => Origin {
                scheme: url.scheme.clone(),
                host: url.host.as_ref().map(|h| h.value.clone()),
                port: url.port,
                opaque: false,
            },
            "file" => Origin {
                scheme: "file".into(),
                host: None,
                port: None,
                opaque: true,
            },
            _ => Origin {
                scheme: url.scheme.clone(),
                host: None,
                port: None,
                opaque: true,
            },
        }
    }
}
