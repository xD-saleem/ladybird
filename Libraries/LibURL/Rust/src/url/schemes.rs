/*
 * Copyright (c) 2026, Saleem Adat<saleemadat@gmail.com>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

pub fn default_port(scheme: &str) -> Option<u16> {
    match scheme {
        "ftp" => Some(21),
        "http" => Some(80),
        "https" => Some(443),
        "ws" => Some(80),
        "wss" => Some(443),
        _ => None,
    }
}

pub fn is_special(scheme: &str) -> bool {
    matches!(scheme, "ftp" | "file" | "http" | "https" | "ws" | "wss")
}
