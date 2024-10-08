// Copyright (c) 2019 Intel Corporation. All rights reserved.
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Bindgen autogenerated structs for `x86_64` boot parameters.

#![cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(missing_docs)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

// Hide the autogenerated documentation for bindgen'ed sources.
#[doc(hidden)]
pub mod bootparam;

#[cfg(feature = "elf")]
pub mod elf;

#[cfg(feature = "elf")]
pub mod start_info;
