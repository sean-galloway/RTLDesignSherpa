// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Package: stream_char_cfg_pkg
// Purpose: Per-build configuration knobs for the STREAM characterization
//          environment.
//
// Why a package:
//   The interesting characterization parameters (engine outstanding-queue
//   depths, response-delay queue capacities) are plumbed all the way down
//   from stream_char_top → stream_char_harness → stream_top_ch8 →
//   stream_core. Centralising them here gives one file to edit per config
//   instead of hunting through three modules.
//
// How to sweep a parameter for a build campaign:
//   The cleanest workflow is to keep one variant package per config and
//   swap which one is in the filelist — e.g.:
//     stream_char_cfg_pkg.sv             ← default (this file, AR=AW=8)
//     stream_char_cfg_pkg_deep.sv        ← AR=AW=16 (deeper side-Qs)
//     stream_char_cfg_pkg_shallow.sv     ← AR=AW=4  (shallower)
//   Each defines the SAME package name (stream_char_cfg_pkg) with
//   different parameter values. The Makefile/filelist picks one.
//
//   Alternatively, override at the stream_char_top instantiation —
//   useful for one-off experiments without creating a new package file.

`timescale 1ns / 1ps

package stream_char_cfg_pkg;

    // -------------------------------------------------------------------------
    // STREAM engine outstanding queues ("side-Qs")
    // -------------------------------------------------------------------------
    // Maximum number of in-flight read/write bursts per engine. These set
    // the depth of stream_core's AR/AW reorder/tracking queues. They are
    // the primary lever for measuring how much memory latency the engines
    // can hide via multi-outstanding pipelining.
    //
    // Little's Law: a sustained transfer hides L cycles of round-trip
    // memory latency when AR_MAX_OUTSTANDING × burst_len >= L.
    //   AR=8, burst=16 → covers 128 cycles before throughput degrades.
    parameter int CFG_AR_MAX_OUTSTANDING = 8;
    parameter int CFG_AW_MAX_OUTSTANDING = 8;

    // -------------------------------------------------------------------------
    // axi_response_delay queue capacities (slave-side memory model)
    // -------------------------------------------------------------------------
    // CAPACITY is the maximum number of beats / BRESPs the pipelined delay
    // block holds in flight. Must be >= engine outstanding × max_burst on
    // the R side, >= engine outstanding on the B side. Power-of-2.
    parameter int CFG_RESP_DELAY_R_CAPACITY = 256;
    parameter int CFG_RESP_DELAY_B_CAPACITY = 16;

endpackage : stream_char_cfg_pkg
