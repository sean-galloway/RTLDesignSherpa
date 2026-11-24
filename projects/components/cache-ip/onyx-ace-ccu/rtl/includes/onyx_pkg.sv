// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_pkg
// Purpose: onyx's own constants -- the MonBus event classes its observer
//   emits (D9) and the house monitor ids it uses. Geometry and the ACE
//   request classes stay in l1_pkg (shared with the caches).
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/ch04_interfaces/04_observation_monbus.md
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-21

package onyx_pkg;

    // ------------------------------------------------------------------
    // MonBus event classes (PktTypePerf, PROTOCOL_CORE) -- D9. Codes 0x20
    // and up: the caches' l1_monlite uses 0x00-0x09 and jet's monlite
    // 0x10-0x16, so one tally profile can hold all three agents.
    // ------------------------------------------------------------------
    typedef enum logic [7:0] {
        ONYX_EV_TXN_START   = 8'h20,   // a grant: a transaction allocated (port, class, slot)
        // 8'h21 was SNOOP_OUT (AC handshakes per cycle), retired as redundant: TXN_START x (N_PORTS-1)
        ONYX_EV_GATHER_DONE = 8'h22,   // the last CR of a slot: verdict (DT, PD), gather latency
        ONYX_EV_MEM_READ    = 8'h23,   // a memory AR taken (slot)
        ONYX_EV_READ_WASTED = 8'h24,   // a DataTransfer verdict for a slot whose read was issued or presented: its beats are dropped
        ONYX_EV_ABSORB      = 8'h25,   // a PassDirty line written to memory (BRESP)
        ONYX_EV_WRITEBACK   = 8'h26,   // a cache write-back taken on the write port (AW)
        ONYX_EV_LOCK_WAIT   = 8'h27    // a port's candidate waited behind a held line: episode duration (emitted on release)
    } onyx_event_t;

    // ------------------------------------------------------------------
    // The IO port's grant classes (D1).  A grant's class rides TXN_START
    // in the l1_pkg ACE request-class code space (3 bits); the IO port has
    // no sideband, so its two transaction kinds take the codes the caches
    // never allocate a transaction under: 7 is unused by l1_pkg, 5 is
    // EVICT, which allocates nothing.  The port field (N_PORTS = the IO
    // port) disambiguates in any case.
    // ------------------------------------------------------------------
    localparam logic [2:0] ONYX_CLS_IO_READ  = 3'd7;   // ReadOnce (shareable) or ReadNoSnoop
    localparam logic [2:0] ONYX_CLS_IO_WRITE = 3'd5;   // WriteUnique / WriteLineUnique (shareable)

    // house monitor ids: the caches use 0x00A0 (l1_monlite), 0x00A1 (the
    // transport observers) and 0x00A2 (jet's monlite); onyx is 0x00A3
    localparam logic [15:0] ONYX_AGENT_ID = 16'h00A3;
    localparam logic [7:0]  ONYX_UNIT_ID  = 8'h01;

endpackage : onyx_pkg
