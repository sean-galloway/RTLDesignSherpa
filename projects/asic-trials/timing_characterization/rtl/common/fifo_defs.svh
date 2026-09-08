// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: fifo_defs
// Purpose: FIFO Memory Definitions module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`ifndef FIFO_DEFS_SVH
`define FIFO_DEFS_SVH

typedef enum int { FIFO_AUTO=0, FIFO_SRL=1, FIFO_BRAM=2 } fifo_mem_t;

`endif // FIFO_DEFS_SVH
