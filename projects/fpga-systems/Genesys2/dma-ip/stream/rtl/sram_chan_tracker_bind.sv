// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Binds sram_chan_tracker into every sram_controller instance — sim only.
// Pulls NUM_CHANNELS / DATA_WIDTH from the bound module's parameters via
// the `.*` connection so the same bind works regardless of channel count.
//
// Gated by `define ENHANCED_DEBUG (off by default). To enable: pass
// +define+ENHANCED_DEBUG on the simulator command line, or `define
// it before this file is parsed. Also gated by `ifndef SYNTHESIS so
// the FPGA build is always a no-op.

`timescale 1ns / 1ps

`ifdef ENHANCED_DEBUG
`ifndef SYNTHESIS
bind sram_controller sram_chan_tracker #(
    .NUM_CHANNELS (NUM_CHANNELS),
    .DATA_WIDTH   (DATA_WIDTH)
) u_chan_tracker (
    .clk                  (clk),
    .rst_n                (rst_n),
    .axi_rd_sram_valid    (axi_rd_sram_valid),
    .axi_rd_sram_ready    (axi_rd_sram_ready),
    .axi_rd_sram_id       (axi_rd_sram_id),
    .axi_rd_sram_data     (axi_rd_sram_data),
    .axi_wr_sram_drain      (axi_wr_sram_drain),
    .axi_wr_sram_valid      (axi_wr_sram_valid),
    .axi_wr_sram_valid_comb (axi_wr_sram_valid_comb),
    .axi_wr_sram_id         (axi_wr_sram_id),
    .axi_wr_sram_data       (axi_wr_sram_data)
);
`endif
`endif // ENHANCED_DEBUG
