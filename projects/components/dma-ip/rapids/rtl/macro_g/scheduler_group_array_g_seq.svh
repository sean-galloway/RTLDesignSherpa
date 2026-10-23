// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// scheduler_group_array_g_seq.svh -- the rapids-g sequencer block (rapids
// TASK-034), hand-written. bin/gen_rapids_g.py includes it in the shared-
// engine branch of the generated scheduler_group_array_g, in front of the
// scheduler loop, and wires each scheduler_g's seq_* port to these nets.
//
// One gatling (rapids_seq_g) serves every channel of this array: one hart
// per channel at 4 and 8 channels, two channels per hart at 16 (rapids_seq_g's
// NUM_HARTS default).

        logic [NUM_CHANNELS-1:0]        g_seq_wr_en, g_seq_attn, g_seq_fault;
        logic [4:0]                     g_seq_wr_addr, g_seq_rd_addr;
        logic [31:0]                    g_seq_wr_data;
        logic [7:0]                     g_seq_alg_max;
        logic [NUM_CHANNELS-1:0][31:0]  g_seq_rd_data;

        rapids_seq_g #(
            .NUM_CHANNELS   (NUM_CHANNELS)
        ) u_seq (
            .clk                (clk),
            .rst_n              (rst_n),
            .seq_restart        (seq_restart),
            .cfg_channel_reset  (cfg_channel_reset),
            .seq_wr_en          (g_seq_wr_en),
            .seq_wr_addr        (g_seq_wr_addr),
            .seq_wr_data        (g_seq_wr_data),
            .seq_rd_addr        (g_seq_rd_addr),
            .seq_rd_data        (g_seq_rd_data),
            .seq_attn           (g_seq_attn),
            .seq_fault          (g_seq_fault),
            .seq_alg_max        (g_seq_alg_max),
            .reg_cmd_valid      (seq_reg_cmd_valid),      // this half's register mailbox:
            .reg_cmd_ready      (seq_reg_cmd_ready),      //   the array's seq_reg_* ports
            .reg_cmd_pwrite     (seq_reg_cmd_pwrite),
            .reg_cmd_paddr      (seq_reg_cmd_paddr),
            .reg_cmd_pwdata     (seq_reg_cmd_pwdata),
            .reg_rsp_valid      (seq_reg_rsp_valid),
            .reg_rsp_ready      (seq_reg_rsp_ready),
            .reg_rsp_prdata     (seq_reg_rsp_prdata),
            .reg_rsp_pslverr    (seq_reg_rsp_pslverr),
            /* verilator lint_off PINCONNECTEMPTY */
            .hart_halted        ()
            /* verilator lint_on PINCONNECTEMPTY */
        );
