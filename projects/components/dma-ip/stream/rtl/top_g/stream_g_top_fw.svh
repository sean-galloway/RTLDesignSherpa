// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// stream_g_top_fw.svh -- the firmware-load glue (stream TASK-020, as rapids
// TASK-038), hand-written. bin/gen_stream_g.py includes it in the generated
// stream_g_top_ch{8,16} in front of the hwif_in block, and sets the FW_*
// read-back fields inside it.
//
// The FW_* registers drive the core's gatling (rapids_seq_g fw_*): FW_CTRL.HOLD
// and ALG_MAX straight through; a write to FW_DATA stores the word at FW_ADDR
// the clock after (the register's value has settled by then), and FW_ADDR
// advances after each FW_DATA write and each FW_RDATA read, so a load or a
// readback is one FW_ADDR write and then a run of data accesses. On a ROM
// build (FW_WRITABLE = 0) nothing advances and the gatling ignores the bus.

    // swmod / swacc are a two-cycle LEVEL behind peakrdl_to_cmdrsp
    // (vault/handbook/design/generated-rtl-discipline.md), so each access is
    // taken on its rising edge, one flop late to line up with the field
    // storage. Counting every cycle stored each word twice and advanced
    // FW_ADDR by two (found on rapids-g).
    logic        w_fw_wr;
    logic [31:0] w_fw_rd_data;
    logic        r_fw_wr, r_fw_rd, r_fw_wr_d, r_fw_rd_d;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_fw_wr   <= 1'b0;
            r_fw_rd   <= 1'b0;
            r_fw_wr_d <= 1'b0;
            r_fw_rd_d <= 1'b0;
        end else begin
            r_fw_wr   <= hwif_out.FW_DATA.DATA.swmod;
            r_fw_rd   <= hwif_out.FW_RDATA.DATA.swacc;
            r_fw_wr_d <= r_fw_wr;
            r_fw_rd_d <= r_fw_rd;
        end
    )
    // One clock per access, a clock after its first (FW_DATA's value has settled)
    assign w_fw_wr = r_fw_wr && !r_fw_wr_d;
    wire w_fw_adv = (FW_WRITABLE != 0) && (w_fw_wr || (r_fw_rd && !r_fw_rd_d));
