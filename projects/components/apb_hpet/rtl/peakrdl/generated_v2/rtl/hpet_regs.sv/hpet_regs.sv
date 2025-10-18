// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_regs
// Purpose: Hpet Regs module
//
// Documentation: projects/components/peakrdl/PRD.md
// Subsystem: peakrdl
//
// Author: sean galloway
// Created: 2025-10-18

module hpet_regs (
        input wire clk,
        input wire rst,

        input wire s_cpuif_req,
        input wire s_cpuif_req_is_wr,
        input wire [8:0] s_cpuif_addr,
        input wire [31:0] s_cpuif_wr_data,
        input wire [31:0] s_cpuif_wr_biten,
        output wire s_cpuif_req_stall_wr,
        output wire s_cpuif_req_stall_rd,
        output wire s_cpuif_rd_ack,
        output wire s_cpuif_rd_err,
        output wire [31:0] s_cpuif_rd_data,
        output wire s_cpuif_wr_ack,
        output wire s_cpuif_wr_err,

        input hpet_regs_pkg::hpet_regs__in_t hwif_in,
        output hpet_regs_pkg::hpet_regs__out_t hwif_out
    );

    //--------------------------------------------------------------------------
    // CPU Bus interface logic
    //--------------------------------------------------------------------------
    logic cpuif_req;
    logic cpuif_req_is_wr;
    logic [8:0] cpuif_addr;
    logic [31:0] cpuif_wr_data;
    logic [31:0] cpuif_wr_biten;
    logic cpuif_req_stall_wr;
    logic cpuif_req_stall_rd;

    logic cpuif_rd_ack;
    logic cpuif_rd_err;
    logic [31:0] cpuif_rd_data;

    logic cpuif_wr_ack;
    logic cpuif_wr_err;

    assign cpuif_req = s_cpuif_req;
    assign cpuif_req_is_wr = s_cpuif_req_is_wr;
    assign cpuif_addr = s_cpuif_addr;
    assign cpuif_wr_data = s_cpuif_wr_data;
    assign cpuif_wr_biten = s_cpuif_wr_biten;
    assign s_cpuif_req_stall_wr = cpuif_req_stall_wr;
    assign s_cpuif_req_stall_rd = cpuif_req_stall_rd;
    assign s_cpuif_rd_ack = cpuif_rd_ack;
    assign s_cpuif_rd_err = cpuif_rd_err;
    assign s_cpuif_rd_data = cpuif_rd_data;
    assign s_cpuif_wr_ack = cpuif_wr_ack;
    assign s_cpuif_wr_err = cpuif_wr_err;

    logic cpuif_req_masked;

    // Read & write latencies are balanced. Stalls not required
    assign cpuif_req_stall_rd = '0;
    assign cpuif_req_stall_wr = '0;
    assign cpuif_req_masked = cpuif_req
                            & !(!cpuif_req_is_wr & cpuif_req_stall_rd)
                            & !(cpuif_req_is_wr & cpuif_req_stall_wr);

    //--------------------------------------------------------------------------
    // Address Decode
    //--------------------------------------------------------------------------
    typedef struct {
        logic HPET_ID;
        logic HPET_CONFIG;
        logic HPET_STATUS;
        logic RESERVED_0C;
        logic HPET_COUNTER_LO;
        logic HPET_COUNTER_HI;
        struct {
            logic TIMER_CONFIG;
            logic TIMER_COMPARATOR_LO;
            logic TIMER_COMPARATOR_HI;
            logic RESERVED;
        } TIMER[2];
    } decoded_reg_strb_t;
    decoded_reg_strb_t decoded_reg_strb;
    logic decoded_req;
    logic decoded_req_is_wr;
    logic [31:0] decoded_wr_data;
    logic [31:0] decoded_wr_biten;

    always_comb begin
        decoded_reg_strb.HPET_ID = cpuif_req_masked & (cpuif_addr == 9'h0);
        decoded_reg_strb.HPET_CONFIG = cpuif_req_masked & (cpuif_addr == 9'h4);
        decoded_reg_strb.HPET_STATUS = cpuif_req_masked & (cpuif_addr == 9'h8);
        decoded_reg_strb.RESERVED_0C = cpuif_req_masked & (cpuif_addr == 9'hc);
        decoded_reg_strb.HPET_COUNTER_LO = cpuif_req_masked & (cpuif_addr == 9'h10);
        decoded_reg_strb.HPET_COUNTER_HI = cpuif_req_masked & (cpuif_addr == 9'h14);
        for(int i0=0; i0<2; i0++) begin
            decoded_reg_strb.TIMER[i0].TIMER_CONFIG = cpuif_req_masked & (cpuif_addr == 9'h100 + (9)'(i0) * 9'h20);
            decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_LO = cpuif_req_masked & (cpuif_addr == 9'h104 + (9)'(i0) * 9'h20);
            decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_HI = cpuif_req_masked & (cpuif_addr == 9'h108 + (9)'(i0) * 9'h20);
            decoded_reg_strb.TIMER[i0].RESERVED = cpuif_req_masked & (cpuif_addr == 9'h10c + (9)'(i0) * 9'h20);
        end
    end

    // Pass down signals to next stage
    assign decoded_req = cpuif_req_masked;
    assign decoded_req_is_wr = cpuif_req_is_wr;
    assign decoded_wr_data = cpuif_wr_data;
    assign decoded_wr_biten = cpuif_wr_biten;

    //--------------------------------------------------------------------------
    // Field logic
    //--------------------------------------------------------------------------
    typedef struct {
        struct {
            struct {
                logic next;
                logic load_next;
            } hpet_enable;
            struct {
                logic next;
                logic load_next;
            } legacy_replacement;
        } HPET_CONFIG;
        struct {
            struct {
                logic [1:0] next;
                logic load_next;
            } timer_int_status;
        } HPET_STATUS;
        struct {
            struct {
                logic [31:0] next;
                logic load_next;
            } counter_lo;
        } HPET_COUNTER_LO;
        struct {
            struct {
                logic [31:0] next;
                logic load_next;
            } counter_hi;
        } HPET_COUNTER_HI;
        struct {
            struct {
                struct {
                    logic next;
                    logic load_next;
                } timer_enable;
                struct {
                    logic next;
                    logic load_next;
                } timer_int_enable;
                struct {
                    logic next;
                    logic load_next;
                } timer_type;
                struct {
                    logic next;
                    logic load_next;
                } timer_size;
                struct {
                    logic next;
                    logic load_next;
                } timer_value_set;
            } TIMER_CONFIG;
            struct {
                struct {
                    logic [31:0] next;
                    logic load_next;
                } timer_comp_lo;
            } TIMER_COMPARATOR_LO;
            struct {
                struct {
                    logic [31:0] next;
                    logic load_next;
                } timer_comp_hi;
            } TIMER_COMPARATOR_HI;
        } TIMER[2];
    } field_combo_t;
    field_combo_t field_combo;

    typedef struct {
        struct {
            struct {
                logic value;
            } hpet_enable;
            struct {
                logic value;
            } legacy_replacement;
        } HPET_CONFIG;
        struct {
            struct {
                logic [1:0] value;
            } timer_int_status;
        } HPET_STATUS;
        struct {
            struct {
                logic [31:0] value;
            } counter_lo;
        } HPET_COUNTER_LO;
        struct {
            struct {
                logic [31:0] value;
            } counter_hi;
        } HPET_COUNTER_HI;
        struct {
            struct {
                struct {
                    logic value;
                } timer_enable;
                struct {
                    logic value;
                } timer_int_enable;
                struct {
                    logic value;
                } timer_type;
                struct {
                    logic value;
                } timer_size;
                struct {
                    logic value;
                } timer_value_set;
            } TIMER_CONFIG;
            struct {
                struct {
                    logic [31:0] value;
                } timer_comp_lo;
            } TIMER_COMPARATOR_LO;
            struct {
                struct {
                    logic [31:0] value;
                } timer_comp_hi;
            } TIMER_COMPARATOR_HI;
        } TIMER[2];
    } field_storage_t;
    field_storage_t field_storage;

    // Field: hpet_regs.HPET_CONFIG.hpet_enable
    always_comb begin
        automatic logic [0:0] next_c;
        automatic logic load_next_c;
        next_c = field_storage.HPET_CONFIG.hpet_enable.value;
        load_next_c = '0;
        if(decoded_reg_strb.HPET_CONFIG && decoded_req_is_wr) begin // SW write
            next_c = (field_storage.HPET_CONFIG.hpet_enable.value & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
            load_next_c = '1;
        end
        field_combo.HPET_CONFIG.hpet_enable.next = next_c;
        field_combo.HPET_CONFIG.hpet_enable.load_next = load_next_c;
    end
    always_ff @(posedge clk) begin
        if(rst) begin
            field_storage.HPET_CONFIG.hpet_enable.value <= 1'h0;
        end else begin
            if(field_combo.HPET_CONFIG.hpet_enable.load_next) begin
                field_storage.HPET_CONFIG.hpet_enable.value <= field_combo.HPET_CONFIG.hpet_enable.next;
            end
        end
    end
    assign hwif_out.HPET_CONFIG.hpet_enable.value = field_storage.HPET_CONFIG.hpet_enable.value;
    // Field: hpet_regs.HPET_CONFIG.legacy_replacement
    always_comb begin
        automatic logic [0:0] next_c;
        automatic logic load_next_c;
        next_c = field_storage.HPET_CONFIG.legacy_replacement.value;
        load_next_c = '0;
        if(decoded_reg_strb.HPET_CONFIG && decoded_req_is_wr) begin // SW write
            next_c = (field_storage.HPET_CONFIG.legacy_replacement.value & ~decoded_wr_biten[1:1]) | (decoded_wr_data[1:1] & decoded_wr_biten[1:1]);
            load_next_c = '1;
        end
        field_combo.HPET_CONFIG.legacy_replacement.next = next_c;
        field_combo.HPET_CONFIG.legacy_replacement.load_next = load_next_c;
    end
    always_ff @(posedge clk) begin
        if(rst) begin
            field_storage.HPET_CONFIG.legacy_replacement.value <= 1'h0;
        end else begin
            if(field_combo.HPET_CONFIG.legacy_replacement.load_next) begin
                field_storage.HPET_CONFIG.legacy_replacement.value <= field_combo.HPET_CONFIG.legacy_replacement.next;
            end
        end
    end
    assign hwif_out.HPET_CONFIG.legacy_replacement.value = field_storage.HPET_CONFIG.legacy_replacement.value;
    // Field: hpet_regs.HPET_STATUS.timer_int_status
    always_comb begin
        automatic logic [1:0] next_c;
        automatic logic load_next_c;
        next_c = field_storage.HPET_STATUS.timer_int_status.value;
        load_next_c = '0;
        if(decoded_reg_strb.HPET_STATUS && decoded_req_is_wr) begin // SW write 1 clear
            next_c = field_storage.HPET_STATUS.timer_int_status.value & ~(decoded_wr_data[1:0] & decoded_wr_biten[1:0]);
            load_next_c = '1;
        end else begin // HW Write
            next_c = hwif_in.HPET_STATUS.timer_int_status.next;
            load_next_c = '1;
        end
        field_combo.HPET_STATUS.timer_int_status.next = next_c;
        field_combo.HPET_STATUS.timer_int_status.load_next = load_next_c;
    end
    always_ff @(posedge clk) begin
        if(field_combo.HPET_STATUS.timer_int_status.load_next) begin
            field_storage.HPET_STATUS.timer_int_status.value <= field_combo.HPET_STATUS.timer_int_status.next;
        end
    end
    // Field: hpet_regs.HPET_COUNTER_LO.counter_lo
    always_comb begin
        automatic logic [31:0] next_c;
        automatic logic load_next_c;
        next_c = field_storage.HPET_COUNTER_LO.counter_lo.value;
        load_next_c = '0;
        if(decoded_reg_strb.HPET_COUNTER_LO && decoded_req_is_wr) begin // SW write
            next_c = (field_storage.HPET_COUNTER_LO.counter_lo.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
            load_next_c = '1;
        end
        field_combo.HPET_COUNTER_LO.counter_lo.next = next_c;
        field_combo.HPET_COUNTER_LO.counter_lo.load_next = load_next_c;
    end
    always_ff @(posedge clk) begin
        if(rst) begin
            field_storage.HPET_COUNTER_LO.counter_lo.value <= 32'h0;
        end else begin
            if(field_combo.HPET_COUNTER_LO.counter_lo.load_next) begin
                field_storage.HPET_COUNTER_LO.counter_lo.value <= field_combo.HPET_COUNTER_LO.counter_lo.next;
            end
        end
    end
    assign hwif_out.HPET_COUNTER_LO.counter_lo.value = field_storage.HPET_COUNTER_LO.counter_lo.value;
    // Field: hpet_regs.HPET_COUNTER_HI.counter_hi
    always_comb begin
        automatic logic [31:0] next_c;
        automatic logic load_next_c;
        next_c = field_storage.HPET_COUNTER_HI.counter_hi.value;
        load_next_c = '0;
        if(decoded_reg_strb.HPET_COUNTER_HI && decoded_req_is_wr) begin // SW write
            next_c = (field_storage.HPET_COUNTER_HI.counter_hi.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
            load_next_c = '1;
        end
        field_combo.HPET_COUNTER_HI.counter_hi.next = next_c;
        field_combo.HPET_COUNTER_HI.counter_hi.load_next = load_next_c;
    end
    always_ff @(posedge clk) begin
        if(rst) begin
            field_storage.HPET_COUNTER_HI.counter_hi.value <= 32'h0;
        end else begin
            if(field_combo.HPET_COUNTER_HI.counter_hi.load_next) begin
                field_storage.HPET_COUNTER_HI.counter_hi.value <= field_combo.HPET_COUNTER_HI.counter_hi.next;
            end
        end
    end
    assign hwif_out.HPET_COUNTER_HI.counter_hi.value = field_storage.HPET_COUNTER_HI.counter_hi.value;
    for(genvar i0=0; i0<2; i0++) begin
        // Field: hpet_regs.TIMER[].TIMER_CONFIG.timer_enable
        always_comb begin
            automatic logic [0:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_CONFIG && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value & ~decoded_wr_biten[2:2]) | (decoded_wr_data[2:2] & decoded_wr_biten[2:2]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_CONFIG.timer_enable.next = next_c;
            field_combo.TIMER[i0].TIMER_CONFIG.timer_enable.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value <= 1'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_CONFIG.timer_enable.load_next) begin
                    field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value <= field_combo.TIMER[i0].TIMER_CONFIG.timer_enable.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_CONFIG.timer_enable.value = field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value;
        // Field: hpet_regs.TIMER[].TIMER_CONFIG.timer_int_enable
        always_comb begin
            automatic logic [0:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_CONFIG.timer_int_enable.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_CONFIG && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_CONFIG.timer_int_enable.value & ~decoded_wr_biten[3:3]) | (decoded_wr_data[3:3] & decoded_wr_biten[3:3]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_CONFIG.timer_int_enable.next = next_c;
            field_combo.TIMER[i0].TIMER_CONFIG.timer_int_enable.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_CONFIG.timer_int_enable.value <= 1'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_CONFIG.timer_int_enable.load_next) begin
                    field_storage.TIMER[i0].TIMER_CONFIG.timer_int_enable.value <= field_combo.TIMER[i0].TIMER_CONFIG.timer_int_enable.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_CONFIG.timer_int_enable.value = field_storage.TIMER[i0].TIMER_CONFIG.timer_int_enable.value;
        // Field: hpet_regs.TIMER[].TIMER_CONFIG.timer_type
        always_comb begin
            automatic logic [0:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_CONFIG.timer_type.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_CONFIG && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_CONFIG.timer_type.value & ~decoded_wr_biten[4:4]) | (decoded_wr_data[4:4] & decoded_wr_biten[4:4]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_CONFIG.timer_type.next = next_c;
            field_combo.TIMER[i0].TIMER_CONFIG.timer_type.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_CONFIG.timer_type.value <= 1'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_CONFIG.timer_type.load_next) begin
                    field_storage.TIMER[i0].TIMER_CONFIG.timer_type.value <= field_combo.TIMER[i0].TIMER_CONFIG.timer_type.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_CONFIG.timer_type.value = field_storage.TIMER[i0].TIMER_CONFIG.timer_type.value;
        // Field: hpet_regs.TIMER[].TIMER_CONFIG.timer_size
        always_comb begin
            automatic logic [0:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_CONFIG.timer_size.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_CONFIG && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_CONFIG.timer_size.value & ~decoded_wr_biten[5:5]) | (decoded_wr_data[5:5] & decoded_wr_biten[5:5]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_CONFIG.timer_size.next = next_c;
            field_combo.TIMER[i0].TIMER_CONFIG.timer_size.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_CONFIG.timer_size.value <= 1'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_CONFIG.timer_size.load_next) begin
                    field_storage.TIMER[i0].TIMER_CONFIG.timer_size.value <= field_combo.TIMER[i0].TIMER_CONFIG.timer_size.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_CONFIG.timer_size.value = field_storage.TIMER[i0].TIMER_CONFIG.timer_size.value;
        // Field: hpet_regs.TIMER[].TIMER_CONFIG.timer_value_set
        always_comb begin
            automatic logic [0:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_CONFIG.timer_value_set.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_CONFIG && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_CONFIG.timer_value_set.value & ~decoded_wr_biten[6:6]) | (decoded_wr_data[6:6] & decoded_wr_biten[6:6]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_CONFIG.timer_value_set.next = next_c;
            field_combo.TIMER[i0].TIMER_CONFIG.timer_value_set.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_CONFIG.timer_value_set.value <= 1'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_CONFIG.timer_value_set.load_next) begin
                    field_storage.TIMER[i0].TIMER_CONFIG.timer_value_set.value <= field_combo.TIMER[i0].TIMER_CONFIG.timer_value_set.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_CONFIG.timer_value_set.value = field_storage.TIMER[i0].TIMER_CONFIG.timer_value_set.value;
        // Field: hpet_regs.TIMER[].TIMER_COMPARATOR_LO.timer_comp_lo
        always_comb begin
            automatic logic [31:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_LO && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.next = next_c;
            field_combo.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value <= 32'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.load_next) begin
                    field_storage.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value <= field_combo.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value = field_storage.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value;
        // Field: hpet_regs.TIMER[].TIMER_COMPARATOR_HI.timer_comp_hi
        always_comb begin
            automatic logic [31:0] next_c;
            automatic logic load_next_c;
            next_c = field_storage.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value;
            load_next_c = '0;
            if(decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_HI && decoded_req_is_wr) begin // SW write
                next_c = (field_storage.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value & ~decoded_wr_biten[31:0]) | (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
                load_next_c = '1;
            end
            field_combo.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.next = next_c;
            field_combo.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.load_next = load_next_c;
        end
        always_ff @(posedge clk) begin
            if(rst) begin
                field_storage.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value <= 32'h0;
            end else begin
                if(field_combo.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.load_next) begin
                    field_storage.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value <= field_combo.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.next;
                end
            end
        end
        assign hwif_out.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value = field_storage.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value;
    end

    //--------------------------------------------------------------------------
    // Write response
    //--------------------------------------------------------------------------
    assign cpuif_wr_ack = decoded_req & decoded_req_is_wr;
    // Writes are always granted with no error response
    assign cpuif_wr_err = '0;

    //--------------------------------------------------------------------------
    // Readback
    //--------------------------------------------------------------------------

    logic readback_err;
    logic readback_done;
    logic [31:0] readback_data;

    // Assign readback values to a flattened array
    logic [31:0] readback_array[14];
    assign readback_array[0][4:0] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 5'h0 : '0;
    assign readback_array[0][5:5] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 1'h1 : '0;
    assign readback_array[0][6:6] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 1'h0 : '0;
    assign readback_array[0][7:7] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 1'h1 : '0;
    assign readback_array[0][12:8] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 5'h1 : '0;
    assign readback_array[0][15:13] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 3'h0 : '0;
    assign readback_array[0][23:16] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 8'h1 : '0;
    assign readback_array[0][31:24] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 8'h1 : '0;
    assign readback_array[1][0:0] = (decoded_reg_strb.HPET_CONFIG && !decoded_req_is_wr) ? field_storage.HPET_CONFIG.hpet_enable.value : '0;
    assign readback_array[1][1:1] = (decoded_reg_strb.HPET_CONFIG && !decoded_req_is_wr) ? field_storage.HPET_CONFIG.legacy_replacement.value : '0;
    assign readback_array[1][31:2] = (decoded_reg_strb.HPET_CONFIG && !decoded_req_is_wr) ? 30'h0 : '0;
    assign readback_array[2][1:0] = (decoded_reg_strb.HPET_STATUS && !decoded_req_is_wr) ? field_storage.HPET_STATUS.timer_int_status.value : '0;
    assign readback_array[2][31:2] = (decoded_reg_strb.HPET_STATUS && !decoded_req_is_wr) ? 30'h0 : '0;
    assign readback_array[3][31:0] = (decoded_reg_strb.RESERVED_0C && !decoded_req_is_wr) ? 32'h0 : '0;
    assign readback_array[4][31:0] = (decoded_reg_strb.HPET_COUNTER_LO && !decoded_req_is_wr) ? field_storage.HPET_COUNTER_LO.counter_lo.value : '0;
    assign readback_array[5][31:0] = (decoded_reg_strb.HPET_COUNTER_HI && !decoded_req_is_wr) ? field_storage.HPET_COUNTER_HI.counter_hi.value : '0;
    for(genvar i0=0; i0<2; i0++) begin
        assign readback_array[i0 * 4 + 6][1:0] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? 2'h0 : '0;
        assign readback_array[i0 * 4 + 6][2:2] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value : '0;
        assign readback_array[i0 * 4 + 6][3:3] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_CONFIG.timer_int_enable.value : '0;
        assign readback_array[i0 * 4 + 6][4:4] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_CONFIG.timer_type.value : '0;
        assign readback_array[i0 * 4 + 6][5:5] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_CONFIG.timer_size.value : '0;
        assign readback_array[i0 * 4 + 6][6:6] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_CONFIG.timer_value_set.value : '0;
        assign readback_array[i0 * 4 + 6][31:7] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ? 25'h0 : '0;
        assign readback_array[i0 * 4 + 7][31:0] = (decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_LO && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_COMPARATOR_LO.timer_comp_lo.value : '0;
        assign readback_array[i0 * 4 + 8][31:0] = (decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_HI && !decoded_req_is_wr) ? field_storage.TIMER[i0].TIMER_COMPARATOR_HI.timer_comp_hi.value : '0;
        assign readback_array[i0 * 4 + 9][31:0] = (decoded_reg_strb.TIMER[i0].RESERVED && !decoded_req_is_wr) ? 32'h0 : '0;
    end

    // Reduce the array
    always_comb begin
        automatic logic [31:0] readback_data_var;
        readback_done = decoded_req & ~decoded_req_is_wr;
        readback_err = '0;
        readback_data_var = '0;
        for(int i=0; i<14; i++) readback_data_var |= readback_array[i];
        readback_data = readback_data_var;
    end

    assign cpuif_rd_ack = readback_done;
    assign cpuif_rd_data = readback_data;
    assign cpuif_rd_err = readback_err;
endmodule
