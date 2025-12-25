// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_pkg
// Purpose: APB5 Protocol Package with AMBA5 extensions
//
// APB5 adds the following signals over APB4:
// - PWAKEUP: Wake-up signal from slave to master
// - PAUSER: User-defined request attributes (master to slave)
// - PWUSER: User-defined write data attributes
// - PRUSER: User-defined read data attributes
// - PBUSER: User-defined response attributes (slave to master)
// - Parity signals for data integrity (optional)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`ifndef APB5_PKG_SV
`define APB5_PKG_SV

package apb5_pkg;
    // Import base APB package for shared constants
    import apb_pkg::*;

    // =============================================================================
    // APB5 PARAMETERS
    // =============================================================================

    // Basic APB5 interface parameters (inherit from APB4)
    parameter int APB5_ADDR_WIDTH   = 32;
    parameter int APB5_DATA_WIDTH   = 32;
    parameter int APB5_STRB_WIDTH   = APB5_DATA_WIDTH / 8;
    parameter int APB5_PROT_WIDTH   = 3;

    // APB5 Extended User Signal Widths
    parameter int APB5_AUSER_WIDTH  = 4;   // Request phase user signals
    parameter int APB5_WUSER_WIDTH  = 4;   // Write data user signals
    parameter int APB5_RUSER_WIDTH  = 4;   // Read data user signals
    parameter int APB5_BUSER_WIDTH  = 4;   // Response user signals

    // APB5 Parity Widths (optional feature)
    parameter int APB5_CTRL_PARITY_WIDTH  = 1;   // Control signal parity
    parameter int APB5_DATA_PARITY_WIDTH  = APB5_DATA_WIDTH / 8;  // Per-byte parity

    // =============================================================================
    // APB5 INTERFACE STRUCTURES
    // =============================================================================

    // APB5 Master to Slave Interface (extends APB4)
    typedef struct packed {
        // APB4 signals
        logic                         pwrite;
        logic [APB5_ADDR_WIDTH-1:0]   paddr;
        logic [APB5_DATA_WIDTH-1:0]   pwdata;
        logic [APB5_STRB_WIDTH-1:0]   pstrb;
        logic [APB5_PROT_WIDTH-1:0]   pprot;
        // APB5 user signals
        logic [APB5_AUSER_WIDTH-1:0]  pauser;    // Request attributes
        logic [APB5_WUSER_WIDTH-1:0]  pwuser;    // Write data attributes
    } apb5_m2s_t;

    // APB5 Slave to Master Interface (extends APB4)
    typedef struct packed {
        // APB4 signals
        logic [APB5_DATA_WIDTH-1:0]   prdata;
        logic                         pslverr;
        // APB5 signals
        logic                         pwakeup;    // Wake-up request
        logic [APB5_RUSER_WIDTH-1:0]  pruser;     // Read data attributes
        logic [APB5_BUSER_WIDTH-1:0]  pbuser;     // Response attributes
    } apb5_s2m_t;

    // APB5 Parity Signals (optional, master to slave)
    typedef struct packed {
        logic [APB5_DATA_PARITY_WIDTH-1:0] pwdataparity;  // Write data parity
        logic                              paddrparity;   // Address parity
        logic                              pctrlparity;   // Control signals parity
    } apb5_m2s_parity_t;

    // APB5 Parity Signals (optional, slave to master)
    typedef struct packed {
        logic [APB5_DATA_PARITY_WIDTH-1:0] prdataparity;  // Read data parity
        logic                              preadyparity;  // PREADY parity
        logic                              pslverrparity; // PSLVERR parity
    } apb5_s2m_parity_t;

    // =============================================================================
    // APB5 COMMAND AND RESPONSE PACKETS
    // =============================================================================

    // APB5 Command Packet (extended with user signals)
    typedef struct packed {
        logic                         last;
        logic                         first;
        logic                         write;
        logic [APB5_PROT_WIDTH-1:0]   prot;
        logic [APB5_STRB_WIDTH-1:0]   strb;
        logic [APB5_ADDR_WIDTH-1:0]   addr;
        logic [APB5_DATA_WIDTH-1:0]   data;
        // APB5 extensions
        logic [APB5_AUSER_WIDTH-1:0]  auser;
        logic [APB5_WUSER_WIDTH-1:0]  wuser;
    } apb5_cmd_packet_t;

    // APB5 Response Packet (extended with user signals and wakeup)
    typedef struct packed {
        logic                         last;
        logic                         first;
        logic                         error;
        logic [APB5_DATA_WIDTH-1:0]   data;
        // APB5 extensions
        logic                         wakeup;
        logic [APB5_RUSER_WIDTH-1:0]  ruser;
        logic [APB5_BUSER_WIDTH-1:0]  buser;
    } apb5_rsp_packet_t;

    // =============================================================================
    // APB5 WAKE-UP TYPES
    // =============================================================================

    // Wake-up state machine states
    typedef enum logic [2:0] {
        WAKEUP_IDLE       = 3'b000,  // No wake-up activity
        WAKEUP_REQUESTED  = 3'b001,  // Slave asserted PWAKEUP
        WAKEUP_PENDING    = 3'b010,  // Master received PWAKEUP, preparing
        WAKEUP_ACTIVE     = 3'b011,  // Master resumed operation
        WAKEUP_COMPLETE   = 3'b100,  // Wake-up sequence complete
        WAKEUP_TIMEOUT    = 3'b101,  // Wake-up timeout occurred
        WAKEUP_ERROR      = 3'b110   // Wake-up error
    } apb5_wakeup_state_t;

    // =============================================================================
    // APB5 HELPER FUNCTIONS
    // =============================================================================

    // Calculate odd parity for data
    function automatic logic calc_parity(logic [7:0] data);
        return ^data;
    endfunction

    // Calculate parity for multi-byte data
    function automatic logic [APB5_DATA_PARITY_WIDTH-1:0] calc_data_parity(
        logic [APB5_DATA_WIDTH-1:0] data
    );
        logic [APB5_DATA_PARITY_WIDTH-1:0] parity;
        for (int i = 0; i < APB5_DATA_PARITY_WIDTH; i++) begin
            parity[i] = calc_parity(data[i*8 +: 8]);
        end
        return parity;
    endfunction

    // Check parity for multi-byte data
    function automatic logic check_data_parity(
        logic [APB5_DATA_WIDTH-1:0]        data,
        logic [APB5_DATA_PARITY_WIDTH-1:0] parity
    );
        return (calc_data_parity(data) == parity);
    endfunction

    // Calculate address parity (odd parity over all address bits)
    function automatic logic calc_addr_parity(logic [APB5_ADDR_WIDTH-1:0] addr);
        return ^addr;
    endfunction

    // Calculate control parity (parity over PWRITE, PSTRB, PPROT)
    function automatic logic calc_ctrl_parity(
        logic                       pwrite,
        logic [APB5_STRB_WIDTH-1:0] pstrb,
        logic [APB5_PROT_WIDTH-1:0] pprot
    );
        return ^{pwrite, pstrb, pprot};
    endfunction

    // =============================================================================
    // APB5 CONVERSION FUNCTIONS
    // =============================================================================

    // Convert APB4 m2s to APB5 m2s (with default user signals)
    function automatic apb5_m2s_t apb4_to_apb5_m2s(apb_m2s_t apb4);
        apb5_m2s_t apb5;
        apb5.pwrite = apb4.pwrite;
        apb5.paddr  = apb4.paddr;
        apb5.pwdata = apb4.pwdata;
        apb5.pstrb  = apb4.pstrb;
        apb5.pprot  = apb4.pprot;
        apb5.pauser = '0;  // Default user signals
        apb5.pwuser = '0;
        return apb5;
    endfunction

    // Convert APB5 m2s to APB4 m2s (drop user signals)
    function automatic apb_m2s_t apb5_to_apb4_m2s(apb5_m2s_t apb5);
        apb_m2s_t apb4;
        apb4.pwrite = apb5.pwrite;
        apb4.paddr  = apb5.paddr;
        apb4.pwdata = apb5.pwdata;
        apb4.pstrb  = apb5.pstrb;
        apb4.pprot  = apb5.pprot;
        return apb4;
    endfunction

    // Convert APB4 s2m to APB5 s2m (with default extensions)
    function automatic apb5_s2m_t apb4_to_apb5_s2m(apb_s2m_t apb4);
        apb5_s2m_t apb5;
        apb5.prdata  = apb4.prdata;
        apb5.pslverr = apb4.pslverr;
        apb5.pwakeup = 1'b0;  // No wake-up by default
        apb5.pruser  = '0;
        apb5.pbuser  = '0;
        return apb5;
    endfunction

    // Convert APB5 s2m to APB4 s2m (drop extensions)
    function automatic apb_s2m_t apb5_to_apb4_s2m(apb5_s2m_t apb5);
        apb_s2m_t apb4;
        apb4.prdata  = apb5.prdata;
        apb4.pslverr = apb5.pslverr;
        return apb4;
    endfunction

endpackage : apb5_pkg

`endif
