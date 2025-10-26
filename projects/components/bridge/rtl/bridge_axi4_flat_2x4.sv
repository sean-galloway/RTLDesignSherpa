`timescale 1ns / 1ps

module bridge_axi4_flat_2x4 #(parameter int  NUM_MASTERS = 2,
parameter int  NUM_SLAVES = 4,
parameter int  DATA_WIDTH = 32,
parameter int  ADDR_WIDTH = 32,
parameter int  ID_WIDTH = 4,
parameter int  STRB_WIDTH = 4 )(
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic [ADDR_WIDTH-1:0] s_axi_awaddr  [NUM_MASTERS],
    input  logic [ID_WIDTH-1:0]   s_axi_awid    [NUM_MASTERS],
    input  logic [7:0]            s_axi_awlen   [NUM_MASTERS],
    input  logic [2:0]            s_axi_awsize  [NUM_MASTERS],
    input  logic [1:0]            s_axi_awburst [NUM_MASTERS],
    input  logic                  s_axi_awlock  [NUM_MASTERS],
    input  logic [3:0]            s_axi_awcache [NUM_MASTERS],
    input  logic [2:0]            s_axi_awprot  [NUM_MASTERS],
    input  logic                  s_axi_awvalid [NUM_MASTERS],
    output logic                  s_axi_awready [NUM_MASTERS],
    input  logic [DATA_WIDTH-1:0] s_axi_wdata   [NUM_MASTERS],
    input  logic [STRB_WIDTH-1:0] s_axi_wstrb   [NUM_MASTERS],
    input  logic                  s_axi_wlast   [NUM_MASTERS],
    input  logic                  s_axi_wvalid  [NUM_MASTERS],
    output logic                  s_axi_wready  [NUM_MASTERS],
    output logic [ID_WIDTH-1:0]   s_axi_bid     [NUM_MASTERS],
    output logic [1:0]            s_axi_bresp   [NUM_MASTERS],
    output logic                  s_axi_bvalid  [NUM_MASTERS],
    input  logic                  s_axi_bready  [NUM_MASTERS],
    input  logic [ADDR_WIDTH-1:0] s_axi_araddr  [NUM_MASTERS],
    input  logic [ID_WIDTH-1:0]   s_axi_arid    [NUM_MASTERS],
    input  logic [7:0]            s_axi_arlen   [NUM_MASTERS],
    input  logic [2:0]            s_axi_arsize  [NUM_MASTERS],
    input  logic [1:0]            s_axi_arburst [NUM_MASTERS],
    input  logic                  s_axi_arlock  [NUM_MASTERS],
    input  logic [3:0]            s_axi_arcache [NUM_MASTERS],
    input  logic [2:0]            s_axi_arprot  [NUM_MASTERS],
    input  logic                  s_axi_arvalid [NUM_MASTERS],
    output logic                  s_axi_arready [NUM_MASTERS],
    output logic [DATA_WIDTH-1:0] s_axi_rdata   [NUM_MASTERS],
    output logic [ID_WIDTH-1:0]   s_axi_rid     [NUM_MASTERS],
    output logic [1:0]            s_axi_rresp   [NUM_MASTERS],
    output logic                  s_axi_rlast   [NUM_MASTERS],
    output logic                  s_axi_rvalid  [NUM_MASTERS],
    input  logic                  s_axi_rready  [NUM_MASTERS],
    output logic [ADDR_WIDTH-1:0] m_axi_awaddr  [NUM_SLAVES],
    output logic [ID_WIDTH-1:0]   m_axi_awid    [NUM_SLAVES],
    output logic [7:0]            m_axi_awlen   [NUM_SLAVES],
    output logic [2:0]            m_axi_awsize  [NUM_SLAVES],
    output logic [1:0]            m_axi_awburst [NUM_SLAVES],
    output logic                  m_axi_awlock  [NUM_SLAVES],
    output logic [3:0]            m_axi_awcache [NUM_SLAVES],
    output logic [2:0]            m_axi_awprot  [NUM_SLAVES],
    output logic                  m_axi_awvalid [NUM_SLAVES],
    input  logic                  m_axi_awready [NUM_SLAVES],
    output logic [DATA_WIDTH-1:0] m_axi_wdata   [NUM_SLAVES],
    output logic [STRB_WIDTH-1:0] m_axi_wstrb   [NUM_SLAVES],
    output logic                  m_axi_wlast   [NUM_SLAVES],
    output logic                  m_axi_wvalid  [NUM_SLAVES],
    input  logic                  m_axi_wready  [NUM_SLAVES],
    input  logic [ID_WIDTH-1:0]   m_axi_bid     [NUM_SLAVES],
    input  logic [1:0]            m_axi_bresp   [NUM_SLAVES],
    input  logic                  m_axi_bvalid  [NUM_SLAVES],
    output logic                  m_axi_bready  [NUM_SLAVES],
    output logic [ADDR_WIDTH-1:0] m_axi_araddr  [NUM_SLAVES],
    output logic [ID_WIDTH-1:0]   m_axi_arid    [NUM_SLAVES],
    output logic [7:0]            m_axi_arlen   [NUM_SLAVES],
    output logic [2:0]            m_axi_arsize  [NUM_SLAVES],
    output logic [1:0]            m_axi_arburst [NUM_SLAVES],
    output logic                  m_axi_arlock  [NUM_SLAVES],
    output logic [3:0]            m_axi_arcache [NUM_SLAVES],
    output logic [2:0]            m_axi_arprot  [NUM_SLAVES],
    output logic                  m_axi_arvalid [NUM_SLAVES],
    input  logic                  m_axi_arready [NUM_SLAVES],
    input  logic [DATA_WIDTH-1:0] m_axi_rdata   [NUM_SLAVES],
    input  logic [ID_WIDTH-1:0]   m_axi_rid     [NUM_SLAVES],
    input  logic [1:0]            m_axi_rresp   [NUM_SLAVES],
    input  logic                  m_axi_rlast   [NUM_SLAVES],
    input  logic                  m_axi_rvalid  [NUM_SLAVES],
    output logic                  m_axi_rready  [NUM_SLAVES]
);

// ==============================================================================
// Module: bridge_axi4_flat_2x4
// Project: Bridge - AXI4 Full Crossbar Generator
// ==============================================================================
// Description: AXI4 2×4 Full Crossbar
//
// Bridge: Connecting masters and slaves across the divide
//
// Generated by: bridge_generator.py (framework version)
// Configuration:
//   - Masters: 2
//   - Slaves: 4
//   - Data Width: 32 bits
//   - Address Width: 32 bits
//   - ID Width: 4 bits
//
// Features:
//   - Full 5-channel AXI4 protocol (AW, W, B, AR, R)
//   - Out-of-order transaction support (ID-based routing)
//   - Separate read/write arbitration (no head-of-line blocking)
//   - Burst transfer optimization (grant locking until xlast)
//
// ==============================================================================

// ==========================================================================
// Write Address Decode (AW channel)
// ==========================================================================
// Check each master's AWADDR against all slave address ranges
// Similar to APB crossbar but separate decode for write address channel
// ==========================================================================

logic [NUM_MASTERS-1:0] aw_request_matrix [NUM_SLAVES];

always_comb begin
    // Initialize all write address requests to zero
    for (int s = 0; s < NUM_SLAVES; s++) begin
        aw_request_matrix[s] = '0;
    end

    // Decode AWADDR to slave for each master
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (s_axi_awvalid[m]) begin
            // Slave 0: Slave0 (0x00000000 - 0x0FFFFFFF)
            if (s_axi_awaddr[m] < 32'h10000000)
                aw_request_matrix[0][m] = 1'b1;

            // Slave 1: Slave1 (0x10000000 - 0x1FFFFFFF)
            if (s_axi_awaddr[m] >= 32'h10000000 &&
                s_axi_awaddr[m] < 32'h20000000)
                aw_request_matrix[1][m] = 1'b1;

            // Slave 2: Slave2 (0x20000000 - 0x2FFFFFFF)
            if (s_axi_awaddr[m] >= 32'h20000000 &&
                s_axi_awaddr[m] < 32'h30000000)
                aw_request_matrix[2][m] = 1'b1;

            // Slave 3: Slave3 (0x30000000 - 0x3FFFFFFF)
            if (s_axi_awaddr[m] >= 32'h30000000 &&
                s_axi_awaddr[m] < 32'h40000000)
                aw_request_matrix[3][m] = 1'b1;

        end
    end
end

// ==========================================================================
// Read Address Decode (AR channel)
// ==========================================================================
// Separate decode for read address channel (independent from writes)
// ==========================================================================

logic [NUM_MASTERS-1:0] ar_request_matrix [NUM_SLAVES];

always_comb begin
    // Initialize all read address requests to zero
    for (int s = 0; s < NUM_SLAVES; s++) begin
        ar_request_matrix[s] = '0;
    end

    // Decode ARADDR to slave for each master
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (s_axi_arvalid[m]) begin
            // Slave 0: Slave0 (0x00000000 - 0x0FFFFFFF)
            if (s_axi_araddr[m] < 32'h10000000)
                ar_request_matrix[0][m] = 1'b1;

            // Slave 1: Slave1 (0x10000000 - 0x1FFFFFFF)
            if (s_axi_araddr[m] >= 32'h10000000 &&
                s_axi_araddr[m] < 32'h20000000)
                ar_request_matrix[1][m] = 1'b1;

            // Slave 2: Slave2 (0x20000000 - 0x2FFFFFFF)
            if (s_axi_araddr[m] >= 32'h20000000 &&
                s_axi_araddr[m] < 32'h30000000)
                ar_request_matrix[2][m] = 1'b1;

            // Slave 3: Slave3 (0x30000000 - 0x3FFFFFFF)
            if (s_axi_araddr[m] >= 32'h30000000 &&
                s_axi_araddr[m] < 32'h40000000)
                ar_request_matrix[3][m] = 1'b1;

        end
    end
end

// ==========================================================================
// AW Channel Arbitration (Write Address)
// ==========================================================================
// Round-robin arbiter per slave for write address channel
// Similar to Delta but for memory-mapped addresses (not streaming)
// Grant held until AWVALID && AWREADY handshake completes
// ==========================================================================

logic [NUM_MASTERS-1:0] aw_grant_matrix [NUM_SLAVES];
logic [$clog2(NUM_MASTERS)-1:0] aw_last_grant [NUM_SLAVES];
logic aw_grant_active [NUM_SLAVES];  // Grant in progress

// AW Arbitration logic for each slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_arbiter
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                aw_grant_matrix[s] <= '0;
                aw_last_grant[s] <= '0;
                aw_grant_active[s] <= 1'b0;
            end else begin
                if (aw_grant_active[s]) begin
                    // Hold grant until AW handshake completes
                    if (m_axi_awvalid[s] && m_axi_awready[s]) begin
                        aw_grant_active[s] <= 1'b0;
                        aw_grant_matrix[s] <= '0;
                        // TODO Phase 2: Store master ID in transaction table
                    end
                end else if (|aw_request_matrix[s]) begin
                    // Round-robin arbitration (same algorithm as Delta)
                    aw_grant_matrix[s] = '0;
                    for (int i = 0; i < NUM_MASTERS; i++) begin
                        int m;
                        m = (int'(aw_last_grant[s]) + 1 + i) % NUM_MASTERS;
                        if (aw_request_matrix[s][m] && aw_grant_matrix[s] == '0) begin
                            aw_grant_matrix[s][m] = 1'b1;
                            aw_last_grant[s] = m[$clog2(NUM_MASTERS)-1:0];
                            aw_grant_active[s] = 1'b1;
                        end
                    end
                end else begin
                    aw_grant_matrix[s] <= '0;
                end
            end
        end
    end
endgenerate

// ==========================================================================
// AW Channel Multiplexing
// ==========================================================================
// Mux granted master's write address signals to slave
// Similar to Delta data mux but for AW channel signals
// ==========================================================================

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_mux
        always_comb begin
            // Default: all zeros
            m_axi_awaddr[s]  = '0;
            m_axi_awid[s]    = '0;
            m_axi_awlen[s]   = '0;
            m_axi_awsize[s]  = '0;
            m_axi_awburst[s] = '0;
            m_axi_awlock[s]  = '0;
            m_axi_awcache[s] = '0;
            m_axi_awprot[s]  = '0;
            m_axi_awvalid[s] = 1'b0;

            // Multiplex granted master to this slave
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (aw_grant_matrix[s][m]) begin
                    m_axi_awaddr[s]  = s_axi_awaddr[m];
                    m_axi_awid[s]    = s_axi_awid[m];
                    m_axi_awlen[s]   = s_axi_awlen[m];
                    m_axi_awsize[s]  = s_axi_awsize[m];
                    m_axi_awburst[s] = s_axi_awburst[m];
                    m_axi_awlock[s]  = s_axi_awlock[m];
                    m_axi_awcache[s] = s_axi_awcache[m];
                    m_axi_awprot[s]  = s_axi_awprot[m];
                    m_axi_awvalid[s] = s_axi_awvalid[m];
                end
            end
        end
    end
endgenerate

// AWREADY backpressure routing
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_awready
        always_comb begin
            s_axi_awready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (aw_grant_matrix[s][m]) begin
                    s_axi_awready[m] = m_axi_awready[s];
                end
            end
        end
    end
endgenerate

// ==========================================================================
// W Channel Multiplexing (Write Data)
// ==========================================================================
// W channel follows AW grant (no independent arbitration)
// Grant locked to master until WLAST completes
// Similar to Delta but with burst support via WLAST
// ==========================================================================

logic [NUM_MASTERS-1:0] w_grant_matrix [NUM_SLAVES];
logic w_burst_active [NUM_SLAVES];  // W burst in progress

// W grant tracking - lock to master that won AW arbitration
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_grant
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                w_grant_matrix[s] <= '0;
                w_burst_active[s] <= 1'b0;
            end else begin
                if (w_burst_active[s]) begin
                    // Hold W grant until WLAST completes
                    if (m_axi_wvalid[s] && m_axi_wready[s] && m_axi_wlast[s]) begin
                        w_burst_active[s] <= 1'b0;
                        w_grant_matrix[s] <= '0;
                    end
                end else if (aw_grant_active[s] && m_axi_awvalid[s] && m_axi_awready[s]) begin
                    // AW completed - lock W to the same master
                    w_grant_matrix[s] <= aw_grant_matrix[s];
                    w_burst_active[s] <= 1'b1;
                end
            end
        end
    end
endgenerate

// W data multiplexing
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_mux
        always_comb begin
            // Default: all zeros
            m_axi_wdata[s]  = '0;
            m_axi_wstrb[s]  = '0;
            m_axi_wlast[s]  = 1'b0;
            m_axi_wvalid[s] = 1'b0;

            // Multiplex W signals from locked master
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (w_grant_matrix[s][m]) begin
                    m_axi_wdata[s]  = s_axi_wdata[m];
                    m_axi_wstrb[s]  = s_axi_wstrb[m];
                    m_axi_wlast[s]  = s_axi_wlast[m];
                    m_axi_wvalid[s] = s_axi_wvalid[m];
                end
            end
        end
    end
endgenerate

// WREADY backpressure routing
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_wready
        always_comb begin
            s_axi_wready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (w_grant_matrix[s][m]) begin
                    s_axi_wready[m] = m_axi_wready[s];
                end
            end
        end
    end
endgenerate

// ==========================================================================
// AR Channel Arbitration (Read Address)
// ==========================================================================
// Independent from write path - no head-of-line blocking
// Round-robin arbiter per slave for read address channel
// Grant held until ARVALID && ARREADY handshake completes
// ==========================================================================

logic [NUM_MASTERS-1:0] ar_grant_matrix [NUM_SLAVES];
logic [$clog2(NUM_MASTERS)-1:0] ar_last_grant [NUM_SLAVES];
logic ar_grant_active [NUM_SLAVES];  // Grant in progress

// AR Arbitration logic for each slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_arbiter
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                ar_grant_matrix[s] <= '0;
                ar_last_grant[s] <= '0;
                ar_grant_active[s] <= 1'b0;
            end else begin
                if (ar_grant_active[s]) begin
                    // Hold grant until AR handshake completes
                    if (m_axi_arvalid[s] && m_axi_arready[s]) begin
                        ar_grant_active[s] <= 1'b0;
                        ar_grant_matrix[s] <= '0;
                        // TODO Phase 2: Store master ID in transaction table
                    end
                end else if (|ar_request_matrix[s]) begin
                    // Round-robin arbitration
                    ar_grant_matrix[s] = '0;
                    for (int i = 0; i < NUM_MASTERS; i++) begin
                        int m;
                        m = (int'(ar_last_grant[s]) + 1 + i) % NUM_MASTERS;
                        if (ar_request_matrix[s][m] && ar_grant_matrix[s] == '0) begin
                            ar_grant_matrix[s][m] = 1'b1;
                            ar_last_grant[s] = m[$clog2(NUM_MASTERS)-1:0];
                            ar_grant_active[s] = 1'b1;
                        end
                    end
                end else begin
                    ar_grant_matrix[s] <= '0;
                end
            end
        end
    end
endgenerate

// ==========================================================================
// AR Channel Multiplexing
// ==========================================================================
// Mux granted master's read address signals to slave
// Independent from AW channel (separate read/write paths)
// ==========================================================================

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_mux
        always_comb begin
            // Default: all zeros
            m_axi_araddr[s]  = '0;
            m_axi_arid[s]    = '0;
            m_axi_arlen[s]   = '0;
            m_axi_arsize[s]  = '0;
            m_axi_arburst[s] = '0;
            m_axi_arlock[s]  = '0;
            m_axi_arcache[s] = '0;
            m_axi_arprot[s]  = '0;
            m_axi_arvalid[s] = 1'b0;

            // Multiplex granted master to this slave
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (ar_grant_matrix[s][m]) begin
                    m_axi_araddr[s]  = s_axi_araddr[m];
                    m_axi_arid[s]    = s_axi_arid[m];
                    m_axi_arlen[s]   = s_axi_arlen[m];
                    m_axi_arsize[s]  = s_axi_arsize[m];
                    m_axi_arburst[s] = s_axi_arburst[m];
                    m_axi_arlock[s]  = s_axi_arlock[m];
                    m_axi_arcache[s] = s_axi_arcache[m];
                    m_axi_arprot[s]  = s_axi_arprot[m];
                    m_axi_arvalid[s] = s_axi_arvalid[m];
                end
            end
        end
    end
endgenerate

// ARREADY backpressure routing
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_arready
        always_comb begin
            s_axi_arready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (ar_grant_matrix[s][m]) begin
                    s_axi_arready[m] = m_axi_arready[s];
                end
            end
        end
    end
endgenerate

// ==========================================================================
// Transaction ID Tracking Tables (Phase 2)
// ==========================================================================
// Purpose: Enable ID-based response routing (out-of-order support)
//
// Structure: Distributed RAM
//   - 4 slaves × 2 tables (write, read)
//   - 2^4 = 16 entries per table
//   - Each entry: $clog2(2) = 1 bits (master index)
//
// Write ID Table: Stores master index for AW transactions → B routing
// Read ID Table:  Stores master index for AR transactions → R routing
// ==========================================================================

// Transaction ID tables: [slave][transaction_id] → master_index
logic [$clog2(NUM_MASTERS):0] write_id_table [NUM_SLAVES][2**ID_WIDTH];
logic [$clog2(NUM_MASTERS):0] read_id_table [NUM_SLAVES][2**ID_WIDTH];

// ID Table Write Logic
// Store master index when AW/AR handshakes complete
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_id_table_write
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                // Tables don't need explicit reset (overwritten on use)
            end else begin
                // Write ID table: Record master for completed AW transactions
                if (m_axi_awvalid[s] && m_axi_awready[s]) begin
                    for (int m = 0; m < NUM_MASTERS; m++) begin
                        if (aw_grant_matrix[s][m]) begin
                            write_id_table[s][m_axi_awid[s]] <= m[$clog2(NUM_MASTERS):0];
                        end
                    end
                end

                // Read ID table: Record master for completed AR transactions
                if (m_axi_arvalid[s] && m_axi_arready[s]) begin
                    for (int m = 0; m < NUM_MASTERS; m++) begin
                        if (ar_grant_matrix[s][m]) begin
                            read_id_table[s][m_axi_arid[s]] <= m[$clog2(NUM_MASTERS):0];
                        end
                    end
                end
            end
        end
    end
endgenerate

// ==========================================================================
// B Channel Demux (Write Response) - Phase 3
// ==========================================================================
// ID-based routing: Lookup master from write_id_table[slave][bid]
// KEY DIFFERENCE from grant-based: Responses can be out-of-order
// Multiple slaves can respond simultaneously to different masters
// ==========================================================================

// B channel response routing to masters
logic [ID_WIDTH-1:0]     b_routed_id    [NUM_MASTERS];
logic [1:0]              b_routed_resp  [NUM_MASTERS];
logic                    b_routed_valid [NUM_MASTERS];

always_comb begin
    // Initialize all master B channels to idle
    for (int m = 0; m < NUM_MASTERS; m++) begin
        b_routed_id[m]    = '0;
        b_routed_resp[m]  = 2'b00;
        b_routed_valid[m] = 1'b0;
    end

    // Route B responses from each slave to target master
    for (int s = 0; s < NUM_SLAVES; s++) begin
        int target_master;  // Master index for this B response
        if (m_axi_bvalid[s]) begin
            // Lookup which master this transaction belongs to
            target_master = int'(write_id_table[s][m_axi_bid[s]]);

            // Route to target master (ID-based, not grant-based)
            b_routed_id[target_master]    = m_axi_bid[s];
            b_routed_resp[target_master]  = m_axi_bresp[s];
            b_routed_valid[target_master] = 1'b1;
        end else begin
            target_master = 0;  // Default when no valid
        end
    end
end

// Assign routed B signals to master output ports
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_b_output
        assign s_axi_bid[m]    = b_routed_id[m];
        assign s_axi_bresp[m]  = b_routed_resp[m];
        assign s_axi_bvalid[m] = b_routed_valid[m];
    end
endgenerate

// B channel backpressure: Route master's BREADY to slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_b_ready
        always_comb begin
            int target_master;
            m_axi_bready[s] = 1'b0;
            if (m_axi_bvalid[s]) begin
                // Find which master this B response goes to
                target_master = int'(write_id_table[s][m_axi_bid[s]]);
                m_axi_bready[s] = s_axi_bready[target_master];
            end else begin
                target_master = 0;  // Default when no valid
            end
        end
    end
endgenerate

// ==========================================================================
// R Channel Demux (Read Data/Response) - Phase 3
// ==========================================================================
// ID-based routing: Lookup master from read_id_table[slave][rid]
// Burst support: Multiple R beats (RLAST indicates last beat)
// Similar to B channel but with DATA_WIDTH data payload
// ==========================================================================

// R channel response routing to masters
logic [DATA_WIDTH-1:0]   r_routed_data  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     r_routed_id    [NUM_MASTERS];
logic [1:0]              r_routed_resp  [NUM_MASTERS];
logic                    r_routed_last  [NUM_MASTERS];
logic                    r_routed_valid [NUM_MASTERS];

always_comb begin
    // Initialize all master R channels to idle
    for (int m = 0; m < NUM_MASTERS; m++) begin
        r_routed_data[m]  = '0;
        r_routed_id[m]    = '0;
        r_routed_resp[m]  = 2'b00;
        r_routed_last[m]  = 1'b0;
        r_routed_valid[m] = 1'b0;
    end

    // Route R responses from each slave to target master
    for (int s = 0; s < NUM_SLAVES; s++) begin
        int target_master;  // Master index for this R response
        if (m_axi_rvalid[s]) begin
            // Lookup which master this transaction belongs to
            target_master = int'(read_id_table[s][m_axi_rid[s]]);

            // Route to target master (ID-based, burst-aware)
            r_routed_data[target_master]  = m_axi_rdata[s];
            r_routed_id[target_master]    = m_axi_rid[s];
            r_routed_resp[target_master]  = m_axi_rresp[s];
            r_routed_last[target_master]  = m_axi_rlast[s];
            r_routed_valid[target_master] = 1'b1;
        end else begin
            target_master = 0;  // Default when no valid
        end
    end
end

// Assign routed R signals to master output ports
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_r_output
        assign s_axi_rdata[m]  = r_routed_data[m];
        assign s_axi_rid[m]    = r_routed_id[m];
        assign s_axi_rresp[m]  = r_routed_resp[m];
        assign s_axi_rlast[m]  = r_routed_last[m];
        assign s_axi_rvalid[m] = r_routed_valid[m];
    end
endgenerate

// R channel backpressure: Route master's RREADY to slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_r_ready
        always_comb begin
            int target_master;
            m_axi_rready[s] = 1'b0;
            if (m_axi_rvalid[s]) begin
                // Find which master this R response goes to
                target_master = int'(read_id_table[s][m_axi_rid[s]]);
                m_axi_rready[s] = s_axi_rready[target_master];
            end else begin
                target_master = 0;  // Default when no valid
            end
        end
    end
endgenerate

endmodule
