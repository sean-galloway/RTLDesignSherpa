`ifndef AMBA_ERROR_PKG_SV
`define AMBA_ERROR_PKG_SV

package amba_error_pkg;
    // Error types
    typedef enum logic [3:0] {
        ERR_NONE          = 4'h0,
        ERR_PARAM         = 4'h1,  // Parameter error
        ERR_PROT_AXI     = 4'h2,  // AXI protocol violation
        ERR_PROT_APB     = 4'h3,  // APB protocol violation
        ERR_BOUNDARY     = 4'h4,  // Boundary crossing error
        ERR_TIMEOUT      = 4'h5,  // Transaction timeout
        ERR_ALIGNMENT    = 4'h6,  // Data alignment error
        ERR_BURST        = 4'h7,  // Burst type/size error
        ERR_WIDTH        = 4'h8   // Data width conversion error
    } error_type_t;

    // Error status structure
    typedef struct packed {
        error_type_t    error_type;     // Type of error
        logic [31:0]    error_count;    // Number of errors
        logic [31:0]    timestamp;      // When error occurred
        logic [31:0]    address;        // Address where error occurred
        logic [3:0]     channel;        // Which channel (AW,W,B,AR,R)
    } error_status_t;

    // Performance monitoring structure
    typedef struct packed {
        logic [31:0]    trans_count;    // Transaction count
        logic [31:0]    latency_max;    // Maximum latency
        logic [31:0]    latency_min;    // Minimum latency
        logic [31:0]    timeout_count;  // Number of timeouts
        logic [31:0]    retry_count;    // Number of retries
    } perf_status_t;

    // Channel identifiers
    typedef enum logic [2:0] {
        CHAN_AW = 3'b000,
        CHAN_W  = 3'b001,
        CHAN_B  = 3'b010,
        CHAN_AR = 3'b011,
        CHAN_R  = 3'b100
    } channel_t;

    // Debug trigger types
    typedef enum logic [1:0] {
        TRIG_NONE   = 2'b00,
        TRIG_ERROR  = 2'b01,
        TRIG_ADDR   = 2'b10,
        TRIG_USER   = 2'b11
    } trigger_type_t;

endpackage : amba_error_pkg

`endif
