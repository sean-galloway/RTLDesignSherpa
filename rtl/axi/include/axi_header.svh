// Basic AXI4 interface parameters
parameter int AXI_ID_WIDTH      = 4;    // ID width is used for identifying transactions.
parameter int AXI_ADDR_WIDTH    = 32;   // Address width determines the maximum addressable memory space.
parameter int AXI_DATA_WIDTH    = 32;   // Data width is the width of the data bus.
parameter int AXI_USER_WIDTH    = 1;    // User-defined signal width, typically for additional sideband information.

// Derived parameters for specific AXI signals
parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8;  // Write strobe width, derived from the data width.

// AXI4-Lite specific parameters (simpler, usually does not include burst transactions)
// No additional parameters are typically defined for AXI4-Lite beyond the basics, as it is a subset of AXI4.

// AXI4-Stream specific parameters
parameter int AXI_TDEST_WIDTH   = 4;    // Destination ID width, used for routing data in interconnects.
parameter int AXI_TUSER_WIDTH   = 1;    // User-defined signal width in AXI4-Stream for sideband information.

// Burst related parameters
parameter int AXI_MAX_BURST_LENGTH = 16;                // Maximum burst length for AXI transactions.
parameter int AXI_BURST_SIZE_WIDTH = 3;                 // Burst size width determines the number of bytes transferred in a burst.

// Optional features parameters
// These are not necessarily 'widths' but are useful for parameterizing certain AXI properties.
parameter int AXI_SUPPORTS_READ  = 1;  // Parameter to enable or disable read channels.
parameter int AXI_SUPPORTS_WRITE = 1;  // Parameter to enable or disable write channels.

// AXI4 protocol supports different types of protection, as defined below:
parameter int AXI_PROT_WIDTH     = 3;   // Protection width, defining the protection type (data, privilege, secure).

// Quality of Service (QoS) - applicable if QoS signals are used
parameter int AXI_QOS_WIDTH      = 4;   // QoS width, providing QoS signaling capabilities.

// Region signaling (optional in AXI4, more common in system interconnects)
parameter int AXI_REGION_WIDTH   = 4;   // Region width, used to identify different regions in the address space.

// Cache type signaling (optional)
parameter int AXI_CACHE_WIDTH    = 4;   // Cache width, providing cache control signaling capabilities.

// Lock signaling (optional in AXI4 for supporting exclusive accesses)
parameter int AXI_LOCK_WIDTH     = 1;   // Lock width, typically a single bit for lock signaling.

// Response signaling
parameter int AXI_RESP_WIDTH     = 2;   // Response width, used for signaling transaction status.

////////////////////////////////////////////////////////////////////////////////////////////////////
// AW Interfaces
// Define a struct for the AW channel signals from master to slave
typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]    awid;    // Write transaction ID
    logic [AXI_ADDR_WIDTH-1:0]  awaddr;  // Write address
    logic [7:0]                 awlen;   // Burst length, 8 bits as per AXI4 specification
    logic [2:0]                 awsize;  // Burst size, encoding the number of bytes per transfer
    logic [1:0]                 awburst; // Burst type (fixed, increment, or wrap)
    logic                       awlock;  // Lock signal for atomic operations
    logic [3:0]                 awcache; // Memory type, caching attributes
    logic [2:0]                 awprot;  // Protection type, defining the data and privilege type of the transaction
    logic [3:0]                 awqos;   // Quality of Service, providing QoS signaling capabilities
    logic [3:0]                 awregion;// Region identifier for address region
    logic [AXI_USER_WIDTH-1:0]  awuser;  // User-defined signal
    logic                       awvalid; // Valid signal for address and control information
} axi4_aw_m2s_t; // Master to Slave transaction type for AW channel

// Define a struct for the AW channel handshake signals from slave to master
typedef struct packed {
    logic                       awready; // Ready signal indicating slave is ready to accept address and control info
} axi4_aw_s2m_t; // Slave to Master handshake type for AW channel

// Define a struct for the W channel signals from master to slave
typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]    wid;     // Write transaction ID, should match AWID
    logic [AXI_DATA_WIDTH-1:0]  wdata;   // Write data
    logic [AXI_WSTRB_WIDTH-1:0] wstrb;   // Write strobe, indicating valid byte lanes in wdata
    logic                       wlast;   // Last transfer indicator for the current write burst
    logic [AXI_USER_WIDTH-1:0]  wuser;   // User-defined signal
    logic                       wvalid;  // Valid signal for write data and control information
} axi4_w_m2s_t; // Master to Slave transaction type for W channel

// Define a struct for the W channel handshake signals from slave to master
typedef struct packed {
    logic                       wready;  // Ready signal indicating slave can accept the write data
} axi4_w_s2m_t; // Slave to Master handshake type for W channel

// Define a struct for the B channel signals from slave to master
typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]    bid;     // Response transaction ID, matching the AWID of the write
    logic [1:0]                 bresp;   // Write response status
    logic [AXI_USER_WIDTH-1:0]  buser;   // User-defined signal
    logic                       bvalid;  // Valid signal for response information
} axi4_b_s2m_t; // Slave to Master response type for B channel

// Define a struct for the B channel handshake signals from master to slave
typedef struct packed {
    logic                       bready;  // Ready signal indicating master can accept the write response
} axi4_b_m2s_t; // Master to Slave handshake type for B channel

////////////////////////////////////////////////////////////////////////////////////////////////////
// AR Interfaces
// Define a struct for the AR channel signals from master to slave
typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]    arid;    // Read transaction ID
    logic [AXI_ADDR_WIDTH-1:0]  araddr;  // Read address
    logic [7:0]                 arlen;   // Burst length for the read transaction
    logic [2:0]                 arsize;  // Burst size, indicating the number of bytes for each transfer
    logic [1:0]                 arburst; // Burst type (fixed, increment, or wrap)
    logic                       arlock;  // Lock signal for atomic operations
    logic [3:0]                 arcache; // Memory type, caching attributes
    logic [2:0]                 arprot;  // Protection type, defining the data and privilege type of the transaction
    logic [3:0]                 arqos;   // Quality of Service, for signaling QoS capabilities
    logic [3:0]                 arregion;// Region identifier for address region
    logic [AXI_USER_WIDTH-1:0]  aruser;  // User-defined signal
    logic                       arvalid; // Valid signal for address and control information
} axi4_ar_m2s_t; // Master to Slave transaction type for AR channel

// Define a struct for the AR channel handshake signals from slave to master
typedef struct packed {
    logic                       arready; // Ready signal indicating slave is ready to accept the address and control info
} axi4_ar_s2m_t; // Slave to Master handshake type for AR channel

// Define a struct for the R channel signals from slave to master
typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]    rid;     // Read transaction ID, echoing back the ARID
    logic [AXI_DATA_WIDTH-1:0]  rdata;   // Read data
    logic [1:0]                 rresp;   // Read response status
    logic                       rlast;   // Last transfer indicator for the current read burst
    logic [AXI_USER_WIDTH-1:0]  ruser;   // User-defined signal
    logic                       rvalid;  // Valid signal indicating data is available
} axi4_r_s2m_t; // Slave to Master data transfer type for R channel

// Define a struct for the R channel handshake signals from master to slave
typedef struct packed {
    logic                       rready;  // Ready signal indicating master can accept the read data
} axi4_r_m2s_t; // Master to Slave handshake type for R channel
