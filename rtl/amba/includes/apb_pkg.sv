`ifndef APB_PKG_SV
`define APB_PKG_SV

package apb_pkg;
    // Basic APB interface parameters
    parameter int APB_ADDR_WIDTH = 32;
    parameter int APB_DATA_WIDTH = 32;
    parameter int APB_USER_WIDTH = 1;
    parameter int APB_STRB_WIDTH = APB_DATA_WIDTH / 8;
    parameter int APB_PROT_WIDTH = 3;

    // Master to Slave Interface (without handshaking)
    typedef struct packed {
        logic                      pwrite;
        logic [APB_ADDR_WIDTH-1:0] paddr;
        logic [APB_DATA_WIDTH-1:0] pwdata;
        logic [APB_STRB_WIDTH-1:0] pstrb;
        logic [APB_PROT_WIDTH-1:0] pprot;
    } apb_m2s_t;

    // Slave to Master Interface (without pready)
    typedef struct packed {
        logic [APB_DATA_WIDTH-1:0] prdata;
        logic                      pslverr;
    } apb_s2m_t;

    // Command Packet Structure (without handshaking)
    typedef struct packed {
        logic                      last;
        logic                      first;
        logic                      write;
        logic [APB_PROT_WIDTH-1:0] prot;
        logic [APB_STRB_WIDTH-1:0] strb;
        logic [APB_ADDR_WIDTH-1:0] addr;
        logic [APB_DATA_WIDTH-1:0] data;
    } apb_cmd_packet_t;

    // Response Packet Structure (without handshaking)
    typedef struct packed {
        logic                      last;
        logic                      first;
        logic                      error;
        logic [APB_DATA_WIDTH-1:0] data;
    } apb_rsp_packet_t;

endpackage : apb_pkg

`endif
