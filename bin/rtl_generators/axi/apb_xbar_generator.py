#!/usr/bin/env python3
import json

def generate_wrapper(json_file):
    with open(json_file, 'r') as f:
        params = json.load(f)

    FILE = params["FILE"]
    S = params["S"]
    M = params["M"]
    ADDR_WIDTH = params["ADDR_WIDTH"]
    DATA_WIDTH = params["DATA_WIDTH"]
    STRB_WIDTH = DATA_WIDTH // 8
    SLAVE_ENABLE = params["SLAVE_ENABLE"]
    SLAVE_ADDR_BASE = params["SLAVE_ADDR_BASE"]
    SLAVE_ADDR_LIMIT = params["SLAVE_ADDR_LIMIT"]
    THRESHOLDS = params["THRESHOLDS"]

    # Generate SystemVerilog code
    sv_code = """
`timescale 1ns / 1ps

module apb_xbar_wrap #(
    parameter int M = 2,
    parameter int S = 4,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH/8
) (
    input  logic                 aclk,
    input  logic                 aresetn,
"""

    # Generate master interfaces
    for i in range(M):
        sv_code += f"""
    input  logic                 m{i}_apb_psel,
    input  logic                 m{i}_apb_penable,
    input  logic                 m{i}_apb_pwrite,
    input  logic [AW-1:0]        m{i}_apb_paddr,
    input  logic [DW:0]          m{i}_apb_pwdata,
    input  logic [SW:0]          m{i}_apb_pstrb,
    output logic                 m{i}_apb_pready,
    output logic [DW:0]          m{i}_apb_prdata,
    output logic                 m{i}_apb_pslverr,
"""

    # Generate slave interfaces
    for i in range(S):
        sv_code += f"""
    output logic                 s{i}_apb_psel,
    output logic                 s{i}_apb_penable,
    output logic                 s{i}_apb_pwrite,
    output logic [AW-1:0]        s{i}_apb_paddr,
    output logic [DW-1:0]        s{i}_apb_pwdata,
    output logic [SW-1:0]        s{i}_apb_pstrb,
    input  logic                 s{i}_apb_pready,
    input  logic [DW-1:0]        s{i}_apb_prdata,
    input  logic                 s{i}_apb_pslverr,
"""

    # Remove trailing comma and newline, and close the module port list
    sv_code = sv_code.rstrip(",\n") + "\n);\n\n"

    # Add in the abbreviations
    sv_code += """
    localparam int DW  = DATA_WIDTH;
    localparam int AW  = ADDR_WIDTH;
    localparam int SW  = STRB_WIDTH;

"""
    # Instantiate the apb_xbar module
    AW = ADDR_WIDTH
    slave_enable_str = f"""{{{', '.join(f"1'b{sen}" for sen in SLAVE_ENABLE)}}}"""
    slave_addr_base_str = f"""{{{', '.join(f"{AW}'h{addr:X}" for addr in SLAVE_ADDR_BASE)}}}"""
    slave_addr_limit_str = f"""{{{', '.join(f"{AW}'h{addr:X}" for addr in SLAVE_ADDR_LIMIT)}}}"""
    sv_code += f"""
    apb_xbar #(
        .M({M}),
        .S({S}),
        .ADDR_WIDTH({ADDR_WIDTH}),
        .DATA_WIDTH({DATA_WIDTH})
    ) apb_xbar_inst (
        .aclk                (aclk),
        .aresetn             (aresetn),
        .SLAVE_ENABLE        ({slave_enable_str}),
        .SLAVE_ADDR_BASE     ({slave_addr_base_str}),
        .SLAVE_ADDR_LIMIT    ({slave_addr_limit_str}),
        .THRESHOLDS          ({4*len(THRESHOLDS)}'h{''.join(f"{t:X}" for t in THRESHOLDS)}),
"""

    # Connect master interfaces
    sig_list = ['psel', 'penable', 'pwrite', 'paddr', 'pwdata', 'pstrb', 'pready', 'prdata', 'pslverr']
    m_apb_dict = {
        sig: '{'
        + ', '.join(f"m{i}_apb_{sig}" for i in range(M - 1, -1, -1))
        + '}'
        for sig in sig_list
    }
    sv_code += f"""
        .m_apb_psel     ({m_apb_dict['psel']}),
        .m_apb_penable  ({m_apb_dict['penable']}),
        .m_apb_pwrite   ({m_apb_dict['pwrite']}),
        .m_apb_paddr    ({m_apb_dict['paddr']}),
        .m_apb_pwdata   ({m_apb_dict['pwdata']}),
        .m_apb_pstrb    ({m_apb_dict['pstrb']}),
        .m_apb_pready   ({m_apb_dict['pready']}),
        .m_apb_prdata   ({m_apb_dict['prdata']}),
        .m_apb_pslverr  ({m_apb_dict['pslverr']}),
"""

    s_apb_dict = {
        sig: '{'
        + ', '.join(f"s{i}_apb_{sig}" for i in range(S - 1, -1, -1))
        + '}'
        for sig in sig_list
    }
    sv_code += f"""
        .s_apb_psel    ({s_apb_dict['psel']}),
        .s_apb_penable ({s_apb_dict['penable']}),
        .s_apb_pwrite  ({s_apb_dict['pwrite']}),
        .s_apb_paddr   ({s_apb_dict['paddr']}),
        .s_apb_pwdata  ({s_apb_dict['pwdata']}),
        .s_apb_pstrb   ({s_apb_dict['pstrb']}),
        .s_apb_pready  ({s_apb_dict['pready']}),
        .s_apb_prdata  ({s_apb_dict['prdata']}),
        .s_apb_pslverr ({s_apb_dict['pslverr']}),
"""

    # Remove trailing comma and newline, and close the module instantiation
    sv_code = sv_code.rstrip(",\n") + "\n    );\n\nendmodule : apb_xbar_wrap\n"

    return FILE, sv_code

# Example usage
json_file = 'apb_xbar_params.json'
FILE, sv_code = generate_wrapper(json_file)

# Optionally, write the generated SystemVerilog code to a file
with open(FILE, 'w') as f:
    f.write(sv_code)
