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
    SLAVE_ENABLE = params["SLAVE_ENABLE"]
    SLAVE_ADDR_BASE  = [int(addr, 16) for addr in params["SLAVE_ADDR_BASE"]]
    SLAVE_ADDR_LIMIT = [int(addr, 16) for addr in params["SLAVE_ADDR_LIMIT"]]
    MST_THRESHOLDS = params["MST_THRESHOLDS"]
    SLV_THRESHOLDS = params["SLV_THRESHOLDS"]
    SLAVE_ENABLE.reverse()
    SLAVE_ADDR_BASE.reverse()
    SLAVE_ADDR_LIMIT.reverse()
    MST_THRESHOLDS.reverse()
    SLV_THRESHOLDS.reverse()

    # Generate SystemVerilog code
    sv_code = f"""
`timescale 1ns / 1ps

module apb_xbar_wrap_m{M}_s{S} #(
    parameter int M = {M},
    parameter int S = {S},
    parameter int ADDR_WIDTH = {ADDR_WIDTH},
    parameter int DATA_WIDTH = {DATA_WIDTH},
    parameter int STRB_WIDTH = {DATA_WIDTH}/8,
    // short params
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH
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
    input  logic [2:0]           m{i}_apb_pprot,
    input  logic [AW-1:0]        m{i}_apb_paddr,
    input  logic [DW-1:0]        m{i}_apb_pwdata,
    input  logic [SW-1:0]        m{i}_apb_pstrb,
    output logic                 m{i}_apb_pready,
    output logic [DW-1:0]        m{i}_apb_prdata,
    output logic                 m{i}_apb_pslverr,
"""

    # Generate slave interfaces
    for i in range(S):
        sv_code += f"""
    output logic                 s{i}_apb_psel,
    output logic                 s{i}_apb_penable,
    output logic                 s{i}_apb_pwrite,
    output logic [2:0]           s{i}_apb_pprot,
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
        .MST_THRESHOLDS      ({4*len(MST_THRESHOLDS)}'h{''.join(f"{t:X}" for t in MST_THRESHOLDS)}),
        .SLV_THRESHOLDS      ({4*len(SLV_THRESHOLDS)}'h{''.join(f"{t:X}" for t in SLV_THRESHOLDS)}),
"""

    # Connect master interfaces
    sig_list = ['psel', 'penable', 'pwrite', 'pprot', 'paddr', 'pwdata', 'pstrb', 'pready', 'prdata', 'pslverr']
    m_apb_dict = {
        sig: '{'
        + ', '.join(f"m{i}_apb_{sig}" for i in range(M - 1, -1, -1))
        + '}'
        for sig in sig_list
    }
    for sig in sig_list:
        pad = 9 - len(sig)
        sv_code += f"        .m_apb_{sig}" + " "*pad + f"({m_apb_dict[sig]}),\n"

    s_apb_dict = {
        sig: '{'
        + ', '.join(f"s{i}_apb_{sig}" for i in range(S - 1, -1, -1))
        + '}'
        for sig in sig_list
    }
    for sig in sig_list:
        pad = 9 - len(sig)
        sv_code += f"        .s_apb_{sig}" + " "*pad + f"({s_apb_dict[sig]}),\n"

    # Remove trailing comma and newline, and close the module instantiation
    sv_code = sv_code.rstrip(",\n") + f"\n    );\n\nendmodule : apb_xbar_wrap_m{M}_s{S}\n"

    return FILE, sv_code

# Example usage
json_file = 'apb_xbar_params.json'
FILE, sv_code = generate_wrapper(json_file)

# Optionally, write the generated SystemVerilog code to a file
with open(FILE, 'w') as f:
    f.write(sv_code)
