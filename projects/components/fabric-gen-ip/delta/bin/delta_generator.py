#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DeltaConfig
# Purpose: Delta: AXI-Stream Crossbar Generator (Framework Version)
#
# Documentation: projects/components/fabric-gen-ip/delta/PRD.md
# Subsystem: delta
#
# Author: sean galloway
# Created: 2025-10-18

"""
Delta: AXI-Stream Crossbar Generator (Framework Version)
Generates parameterized AXI-Stream switches using the unified verilog framework

This version uses the sophisticated framework from bin/rtl_generators/verilog/
for better structure, maintainability, and consistency with other generators.

Author: RTL Design Sherpa
Project: Delta (AXI-Stream Crossbar Generator)
Version: 2.0 (Framework-based)
"""

import argparse
import sys
import os
import math
from dataclasses import dataclass
from typing import Tuple
from pathlib import Path

# Import the framework
# parents[5] = repo root (bin/ -> delta/ -> fabric-gen-ip/ -> components/ -> projects/ -> root)
sys.path.insert(0, str(Path(__file__).resolve().parents[5] / 'bin'))
from rtl_generators.verilog.module import Module


@dataclass
class DeltaConfig:
    """Configuration for AXI-Stream crossbar generation"""
    topology: str           # "flat" or "tree"
    num_masters: int        # Number of master interfaces
    num_slaves: int         # Number of slave interfaces
    data_width: int         # TDATA width in bits
    dest_width: int         # TDEST width (calculated)
    id_width: int           # TID width (calculated)
    user_width: int = 1     # TUSER width
    strb_width: int = 0     # TSTRB width in bits; 0 = no TSTRB ports
    amba5: bool = False     # Emit AMBA 5 sidebands: TWAKEUP + IHI 0051B ch. 5 *CHK signals
    registered_outputs: bool = True  # Add output registers
    arbiter_type: str = "round_robin"  # "round_robin" or "fixed_priority"
    add_performance_counters: bool = True  # Add optional performance monitoring


class DeltaFlatCrossbar(Module):
    """
    AXI-Stream Flat Crossbar Generator using Module framework

    Inherits from Module to leverage structured RTL generation:
    - Automatic port/parameter formatting
    - Clean code organization
    - Validation and error checking
    """

    def __init__(self, config: DeltaConfig):
        self.cfg = config
        self.module_str = f'delta_axis_flat_{config.num_masters}x{config.num_slaves}'

        # Initialize Module base class
        Module.__init__(self, module_name=self.module_str)

        # Optional flavor columns (rtl/amba/axis4 + axis5 parity with these)
        self.strb_on = config.strb_width > 0
        self.amba5_on = config.amba5

        # Define parameters
        param_str = f'''
            parameter int DATA_WIDTH = {config.data_width},
            parameter int DEST_WIDTH = {config.dest_width},
            parameter int ID_WIDTH   = {config.id_width},
            parameter int USER_WIDTH = {config.user_width},
        '''
        if self.strb_on:
            param_str += f'parameter int STRB_WIDTH = {config.strb_width},\n'
        if self.amba5_on:
            # Check-signal widths, IHI 0051B Table 5-1 (one bit per byte,
            # top bit covers a short remainder). Derived, so overriding a
            # payload width at instantiation keeps the check ports in step.
            param_str += 'parameter int TDATACHK_W = DATA_WIDTH / 8,\n'
            if self.strb_on:
                param_str += 'parameter int TSTRBCHK_W = (STRB_WIDTH + 7) / 8,\n'
            param_str += 'parameter int TIDCHK_W = (ID_WIDTH + 7) / 8,\n'
            param_str += 'parameter int TDESTCHK_W = (DEST_WIDTH + 7) / 8,\n'
            param_str += 'parameter int TUSERCHK_W = (USER_WIDTH + 7) / 8,\n'
        param_str += f'''parameter int NUM_MASTERS = {config.num_masters},
            parameter int NUM_SLAVES  = {config.num_slaves}
        '''
        self.params.add_param_string(param_str)

        # Define ports
        port_str = '''
            input  logic aclk,
            input  logic aresetn,

            input  logic [DATA_WIDTH-1:0]  s_axis_tdata  [NUM_MASTERS],
        '''
        if self.strb_on:
            port_str += 'input  logic [STRB_WIDTH-1:0]  s_axis_tstrb  [NUM_MASTERS],\n'
        port_str += '''
            input  logic                   s_axis_tvalid [NUM_MASTERS],
            output logic                   s_axis_tready [NUM_MASTERS],
            input  logic                   s_axis_tlast  [NUM_MASTERS],
            input  logic [DEST_WIDTH-1:0]  s_axis_tdest  [NUM_MASTERS],
            input  logic [ID_WIDTH-1:0]    s_axis_tid    [NUM_MASTERS],
            input  logic [USER_WIDTH-1:0]  s_axis_tuser  [NUM_MASTERS],
        '''
        if self.amba5_on:
            port_str += self._chk_port_string('s', 'NUM_MASTERS') + ',\n'
        port_str += '''
            output logic [DATA_WIDTH-1:0]  m_axis_tdata  [NUM_SLAVES],
        '''
        if self.strb_on:
            port_str += 'output logic [STRB_WIDTH-1:0]  m_axis_tstrb  [NUM_SLAVES],\n'
        port_str += '''
            output logic                   m_axis_tvalid [NUM_SLAVES],
            input  logic                   m_axis_tready [NUM_SLAVES],
            output logic                   m_axis_tlast  [NUM_SLAVES],
            output logic [DEST_WIDTH-1:0]  m_axis_tdest  [NUM_SLAVES],
            output logic [ID_WIDTH-1:0]    m_axis_tid    [NUM_SLAVES],
            output logic [USER_WIDTH-1:0]  m_axis_tuser  [NUM_SLAVES]
        '''
        if self.amba5_on:
            port_str += ',\n' + self._chk_port_string('m', 'NUM_SLAVES')
        self.ports.add_port_string(port_str)

    def _payload_chk_fields(self):
        """Payload check fields as (signal, check-width param, payload width param).

        IHI 0051B Table 5-1. These are carried end to end with the beat.
        TSTRBCHK exists only when TSTRB does (section 5.3: an absent signal's
        check is omitted).
        """
        fields = [('tdata', 'TDATACHK_W', 'DATA_WIDTH')]
        if self.strb_on:
            fields.append(('tstrb', 'TSTRBCHK_W', 'STRB_WIDTH'))
        fields += [('tlast', None, None),
                   ('tid', 'TIDCHK_W', 'ID_WIDTH'),
                   ('tdest', 'TDESTCHK_W', 'DEST_WIDTH'),
                   ('tuser', 'TUSERCHK_W', 'USER_WIDTH')]
        return fields

    def _chk_port_string(self, side: str, count: str) -> str:
        """AMBA 5 ports for one side: TWAKEUP, the *CHK set, the sticky error.

        side 's' is the receiver side (masters drive into the crossbar), side
        'm' the transmitter side. Payload checks and TVALIDCHK/TWAKEUPCHK
        travel with the transmitter; TREADYCHK travels the other way.
        """
        rx = side == 's'
        fwd = 'input ' if rx else 'output'
        rev = 'output' if rx else 'input '
        lines = [f'{fwd} logic {side}_axis_twakeup [{count}]']
        for sig, chk_w, _ in self._payload_chk_fields():
            packed = f'[{chk_w}-1:0] ' if chk_w else ''
            lines.append(f'{fwd} logic {packed}{side}_axis_{sig}chk [{count}]')
        lines.append(f'{fwd} logic {side}_axis_tvalidchk [{count}]')
        lines.append(f'{rev} logic {side}_axis_treadychk [{count}]')
        lines.append(f'{fwd} logic {side}_axis_twakeupchk [{count}]')
        lines.append(f'output logic {side}_parity_error [{count}]')
        return ',\n'.join(lines)

    def generate_header_comment(self):
        """Generate Delta-specific header comment"""
        self.comment("==============================================================================")
        self.comment(f"Module: {self.module_str}")
        self.comment("Project: Delta - AXI-Stream Crossbar Generator")
        self.comment("==============================================================================")
        self.comment(f"Description: AXI-Stream {self.cfg.num_masters}×{self.cfg.num_slaves} Flat Crossbar Switch")
        self.comment("")
        self.comment("Delta: Where data flows split and merge like river deltas")
        self.comment("")
        self.comment("Generated by: delta_generator_v2.py (framework version)")
        self.comment("Configuration:")
        self.comment(f"  - Topology: {self.cfg.topology}")
        self.comment(f"  - Masters: {self.cfg.num_masters}")
        self.comment(f"  - Slaves: {self.cfg.num_slaves}")
        self.comment(f"  - Data Width: {self.cfg.data_width} bits")
        self.comment(f"  - TDEST Width: {self.cfg.dest_width} bits")
        self.comment(f"  - TID Width: {self.cfg.id_width} bits")
        self.comment(f"  - Arbiter: {self.cfg.arbiter_type}")
        self.comment("")
        self.comment("Features:")
        self.comment("  - Per-slave round-robin arbitration")
        self.comment("  - Packet atomicity (locked grant until TLAST)")
        if self.strb_on:
            self.comment(f"  - Optional TSTRB byte qualifiers (STRB_WIDTH={self.cfg.strb_width})")
        if self.amba5_on:
            self.comment("  - AMBA 5 TWAKEUP steering + interface check signals (IHI 0051B ch. 5,")
            self.comment("    Odd_Parity_Byte_All): payload *CHK carried with the beat, checked on")
            self.comment("    ingress; TVALIDCHK/TREADYCHK/TWAKEUPCHK generated or checked per port;")
            self.comment("    sticky s_parity_error/m_parity_error per port")
        self.comment("  - Registered outputs for timing closure")
        self.comment("  - Full AXI-Stream compliance")
        self.comment("")
        self.comment("==============================================================================")
        self.instruction("")

    def generate_request_decode(self):
        """Generate request decode logic (TDEST -> slave select)"""
        self.comment("==========================================================================")
        self.comment("Request Generation - Decode TDEST to slave select")
        self.comment("==========================================================================")
        self.comment("AXIS Advantage: Direct TDEST decode (simpler than APB address ranges)")
        self.comment("")
        self.comment("Each master's TDEST field directly identifies target slave")
        self.comment("No address range checking needed (unlike APB crossbar)")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] request_matrix [NUM_SLAVES];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all requests to zero")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("        request_matrix[s] = '0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Generate requests based on TDEST")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        if (s_axis_tvalid[m] && (s_axis_tdest[m] < NUM_SLAVES[$clog2(NUM_SLAVES+1)-1:0])) begin")
        self.instruction("            // Direct decode: TDEST is slave index")
        self.instruction("            request_matrix[s_axis_tdest[m]][m] = 1'b1;")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

    def generate_arbiter_logic(self):
        """Generate per-slave round-robin arbiter with packet atomicity"""
        self.comment("==========================================================================")
        self.comment("Per-Slave Round-Robin Arbiters with Packet Atomicity")
        self.comment("==========================================================================")
        self.comment("Similar to APB crossbar, but with PACKET ATOMICITY:")
        self.comment("- APB: Re-arbitrate every cycle")
        self.comment("- AXIS: Lock grant until TLAST (prevent packet interleaving)")
        self.comment("")
        self.comment("Round-robin ensures fair bandwidth allocation")
        self.comment("Packet atomicity ensures correct streaming behavior")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] grant_matrix [NUM_SLAVES];")
        self.instruction("logic [$clog2(NUM_MASTERS)-1:0] last_grant [NUM_SLAVES];")
        self.instruction("logic packet_active [NUM_SLAVES];  // NEW vs APB: Track packet in progress")
        self.instruction("")

        self.comment("Arbitration logic for each slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_arbiter")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn) begin")
        self.instruction("                grant_matrix[s] <= '0;")
        self.instruction("                last_grant[s] <= '0;")
        self.instruction("                packet_active[s] <= 1'b0;")
        self.instruction("            end else begin")
        self.instruction("                if (packet_active[s]) begin")
        self.instruction("                    // Hold grant until TLAST (packet atomicity)")
        self.instruction("                    if (m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s]) begin")
        self.instruction("                        packet_active[s] <= 1'b0;")
        self.instruction("                        grant_matrix[s] <= '0;")
        self.instruction("                    end")
        self.instruction("                end else if (|request_matrix[s]) begin")
        self.instruction("                    // Round-robin arbitration (same as APB)")
        self.instruction("                    grant_matrix[s] = '0;")
        self.instruction("                    for (int i = 0; i < NUM_MASTERS; i++) begin")
        self.instruction("                        int m;")
        self.instruction("                        m = (last_grant[s] + 1 + i) % NUM_MASTERS;")
        self.instruction("                        if (request_matrix[s][m] && grant_matrix[s] == '0) begin")
        self.instruction("                            grant_matrix[s][m] = 1'b1;")
        self.instruction("                            last_grant[s] = m[$clog2(NUM_MASTERS)-1:0];")
        self.instruction("                            packet_active[s] = 1'b1;")
        self.instruction("                        end")
        self.instruction("                    end")
        self.instruction("                end else begin")
        self.instruction("                    grant_matrix[s] <= '0;")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_crossbar_mux(self):
        """Generate crossbar data multiplexing"""
        self.comment("==========================================================================")
        self.comment("Crossbar Data Multiplexing")
        self.comment("==========================================================================")
        self.comment("Same pattern as APB crossbar, just more signals:")
        self.comment("- APB muxes: PRDATA, PSLVERR")
        self.comment("- AXIS muxes: TDATA, TVALID, TLAST, TDEST, TID, TUSER")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_mux")
        self.instruction("        always_comb begin")
        self.instruction("            // Default: all zeros")
        self.instruction("            m_axis_tdata[s]  = '0;")
        self.instruction("            m_axis_tvalid[s] = 1'b0;")
        self.instruction("            m_axis_tlast[s]  = 1'b0;")
        self.instruction("            m_axis_tdest[s]  = '0;")
        self.instruction("            m_axis_tid[s]    = '0;")
        self.instruction("            m_axis_tuser[s]  = '0;")
        if self.strb_on:
            self.instruction("            m_axis_tstrb[s]  = '0;")
        if self.amba5_on:
            # Idle check bits are all ones: the odd parity of the all-zero
            # payload defaults above (only meaningful while TVALID is high).
            for sig, chk_w, _ in self._payload_chk_fields():
                self.instruction(f"            m_axis_{sig}chk[s] = '1;" if chk_w else
                                 f"            m_axis_{sig}chk[s] = 1'b1;")
        self.instruction("")
        self.instruction("            // Multiplex granted master to this slave")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (grant_matrix[s][m]) begin")
        self.instruction("                    m_axis_tdata[s]  = s_axis_tdata[m];")
        self.instruction("                    m_axis_tvalid[s] = s_axis_tvalid[m];")
        self.instruction("                    m_axis_tlast[s]  = s_axis_tlast[m];")
        self.instruction("                    m_axis_tdest[s]  = s_axis_tdest[m];")
        self.instruction("                    m_axis_tid[s]    = s_axis_tid[m];")
        self.instruction("                    m_axis_tuser[s]  = s_axis_tuser[m];")
        if self.strb_on:
            self.instruction("                    m_axis_tstrb[s]  = s_axis_tstrb[m];")
        if self.amba5_on:
            for sig, _, _ in self._payload_chk_fields():
                self.instruction(f"                    m_axis_{sig}chk[s] = s_axis_{sig}chk[m];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_backpressure_logic(self):
        """Generate TREADY backpressure logic"""
        self.comment("==========================================================================")
        self.comment("Backpressure (TREADY) Logic")
        self.comment("==========================================================================")
        self.comment("Identical to APB PREADY logic, just renamed signal:")
        self.comment("- APB: pready[m] = pready_slave[granted_slave]")
        self.comment("- AXIS: s_axis_tready[m] = m_axis_tready[granted_slave]")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_tready")
        self.instruction("        always_comb begin")
        self.instruction("            s_axis_tready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (grant_matrix[s][m]) begin")
        self.instruction("                    s_axis_tready[m] = m_axis_tready[s];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_wakeup_logic(self):
        """Generate AMBA 5 TWAKEUP steering (only when amba5 enabled)"""
        if not self.amba5_on:
            return

        self.comment("==========================================================================")
        self.comment("AMBA 5 Wakeup (TWAKEUP) Steering")
        self.comment("==========================================================================")
        self.comment("TWAKEUP is a hint that may precede TVALID (a master wakes a slave before")
        self.comment("presenting data), so it is decoded from TDEST directly - no grant needed.")
        self.comment("Per slave: OR of twakeup from every master whose TDEST selects this slave.")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("        m_axis_twakeup[s] = 1'b0;")
        self.instruction("        for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("            if (s_axis_twakeup[m] && (s_axis_tdest[m] == s[$clog2(NUM_SLAVES)-1:0])) begin")
        self.instruction("                m_axis_twakeup[s] = 1'b1;")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

    def _emit_byte_checks(self, idx: str, sig: str, chk_w: str, pay_w: str):
        """One dataint_parity (odd, CHUNKS=1) per check bit of a payload field.

        Check bit [g] covers bits [8g+7:8g]; the top bit covers what is left
        when the field is not a whole number of bytes (IHI 0051B section 5.3).
        """
        side = 's_axis'
        if chk_w is None:
            self.instruction(f"        dataint_parity #(.CHUNKS(1), .WIDTH(1)) u_{sig}chk (")
            self.instruction(f"            .data_in     ({side}_{sig}[{idx}]),")
            self.instruction(f"            .parity_in   ({side}_{sig}chk[{idx}]),")
            self.instruction("            .parity_type (1'b0),")
            self.instruction(f"            .parity      (w_{sig}chk_exp),")
            self.instruction(f"            .parity_err  (w_{sig}chk_err)")
            self.instruction("        );")
            return
        self.instruction(f"        for (genvar g = 0; g < {chk_w}; g++) begin : g_{sig}chk")
        self.instruction("            localparam int LO = 8 * g;")
        self.instruction(f"            localparam int PIECE_W = ({pay_w} - LO < 8) ? ({pay_w} - LO) : 8;")
        self.instruction("            dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (")
        self.instruction(f"                .data_in     ({side}_{sig}[{idx}][LO +: PIECE_W]),")
        self.instruction(f"                .parity_in   ({side}_{sig}chk[{idx}][g]),")
        self.instruction("                .parity_type (1'b0),")
        self.instruction(f"                .parity      (w_{sig}chk_exp[g]),")
        self.instruction(f"                .parity_err  (w_{sig}chk_err[g])")
        self.instruction("            );")
        self.instruction("        end")

    def _emit_ctrl_chk(self, inst: str, data: str, chk_in: str, parity: str, err: str):
        """Single-bit critical control: the check bit is the inversion (5.3)."""
        self.instruction(f"        dataint_parity #(.CHUNKS(1), .WIDTH(1)) {inst} (")
        self.instruction(f"            .data_in     ({data}),")
        self.instruction(f"            .parity_in   ({chk_in}),")
        self.instruction("            .parity_type (1'b0),")
        self.instruction(f"            .parity      ({parity}),")
        self.instruction(f"            .parity_err  ({err})")
        self.instruction("        );")

    def _emit_sticky(self, flag: str, idx: str, cond: str):
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn)")
        self.instruction(f"                {flag}[{idx}] <= 1'b0;")
        self.instruction(f"            else if ({cond})")
        self.instruction(f"                {flag}[{idx}] <= 1'b1;")
        self.instruction("        end")

    def generate_check_logic(self):
        """AMBA 5 interface check signals (only when amba5 enabled).

        IHI 0051B ch. 5, Check_Type = Odd_Parity_Byte_All: a check bit plus
        the bits it covers always hold an odd number of ones. Every check
        bit is computed or checked by rtl/common dataint_parity.

        Master (s_*) ports, where the crossbar is the receiver:
          - payload *CHK checked against the payload while TVALID is high,
            then carried to the granted slave port unchanged;
          - TVALIDCHK / TWAKEUPCHK checked every cycle out of reset;
          - TREADYCHK generated from the TREADY the crossbar drives.
        Slave (m_*) ports, where the crossbar is the transmitter:
          - TVALIDCHK / TWAKEUPCHK generated from what the crossbar drives;
          - TREADYCHK checked every cycle out of reset.
        Any mismatch sets that port's sticky {s,m}_parity_error.
        """
        if not self.amba5_on:
            return

        fields = self._payload_chk_fields()
        self.comment("==========================================================================")
        self.comment("AMBA 5 Interface Check Signals (IHI 0051B ch. 5, Odd_Parity_Byte_All)")
        self.comment("==========================================================================")
        self.comment("ODD parity: a check bit plus the bits it covers hold an odd number of")
        self.comment("ones. Check bit [n] covers bits [8n+7:8n]; the top bit covers a short")
        self.comment("remainder. Payload *CHK is checked on ingress (enabled by TVALID) and")
        self.comment("carried through the mux; TVALIDCHK/TWAKEUPCHK/TREADYCHK are generated")
        self.comment("by whichever side drives the signal and checked by the other.")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_s_chk")
        for sig, chk_w, _ in fields:
            packed = f"[{chk_w}-1:0] " if chk_w else ""
            self.instruction(f"        logic {packed}w_{sig}chk_exp, w_{sig}chk_err;")
        self.instruction("        logic w_tvalidchk_err, w_twakeupchk_err;")
        self.instruction("        logic w_tvalidchk_exp, w_twakeupchk_exp, w_treadychk_err;")
        self.instruction("        logic w_payload_err;")
        self.instruction("")
        for sig, chk_w, pay_w in fields:
            self._emit_byte_checks('m', sig, chk_w, pay_w)
        self.instruction("")
        self._emit_ctrl_chk("u_tvalidchk", "s_axis_tvalid[m]", "s_axis_tvalidchk[m]",
                            "w_tvalidchk_exp", "w_tvalidchk_err")
        self._emit_ctrl_chk("u_twakeupchk", "s_axis_twakeup[m]", "s_axis_twakeupchk[m]",
                            "w_twakeupchk_exp", "w_twakeupchk_err")
        self._emit_ctrl_chk("u_treadychk", "s_axis_tready[m]", "1'b0",
                            "s_axis_treadychk[m]", "w_treadychk_err")
        self.instruction("")
        err_terms = " || ".join(
            f"(|w_{sig}chk_err)" if chk_w else f"w_{sig}chk_err" for sig, chk_w, _ in fields)
        self.instruction(f"        assign w_payload_err = s_axis_tvalid[m] && ({err_terms});")
        self.instruction("")
        self._emit_sticky("s_parity_error", "m",
                          "w_payload_err || w_tvalidchk_err || w_twakeupchk_err")
        self.instruction("")
        self.instruction("        /* verilator lint_off UNUSEDSIGNAL */")
        exp_terms = ", ".join(f"w_{sig}chk_exp" for sig, _, _ in fields)
        self.instruction("        logic unused_s_chk;")
        self.instruction(f"        assign unused_s_chk = ^{{{exp_terms}, w_tvalidchk_exp, w_twakeupchk_exp, w_treadychk_err}};")
        self.instruction("        /* verilator lint_on UNUSEDSIGNAL */")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_m_chk")
        self.instruction("        logic w_treadychk_exp, w_treadychk_err;")
        self.instruction("        logic w_tvalidchk_err, w_twakeupchk_err;")
        self.instruction("")
        self._emit_ctrl_chk("u_tvalidchk", "m_axis_tvalid[s]", "1'b0",
                            "m_axis_tvalidchk[s]", "w_tvalidchk_err")
        self._emit_ctrl_chk("u_twakeupchk", "m_axis_twakeup[s]", "1'b0",
                            "m_axis_twakeupchk[s]", "w_twakeupchk_err")
        self._emit_ctrl_chk("u_treadychk", "m_axis_tready[s]", "m_axis_treadychk[s]",
                            "w_treadychk_exp", "w_treadychk_err")
        self.instruction("")
        self._emit_sticky("m_parity_error", "s", "w_treadychk_err")
        self.instruction("")
        self.instruction("        /* verilator lint_off UNUSEDSIGNAL */")
        self.instruction("        logic unused_m_chk;")
        self.instruction("        assign unused_m_chk = ^{w_treadychk_exp, w_tvalidchk_err, w_twakeupchk_err};")
        self.instruction("        /* verilator lint_on UNUSEDSIGNAL */")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_performance_counters(self):
        """Generate optional performance counters"""
        if not self.cfg.add_performance_counters:
            return

        self.comment("==========================================================================")
        self.comment("Performance Counters (Optional)")
        self.comment("==========================================================================")
        self.comment("Track packets and transfers per master/slave for performance analysis")
        self.comment("==========================================================================")
        self.instruction("")

        self.comment("Packet counters per master")
        self.instruction("logic [31:0] pkt_count_master [NUM_MASTERS];")
        self.instruction("logic [31:0] pkt_count_slave [NUM_SLAVES];")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    // Master packet counters")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_counters")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn)")
        self.instruction("                pkt_count_master[m] <= '0;")
        self.instruction("            else if (s_axis_tvalid[m] && s_axis_tready[m] && s_axis_tlast[m])")
        self.instruction("                pkt_count_master[m] <= pkt_count_master[m] + 1;")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Slave packet counters")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_counters")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn)")
        self.instruction("                pkt_count_slave[s] <= '0;")
        self.instruction("            else if (m_axis_tvalid[s] && m_axis_tready[s] && m_axis_tlast[s])")
        self.instruction("                pkt_count_slave[s] <= pkt_count_slave[s] + 1;")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_assertions(self):
        """Generate SystemVerilog assertions"""
        self.comment("==========================================================================")
        self.comment("Assertions for Debug and Verification")
        self.comment("==========================================================================")
        self.instruction("`ifdef FORMAL")
        self.comment("One-hot grant check")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_onehot_assert")
        self.instruction("        assert property (@(posedge aclk) disable iff (!aresetn)")
        self.instruction("            $onehot0(grant_matrix[s])")
        self.instruction("        ) else $error(\"Grant matrix not one-hot for slave %0d\", s);")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")
        self.comment("TDEST in range check")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_tdest_assert")
        self.instruction("        assert property (@(posedge aclk) disable iff (!aresetn)")
        self.instruction("            s_axis_tvalid[m] |-> s_axis_tdest[m] < NUM_SLAVES")
        self.instruction("        ) else $error(\"TDEST out of range for master %0d\", m);")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("`endif")
        self.instruction("")

    def verilog(self, file_path):
        """Generate complete RTL (main entry point)"""
        # Generate header comment
        self.generate_header_comment()

        # Generate logic sections
        self.generate_request_decode()
        self.generate_arbiter_logic()
        self.generate_crossbar_mux()
        self.generate_backpressure_logic()
        self.generate_wakeup_logic()
        self.generate_check_logic()
        self.generate_performance_counters()
        self.generate_assertions()

        # Module framework handles module header/footer
        self.start()  # Auto-generates module header with ports/params
        self.end()    # Auto-generates endmodule

        # Write to file
        self.write(file_path, f'{self.module_name}.sv')


class DeltaSplitter1to2(Module):
    """1:2 Splitter node for tree topology"""

    module_str = 'delta_split_1to2'

    def __init__(self, config: DeltaConfig):
        Module.__init__(self, module_name=self.module_str)
        self.cfg = config

        param_str = f'''
            parameter int DATA_WIDTH = {config.data_width},
            parameter int DEST_WIDTH = {config.dest_width},
            parameter int ID_WIDTH   = {config.id_width},
            parameter int USER_WIDTH = {config.user_width},
            parameter int SPLIT_BIT  = 0
        '''
        self.params.add_param_string(param_str)

        port_str = '''
            input  logic aclk,
            input  logic aresetn,

            input  logic [DATA_WIDTH-1:0]  s_axis_tdata,
            input  logic                   s_axis_tvalid,
            output logic                   s_axis_tready,
            input  logic                   s_axis_tlast,
            input  logic [DEST_WIDTH-1:0]  s_axis_tdest,
            input  logic [ID_WIDTH-1:0]    s_axis_tid,
            input  logic [USER_WIDTH-1:0]  s_axis_tuser,

            output logic [DATA_WIDTH-1:0]  m0_axis_tdata,
            output logic                   m0_axis_tvalid,
            input  logic                   m0_axis_tready,
            output logic                   m0_axis_tlast,
            output logic [DEST_WIDTH-1:0]  m0_axis_tdest,
            output logic [ID_WIDTH-1:0]    m0_axis_tid,
            output logic [USER_WIDTH-1:0]  m0_axis_tuser,

            output logic [DATA_WIDTH-1:0]  m1_axis_tdata,
            output logic                   m1_axis_tvalid,
            input  logic                   m1_axis_tready,
            output logic                   m1_axis_tlast,
            output logic [DEST_WIDTH-1:0]  m1_axis_tdest,
            output logic [ID_WIDTH-1:0]    m1_axis_tid,
            output logic [USER_WIDTH-1:0]  m1_axis_tuser
        '''
        self.ports.add_port_string(port_str)

    def verilog(self, file_path):
        """Generate 1:2 splitter RTL"""
        self.comment("Route selection based on TDEST bit")
        self.instruction("logic route_to_1;")
        self.stmt_assign("route_to_1", "s_axis_tdest[SPLIT_BIT]")
        self.instruction("")

        self.comment("Output 0 (lower branch)")
        self.stmt_assign("m0_axis_tdata", "s_axis_tdata")
        self.stmt_assign("m0_axis_tvalid", "s_axis_tvalid && !route_to_1")
        self.stmt_assign("m0_axis_tlast", "s_axis_tlast")
        self.stmt_assign("m0_axis_tdest", "s_axis_tdest")
        self.stmt_assign("m0_axis_tid", "s_axis_tid")
        self.stmt_assign("m0_axis_tuser", "s_axis_tuser")
        self.instruction("")

        self.comment("Output 1 (upper branch)")
        self.stmt_assign("m1_axis_tdata", "s_axis_tdata")
        self.stmt_assign("m1_axis_tvalid", "s_axis_tvalid && route_to_1")
        self.stmt_assign("m1_axis_tlast", "s_axis_tlast")
        self.stmt_assign("m1_axis_tdest", "s_axis_tdest")
        self.stmt_assign("m1_axis_tid", "s_axis_tid")
        self.stmt_assign("m1_axis_tuser", "s_axis_tuser")
        self.instruction("")

        self.comment("Backpressure")
        self.stmt_assign("s_axis_tready", "route_to_1 ? m1_axis_tready : m0_axis_tready")
        self.instruction("")

        self.start()
        self.end()
        self.write(file_path, f'{self.module_name}.sv')


def calculate_widths(num_masters: int, num_slaves: int) -> Tuple[int, int]:
    """Calculate TDEST and TID widths"""
    dest_width = max(1, math.ceil(math.log2(num_slaves)))
    id_width = max(1, math.ceil(math.log2(num_masters)))
    return dest_width, id_width


def main():
    parser = argparse.ArgumentParser(
        description="Delta: AXI-Stream Crossbar Generator (Framework Version)",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    parser.add_argument("--topology", choices=["flat", "tree", "both", "mesh"], default="flat")
    parser.add_argument("--masters", type=int)
    parser.add_argument("--slaves", type=int)
    parser.add_argument("--data-width", type=int, default=64)
    parser.add_argument("--user-width", type=int, default=1)
    parser.add_argument("--strb-width", type=int, default=0,
                        help="TSTRB width in bits; 0 (default) omits TSTRB ports")
    parser.add_argument("--amba5", action="store_true",
                        help="Emit AMBA 5 sidebands: TWAKEUP steering + the IHI 0051B ch. 5 "
                             "check signals (TDATACHK, TSTRBCHK, TLASTCHK, TIDCHK, TDESTCHK, "
                             "TUSERCHK, TVALIDCHK, TREADYCHK, TWAKEUPCHK; odd parity). "
                             "Requires a whole-byte --data-width.")
    parser.add_argument("--cells-x", type=int, default=2, help="Mesh cells along X")
    parser.add_argument("--cells-y", type=int, default=2, help="Mesh cells along Y")
    parser.add_argument("--cells-z", type=int, default=1, help="Mesh cells along Z")
    parser.add_argument("--torus-x", action="store_true", help="Wrap X dimension")
    parser.add_argument("--torus-y", action="store_true", help="Wrap Y dimension")
    parser.add_argument("--torus-z", action="store_true", help="Wrap Z dimension")
    parser.add_argument("--source-route", action="store_true", help="Use source routing")
    parser.add_argument("--speculation", action="store_true", help="Enable speculative routing")
    parser.add_argument("--fifo-impl", choices=["reg", "sram"], default="reg",
                        help="Mesh router FIFO implementation")
    parser.add_argument("--output-dir", type=str, default="../rtl")
    parser.add_argument("--nodes", action="store_true")
    parser.add_argument("--no-counters", action="store_true")

    args = parser.parse_args()

    if args.topology != "mesh":
        if args.masters is None:
            parser.error("--masters is required for flat/tree/both topologies")
        if args.slaves is None:
            parser.error("--slaves is required for flat/tree/both topologies")

    if args.amba5 and args.data_width % 8:
        parser.error("--amba5 requires --data-width to be a whole number of bytes "
                     "(TDATACHK is one bit per TDATA byte, IHI 0051B Table 5-1)")
    if args.strb_width < 0:
        parser.error("--strb-width must be >= 0")

    os.makedirs(args.output_dir, exist_ok=True)

    topologies_to_generate = ["flat", "tree"] if args.topology == "both" else [args.topology]

    config = None
    if args.topology != "mesh":
        dest_width, id_width = calculate_widths(args.masters, args.slaves)
        config = DeltaConfig(
            topology=args.topology,
            num_masters=args.masters,
            num_slaves=args.slaves,
            data_width=args.data_width,
            dest_width=dest_width,
            id_width=id_width,
            user_width=args.user_width,
            strb_width=args.strb_width,
            amba5=args.amba5,
            add_performance_counters=not args.no_counters
        )

    for topo in topologies_to_generate:
        if topo == "flat":
            config.topology = topo
            generator = DeltaFlatCrossbar(config)
            generator.verilog(args.output_dir)
            print(f"Generated flat topology: {args.output_dir}/delta_axis_flat_{args.masters}x{args.slaves}.sv")
        elif topo == "mesh":
            from delta_mesh import DeltaMeshConfig, generate_mesh, validate_mesh
            mesh_cfg = DeltaMeshConfig(
                cells_x=args.cells_x,
                cells_y=args.cells_y,
                cells_z=args.cells_z,
                torus_x=args.torus_x,
                torus_y=args.torus_y,
                torus_z=args.torus_z,
                source_route=args.source_route,
                speculation=args.speculation,
                fifo_impl=args.fifo_impl,
                data_width=args.data_width,
                user_width=args.user_width,
                amba5=args.amba5,
                add_counters=not args.no_counters,
            )
            validate_mesh(mesh_cfg)
            try:
                generate_mesh(mesh_cfg, args.output_dir)
            except NotImplementedError as err:
                parser.error(str(err))
        else:
            print(f"Tree topology generation not yet implemented in framework version")

    if args.nodes:
        if config is None:
            parser.error("--nodes requires flat/tree/both topology")
        splitter = DeltaSplitter1to2(config)
        splitter.verilog(args.output_dir)
        print(f"Generated node primitive: {args.output_dir}/delta_split_1to2.sv")

    print(f"\n{'='*70}")
    print(f"Delta generation complete (framework version)!")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
