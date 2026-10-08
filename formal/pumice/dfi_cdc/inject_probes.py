#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# inject_probes.py -- bring pumice_dfi_cdc's pairing/edge internals out as
# probe ports on the GENERATED flat file (cdc_flat.v), for the formal wrapper.
#
# WHY THIS EXISTS (TASK-035, the dfi_cdc name-resolution blocker, root-caused
# 2026-10-08). yosys 0.62 in this flow does NOT resolve hierarchical references
# from the wrapper into the DUT: `dut.w_wtok_push` "elaborates" as an IMPLICIT
# WIRE (frontend warning "Identifier ... is implicitly declared"), and in formal
# mode an undriven wire is a FREE INPUT. The first version of this wrapper
# asserted on such wires -- demonstrably not the source signals (wd_ready_o and
# the accepted-beat wire both 1 while the probed w_wtok_ready read 0, which the
# RTL makes impossible). The same silently-free mechanism is why wr_data_cam's
# disabled SRAM-readback check could not be corroborated. So internals are made
# observable the honest way: probe OUTPUT PORTS on the DUT in the generated,
# untracked flat file. The tracked RTL is never touched.
#
# THE AUDIT IS THE INJECTION. For every internal net, the expected source
# hookup is verified textually, INSTANCE BY INSTANCE, against the sv2v output
# before anything is wired; a mismatch fails the build (no silent mis-wire).
# The two init-token FIFOs leave wr_ready DANGLING (`wr_ready()`), so those
# hookups are filled with named nets and surfaced as probes -- a dangling port
# cannot be observed at all.

import sys

# Expected source hookups, instance by instance: the flat net an instance
# port is connected to. Checked verbatim inside that instance's port map.
SRC_HOOKUPS = [
    ("u_cmd_fifo",  "wr_ready", "cmd_ready_o"),
    ("u_wd_fifo",   "wr_ready", "w_wd_data_ready"),
    ("u_wtok_fifo", "wr_valid", "w_wtok_push"),
    ("u_wtok_fifo", "wr_ready", "w_wtok_ready"),
    ("u_wtok_fifo", "rd_valid", "pwr_staged_valid_o"),
    ("u_rd_fifo",   "wr_ready", "prd_ready_o"),
]

# Direct-alias probes: output port driven by an existing module-level net.
ALIAS_PROBES = [
    ("o_p_w_wd_data_ready", "w_wd_data_ready"),
    ("o_p_w_wtok_ready",    "w_wtok_ready"),
    ("o_p_w_wtok_push",     "w_wtok_push"),
    ("o_p_w_istart_push",   "w_istart_push"),
    ("o_p_w_icmp_push",     "w_icmp_push"),
]

# Dangling wr_ready hookups (init token FIFOs): instance -> probe net/port.
DANGLING_PROBES = {"u_istart_tok": "w_istart_tok_ready",
                   "u_icmp_tok":   "w_icmp_tok_ready"}


def instance_body(text, inst):
    """Return the port-map slice of `inst`'s instantiation, or None."""
    pat = ") " + inst + "("
    idx = text.find(pat)
    if idx < 0:
        return None
    start = text.index("(", idx)
    end = text.index(");", start)
    return text[start:end]


def main():
    if len(sys.argv) != 3:
        sys.exit("usage: inject_probes.py <in: sv2v output> <out: probed flat>")
    src, dst = sys.argv[1], sys.argv[2]
    text = open(src).read()

    # --- 1. the instance-by-instance hookup audit -------------------------
    for inst, port, expr in SRC_HOOKUPS:
        body = instance_body(text, inst)
        want = ".%s(%s)" % (port, expr)
        if body is None or want not in body:
            sys.exit("inject_probes: AUDIT FAIL: %s.%s is not hooked to `%s` "
                     "in the sv2v output -- flat net names changed; re-audit "
                     "before probing" % (inst, port, expr))

    # --- 2. fill the dangling wr_ready hookups ----------------------------
    for inst, net in DANGLING_PROBES.items():
        body = instance_body(text, inst)
        if body is None:
            sys.exit("inject_probes: AUDIT FAIL: instance %s not found" % inst)
        if (".wr_ready(%s)" % net) in body:
            continue                                   # idempotent
        if ".wr_ready()" not in body:
            sys.exit("inject_probes: AUDIT FAIL: %s.wr_ready is not dangling "
                     "as expected -- re-audit" % inst)
        start = text.index("(", text.find(") " + inst + "("))
        end = text.index(");", start)
        seg = text[start:end].replace(".wr_ready()", ".wr_ready(%s)" % net, 1)
        text = text[:start] + seg + text[end:]

    # --- 3. add the probe ports to module pumice_dfi_cdc ------------------
    mod_start = text.index("module pumice_dfi_cdc (")
    hdr_end = text.index(");", mod_start)
    if "o_p_w_wtok_push" not in text[mod_start:hdr_end]:
        names = ","
        names += "".join("\n\t%s," % p for p, _ in ALIAS_PROBES)
        names += "".join("\n\t%s," % p for p in DANGLING_PROBES.values())
        names = names.rstrip(",")          # no trailing comma before `);`
        text = text[:hdr_end] + names + text[hdr_end:]
        decl_at = text.index(");", mod_start) + 2
        decls = "".join("\toutput wire %s;\n" % p for p, _ in ALIAS_PROBES)
        decls += "".join("\toutput wire %s;\n" % p for p in DANGLING_PROBES.values())
        decls += "".join("\tassign %s = %s;\n" % (p, n)
                         for p, n in ALIAS_PROBES)
        text = text[:decl_at] + "\n" + decls + text[decl_at:]

    open(dst, "w").write(text)
    print("inject_probes: %d hookups audited, %d probes wired"
          % (len(SRC_HOOKUPS), len(ALIAS_PROBES) + len(DANGLING_PROBES)))


if __name__ == "__main__":
    main()
