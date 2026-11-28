#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gen_port_tables
# Purpose: Regenerate the port and parameter tables of the peregrine HAS and
#          MAS from the RTL, so the books cannot drift from the source.
#
# Each table sits between marker comments in a chapter:
#     <!-- GEN:ports:peregrine_core -->  ...  <!-- /GEN -->
#     <!-- GEN:params:peregrine_core --> ...  <!-- /GEN -->
# Names, directions, widths and defaults come from the module header.  The
# description is the port's own trailing comment when it has one, otherwise
# the entry in DESC below; a port with neither is an error, as is a DESC or
# GROUPS entry naming a port the module does not have.
#
# Usage: python3 gen_port_tables.py [--check]   (from any directory)
#   --check  exit 1 if any chapter would change (nothing is written)

import pathlib
import re
import sys

DOCS = pathlib.Path(__file__).resolve().parent.parent      # .../docs
RTL = DOCS.parent / "rtl"
BOOKS = [DOCS / "peregrine_has", DOCS / "peregrine_mas"]

SOURCES = {
    "peregrine_core": RTL / "top/peregrine_core.sv",
    "peregrine_top": RTL / "top/peregrine_top.sv",
    "peregrine_bpred": RTL / "fub/peregrine_bpred.sv",
    "peregrine_csr": RTL / "fub/peregrine_csr.sv",
    "peregrine_mdu": RTL / "fub/peregrine_mdu.sv",
    "peregrine_hazard": RTL / "fub/peregrine_hazard.sv",
    "peregrine_icache": RTL / "fub/peregrine_icache.sv",
    "peregrine_clint": RTL / "fub/peregrine_clint.sv",
    "peregrine_uc_axi": RTL / "fub/peregrine_uc_axi.sv",
    "peregrine_axi4_arb": RTL / "fub/peregrine_axi4_arb.sv",
    "peregrine_if_id": RTL / "fub/peregrine_if_id.sv",
    "peregrine_id_ex": RTL / "fub/peregrine_id_ex.sv",
    "peregrine_ex_mem": RTL / "fub/peregrine_ex_mem.sv",
    "peregrine_mem_wb": RTL / "fub/peregrine_mem_wb.sv",
}

AXI_MASTER = {
    "arid": "Read address id", "araddr": "Read address", "arlen": "Burst length - 1",
    "arsize": "Beat size (log2 bytes)", "arburst": "Burst type", "arvalid": "Read address valid",
    "arready": "Read address ready", "rid": "Read data id", "rdata": "Read data beat",
    "rresp": "Read response", "rlast": "Last read beat", "rvalid": "Read data valid",
    "rready": "Read data ready", "awid": "Write address id", "awaddr": "Write address",
    "awlen": "Burst length - 1", "awsize": "Beat size (log2 bytes)", "awburst": "Burst type",
    "awvalid": "Write address valid", "awready": "Write address ready", "wdata": "Write data beat",
    "wstrb": "Write byte strobes", "wlast": "Last write beat", "wvalid": "Write data valid",
    "wready": "Write data ready", "bid": "Write response id", "bresp": "Write response",
    "bvalid": "Write response valid", "bready": "Write response ready",
    "arlock": "Driven 0", "arcache": "Driven 0", "arprot": "Driven 0", "arqos": "Driven 0",
    "arregion": "Driven 0", "awlock": "Driven 0", "awcache": "Driven 0", "awprot": "Driven 0",
    "awqos": "Driven 0", "awregion": "Driven 0",
}


def axi_desc(name):
    """Generic description of an AXI4 channel signal, by its suffix."""
    for prefix, extra in (("m_axi_", ""), ("s_axi_", " (per master, flattened)")):
        if name.startswith(prefix) and name[len(prefix):] in AXI_MASTER:
            return AXI_MASTER[name[len(prefix):]] + extra
    return None


RVFI = {
    "rvfi_valid": "One instruction retires this cycle (WB, not under mem_wait)",
    "rvfi_order": "Retire index, counting trap beats",
    "rvfi_pc_rdata": "PC of the retiring instruction",
    "rvfi_pc_wdata": "Its next PC: the trap vector on a trap, mepc on mret",
    "rvfi_insn": "Instruction word",
    "rvfi_trap": "The instruction trapped in MEM (no rd write, no memory access)",
    "rvfi_rs1_addr": "rs1 field", "rvfi_rs2_addr": "rs2 field",
    "rvfi_rs1_rdata": "rs1 value used (the latched operand for an M instruction)",
    "rvfi_rs2_rdata": "rs2 value used (the latched operand for an M instruction)",
    "rvfi_rd_addr": "rd written, 0 when none", "rvfi_rd_wdata": "Value written to rd, 0 when none",
    "rvfi_mem_addr": "Word address of the access", "rvfi_mem_rmask": "Bytes read",
    "rvfi_mem_wmask": "Bytes written", "rvfi_mem_rdata": "Word read",
    "rvfi_mem_wdata": "Data written, on its lanes",
}

DESC = {
    "peregrine_core": {
        "clk": "Core clock", "rst_n": "Asynchronous active-low reset (synchronized inside)",
        "imem_rdata": "The word at imem_addr, this cycle (comb read, or a registered read at last cycle's imem_addr_next)",
        "imem_addr": "PC of the instruction being fetched",
        "dmem_req": "Load or store in MEM this cycle (gated by mem_wait)",
        "dmem_addr": "Word address of the access",
        "dmem_rdata": "The load's word in the cycle after the request (WB), held until WB retires",
        "dmem_wstrb": "Store byte strobes, 0 for a load",
        "dmem_wdata": "Store data, rotated onto its lanes",
        "irq_software": "Machine software interrupt (level)",
        "irq_timer": "Machine timer interrupt (level)",
        "irq_external": "Machine external interrupt (level)",
        **RVFI,
        "rvfi_trap_cause": "mcause of the trap committed with this beat, valid with rvfi_trap",
        "rvfi_bp_pred_taken": "Predicted taken at fetch",
        "rvfi_bp_pred_target": "Predicted target at fetch",
        "rvfi_bp_mispredict": "EX found the prediction wrong",
    },
    "peregrine_top": {
        "clk": "Clock for the core, caches and fabric port",
        "rst_n": "Asynchronous active-low reset (synchronized inside)",
        "irq_external": "Machine external interrupt (level)",
        "tb_irq_software": "TB hook ORed into the CLINT software interrupt; tie 0",
        "tb_irq_timer": "TB hook ORed into the CLINT timer interrupt; tie 0",
        "dc_clean_req": "Hold high to clean the D$ (TB / debug hook); tie 0",
        "dc_clean_done": "High from the clean's completion until dc_clean_req drops",
        "dobs_valid": "A load or store was accepted this cycle",
        "dobs_addr": "Its word address", "dobs_wstrb": "Its byte strobes (0 for a load)",
        "dobs_wdata": "Its store data",
        **RVFI,
        "rvfi_trap_cause": "mcause of the trap committed with this beat, valid with rvfi_trap",
        "rvfi_bp_pred_taken": "Predicted taken at fetch",
        "rvfi_bp_pred_target": "Predicted target at fetch",
        "rvfi_bp_mispredict": "EX found the prediction wrong",
    },
    "peregrine_bpred": {"clk": "Clock", "rst_n": "Reset (BTB valid bits only)",
                        "lookup_pc": "Fetch PC (IF)", "pred_taken": "Guess: taken",
                        "pred_target": "Guess: target (meaningful when taken)",
                        "upd_pc": "PC of the resolved instruction", "upd_taken": "Its resolved direction",
                        "upd_target": "Its resolved target"},
    "peregrine_csr": {"clk": "Clock", "rst_n": "Reset",
                      "raddr": "CSR address of the instruction in EX", "rdata": "Its current value",
                      "r_exists": "The address is implemented (0: illegal instruction)",
                      "wen": "CSR write committed in MEM", "waddr": "Its address", "wdata": "Its value",
                      "trap_take": "Trap entry committed in MEM", "trap_cause": "mcause to write",
                      "trap_epc": "mepc to write (the trapping PC)", "trap_tval": "mtval to write",
                      "irq_buserr": "amber's write-back error status, mip.16 (level; BUSERR_EN)",
                      "buserr_info": "What mbuserr (0x7C0) reads: {line address[31:2], overflow, valid}",
                      "buserr_clear": "A write to mbuserr committed (pulse): clears amber's status",
                      "mret_take": "mret committed in MEM",
                      "irq_block": "hold irq_pending low: from an mret until the next instruction commits (TASK-007)",
                      "irq_software": "MSIP pin (level)", "irq_timer": "MTIP pin (level)",
                      "irq_external": "MEIP pin (level)",
                      "mtvec": "Trap vector (direct mode)", "mepc": "Return PC for mret",
                      "irq_pending": "An enabled interrupt was pending and mstatus.MIE set in the previous cycle (registered)",
                      "irq_cause": "Its mcause (MEI > MSI > MTI)"},
    "peregrine_mdu": {"clk": "Clock", "rst_n": "Reset (busy, done, count)",
                      "funct3": "M-extension operation", "idle": "Neither busy nor done",
                      "done": "Result valid, held until consumed",
                      "result": "Result word, valid under done"},
    "peregrine_hazard": {"fwd_a": "rs1 forwarding select (FWD_*)", "fwd_b": "rs2 forwarding select (FWD_*)",
                         "stall_ifid": "Load-use stall", "flush_ifid": "EX redirect flush of IF/ID",
                         "flush_idex": "EX redirect flush of ID/EX",
                         "id_rs1_addr": "ID rs1 (load-use check)", "id_rs2_addr": "ID rs2 (load-use check)",
                         "fwd_rs1_addr": "rs1 compared for forwarding", "fwd_rs2_addr": "rs2 compared for forwarding",
                         "idex_rd_addr": "rd of the instruction in EX", "idex_is_load": "The instruction in EX is a valid load",
                         "exmem_rd_addr": "Producer for the EX/MEM arm", "exmem_rd_wen": "Its write enable",
                         "memwb_rd_addr": "Producer for the MEM/WB arm", "memwb_rd_wen": "Its write enable",
                         "ex_flush": "EX redirect (mispredict)"},
    "peregrine_icache": {"clk": "Clock", "rst_n": "Reset (state and valid bits)",
                         "fetch_rdata": "Word at fetch_addr, the cycle after", "stall": "fetch_rdata is not the word at fetch_addr",
                         "inv_req": "Invalidate request (level, fence.i)", "inv_ack": "Pulses on the cycle every valid bit clears"},
    "peregrine_clint": {"clk": "Clock", "rst_n": "Reset", "req_valid": "Register access this cycle",
                        "req_we": "Write", "req_wstrb": "Byte strobes", "req_wdata": "Write data",
                        "rsp_valid": "Response, the cycle after the request", "rsp_rdata": "Read data",
                        "irq_software": "msip bit 0", "irq_timer": "mtime >= mtimecmp (registered)"},
    "peregrine_uc_axi": {"clk": "Clock", "rst_n": "Reset", "req_valid": "Load or store request",
                         "req_ready": "Idle: one transaction at a time", "req_addr": "Byte address",
                         "req_we": "Store", "req_wstrb": "Byte strobes of the 32-bit word", "req_wdata": "Store word",
                         "rsp_valid": "One-cycle response (a store's after B)", "rsp_rdata": "Load word, 0 outside rsp_valid",
                         "rsp_err": "The response was SLVERR / DECERR (RRESP[1] / BRESP[1]), with rsp_valid"},
    "peregrine_axi4_arb": {"clk": "Clock", "rst_n": "Reset"},
}
for _m in ("peregrine_if_id", "peregrine_id_ex", "peregrine_ex_mem", "peregrine_mem_wb"):
    DESC[_m] = {"clk": "Clock", "rst_n": "Reset (control fields)", "stall": "Hold the record",
                "flush": "Load the bubble record (wins over stall)", "d_i": "Record in", "q_o": "Record out"}

PDESC = {
    "RESET_ADDR": "First fetch address",
    "MUL_DSP": "0: iterative multiply (33 stall cycles); 1: one registered DSP product (2)",
    "BP_EN": "1: BTB + BHT prediction; 0: predict not taken (merlin's fetch)",
    "BTB_ENTRIES": "BTB entries, a power of two (PRD P5: 32)",
    "BHT_ENTRIES": "BHT counters, a power of two >= BTB_ENTRIES (PRD P5: 256)",
    "CACHE_EN": "0: cacheless build (PRD P12); 1: the build inside peregrine_top",
    "ICACHE_BYTES": "I$ capacity (PRD P9: 4096)", "ICACHE_LINE": "I$ line size (PRD P9: 64)",
    "AXI_DW": "Fabric data width, and amber's BUS_WIDTH (32 or 64)",
    "AXI_IW": "Per-master AXI id width; the fabric id is AXI_IW + 2",
    "MTIME_DIV": "CLINT clocks per mtime tick (>= 1)",
    "DC_SETS": "amber sets", "DC_WAYS": "amber ways", "DC_LINE": "amber line bytes",
    "FIW": "Fabric id width (derived)", "STRBW": "Strobe width (derived)",
    "M_EXT": "Sets misa.M",
    "SIZE_BYTES": "Capacity, a power of two", "LINE_BYTES": "Line size, a power of two >= AXI_DW/8",
    "NM": "Number of masters (>= 2)", "MI_W": "Master index width (derived)",
}
PDESC_MOD = {
    ("peregrine_axi4_arb", "FIW"): "Fabric id width, AXI_IW + MI_W (derived)",
    ("peregrine_axi4_arb", "AXI_IW"): "Master-side id width",
    ("peregrine_icache", "AXI_DW"): "Fabric data width, 32 or 64",
    ("peregrine_icache", "AXI_IW"): "AXI id width; the I$ always uses id 0",
    ("peregrine_uc_axi", "AXI_DW"): "Fabric data width, 32 or 64",
    ("peregrine_uc_axi", "AXI_IW"): "AXI id width; the port always uses id 0",
    ("peregrine_axi4_arb", "AXI_DW"): "Data width",
    ("peregrine_mdu", "MUL_DSP"): "0: multiply iteratively, 32 steps; 1: one registered 32x32 product",
    ("peregrine_top", "UC_BASE"): "Uncached window base: an address is uncached when (addr & UC_MASK) == UC_BASE",
    ("peregrine_top", "UC_MASK"): "Uncached window mask (default: bits 31:28, the 0x1000_0000 window)",
    ("peregrine_csr", "BUSERR_EN"): "1: interrupt 16 (mip / mie bit 16) and the mbuserr CSR exist (the cached build)",
}

GROUPS = {
    "peregrine_core": [
        ("Clock, reset and hold", ["clk", "rst_n", "mem_wait"]),
        ("Instruction fetch", ["imem_addr", "imem_addr_next", "imem_addr_next_nw", "imem_rdata"]),
        ("Data access", ["dmem_req", "dmem_addr", "dmem_rdata", "dmem_wstrb", "dmem_wdata"]),
        ("Cached-build handshake (CACHE_EN=1; 0 when CACHE_EN=0)", ["dmem_req_pre", "fencei_req"]),
        ("Bus errors (CACHE_EN=1; tie 0 when CACHE_EN=0)", ["imem_fault", "dmem_fault", "irq_buserr",
                                                            "buserr_info", "buserr_clear"]),
        ("Interrupts", ["irq_software", "irq_timer", "irq_external"]),
        ("RVFI retire", [p for p in RVFI]),
        ("Trap and predictor observation", ["rvfi_trap_cause", "rvfi_bp_pred_taken",
                                            "rvfi_bp_pred_target", "rvfi_bp_mispredict"]),
    ],
    "peregrine_top": [
        ("Clock, reset and interrupts", ["clk", "rst_n", "irq_external", "tb_irq_software", "tb_irq_timer"]),
        ("D$ clean hook", ["dc_clean_req", "dc_clean_done"]),
        ("AXI4 fabric master: read", ["m_axi_" + k for k in AXI_MASTER if k.startswith(("ar", "r"))]),
        ("AXI4 fabric master: write", ["m_axi_" + k for k in AXI_MASTER if k.startswith(("aw", "w", "b"))]),
        ("D-side observation (TB)", ["dobs_valid", "dobs_addr", "dobs_wstrb", "dobs_wdata"]),
        ("RVFI retire", [p for p in RVFI]),
        ("Trap and predictor observation", ["rvfi_trap_cause", "rvfi_bp_pred_taken",
                                            "rvfi_bp_pred_target", "rvfi_bp_mispredict"]),
    ],
}

RE_HDR = re.compile(r"^module\s+(\w+)(?P<body>.*?)^\);", re.S | re.M)
RE_PORT = re.compile(r"^\s*(input|output|inout)\s+(?:logic|wire|reg)?\s*(?:signed\s+)?"
                     r"(\[[^\]]+\]\s*)?([\w:.]+\s+)?(\w+)\s*,?\s*(?://\s*(.*))?$")
RE_PARAM = re.compile(r"^\s*(parameter|localparam)\s+(.*?)\s*(\w+)\s*=\s*([^,/]+?)\s*,?\s*(?://\s*(.*))?$")


def parse(path):
    text = path.read_text()
    m = RE_HDR.search(text)
    if not m:
        raise SystemExit(f"{path}: no module header")
    body = m.group("body")
    split = re.search(r"^\)\s*\($", body, re.M)       # ") (" between params and ports
    if split:
        pblock, portblock = body[:split.start()], body[split.end():]
    else:
        pblock, portblock = "", body
    params, ports = [], []
    for line in pblock.splitlines():
        pm = RE_PARAM.match(line)
        if pm:
            kind, ptype, name, default, cmt = pm.groups()
            params.append(dict(kind=kind, type=ptype.strip() or "-", name=name,
                               default=default.strip(), cmt=(cmt or "").strip()))
    for line in portblock.splitlines():
        pp = RE_PORT.match(line)
        if pp:
            d, rng, typ, name, cmt = pp.groups()
            if typ and not rng:
                width = typ.strip()            # a struct type, e.g. peregrine_pkg::if_id_t
            else:
                width = (rng or "").strip() or "1"
            ports.append(dict(dir=d, width=width, name=name, cmt=(cmt or "").strip()))
    if not ports:
        raise SystemExit(f"{path}: no ports parsed")
    return params, ports


def esc(s):
    """Escape a table cell: pipes, and dollar signs (pandoc reads $...$ as math)."""
    return s.replace("|", "\\|").replace("$", "\\$")


def esc_code(s):
    """Escape a code-span cell: pipes only ($ is literal inside backticks)."""
    return s.replace("|", "\\|")


def port_tables(mod):
    _, ports = parse(SOURCES[mod])
    names = [p["name"] for p in ports]
    desc = DESC.get(mod, {})
    for k in desc:
        if k not in names:
            raise SystemExit(f"{mod}: DESC names '{k}', not a port")
    groups = GROUPS.get(mod, [("Ports", names)])
    seen = [n for _, g in groups for n in g]
    for n in seen:
        if n not in names:
            raise SystemExit(f"{mod}: GROUPS names '{n}', not a port")
    missing = [n for n in names if n not in seen]
    dup = {n for n in seen if seen.count(n) > 1}
    if missing or dup:
        raise SystemExit(f"{mod}: ports not grouped {missing}, grouped twice {sorted(dup)}")
    by = {p["name"]: p for p in ports}
    out = []
    for title, group in groups:
        rows = ["| Port | Dir | Width | Description |",
                "|----------------------|----------|------------|----------------------------------|"]
        for n in group:
            p = by[n]
            text = p["cmt"] or desc.get(n) or axi_desc(n)
            if not text:
                raise SystemExit(f"{mod}.{n}: no trailing comment and no DESC entry")
            rows.append(f"| `{n}` | {p['dir']} | `{esc_code(p['width'])}` | {esc(text)} |")
        cap = f": {mod} ports" if len(groups) == 1 else f": {mod} ports: {esc(title)}"
        out.append("\n".join(rows) + "\n\n" + cap + "\n")
    return "\n".join(out)


def param_table(mod):
    params, _ = parse(SOURCES[mod])
    if not params:
        return "No parameters.\n"
    rows = ["| Parameter | Kind | Type | Default | Description |",
            "|----------------|----------|------------|--------------|------------------------------|"]
    for p in params:
        text = PDESC_MOD.get((mod, p["name"])) or p["cmt"] or PDESC.get(p["name"])
        if not text:
            raise SystemExit(f"{mod}.{p['name']}: no description")
        rows.append(f"| `{p['name']}` | {p['kind']} | `{esc_code(p['type'])}` | `{esc_code(p['default'])}` | {esc(text)} |")
    return "\n".join(rows) + f"\n\n: {mod} parameters\n"


RE_BLOCK = re.compile(r"(<!-- GEN:(ports|params):(\w+) -->\n)(.*?)(<!-- /GEN -->)", re.S)


def regen(text):
    def sub(m):
        body = port_tables(m.group(3)) if m.group(2) == "ports" else param_table(m.group(3))
        return m.group(1) + "\n" + body + "\n" + m.group(5)
    return RE_BLOCK.sub(sub, text)


def main():
    check = "--check" in sys.argv[1:]
    changed = []
    for book in BOOKS:
        for md in sorted(book.rglob("*.md")):
            old = md.read_text()
            new = regen(old)
            if new != old:
                changed.append(md)
                if not check:
                    md.write_text(new)
    for md in changed:
        print(("stale: " if check else "updated: ") + str(md.relative_to(DOCS)))
    if not changed:
        print("port/parameter tables current")
    return 1 if (check and changed) else 0


if __name__ == "__main__":
    sys.exit(main())
