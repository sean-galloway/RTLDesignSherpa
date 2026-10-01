"""Generate the scoria_core DV wrapper's declarations from the core's own ports.

scoria_core declares TWO PORTS ON ONE LINE in the AXI block:

    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,

so the unit of parsing is the COMMA-SEPARATED FRAGMENT, not the line. A
fragment that starts with input/output re-declares direction and type; one that
does not inherits both from the fragment before it (a genuine `a_i, b_i` list).
Getting that wrong produced `input logic [IW-1:0] input logic [AW-1:0]
s_axi_awaddr` and verilator rejected it on the first elaboration -- which is
why this generator is always followed by one.
"""
import re, sys

src = open("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/top/scoria_core.sv").read()
block = src[src.index(") ("):]
block = block[:block.index("\n);")]

DFI = re.compile(r"^dfi_(address|bank|cas_n|ras_n|we_n|cs_n|odt|wrdata|wrdata_en|"
                 r"wrdata_mask|rddata_en|rddata|rddata_valid|init_start|init_complete)_[io]$")
OBS = re.compile(r"^(stall_|stat_|zq_|wrlvl_|mr_wr|cl_o|cwl_o|bl_o|init_done|"
                 r"dram_reset_n|dfi_phylvl_|dfi_phy_wrlvl_|dfi_wrlvl_)")
TYPE = r"(?:logic|memtype_e|page_policy_e|dram_op_e)\s*(?:\[[^\]]+\]\s*)*"

# strip comments, join into one stream, split on commas
text = "\n".join(l.split("//")[0] for l in block.splitlines())
# The block starts at the ") (" that closes the parameter list and opens the
# port list, so cut past that "(" unconditionally. Guarding it on
# `startswith("(")` left the ")" glued to the first fragment, which silently
# DROPPED aclk -- and a dropped clock surfaces only as `.*` failing to find it,
# four hundred lines away.
text = text[text.index("(") + 1:]
frags = [f.strip() for f in text.split(",")]

ports, nets, dfi = [], [], []
cur_dir = cur_typ = None
for frag in frags:
    if not frag:
        continue
    m = re.match(rf"^(input|output)\s+({TYPE})\s*(.+)$", frag, re.S)
    if m:
        cur_dir, cur_typ, rest = m.group(1), m.group(2).strip(), m.group(3).strip()
    else:
        if cur_dir is None:
            continue
        rest = frag
    # trailing unpacked dimension
    unpacked = ""
    um = re.search(r"(\[[^\]]+\])\s*$", rest)
    if um and not re.match(r"^\[", rest):
        unpacked = " " + um.group(1)
        rest = rest[:um.start()].strip()
    name = rest.strip()
    if not re.match(r"^[A-Za-z_]\w*$", name):
        print(f"UNPARSED FRAGMENT: {frag!r} -> name {name!r}", file=sys.stderr)
        continue
    if DFI.match(name):
        dfi.append((cur_dir, cur_typ, name))
    elif cur_dir == "output" and OBS.match(name):
        nets.append(f"    {cur_typ} {name}{unpacked};")
    else:
        ports.append(f"    {cur_dir} {cur_typ} {name}{unpacked},")

print("// ---- PORTS (BFM- and TB-driven) ----")
print("\n".join(ports))
print("\n// ---- OBSERVABLE NETS (read by the test, not wrapper ports) ----")
print("\n".join(nets))
print("\n// ---- DFI, renamed for the BFM ----")
for d, t, n in dfi:
    base = n[:-2] if n.endswith(("_i", "_o")) else n
    print(f"    {t} phy_{base};   // core {n} ({d})")
