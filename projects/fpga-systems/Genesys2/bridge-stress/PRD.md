<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Genesys 2 (Kintex-7) Bridge Stress Model -- PRD

**Version:** 0.3 (draft) · **Date:** 2026-10-19 · **Status:** AXI4, AXI3 and AXI5 builds passing on the Genesys 2: 27/27 board runs each (9 profiles x 3 seeds x 4000 bursts per master direction) and a 15-minute chaos soak each

## 1. Purpose

Validate the bridge generator's fabrics in silicon, independent of any other
IP. Every port of the device under test (a generated bridge) is driven or
answered by a purpose-built stress block, so the only design on the board
whose behaviour is in question is the bridge.

The existing harnesses were reviewed first. Their blocks are kept where they
fit and not used where they cannot check a fabric:

| Block | From | Why not as-is |
|---|---|---|
| `axi4_master_wr_injector` / `axi4_master_rd_crc_check` | pumice / DDR2 characterization | the read checker regenerates each beat's address in AR issue order and never checks RID/BID: a fabric that reorders across IDs or interleaves R (this one does both) fails it falsely, and a misrouted response goes unseen |
| `axi4_slave_rd_injector` / `axi4_slave_wr_crc_check` | STREAM characterization | one burst at a time, in order, with a running CRC per channel: they cannot reorder, interleave, or answer per-ID, which is what exercises the bridge's response paths |

What carries over: the address-generation discipline, the protocol channel
modules (`axi4_{master,slave}_{rd,wr}`), the UART host link and
configuration-bridge pattern, the stage-then-GO launch, PeakRDL register
access by name, and the sim harness that runs the board's own host code.

## 2. The data contract

Every byte is a function of its fabric address, the owning slave's tag and
the direction (`rtl/amba/includes/axi_stress_pkg.sv`, `f_word`). Nothing is
stored, so any master may read or write any slave, responses may come back in
any order, and a byte that lands on the wrong lane, beat, address or slave
fails the check at the far end. The function is xorshift32-based: a bijection,
so an address error is always a data error, and XOR-only, so it costs two
LUT levels at bus rate.

Real memories (build-xil: LiteDRAM DDR3, the AXI BRAM controller) keep what they
are given, so a window onto one is a *mem* window (`f_maddr`): every write of
a byte carries the value a read of it expects, `f_word(f_maddr(A), tag, RD)`,
with `f_maddr(A)` the address modulo 2^MEM_LG2. Writes are then idempotent:
the contents stay a function of the address whatever order any number of
masters write in, and reads check as before. Every mem window shares one tag
(`bstress.MEM_TAG`) and hashes modulo 1 MB, so two memories hold one image
at equal offsets and a copy engine moving bytes between them keeps both
checkable; a misroute between them at the same offset is the one error it
cannot see. A memory starts unknown, so each run opens with a fill GO (a
stress master sweeps it in full-width bursts, cfg FILL) and closes with a
read sweep that checks every byte -- whatever the vendor masters wrote
included.

## 3. Architecture

| Layer | Where | What |
|---|---|---|
| stress cores | `rtl/amba/shared/axi_stress_*.sv` | protocol-neutral master (generator + per-ID ordered scoreboard, rd and wr) and slave (hash responder with reorder / interleave / latency / throttle / SLVERR window); `cfg` / `sts` structs, no CSRs |
| protocol shells | `rtl/amba/shared/<proto>_{master,slave}_stress.sv` | the cores on the protocol's channel modules: AXI4, AXI3 (bursts cut to 16 beats in the generator, WID carried with each W beat, 2-bit lock), AXI5 (`axi5_*` channel modules; NSAID / TRACE / MPAM / MECID / POISON per port, from the DUT TOML's `axi5_features`), AXI4-Lite (`axil4_*` channel modules; the cores built `LEN_MASK = 0` and `SIZE_FIXED`, so every transfer is one aligned bus-wide beat; the master keeps each direction's issued IDs in a FIFO and stamps them back onto the in-order responses, the slave presents every request to its core as ID 0), AXI5-Lite (`axil5_*` channel modules; single-beat as AXI4-Lite, but the cores' IDs go on the bus and the slave may answer different IDs in any order, IHI 0022L B2.1.5; TRACE and POISON as on AXI5; USER not driven), APB4 / APB5 (`apb4_*` / `apb5_*` requester and completer; one 32-bit transfer at a time, the master's two cores sharing the bus round-robin with a `{write, ID}` FIFO routing each response back, the slave handing each transfer to its core and in offset mode behind a bridge; the APB5 slave waits for PWAKEUP before PREADY, the APB5 master drives it by IHI 0024E 3.7.2; USER and parity off) |
| register blocks | `rtl/regs/*.rdl`, `rtl/bstress_{mst,slv}_csr.sv` | one regblock per block, in that block's clock (`apb4_to_peakrdl` carries the access across) |
| harness | `rtl/generated/bs_harness_<dut>/` from `bin/gen_bs_harness.py` | generated from the DUT TOML: one shell per DUT port, the configuration bridge, control regs, GO/STOP into every clock |
| board top | `rtl/bs_genesys2_top.sv` | MMCM (aclk 100 MHz, cclk 75 MHz), resets, UART, LEDs |
| board top, build-xil | `rtl/bs_genesys2_xil_top.sv`, `fpga/tcl/bs_xil_ip.tcl` | the harness's vendor ports on third-party IP: LiteDRAM DDR3 (`bs_litedram`, generated by `bin/gen_litedram.sh` from `rtl/litedram/bs_litedram.yml`; its user_clk is aclk, cclk from an MMCM on it), AMD/Xilinx AXI BRAM controller + block memory, AXI Traffic Generator, AXI Central DMA, an AXI Protocol Checker on each memory link; IP status into EXT_STS0..3 |
| vendor host | `bin/bstress_xil.py` | programs the traffic generator (command lists, master RAM image) and the DMA (copies at equal offsets) around each run and checks what they report and read |
| host | `bin/bstress.py`, `bin/run_stress.py` | window plan from the TOML, profiles, verdict; the same code in sim and on the board |

### Checks

| Code | Side | Fires on |
|---|---|---|
| RD_STRAY / WR_STRAY | master | a response on an ID with nothing outstanding |
| RD_LAST | master | RLAST on the wrong beat of the burst its RID names |
| RD_RESP / WR_RESP | master | a response code other than the window's (OKAY / SLVERR / DECERR) |
| RD_DATA | master | an active byte lane differs from `f_word` |
| WR_EARLY | master | a B before the burst's last W left the master |
| HANG | master | work outstanding and no response for 2^n cycles |
| S_ADDR | slave | a request outside the slave's window (misroute) |
| S_PROTO | slave | an illegal burst: size, WRAP shape, FIXED/WRAP length, 4 KB crossing |
| S_WDATA / S_WSTRB / S_WLAST | slave | a strobed byte wrong, a strobe outside the beat, WLAST misplaced |
| S_WID | AXI3 slave | a W beat whose WID is not the AWID of the burst it belongs to (interleaved or mis-stamped write data) |
| S_SB | AXI5 slave | a request's NSAID / TRACE / MPAM / MECID is not `f_sb(address)` (from a master whose path carries sideband natively) or not 0 (from any other: the slave tells them apart by the master index in the fabric ID), a W beat's WPOISON is not `f_poison(beat address)`, or a request breaks the IDUNQ rule on the IDs the slave sees (unique with another burst of its ID held, or any request on an ID whose held burst is unique) |
| M_SB | AXI5 master | BTRACE / RTRACE is not the request's TRACE (a trace-capable bridge port echoes it whatever the slave, bridge BUG-010), an R beat's RPOISON is not `f_poison(beat address)`, or BIDUNQ / RIDUNQ is not the bit the burst was issued with |
| S_PROTO (atomics) | AXI5 slave | an AWATOP the master would never issue: not one aligned INCR beat inside the bus, a size its class does not allow, a reserved encoding |
| RD_* in a write block | AXI5 master | a read-return atomic's R beat: no atomic owed on its RID (RD_STRAY), RLAST low (RD_LAST), RRESP not the window's (RD_RESP), a lane not `f_word(address, tag, RD)` (RD_DATA) |

AXI5 sideband and poison follow the data contract: every field is a hash of
the address (`f_sb`, `f_poison` in `axi_stress_pkg`), so both ends compute it
and nothing is stored. Poison is drawn 1 beat in 2^POISON_LG2 by address
hash, on paths where both ends enable it.

AXI5 IDUNQ: a master marks a burst unique (by address hash) only when its ID
has nothing outstanding, and issues nothing more on that ID until it
completes. The bridge's master port regenerates BIDUNQ / RIDUNQ; every IDUNQ
slave checks that the fabric still keeps the rule on the IDs it sees.

AXI5 atomics: 1 write burst in 2^WR_ATOM.LG2 on an atomic path becomes one
legal beat -- AtomicStore / Load / Swap / Compare by address hash, 1..8
bytes (2..32 for Compare), aligned INCR -- on an ID with the MSB set, issued
only when that ID has nothing outstanding (the AXI5 atomic ID rule). The
operand is ordinary write data. The slave is stateless, so a read-return
atomic's "original value" is the read hash `f_word(address, tag, RD)` on the
beat's lanes; it is sent after the W beat and merged onto R between read
bursts.

AXI5 MTE: one 4-bit tag per 16 bytes, every field a hash of an address both
ends know (`axi_stress_pkg`): AWTAGOP Invalid / Transfer / Update / Match
(Invalid on an atomic), ARTAGOP Invalid / Transfer / Fetch, WTAG / RTAG per
16-byte slot (0 when the tag operation is Invalid), WTAGUPDATE on Update,
BTAGMATCH pass / fail on Match. The slave checks the request and W side
(S_SB), the master RTAG and BTAGMATCH (M_SB). Every per-address choice
(poison, the MTE fields, the atomic and IDUNQ picks) uses the keyed hash
`f_hk`, not `f_sb` with an XOR key: xorshift is linear, and XOR-keyed picks
off one address are locked together (the first MTE run never failed a tag
match).

### Limits

| Limit | Value | Why / effect |
|---|---|---|
| bridge: read-return atomics in flight per slave port | 8 | the slave adapter's `axi5_atomic_rr_tracker` is built `DEPTH(8)`; the ninth atomic AW stalls until a slot frees (bridge TASK-020 makes it a TOML key). Slows a run, never fails it |
| bridge: atomic masters per fabric | none | every fabric ID carries its master's index, so atomics from different masters never alias at a slave |
| model: atomic IDs | the upper half of each atomic master's ID space | atomics use ID MSB = 1; the host keeps that master's read and write IDs below it. An atomic master needs `id_width >= 2` |
| model: atomics and IDUNQ bursts in flight | one per ID | the AXI5 rules; the master waits rather than violate them |
| model: read-return atomics owed per master | 16 (`DEPTH`) | a full table holds the next atomic |
| model: read-return atomics queued per slave | 16 (`DEPTH`) | a full queue holds the atomic's W beat |
| model: atomic shapes | one beat, aligned INCR, 1..8 bytes (Compare 2..32), within the bus | a slave flags any other atomic as S_PROTO, so a fabric that changes an atomic is caught |
| bridge: MTE ports | 128 bits or wider, every connected path AXI5 at both ends, MTE on and one width | the validator's rules (MAS 2.10); `bridge_bs_axi5`'s cpu clique is 128-bit for it |
| model: MTE tag operations | no tag operation on an atomic; ARTAGOP never 2'b10 | keeps every request spec-plausible |
| model: AXI4-Lite data width | 32 or 64 | AXI4-Lite allows only these; the pair test builds both |
| model: APB data width, transfers in flight | 32; one per bus | APB4 / APB5 data is at most 32 bits and the cores need 32; APB holds the bus until PREADY. The master queues up to `DEPTH` (16) commands behind it |
| model: APB5 PWAKEUP | the stress slave waits for it | a Completer may wait for PWAKEUP before PREADY (IHI 0024E 3.7.2); a requester that never raises it during a transfer hangs that transfer (HANG). A drop between PSEL and PREADY is only seen if PWAKEUP is still low when the slave's response is ready |
| model: AXI5-Lite data width | 32 or 64 | AXI5-Lite allows wider, but POISON is one bit per 64 data bits and the cores poison per beat: the shells hold DW to the widths where those agree (elaboration check) |
| model: AXI4-Lite transfers in flight per direction | `DEPTH` (16) | the master's issued-ID FIFO; a full FIFO holds the next address. Responses must return in issue order (AXI4-Lite has no ID). A read returned out of order is paired with the wrong burst and fails RD_DATA (the data are a function of the address). B carries no data, so two writes whose B's swap are caught only when their responses differ (RD/WR_RESP, the error window): a swap of two OKAYs is invisible |

Every check is shown to fire by the pair test's fault injector
(`val/amba/test_axi_stress_pair.py`), and an independent Python monitor
checks the blocks themselves against the model.

## 4. Builds

| Build | DUT | Status |
|---|---|---|
| `build-axi4` | `bridge_bs_axi4`: 4 AXI4 masters (64/128/32/64, IDs 8/4/6/8, one cdc) x 4 AXI4 slaves (64/128/32/64, one cdc), a 256 MB hole | WNS +0.081 ns at 100 / 75 MHz, 94.8k LUTs (47%), no BRAM/DSP; sim and board: every profile passes under the path limits |
| `build-axi3` | `bridge_bs_axi3`: the same shape with AXI3 on every port that does not cross a clock (cpu, dma, io; mem0, mem1, mem2). The two CDC ports (acc, mem3) stay AXI4: the generator has no AXI3 CDC (`validate_axi3`, rule 3). Paths: AXI3 -> AXI3, AXI3 -> AXI4, and AXI4 -> AXI3 with bursts longer than 16 beats chopped | WNS +0.001 ns, WHS +0.013 ns at 100 / 75 MHz, 106.7k LUTs (52%); sim and board: every profile passes under the path limits |

| `build-xil` | `bridge_bs_xil`: stress masters cpu (64b) and dma (128b, cdc), the AXI Traffic Generator (64b, ID 2) and AXI Central DMA (64b, no ID); stress slaves mem0 (64b) and mem1 (32b, cdc), LiteDRAM DDR3 (128b, 1 GB at 0x4000_0000; it replaced MIG 7-series, below) and the AXI BRAM controller (64b, 64 KB at 0x2000_0000). The vendor masters reach only the memories. `[harness] vendor` in the TOML makes the generator bring those ports out as pins; the configuration bridge's ext0 / ext1 AXI4-Lite windows carry the host to the traffic generator and DMA registers | board-green with LiteDRAM and Ocelus: the DUT is the bridge's monitored variant (`bridge_bs_xil_mon`, an Ocelus monitor on every port; mem1 monitored on its own clock through `bridge_mon_cdc`), its cfg regblock and 32-bit error drain on the configuration bridge's ext2 / ext3, and the host reports every record per run (`bin/bstress_ocelus.py`). WNS +0.089 ns, WHS +0.045 ns, ~124k LUTs (61%). The DMA register slave is on ext1 directly (bridge BUG-020 fixed); the BRAM controller is dual-port (a DMA copy inside a single-port one deadlocks). Earlier, the MIG build with mig excluded: 27/27 and a 94/94 soak |
| `build-xmix` | `bridge_bs_xmix`: AXI3, AXI4 and AXI5 together with the third-party IP -- stress masters cpu (AXI5, 64b, nsaid / trace / mpam / mecid / unique), io (AXI3, 64b) and acc (AXI4, 32b, cdc), the traffic generator and the DMA; stress slaves mem0 (AXI5), mem1 (AXI3) and mem2 (AXI4, 32b, cdc), LiteDRAM DDR3 (AXI4, 128b) and the BRAM controller on an AXI3 port: AMD's AXI Protocol Converter (AXI3 in, AXI4 out) in front of it and an AXI Protocol Checker in AXI3 mode on the bridge's link. build-xil's board top with `BS_XMIX` | board-green: every profile x seeds 1-3 30/30; WNS +0.028 ns, WHS +0.007 ns. Its first runs found converters BUG-013 (AXI3 slave + W-first) and bridge BUG-022 (multi-driven sideband), and two host gaps in the fill / read sweep (below) |
| `build-axi5` | `bridge_bs_axi5`: AXI5 on every port that does not cross a clock (cpu 64b, dma 128b, io 32b; mem0 64b, mem1 128b, mem2 64b), all with NSAID / TRACE / MPAM / MECID; the CDC ports (acc, mem3) stay AXI4. Poison on a 64-bit clique (cpu -> mem0, mem2): the validator allows it only where every connected path is AXI5 at both ends and one width. mem1 takes native (dma), width-converted (io: sideband dropped) and AXI4 (acc) requests at once and tells them apart by the fabric's master index | with IDUNQ on every AXI5 port and atomics and MTE on the 128-bit cpu clique (cpu IDs 4): WNS +0.020 ns, WHS +0.004 ns at 100 / 75 MHz, 94.3k LUTs (46%); sim 9/9 (with a pin-level count that atomics, IDUNQ, poison and every tag operation really ran), board 27/27, soak 172/172 |

## 5. Phases

| Phase | Adds | Shells |
|---|---|---|
| 1 | the cores, AXI4, the Genesys 2 build | `axi4_{master,slave}_stress` |
| 2a (done) | AXI3 ports, `build-axi3` | `axi3_{master,slave}_stress` (WID, 16-beat, 2-bit lock) |
| 2b (sideband + poison) | AXI5 ports in a mixed DUT, `build-axi5` | `axi5_{master,slave}_stress`: NSAID, TRACE, MPAM, MECID, POISON |
| 2c (done) | IDUNQ, atomics | the same shells; see bridge TASK-019 |
| 2d (done) | MTE | the same shells |
| 2e (done) | `build-xil`, `build-xmix`: third-party IP on the bridge -- real memories (mem windows, fill / read sweeps) and vendor masters | the AXI4 shells; LiteDRAM, BRAM controller, traffic generator, DMA, protocol checkers |
| 3 | AXI4-Lite / AXI5-Lite, APB4 / APB5, WB4 | single-beat shells; slaves in offset mode where the bridge hands them a window offset. AXI4-Lite, AXI5-Lite, APB4 and APB5 shells done 2026-10-23 (`axil{4,5}_*_stress`, `apb{4,5}_*_stress`, pair test cells); WB4 next |

## 6. Findings

| ID | Where | Finding |
|---|---|---|
| bridge BUG-018 (fixed) | DUT | width-converted paths emitted illegal AXI for FIXED, WRAP, narrow and unaligned bursts -- in sim and on the board. Fixed: the dwidth converters take every legal burst (PACK / PASS / EXPAND per burst; downsize FIXED / WRAP is correct but slow), and the framework BFMs walk bursts by AXI A3.4.1 (RDS-DV 1.2.9). The host's `bstress.path_caps` limit is gone and `--full-axi` is a no-op; board 150/150 with no limits |
| converters BUG-010 | shared CSR path | `peakrdl_to_cmdrsp` hands the regblock every access twice: a singlepulse is two cycles. Through a toggle synchronizer that lost the cclk domain's GO; the harness edge-detects GO / STOP |
| (fixed here) | stress master | `32'(now - stamp)` on 16-bit stamps saturated LAT_SUM in Vivado, not in Verilator; the latency is a 16-bit wire now |
| converters BUG-011 (fixed) | DUT, AXI3 slave adapters | `axi4_to_axi3` chopped an unaligned INCR longer than 16 beats into chunks that all stayed unaligned (AXI: every beat after the first is aligned), so the AXI3 slave took the first beat of each later chunk for a partial one. `S_WSTRB` in sim and on the board (0/4 runs on the pre-fix bitstream); the chunk address is aligned now, with regressions in the converter suite |
| (fixed here) | build flow | `make lint` never passed `BS_HARNESS`, so every build linted the AXI4 harness; the build Makefiles set `LINT_DEFINES` |
| (limit) | bridge generator | no AXI3 port may be a CDC port (v1); `build-axi3` keeps its CDC ports AXI4 |
| (limit) | bridge generator | no AXI5 port may be a CDC port (the crossing carries the AXI4 set); `build-axi5` keeps its CDC ports AXI4 |
| (by design) | DUT, AXI5 master ports | a trace-capable master port echoes AxTRACE on BTRACE / RTRACE itself, whatever the slave (bridge BUG-010), and asserts in sim that a trace-capable slave echoes it too. The stress model's first slave returned an address hash and hit that assertion; it echoes now |
| bridge BUG-020 (fixed) | DUT, every crossbar | the W route of a write is pushed only when the slave port accepts its AW, so a slave that waits for WVALID before AWREADY (legal, AXI A3.3.1) deadlocks the bridge. Found on the board by the AXI CDMA register slave: its first register write never got a B and the configuration bridge stayed wedged. No stress slave or slave BFM waited that way, so no earlier sim or build could see it. Fixed (owner bypass in `bridge_cdc_slave_arb`; `axi4_to_axil4_wr` registers every AW); the stress slaves' `W_FIRST` mode and the `w_first` profile gate it; board 20/20 with the CDMA on ext1 directly |
| converters BUG-012 (fixed) | DUT, every downsizing write path | a write split into several master bursts lost its B when the slave answered its first part before its final AW issued: the converter pushed the burst's B-CAM entry at the final AW, and only that AW waited for a slot, so with the CAM full the first part's B matched nothing and was dropped. Found on the board as one cpu write into mem1 (64 -> 32, cdc) never completing, about once in 50 `narrow` runs; Ocelus named the port, ID and address, and that no slave held it. Fixed (entry pushed at the first AW with the part count); unit test `..._early_b` fails before, passes after; board `narrow` 300/300 |
| converters BUG-013 (fixed) | DUT, every AXI3 slave port | `axi4_to_axi3_wr` queued an unchopped write's W descriptor only at the AXI3 port's AW handshake, so a slave that waits for WVALID before AWREADY deadlocked it -- bridge BUG-020's class, in a converter. Found by build-xmix `w_first` (its AXI3 mem1); reproduced in the build-axi3 harness sim. Fixed: the descriptor is queued when the AW is offered |
| bridge BUG-022 (fixed) | DUT, AXI5-sideband fabrics | on a rate-buffered width-converted path the sideband ties and the rate buffer both drove the output struct (Vivado Synth 8-6859 on every build-xmix master adapter; the FPGA lint waives MULTIDRIVEN). Fixed: ties on the buffer's input |
| (host) | fill / read sweep | an AXI3 master's sweep was sized for 256-beat bursts, which AXI3 cannot carry (its shell's LEN_MASK is 16 beats): it covered 1/16 of the memory and the rest read back erased (`sweep_bursts`). And an AXI5 trace master's sweep expected no trace echo, but the bridge echoes the request's trace on every path (bridge BUG-010) |
| bridge BUG-021 (fixed) | DUT, every `_mon` variant | each port's monitor kept the wrapper's 8-entry table while the port runs 16 deep, so any port past 8 outstanding reported false ORPHAN errors (Ocelus's first board run, a `clean` one). Fixed: MAX_TRANSACTIONS = the port's max_outstanding |
| (vendor IP) | MIG 7-series on this board | DDR3 calibrates, then within ~35 us of a write sweep MIG's own controller raises `app_rd_data_valid` with no read issued anywhere and holds `app_rdy` low for good; every hang and the checker's "RVALID with no AR" follow (ILA, `reports/ila/bridge_bs_xil_mig_spurious_rd_data_valid.csv`). The fabric benchmark saw the same family on this board and moved to LiteDRAM; so does build-xil (owner decision 2026-10-20). Not a bridge defect |
| (vendor IP) | AXI CDMA | writing CDMACR.Reset resets its register slave with that write still open: its B never comes, and an AXI host waiting for it hangs. The host never soft-resets it |
| (vendor IP) | AXI Traffic Generator | with one ARID outstanding to two slaves at once (DDR and BRAM) its read list never finishes: no error, MSTDONE never sets, the bus idle. A protocol checker on its own link (bs_pc_atg) passes every response the bridge gave it, so the bridge is not at fault; its read-completion pointer advances only on a one-cycle completion vector (the `| vec_ff` term is commented out in the shipped source). The host keeps each memory on its own read IDs |
| (host) | AXI Traffic Generator | a command's master-RAM index (PG125 CMDRAM bits 76:64) is a BYTE address into the 8 KB master RAM; read as a beat index it pointed every command at the wrong data, and the read sweep after the run caught the zeros it wrote |
| (vendor IP) | AXI Protocol Checker | flags AXI_ERRM_WDATA_NUM and AXI_ERRM_WSTRB whenever a slave takes W before its AW (allowed by AXI; its source says it cannot check strobes for write data before address): the single-port BRAM link, and LiteDRAM on every fill (ILA, 2026-10-20: 256 correct beats, W 60 cycles ahead of the AW handshake). The host logs these two instead of failing; the sim judges them with the framework checker on the same links |
| bridge BUG-019 (fixed) | DUT, several converters | unaligned INCR bursts kept their start misalignment past the first beat in the dwidth downsize, `axi4_to_axil4` (and AXI5-Lite / WB4) and `axi_gen_addr` (APB) paths; `axi4_to_axi3` was fixed as converters BUG-011. Fixed: every converter steps INCR from the aligned start, and the downsize does start-lane accounting |
| bridge BUG-023 (fixed) | DUT, every crossbar | a path's W destination FIFO was sized to the master's outstanding limit and had no full check, but a width converter issues several AWs per master burst (one per beat for a wide FIXED / WRAP after BUG-018), so the 17th entry sent W beats to the wrong slave. Found on the board as a `bursts` hang plus S_WDATA errors on build-axi4, right after the BUG-018 fix. Fixed: the FIFO's full flag gates the AW |
| bridge BUG-024 (fixed) | DUT, crossbars with CDC slaves | crossed-W deadlock: a master's AW to a CDC (lane) slave and a later AW to a slot slave could be ordered one way in the master's W stream and the other way at a slave, so each slave waited on the other's W. Found on the board as a `reorder` hang on build-axi4. Fixed: while a master has W live toward a lane slave, its AWs to every other slave wait |

## 7. Board results

| Run | Result | Data |
|---|---|---|
| every profile x seeds 1-3, 4000 bursts per master direction | 27/27 PASS; 0.34-19.2 ms per run | `reports/board/bridge_bs_axi4_20261019_102024.csv` |
| `bursts`, `narrow` with `--full-axi` | FAIL as BUG-018 predicts; no hang | `reports/board/bridge_bs_axi4_20261019_102327.csv` |
| latency-fix bitstream: every profile x seeds 11-12, 4000 bursts | 18/18 PASS; chaos latency mean 2338 / max 19689 cycles | `reports/board/bridge_bs_axi4_20261019_103727.csv` |
| soak: chaos, a fresh seed per run, 8000 bursts per master direction, 15 min | 166/166 PASS (~10.6 M bursts) | `reports/board/bridge_bs_axi4_20261019_103942.csv` |
| AXI3, pre-fix bitstream (BUG-011): `clean`, `bursts`, seeds 1-2 | 0/4 PASS: `S_WSTRB` on the AXI3 slaves, every error from the AXI4 master's chopped writes | `reports/board/bridge_bs_axi3_20261019_135031.csv` |
| AXI3: every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi3_20261019_140649.csv` |
| AXI3 soak: chaos, a fresh seed per run, 8000 bursts per master direction, 15 min | 168/168 PASS (~10.7 M bursts) | `reports/board/bridge_bs_axi3_20261019_140943.csv` |
| AXI5: every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi5_20261019_181755.csv` |
| AXI5 soak: chaos, a fresh seed per run, 8000 bursts per master direction, 15 min | 174/174 PASS (~11.1 M bursts) | `reports/board/bridge_bs_axi5_20261019_182057.csv` |
| AXI5 + IDUNQ + atomics: every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi5_20261019_214752.csv` |
| AXI5 + IDUNQ + atomics soak: chaos, fresh seeds, 8000 bursts, 15 min | 172/172 PASS (~11.0 M bursts) | `reports/board/bridge_bs_axi5_20261019_215052.csv` |
| AXI5 + MTE (128-bit full clique): every profile x seeds 1-3, 4000 bursts | 27/27 PASS | `reports/board/bridge_bs_axi5_20261019_235603.csv` |
| AXI5 + MTE soak: chaos, fresh seeds, 8000 bursts, 15 min | 172/172 PASS (~11.0 M bursts) | `reports/board/bridge_bs_axi5_20261019_235905.csv` |
| build-xil (MIG bitstream), mig excluded: every profile x seeds 1-3, 4000 bursts; per run the traffic generator loops 8 + 8 commands on BRAM and checks its reads, the DMA copies, the read sweep checks all 64 KB | 27/27 PASS | `reports/board/bridge_bs_xil_20261020_064133.csv` |
| build-xil soak (MIG bitstream), mig excluded: chaos, fresh seeds, 8000 bursts, 15 min | 94/94 PASS; 188 DMA copies | `reports/board/bridge_bs_xil_20261020_064611.csv` |
| build-xil, LiteDRAM, before converters BUG-012: `narrow`, 4000 bursts | hung about once in 50 runs (26/27, 39/40, 57/58, 50/51): one cpu write into mem1 never completed; Ocelus: `cpu.wr AXI_TIMEOUT_RESP id=0x32 addr=0x1617b9b8` | `reports/board/bridge_bs_xil_20261020_150531.csv` |
| build-xil, LiteDRAM + Ocelus, converters BUG-012 fixed: `narrow` seeds 1001-1300, 4000 bursts | 300/300 PASS, zero Ocelus records | `reports/board/bridge_bs_xil_20261020_162240.csv` |
| build-xil, LiteDRAM + Ocelus: `w_first` seeds 1-20 (bridge BUG-020 gate, CDMA on ext1 directly) | 20/20 PASS | `reports/board/bridge_bs_xil_20261020_171410.csv` |
| build-xil, LiteDRAM + Ocelus: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_xil_20261020_171812.csv` |
| build-xmix (AXI3 / AXI4 / AXI5 + third-party IP), before converters BUG-013: every profile x seeds 1-3 | 27/28: `w_first` hung at once | `reports/board/bridge_bs_xmix_20261020_195840.csv` |
| build-xmix, converters BUG-013 fixed: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_xmix_20261020_210344.csv` |
| build-axi4, bridge BUG-018/019/023/024 fixed, no path limits: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_axi4_20261022_002825.csv` |
| build-axi3, bridge BUG-018/019/023/024 fixed, no path limits: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_axi3_20261022_003122.csv` |
| build-axi5, bridge BUG-018/019/023/024 fixed, no path limits: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_axi5_20261022_003411.csv` |
| build-xil, bridge BUG-018/019/023/024 fixed, no path limits: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_xil_20261022_003706.csv` |
| build-xmix, bridge BUG-018/019/023/024 fixed, no path limits: every profile x seeds 1-3, 4000 bursts | 30/30 PASS | `reports/board/bridge_bs_xmix_20261022_004216.csv` |
| build-axi4, large run: every profile x seeds 1-3, 20000 bursts per master direction | 30/30 PASS; 4.8 M bursts, 1.27 s of board time | `reports/board/bridge_bs_axi4_20261022_093552.csv` (per-port MB/s, latency and outstanding in the `.json`) |
| build-axi3, large run: every profile x seeds 1-3, 20000 bursts per master direction | 30/30 PASS; 4.8 M bursts, 0.74 s | `reports/board/bridge_bs_axi3_20261022_093846.csv` (per-port MB/s, latency and outstanding in the `.json`) |
| build-axi5, large run: every profile x seeds 1-3, 20000 bursts per master direction | 30/30 PASS; 4.8 M bursts, 1.19 s | `reports/board/bridge_bs_axi5_20261022_095510.csv` (per-port MB/s, latency and outstanding in the `.json`) |
| build-xil, large run: every profile x seeds 1-3, 20000 bursts per master direction | 30/30 PASS; 2.4 M bursts, 1.20 s | `reports/board/bridge_bs_xil_20261022_094222.csv` (per-port MB/s, latency and outstanding in the `.json`) |
| build-xmix, large run: every profile x seeds 1-3, 20000 bursts per master direction | 30/30 PASS; 3.6 M bursts, 0.77 s | `reports/board/bridge_bs_xmix_20261022_094737.csv` (per-port MB/s, latency and outstanding in the `.json`) |
| build-axi4, large run, 32-bit latency: every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 89,029 cycles (backpressure, dma rd) | `reports/board/bridge_bs_axi4_20261022_124511.csv` |
| build-axi3, large run, 32-bit latency: every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 34,860 cycles | `reports/board/bridge_bs_axi3_20261022_124814.csv` |
| build-axi5, large run, 32-bit latency: every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 87,499 cycles (backpressure, dma rd) | `reports/board/bridge_bs_axi5_20261022_125132.csv` |
| build-xil, large run, 32-bit latency: every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 17,907 cycles | `reports/board/bridge_bs_xil_20261022_125438.csv` |
| build-xmix, large run, 32-bit latency: every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 20,623 cycles | `reports/board/bridge_bs_xmix_20261022_130936.csv` |
| build-axi4, rebuilt with the `bridge_id_remap` timing fix (bridge f02b67aef): every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 64,981 cycles; routed WNS +0.001 ns | `reports/board/bridge_bs_axi4_20261022_215324.csv` |
| build-axi3, rebuilt with the `bridge_id_remap` timing fix (bridge f02b67aef): every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 35,871 cycles; routed WNS +0.010 ns | `reports/board/bridge_bs_axi3_20261022_215615.csv` |
| build-axi5, rebuilt with the `bridge_id_remap` timing fix (bridge f02b67aef): every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 80,096 cycles; routed WNS +0.011 ns | `reports/board/bridge_bs_axi5_20261022_215906.csv` |
| build-xil, rebuilt with the `bridge_id_remap` timing fix (bridge f02b67aef): every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 15,866 cycles; routed WNS +0.050 ns | `reports/board/bridge_bs_xil_20261022_220154.csv` |
| build-xmix, rebuilt with the `bridge_id_remap` timing fix (bridge f02b67aef): every profile x seeds 1-3, 20000 bursts | 30/30 PASS; max latency 20,337 cycles; routed WNS +0.086 ns | `reports/board/bridge_bs_xmix_20261022_220719.csv` |

## 8. Running

The long runs belong on the board: one build's every profile x 3 seeds at
20000 bursts takes about 1 s of board time. The same coverage in simulation
takes hours (10 profiles x 400 bursts: 2.5 h per DUT), so the sim levels stay
short (40 / 200 / 1000 bursts) and check behaviour; volume comes from
`run_stress.py --txns`.

Latency figures are issue-to-retire cycles, modulo 2^32 (43 s at 100 MHz):
the stress master's stamps, `LAT_MAX` and the saturating `LAT_SUM` are all 32
bits (`axi_stress_mst_{rd,wr}`). Its hang check is master-wide idle, not
per-burst age, so one slow burst does not trip it; the width is what bounds the
reading. The stamps were 16 bits until 2026-10-22, and a burst slower than
65,535 cycles then read wrapped -- the morning's large runs (rows above marked
"large run" without "32-bit latency") carry that limit. With 32 bits,
`backpressure`'s `dma` reads on build-axi4 and build-axi5 measured
57-89k cycles (five of six runs over 2^16); every other maximum on every build
stayed below 43k. `val/amba/test_axi_stress_pair.py` `long_lat` holds a B for
70,000 cycles and checks the reading.

```
bin/regen.sh                                   # bridges, regblocks, harness
cd dv/tests && make run-all-gate-parallel      # sim: the board's host code over the sim UART
cd build-axi4 && make bitstream && make program   # or build-axi3
python3 bin/run_stress.py                      # every profile, 3 seeds (--build axi3 for build-axi3)
python3 bin/run_stress.py --soak 3600          # chaos, a fresh seed per run, one hour
```
