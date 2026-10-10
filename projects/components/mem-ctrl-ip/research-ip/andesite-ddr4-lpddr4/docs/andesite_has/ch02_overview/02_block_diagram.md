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

# Block Diagram

## The whole controller, marked against scoria

Read this figure first. The colour of each block tells you the size of this
project: green blocks are scoria's, used as-is; amber blocks change in named,
bounded ways; red blocks are new. One grey block is carried dormant — present
in the RTL, unexercised at this design point, with the waking condition named
in Chapter 3.1.

### Figure 2.1: andesite block diagram, with inheritance marking

```mermaid
flowchart TB
    HOST_AXI["andesite_axi4_layer<br/>INHERITED"] --> HOST_CHOP["axi_burst_chopper<br/>INHERITED"]
    HOST_CHOP --> HOST_RIN["rd_intake<br/>INHERITED"]
    HOST_CHOP --> HOST_WIN["wr_intake<br/>INHERITED"]
    HOST_WIN --> HOST_WSPLIT["wr_splitter<br/>INHERITED"]
    HOST_RIN --> SCHED
    HOST_WSPLIT --> SCHED

    subgraph SCHED["Scheduler"]
        direction TB
        SCHED_CORE["scheduler_layer<br/>MODIFIED — maintenance + L/S admission"]
        SCHED_ARB["cmd_arbiter<br/>MODIFIED — tCCD_L/S aware"]
        SCHED_PP["page_policy<br/>INHERITED"]
        SCHED_RDCAM["rd_cmd_cam<br/>INHERITED"]
        SCHED_WRCAM["wr_data_cam<br/>INHERITED"]
        SCHED_BT["bank_timer / bank_timers<br/>INHERITED"]
        SCHED_GT["global_timers<br/>MODIFIED — tRRD_L/S, tCCD_L/S"]
        SCHED_AM["addr_mapper<br/>MODIFIED — bank-group decode"]
        SCHED_CORE --> SCHED_ARB
        SCHED_CORE --> SCHED_BT
        SCHED_CORE --> SCHED_GT
        SCHED_AM --> SCHED_CORE
        SCHED_ARB --> SCHED_PP
        SCHED_ARB --> SCHED_RDCAM
        SCHED_ARB --> SCHED_WRCAM
    end

    subgraph MAINT["Maintenance"]
        direction TB
        MAINT_REF["refresh_ctrl<br/>MODIFIED — FGR 1x/2x/4x"]
        MAINT_ZQ["zq_ctrl<br/>INHERITED — NEW submodule: LPDDR4 MPC path"]
        MAINT_ODT["odt_ctrl<br/>NEW — RTT_NOM/WR/PARK"]
    end
    SCHED --> MAINT

    subgraph INITTR["Init and training"]
        direction TB
        INIT_SEQ["init_sequencer<br/>MODIFIED — RESET#, gear-down, parity enable"]
        INIT_MR["mode_register<br/>MODIFIED — MR0-MR6"]
        INIT_WRLVL["wrlvl_ifc<br/>MODIFIED — interface only, no search loop"]
        INIT_RDLVL["rdlvl_ifc<br/>NEW — MPR read leveling, no search loop"]
        INIT_CA["ca_train_ifc<br/>NEW — LPDDR4 CA/WDQ training"]
    end
    INIT_SEQ --> SCHED
    INIT_MR --> INIT_SEQ

    subgraph DFI["DFI v4.0 layer"]
        direction TB
        DFI_PATH["dfi_cmd_path<br/>MODIFIED — ACT_n, BG, parity wires"]
        DFI_FMT["dfi_cmd_formatter<br/>MODIFIED — NEW submodule: LPDDR4 CA path"]
        DFI_RDA["dfi_rd_aligner<br/>MODIFIED — DBI read path"]
        DFI_WRS["dfi_wr_serializer<br/>MODIFIED — DBI write path"]
        DFI_CDC["dfi_cdc<br/>INHERITED"]
        DFI_PACK["dfi_signal_pack<br/>carried dormant"]
        DFI_HIST["cmd_history_checker<br/>INHERITED — DDR4 spacing set"]
    end
    SCHED --> DFI_FMT
    MAINT --> DFI_PATH
    DFI_FMT --> DFI_PATH
    DFI_PATH --> DFI_RDA
    DFI_PATH --> DFI_WRS

    CSR["CSR block (PeakRDL)<br/>flow INHERITED — contents grow"] -.-> SCHED
    CSR -.-> MAINT
    CSR -.-> INITTR
    CSR -.-> DFI

    classDef inh fill:#228B22,color:#FFFFFF,stroke:#145214;
    classDef mod fill:#E6A817,color:#000000,stroke:#8a650f;
    classDef new fill:#C62828,color:#FFFFFF,stroke:#7a1414;
    classDef dorm fill:#808080,color:#FFFFFF,stroke:#4d4d4d,stroke-dasharray:5 5;

    class HOST_AXI,HOST_CHOP,HOST_RIN,HOST_WIN,HOST_WSPLIT,SCHED_PP,SCHED_RDCAM,SCHED_WRCAM,SCHED_BT,DFI_CDC,DFI_HIST,MAINT_ZQ inh;
    class SCHED_CORE,SCHED_ARB,SCHED_GT,SCHED_AM,MAINT_REF,INIT_SEQ,INIT_MR,INIT_WRLVL,DFI_PATH,DFI_FMT,DFI_RDA,DFI_WRS mod;
    class MAINT_ODT,INIT_RDLVL,INIT_CA new;
    class DFI_PACK dorm;
```

: Figure 2.1: andesite DDR4/LPDDR4, inherited (green), modified (amber), new (red), dormant (grey)

**Source:** [01_block_diagram.mmd](../assets/mermaid/01_block_diagram.mmd) — the fence above
and the `.mmd` file carry the same source; the doc pipeline renders it to PNG
at build time. The layout is split into host, scheduler, maintenance, init and
training, and DFI subgraphs rather than drawn wide.

## Reading the figure

**The front end is entirely green.** The AXI4 interface — read and write
intakes, the write-data CAM's front side, the burst chopper, the FSM-free
split/aggregate — is untouched by the move to DDR4. Nothing about DDR4 or
LPDDR4 reaches the host side.

**The scheduler is green in structure, amber at the edges.** The FR-FCFS
arbiter mechanism, the per-(rank,bank) bank timers and the page policy are
inherited. What turns amber is bank-group awareness: the address mapper grows
the BG decode, the arbiter and the global timers learn the long/short pairs,
and the scheduler keeps admitting maintenance traffic the way scoria's does —
request/grant, never preempt (family doctrine 2).

**Important:** one inherited detail must be inherited *including its fix*.
scoria's `global_timers` inherited pumice's next-state-function fix (pumice
ISSUE-018: readiness flags published one cycle late, which permitted tCCD and
tRTW violations). andesite inherits the fixed form the same way; a fresh
implementation of the same block from the same description would reintroduce
the bug.

**The amber maintenance block is refresh, for FGR.** `refresh_ctrl` turns
amber because DDR4's fine-granularity refresh (1x/2x/4x, selected in MR3)
adds a density dimension on top of the mechanism scoria landed with TASK-001
(elastic refresh, TCR, ZQCS placement — the policy base andesite keeps, Ch
3.4). `zq_ctrl` stays green for DDR4 — DDR4 keeps `ZQCS`/`ZQCL` exactly as
scoria issues them — with a red submodule for LPDDR4, whose calibration rides
the MPC command.

**The red blocks are three, and all three are bounded.** `odt_ctrl` is new
because dynamic ODT has no scoria counterpart. `rdlvl_ifc` and
`ca_train_ifc` are new because read leveling and LPDDR4 CA/WDQ training have
none. All three are interfaces with telemetry; none contains a search loop.

**The grey block is `dfi_signal_pack`, carried dormant.** The pack stage
stays a registered pipeline; its DFI 4.0 frequency-ratio variants go
unexercised at this design point. The waking conditions for it and
`powerdown_ctrl` are named in Chapter 3.1.

## What the figure deliberately omits

The PHY, because DFI is the boundary. Any training-search state machine,
because the searches live in firmware per the D2 precedent. The DDR5-oriented
signals of DFI v4.x, because andesite does not implement them. Each absence
is named somewhere in this book so it reads as a decision rather than an
oversight.
