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

# Relationship to Nexus (IEEE-ISTO 5001)

The references chapter already names the Nexus 5001 Forum standard (the
2003 Version 2.0 text, local PDF
`rtl/amba/references/DebugTraceInterfaceStandard__IeeeIsto2003.pdf`). This
chapter is that reference expanded: why the comparison keeps coming up, where the
correspondence is real, and where the two systems split.

Nexus standardizes how an embedded processor reports its own activity to an
external debug tool: typed messages (each led by a 6-bit TCODE), per-source
IDs, optional timestamps, and program / data / ownership trace, streamed
off-chip through a dedicated auxiliary port while the core runs. Ocelus looks
similar from a distance -- typed packets, per-source identity, timestamps --
and the correspondence is real enough that four of the six integrator axes
in this paper have direct Nexus counterparts:

| Nexus mechanism | Ocelus counterpart | Chapter |
|---|---|---|
| Source IDs in each message | Identity space allocation | [4](04_identity_space_allocation.md) |
| TSTAMP field per message | Timestamp policy | [6](06_timestamp_policy.md) |
| Message typing (6-bit TCODE) | Packet-type field, filtered per type at the group | [8](08_packet_type_filtering.md) |
| AUX trace port (MDO/MSEO pins) | Drain path: error FIFO and memory ring | [7](07_drain_path_selection.md) |

That is why the comparison keeps coming up. The split is everything the table
leaves out.

**Nexus answers "what happened?" Ocelus answers "is something wrong right
now?"** Nexus is observability: enough state leaves the chip to reconstruct
processor behavior after the fact. Ocelus is operational monitoring: it
reports condition crossings on live AMBA traffic and hands them to software
through the drains. A flight recorder versus a smoke alarm.

Three structural differences follow:

1. **Consumer location.** Nexus streams to an external debugger over the AUX
   port; every message is target-to-tool. Ocelus packets terminate on-chip --
   the error FIFO the host reads over AXI-Lite behind an interrupt, and the
   memory ring the group fills with AXI bursts. (The planned HIVE policy tier
   reads the same drains.)
2. **Information policy.** Nexus pays pins, serialization logic, and external
   capture hardware to stream continuously. Ocelus emits edge-triggered
   packets only, which is what makes the Revision 1.1 posture affordable:
   lite monitor on every port, full monitor only where justified
   ([chapter 10](10_what_it_costs.md)).
3. **Loop closure.** Nexus is open loop: data leaves and nothing in the system
   changes. Ocelus exists to close one: detect on the fabric, drain, and let
   software escalate.

**The watchpoint distinction.** The crispest single-sentence version: what
Nexus uses as a filter, Ocelus uses as the output. In Nexus, a watchpoint
does not halt the core -- it emits a message to external tools and, in Class
4 implementations, gates the start of program and data trace. The watchpoint
exists to control what gets traced. In Ocelus, the condition crossing is the
product: the monitor raises a packet, the group filters it, the drain carries
it. There is no trace stream for it to gate.

**Placement.** Nexus instruments the processor core; Ocelus instruments the
bus. That is the insertion-point axis ([chapter 5](05_where_to_insert_monitoring.md)),
and it is why the two are complements, not competitors: on an SoC running
RISC-V, the cores can speak N-Trace (a strict subset of IEEE-5001 Nexus
messaging) while Ocelus covers the fabric around them. Nexus-family trace
watches the processors; Ocelus watches the system they run on.

**Version note.** The repository holds the 2003 Version 2.0 text cited in
chapter 1. IEEE-ISTO 5001-2012 is the later revision, and the Nexus 5001
Forum dissolved in September 2020 with the standard left openly available --
none of which changes the comparison, since the mechanisms above are common
to both revisions.
