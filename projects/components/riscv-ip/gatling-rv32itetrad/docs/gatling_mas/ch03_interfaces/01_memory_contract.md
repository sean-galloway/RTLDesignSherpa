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


# Internal Interfaces

## The memory contract: one stage of latency, no wait

Every memory the barrel touches answers exactly one stage after it is asked:

| Memory | Request | Data | Provided by |
|---|---|---|---|
| Instruction | F | D | `gatling_mem_bram` port A |
| Register file | D | X | `gatling_regfile` |
| Data (load) | X | W | `gatling_mem_bram` port B |

: Table 3.1: Request and data stages

This is why gatling has no `mem_wait`. kestrel, single-cycle, has to stall a cycle on every block-RAM load; the barrel's stages are exactly the block RAM's latency, so nothing waits. A memory system for gatling must keep this contract on both ports, which `gatling_mem_bram` does by registering both reads and by giving the core port B unconditionally.

## Run and halt between core and memory system

`gatling_mem_bram` drives `hart_run` from CTRL; the core reports `halted` and `halt_cause` per context, and the memory system latches them into STATUS. The core's own halt state clears while a context is held; the memory system's STATUS keeps the verdict until the next run, so the host can read it after stopping the context.
