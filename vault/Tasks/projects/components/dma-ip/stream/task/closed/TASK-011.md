# TASK-011: Configurable decompression in `monbus_tally_axil` (LOW priority, future)
> **Was an UN-IDed heading in `closed.md` until 2026-09-24** — it carried no task number at all, so nothing could cite it and the checker could not see it. Given an ID by this migration.

**Priority:** low. Nothing is blocked on it — the compression format is already
verifiable without it (see "not blocked" below).

**What:** let the tally ingest the COMPRESSED monbus stream, not just RAW
3-beat records, selected at runtime.

**Why it does not exist today:** the tally reconstructs each 128-bit packet with
a mod-3 counter over the ingest write stream:

```
beat0 = {tag[3:0]=0, source_ts[59:0]}
beat1 = packet[127:64]
beat2 = packet[63:0]
```

That layout only holds for `USE_COMPRESSION == 0`. With compression on, the
beats are Tier-0/Tier-1 slots and the mod-3 reassembly produces garbage — which
is why `OBS_CTRL.COMPRESS_EN` carries the warning "leave 0 unless the consumer
decompresses". The tally is that consumer, and it cannot.

**What the decoder has to do** (README_COMPRESSION_DATASET.md 2.5, "Decoder
mirror"): reconstruct CAM state from the slot stream alone, with no
out-of-band information. Tier-0 escapes install templates; Tier-1 hits
reconstruct `(key, event_data)` from `CAM[idx]` plus the slot fields, and must
touch the CAM in exactly the same order the encoder did. So this is a stateful
CAM-maintaining decoder, not a beat reshuffle — the real work of the task.

**Not blocked on this** — deliberately. `comp_sram` (sdpram_slave_axil_axil,
`0x001A0000`, 64 KB) was added to the bridge so compressed traffic can be
written to an ORDINARY memory and read back by the host, then compared against
the bit-exact Python golden `bin/TBClasses/monbus/monbus_compressor.py`. That
verifies the format on silicon without any RTL decoder. The tally decoder is a
convenience (decode in hardware, tally directly) rather than a prerequisite.

**Acceptance:**

- A runtime bit selects RAW vs COMPRESSED ingest; RAW behaviour is bit-identical
  to today when it is clear.
- Decoding the dataset in `reports/compression_dataset/` reproduces the original
  records bit-exactly, matching the Python decoder (682 records, 32 templates,
  93.5% Tier-1 hit rate is the published bring-up target).
- A compressed run and a raw run of the same traffic produce the SAME tally bins.

**Related:** [[project_stream_mon_tally_coverage]]. Format spec + dataset:
`projects/NexysA7/stream_characterization/reports/compression_dataset/README_COMPRESSION_DATASET.md`.

---
