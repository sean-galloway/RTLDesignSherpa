"""monbus_sniffer.py — capture (packet, timestamp) records from a
live cocotb DUT for offline analysis with `monbus_compressor`.

Usage in a cocotb test:

    from TBClasses.monbus.sniffer import MonbusSniffer

    sniffer = MonbusSniffer(dut.monbus_valid, dut.monbus_ready,
                            dut.monbus_packet, dut.monbus_timestamp,
                            dut.axi_aclk)
    sniffer.start()
    # ... drive the test ...
    sniffer.stop()
    sniffer.dump_json("/tmp/capture.json")     # or
    sniffer.dump_csv ("/tmp/capture.csv")

The sniffer is a pure observer — it never drives anything. It records
every cycle where `valid && ready` are both asserted on the rising
edge of `clk`. Suitable for tapping the monbus_axil_group input port
(captures aggregated stream) or any per-wrapper monbus output (captures
single-source stream — useful for per-source isolation studies).

Capture format is a list of `(packet_int, timestamp_int)` tuples in
arrival order, directly consumable by `monbus_compressor.Encoder.encode()`.
"""

from __future__ import annotations

import json
import csv
import os
from typing import List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge


class MonbusSniffer:
    """Lightweight passive observer of a monbus interface."""

    def __init__(self,
                 valid_sig, ready_sig, packet_sig, timestamp_sig,
                 clk_sig,
                 label: str = "monbus"):
        """
        Args:
            valid_sig:     cocotb signal handle for monbus_valid
            ready_sig:     cocotb signal handle for monbus_ready
            packet_sig:    cocotb signal handle for monbus_packet (128 bits)
            timestamp_sig: cocotb signal handle for monbus_timestamp (64 bits)
            clk_sig:       cocotb signal handle for the clock the interface runs on
            label:         optional name for logging / file headers
        """
        self.valid_sig     = valid_sig
        self.ready_sig     = ready_sig
        self.packet_sig    = packet_sig
        self.timestamp_sig = timestamp_sig
        self.clk_sig       = clk_sig
        self.label         = label

        self.records: List[Tuple[int, int]] = []
        self._task: Optional[cocotb.Task] = None
        self._stop_flag: bool = False

    def start(self):
        """Begin sampling. Idempotent — safe to call once per test."""
        if self._task is not None:
            return
        self._stop_flag = False
        self._task = cocotb.start_soon(self._sample_loop())

    def stop(self):
        """Stop sampling. After this, the records list is final."""
        self._stop_flag = True

    @property
    def count(self) -> int:
        return len(self.records)

    async def _sample_loop(self):
        while not self._stop_flag:
            await RisingEdge(self.clk_sig)
            # Both valid and ready must resolve to int 1 — XZX states fail safe.
            try:
                v = int(self.valid_sig.value)
                r = int(self.ready_sig.value)
            except (ValueError, TypeError):
                continue
            if v == 1 and r == 1:
                try:
                    pkt = int(self.packet_sig.value)
                    ts  = int(self.timestamp_sig.value)
                except (ValueError, TypeError):
                    continue
                self.records.append((pkt, ts))

    # ----- dumpers --------------------------------------------------------

    def dump_json(self, path: str, extra_meta: Optional[dict] = None):
        """Write records to JSON. Records as hex strings to avoid truncation
        in tools that don't handle 128-bit ints natively.
        """
        meta = {
            "label": self.label,
            "schema_version": 1,
            "record_count": len(self.records),
        }
        if extra_meta:
            meta.update(extra_meta)
        out = {
            "meta": meta,
            "records": [
                {"packet": f"0x{pkt:032x}", "timestamp": f"0x{ts:016x}"}
                for pkt, ts in self.records
            ],
        }
        os.makedirs(os.path.dirname(os.path.abspath(path)) or ".", exist_ok=True)
        with open(path, "w") as f:
            json.dump(out, f, indent=2)

    def dump_csv(self, path: str):
        """Write records to a 2-column CSV (packet, timestamp), hex-encoded."""
        os.makedirs(os.path.dirname(os.path.abspath(path)) or ".", exist_ok=True)
        with open(path, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["packet_hex", "timestamp_hex"])
            for pkt, ts in self.records:
                w.writerow([f"0x{pkt:032x}", f"0x{ts:016x}"])


def load_capture(path: str) -> List[Tuple[int, int]]:
    """Load a capture file (JSON or CSV — autodetected from extension)
    back into the list-of-tuples form the encoder expects."""
    ext = os.path.splitext(path)[1].lower()
    if ext == ".json":
        with open(path) as f:
            doc = json.load(f)
        return [(int(r["packet"], 0), int(r["timestamp"], 0)) for r in doc["records"]]
    elif ext == ".csv":
        out = []
        with open(path) as f:
            r = csv.DictReader(f)
            for row in r:
                out.append((int(row["packet_hex"], 0), int(row["timestamp_hex"], 0)))
        return out
    else:
        raise ValueError(f"unknown capture extension: {ext!r}")


__all__ = ["MonbusSniffer", "load_capture"]
