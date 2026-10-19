# TASK-045: CXS per-stream packet framing and credits beyond the spec cap

**Priority:** P1
**Status:** closed 2026-10-16
**Owner:** sean galloway

The CXS family tracked ONE open packet per link. IHI 0079D 2.5.2 defines a
stream as the flits sharing CXSPRCLTYPE/CXSSRCID/CXSTGTID and lets streams
interleave, so framing is per stream. Found by the CXS injector's interleave
mode and the byte-granular RAPIDS source (round-robin per drain block while a
packet spans the descriptor): legal traffic the family itself rejected.
Owner decision 2026-10-16: per-stream tracking.

## Done

- `cxs_stream_key` (new): the low CXS_STREAM_{PRCL,SRCID,TGTID}_BITS of the
  three fields. `cxs_cntl_track` keeps one open bit per key (KEY_W = 0 is the
  old single-context behaviour, the default everywhere).
- cxs_master / cxs_slave / _cg / _monlite and cxs_monitor_lite take the key
  params; `axis_to_cxs` frames START per TID/TDEST key.
- `CXS_CREDIT_BEYOND_SPEC` (owner 2026-10-16, for a whole-SRAM credit pool):
  skips rule 12 only, in cxs_pkg::config_error and RDS-DV CXSConfig alike.
- `cxs_link_snoop` (new): passive wire-level credit/link/framing model.
- RDS-DV: CXSDepacketizer per stream (dict on the full spec key);
  CXSTransmitter open-packet model per stream; CXSConfig.credit_beyond_spec;
  5 new unit tests (81/81).
- Tests: val/amba/test_cxs_stream_interleave.py -- key on: clean; key off:
  the SAME traffic must set protocol_error (proves the key, 4/4). val/amba
  CXS FULL 61/61, monitors CXS FULL 24/24.
