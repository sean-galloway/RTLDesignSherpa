<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open

## BRIDGE-018 — A native-AXI5 fabric
**Status:** open 2026-09-11 (split out of BRIDGE-014 when its master-protocol
half closed)
**Priority:** P3. No feature anyone has asked for needs it.

The crossbar is AXI4-shaped inside, with the AXI5 sideband riding alongside
in the channel structs (BRIDGE-002 A5-2). That covers every AMBA5 feature
delivered so far -- interop sideband, native sideband, atomics of every
class, poison, the Lite and APB5 ports on both sides (BRIDGE-014). What it
cannot express is a feature whose semantics change the fabric's own rules:
read-data chunking (per-beat ordering inside a burst), MTE tags with their
own ordering, or anything that needs the crossbar to reason about AXI5
transaction attributes rather than carry them. If one of those becomes a
requirement, this is where it goes: the structs, the crossbar mux, both
adapters' tracking paths and the response mux all change together.

Not owed until a consumer appears. Related: [[BRIDGE-002]], [[BRIDGE-014]]
(both closed).
