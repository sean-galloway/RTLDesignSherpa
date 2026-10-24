# TASK-018: loadable firmware memory, as on rapids-g

**Priority:** P3
**Status:** CLOSED 2026-10-24 -- delivered by stream TASK-020 phase 4: stream-g carries rapids-g's loadable firmware memory as is (FW_CTRL/FW_ADDR/FW_DATA/FW_RDATA at 0x3A0-0x3AC, FW_WRITABLE on the build; MAS 7.3), proven on the Genesys 2 the same day
**Owner:** sean galloway

## Why

Owner 2026-10-23: once the loadable firmware memory (a BRAM written from config space, a ROM once the image
is golden) is proven on rapids-g (rapids TASK-038), STREAM should have it too.

## Answered 2026-10-24

The owner asked for gatling in STREAM: a firmware-sequenced STREAM variant (stream TASK-020), built as
rapids-g was. The loadable firmware memory comes with its sequencer block (phase 4), and this item closes then.

## Open question (as filed)

STREAM has no firmware today: no gatling and no instruction memory anywhere under `stream/rtl`. What
"the same" means here is to be decided with the owner when rapids TASK-038 closes -- a firmware-sequenced
STREAM variant (as rapids-g is to RAPIDS), or the loader as a shared block for any area that adopts one.

## Done when

The owner's answer to the open question is built and tested to the rapids TASK-038 standard.
