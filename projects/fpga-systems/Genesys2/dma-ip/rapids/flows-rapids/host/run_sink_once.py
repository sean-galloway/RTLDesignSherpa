#!/usr/bin/env python3
# Loop SINK runs (CHANNEL_RESET disabled) until the scheduler wedges
# (snk_system_idle stuck 0), leaving it frozen for an ILA snapshot. The wedge is
# an intermittent timing race, so one run may not trip it; back-to-back runs do.
import sys, io as _io, contextlib
sys.path.insert(0, 'projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids/host')
from rapids_byte_io import RapidsByteIO
import run_characterization as rc
import board_guard
_hw = board_guard.HardwareRun(readback=False)
try:
    _hw.__enter__()
except board_guard.BoardBusy as exc:
    print(f"FAIL: {exc}")
    sys.exit(board_guard.LOCK_BUSY_EXIT)
port  = sys.argv[1] if len(sys.argv) > 1 else '/dev/ttyUSB1'
beats = int(sys.argv[2]) if len(sys.argv) > 2 else 64
with contextlib.redirect_stdout(_io.StringIO()):
    io = RapidsByteIO(port=port, baudrate=115200, timeout=1.0)
    c = rc.RapidsByteCampaign(io, 8, verbose=False)
    c.reset_channels = lambda: None
    c.configure()
wedged = False
for i in range(12):
    with contextlib.redirect_stdout(_io.StringIO()):
        ok, _ = c.run_sink_selfcheck(list(range(8)), beats, timeout_s=5.0)
    idle = io.csr_field('STATUS', 'SNK_IDLE')
    print(f"run {i+1}: pass={ok} SNK_IDLE={idle}")
    if idle == 0:
        print(f"WEDGED after {i+1} runs (beats={beats}) — frozen for ILA")
        wedged = True
        break
if not wedged:
    print(f"did NOT wedge in 12 runs at beats={beats}")
io.close()
_hw.__exit__(None, None, None)
