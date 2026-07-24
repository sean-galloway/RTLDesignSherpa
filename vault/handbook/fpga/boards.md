---
title: Boards
summary: JTAG serials, UART chips, and the gotchas that eat an afternoon.
---

# Board handling (this lab)

Shared JTAG chain - select by serial (env RAPIDS_CHAR_JTAG_SERIAL):
- Nexys A7:  210292B7D46F  (xc7a100t)
- Genesys 2: 200300B818A0  (xc7k325t)

Gotchas:
- Genesys 2 UART is a SEPARATE FT232R (serial AU05X8RM), not the JTAG
  FT2232. Both must be plugged; if the FT232R is not enumerated, there is
  no UART no matter what the bitstream does.
- Digilent Adept kills the UART ttyUSB. Do NOT power-cycle the board after
  programming - reprogram loses the port binding.
- ftdi_sio does not block Vivado programming; no driver dance needed.
- A7 note: its stream_char build sits on a timing knife-edge at 100 MHz
  (compressor CAM); the K325T does not - prefer the Genesys for monitor
  work ([[timing-closure]]).
