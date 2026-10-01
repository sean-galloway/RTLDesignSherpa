# Acronyms and terminology

| Term | Meaning |
| --- | --- |
| AXI4-Lite | The simple AMBA bus the FPGA-side bridge drives. One 32-bit transfer per transaction, no bursts. |
| BFM | Bus Functional Model. A simulation driver standing in for real traffic. |
| Byte channel | Any object with `write`, `read_until`, `reset_input_buffer`, `reset_output_buffer`, `close`, `is_open`. A `UartLink` is one; so is a cocotb channel. |
| CSR | Control and Status Register. |
| Entry point | A `host_*.py` or `run_*.py`: the file a person or Makefile invokes. |
| FT2232, FT232R | FTDI USB parts. The FT2232 carries two interfaces (JTAG and UART on one chip); the FT232R carries one. |
| hw_server | Xilinx's JTAG daemon. Vivado talks to the cable through it. |
| IDCODE | The JTAG identification register of a device on the chain. |
| JTAG serial | The USB serial number Vivado uses to pin a `hw_target`. |
| Probe | A predicate handed an open link that answers "is this the board I want?". |
| Sequence | A named, dependency-declaring unit of work (Chapter 3). |
| SequenceContext | What a sequence is given: a bus, a board, parameters, earlier results. |
| USB serial | The serial number the USB descriptor reports. On a Nexys A7 this is also the JTAG serial. |

## Terms used precisely in this book

**Port** always means a character device path (`/dev/ttyUSB3`), never an RTL
port. The RTL sense does not appear in this book.

**Board** means a `Board` object from the registry -- the software handle --
unless the text says "physical board".

**Sequence** means a `Sequence` subclass, not "a sequence of bytes". Where the
byte sense is meant the text says "byte stream".

**Entry point** and **host program** are the same thing. The convention names it
by prefix: a file named `host_*` is an entry point. The directory it sits in is
not what makes it one (Chapter 5).
