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

# signal

The `signal` module, located at `rtl_generators/verilog/signal.py`, parses, manipulates, and generates Verilog signal declaration strings. It relies on `ParserHelper` from `rtl_generators.verilog.verilog_parser` for parsing and formatting utility functions. Here's a detailed breakdown of the module:

![Signal UML](../../images_scripts_uml/verilog_Signal.svg)

This module consists of a `SignalRecord` data class holding signal information. There is a `Signal` class managing a list of `SignalRecord` instances. The `Signal` class includes methods to add new signal strings, generate wire declarations, and create port strings for a Verilog module.

## Key Functionalities

- `__init__(self, signal_str='')`: Initializes the `Signal` object by parsing a signal string and converting it into `SignalRecord` instances.

- `_found_name(self, name: str) -> Tuple[bool, int]`: Searches for a signal by name in the list and returns a tuple with a boolean indicating the signal and its index.

- `_convert_sigrec_list(self, rec_list)`: Converts a record list from `ParserHelper` into a list of `SignalRecord` objects, merging signal information upon detecting duplicate names.

- `add_port_string(self, signal_str)`: Parses a signal port string and incorporates its information into the `Signal` object's records.

- `create_wire_string(self) -> str`: Creates a formatted string for declaring wires in a Verilog module, aligning elements for readability.

- `create_port_string(self) -> str`: Creates a formatted string for port declarations in a Verilog module, placing commas appropriately in the signal list.

---

## Block Hierarchy and Links

- [Module Class](module.md)
- [Parser Helper Class](verilog_parser.md)
- [Signal Class](signal.md)
- [Parameter Class](param.md)
- [Utils](utils.md)

---

[Back to Scripts Index](index.md)

---
