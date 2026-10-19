// SPDX-License-Identifier: MIT
// Empty stub for ocelus_pkg - satisfies `import ocelus_pkg::*` in rapids_imports.svh
// without re-exporting create_monitor_packet (which causes sv2v ambiguity with
// ocelus_common_pkg). All needed symbols come from the individual protocol packages.
package ocelus_pkg;
endpackage
