# Flash the Nexys A7 with the LiteDRAM char bitstream via JTAG.
set self [file normalize "[file dirname [info script]]/.."]
open_hw_manager
connect_hw_server
open_hw_target
set dev [lindex [get_hw_devices xc7a100t*] 0]
current_hw_device $dev
set_property PROGRAM.FILE "$self/bitstream/litedram_char.bit" $dev
program_hw_devices $dev
close_hw_manager
