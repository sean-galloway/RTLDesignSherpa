# Filelist for axi4_slave_rom
# Location: projects/components/misc/rtl/filelists/axi4_slave_rom.f
#
# A read-only AXI4 slave over simple_rom: the AXI4 read slave from rtl/amba
# plus the ROM. Both arrive by -f include; neither is hand-listed.

+incdir+$REPO_ROOT/rtl/amba/includes

-f $REPO_ROOT/rtl/amba/filelists/axi4_slave_rd.f
-f $REPO_ROOT/projects/components/misc/rtl/filelists/simple_rom.f

$REPO_ROOT/projects/components/misc/rtl/axi4_slave_rom.sv
