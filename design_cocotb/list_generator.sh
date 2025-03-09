#!/bin/bash

python list_generator.py --type rtl \
    --file "$PROJ/design/tigris_chip/rtl/tigris_mx2_chip_top.f" \
    --file "$PROJ/design/command_if/rtl/command_if_vhdl_top_only.f" \
    --file "$PROJ/design/RAE_pair/rtl/RAE_pair_vhdl_only.f" \
    --outfile "$PROJ/rtl_list"

python list_generator.py --type syn \
    --file "$PROJ/design/tigris_chip/rtl/tigris_mx2_chip_top.f" \
    --file "$PROJ/design/command_if/rtl/command_if_vhdl_top_only.f" \
    --file "$PROJ/design/RAE_pair/rtl/RAE_pair_vhdl_only.f" \
    --outfile "$PROJ/syn_list"