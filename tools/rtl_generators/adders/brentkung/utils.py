from .pg import PG as PG
from .bitwise_pg_logic import BitwisePGLogic as BitwisePGLogic
from .group_pg_logic import GroupPGLogic as GroupPGLogic
from .sum_logic import SumLogic as SumLogic
from .brent_kung_adder import BrentKungAdder as BrentKungAdder
from adders.blocks import BlackBlock
from adders.blocks import GrayBlock


def write_module(file_path, module):
    bus_width = module.buswidth if hasattr(module, 'buswidth') else None
    unique = module.unique
    if bus_width is not None and unique is False:
        file_name = f"{module.module_name}_{str(bus_width).zfill(3)}.sv"
    else:
        file_name = f"{module.module_name}.sv"
    module.verilog(file_path=file_path, file_name=file_name)
    print('"{file_name}"'.format(file_name=file_name))


def write(file_path, bitwidth):
    print('Generated:')
    # Write BlackBlock.v
    write_module(file_path, BlackBlock())

    # Write GrayBlock.v
    write_module(file_path, GrayBlock())

    # Write PG.v
    write_module(file_path, PG())

    # Write BitwisePGLogic.v
    write_module(file_path, BitwisePGLogic(bitwidth))

    # Write GroupPGLogic.v
    write_module(file_path, GroupPGLogic(bitwidth))

    # Write SumLogic.v
    write_module(file_path, SumLogic(bitwidth))

    # Write BrentKungAdder
    write_module(file_path, BrentKungAdder(bitwidth))
