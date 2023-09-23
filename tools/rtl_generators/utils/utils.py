from rtl_generators.adders.brentkung.pg import PG as PG
from rtl_generators.adders.brentkung.bitwise_pg_logic import BitwisePGLogic as BitwisePGLogic
from rtl_generators.adders.brentkung.group_pg_logic import GroupPGLogic as GroupPGLogic
from rtl_generators.adders.brentkung.sum_logic import SumLogic as SumLogic
from rtl_generators.adders.brentkung.brent_kung_adder import BrentKungAdder as BrentKungAdder
from rtl_generators.adders.brentkung.black import Black
from rtl_generators.adders.brentkung.gray import Gray


def write_module(file_path, module):
    file_name = f"{module.module_name}.v"
    module.verilog(file_path=file_path)
    print(f'"{file_name}"')


def write_bk(file_path, bitwidth):
    print('Generated:')
    # Write BlackBlock.v
    write_module(file_path, Black())

    # Write GrayBlock.v
    write_module(file_path, Gray())

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
