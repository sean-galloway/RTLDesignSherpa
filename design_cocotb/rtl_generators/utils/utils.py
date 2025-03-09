from rtl_generators.adders.brentkung.pg import PG
from rtl_generators.adders.brentkung.bitwise_pg_logic import BitwisePGLogic
from rtl_generators.adders.brentkung.group_pg_logic import GroupPGLogic
from rtl_generators.adders.brentkung.sum_logic import SumLogic
from rtl_generators.adders.brentkung.brent_kung_adder import BrentKungAdder
from rtl_generators.adders.brentkung.black import Black
from rtl_generators.adders.brentkung.gray import Gray
from rtl_generators.multipliers.dadda_multiplier import DaddaTree
from rtl_generators.multipliers.wallace_multiplier import WallaceTree
from rtl_generators.ecc.hamming import HammingEncode, HammingDecode

def write_module(file_path, module):
    file_name = f"{module.module_name}.sv"
    module.verilog(file_path=file_path)
    print(f'"{file_name}"')


def write_dadda(file_path, buswidth):
    write_module(file_path, DaddaTree(buswidth))


def write_wallace(file_path, type, buswidth):
    write_module(file_path, WallaceTree(type, buswidth))


def write_bk(file_path, buswidth):
    write_module(file_path, Black())
    write_module(file_path, Gray())
    write_module(file_path, PG())
    write_module(file_path, BitwisePGLogic(buswidth))
    write_module(file_path, GroupPGLogic(buswidth))
    write_module(file_path, SumLogic(buswidth))
    write_module(file_path, BrentKungAdder(buswidth))

def write_hamming(file_path, buswidth):
    write_module(file_path, HammingEncode(buswidth))
    write_module(file_path, HammingDecode(buswidth))

