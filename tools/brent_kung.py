from optparse import OptionParser
import math
from rtl_generators.utils import write_bk

def get_args():
    parser = OptionParser()

    parser.add_option('--path', dest='path', default=0.,
                        type='string', help='Output files path')
    parser.add_option('--adder-type', dest='adder_type',
                        default='brent_kung', type='string', help="Adder Type")
    parser.add_option('--bitwidth', dest='bitwidth',
                        default=16, type='int', help='Adder Bitwidth')

    (options, args) = parser.parse_args()
    return options

def _main(args):
    valid_adder_types = ['brent_kung']
    assert (
        args.adder_type in valid_adder_types
    ), f'Error in Adder Type:: Adder Types must be one of {valid_adder_types}'

    assert math.log2(args.bitwidth) == int(
        math.log2(args.bitwidth)), 'Bitwise must be power of 2.'

    if args.adder_type == 'brent_kung':
        write_bk(args.path, args.bitwidth)
    else:
        print('Some Error.')
        exit(-1)


if __name__ == "__main__":
    args = get_args()
    _main(args)
