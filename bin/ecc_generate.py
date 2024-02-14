#!/usr/bin/python3

from optparse import OptionParser
import math
from rtl_generators.utils import write_hamming


def get_args():
    parser = OptionParser()

    parser.add_option('--path', dest='path', default=0.,
                        type='string', help='Output files path')
    parser.add_option('--type', dest='type',
                        type='string', help="ECC Type (hamming|bch)")
    parser.add_option('--buswidth', dest='buswidth',
                        default=16, type='int', help='data width')

    (options, args) = parser.parse_args()
    return options


def _main(args):
    valid_types = ['hamming']
    assert (
        args.type in valid_types
    ), f'Error in ECC Type:: Adder Types must be one of {valid_types}'

    assert args.buswidth>2, 'Bus Width must be greater than two'

    if args.type == 'hamming':
        write_hamming(args.path, args.buswidth)
    else:
        print(f'Unknown option {args.type}')
        exit(-1)


if __name__ == "__main__":
    args = get_args()
    _main(args)
