#!/usr/bin/python3

from optparse import OptionParser
import math
from rtl_generators.utils import write_bk, write_dadda, write_wallace


def get_args():
    parser = OptionParser()

    parser.add_option('--path', dest='path', default=0.,
                        type='string', help='Output files path')
    parser.add_option('--type', dest='type',
                        default='brent_kung', type='string', help="Adder Type")
    parser.add_option('--buswidth', dest='buswidth',
                        default=16, type='int', help='Bitwidth')

    (options, args) = parser.parse_args()
    return options


def _main(args):
    valid_types = ['brent_kung', 'dadda', 'wallace_fa', 'wallace_csa']
    assert (
        args.type in valid_types
    ), f'Error in Adder Type:: Adder Types must be one of {valid_types}'

    assert math.log2(args.buswidth) == int(
        math.log2(args.buswidth)), 'Bus Width must be power of 2.'

    if args.type == 'brent_kung':
        write_bk(args.path, args.buswidth)
    elif args.type == 'dadda':
        write_dadda(args.path, args.buswidth)
    elif args.type == 'wallace_fa':
        write_wallace(args.path, 'fa', args.buswidth)
    elif args.type == 'wallace_csa':
        write_wallace(args.path, 'csa', args.buswidth)
    else:
        print(f'Unknown option {args.type}')
        exit(-1)


if __name__ == "__main__":
    args = get_args()
    _main(args)
