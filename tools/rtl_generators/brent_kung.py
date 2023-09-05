import math
import utils as utils
import adders.brentkung as brentkung


def _main(args):
    valid_adder_types = ['brent_kung']
    assert args.adder_type in valid_adder_types, 'Error in Adder Type:: Adder Types must be one of {}'.format(
        valid_adder_types)

    assert math.log2(args.bitwidth) == int(
        math.log2(args.bitwidth)), 'Bitwise must be power of 2.'

    if args.adder_type == 'brent_kung':
        brentkung.write(args.path, args.bitwidth)
    else:
        print('Some Error.')
        exit(-1)


if __name__ == "__main__":
    args = utils.get_args()
    _main(args)
