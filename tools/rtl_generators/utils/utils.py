from optparse import OptionParser


def create_matrix_2d(row, col, default_val='x'):
    return [[default_val] * col for i in range(row)]


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
