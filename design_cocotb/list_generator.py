#!/usr/bin/python3.11
"""Creates lists for RTL and for Synthesis"""

import argparse
import pprint

from FileFolderFunctions.file_list_processor import FileListProcessor
pp = pprint.PrettyPrinter(indent=4)

def get_args():
    """Parse the command line"""
    parser = argparse.ArgumentParser(description="Process input files and options.")

    help_str = ('Specify the output file, prefix portion of the name; '
                'the suffix is created automatically.')
    # Add arguments
    parser.add_argument(
        '--file',
        action='append',  # Allows multiple occurrences of this argument
        dest='files',
        required=True,
        help='Specify a file. Can be used multiple times to specify multiple files.'
    )
    parser.add_argument(
        '--type',
        choices=['rtl', 'syn'],  # Restrict to specific choices
        required=True,
        help='Specify the type. Choices are rtl or syn.'
    )
    parser.add_argument(
        '--outfile',
        required=True,
        help=help_str
    )
    parser.add_argument(
        '--debug',
        action='store_true',  # Boolean flag, defaults to False
        help='Enable debug mode.'
    )

    return parser.parse_args()

def main(args):
    """Process input files based on provided arguments.

    This function processes the input files and options to generate
    either an RTL or synthesis file list. It uses the FileListProcessor
    to handle file operations based on the specified type.
    """
    dbg = bool(args.debug)
    fp = FileListProcessor(filelist=args.files, debug=dbg)

    if args.type == 'rtl':
        fp.write_filelist(args.outfile)
    else:
        fp.write_synth_filelist(args.outfile)


if __name__ == '__main__':
    options = get_args()
    main(options)
