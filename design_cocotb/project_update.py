#!/usr/bin/python3.11
"""Update the Files In a REPO for a new project name"""

import pprint
from FileFolderFunctions.UpdateFile import UpdateFile


pp = pprint.PrettyPrinter(indent=4)


# Main
if __name__ == "__main__":

    # Define the UpdateFile regex search and replace pairs
    uf_regex_pairs = [
        [r'Project Name  : Tigris',         r'Project Name  : Indus'],
        [r'tigris_core_top',                r'indus_core_top'],
        [r'tigris_die_top',                 r'indus_die_top'],
        [r'tigris_io',                      r'indus_io'],
        [r'on tigris',                      r'on indus'],
        [r'tigris_',                        r'indus_'],
        [r'TIGRIS',                         r'INDUS'],
        [r'Tigris ',                        r'Indus '],
        [r'tigris_core',                    r'indus_core'],
        [r'tigris core',                    r'indus core'],
        [r'_tigris_',                       r'_indus_'],
        [r'Tigris',                         r'Indus'],
        [r'tigris_fractalcore',             r'indus_fractalcore'],
        [r'tigris_output_select_enable',    r'indus_output_select_enable'],
        [r'tigris_id',                      r'indus_id'],
        [r'tigris_die',                     r'indus_die']
    ]
    uf_skip_regex = [ 
                        r'Storage2.projects',
                        r'VENDOR_IP'
                    ]

    # Initialize the UpdateFile class
    uf = UpdateFile(root_dir="design", regex_list=uf_regex_pairs, skip_regex_list=uf_skip_regex)

    # Find matching contents in any file
    uf.find_items()

    # Report matched items to a file
    uf.report_items("uf_matched_items_report.txt")

    # Make the substitutions
    uf.sub_items()

    # Define the FileFindMove regex search and replace pairs
    ffm_regex_pairs = [
        [r"(.*)tigris(.*)", r"\1indus\2"],
    ]

    # Initialize the FileFindMove class
    # ffm = FileFindMove(root_dir="design", regex_list=ffm_regex_pairs)

    # Find matching files and directories
    # ffm.find_items()

    # Report matched items to a file
    # ffm.report_items("ffm_matched_items_report.txt")

    # Move the matched matched files and directories
    # ffm.move_items()
