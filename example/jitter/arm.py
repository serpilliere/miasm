from __future__ import print_function

import logging
import os.path
import sys

from miasm.analysis.sandbox import Sandbox_Linux_arml
from miasm.core.locationdb import LocationDB


def arm(params):
    # Get arguments
    parser = Sandbox_Linux_arml.parser(description="""Sandbox an elf binary with arm
     engine (ex: jit_arm.py samples/md5_arm -a A684)""")
    parser.add_argument("filename", help="ELF Filename")
    parser.add_argument('-v', "--verbose", help="verbose mode", action="store_true")
    options = parser.parse_args(params)

    # Prepare the sandbox
    loc_db = LocationDB()
    sb = Sandbox_Linux_arml(loc_db, options.filename, options, globals())

    # Handle 'verbose' option
    if options.verbose is True:
        logging.basicConfig(level=logging.INFO)
    else:
        logging.basicConfig(level=logging.WARNING)

    if options.verbose is True:
        print(sb.jitter.vm)

    # Run the code
    sb.run()


def test(jitter_name):
    current_path = os.path.dirname(__file__)
    input = os.path.join(current_path, "..", "samples", "md5_arm")

    arm([input, "--mimic-env", "--jitter", jitter_name])


if __name__ == '__main__':
    arm(sys.argv)
