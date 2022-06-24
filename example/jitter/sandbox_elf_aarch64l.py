import logging

from miasm.analysis.sandbox import Sandbox_Linux_aarch64l
from miasm.core.locationdb import LocationDB
from miasm.jitter.jitload import log_func

# Insert here user defined methods

# Parse arguments
parser = Sandbox_Linux_aarch64l.parser(description="ELF sandboxer")
parser.add_argument("filename", help="ELF Filename")


def main(options):
    # Create sandbox
    loc_db = LocationDB()
    sb = Sandbox_Linux_aarch64l(loc_db, options.filename, options, globals())

    log_func.setLevel(logging.ERROR)

    # Run
    sb.run()

    assert (sb.jitter.running is False)


def test(sample_md5_aarch64l, jitter_name):
    path, _ = sample_md5_aarch64l
    main(parser.parse_args([path, "--mimic-env", "--jitter", jitter_name]))


if __name__ == '__main__':
    main(parser.parse_args())
