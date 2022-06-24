from miasm.analysis.sandbox import Sandbox_Win_x86_32
from miasm.core.locationdb import LocationDB

# Insert here user defined methods

# Parse arguments
parser = Sandbox_Win_x86_32.parser(description="PE sandboxer")
parser.add_argument("filename", help="PE Filename")


def main(options):
    # Create sandbox
    loc_db = LocationDB()
    sb = Sandbox_Win_x86_32(loc_db, options.filename, options, globals())

    # Run
    sb.run()

    assert not sb.jitter.running


if __name__ == '__main__':
    main(parser.parse_args())
