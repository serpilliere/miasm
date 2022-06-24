"""This example illustrate the Sandbox.call API, for direct call of a given
function"""

from miasm.analysis.binary import Container
from miasm.analysis.sandbox import Sandbox_Linux_arml
from miasm.core.locationdb import LocationDB
from miasm.core.utils import hexdump
from miasm.os_dep.linux_stdlib import linobjs

parser = Sandbox_Linux_arml.parser(description="ELF sandboxer")
parser.add_argument("filename", help="ELF Filename")


def main(options):
    loc_db = LocationDB()
    sb = Sandbox_Linux_arml(loc_db, options.filename, options, globals())

    with open(options.filename, "rb") as fdesc:
        cont = Container.from_stream(fdesc, loc_db)
        loc_key = cont.loc_db.get_name_location("md5_starts")
        addr_to_call = cont.loc_db.get_location_offset(loc_key)

    # Calling md5_starts(malloc(0x64))
    addr = linobjs.heap.alloc(sb.jitter, 0x64)
    sb.call(addr_to_call, addr)
    hexdump(sb.jitter.vm.get_mem(addr, 0x64))


def test(sample_md5_arm, jitter_name):
    bin_path, _ = sample_md5_arm
    main(parser.parse_args([bin_path, "--jitter", jitter_name]))


if __name__ == '__main__':
    # Parse arguments
    options = parser.parse_args()
