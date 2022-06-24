import pytest

from miasm.analysis.machine import Machine
import miasm.os_dep.common as commonapi
from miasm.core.locationdb import LocationDB

machine = Machine("x86_32")

loc_db = LocationDB()
jit = machine.jitter(loc_db)
jit.init_stack()


def test_get_size():
    heap = commonapi.heap()

    with pytest.raises(AssertionError):
        heap.get_size(jit.vm, 0)

    heap.alloc(jit, 20)
    heap.alloc(jit, 40)
    heap.alloc(jit, 50)
    heap.alloc(jit, 60)
    ptr = heap.alloc(jit, 10)
    heap.alloc(jit, 80)

    for i in range(10):
        assert heap.get_size(jit.vm, ptr + i) == 10
