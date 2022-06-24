import pytest

from miasm.core.locationdb import LocationDB

from miasm.analysis.machine import Machine


@pytest.fixture
def jitter(jitter_name):
    machine = Machine("x86_64")
    loc_db = LocationDB()
    return machine.jitter(loc_db, jitter_name)


def test_rax_positive(jitter):
    jitter.cpu.RAX = 16565615892967251934
    assert jitter.cpu.RAX == 16565615892967251934


def test_rax_negative1(jitter):
    jitter.cpu.RAX = -1
    assert jitter.cpu.RAX == 0xffffffffffffffff


def test_rax_negative2(jitter):
    jitter.cpu.RAX = -2
    assert jitter.cpu.RAX == 0xfffffffffffffffe


def test_eax_negative2(jitter):
    jitter.cpu.EAX = -2
    assert jitter.cpu.EAX == 0xfffffffe


def test_rax_negative_to_positive(jitter):
    jitter.cpu.RAX = -0xffffffffffffffff
    assert jitter.cpu.RAX == 1


@pytest.mark.parametrize("value", [0x1ffffffffffffffff, 0x10000000000000000])
def test_rax_too_big(jitter, value):
    with pytest.raises(TypeError):
        jitter.cpu.RAX = value


def test_eax_negative_to_positive1(jitter):
    jitter.cpu.EAX = -0xefffffff
    assert jitter.cpu.EAX == 0x10000001


def test_eax_negative_to_positive2(jitter):
    jitter.cpu.EAX = -0xFFFFFFFF
    assert jitter.cpu.EAX == 1


def test_eax_too_big(jitter):
    with pytest.raises(TypeError):
        jitter.cpu.EAX = -0x1ffffffff
