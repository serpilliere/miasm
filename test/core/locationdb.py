import pytest

from miasm.core.locationdb import LocationDB


def test_basic_offset():
    loc_db = LocationDB()
    loc_key1 = loc_db.add_location()
    loc_key2 = loc_db.add_location()
    loc_db.set_location_offset(loc_key2, 0x1234)

    assert loc_db.get_location_offset(loc_key1) is None
    assert loc_db.get_location_offset(loc_key2) == 0x1234

    loc_db.consistency_check()


def test_pretty_str():
    loc_db = LocationDB()
    loc_key1 = loc_db.add_location()
    loc_key2 = loc_db.add_location()
    loc_db.set_location_offset(loc_key2, 0x1234)
    loc_key3 = loc_db.add_location()
    loc_db.add_location_name(loc_key3, "first_name")
    loc_db.add_location_name(loc_key3, "second_name")
    loc_db.set_location_offset(loc_key3, 0x5678)
    loc_db.remove_location_name(loc_key3, "second_name")

    assert loc_db.pretty_str(loc_key1) == str(loc_key1)
    assert loc_db.pretty_str(loc_key2) == "loc_key_1, loc_1234"
    assert loc_db.pretty_str(loc_key3) == "loc_key_2, first_name, loc_5678"
    assert loc_db.get_location_offset(loc_db.get_name_location("first_name")) == 0x5678

    loc_db.consistency_check()


def test_offset():
    loc_db = LocationDB()

    loc_key4 = loc_db.add_location()
    assert loc_db.get_location_offset(loc_key4) is None

    loc_key2 = loc_db.add_location()
    loc_db.set_location_offset(loc_key2, 0x1234)

    loc_db.set_location_offset(loc_key4, 0x1122)
    assert loc_db.get_location_offset(loc_key4) == 0x1122

    loc_db.unset_location_offset(loc_key4)
    assert loc_db.get_location_offset(loc_key4) is None

    with pytest.raises(ValueError):
        loc_db.set_location_offset(loc_key4, 0x1234)

    assert loc_db.get_location_offset(loc_key4) is None
    loc_db.set_location_offset(loc_key4, 0x1122)

    with pytest.raises(ValueError):
        loc_db.set_location_offset(loc_key4, 0x1123)

    assert loc_db.get_location_offset(loc_key4) == 0x1122

    loc_db.set_location_offset(loc_key4, 0x1123, force=True)
    assert loc_db.get_location_offset(loc_key4) == 0x1123

    assert loc_db.get_offset_location(0x1123) is not None

    with pytest.raises(ValueError):
        loc_db.add_location(offset=0x1123)

    assert loc_db.add_location(offset=0x1123, strict=False) == loc_key4
    assert loc_db.get_offset_location(0x1123) == loc_key4
    assert loc_db.get_or_create_offset_location(0x1123) == loc_key4

    loc_key4_bis = loc_db.get_or_create_offset_location(0x1144)
    assert loc_db.get_offset_location(0x1144) == loc_key4_bis

    loc_db.consistency_check()


def test_names():
    loc_db = LocationDB()
    # Names manipulation
    name1 = "name1"
    name2 = "name2"
    name3 = "name3"
    loc_key1 = loc_db.add_location()
    loc_key5 = loc_db.add_location()
    assert len(loc_db.get_location_names(loc_key5)) == 0

    loc_db.add_location_name(loc_key5, name1)
    loc_db.add_location_name(loc_key5, name2)
    assert loc_db.get_name_location(name1) is not None
    assert loc_db.get_name_location(name2) is not None
    assert name1 in loc_db.get_location_names(loc_key5)
    assert name2 in loc_db.get_location_names(loc_key5)
    assert loc_db.get_name_location(name1) == loc_key5

    loc_db.remove_location_name(loc_key5, name1)
    assert loc_db.get_name_location(name1) is None
    assert name1 not in loc_db.get_location_names(loc_key5)

    with pytest.raises(ValueError):
        loc_db.remove_location_name(loc_key5, name1)

    with pytest.raises(ValueError):
        loc_db.add_location_name(loc_key1, name2)

    with pytest.raises(ValueError):
        loc_db.add_location(name=name2)

    assert loc_db.add_location(name=name2, strict=False) == loc_key5
    assert loc_db.get_or_create_name_location(name2) == loc_key5
    loc_key5_bis = loc_db.get_or_create_name_location(name3)
    assert loc_db.get_name_location(name3) == loc_key5_bis

    loc_db.consistency_check()

    # Name and offset manipulation
    assert loc_db.get_location_offset(loc_db.get_name_location(name2)) is None
    assert loc_db.get_name_location("unk_name") is None


def test_merge():
    loc_db = LocationDB()
    name2 = "name2"
    loc_key5 = loc_db.add_location()
    loc_db.add_location_name(loc_key5, name2)

    # Merge
    loc_db2 = LocationDB()
    loc_db2.add_location(offset=0x3344)
    loc_db.merge(loc_db2)

    assert loc_db.get_offset_location(0x3344) is not None
    assert loc_db.get_name_location(name2) is not None

    loc_db.consistency_check()

    assert loc_db.get_name_location(name2) == loc_key5


def test_merge_with_conflicts():
    loc_db = LocationDB()
    name2 = "name2"
    loc_key5 = loc_db.add_location()
    loc_db.add_location_name(loc_key5, name2)

    # Merge
    loc_db2 = LocationDB()
    loc_db2.add_location(offset=0x3344)
    loc_db2.add_location(name=name2)
    with pytest.raises(ValueError):
        loc_db.merge(loc_db2)

    # It is undefined whether 0x3344 is a valid offset now or not
    assert loc_db.get_name_location(name2) is not None

    loc_db.consistency_check()

    assert loc_db.get_name_location(name2) == loc_key5


def test_delete():
    loc_db = LocationDB()
    loc_key5 = loc_db.add_location()
    name2 = "name2"
    loc_db.add_location_name(loc_key5, name2)

    # Delete
    loc_db.remove_location(loc_key5)
    assert loc_db.get_name_location(name2) is None

    loc_db.consistency_check()


if __name__ == '__main__':
    test_basic_offset()
    test_pretty_str()
    test_offset()
    test_names()
    test_merge()
    test_delete()
