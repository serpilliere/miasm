from miasm.core.utils import BoundedDict


def test_bounded_dict():
    # Use a callback
    def logger(key):
        print("DELETE", key)

    # Create a 5/2 dictionary
    bd = BoundedDict(5, 2, initialdata={"element": "value"},
                     delete_cb=logger)
    bd["element2"] = "value2"
    assert ("element" in bd)
    assert ("element2" in bd)
    assert bd["element"] == "value"
    assert bd["element2"] == "value2"

    # Increase 'element2' use
    _ = bd["element2"]

    for i in range(6):
        bd[i] = i
        print("Insert %d -> %s" % (i, bd))

    assert (len(bd) == 2)

    assert ("element2" in bd)
    assert bd["element2"] == "value2"
