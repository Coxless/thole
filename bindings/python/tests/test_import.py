import thole


def test_version():
    assert isinstance(thole.__version__, str)
    assert thole.__version__
