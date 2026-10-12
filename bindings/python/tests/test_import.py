import thole


def test_version():
    assert isinstance(thole.__version__, str)
    assert thole.__version__


def test_areas():
    from thole import quad, roots

    assert quad.gauss_kronrod and roots.newton
