from hypothesis import strategies as st
from hypothesis import given
import pytest

# @pytest.mark.xfail
@given(st.functions(
    like=lambda state, move1, move2, result: (state, result),
    returns=st.tuples(st.integers(), st.integers()),
    pure=True,
))
def test_fn(f):
    assert f(1, 2, 3, 4) == (5, 6)
