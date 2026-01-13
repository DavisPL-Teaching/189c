
# We might need this
from math import sqrt

# 1. Write the program
def integer_sqrt(n):
    # Ideas: binary search and check the square to see if it's greater than the target integer - keep narrowing search window until we hit the point
    # where the current integer is the int square root
    # Another idea: just call the sqrt function and round it down.
    return int(sqrt(n))

# 2. Write the specification
# TODO
# In plain English:
# Suggestion: whatever the function returns, if we square it, we get n
# This is the right idea but might not always work...
# Input: 10, int(sqrt(10)) = 3, 3*3 = 9, not quite 10
# Suggestion:
# - if our answer is ans, we could look at ans^2 and (ans+1)^2
# - The original integer n should be between ans^2 and (ans+1)^2
# - In our example: 3^2 = 9 < 10 < 4^2 = 16

# As a logical assertion:
# assert ans * ans <= n and (ans + 1) * (ans + 1) > n

# 3. Check the specification
# This step will depend on the tool.
# As a Hypothesis test: - @given annotation and a unit test.
@pytest.mark.skip # comment out to run
@given(st.integers(min_value=0, max_value=10_000))
def test_integer_sqrt(n):
    ans = integer_sqrt(n)
    assert (ans * ans <= n and (ans + 1) * (ans + 1) > n)

# Some examples to try running the program
# print(integer_sqrt(3))
# print(integer_sqrt(-3))

# - 6 is stronger than 7 iff all programs satisfying 6 also satisfy 7
# Is there a program satisfying 6 but not 7?

def prog_ex(x):
    # Program returning 9 if the input is 100, otherwise returning 11
    if x == 100:
        return 9
    else:
        return 11

@given(st.integers(min_value=0, max_value=10_000))
def test_prog_ex_spec_6(x):
    y = prog_ex(x)
    if x > 100:
        assert y > 10

@given(st.integers(min_value=50, max_value=200)) # <- precondition
# Mark as expected failure -
@pytest.mark.xfail
def test_prog_ex_spec_7(x):
    y = prog_ex(x)
    if x >= 100: # <- precondition
        assert y >= 10 # <- postcondition

# - 7 is stronger than 6 iff all programs satisfying 7 also satisfy 6
# (Exercise)

# @pytest.mark.skip
# # @given(st.integers(min_value = , max_value = ))
# def test_prog_ex_stronger():
#     # TODO
#     raise NotImplementedError
