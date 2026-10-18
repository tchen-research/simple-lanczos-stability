"""Exact rational check of the one-dimensional run used in the report.

This checks data against the paper's arithmetic model; it does not claim
that an IEEE implementation produces these particular rounding errors.
The unit eigenvector is (1,-1)/sqrt(2); the rational checks below use its
unnormalized direction, which has the same kernel/eigenvector identities.
"""
from fractions import Fraction as Q

eps = Q(1, 1000)
k = 2
A = Q(1)
v = [Q(0), Q(1), Q(1), Q(0)]
beta = [Q(0), eps, Q(0)]
alpha = [Q(0), 1 - eps, 1 - eps]
u = [Q(0), Q(1), Q(1)]
w = [Q(0), Q(1), 1 - eps]
z = [Q(0), eps, Q(0)]
ealpha = [Q(0), -eps, Q(0)]

assert 0 <= k * eps <= Q(1, 100)
assert beta[1] > 0 and beta[2] == 0 and z[2] == 0
for j in (1, 2):
    assert u[j] == A * v[j]
    assert w[j] == u[j] - beta[j - 1] * v[j - 1]
    assert alpha[j] == v[j] * w[j] + ealpha[j]
    assert abs(ealpha[j]) <= eps * abs(v[j]) * abs(w[j])
    assert z[j] == w[j] - alpha[j] * v[j]
    assert beta[j] * v[j + 1] == z[j]
    assert abs(v[j] ** 2 - 1) <= eps
# All vector arithmetic and normalization errors are zero.
theta = 1 - 2 * eps
direction = [Q(1), Q(-1)]
T = [[1 - eps, eps], [eps, 1 - eps]]
assert [sum(T[i][j] * direction[j] for j in range(2))
        for i in range(2)] == [theta * x for x in direction]
assert v[1] * direction[0] + v[2] * direction[1] == 0
print('PASS: model identities and bounds; beta_1 > 0; terminal beta_2 = 0; '
      'unit eigenvector direction has V_2 y = 0.')
