"""Compare Greenbaum's extension construction with the paper's dilation.

Both constructions start from the SAME float32 Lanczos run (no
reorthogonalization) on the Strakos matrix used in backward_stability.py.

Extension (port of greenbaum_extension/extendT.m):
  identify converged Ritz / cluster vectors W (m of them), then continue the
  three-term recurrence in "exact" arithmetic (float64 with repeated explicit
  orthogonalization, standing in for vpa), orthogonalizing new vectors against
  W and against each other.  Result: tridiagonal T_ext of dimension
  N = n + k - m whose leading k x k block is the computed T_k, satisfying
  H Q = Q T_ext + F with F small.

Dilation (this paper): exact orthogonalization by nilpotent dilation plus
  symmetric completion.  Result: B of dimension n k with
  B V_hat = V_hat T_k + beta_bar v_hat e_k^T exactly, ||B - I_k (x) H|| <= 3||E_hat||.

Printed: side-by-side model dimension, perturbation size, eigenvalue
localization, starting-weight (cluster-weight) fidelity, and how well exact
Lanczos on the model reproduces the computed T_k.
"""

import numpy as np

rng = np.random.default_rng(0)

# ---------------------------------------------------------------- shared run
# (identical to backward_stability.py)


def strakos_eigenvalues(n, lam1=0.1, lamn=100.0, rho=0.9):
    i = np.arange(1, n + 1)
    return lam1 + (i - 1) / (n - 1) * (lamn - lam1) * rho ** (n - i)


def lanczos_f32(H, v, kmax):
    H = H.astype(np.float32)
    n = H.shape[0]
    V = np.zeros((n, kmax + 1), dtype=np.float32)
    alpha = np.zeros(kmax, dtype=np.float32)
    beta = np.zeros(kmax, dtype=np.float32)
    v = v.astype(np.float32)
    V[:, 0] = v / np.float32(np.sqrt(np.float32(v @ v)))
    beta_prev = np.float32(0.0)
    for j in range(kmax):
        u = H @ V[:, j]
        w = u - beta_prev * V[:, j - 1] if j > 0 else u
        alpha[j] = np.float32(w @ V[:, j])
        w = w - alpha[j] * V[:, j]
        beta[j] = np.float32(np.sqrt(np.float32(w @ w)))
        V[:, j + 1] = w / beta[j]
        beta_prev = beta[j]
    return V, alpha, beta


def lanczos_exact(A, q1, kmax):
    n = A.shape[0]
    Q = np.zeros((n, kmax + 1))
    alpha = np.zeros(kmax)
    beta = np.zeros(kmax)
    Q[:, 0] = q1 / np.linalg.norm(q1)
    for j in range(kmax):
        w = A @ Q[:, j]
        alpha[j] = w @ Q[:, j]
        w = w - alpha[j] * Q[:, j] - (beta[j - 1] * Q[:, j - 1] if j > 0 else 0)
        for _ in range(2):
            w -= Q[:, : j + 1] @ (Q[:, : j + 1].T @ w)
        beta[j] = np.linalg.norm(w)
        if beta[j] == 0:
            break
        Q[:, j + 1] = w / beta[j]
    return alpha, beta


def tridiag(a, b):
    return np.diag(a) + np.diag(b, 1) + np.diag(b, -1)


nrm = lambda A: np.linalg.norm(A, 2)

n, k = 64, 30
lam = strakos_eigenvalues(n, lam1=1e-3, lamn=1.0)[::-1]   # lambda_1 largest
H = np.diag(lam)
normA = np.max(np.abs(lam))

v = rng.standard_normal(n)
V, alpha32, beta32 = lanczos_f32(H, v, k)
Q = V.astype(np.float64)                     # n x (k+1), fp Lanczos vectors
Q /= np.linalg.norm(Q, axis=0)               # renormalize (as extendT does)
alpha = alpha32.astype(np.float64)
beta = beta32.astype(np.float64)
T = tridiag(alpha, beta[: k - 1])
wts_H = Q[:, 0] ** 2                          # weights of q1 (H is diagonal)


def cluster_weights(evals, evecs, q1):
    wts = (evecs.T @ q1) ** 2
    idx = np.argmin(np.abs(evals[:, None] - lam[None, :]), axis=1)
    total = np.zeros(n)
    np.add.at(total, idx, wts)
    return total


# ======================================================= Greenbaum extension

# eps1, eps2 as in extendT.m
FJ = H @ Q[:, :k] - Q[:, :k] @ T - beta[k - 1] * np.outer(Q[:, k], np.eye(k)[-1])
eps1 = np.max(np.linalg.norm(FJ, axis=0)) / normA
eps2 = np.max(np.abs(beta * np.sum(Q[:, :k] * Q[:, 1:k + 1], axis=0))) / normA
cluster_width = np.sqrt(max(eps1, eps2)) * normA

# Ritz pairs of T_k, bottom row of S made positive
theta, S = np.linalg.eigh(T)
S[:, S[-1] < 0] *= -1
Y = Q[:, :k] @ S

# replace clustered Ritz vectors by cluster vectors
YY = []
l1 = 0
for l in range(k):
    if l == k - 1 or theta[l + 1] - theta[l] > cluster_width:
        if l1 == l:
            YY.append(Y[:, l])
        else:
            c = S[-1, l1:l + 1]
            YY.append(Y[:, l1:l + 1] @ c / np.linalg.norm(c))
        l1 = l + 1
YY = np.array(YY).T
JJ = YY.shape[1]

# order by size of projection onto q_{k+1}; drop those with large projection
proj = np.abs(YY.T @ Q[:, k]) / np.linalg.norm(YY, axis=0)
order = np.argsort(proj)
YY = YY[:, order]
proj = proj[order]
m = JJ
while m >= 1 and proj[m - 1] > cluster_width / beta[k - 1]:
    m -= 1


def basis_and_errs(mm):
    if mm == 0:
        return np.zeros((n, 0)), beta[k - 1] * 0.0, beta[k - 1]
    W = np.linalg.svd(YY[:, :mm], full_matrices=False)[0]
    err1 = beta[k - 1] * np.linalg.norm(W.T @ Q[:, k])
    err2 = beta[k - 1] * np.linalg.norm(Q[:, k - 1] - W @ (W.T @ Q[:, k - 1]))
    return W, err1, err2


W, err1, err2 = basis_and_errs(m)
mbest, best = m, max(err1, err2)
mm = m
while mm > 1 and err1 > 100 * err2:          # remove vectors until balanced
    mm -= 1
    _, err1, err2 = basis_and_errs(mm)
    if max(err1, err2) < best:
        mbest, best = mm, max(err1, err2)
while mm < JJ and err2 > 100 * err1:         # add vectors until balanced
    mm += 1
    _, err1, err2 = basis_and_errs(mm)
    if max(err1, err2) < best:
        mbest, best = mm, max(err1, err2)
m = mbest
W, err1, err2 = basis_and_errs(m)
N = n + k - m

# continue the recurrence, orthogonalizing against W and the new vectors
Qe = np.zeros((n, N))
Qe[:, :k] = Q[:, :k]
alpha_e = list(alpha)
beta_e = list(beta[: k - 1])

vv = H @ Qe[:, k - 1] - alpha[k - 1] * Qe[:, k - 1] - beta[k - 2] * Qe[:, k - 2]
if m > 0:
    vv -= W @ (W.T @ vv)
beta_e.append(np.linalg.norm(vv))            # replaces computed beta_k
Qe[:, k] = vv / beta_e[-1]

for j in range(k, N - 1):
    w = H @ Qe[:, j] - beta_e[j - 1] * Qe[:, j - 1]
    a = w @ Qe[:, j]
    alpha_e.append(a)
    w = w - a * Qe[:, j]
    for _ in range(2):
        if m > 0:
            w -= W @ (W.T @ w)
        w -= Qe[:, k:j + 1] @ (Qe[:, k:j + 1].T @ w)
    beta_e.append(np.linalg.norm(w))
    Qe[:, j + 1] = w / beta_e[-1]
w = H @ Qe[:, N - 1] - beta_e[N - 2] * Qe[:, N - 2]
alpha_e.append(w @ Qe[:, N - 1])
w = w - alpha_e[-1] * Qe[:, N - 1]
for _ in range(2):
    if m > 0:
        w -= W @ (W.T @ w)
    w -= Qe[:, k:] @ (Qe[:, k:].T @ w)
beta_leftover = np.linalg.norm(w)            # should be ~ 0: space exhausted

T_ext = tridiag(np.array(alpha_e), np.array(beta_e))
F = H @ Qe - Qe @ T_ext                      # perturbed recurrence residual

WQ = np.hstack([W, Qe[:, k:]])
orth_ext = nrm(WQ.T @ WQ - np.eye(n))
ev_ext, evec_ext = np.linalg.eigh(T_ext)
dist_ext = np.max(np.abs(ev_ext[:, None] - lam[None, :]).min(axis=1))
wt_ext = cluster_weights(ev_ext, evec_ext, np.eye(N)[:, 0])
a_ext, b_ext = lanczos_exact(T_ext, np.eye(N)[:, 0], k)
dev_ext = max(np.max(np.abs(alpha - a_ext)), np.max(np.abs(beta[:k - 1] - b_ext[:k - 1])))

# ======================================================= paper's dilation

Vk = Q[:, :k] * np.linalg.norm(V[:, :k].astype(np.float64), axis=0)  # undo renorm
Vk = V[:, :k].astype(np.float64)
r = beta[k - 1] * V[:, k].astype(np.float64)
d = np.linalg.norm(Vk, axis=0)
Vbar = Vk / d
beta_bar = np.linalg.norm(r / d[-1])
vbar_next = (r / d[-1]) / beta_bar
G = Vbar.T @ Vbar
U = np.triu(G - np.eye(k), 1)
C = np.linalg.inv(np.eye(k) + U)
K = np.eye(k) - C
s = C @ (Vbar.T @ vbar_next)
y = vbar_next - Vbar @ s
blocks = [Vbar @ C]
for _ in range(1, k):
    blocks.append(blocks[-1] @ K)
Vhat = np.vstack(blocks)
vhat = np.concatenate([y] + [blocks[j] @ s for j in range(k - 1)])
ek = np.eye(k)[:, -1]
Ehat = np.vstack([H @ blk for blk in blocks]) - Vhat @ T - beta_bar * np.outer(vhat, ek)
Delta = -Ehat @ Vhat.T - Vhat @ Ehat.T + Vhat @ (Vhat.T @ Ehat) @ Vhat.T
B = np.kron(np.eye(k), H) + Delta

ev_B, evec_B = np.linalg.eigh(B)
dist_B = np.max(np.abs(ev_B[:, None] - lam[None, :]).min(axis=1))
wt_B = cluster_weights(ev_B, evec_B, Vhat[:, 0])
a_B, b_B = lanczos_exact(B, Vhat[:, 0], k)
dev_B = max(np.max(np.abs(alpha - a_B)), np.max(np.abs(beta[:k - 1] - b_B[:k - 1])))

# ======================================================= report

print(f"Same float32 run: Strakos matrix, n = {n}, k = {k}, ||H|| = {normA:g}, "
      f"eps32 = {np.finfo(np.float32).eps:.1e}")
print(f"extension internals: eps1 = {eps1:.2e}, eps2 = {eps2:.2e}, "
      f"cluster_width = {cluster_width:.2e}, m = {m} converged directions, "
      f"err1 = {err1:.2e}, err2 = {err2:.2e}\n")

rows = [
    ("model dimension", f"{n * k} (= nk)", f"{N} (= n + k - m)"),
    ("perturbation", f"{nrm(Delta):.2e}  (||Delta||, symmetric)",
     f"{np.linalg.norm(F):.2e}  (||F||_F, recurrence residual)"),
    ("model basis orthonormality", f"{nrm(Vhat.T @ Vhat - np.eye(k)):.2e}",
     f"{orth_ext:.2e}  ([W, Q_new]; first k cols stay non-orthogonal)"),
    ("leftover boundary beta", "0 (exact)", f"{beta_leftover:.2e}"),
    ("max dist(eig(model), spec(H))", f"{dist_B:.2e}", f"{dist_ext:.2e}"),
    ("max cluster-weight error", f"{np.max(np.abs(wt_B - wts_H)):.2e}",
     f"{np.max(np.abs(wt_ext - wts_H)):.2e}"),
    ("T_k embedded in tridiagonal model", "exact (thm; block of T_tilde)",
     "exact (by construction)"),
    ("  f64 check of the embedding", f"{dev_B:.2e}  (k Lanczos steps on dense B)",
     f"{dev_ext:.2e}  (reads off T_ext directly)"),
]
w1, w2 = 30, 40
print(f"{'':{w1}s}   {'dilation (paper)':{w2}s} extension (Greenbaum)")
for label, cb, ce in rows:
    print(f"{label:{w1}s}   {cb:{w2}s} {ce}")
