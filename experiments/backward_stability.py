"""Numerical demonstration of the Greenbaum-type backward model.

A float32 Lanczos run (no reorthogonalization) on the Strakos matrix loses
orthogonality completely.  We build the paper's backward model explicitly in
float64 -- normalization, nilpotent dilation, symmetric completion -- and
verify each claim of the backward theorem:

  * the dilated basis V_hat is exactly orthonormal, V_hat e_1 stacks v_1;
  * the dilated residual E_hat has norm O(eps * ||H||), eps = float32 unit
    roundoff, even though the run's orthogonality is O(1);
  * the correction Delta is symmetric with ||Delta|| <= 3 ||E_hat||, and
    B = H_hat + Delta satisfies the exact recurrence B V_hat = V_hat T_k
    + beta_bar v_hat e_k^T;
  * every eigenvalue of B is within ||Delta|| of spec(H)  (Weyl);
  * completing the basis gives an orthogonal U_hat, with first k columns
    V_hat, for which Ttilde = U_hat' B U_hat is tridiagonal with leading
    block exactly T_k;
  * exact Lanczos on (Ttilde, e_1) reproduces the computed T_k, while
    exact Lanczos on (H, v_1) does not.

"Exact" Lanczos means float64 with full reorthogonalization.  The run and all
derived plotting data are saved to backward_stability_run.npz.  Run
plot_backward_stability.py separately to generate the four paper figures.
"""

from pathlib import Path

import numpy as np

here = Path(__file__).resolve().parent

rng = np.random.default_rng(0)


# ---------------------------------------------------------------- setup

def strakos_eigenvalues(n, lam1=0.1, lamn=100.0, rho=0.9):
    i = np.arange(1, n + 1)
    return lam1 + (i - 1) / (n - 1) * (lamn - lam1) * rho ** (n - i)


def lanczos_f32(H, v, kmax):
    """Paige's A1 variant, all kernels in float32, starting from nonzero v."""
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
        if beta[j] == 0:
            raise RuntimeError("breakdown")
        V[:, j + 1] = w / beta[j]
        beta_prev = beta[j]
    return V, alpha, beta


def lanczos_exact(A, q1, kmax):
    """float64 Lanczos with twice-repeated full reorthogonalization."""
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


# ------------------------------------------------------- finite-precision run

n, k = 64, 30
# descending convention: lam[0] = lambda_1 is the LARGEST eigenvalue
lam = strakos_eigenvalues(n, lam1=1e-3, lamn=1.0)[::-1]
H = np.diag(lam)
normH = np.max(np.abs(lam))
eps32 = np.finfo(np.float32).eps  # 2^-23

v = rng.standard_normal(n)
V, alpha32, beta32 = lanczos_f32(H, v, k)

Vk = V[:, :k].astype(np.float64)
alpha = alpha32.astype(np.float64)
beta = beta32.astype(np.float64)
T = np.diag(alpha) + np.diag(beta[: k - 1], 1) + np.diag(beta[: k - 1], -1)
r = beta[k - 1] * V[:, k].astype(np.float64)  # beta_k v_{k+1}
ek = np.zeros(k)
ek[-1] = 1.0

loss = np.linalg.norm(Vk.T @ Vk - np.eye(k), 2)
Fk = H @ Vk - Vk @ T - np.outer(r, ek)

# ------------------------------------------------------- Paige figure

# For every prefix T_t and each of its Ritz pairs, evaluate the two factors in
# Paige's theorem using the stored vectors from this same float32 run.
paige_residual = []
paige_overlap = []
paige_iteration = []
lambda1_error = []
lambda1_overlap = []
for t in range(2, k + 1):
    Tt = (np.diag(alpha[:t])
          + np.diag(beta[:t - 1], 1)
          + np.diag(beta[:t - 1], -1))
    theta_t, Yt = np.linalg.eigh(Tt)
    Xt = Vk[:, :t] @ Yt
    residual_t = beta[t - 1] * np.abs(Yt[-1, :]) / normH
    overlap_t = np.abs(Xt.T @ V[:, t].astype(np.float64))
    paige_residual.extend(residual_t)
    paige_overlap.extend(overlap_t)
    paige_iteration.extend(np.full(t, t))
    lambda1_error.append(np.abs(theta_t[-1] - lam[0]) / normH)
    lambda1_overlap.append(overlap_t[-1])

lambda1_global_loss = [
    np.linalg.norm(Vk[:, :t].T @ Vk[:, :t] - np.eye(t), 2)
    for t in range(2, k + 1)
]

paige_residual = np.asarray(paige_residual)
paige_overlap = np.asarray(paige_overlap)
paige_iteration = np.asarray(paige_iteration)
paige_product = paige_residual * paige_overlap
lambda1_error = np.asarray(lambda1_error)
lambda1_overlap = np.asarray(lambda1_overlap)
lambda1_global_loss = np.asarray(lambda1_global_loss)
print(f"Paige products: max o*s/(eps32*||H||) = "
      f"{np.max(paige_product) / eps32:.3f} over "
      f"{paige_product.size} Ritz pairs")

# ------------------------------------------------------- backward model

# normalization
d = np.linalg.norm(Vk, axis=0)
Vbar = Vk / d
r_bar = r / d[-1]
beta_bar = np.linalg.norm(r_bar)
vbar_next = r_bar / beta_bar if beta_bar > 0 else np.eye(n)[:, 0]

# Gram triangle and nilpotent dilation
G = Vbar.T @ Vbar
U = np.triu(G - np.eye(k), 1)
a_vec = Vbar.T @ vbar_next
C = np.linalg.inv(np.eye(k) + U)
K = np.eye(k) - C
s = C @ a_vec
y = vbar_next - Vbar @ s

blocks = [Vbar @ C]
for _ in range(1, k):
    blocks.append(blocks[-1] @ K)
Vhat = np.vstack(blocks)                                   # (n k) x k
vhat = np.concatenate([y] + [blocks[j] @ s for j in range(k - 1)])

HVhat = np.vstack([H @ blk for blk in blocks])             # (I_k (x) H) V_hat
Ehat = HVhat - Vhat @ T - beta_bar * np.outer(vhat, ek)

# symmetric completion
Hhat = np.kron(np.eye(k), H)
VtE = Vhat.T @ Ehat
Delta = -Ehat @ Vhat.T - Vhat @ Ehat.T + Vhat @ VtE @ Vhat.T
B = Hhat + Delta

# Complete the basis as in the proof of lem:completion.  The recurrence already
# gives the first k Lanczos vectors and coefficients analytically, so preserve
# Vhat and T exactly and run the numerical completion only beyond that prefix.
N = n * k
Uhat = np.zeros((N, N))
Uhat[:, :k] = Vhat
diag_t = np.zeros(N)
off_t = np.zeros(N - 1)
diag_t[:k] = alpha
off_t[: k - 1] = beta[: k - 1]

# B Vhat[:, -1] has the known residual beta_bar * vhat orthogonal to Vhat.
# Normalize it to obtain the first vector beyond the prescribed prefix.
boundary_residual = beta_bar * vhat
boundary_norm = np.linalg.norm(boundary_residual)
breakdown_tol = 1e-14
if boundary_norm <= breakdown_tol:
    raise RuntimeError("breakdown at the boundary of the prescribed prefix")
off_t[k - 1] = boundary_norm
Uhat[:, k] = boundary_residual / boundary_norm

breakdown_events = []
for j in range(k, N):
    w = B @ Uhat[:, j]
    diag_t[j] = w @ Uhat[:, j]
    if j + 1 == N:
        break
    # full reorthogonalization against all previous columns, twice
    for _ in range(2):
        w -= Uhat[:, : j + 1] @ (Uhat[:, : j + 1].T @ w)
    nw = np.linalg.norm(w)
    if nw <= breakdown_tol:
        breakdown_events.append((j + 1, nw))
        # breakdown: restart from any direction orthogonal to what we have
        for cand in np.eye(N):
            r = cand - Uhat[:, : j + 1] @ (Uhat[:, : j + 1].T @ cand)
            r -= Uhat[:, : j + 1] @ (Uhat[:, : j + 1].T @ r)
            if np.linalg.norm(r) > 1e-8:
                w, nw = r, np.linalg.norm(r)
                break
        off_t[j] = 0.0
    else:
        off_t[j] = nw
    Uhat[:, j + 1] = w / nw
Ttilde = np.diag(diag_t) + np.diag(off_t, 1) + np.diag(off_t, -1)
assert np.array_equal(Ttilde[:k, :k], T)

# ------------------------------------------------------- verification

nrm = lambda A: np.linalg.norm(A, 2)
e1hat = np.zeros(n * k)
e1hat[:n] = Vbar[:, 0]

checks = [
    ("run:   loss of orthogonality  ||Vk' Vk - I||", loss, "O(1): orthogonality is gone"),
    ("run:   governing residual ||F_k|| / ||H||", nrm(Fk) / normH, f"O(eps32) = O({eps32:.1e})"),
    ("model: ||Vhat' Vhat - I||", nrm(Vhat.T @ Vhat - np.eye(k)), "float64 roundoff"),
    ("model: ||Vhat' vhat||,  ||vhat||", (nrm(Vhat.T @ vhat), np.linalg.norm(vhat)), "0 and <= 1"),
    ("model: ||Vhat e1 - stack(v1/||v1||)||", np.linalg.norm(Vhat[:, 0] - e1hat), "float64 roundoff"),
    ("model: ||K||  (nilpotent block)", nrm(K), "<= 1"),
    ("model: ||Ehat|| / ||H||", nrm(Ehat) / normH, f"O(eps32) = O({eps32:.1e})"),
    ("model: ||Delta|| / (3 ||Ehat||)", nrm(Delta) / (3 * nrm(Ehat)), "<= 1"),
    ("model: exact recurrence ||B Vhat - Vhat T - beta_bar vhat ek'||", nrm(B @ Vhat - Vhat @ T - beta_bar * np.outer(vhat, ek)), "float64 roundoff"),
    ("model: max dist(eig(B), spec(H))", np.max(np.abs(np.linalg.eigvalsh(B)[:, None] - lam[None, :]).min(axis=1)), f"<= ||Delta|| = {nrm(Delta):.2e}"),
    ("model: ||Uhat' Uhat - I||", nrm(Uhat.T @ Uhat - np.eye(N)), "float64 roundoff"),
    ("model: ||Uhat[:, :k] - Vhat||", nrm(Uhat[:, :k] - Vhat), "0: first k columns are Vhat"),
    ("model: ||Ttilde - Uhat' B Uhat||", nrm(Ttilde - Uhat.T @ B @ Uhat), "float64 roundoff"),
    ("model: Ttilde[:k, :k] bitwise equals T_k", float(np.array_equal(Ttilde[:k, :k], T)), "1: constructed analytically"),
    ("model: ||Uhat' Hhat Uhat - Ttilde||", nrm(Uhat.T @ Hhat @ Uhat - Ttilde), f"<= 3||Ehat|| = {3 * nrm(Ehat):.2e}"),
]

print(f"Strakos matrix, n = {n}, k = {k}, ||H|| = {normH:g}, float32 run "
      f"(eps32 = {eps32:.2e})\n")
if breakdown_events:
    print("  continuation restarts (step, residual norm): "
          + ", ".join(f"({j}, {nw:.2e})" for j, nw in breakdown_events)
          + "\n")
else:
    print("  continuation restarts: none\n")
for label, val, expect in checks:
    val = ", ".join(f"{x:9.2e}" for x in np.atleast_1d(val))
    print(f"  {label:<62s} {val:>22s}   [{expect}]")

# --------------------------------------- the theorem's "Consequently" clause

alpha_T, beta_T = lanczos_exact(Ttilde, np.eye(N)[:, 0], k)
alpha_H, beta_H = lanczos_exact(H, Vbar[:, 0], k)

# T_k contains alpha_1,...,alpha_k and beta_1,...,beta_{k-1}.  The final
# beta_k is the boundary coefficient and is not part of the prescribed block.
dev_T = max(np.max(np.abs(alpha - alpha_T)),
            np.max(np.abs(beta[: k - 1] - beta_T[: k - 1])))
dev_H = max(np.max(np.abs(alpha - alpha_H)),
            np.max(np.abs(beta[: k - 1] - beta_H[: k - 1])))
coeffs_match_bits = (np.array_equal(alpha_T, alpha)
                     and np.array_equal(beta_T[: k - 1], beta[: k - 1]))

print(f"""
Exact Lanczos versus the computed T_k (max deviation over its coefficients):

  on (H, v1):        {dev_H:9.2e}   (forward instability: the computed run does
                                  NOT track exact Lanczos on H)
  on (Ttilde, e1):   {dev_T:9.2e}   (backward stability: the computed T_k IS the
                                  exact output for the nearby problem;
                                  bitwise coefficient match: {coeffs_match_bits})

with ||B - Hhat|| = ||Delta|| = {nrm(Delta):.2e} <= 3 ||Ehat|| ~ eps32 ||H|| = {eps32 * normH:.2e}.
""")

# ------------------------------------------------------- plotting data

steps = np.arange(1, k + 1)
dev_a = np.abs(alpha - alpha_H)
dev_b = np.abs(beta - beta_H)
loss_j = np.array([np.linalg.norm(Vk[:, :j].T @ Vk[:, :j] - np.eye(j), 2)
                   for j in steps])

evals_T, evecs_T = np.linalg.eigh(Ttilde)
q = np.eye(N)[:, 0]                  # e_1, the starting vector of the model
wts_T = (evecs_T.T @ q) ** 2
wts_H = Vbar[:, 0] ** 2              # H is diagonal: eigenvectors are e_i

cluster = np.argmin(np.abs(evals_T[:, None] - lam[None, :]), axis=1)
cluster_wt = np.zeros(n)
np.add.at(cluster_wt, cluster, wts_T)
print(f"cluster weights: max |weight_Ttilde - weight_A| = "
      f"{np.max(np.abs(cluster_wt - wts_H)):.2e}")

run_path = here / "backward_stability_run.npz"
np.savez_compressed(
    run_path,
    format_version=np.int64(1),
    seed=np.int64(0),
    n=np.int64(n),
    k=np.int64(k),
    eps32=np.float64(eps32),
    normH=np.float64(normH),
    lam=lam,
    V=V,
    alpha=alpha,
    beta=beta,
    paige_residual=paige_residual,
    paige_overlap=paige_overlap,
    paige_iteration=paige_iteration,
    lambda1_error=lambda1_error,
    lambda1_overlap=lambda1_overlap,
    lambda1_global_loss=lambda1_global_loss,
    steps=steps,
    dev_a=dev_a,
    dev_b=dev_b,
    loss_j=loss_j,
    evals_T=evals_T,
    wts_T=wts_T,
    wts_H=wts_H,
    cluster=cluster,
    cluster_wt=cluster_wt,
)
print(f"saved run and plotting data to {run_path.name}")
