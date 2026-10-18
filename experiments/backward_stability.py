"""Numerical demonstration of the Greenbaum-type backward model.

A float32 Lanczos run (no reorthogonalization) on the Strakos matrix A loses
orthogonality completely.  We build the paper's backward model explicitly in
float64, following sec:backward step by step, and verify each claim:

  * normalization (sec:normalized): Vbar_{k+1} = [v_1/d_1, ..., v_{k+1}/d_{k+1}]
    has Gram matrix I + Rbar' + Rbar with Rbar strictly upper triangular, and
    T_k Rbar_k - Rbar_{k+1} T_k = [Mbar_k; 0'] with Mbar_k upper triangular
    and O(eps * ||A||) (cor:normalized-commutator);
  * nilpotent dilation (lem:dilation): with C = (I + Rbar_{k+1})^{-1},
    K = I - C, the (k+1)-block matrix
        Vhat_{k+1} = col(Vbar C, Vbar C K, ..., Vbar C K^k)
    has exactly orthonormal columns and first column col(vbar_1, 0, ..., 0);
  * exchange rule (lem:exchange): ||K_k|| <= 1, ||C_k|| <= 2, and
    T_k K_k^r - K_{k+1}^r T_k = J D_r with ||D_r|| <= r ||L_k||;
  * dilated recurrence (lem:dilated-recurrence): Ehat = Ahat Vhat_k
    - Vhat_{k+1} T_k has norm O(eps * ||A||), eps = float32 unit roundoff,
    even though the run's orthogonality is O(1);
  * backward model (thm:greenbaum): Delta = -Ehat Vhat_k' - Vhat_k Ehat'
    + Vhat_k (Vhat_k' Ahat Vhat_k - T_k) Vhat_k' is symmetric, Delta Vhat_k =
    -Ehat, ||Delta|| <= 2 ||Ehat||, and Atilde = Ahat + Delta satisfies
    Atilde Vhat_k = Vhat_{k+1} T_k exactly; exact Lanczos on (Atilde, vtilde),
    vtilde = col(vbar_1, 0, ..., 0), reproduces alpha_1..alpha_k and
    beta_1..beta_k, while exact Lanczos on (A, vbar_1) does not;
  * every eigenvalue of Atilde is within ||Delta|| of spec(A), and the weight
    of vtilde on the eigenvalues of Atilde in [lambda - ||Delta||,
    lambda + ||Delta||] is close to the weight of vbar_1 on lambda.

Here T_k denotes the (k+1) x k matrix [T_k; beta_k e_k'] where it multiplies
from the right, Ahat = I_{k+1} (x) A, and J = first k columns of I_{k+1}.
"Exact" Lanczos means float64 with full reorthogonalization.  The run and all
derived plotting data are saved to backward_stability_run.npz.  Run
plot_backward_stability.py separately to generate the four paper figures.
"""

from pathlib import Path

import numpy as np
from scipy.linalg import solve_triangular

here = Path(__file__).resolve().parent

rng = np.random.default_rng(0)


# ---------------------------------------------------------------- setup

def strakos_eigenvalues(n, lam1=0.1, lamn=100.0, rho=0.9):
    i = np.arange(1, n + 1)
    return lam1 + (i - 1) / (n - 1) * (lamn - lam1) * rho ** (n - i)


def lanczos_f32(A, v, kmax):
    """Paige's A1 variant, all kernels in float32, starting from nonzero v."""
    A = A.astype(np.float32)
    n = A.shape[0]
    V = np.zeros((n, kmax + 1), dtype=np.float32)
    alpha = np.zeros(kmax, dtype=np.float32)
    beta = np.zeros(kmax, dtype=np.float32)
    v = v.astype(np.float32)
    V[:, 0] = v / np.float32(np.sqrt(np.float32(v @ v)))
    beta_prev = np.float32(0.0)
    for j in range(kmax):
        u = A @ V[:, j]
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
A = np.diag(lam)
normA = np.max(np.abs(lam))
eps32 = np.finfo(np.float32).eps  # 2^-23

v = rng.standard_normal(n)
V, alpha32, beta32 = lanczos_f32(A, v, k)

Vk = V[:, :k].astype(np.float64)
Vkp = V.astype(np.float64)                                  # [V_k, v_{k+1}]
alpha = alpha32.astype(np.float64)
beta = beta32.astype(np.float64)
T = np.diag(alpha) + np.diag(beta[: k - 1], 1) + np.diag(beta[: k - 1], -1)
uT = np.vstack([T, beta[k - 1] * np.eye(k)[-1]])           # underline T_k
J = np.eye(k + 1)[:, :k]

loss = np.linalg.norm(Vk.T @ Vk - np.eye(k), 2)
Fk = A @ Vk - Vkp @ uT                                      # eq:governing

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
    residual_t = beta[t - 1] * np.abs(Yt[-1, :]) / normA
    overlap_t = np.abs(Xt.T @ V[:, t].astype(np.float64))
    paige_residual.extend(residual_t)
    paige_overlap.extend(overlap_t)
    paige_iteration.extend(np.full(t, t))
    lambda1_error.append(np.abs(theta_t[-1] - lam[0]) / normA)
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
print(f"Paige products: max o*s/(eps32*||A||) = "
      f"{np.max(paige_product) / eps32:.3f} over "
      f"{paige_product.size} Ritz pairs")

# ------------------------------------------------------- backward model

nrm = lambda X: np.linalg.norm(X, 2)

# normalization (sec:normalized): every v_j, j <= k+1, is scaled by its own
# norm; at a terminal step vbar_{k+1} is any unit vector
d = np.linalg.norm(Vkp, axis=0)
Vbar = Vkp / d                                              # Vbar_{k+1}
if beta[k - 1] == 0:
    Vbar[:, k] = np.eye(n)[:, 0]
Fbar = A @ Vbar[:, :k] - Vbar @ uT                          # eq:normalized-interface
G = Vbar.T @ Vbar                                           # eq:normalized-gram
Rbar = np.triu(G, 1)                                        # Rbar_{k+1}
Rbar_k = Rbar[:k, :k]
MM = uT @ Rbar_k - Rbar @ uT                                # eq:normalized-M-def
Mbar = MM[:k]

# nilpotent dilation (eq:CKsy, eq:dilation-def).  C is unit upper triangular;
# enforce the exact pattern so that K^{k+1} = 0 exactly.
K = -np.triu(solve_triangular(np.eye(k + 1) + Rbar, np.eye(k + 1),
                              unit_diagonal=True), 1)       # K_{k+1}
C = np.eye(k + 1) - K                                       # C_{k+1}
C_k, K_k = C[:k, :k], K[:k, :k]

Kpow = [np.eye(k + 1)]                                      # K_{k+1}^r, r = 0..k+1
for _ in range(k + 1):
    Kpow.append(Kpow[-1] @ K)
assert not np.any(Kpow[-1])
blocks = [Vbar @ C @ Kpow[r] for r in range(k + 1)]
Vhat_kp = np.vstack(blocks)                                 # (n (k+1)) x (k+1)
Vhat = Vhat_kp[:, :k]                                       # Vhat_k
vhat = Vhat_kp[:, k]                                        # vhat_{k+1}
N = n * (k + 1)
vtilde = np.zeros(N)                                        # model start vector
vtilde[:n] = Vbar[:, 0]

# exchange rule (lem:exchange): D_0 = 0, D_{r+1} = D_r K_k + K_k^r L_k
L_k = C_k @ Mbar @ C_k
D = [np.zeros((k, k))]
for r in range(k + 1):
    D.append(D[-1] @ K_k + Kpow[r][:k, :k] @ L_k)
exch_res = max(nrm(uT @ Kpow[r][:k, :k] - Kpow[r] @ uT - J @ D[r])
               for r in range(k + 2))
exch_ratio = max(nrm(D[r]) / (r * nrm(L_k)) for r in range(1, k + 2))

# dilated recurrence (lem:dilated-recurrence)
Ahat_Vhat = np.vstack([A @ blk[:, :k] for blk in blocks])   # (I_{k+1} (x) A) Vhat_k
Ehat = Ahat_Vhat - Vhat_kp @ uT
Er_res = max(nrm(Ehat[r * n:(r + 1) * n]
                 - Fbar @ C_k @ Kpow[r][:k, :k]
                 - Vbar[:, :k] @ (D[r] - D[r + 1]))
             for r in range(k + 1))

# symmetric correction (thm:greenbaum)
Ahat = np.kron(np.eye(k + 1), A)
Delta = (-Ehat @ Vhat.T - Vhat @ Ehat.T
         + Vhat @ (Vhat.T @ Ahat_Vhat - T) @ Vhat.T)
Atilde = Ahat + Delta                                       # the model matrix

# ------------------------------------------------------- verification

nD, nE = nrm(Delta), nrm(Ehat)
evals_At, evecs_At = np.linalg.eigh(Atilde)
dist_eig = np.abs(evals_At[:, None] - lam[None, :])

checks = [
    ("run:   loss of orthogonality ||Vk' Vk - I||", loss, "O(1): orthogonality is gone"),
    ("run:   ||F_k|| / ||A||", nrm(Fk) / normA, f"O(eps32) = O({eps32:.1e})"),
    ("lem:normalized-errors  ||Fbar_k|| / ||A||", nrm(Fbar) / normA, f"O(eps32)"),
    ("eq:normalized-gram  ||diag(Gbar) - 1||", np.max(np.abs(np.diag(G) - 1)), "float64 roundoff"),
    ("eq:normalized-M-def  last row; strict lower part of Mbar", (np.max(np.abs(MM[k])), np.max(np.abs(np.tril(Mbar, -1)))), "0 and 0"),
    ("cor:normalized-commutator  ||Mbar_k|| / ||A||", nrm(Mbar) / normA, f"O(eps32)"),
    ("lem:dilation  ||Vhat_{k+1}' Vhat_{k+1} - I||", nrm(Vhat_kp.T @ Vhat_kp - np.eye(k + 1)), "float64 roundoff"),
    ("lem:dilation  ||Vhat_{k+1} e1 - col(vbar_1, 0, ..., 0)||", np.linalg.norm(Vhat_kp[:, 0] - vtilde), "0"),
    ("lem:exchange  ||K_k||, ||C_k||", (nrm(K_k), nrm(C_k)), "<= 1 and <= 2"),
    ("lem:exchange  ||L_k|| / ||A||", nrm(L_k) / normA, "O(eps32)"),
    ("lem:exchange  max_r ||T K_k^r - K_{k+1}^r T - J D_r||", exch_res, "float64 roundoff"),
    ("lem:exchange  max_r ||D_r|| / (r ||L_k||)", exch_ratio, "<= 1"),
    ("lem:dilated-recurrence  ||Ehat|| / ||A||", nE / normA, f"O(eps32) = O({eps32:.1e})"),
    ("lem:dilated-recurrence  max_r ||E_r - (block formula)||", Er_res, "float64 roundoff"),
    ("thm:greenbaum  ||Delta - Delta'||", nrm(Delta - Delta.T), "float64 roundoff"),
    ("thm:greenbaum  ||Delta Vhat_k + Ehat||", nrm(Delta @ Vhat + Ehat), "float64 roundoff"),
    ("thm:greenbaum  ||Delta|| / (2 ||Ehat||)", nD / (2 * nE), "<= 1"),
    ("thm:greenbaum  ||Atilde Vhat_k - Vhat_{k+1} T||", nrm(Atilde @ Vhat - Vhat_kp @ uT), "float64 roundoff"),
    ("max dist(eig(Atilde), spec(A))", np.max(dist_eig.min(axis=1)), f"<= ||Delta|| = {nD:.2e}"),
]

print(f"Strakos matrix, n = {n}, k = {k}, ||A|| = {normA:g}, float32 run "
      f"(eps32 = {eps32:.2e})\n")
for label, val, expect in checks:
    val = ", ".join(f"{x:9.2e}" for x in np.atleast_1d(val))
    print(f"  {label:<60s} {val:>20s}   [{expect}]")

# --------------------------------------- exact Lanczos on the model

alpha_At, beta_At = lanczos_exact(Atilde, vtilde, k)
alpha_A, beta_A = lanczos_exact(A, Vbar[:, 0], k)

# compare alpha_1,...,alpha_k and beta_1,...,beta_k
dev_At = max(np.max(np.abs(alpha - alpha_At)), np.max(np.abs(beta - beta_At)))
dev_A = max(np.max(np.abs(alpha - alpha_A)), np.max(np.abs(beta - beta_A)))

print(f"""
Exact Lanczos versus the computed alpha_1..alpha_k, beta_1..beta_k
(max deviation):

  on (A, vbar_1):       {dev_A:9.2e}   (forward instability: the computed run
                                     does NOT track exact Lanczos on A)
  on (Atilde, vtilde):  {dev_At:9.2e}   (backward stability: the computed T_k
                                     IS the exact output for the nearby problem)

with ||Atilde - Ahat|| = ||Delta|| = {nD:.2e} <= 2 ||Ehat|| = {2 * nE:.2e}.
""")

# ------------------------------------------------------- plotting data

steps = np.arange(1, k + 1)
dev_a = np.abs(alpha - alpha_A)
dev_b = np.abs(beta - beta_A)
loss_j = np.array([np.linalg.norm(Vk[:, :j].T @ Vk[:, :j] - np.eye(j), 2)
                   for j in steps])

wts_At = (evecs_At.T @ vtilde) ** 2
wts_A = Vbar[:, 0] ** 2              # A is diagonal: eigenvectors are e_i

# cluster of lambda_i: eigenvalues of Atilde in [lambda_i - ||Delta||,
# lambda_i + ||Delta||]  (-1 if in none)
inside = dist_eig <= nD
assert np.all(inside.sum(axis=1) <= 1)
cluster = np.where(inside.any(axis=1), inside.argmax(axis=1), -1)
sizes = np.bincount(cluster[cluster >= 0], minlength=n)
cluster_wt = np.zeros(n)
np.add.at(cluster_wt, cluster[cluster >= 0], wts_At[cluster >= 0])
print(f"clusters: sizes in [{sizes.min()}, {sizes.max()}], "
      f"{np.sum(cluster < 0)} eigenvalues outside every cluster; "
      f"max |weight_Atilde - weight_A| = {np.max(np.abs(cluster_wt - wts_A)):.2e}, "
      f"relative {np.max(np.abs(cluster_wt - wts_A) / wts_A):.2e}")

run_path = here / "backward_stability_run.npz"
np.savez_compressed(
    run_path,
    format_version=np.int64(2),
    seed=np.int64(0),
    n=np.int64(n),
    k=np.int64(k),
    eps32=np.float64(eps32),
    normA=np.float64(normA),
    norm_Delta=np.float64(nD),
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
    evals_At=evals_At,
    wts_At=wts_At,
    wts_A=wts_A,
    cluster=cluster,
    cluster_wt=cluster_wt,
)
print(f"saved run and plotting data to {run_path.name}")
