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
  * exact Lanczos on (B, V_hat e_1) reproduces the computed T_k, while
    exact Lanczos on (H, v_1) does not.

"Exact" Lanczos means float64 with full reorthogonalization.

Saves four figures for inclusion in the paper.  In particular,
paige_theorem.pdf evaluates Paige's product on every Ritz pair of every prefix
of the same finite-precision run used by the backward-stability figures, while
paige_lambda1.pdf follows only the Ritz approximation to the largest eigenvalue.
"""

import os
import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib import font_manager

here = os.path.dirname(os.path.abspath(__file__))

# A newly installed user font may not yet appear in Matplotlib's cached font
# list.  Register Routed Gothic explicitly so the style never falls back.
for font_path in font_manager.findSystemFonts():
    if Path(font_path).name.casefold() == "routed-gothic.ttf":
        font_manager.fontManager.addfont(font_path)
        break
else:
    raise RuntimeError("Routed Gothic is required by oldstyle.mplstyle")

plt.style.use(os.path.join(here, "oldstyle.mplstyle"))

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
print(f"Paige products: max o*s/(eps32*||H||) = "
      f"{np.max(paige_product) / eps32:.3f} over "
      f"{paige_product.size} Ritz pairs")

figp, axp = plt.subplots(figsize=(4.7, 2.8))
axp.set_xscale("log")
axp.set_yscale("log")
sc = axp.scatter(paige_residual, paige_overlap,
                 c=paige_iteration, cmap="Greys", vmin=-8, vmax=k,
                 s=11, edgecolors="black", linewidths=0.25, zorder=3)

paige_x = np.logspace(-10, 0, 300)
axp.plot(paige_x, eps32 / paige_x, "--", color="black", lw=0.9,
         label=r"$o\,s=\varepsilon$")
axp.set_xlim(3e-10, 1)
axp.set_ylim(1e-9, 2)
axp.set_xlabel(
    r"normalized scalar residual $s=\beta_t|\mathbf{e}_t^\mathsf{T}\mathbf{y}|/||\mathbf{A}||$")
axp.set_ylabel(
    r"orthogonality defect $o=|(\mathbf{V}_t\mathbf{y})^\mathsf{T}\mathbf{v}_{t+1}|$")
axp.legend(loc="lower left")
axp.text(0.98, 0.96,
         rf"$\max\;o\,s/\varepsilon={np.max(paige_product) / eps32:.2f}$",
         ha="right", va="top", transform=axp.transAxes)

cbar = figp.colorbar(sc, ax=axp, pad=0.025, aspect=24)
cbar.set_label(r"iteration $t$")
cbar.set_ticks([2, 10, 20, 30])

figp.tight_layout()
figp.savefig(os.path.join(here, "paige_theorem.pdf"),
             bbox_inches="tight")

# A simpler trajectory for just the largest Ritz pair, which approximates
# lambda_1 = 1 throughout this run.
lambda1_steps = np.arange(2, k + 1)
figl, lambda_axes = plt.subplots(1, 3, figsize=(6.2, 2.2), sharey=True)
for ax, values, title in [
        (lambda_axes[0], lambda1_error,
         r"$|\theta_1^{(t)}-\lambda_1|/||\mathbf{A}||$"),
        (lambda_axes[1], lambda1_overlap,
         r"$|(\mathbf{V}_t\mathbf{y}_1^{(t)})^\mathsf{T}\mathbf{v}_{t+1}|$"),
        (lambda_axes[2], lambda1_global_loss,
         r"$||\mathbf{V}_t^\mathsf{T}\mathbf{V}_t-\mathbf{I}||$")]:
    ax.semilogy(lambda1_steps, values, "o-",
                markerfacecolor="white", markeredgecolor="black")
    ax.set_xlim(2, k)
    ax.set_ylim(1e-9, 2)
    ax.set_xlabel(r"iteration $t$")
    ax.set_title(title, fontsize=9)
lambda_axes[0].set_ylabel(r"magnitude")
figl.tight_layout()
figl.savefig(os.path.join(here, "paige_lambda1.pdf"),
             bbox_inches="tight")

if "--paige-only" in sys.argv:
    print("figures saved to paige_theorem.pdf, paige_lambda1.pdf")
    raise SystemExit(0)

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
]

print(f"Strakos matrix, n = {n}, k = {k}, ||H|| = {normH:g}, float32 run "
      f"(eps32 = {eps32:.2e})\n")
for label, val, expect in checks:
    val = ", ".join(f"{x:9.2e}" for x in np.atleast_1d(val))
    print(f"  {label:<62s} {val:>22s}   [{expect}]")

# --------------------------------------- the theorem's "Consequently" clause

alpha_B, beta_B = lanczos_exact(B, Vhat[:, 0], k)
alpha_H, beta_H = lanczos_exact(H, Vbar[:, 0], k)

dev_B = max(np.max(np.abs(alpha - alpha_B)), np.max(np.abs(beta - beta_B)))
dev_H = max(np.max(np.abs(alpha - alpha_H)), np.max(np.abs(beta - beta_H)))

print(f"""
Exact Lanczos versus the computed T_k (max deviation over all alpha_j, beta_j):

  on (H, v1):        {dev_H:9.2e}   (forward instability: the computed run does
                                  NOT track exact Lanczos on H)
  on (B, Vhat e1):   {dev_B:9.2e}   (backward stability: the computed T_k IS the
                                  exact output for the nearby matrix B)

with ||B - Hhat|| = ||Delta|| = {nrm(Delta):.2e} <= 3 ||Ehat|| ~ eps32 ||H|| = {eps32 * normH:.2e}.
""")

# ------------------------------------------------------- figure 1

steps = np.arange(1, k + 1)
dev_a = np.abs(alpha - alpha_H)
dev_b = np.abs(beta - beta_H)
loss_j = np.array([np.linalg.norm(Vk[:, :j].T @ Vk[:, :j] - np.eye(j), 2)
                   for j in steps])

fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(6.2, 2.2), sharey=True)
ylim = (1e-10, 1e1)

for ax, data, title in [
        (ax1, dev_a,
         r"$|\alpha_j-\alpha_j^{\mathrm{exact}}|$"),
        (ax2, dev_b,
         r"$|\beta_j-\beta_j^{\mathrm{exact}}|$"),
        (ax3, loss_j,
         r"$||\mathbf{V}_j^\mathsf{T}\mathbf{V}_j-\mathbf{I}||$")]:
    ax.semilogy(steps, data, "o-", markerfacecolor="white",
                markeredgecolor="black")
    ax.set_title(title, fontsize=9)
    ax.set_xlabel(r"iteration $j$")
    ax.set_ylim(ylim)

fig.tight_layout()
fig.savefig(os.path.join(here, "backward_stability.pdf"),
            bbox_inches="tight")

# ------------------------------------------------------- spectral figure

evals_B, evecs_B = np.linalg.eigh(B)
q = Vhat[:, 0]                       # = V_hat e_1, the model starting vector
wts_B = (evecs_B.T @ q) ** 2
wts_H = Vbar[:, 0] ** 2              # H is diagonal: eigenvectors are e_i

cluster = np.argmin(np.abs(evals_B[:, None] - lam[None, :]), axis=1)
mass = np.zeros(n)
np.add.at(mass, cluster, wts_B)
print(f"cluster masses: max |mass_B - weight_H| = "
      f"{np.max(np.abs(mass - wts_H)):.2e}")

fig2, axes = plt.subplots(1, 4, figsize=(6.2, 2.4), sharey=True,
                          gridspec_kw={"width_ratios": [2.4, 1, 1, 1]})
bx1 = axes[0]
ylo = 1e-16

bx1.vlines(lam, ylo, wts_H, color="black", lw=0.8,
           label=r"weight of $\bar{\mathbf{v}}_1$ on $\lambda_i(\mathbf{A})$")
bx1.plot(lam, mass, "x", color="black", ms=4, mew=0.9,
         label=r"cluster mass of $\widehat{\mathbf{V}}\mathbf{e}_1$ on $\mathbf{B}$")
bx1.set_xscale("log")
bx1.set_yscale("log")
bx1.set_ylim(ylo, 3e0)
bx1.set_xlabel(r"eigenvalue")
bx1.set_ylabel(r"weight")
legend = bx1.legend(loc="lower left", frameon=True, fancybox=False,
                    framealpha=1.0, facecolor="white", edgecolor="black")
legend.get_frame().set_linewidth(0.6)

half = 1e-7
for ax, i0 in zip(axes[1:], [0, 1, 2]):
    mem = cluster == i0
    th = evals_B[mem]
    ax.vlines(th, ylo, np.maximum(wts_B[mem], ylo), color="black", lw=0.8)
    ax.plot(th, np.maximum(wts_B[mem], ylo), "x", color="black", ms=4,
            mew=0.9)
    ax.plot(th, np.full(th.shape, 3 * ylo), "|", color="black", ms=6)
    ax.vlines(lam[i0], ylo, wts_H[i0], color="black", lw=1.3)
    ax.set_yscale("log")
    ax.set_xlim(lam[i0] - 1.4 * half, lam[i0] + 1.4 * half)
    lbl = i0 + 1
    ax.set_xticks([lam[i0] - half, lam[i0], lam[i0] + half])
    ax.set_xticklabels([rf"$\lambda_{{{lbl}}}{{-}}10^{{-7}}$",
                        rf"$\lambda_{{{lbl}}}$",
                        rf"$\lambda_{{{lbl}}}{{+}}10^{{-7}}$"], fontsize=6)
    # Matplotlib normally aligns tick labels by the tops of their bounding
    # boxes.  Superscripts make the side labels taller than the center label,
    # so align all three on their mathematical baselines instead.
    for tick_label in ax.get_xticklabels():
        tick_label.set_verticalalignment("baseline")
        tick_label.set_y(-0.08)

fig2.tight_layout()
fig2.savefig(os.path.join(here, "spectral_measure.pdf"),
             bbox_inches="tight")
print("figures saved to backward_stability.pdf, paige_theorem.pdf, "
      "paige_lambda1.pdf, spectral_measure.pdf")
