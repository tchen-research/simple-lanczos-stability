"""Generate the paper figures from a saved backward-stability run.

Run backward_stability.py once to create backward_stability_run.npz.  This
script only loads that data and plots it, so style and layout iterations avoid
repeating the numerical experiment.
"""

import os
from pathlib import Path

# LX Fonts lives in the older local TeX tree, while Matplotlib's DVI reader
# resolves metrics through the system kpsewhich.  Point both at the same tree.
os.environ.setdefault("TEXMFHOME", "/usr/local/texlive/2023/texmf-dist")
os.environ.setdefault("TEXMFSYSVAR", "/usr/local/texlive/2023/texmf-var")

import matplotlib.pyplot as plt
import numpy as np


HERE = Path(__file__).resolve().parent
RUN_PATH = HERE / "backward_stability_run.npz"


def configure_style():
    """Load the paper's LaTeX/LX plotting style."""
    plt.style.use(HERE / "oldstyle.mplstyle")


def load_run():
    if not RUN_PATH.exists():
        raise FileNotFoundError(
            f"{RUN_PATH.name} not found; run backward_stability.py first"
        )
    with np.load(RUN_PATH) as stored:
        if int(stored["format_version"]) != 2:
            raise ValueError("unsupported backward-stability run format")
        return {name: stored[name] for name in stored.files}


def save_figure(fig, filename):
    """Apply the common layout and save a publication figure."""
    fig.tight_layout()
    fig.savefig(HERE / filename, bbox_inches="tight")
    plt.close(fig)


def plot_paige_theorem(run):
    k = int(run["k"])
    eps32 = float(run["eps32"])
    paige_residual = run["paige_residual"]
    paige_overlap = run["paige_overlap"]
    paige_iteration = run["paige_iteration"]
    paige_product = paige_residual * paige_overlap

    fig, ax = plt.subplots(figsize=(4.7, 2.8))
    ax.set_xscale("log")
    ax.set_yscale("log")
    scatter = ax.scatter(
        paige_residual,
        paige_overlap,
        c=paige_iteration,
        cmap="Greys",
        vmin=-8,
        vmax=k,
        s=11,
        edgecolors="black",
        linewidths=0.25,
        zorder=3,
    )

    paige_x = np.logspace(-10, 0, 300)
    ax.plot(
        paige_x,
        eps32 / paige_x,
        "--",
        color="black",
        lw=0.9,
        label=r"$o\,s=\varepsilon$",
    )
    ax.set_xlim(3e-10, 1)
    ax.set_ylim(1e-9, 2)
    ax.set_xlabel(
        r"normalized scalar residual $s=\beta_t|\mathbf{e}_t^\mathsf{T}\mathbf{y}|/||\mathbf{A}||$"
    )
    ax.set_ylabel(
        r"orthogonality defect $o=|(\mathbf{V}_t\mathbf{y})^\mathsf{T}\mathbf{v}_{t+1}|$"
    )
    ax.legend(loc="lower left")
    ax.text(
        0.98,
        0.96,
        rf"$\max\;o\,s/\varepsilon={np.max(paige_product) / eps32:.2f}$",
        ha="right",
        va="top",
        transform=ax.transAxes,
    )

    colorbar = fig.colorbar(scatter, ax=ax, pad=0.025, aspect=24)
    colorbar.set_label(r"iteration $t$")
    colorbar.set_ticks([2, 10, 20, 30])
    save_figure(fig, "paige_theorem.pdf")


def plot_lambda1(run):
    k = int(run["k"])
    lambda1_steps = np.arange(2, k + 1)
    fig, axes = plt.subplots(1, 3, figsize=(6.2, 2.2), sharey=True)
    for ax, values, title in [
        (
            axes[0],
            run["lambda1_error"],
            r"$|\theta_1^{(t)}-\lambda_1|/||\mathbf{A}||$",
        ),
        (
            axes[1],
            run["lambda1_overlap"],
            r"$|(\mathbf{V}_t\mathbf{y}_1^{(t)})^\mathsf{T}\mathbf{v}_{t+1}|$",
        ),
        (
            axes[2],
            run["lambda1_global_loss"],
            r"$||\mathbf{V}_t^\mathsf{T}\mathbf{V}_t-\mathbf{I}||$",
        ),
    ]:
        ax.semilogy(
            lambda1_steps,
            values,
            "o-",
            markerfacecolor="white",
            markeredgecolor="black",
        )
        ax.set_xlim(2, k)
        ax.set_ylim(1e-9, 2)
        ax.set_xlabel(r"iteration $t$")
        ax.set_title(title, fontsize=9)
    axes[0].set_ylabel(r"magnitude")
    save_figure(fig, "paige_lambda1.pdf")


def plot_backward_errors(run):
    fig, axes = plt.subplots(1, 3, figsize=(6.2, 2.2), sharey=True)
    for ax, data, title in [
        (axes[0], run["dev_a"], r"$|\alpha_j-\alpha_j^{\mathrm{exact}}|$"),
        (axes[1], run["dev_b"], r"$|\beta_j-\beta_j^{\mathrm{exact}}|$"),
        (
            axes[2],
            run["loss_j"],
            r"$||\mathbf{V}_j^\mathsf{T}\mathbf{V}_j-\mathbf{I}||$",
        ),
    ]:
        ax.semilogy(
            run["steps"],
            data,
            "o-",
            markerfacecolor="white",
            markeredgecolor="black",
        )
        ax.set_title(title, fontsize=9)
        ax.set_xlabel(r"iteration $j$")
        ax.set_ylim(1e-10, 1e1)
    save_figure(fig, "backward_stability.pdf")


def plot_spectral_measure(run):
    lam = run["lam"]
    evals_At = run["evals_At"]
    wts_At = run["wts_At"]
    wts_A = run["wts_A"]
    cluster = run["cluster"]
    cluster_wt = run["cluster_wt"]

    fig, axes = plt.subplots(
        1,
        4,
        figsize=(6.2, 2.4),
        sharey=True,
        gridspec_kw={"width_ratios": [2.4, 1, 1, 1]},
    )
    overview = axes[0]
    ylo = 1e-16

    overview.vlines(
        lam,
        ylo,
        wts_A,
        color="black",
        lw=0.8,
        label=r"weight of $\bar{\mathbf{v}}_1$ on $\lambda_i(\mathbf{A})$",
    )
    overview.plot(
        lam,
        cluster_wt,
        "o",
        color="black",
        ms=4,
        markerfacecolor="white",
        markeredgecolor="black",
        markeredgewidth=0.8,
        label=r"cluster weight of $\widetilde{\mathbf{v}}$ on $\widetilde{\mathbf{A}}$",
    )
    overview.set_xscale("log")
    overview.set_yscale("log")
    overview.set_ylim(ylo, 3e0)
    overview.set_xlabel(r"eigenvalue")
    overview.set_ylabel(r"weight")
    legend = overview.legend(
        loc="lower left",
        frameon=True,
        fancybox=False,
        framealpha=1.0,
        facecolor="white",
        edgecolor="black",
    )
    legend.get_frame().set_linewidth(0.6)

    half = 1e-7
    for ax, i0 in zip(axes[1:], [0, 1, 2]):
        members = cluster == i0
        theta = evals_At[members]
        weights = np.maximum(wts_At[members], ylo)
        ax.vlines(theta, ylo, weights, color="black", lw=0.8, zorder=1)
        ax.plot(theta, np.full(theta.shape, 3 * ylo), "|", color="black", ms=6)
        ax.vlines(lam[i0], ylo, wts_A[i0], color="black", lw=1.3)
        ax.plot(
            theta,
            weights,
            "o",
            color="black",
            ms=4,
            markerfacecolor="white",
            markeredgecolor="black",
            markeredgewidth=0.8,
            zorder=3,
        )
        ax.set_yscale("log")
        ax.set_xlim(lam[i0] - 1.5 * half, lam[i0] + 1.5 * half)
        label = i0 + 1
        ax.set_xticks([lam[i0] - half, lam[i0] + half])
        ax.set_xticklabels(
            [
                rf"$\lambda_{{{label}}}{{-}}10^{{-7}}$",
                rf"$\lambda_{{{label}}}{{+}}10^{{-7}}$",
            ]
        )

    save_figure(fig, "spectral_measure.pdf")


def main():
    configure_style()
    run = load_run()
    plot_paige_theorem(run)
    plot_lambda1(run)
    plot_backward_errors(run)
    plot_spectral_measure(run)
    print(
        "figures saved to backward_stability.pdf, paige_theorem.pdf, "
        "paige_lambda1.pdf, spectral_measure.pdf"
    )


if __name__ == "__main__":
    main()
