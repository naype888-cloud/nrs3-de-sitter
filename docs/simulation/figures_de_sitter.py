"""Figures for the de Sitter horizon: Λ = 3π / (ℓ_P² S), the horizon and the scale factor."""

import numpy as np
import matplotlib.pyplot as plt

from style import OUT, BLUE, ORANGE, MUTED, INK2

L_P = 1.616255e-35            # Planck length [m]
C = 299792458.0               # speed of light [m/s]
MPC = 3.0856775814913673e22   # megaparsec [m]
GLY = 9.4607304725808e24      # gigalight-year [m]
GYR = 3.15576e16              # gigayear [s]
LAMBDA_OBS = 1.1056e-52       # Planck 2018 [m^-2]


def cosmological_constant(s):
    """`entropyCosmologicalConstant`: Λ = 3π / (ℓ_P² S)."""
    return 3 * np.pi / (L_P**2 * s)


S_OBS = 3 * np.pi / (L_P**2 * LAMBDA_OBS)


def figure_lambda():
    s = np.logspace(100, 130, 400)
    fig, ax = plt.subplots(figsize=(7.2, 4.3), dpi=150)
    ax.loglog(s, cosmological_constant(s), color=BLUE, lw=2.2, label=r"$\Lambda = 3\pi/(\ell_P^2 S)$")
    ax.scatter([S_OBS], [LAMBDA_OBS], color=ORANGE, zorder=3, s=42,
               label=r"Planck 2018: $\Lambda = 1.106\times10^{-52}\,\mathrm{m^{-2}}$")
    ax.axvline(S_OBS, color=ORANGE, lw=0.8, ls=":")
    ax.axhline(LAMBDA_OBS, color=ORANGE, lw=0.8, ls=":")
    ax.annotate(f"S = {S_OBS:.3e}", (S_OBS, LAMBDA_OBS), xytext=(12, 14),
                textcoords="offset points", color=ORANGE)
    ax.set_xlabel(r"horizon entropy $S/k_B$")
    ax.set_ylabel(r"$\Lambda$  [m$^{-2}$]")
    ax.set_title("The cosmological constant fixed by the horizon entropy")
    ax.legend(fontsize=9, loc="lower left")
    fig.tight_layout()
    fig.savefig(OUT / "lambda_entropy.png")
    plt.close(fig)


def figure_scale_factor():
    t = np.linspace(-30, 30, 400)
    fig, ax = plt.subplots(figsize=(7.2, 4.3), dpi=150)
    for s, color, ls, label in [(S_OBS, BLUE, "-", "S = S_obs"),
                                (2 * S_OBS, ORANGE, "--", "S = 2 S_obs"),
                                (S_OBS / 2, MUTED, "-.", "S = S_obs / 2")]:
        h = np.sqrt(cosmological_constant(s) / 3) * C
        ax.plot(t, np.exp(h * t * GYR), color=color, ls=ls, lw=2,
                label=f"{label}  (H = {h * MPC / 1e3:.1f} km/s/Mpc)")
    ax.set_yscale("log")
    ax.set_xlabel("t  [Gyr]")
    ax.set_ylabel(r"$a(t)/a_0$")
    ax.set_title("de Sitter scale factors solving both Friedmann equations")
    ax.legend(fontsize=9)
    fig.tight_layout()
    fig.savefig(OUT / "scale_factor.png")
    plt.close(fig)


def figure_horizon():
    s = np.logspace(110, 130, 300)
    fig, ax = plt.subplots(figsize=(7.2, 4.5), dpi=150)
    ax.loglog(s, np.sqrt(3 / cosmological_constant(s)) / GLY, color=BLUE, lw=2.2,
              label=r"$r_H = \sqrt{3/\Lambda} = c/|H|$  [Gly]")
    ax2 = ax.twinx()
    ax2.loglog(s, np.pi * C**2 / (L_P**2 * s), color=ORANGE, lw=2.2, ls="--",
               label=r"$H^2 = \pi c^2/(\ell_P^2 S)$  [s$^{-2}$]")
    ax2.grid(False)
    ax2.spines["right"].set_visible(True)
    ax.axvline(S_OBS, color=MUTED, lw=0.8, ls=":")
    ax.set_xlabel(r"horizon entropy $S/k_B$")
    ax.set_ylabel(r"$r_H$  [Gly]")
    ax2.set_ylabel(r"$H^2$  [s$^{-2}$]", color=INK2)
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, fontsize=9, loc="upper center", bbox_to_anchor=(0.5, -0.18), ncol=2)
    ax.set_title("Horizon radius and Hubble rate against the entropy")
    fig.tight_layout()
    fig.savefig(OUT / "horizon_hubble.png")
    plt.close(fig)


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    figure_lambda()
    figure_scale_factor()
    figure_horizon()
    h = np.sqrt(LAMBDA_OBS / 3) * C
    print(f"S_obs = {S_OBS:.4e}, r_H = {np.sqrt(3 / LAMBDA_OBS) / GLY:.2f} Gly, "
          f"H = {h * MPC / 1e3:.2f} km/s/Mpc")
