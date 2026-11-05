"""Reproduce the article figure and run numerical cross-checks (not proofs).

Requirements: numpy, matplotlib. Run: python3 verify_model.py
All random checks use seed 20261026. The figure uses exact analytic formulas.
"""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
rng = np.random.default_rng(20261026)


def triangle(r, a, b, c):
    return np.array([[1, r*np.exp(1j*a), r*np.exp(-1j*c)],
                     [r*np.exp(-1j*a), 1, r*np.exp(1j*b)],
                     [r*np.exp(1j*c), r*np.exp(-1j*b), 1]])


def frame(m, d):
    z = rng.normal(size=(m, d)) + 1j*rng.normal(size=(m, d))
    # Stable SVD evaluation of the polar formula z (z* z)^(-1/2).
    u, _, vh = np.linalg.svd(z, full_matrices=False)
    return u @ vh


max_det_error = 0.0
for _ in range(1000):
    r = rng.uniform(0, 1)
    a, b, c = rng.uniform(-np.pi, np.pi, 3)
    actual = np.linalg.det(triangle(r, a, b, c))
    expected = (1-r)**2*(1+2*r)-4*r**3*np.sin((a+b+c)/2)**2
    max_det_error = max(max_det_error, abs(actual-expected))
    assert abs(actual-expected) < 1e-12
    if r <= .5:
        assert np.linalg.eigvalsh(triangle(r, a, b, c)).min() > -1e-12

max_bound_violation = 0.0
max_exact_composition_error = 0.0
for d in [1, 2, 3]:
    for _ in range(100):
        m = 3*d+1
        v = [frame(m, d) for _ in range(3)]
        k = [[x.conj().T @ y for y in v] for x in v]
        delta = lambda i, j: max(0, d-np.linalg.norm(k[i][j], 'fro')**2)
        defect_sq = np.linalg.norm(k[0][2]-k[0][1]@k[1][2], 'fro')**2
        bound = delta(0, 1)*delta(1, 2)
        max_bound_violation = max(max_bound_violation, defect_sq-bound)
        assert defect_sq <= bound+1e-10
        block = np.block(k)
        assert np.linalg.eigvalsh(block).min() > -1e-10
        w = frame(m, d)
        q = [frame(d, d) for _ in range(3)]
        vv = [w @ z for z in q]
        kk = [[x.conj().T @ y for y in vv] for x in vv]
        err = np.linalg.norm(kk[0][1]@kk[1][2]-kk[0][2], 'fro')
        max_exact_composition_error = max(max_exact_composition_error, err)
        assert err < 1e-12

r = np.linspace(0, 1, 1501)
allowance = np.ones_like(r)
mask = r > .5
allowance[mask] = np.clip((1-r[mask])*np.sqrt(1+2*r[mask])/(2*r[mask]**1.5), 0, 1)
phi = 2*np.arcsin(allowance)
accept = phi/np.pi
plt.rcParams.update({"font.family":"DejaVu Sans", "font.size":10,
                     "axes.spines.top":False, "axes.spines.right":False})
fig, axes = plt.subplots(1, 2, figsize=(9.0, 3.2), constrained_layout=True)
axes[0].fill_between(r, -phi/np.pi, phi/np.pi, color="#b9d8e8")
axes[0].plot(r, phi/np.pi, color="#175575", linewidth=1.8)
axes[0].plot(r, -phi/np.pi, color="#175575", linewidth=1.8)
axes[0].set(xlabel="Overlap magnitude r", ylabel=r"Allowed wrapped flux $\Phi/\pi$",
            title="Positivity restricts the loop phase", xlim=(0,1), ylim=(-1.05,1.05))
axes[1].plot(r, accept, color="#175575", linewidth=2)
axes[1].set(xlabel="Overlap magnitude r", ylabel="Acceptance probability",
            title="Independent uniform edge phases", xlim=(0,1), ylim=(0,1.05))
for ax in axes:
    ax.axvline(.5, color=".5", linestyle="--", linewidth=.8)
    ax.grid(alpha=.15)
fig.savefig(ROOT/"triangle_constraint.pdf", bbox_inches="tight")
fig.savefig(ROOT/"triangle_constraint.png", dpi=180, bbox_inches="tight")
plt.close(fig)

result = {"seed":20261026, "triangle_checks":1000,
          "random_block_checks":300, "saturated_block_checks":300,
          "maximum_determinant_error":float(max_det_error),
          "maximum_bound_violation":float(max_bound_violation),
          "maximum_exact_composition_error":float(max_exact_composition_error),
          "status":"PASS", "role":"Numerical cross-checks, not formal proofs"}
(ROOT/"NUMERICAL_CHECKS.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
