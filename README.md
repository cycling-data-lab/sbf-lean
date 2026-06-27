# sbf-lean — Lean 4 formalisation of Theorem 1

[![CI](https://github.com/cycling-data-lab/sbf-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/cycling-data-lab/sbf-lean/actions/workflows/ci.yml)
[![Lean 4 + Mathlib](https://img.shields.io/badge/Lean%204-Mathlib-blue.svg)](https://leanprover-community.github.io/)
[![proof: machine-checked](https://img.shields.io/badge/proof-machine--checked%20(zero%20sorry)-success.svg)](#sorry-free-certificate)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](./LICENSE)

Machine-checked (Lean 4 + Mathlib) formalisation of **Theorem 1** of
[**`structural-bounds-framework`**](https://github.com/cycling-data-lab/structural-bounds-framework),
notes/01 — the *Universal spectral lower bound* (Fossé–Pallares). This is the formal-proof
companion to that manuscript, living alongside it in `cycling-data-lab`.

## Result

`SbfLean/Basic.lean` proves, **with zero `sorry`**:

| Lean name | Paper statement |
|---|---|
| `SBF.transduction` | Lemma "Population–train–holdout": `SE_V = SE_T + SE_{Tᶜ}` |
| `SBF.bessel_sum` | Bessel-projection floor (coordinate-sum form) |
| `SBF.bessel_floor_proj` | Bessel floor for the **genuine** orthogonal projection `P_S y` |
| `SBF.lossOn_compl_eq` | The transduction rearrangement `L_{Tᶜ} = ρ·L_V − (ρ−1)·L_T` is an **identity** (forced `ρ = N/\|Tᶜ\|`), not an assumption |
| `SBF.one_le_rho` | The forced ratio `ρ = N/\|Tᶜ\| ≥ 1` |
| `SBF.universal_lower_bound` | **Theorem 1** (abstract floor): `floor ≤ E_T[L_{Tᶜ}(f̂)]` — the slacks cancel exactly |
| `SBF.universal_lower_bound_proj` | **Theorem 1** (geometric form): same bound with `floor := L_V(P_S y)` the *genuine* projection-`R²`, learner outputs assumed in `S` |
| `SBF.witness_saturates` | **Tightness**: the witness `P_S y` attains the floor exactly, `E_T[L_{Tᶜ}(P_S y)] = floor` |
| `SBF.lower_bound_tight` | **Two-sided**: bound holds for every admissible learner *and* the witness meets it with equality (conjunction) |
| `SBF.floor_eq_R2spec` | **Headline form**: `floor = (1 − R²_spec)·Var(y)` for non-constant `y`, with `Var`/`R²_spec` defined honestly in Lean |
| `SBF.erm_oracle` | **Theorem 2** (deterministic core): ERM excess population risk `L_V(fhat) ≤ floor + 2B` given a train-vs-population deviation bound `B` |
| `SBF.erm_population_sandwich` | **Saturation**: `floor ≤ L_V(fhat) ≤ floor + 2B` — ERM risk within the slack `2B` of the floor |

`floor = (1 − R²_spec(S,y))·Var(y) = L_V(P_S y, y)`.

Architecture: the core (transduction, Bessel, slack-cancellation) is **pure finite-sum
real algebra**; the *only* contact with Mathlib's analysis is `bessel_floor_proj`,
which discharges the Bessel orthogonality from `Submodule.starProjection_inner_eq_zero`,
so the floor is the real projection-`R²` (no assumed geometry).
`universal_lower_bound_proj` then *wires* `bessel_floor_proj` into the main theorem: it
discharges the abstract Bessel-floor (`hfit`) and witness-saturation (`hwit`) hypotheses
from the real orthogonal projection on `EuclideanSpace ℝ (Fin N)`, leaving only the
protocol / transduction / ERM hypotheses — the learner-specific assumptions the paper
actually makes.

The protocol's exchangeability `E_T[L_T(f)] = L_V(f)` is a hypothesis of the theorem,
exactly as in the paper ("for any protocol Π satisfying …").

### Sorry-free certificate

```
'SBF.universal_lower_bound'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.universal_lower_bound_proj' depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.witness_saturates'          depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.lower_bound_tight'          depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.floor_eq_R2spec'            depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.erm_oracle'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.erm_population_sandwich'    depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.bessel_sum'           depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.transduction'         depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.bessel_floor_proj'    depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.lossOn_compl_eq'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SBF.one_le_rho'           depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean axioms — **no `sorryAx`**.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get   # precompiled Mathlib oleans (first time only)
lake build
```

Toolchain: Lean `v4.31.0` (see `lean-toolchain`), Mathlib pinned in `lake-manifest.json`.

> Note: keep this project on the nvme/btrfs disk (`/home`). The build's `.lake`
> (~several GB of Mathlib oleans) must NOT live under `/tmp` or `$HOME`-tmpfs paths,
> which are RAM-backed with a ~6 GB quota on this machine.

## Not yet formalised

The **population-level** saturation (`E_T[L_{Tᶜ}(P_S y)] = floor`, `witness_saturates`) and
the **deterministic ERM oracle skeleton** of Theorem 2 (`erm_oracle` /
`erm_population_sandwich`, parametrised by an abstract deviation bound `B`) are done. What
remains is supplying the finite-sample *value* of `B` — the `2·R^trans_n + 23.1·M²·√(…)`
concentration term, which needs a Hoeffding–Serfling (sampling-without-replacement)
inequality not yet in Mathlib, plus tightening the paper's `O(·)`/`≈` steps — and the full
Theorem 3 (Berry–Esseen minimax). See the framework's notes/02.

## Siblings

- [`structural-bounds-framework`](https://github.com/cycling-data-lab/structural-bounds-framework)
  — **the manuscript this verifies** (paper + experiments); this repo is its formal-proof
  companion.
- [`od-lean`](https://github.com/cycling-data-lab/od-lean) — the same finite-algebra-core
  formalisation style applied to the GBFS OD identifiability bounds
  ([`gbfs-od-reconstruction`](https://github.com/cycling-data-lab/gbfs-od-reconstruction));
  shares the Mathlib olean cache (identical pin).
