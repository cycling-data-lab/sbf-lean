import Mathlib

/-!
# Universal spectral lower bound (Theorem 1)

Lean 4 / Mathlib formalisation of Theorem 1 of Fossé–Pallares,
`structural-bounds-framework`, notes/01 ("Universal spectral lower bound").

Architecture (zero `sorry`):
* The heart — Bessel floor (`bessel_sum`), transduction (`transduction`) and the
  slack-cancellation (`universal_lower_bound`) — is **pure finite-sum real algebra**.
* The only contact with Mathlib's geometry is `bessel_floor_proj`, which discharges
  the Bessel orthogonality for the **genuine** orthogonal projection
  (`Submodule.starProjection`), so the floor really is the projection-`R²`.
-/

set_option linter.style.header false

open Finset

namespace SBF

variable {N : ℕ}

/-- Total (un-normalised) squared error of predictor `f` against target `y` on a set. -/
def SE (S : Finset (Fin N)) (f y : Fin N → ℝ) : ℝ := ∑ v ∈ S, (f v - y v) ^ 2

/-- Population loss on all `N` nodes. -/
noncomputable def LV (f y : Fin N → ℝ) : ℝ := (N : ℝ)⁻¹ * SE univ f y

/-- Mean squared-error loss on a node subset. -/
noncomputable def lossOn (S : Finset (Fin N)) (f y : Fin N → ℝ) : ℝ :=
  (S.card : ℝ)⁻¹ * SE S f y

/-- **Transduction identity** (notes/01, "Population–train–holdout"): the total error
splits over `T` and its complement. Pure counting. -/
lemma transduction (T : Finset (Fin N)) (f y : Fin N → ℝ) :
    SE univ f y = SE T f y + SE Tᶜ f y := by
  classical
  simp only [SE]
  exact (Finset.sum_add_sum_compl T (fun v => (f v - y v) ^ 2)).symm

/-- **Bessel-projection floor** (notes/01) in pure coordinate-sum form: if the residual
`y - p` is orthogonal to `f - p` (coordinate inner product), then `p` is at least as
close to `y` as `f`. The sole geometric content of Theorem 1, reduced to finite-sum
algebra. -/
lemma bessel_sum (y p f : Fin N → ℝ)
    (hortho : ∑ v, (y v - p v) * (f v - p v) = 0) :
    SE univ p y ≤ SE univ f y := by
  have hcross : (∑ v, (f v - p v) * (p v - y v)) = 0 := by
    have hsum0 :
        (∑ v, ((f v - p v) * (p v - y v) + (y v - p v) * (f v - p v))) = 0 :=
      Finset.sum_eq_zero (fun v _ => by ring)
    rw [Finset.sum_add_distrib, hortho, add_zero] at hsum0
    exact hsum0
  have hexp : SE univ f y
      = SE univ p y + 2 * (∑ v, (f v - p v) * (p v - y v)) + (∑ v, (f v - p v) ^ 2) := by
    simp only [SE]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hnn : 0 ≤ ∑ v, (f v - p v) ^ 2 := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  rw [hexp, hcross]; linarith

/-- An evaluation protocol: a finite weighted family of train sets whose induced mean
loss equals the population loss on every deterministic predictor (exchangeability). -/
structure Protocol (N : ℕ) where
  sets : Finset (Finset (Fin N))
  w : Finset (Fin N) → ℝ
  w_nonneg : ∀ T ∈ sets, 0 ≤ w T
  w_sum : ∑ T ∈ sets, w T = 1
  unbiased : ∀ (f y : Fin N → ℝ), ∑ T ∈ sets, w T * lossOn T f y = LV f y

/-- Expectation under the protocol. -/
noncomputable def Protocol.E (P : Protocol N) (g : Finset (Fin N) → ℝ) : ℝ :=
  ∑ T ∈ P.sets, P.w T * g T

lemma Protocol.E_mono (P : Protocol N) {g h : Finset (Fin N) → ℝ}
    (hgh : ∀ T ∈ P.sets, g T ≤ h T) : P.E g ≤ P.E h :=
  Finset.sum_le_sum (fun T hT => mul_le_mul_of_nonneg_left (hgh T hT) (P.w_nonneg T hT))

lemma Protocol.E_const (P : Protocol N) (c : ℝ) : P.E (fun _ => c) = c := by
  unfold Protocol.E
  rw [← Finset.sum_mul, P.w_sum, one_mul]

lemma Protocol.E_smul_add (P : Protocol N) (a b : ℝ) (g h : Finset (Fin N) → ℝ) :
    P.E (fun T => a * g T + b * h T) = a * P.E g + b * P.E h := by
  unfold Protocol.E
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun T _ => by ring)

/--
**Theorem 1 — Universal spectral lower bound** (notes/01, eq. thm-lower).

`floor` stands for `(1 − R²_spec(S,y))·Var(y) = LV(pStar, y)`, where `pStar = P_S y`.
Hypotheses mirror the paper:
* `htrans`  : transduction rearranged, `L_{T^c} = ρ·L_V − (ρ−1)·L_T`;
* `hfit`    : Bessel floor for the learner (A3), `floor ≤ L_V(fhat T)`;
* `herm`    : ERM (A2), train loss `≤` witness `pStar` train loss;
* `hwit`    : the witness saturates the floor, `L_V(pStar) = floor`;
* `P.unbiased` : protocol exchangeability;
* `hρ`      : `ρ ≥ 1`.

Conclusion: `floor ≤ E_T[L_{T^c}(fhat T)]` — the expected leave-node-out loss is at
least the spectral floor, with the two slacks cancelling exactly. -/
theorem universal_lower_bound
    (P : Protocol N)
    (y : Fin N → ℝ) (fhat : Finset (Fin N) → (Fin N → ℝ)) (pStar : Fin N → ℝ)
    (ρ floor : ℝ)
    (htrans : ∀ T ∈ P.sets,
        lossOn Tᶜ (fhat T) y = ρ * LV (fhat T) y - (ρ - 1) * lossOn T (fhat T) y)
    (hfit : ∀ T ∈ P.sets, floor ≤ LV (fhat T) y)
    (herm : ∀ T ∈ P.sets, lossOn T (fhat T) y ≤ lossOn T pStar y)
    (hwit : LV pStar y = floor)
    (hρ : (1 : ℝ) ≤ ρ) :
    floor ≤ P.E (fun T => lossOn Tᶜ (fhat T) y) := by
  have hErewrite :
      P.E (fun T => lossOn Tᶜ (fhat T) y)
        = ρ * P.E (fun T => LV (fhat T) y)
          - (ρ - 1) * P.E (fun T => lossOn T (fhat T) y) := by
    have h1 : P.E (fun T => lossOn Tᶜ (fhat T) y)
        = P.E (fun T => ρ * LV (fhat T) y + (-(ρ - 1)) * lossOn T (fhat T) y) := by
      unfold Protocol.E
      refine Finset.sum_congr rfl (fun T hT => ?_)
      dsimp only
      rw [htrans T hT]; ring
    rw [h1, P.E_smul_add]; ring
  have hLV : floor ≤ P.E (fun T => LV (fhat T) y) := by
    calc floor = P.E (fun _ => floor) := (P.E_const floor).symm
      _ ≤ P.E (fun T => LV (fhat T) y) := P.E_mono hfit
  have hLT : P.E (fun T => lossOn T (fhat T) y) ≤ floor := by
    calc P.E (fun T => lossOn T (fhat T) y)
        ≤ P.E (fun T => lossOn T pStar y) := P.E_mono herm
      _ = LV pStar y := P.unbiased pStar y
      _ = floor := hwit
  rw [hErewrite]
  have hcoef : (0 : ℝ) ≤ ρ - 1 := by linarith
  nlinarith [hLV, hLT, hcoef, mul_le_mul_of_nonneg_left hLT hcoef,
             mul_le_mul_of_nonneg_left hLV (by linarith : (0:ℝ) ≤ ρ)]

/-! ### Genuine orthogonal projection discharges the Bessel orthogonality

Connecting `bessel_sum` to the real orthogonal projection on `EuclideanSpace ℝ (Fin N)`,
so the floor in Theorem 1 is the genuine projection-`R²`, with no assumed geometry. -/

/-- **Genuine Bessel floor.** For the actual orthogonal projection `pStar = P_S y` and
any `f ∈ S`, the population error at `pStar` is `≤` that at `f`. This discharges the
orthogonality hypothesis of `bessel_sum` from `starProjection_inner_eq_zero`. -/
lemma bessel_floor_proj (S : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    [S.HasOrthogonalProjection] (y f : EuclideanSpace ℝ (Fin N)) (hf : f ∈ S) :
    SE univ (S.starProjection y).ofLp y.ofLp ≤ SE univ f.ofLp y.ofLp := by
  apply bessel_sum
  have hmem : (f - S.starProjection y) ∈ S :=
    S.sub_mem hf (S.starProjection_apply_mem y)
  have h0 := Submodule.starProjection_inner_eq_zero (𝕜 := ℝ) y (f - S.starProjection y) hmem
  rw [PiLp.inner_apply] at h0
  simpa [RCLike.inner_apply, mul_comm] using h0

/-- **Theorem 1 — geometric instantiation.** When the learner's outputs lie in the
hypothesis subspace `S` and the floor is taken to be the *genuine* projection floor
`L_V(P_S y)`, the two abstract slack hypotheses of `universal_lower_bound` — the learner
Bessel floor `hfit` and the witness saturation `hwit` — are discharged from
`bessel_floor_proj`. Only the protocol/transduction/ERM hypotheses remain, exactly the
learner-specific assumptions the paper makes. This wires the real orthogonal projection
into Theorem 1, so the floor is the honest projection-`R²`, not an abstract real. -/
theorem universal_lower_bound_proj
    (P : Protocol N)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin N))) [S.HasOrthogonalProjection]
    (y : EuclideanSpace ℝ (Fin N))
    (fhat : Finset (Fin N) → EuclideanSpace ℝ (Fin N))
    (hmem : ∀ T ∈ P.sets, fhat T ∈ S)
    (ρ : ℝ)
    (htrans : ∀ T ∈ P.sets,
        lossOn Tᶜ (fhat T).ofLp y.ofLp
          = ρ * LV (fhat T).ofLp y.ofLp
            - (ρ - 1) * lossOn T (fhat T).ofLp y.ofLp)
    (herm : ∀ T ∈ P.sets,
        lossOn T (fhat T).ofLp y.ofLp ≤ lossOn T (S.starProjection y).ofLp y.ofLp)
    (hρ : (1 : ℝ) ≤ ρ) :
    LV (S.starProjection y).ofLp y.ofLp
      ≤ P.E (fun T => lossOn Tᶜ (fhat T).ofLp y.ofLp) :=
  universal_lower_bound P y.ofLp (fun T => (fhat T).ofLp)
    (S.starProjection y).ofLp ρ (LV (S.starProjection y).ofLp y.ofLp)
    htrans
    (fun T hT => by
      have hSE := bessel_floor_proj S y (fhat T) (hmem T hT)
      simpa [LV] using
        mul_le_mul_of_nonneg_left hSE (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹))
    herm rfl hρ

/-- **Saturation in expectation** (tightness of Theorem 1). The witness `pStar`
(the in-class population minimiser `P_S y`) attains the floor *exactly*:
`E_T[L_{Tᶜ}(pStar)] = floor`. Combined with `universal_lower_bound`, this shows the floor
is not merely a valid lower bound but the *exact* expected leave-node-out loss of the
population minimiser — the bound is tight at the population level. Pure algebra from the
transduction rearrangement and protocol exchangeability (`P.unbiased`); no concentration
machinery (that is the separate slack of the full Theorem 2). -/
theorem witness_saturates
    (P : Protocol N)
    (y pStar : Fin N → ℝ) (ρ floor : ℝ)
    (htrans : ∀ T ∈ P.sets,
        lossOn Tᶜ pStar y = ρ * LV pStar y - (ρ - 1) * lossOn T pStar y)
    (hwit : LV pStar y = floor) :
    P.E (fun T => lossOn Tᶜ pStar y) = floor := by
  have hub : P.E (fun T => lossOn T pStar y) = LV pStar y := P.unbiased pStar y
  have hrw : P.E (fun T => lossOn Tᶜ pStar y)
      = P.E (fun T => ρ * LV pStar y + (-(ρ - 1)) * lossOn T pStar y) := by
    unfold Protocol.E
    refine Finset.sum_congr rfl (fun T hT => ?_)
    dsimp only
    rw [htrans T hT]; ring
  rw [hrw, P.E_smul_add, P.E_const, hub, hwit]; ring

/-- The lower bound is **two-sided tight**: every protocol-admissible learner has expected
leave-node-out loss `≥ floor` (`universal_lower_bound`), and the witness `pStar` meets it
with equality (`witness_saturates`). Packaged as a single conjunction. -/
theorem lower_bound_tight
    (P : Protocol N)
    (y : Fin N → ℝ) (fhat : Finset (Fin N) → (Fin N → ℝ)) (pStar : Fin N → ℝ)
    (ρ floor : ℝ)
    (htrans : ∀ T ∈ P.sets,
        lossOn Tᶜ (fhat T) y = ρ * LV (fhat T) y - (ρ - 1) * lossOn T (fhat T) y)
    (htransWit : ∀ T ∈ P.sets,
        lossOn Tᶜ pStar y = ρ * LV pStar y - (ρ - 1) * lossOn T pStar y)
    (hfit : ∀ T ∈ P.sets, floor ≤ LV (fhat T) y)
    (herm : ∀ T ∈ P.sets, lossOn T (fhat T) y ≤ lossOn T pStar y)
    (hwit : LV pStar y = floor)
    (hρ : (1 : ℝ) ≤ ρ) :
    floor ≤ P.E (fun T => lossOn Tᶜ (fhat T) y)
      ∧ P.E (fun T => lossOn Tᶜ pStar y) = floor :=
  ⟨universal_lower_bound P y fhat pStar ρ floor htrans hfit herm hwit hρ,
   witness_saturates P y pStar ρ floor htransWit hwit⟩

/-! ### The transduction rearrangement is an identity, not an assumption

`universal_lower_bound` takes the rearranged transduction `htrans` and the constant `ρ` as
hypotheses. In fact, with the *forced* value `ρ = N/|Tᶜ|`, that rearrangement is an
algebraic identity (and `ρ ≥ 1`), so both `htrans` and `hρ` are discharged from first
principles for any proper split (`T` and `Tᶜ` both non-empty). -/

/-- **Transduction–`ρ` identity.** With `ρ = N/|Tᶜ|`, the holdout loss satisfies
`L_{Tᶜ}(f) = ρ·L_V(f) − (ρ−1)·L_T(f)` for every predictor `f`, on any proper split. This
is the `htrans` hypothesis of Theorem 1, here *proved* rather than assumed. -/
lemma lossOn_compl_eq (T : Finset (Fin N)) (f y : Fin N → ℝ)
    (hT : T.Nonempty) (hTc : Tᶜ.Nonempty) :
    lossOn Tᶜ f y
      = ((N : ℝ) / (Tᶜ.card : ℝ)) * LV f y
        - ((N : ℝ) / (Tᶜ.card : ℝ) - 1) * lossOn T f y := by
  have hc : (Tᶜ.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hTc).ne'
  have hTcard : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hT).ne'
  have hcard : (T.card : ℝ) + (Tᶜ.card : ℝ) = (N : ℝ) := by
    have h := Finset.card_add_card_compl T
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  have hcpos : (0 : ℝ) < (Tᶜ.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hTc)
  have hTnn : (0 : ℝ) ≤ (T.card : ℝ) := by positivity
  have hsum : (T.card : ℝ) + (Tᶜ.card : ℝ) ≠ 0 := ne_of_gt (by linarith)
  unfold lossOn LV
  rw [transduction T f y, ← hcard]
  field_simp
  ring

/-- The forced ratio `ρ = N/|Tᶜ| ≥ 1`, since the holdout is a subset of all `N` nodes. -/
lemma one_le_rho (T : Finset (Fin N)) (hTc : Tᶜ.Nonempty) :
    (1 : ℝ) ≤ (N : ℝ) / (Tᶜ.card : ℝ) := by
  have hcpos : (0 : ℝ) < (Tᶜ.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hTc)
  rw [le_div_iff₀ hcpos, one_mul]
  have hle : Tᶜ.card ≤ N := by
    have h := Finset.card_le_univ (Tᶜ)
    rwa [Fintype.card_fin] at h
  exact_mod_cast hle

/-! ### Headline form: the floor is `(1 − R²_spec)·Var(y)`

Anchoring the abstract `floor = L_V(pStar)` to the paper's headline quantity, by giving
`Var(y)` and the learner-specific spectral `R²` honest Lean definitions. -/

/-- Empirical mean of `y` over all `N` nodes. -/
noncomputable def mean (y : Fin N → ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ v, y v

/-- Population variance of `y`: the MSE of the best constant predictor (the mean). -/
noncomputable def Var (y : Fin N → ℝ) : ℝ := LV (fun _ => mean y) y

/-- **Learner-specific spectral `R²`** (notes/01): the fraction of `Var(y)` captured by the
in-class population minimiser `pStar = P_S y`, `R²_spec := 1 − L_V(pStar)/Var(y)`. -/
noncomputable def R2spec (pStar y : Fin N → ℝ) : ℝ := 1 - LV pStar y / Var y

/-- **Headline identity** (Theorem 1, displayed form). The abstract floor `L_V(pStar)`
is exactly `(1 − R²_spec)·Var(y)` whenever `y` is non-constant (`Var(y) ≠ 0`). Combined
with `hwit : L_V(pStar) = floor`, this is the paper's `floor = (1 − R²_spec)·Var(y)`. -/
lemma floor_eq_R2spec (pStar y : Fin N → ℝ) (hVar : Var y ≠ 0) :
    (1 - R2spec pStar y) * Var y = LV pStar y := by
  unfold R2spec
  rw [sub_sub_cancel, div_mul_cancel₀ (LV pStar y) hVar]

/-! ### Theorem 2 — deterministic ERM oracle skeleton

The upper-bound (saturation) theorem is fundamentally a concentration statement. Its
*deterministic* core is the standard ERM oracle inequality: given a uniform train-vs-
population deviation bound `B`, the ERM's excess population risk is `≤ 2B`. The
finite-sample *value* of `B` (the transductive Rademacher + Hoeffding–Serfling term of
notes/02) is the separate concentration step, isolated here as the hypotheses `hdev*` —
exactly as Theorem 1 isolates exchangeability. -/

/-- **Theorem 2 — ERM oracle inequality (deterministic core).** With `herm` the train-ERM
property and `hdevF`/`hdevP` the train-vs-population deviation bound `B` for the ERM output
and the witness, the ERM population risk satisfies `L_V(fhat) ≤ floor + 2B`. -/
theorem erm_oracle
    (T : Finset (Fin N))
    (y fhat pStar : Fin N → ℝ) (floor B : ℝ)
    (herm : lossOn T fhat y ≤ lossOn T pStar y)
    (hdevF : |lossOn T fhat y - LV fhat y| ≤ B)
    (hdevP : |lossOn T pStar y - LV pStar y| ≤ B)
    (hwit : LV pStar y = floor) :
    LV fhat y ≤ floor + 2 * B := by
  have hF := abs_le.mp hdevF
  have hP := abs_le.mp hdevP
  calc LV fhat y ≤ lossOn T fhat y + B := by linarith [hF.1]
    _ ≤ lossOn T pStar y + B := by linarith [herm]
    _ ≤ LV pStar y + 2 * B := by linarith [hP.2]
    _ = floor + 2 * B := by rw [hwit]

/-- **Population-risk sandwich for the ERM.** The lower side is the Bessel/spectral floor
(`hfit`, A3), the upper side is `erm_oracle`: `floor ≤ L_V(fhat) ≤ floor + 2B`. So the
ERM's population risk sits within the concentration slack `2B` of the spectral floor — the
finite-sample statement of saturation, modulo the value of `B`. -/
theorem erm_population_sandwich
    (T : Finset (Fin N))
    (y fhat pStar : Fin N → ℝ) (floor B : ℝ)
    (hfit : floor ≤ LV fhat y)
    (herm : lossOn T fhat y ≤ lossOn T pStar y)
    (hdevF : |lossOn T fhat y - LV fhat y| ≤ B)
    (hdevP : |lossOn T pStar y - LV pStar y| ≤ B)
    (hwit : LV pStar y = floor) :
    floor ≤ LV fhat y ∧ LV fhat y ≤ floor + 2 * B :=
  ⟨hfit, erm_oracle T y fhat pStar floor B herm hdevF hdevP hwit⟩

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms universal_lower_bound
#print axioms universal_lower_bound_proj
#print axioms witness_saturates
#print axioms lower_bound_tight
#print axioms floor_eq_R2spec
#print axioms erm_oracle
#print axioms erm_population_sandwich
#print axioms lossOn_compl_eq
#print axioms one_le_rho
#print axioms bessel_sum
#print axioms transduction
#print axioms bessel_floor_proj

end SBF
