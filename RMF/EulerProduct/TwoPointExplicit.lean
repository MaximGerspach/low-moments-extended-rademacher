/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.TwoPoint
import RMF.EulerProduct.TwoPointClosed

/-!
# Harper's (5.1) with its error constant named

`RMF.exists_abs_log_integral_two_point_le` — Harper's (5.1), the two-point moment of a block
Euler product — hides its error constant in an existential, and every constant of Key
Proposition 5's crude and high ranges is built from it.

A witness obtained by `Classical.choose` has no size, so each step of the chain is restated here
with its witness named:

* `RMF.taylorProdConst Q n` — the multi-factor Taylor expansion's constant, explicit in the
  coefficient bound `Q` and the index count `n`, from `RMF.exists_taylor_bound_prod`;
* `RMF.logTwoPointSubConst` — the constant of the logarithm of the two-point local moment, from
  the closed form;
* `RMF.twoPointMomentConst` — Harper's (5.1) itself;
* `RMF.twoPointTailConst` — its error at the shortest range `x = 400`, where
  `\sqrt x\log x ≈ 120`.

**The witnesses never mention the space.**  Each is a closed real term; the measurable space
appears in the existential statements only because they sit inside a `variable {Ω}` section,
which puts the existential *inside* the space binder and so makes `Classical.choose` depend on it.
Naming the constants removes that apparent dependence.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {ι : Type*}

/-- **The multi-factor Taylor expansion's constant**, `RMF.exists_taylor_bound_prod`'s witness
written out: explicit in the coefficient bound `Q` and the number `n` of factors. -/
noncomputable def taylorProdConst (Q n : ℝ) : ℝ :=
  1 + 2 * Q * n + (2 * Q * n) ^ 3 + 9 / 4 * (Q * n) ^ 2
    + (Real.exp (Q * n) + (1 + Q * n / 2 + (Q * n) ^ 2 / 8 + Q * n / 8)) * (2 * Q * n) ^ 3

/-- **The logarithm of the two-point local moment**: `0.56`, from the closed form
(`RMF.abs_log_local_two_point_sub_le_closed`). -/
noncomputable def logTwoPointSubConst : ℝ := 0.56

/-- `RMF.logTwoPointSubConst` is positive. -/
lemma logTwoPointSubConst_pos : 0 < logTwoPointSubConst := by
  rw [logTwoPointSubConst]
  norm_num

/-- **`RMF.exists_abs_log_local_two_point_sub_le` with its witness named**, from the closed form
`RMF.integral_local_two_point_eq`. -/
theorem abs_log_local_two_point_sub_le :
    ∀ (w₁ w₂ : ℂ) (δ : ℝ), 0 ≤ δ → δ ≤ 0.136 → ‖w₁‖ ≤ δ → ‖w₂‖ ≤ δ →
      |Real.log (∫ z, ‖(1 - z * w₁)⁻¹‖ ^ 2 * ‖(1 - z * w₂)⁻¹‖ ^ 2 ∂steinhausLaw)
          - ‖w₁ + w₂‖ ^ 2| ≤ logTwoPointSubConst * δ ^ 3 := by
  intro w₁ w₂ δ hδ0 hδ h₁ h₂
  rw [logTwoPointSubConst]
  exact abs_log_local_two_point_sub_le_closed hδ0 hδ h₁ h₂

/-- **`RMF.exists_abs_log_localTwoPointMoment_sub_le` with its witness named.**  A
pass-through: the per-prime weights are `p^{-(1/2+σ)}`, so the cube is the (5.1) summand. -/
theorem abs_log_localTwoPointMoment_sub_le :
    ∀ (p : ℕ), p.Prime → ∀ σ t x y : ℝ, 400 ≤ x → x ≤ (p : ℝ) → (p : ℝ) ≤ y →
      -(1 / Real.log y) ≤ σ →
      |Real.log (localTwoPointMoment p σ t)
          - (2 + 2 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ logTwoPointSubConst * (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
  have h := abs_log_local_two_point_sub_le
  refine fun p hp σ t x y hx hxp hpy hσ => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  obtain ⟨h₁, h₂, hsmall⟩ := norm_weights_eq (t := t) hp hx hxp hpy hσ
  have key := h _ _ _ (Real.rpow_nonneg hp0.le _) hsmall h₁.le h₂.le
  rw [norm_sq_add_prime_cpow_neg ⟨p, hp⟩ (by simp : (((1 / 2 + σ : ℝ) : ℂ)).re = 1 / 2 + σ)]
    at key
  have hcube : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 3 = (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 3, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  rwa [hcube] at key

/-- **Harper's (5.1) error constant.**  `RMF.logTwoPointSubConst` times the prime tail's
`e³·8\log 4` from `RMF.sum_prime_Ioc_rpow_cube_le'`. -/
noncomputable def twoPointMomentConst : ℝ :=
  logTwoPointSubConst * (Real.exp 3 * (8 * Real.log 4))

/-- `RMF.twoPointMomentConst` is positive. -/
lemma twoPointMomentConst_pos : 0 < twoPointMomentConst := by
  have h := logTwoPointSubConst_pos
  have hlog : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rw [twoPointMomentConst]
  positivity

/-- **`RMF.exists_abs_log_prod_localTwoPointMoment_le` with its witness named.** -/
theorem abs_log_prod_localTwoPointMoment_le :
    ∀ σ t x y : ℝ, 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      |Real.log (∏ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, localTwoPointMoment p σ t)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + 2 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ twoPointMomentConst / (Real.sqrt x * Real.log x) := by
  have hloc := abs_log_localTwoPointMoment_sub_le
  have hC₁ : 0 < logTwoPointSubConst := logTwoPointSubConst_pos
  rw [twoPointMomentConst]
  set C₁ : ℝ := logTwoPointSubConst with hC₁def
  refine fun σ t x y hx hxy hσ => ?_
  have hy0 : (0 : ℝ) ≤ y := by linarith
  -- membership of the range gives exactly the two inequalities the per-prime estimate wants
  have hrange : ∀ q ∈ {q ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | Nat.Prime q},
      Nat.Prime q ∧ x ≤ (q : ℝ) ∧ (q : ℝ) ≤ y := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
    refine ⟨hq.2, ?_, ?_⟩
    · have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq.1.1
      linarith
    · exact le_trans (by exact_mod_cast hq.1.2) (Nat.floor_le hy0)
  refine le_trans (abs_log_prod_sub_sum_le (C := C₁)
    (b := fun q => (q : ℝ) ^ (-(3 / 2) - 3 * σ)) (fun q hq => ?_) (fun q hq => ?_)) ?_
  · obtain ⟨hqp, hxq, hqy⟩ := hrange q hq
    exact localTwoPointMoment_pos hqp hx hxq hqy hσ
  · obtain ⟨hqp, hxq, hqy⟩ := hrange q hq
    exact hloc q hqp σ t x y hx hxq hqy hσ
  · calc C₁ * ∑ q ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime q, (q : ℝ) ^ (-(3 / 2) - 3 * σ)
        ≤ C₁ * (Real.exp 3 * (8 * Real.log 4 / (Real.sqrt x * Real.log x))) :=
          mul_le_mul_of_nonneg_left (sum_prime_Ioc_rpow_cube_le' (by linarith) hxy hσ) hC₁.le
      _ = C₁ * (Real.exp 3 * (8 * Real.log 4)) / (Real.sqrt x * Real.log x) := by ring

/-- **Harper's (5.1) with its error constant named**: `RMF.twoPointMomentConst`.  Same
statement as `RMF.exists_abs_log_integral_two_point_le`, with the witness written out. -/
theorem abs_log_integral_two_point_le {Ω : Type*} [MeasurableSpace Ω] :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ σ t x y : ℝ, 400 ≤ x → x ≤ y → -(1 / Real.log y) ≤ σ →
      |Real.log (∫ ω,
            ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
              * ‖randomEulerProductIco f (⌊x⌋₊ + 1) (⌊y⌋₊ + 1)
                  (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          - ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p,
              (2 + 2 * Real.cos (t * Real.log (p : ℝ))) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ twoPointMomentConst / (Real.sqrt x * Real.log x) := by
  have h := abs_log_prod_localTwoPointMoment_le
  refine fun f μ hf σ t x y hx hxy hσ => ?_
  have hre : (0 : ℝ) < 1 / 2 + σ := half_add_pos hx hxy hσ
  have hre₁ : 0 < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hre₂ : 0 < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq _ _ hre₁ hre₂,
    ← filter_prime_Ioc_eq_primesIco]
  simpa only [localTwoPointMoment] using h σ t x y hx hxy hσ

/-! ### The error at the shortest range

`RMF.abs_log_integral_two_point_le` holds for `x ≥ 400`, and its error `C/(\sqrt x\log x)` is at
most its value at `x = 400`: `\sqrt{400}\log 400 ≈ 120`. -/

/-- **Harper's (5.1) error at the shortest range**:
`RMF.twoPointMomentConst/(\sqrt{400}\log 400)`, which bounds the error of
`RMF.abs_log_integral_two_point_le` at every `x ≥ 400`. -/
noncomputable def twoPointTailConst : ℝ := twoPointMomentConst / (Real.sqrt 400 * Real.log 400)

lemma one_le_sqrt_mul_log_four_hundred : 1 ≤ Real.sqrt 400 * Real.log 400 := by
  have hs : Real.sqrt 400 = 20 := by
    rw [show (400 : ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hl : 1 ≤ Real.log 400 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  rw [hs]
  linarith

lemma twoPointTailConst_pos : 0 < twoPointTailConst :=
  div_pos twoPointMomentConst_pos (by linarith [one_le_sqrt_mul_log_four_hundred])

/-! ### The same error from a floor

`RMF.twoPointTailConst` is the error at the *shortest* admissible range, `x = 400`.  But the
bottom block sits at `RMF.blockScale θ 0 = e^{e^θ}` with `θ ≥ 125` (`RMF.harperTheta_ge`), so the
range the argument actually visits is `e^{e^{125}}`, where `√x\log x` is enormous.  The floored
version below charges the error at the range where it is used. -/

/-- **Harper's (5.1) error from a floor `y`**: `RMF.twoPointMomentConst/(\sqrt y\log y)`, which
bounds the error of `RMF.abs_log_integral_two_point_le` at every `x ≥ y`.
`RMF.twoPointTailConst` is the case `y = 400`. -/
noncomputable def twoPointTailConstAt (y : ℝ) : ℝ :=
  twoPointMomentConst / (Real.sqrt y * Real.log y)

/-- `\sqrt x\log x` is increasing from any floor `y ≥ 400`. -/
lemma sqrt_mul_log_mono_of {x y : ℝ} (hy : 400 ≤ y) (hxy : y ≤ x) :
    Real.sqrt y * Real.log y ≤ Real.sqrt x * Real.log x :=
  mul_le_mul (Real.sqrt_le_sqrt hxy) (Real.log_le_log (by linarith) hxy)
    (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)

/-- `1 ≤ \sqrt y\log y` for every `y ≥ 400`. -/
lemma one_le_sqrt_mul_log_of {y : ℝ} (hy : 400 ≤ y) : 1 ≤ Real.sqrt y * Real.log y :=
  le_trans one_le_sqrt_mul_log_four_hundred (sqrt_mul_log_mono_of le_rfl hy)

/-- `RMF.twoPointTailConstAt` is positive on `y ≥ 400`. -/
lemma twoPointTailConstAt_pos {y : ℝ} (hy : 400 ≤ y) : 0 < twoPointTailConstAt y :=
  div_pos twoPointMomentConst_pos (by linarith [one_le_sqrt_mul_log_of hy])

/-- **The error of `RMF.abs_log_integral_two_point_le` at `x ≥ y` is at most
`RMF.twoPointTailConstAt y`.** -/
lemma twoPointMomentConst_div_le_tailAt {x y : ℝ} (hy : 400 ≤ y) (hxy : y ≤ x) :
    twoPointMomentConst / (Real.sqrt x * Real.log x) ≤ twoPointTailConstAt y :=
  div_le_div_of_nonneg_left twoPointMomentConst_pos.le
    (by linarith [one_le_sqrt_mul_log_of hy]) (sqrt_mul_log_mono_of hy hxy)

end RMF
