/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.Upper
import RMF.Reduction.StepsExplicit
import RMF.Probability.ChaosMomentExplicit

/-!
# Harper's upper bound with an explicit constant: the small range

The step that takes an explicit upper bound past a threshold `x₀` down to every `x ≥ 1` without
making the constant grow with `x₀`.  `RMF.harper_upper_ge_three_of_full` bounds the moments on
`3 ≤ x ≤ x₀` by `max 1 x₀`; `RMF.harper_upper_of_rpow_le` uses `E|S_x|^{2q} ≤ 1` instead
(`RMF.IsSteinhausRMF.integral_norm_normalisedSum_rpow_le_one`: Jensen against the second moment
`⌊x⌋/x`), so that the small range costs only `max_q (1 + (1-q)√(log log x₀))^q`.
`RMF.one_add_mul_rpow_le_of_end` bounds that maximum on an interval of `q` from its endpoints;
`RMF.harper_upper_numeral` applies the step at `x₀ = exp(exp 10⁴)`.
-/

open MeasureTheory
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Down to `x = 3` -/

/-- **`E|S_x|^{2q} ≤ 1`** for `x ≥ 1` and `0 ≤ q ≤ 1`: Jensen against the second moment
`E‖S_x‖² = ⌊x⌋/x`. -/
lemma IsSteinhausRMF.integral_norm_normalisedSum_rpow_le_one {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ) ≤ 1 := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
    exact hY.isProbabilityMeasure
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hpt : ∀ ω, ‖normalisedSum f x ω‖ ^ (2 * q) = (‖normalisedSum f x ω‖ ^ 2) ^ q := by
    intro ω
    rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  simp_rw [hpt]
  have hsq : ∀ ω, ‖normalisedSum f x ω‖ ^ 2 = ‖partialSum f ⌊x⌋₊ ω‖ ^ 2 / x := by
    intro ω
    rw [normalisedSum, randomSum_eq_partialSum, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hsx.le, div_pow, Real.sq_sqrt hx0.le]
  have hmom : (∫ ω, ‖normalisedSum f x ω‖ ^ 2 ∂μ) ≤ 1 := by
    simp_rw [hsq]
    rw [integral_div, hf.second_moment, div_le_one hx0]
    exact Nat.floor_le hx0.le
  have hb : ∀ᵐ ω ∂μ, ‖normalisedSum f x ω‖ ^ 2 ≤ ((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ 2 := by
    filter_upwards [hf.ae_norm_normalisedSum_le x] with ω hω
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hjensen := integral_rpow_le_rpow_integral_of_bound hq0 hq1
    ((hf.measurable_normalisedSum x).norm.pow_const 2)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) hb
  exact le_trans hjensen (Real.rpow_le_one (integral_nonneg fun ω => sq_nonneg _) hmom hq0)

/-- **The target's base on `[q₁, q₂]` from its endpoints**: for `0 ≤ q₁ ≤ q ≤ q₂ ≤ 1` and
`s ≥ 0`, `(1 + (1-q)s)^q ≤ e^{q₂ log(1 + (1-q₁)s)}`, since the base is at least `1` and
decreases in `q`. -/
lemma one_add_mul_rpow_le_of_end {q q₁ q₂ s : ℝ} (hs : 0 ≤ s) (hq₁ : 0 ≤ q₁) (h1q : q₁ ≤ q)
    (hq2 : q ≤ q₂) (hq₂ : q₂ ≤ 1) :
    (1 + (1 - q) * s) ^ q ≤ Real.exp (q₂ * Real.log (1 + (1 - q₁) * s)) := by
  have hq0 : 0 ≤ q := le_trans hq₁ h1q
  have hb1 : 1 ≤ 1 + (1 - q) * s := by
    have := mul_nonneg (sub_nonneg.2 (le_trans hq2 hq₂)) hs
    linarith
  have hbb : 1 + (1 - q) * s ≤ 1 + (1 - q₁) * s := by
    have := mul_le_mul_of_nonneg_right (show 1 - q ≤ 1 - q₁ by linarith) hs
    linarith
  calc (1 + (1 - q) * s) ^ q ≤ (1 + (1 - q₁) * s) ^ q :=
        Real.rpow_le_rpow (by linarith) hbb hq0
    _ ≤ (1 + (1 - q₁) * s) ^ q₂ := Real.rpow_le_rpow_of_exponent_le (le_trans hb1 hbb) hq2
    _ = Real.exp (q₂ * Real.log (1 + (1 - q₁) * s)) := by
        rw [Real.rpow_def_of_pos (by linarith), mul_comm]

/-- **The target below `x₀` against a bound on its base at `x₀`**: for `1 ≤ x ≤ x₀`, `q ∈ [0, 1]`
and `(1 + (1-q)√(log log x₀))^q ≤ C₀`, `1 ≤ C₀·(1 + (1-q)√(log log x))^{-q}`. -/
lemma one_le_mul_target_of_rpow_le {x x₀ q C₀ : ℝ} (hx : 1 ≤ x) (hxx₀ : x ≤ x₀) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hC₀ : (1 + (1 - q) * Real.sqrt (Real.log (Real.log x₀))) ^ q ≤ C₀) :
    1 ≤ C₀ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  have hs0 : 0 ≤ Real.sqrt (Real.log (Real.log x)) := Real.sqrt_nonneg _
  have hT0 : 0 < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    have := mul_nonneg (sub_nonneg.2 hq1) hs0
    linarith
  have hss : Real.sqrt (Real.log (Real.log x)) ≤ Real.sqrt (Real.log (Real.log x₀)) := by
    rcases le_or_gt (Real.log x) 1 with hl | hl
    · have hll : Real.log (Real.log x) ≤ 0 := Real.log_nonpos (Real.log_nonneg hx) hl
      rw [Real.sqrt_eq_zero'.2 hll]
      exact Real.sqrt_nonneg _
    · exact Real.sqrt_le_sqrt (Real.log_le_log (by linarith)
        (Real.log_le_log (by linarith) hxx₀))
  have hTq : 0 < (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ q :=
    Real.rpow_pos_of_pos hT0 _
  have hle : (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ q ≤ C₀ := by
    refine le_trans (Real.rpow_le_rpow hT0.le ?_ hq0) hC₀
    have := mul_le_mul_of_nonneg_left hss (sub_nonneg.2 hq1)
    linarith
  rw [Real.rpow_neg hT0.le, ← div_eq_mul_inv, one_le_div hTq]
  exact hle

/-- **Harper's upper bound for every `x ≥ 1`, from a bound past `x₀` and `E|S_x|^{2q} ≤ 1`.**
Below `x₀` the moment is at most `1` (`RMF.IsSteinhausRMF.integral_norm_normalisedSum_rpow_le_one`)
and the target is at least `1/C₀` once `(1 + (1-q)√(log log x₀))^q ≤ C₀` for every `q ∈ [0, 1]`
(`RMF.one_le_mul_target_of_rpow_le`), so `C₀` serves on the whole range. -/
theorem harper_upper_of_rpow_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsSteinhausRMF f μ) {C₀ x₀ : ℝ}
    (hC₀ : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → (1 + (1 - q) * Real.sqrt (Real.log (Real.log x₀))) ^ q ≤ C₀)
    (H : ∀ x q : ℝ, x₀ ≤ x → 0 ≤ q → q ≤ 1 →
      ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
        ≤ C₀ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q))
    {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      ≤ C₀ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  rcases le_or_gt x₀ x with hx₀ | hx₀
  · exact H x q hx₀ hq0 hq1
  calc (∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ)
      ≤ 1 := hf.integral_norm_normalisedSum_rpow_le_one hx hq0 hq1
    _ ≤ C₀ * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) :=
        one_le_mul_target_of_rpow_le hx hx₀.le hq0 hq1 (hC₀ q hq0 hq1)

end RMF
