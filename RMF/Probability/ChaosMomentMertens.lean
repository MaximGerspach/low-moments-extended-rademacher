/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosMomentExplicit
import RMF.NumberTheory.MertensProductSharp

/-!
# The chaos moments with Mertens' product at `e^γ`

The chaos's first moment and the restricted chaos both come from `(log x)⁻¹E‖F_x(1/2+σ)‖²`, which
Mertens bounds by `e^{γ + 9.0028/L₀}` once `log x ≥ L₀` (`RMF.normSqLogSharpConst`,
`RMF.prod_primesBelow_inv_le_exp_eulerMascheroni`).  This file proves that bound,
`RMF.inv_log_mul_integral_normSq_shift_le_sharp`, and the first moment of the chaos it gives,
`RMF.integral_chaosUnitShift_le_sharp`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The second moment at `e^γ` -/

/-- **The Mertens constant at `e^γ`**, `exp(γ + 9.0028/L₀)`: the bound on
`(log x)⁻¹E‖F_x(1/2+σ)‖²` once `x ≥ e^{L₀} + 1`. -/
noncomputable def normSqLogSharpConst (L₀ : ℝ) : ℝ :=
  Real.exp (Real.eulerMascheroniConstant + 9.0028 / L₀)

lemma normSqLogSharpConst_pos (L₀ : ℝ) : 0 < normSqLogSharpConst L₀ := Real.exp_pos _

omit [MeasurableSpace Ω] in
/-- **The normalised second moment at `e^γ`**: `(log x)⁻¹E‖F_x(1/2+σ)‖² ≤ e^{γ + 9.0028/L₀}` for
`σ ≥ 0`, `L₀ ≥ 1` and `x ≥ e^{L₀} + 1`.  The second moment at `σ` is at most the one at `σ = 0`,
which is the Mertens product, bounded by `RMF.prod_primesBelow_inv_le_exp_eulerMascheroni`. -/
theorem inv_log_mul_integral_normSq_shift_le_sharp {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) {x σ L₀ : ℝ}
    (hL₀ : 1 ≤ L₀) (hx : Real.exp L₀ + 1 ≤ x) (hσ : 0 ≤ σ) :
    (Real.log x)⁻¹ * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
        (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν ≤ normSqLogSharpConst L₀ := by
  have hf' : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hsre : (0 : ℝ) < (shiftLine 0 0).re := by rw [re_shiftLine]; norm_num
  have he2 : (2 : ℝ) ≤ Real.exp L₀ := by
    have := Real.add_one_le_exp L₀
    linarith
  have hfl : Real.exp L₀ ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hN2' : (2 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hN2 : 2 ≤ ⌊x⌋₊ := by exact_mod_cast hN2'
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlogN : (0 : ℝ) < Real.log ((⌊x⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hL : L₀ ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hfl
  have hlogx : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le hlogN hlogx
  -- the second moment is the Mertens product
  have hprod : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
      (⌊x⌋₊ + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν)
      = ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
    rw [hf'.integral_norm_randomEulerProduct_sq' (⌊x⌋₊ + 1) hsre]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [re_shiftLine, show (-2 : ℝ) * (1 / 2 + 0) = -1 by ring, Real.rpow_neg_one]
  have hbound : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 - ((p : ℝ))⁻¹)⁻¹
      ≤ normSqLogSharpConst L₀ * Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    prod_primesBelow_inv_le_exp_eulerMascheroni hN2 (by linarith) hL
  have hlog : (0 : ℝ) ≤ (Real.log x)⁻¹ := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left (integral_normSq_shiftLine_mono hY _ hσ) hlog) ?_
  rw [hprod, inv_mul_eq_div, div_le_iff₀ hlogx0]
  exact le_trans hbound
    (mul_le_mul_of_nonneg_left hlogx (normSqLogSharpConst_pos L₀).le)

omit [MeasurableSpace Ω] in
/-- **The chaos first moment at `e^γ`**: `E[chaosUnitShift] ≤ e^{γ + 9.0028/L₀}` for `σ ≥ 0`,
`L₀ ≥ 1` and `x ≥ e^{L₀} + 1`. -/
theorem integral_chaosUnitShift_le_sharp {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) {x σ L₀ : ℝ} (hL₀ : 1 ≤ L₀)
    (hx : Real.exp L₀ + 1 ≤ x) (hσ : 0 ≤ σ) :
    (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν)
      ≤ normSqLogSharpConst L₀ := by
  rw [integral_chaosUnitShift_eq hY x σ (by linarith)]
  exact inv_log_mul_integral_normSq_shift_le_sharp hY hL₀ hx hσ

end RMF
