/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperExplicit
import RMF.Probability.ChaosMomentMertens
import RMF.Reduction.PeriodisationSharp
import RMF.Reduction.StepsSharp

/-!
# Harper's upper bound with `q`-dependent constants

`RMF.harper_upper_full` pays a fixed factor at each conversion: `2` for rounding the cutoff
down, `2` for `log log` of the cutoff, `2` for the block count and `3` below `q = 2/3`.  The
pieces here let the constant stay a function of `q`, each conversion costing a factor `k > 1` and
the error term an `η > 0`, at a threshold depending on `k` and `η`:
* `RMF.periodisation_upper_sharp`, the periodisation at `∑_n w_n^q`;
* `RMF.loglog_floor_harperCutoff_ge_sub_two_log`, `log log` of the rounded-down cutoff;
* `RMF.exp_neg_mul_sq_le_mul_target`, the error term as an `η`-fraction of the target;
* `RMF.integral_chaosUnit_rpow_le_loglog_of`, which turns a chaos-moment bound against the block
  count into one against `log log y` at the cost `k`.

`RMF.harper_upper_of_chaos_sieve` (`RMF/Reduction/UpperSieve.lean`) assembles the first three;
the last enters the chaos moments it takes as a hypothesis
(`RMF.integral_chaosUnit_rpow_le_averaged`).
-/

open MeasureTheory
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The periodisation -/

/-- **Periodisation at the exact window weights**: `RMF.periodisation_upper` at `∑_n w_n^q`
(`RMF.integral_rpow_line_le_sharp`) in place of `8∑_n (1+n²)^{-q}`. -/
theorem periodisation_upper_sharp :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ y q : ℝ, 2 ≤ y → 1 / 2 < q → q ≤ 1 →
        ∫ ω, eulerLineIntegral f y ω ^ q ∂μ
          ≤ (∑' n : ℤ, lineWeight n ^ q) * ∫ ω, chaosUnit f y ω ^ q ∂μ := by
  intro f μ hf y q hy hq0 hq1
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hunit : ∀ ω, chaosUnit (fun ω => compMultExtension fun p => X p ω) y ω
      = (Real.log y)⁻¹ * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq (1 / 2) X (⌊y⌋₊ + 1) ω h := by
    intro ω
    rw [chaosUnit, intervalIntegral.integral_of_le zero_le_one]
    rfl
  simp_rw [eulerLineIntegral, hunit]
  exact integral_rpow_line_le_sharp (1 / 2) (by norm_num) hX (⌊y⌋₊ + 1)
    (inv_nonneg.2 hlog.le) hq0 hq1

/-! ### The conversions -/

/-- **`log log` of the rounded-down cutoff**: `log log ⌊Y⌋ ≥ L - 2 log L - 1` for the Harper cutoff
`Y` and `L = log log x`.  `log ⌊Y⌋ ≥ (log Y)/2`, and `log log Y = L - 2 log L`
(`RMF.loglog_harperCutoff`). -/
lemma loglog_floor_harperCutoff_ge_sub_two_log {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    Real.log (Real.log x) - 2 * Real.log (Real.log (Real.log x)) - 1
      ≤ Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) := by
  obtain ⟨-, -, hL36⟩ := harper_regime hx
  have hY36 : Real.exp 36 ≤ harperCutoff x := exp_le_harperCutoff hx
  have hexp36 : (37 : ℝ) ≤ Real.exp 36 := by
    have := Real.add_one_le_exp (36 : ℝ)
    linarith
  have hY0 : (0 : ℝ) < harperCutoff x := by linarith
  have hfl : harperCutoff x / 2 ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (harperCutoff x)
    linarith
  have hlogY : Real.log (Real.log x) ≤ Real.log (harperCutoff x) := log_harperCutoff_ge hx
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlfl : Real.log (harperCutoff x) / 2 ≤ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log (harperCutoff x / 2) ≤ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hfl
    rw [Real.log_div hY0.ne' (by norm_num)] at h1
    linarith
  have hlY0 : 0 < Real.log (harperCutoff x) / 2 := by linarith
  have hll : Real.log (Real.log (harperCutoff x)) - Real.log 2
      ≤ Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) := by
    have h1 := Real.log_le_log hlY0 hlfl
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    exact h1
  rw [loglog_harperCutoff hx] at hll
  linarith

/-- **The error term is an `η`-fraction of the target**: `e^{-cL²} ≤ η(1 + (1-q)√L)^{-q}` for
`2/3 ≤ q ≤ 1`, once `L = log log x ≥ 2(1 + |log η|)/c`.  Half of `cL²` pays for the target
(`RMF.harper_error_le_target`), the other half for `η`. -/
lemma exp_neg_mul_sq_le_mul_target {x c q η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hx : Real.exp (Real.exp 36) ≤ x)
    (hthr : 2 * (1 + |Real.log η|) / c ≤ Real.log (Real.log x))
    (hq0 : 2 / 3 ≤ q) (hq1 : q ≤ 1) :
    Real.exp (-(c * Real.log (Real.log x) ^ 2))
      ≤ η * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨-, -, hL36⟩ := harper_regime hx
  have hc2 : 0 < c / 2 := by positivity
  have hthr' : 2 * (1 + |Real.log η|) ≤ Real.log (Real.log x) * c := (div_le_iff₀ hc).1 hthr
  have habs0 := abs_nonneg (Real.log η)
  have h1 : 1 / (c / 2) ≤ Real.log (Real.log x) := by
    rw [one_div_div, div_le_iff₀ hc]
    linarith
  have hT := harper_error_le_target hc2 hx h1 hq0 hq1
  have hLL : Real.log (Real.log x) ≤ Real.log (Real.log x) ^ 2 := by nlinarith
  have hη' : Real.exp (-(c / 2 * Real.log (Real.log x) ^ 2)) ≤ η := by
    calc Real.exp (-(c / 2 * Real.log (Real.log x) ^ 2)) ≤ Real.exp (Real.log η) := by
          refine Real.exp_le_exp.2 ?_
          have h2 : c / 2 * Real.log (Real.log x) ≤ c / 2 * Real.log (Real.log x) ^ 2 :=
            mul_le_mul_of_nonneg_left hLL hc2.le
          have h3 := neg_abs_le (Real.log η)
          nlinarith
      _ = η := Real.exp_log hη
  have hsplit : Real.exp (-(c * Real.log (Real.log x) ^ 2))
      = Real.exp (-(c / 2 * Real.log (Real.log x) ^ 2))
        * Real.exp (-(c / 2 * Real.log (Real.log x) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul hη' hT (Real.exp_pos _).le hη.le

/-! ### The chaos moments against `log log y` -/

/-- The arithmetic of `RMF.integral_chaosUnit_rpow_le_loglog_of`: `L ≤ k²t` from `L - D ≤ t` and
`k²D ≤ (k²-1)L`. -/
lemma le_sq_mul_of_sub_le {k L D t : ℝ} (hD : k ^ 2 * D ≤ (k ^ 2 - 1) * L) (ht : L - D ≤ t) :
    L ≤ k ^ 2 * t := by
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg k)]

/-- **From the block count to `log log y`**: a Steinhaus chaos-moment bound at `σ = 0` against
`t = harperBlockCount D y` becomes one against `log log y` at the cost `k`, past
`max{y₁, exp(exp(k²(D+1)/(k²-1)))}`. -/
theorem integral_chaosUnit_rpow_le_loglog_of {S : ℝ → ℝ} {D : ℕ} {y₁ k : ℝ} (hk : 1 < k)
    (hy₁ : 2 ≤ y₁)
    (H : ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ y q : ℝ, y₁ ≤ y → 0 ≤ q → q ≤ 1 →
        (∫ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) y 0 ω ^ q ∂ν)
          ≤ S q * (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q)) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ y q : ℝ, max y₁ (Real.exp (Real.exp (k ^ 2 * ((D : ℝ) + 1) / (k ^ 2 - 1)))) ≤ y →
        0 ≤ q → q ≤ 1 →
        ∫ ω, chaosUnit f y ω ^ q ∂μ
          ≤ k * S q * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by
  intro f μ hf y q hy hq0 hq1
  obtain ⟨Y, hY, rfl⟩ := hf.exists_primeValues
  have hy₁' : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : (2 : ℝ) ≤ y := le_trans hy₁ hy₁'
  have hexp : Real.exp (Real.exp (k ^ 2 * ((D : ℝ) + 1) / (k ^ 2 - 1))) ≤ y :=
    le_trans (le_max_right _ _) hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : Real.exp (k ^ 2 * ((D : ℝ) + 1) / (k ^ 2 - 1)) ≤ Real.log y :=
    (Real.le_log_iff_exp_le hy0).2 hexp
  have hlogy0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le (Real.exp_pos _) hlogy
  have hL : k ^ 2 * ((D : ℝ) + 1) / (k ^ 2 - 1) ≤ Real.log (Real.log y) :=
    (Real.le_log_iff_exp_le hlogy0).2 hlogy
  have hk2 : 0 < k ^ 2 - 1 := by nlinarith
  have hkD : k ^ 2 * ((D : ℝ) + 1) ≤ (k ^ 2 - 1) * Real.log (Real.log y) := by
    rw [div_le_iff₀ hk2] at hL
    linarith
  have hDL : (D : ℝ) ≤ Real.log (Real.log y) := by
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
    nlinarith
  have ht : Real.log (Real.log y) - ((D : ℝ) + 1) ≤ (harperBlockCount D y : ℝ) := by
    rw [cast_harperBlockCount hDL]
    have := Nat.lt_floor_add_one (Real.log (Real.log y))
    linarith
  have htar := rpow_neg_target_le_of_sq_le (t := (harperBlockCount D y : ℝ))
    (Λ := Real.log (Real.log y)) hk.le (le_sq_mul_of_sub_le hkD ht) hq0 hq1
  have h := H Y μ hY y q hy₁' hq0 hq1
  have heq : ∀ ω, chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) y 0 ω
      = chaosUnit (fun ω => compMultExtension fun p => Y p ω) y ω :=
    fun ω => chaosUnitShift_zero _ _ _
  simp_rw [heq] at h
  have hT0 : (0 : ℝ) < (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q) := by
    refine Real.rpow_pos_of_pos ?_ _
    have := mul_nonneg (sub_nonneg.2 hq1) (Real.sqrt_nonneg (harperBlockCount D y : ℝ))
    linarith
  have hI0 : (0 : ℝ)
      ≤ ∫ ω, chaosUnit (fun ω => compMultExtension fun p => Y p ω) y ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosUnit_nonneg hy2 ω) _
  have hS0 := nonneg_of_mul_nonneg_left (le_trans hI0 h) hT0
  calc ∫ ω, chaosUnit (fun ω => compMultExtension fun p => Y p ω) y ω ^ q ∂μ
      ≤ S q * (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q) := h
    _ ≤ S q * (k * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :=
        mul_le_mul_of_nonneg_left htar hS0
    _ = k * S q * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q) := by ring

end RMF
