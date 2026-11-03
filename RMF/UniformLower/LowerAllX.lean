/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.FinalRegimes

/-!
# The explicit lower bounds from `q = ½` up, for every `x ≥ 3`

`E S(x) = 1` for every `x ≥ 1` (`RMF.integral_weightedRademacherSum_eq_one`: `E f(n) = 0` for
`n > 1`), so `E|S(x)| ≥ 1` and, by Jensen between powers, `E|S(x)|^{2q} ≥ 1` for `q ≥ ½`.  That
covers the targets where they are at most `1`, and the regimes of
`RMF/UniformLower/FinalRegimes.lean` (`x ≥ exp(exp 6000)`) and Bonami–Beckner (`x ≥ e^{405}`,
`2q - 1 ≥ 10⁻⁸`) cover the rest.  With `Λ = log log x`:

* `RMF.integral_norm_weightedRademacherSum_ge_half_explicit`: `10⁻⁷Λ^{3/4} ≤ E|S(x)|` for every
  `x ≥ 3`;
* `RMF.integral_rpow_weightedRademacherSum_ge_aboveHalf_explicit`:
  `10⁻¹⁰(log x)^{q(2q-1)}min{1/(2q-1), Λ}^{3/4} ≤ E|S(x)|^{2q}` for `½ < q ≤ 1` and every `x ≥ 3`.

The three cases together, for every `x ≥ 3`, are
`RMF.weighted_rademacher_moments_lower_uniform_explicit_every_x`
(`RMF/UniformLower/MainExplicitAllX.lean`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The first moment -/

/-- `E f(n) = [n = 1]` for `n ≥ 1`: orthogonality against `f(1) = 1`. -/
lemma integral_squarefreeExtension_eq_ite {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, squarefreeExtension (fun p => X p ω) n ∂μ = if n = 1 then 1 else 0 := by
  have h := hX.isRademacherRMF.orthogonality hn one_ne_zero
  simp only [squarefreeExtension_apply_one, map_one, mul_one] at h
  rw [h]
  by_cases h1 : n = 1
  · subst h1
    simp
  · simp [h1]

/-- **`E S(x) = 1`** for every Rademacher `X` and every `x ≥ 1`: only `n = 1` contributes. -/
theorem integral_weightedRademacherSum_eq_one {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    ∫ ω, weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω ∂μ = 1 := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have h1 : 1 ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.2 ⟨le_rfl, (Nat.one_le_floor_iff x).2 hx⟩
  have hint : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, Integrable
      (fun ω => squarefreeExtension (fun p => X p ω) n / (Real.sqrt n : ℂ)) μ :=
    fun n _ => (Integrable.of_bound (hf.measurable_apply n).aestronglyMeasurable 1
      (hf.norm_apply_le_one n)).div_const _
  simp only [weightedRademacherSum]
  rw [integral_finsetSum _ hint, Finset.sum_eq_single 1 ?_ fun h => absurd h1 h, integral_div,
    integral_squarefreeExtension_eq_ite hX one_ne_zero, if_pos rfl]
  · simp
  · intro n hn hn1
    rw [integral_div, integral_squarefreeExtension_eq_ite hX
      (Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hn).1), if_neg hn1, zero_div]

/-- `1 ≤ E|S(x)|` for every Rademacher `X` and every `x ≥ 1`. -/
theorem one_le_integral_norm_weightedRademacherSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
  have h := norm_integral_le_integral_norm (μ := μ)
    (weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x)
  rwa [integral_weightedRademacherSum_eq_one hX hx, norm_one] at h

/-- `1 ≤ E|S(x)|^{2q}` for every Rademacher `X`, every `x ≥ 1` and every `q ≥ ½`:
`E|S(x)| ≤ (E|S(x)|^{2q})^{1/(2q)}` (`RMF.integral_rpow_le_rpow_integral_of_le`). -/
theorem one_le_integral_rpow_weightedRademacherSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq : 1 / 2 ≤ q) :
    1 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have h1 := one_le_integral_norm_weightedRademacherSum hX hx
  have hJ := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := q) (q := 1 / 2) (by norm_num) hq
    (memLp_weightedRademacherSum hX x _)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hJ
  simp only [Real.rpow_one] at hJ
  have hE0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  by_contra hlt
  have h2 := Real.rpow_lt_one (z := 1 / 2 / q) hE0 (not_le.1 hlt)
    (div_pos (by norm_num) (by linarith))
  linarith

/-! ### Arithmetic -/

/-- `1 ≤ log x` for `x ≥ 3`. -/
lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.le_log_iff_exp_le (by linarith)).2 (by linarith)

/-- `log log x < 6000` for `1 < x < exp(exp 6000)`. -/
lemma loglog_lt_six_thousand {x : ℝ} (hx : 1 < x) (hx' : x < Real.exp (Real.exp 6000)) :
    Real.log (Real.log x) < 6000 :=
  (Real.log_lt_iff_lt_exp (Real.log_pos hx)).2 ((Real.log_lt_iff_lt_exp (by linarith)).2 hx')

/-- `Λ^{3/4} ≤ 6000` for `0 ≤ Λ ≤ 6000`. -/
lemma rpow_three_quarters_le_six_thousand {Λ : ℝ} (h0 : 0 ≤ Λ) (h : Λ ≤ 6000) :
    Λ ^ (3 / 4 : ℝ) ≤ 6000 :=
  calc Λ ^ (3 / 4 : ℝ) ≤ 6000 ^ (3 / 4 : ℝ) := Real.rpow_le_rpow h0 h (by norm_num)
    _ ≤ 6000 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 6000 := Real.rpow_one _

/-- **The target above `½` is at most `1` for `log x ≤ 405`**: for `1 ≤ L ≤ 405` and
`½ < q ≤ 1`, `10⁻¹⁰L^{q(2q-1)}min{1/(2q-1), log L}^{3/4} ≤ 10⁻¹⁰L² ≤ 1`. -/
lemma aboveHalf_target_le_one_of_le_405 {q L : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hL1 : 1 ≤ L) (hL : L ≤ 405) :
    1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ)) ≤ 1 := by
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log L) :=
    le_min (inv_nonneg.2 hδ0.le) (Real.log_nonneg hL1)
  have hmL : min (2 * q - 1)⁻¹ (Real.log L) ≤ L :=
    (min_le_right _ _).trans (Real.log_le_self (by linarith))
  have hA : L ^ (q * (2 * q - 1)) ≤ L := by
    calc L ^ (q * (2 * q - 1)) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (mul_le_one₀ hq1 hδ0.le (by linarith))
      _ = L := Real.rpow_one L
  have hB : min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ L := by
    calc min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hmin0 hmL (by norm_num)
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hAB : L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ 405 * 405 :=
    mul_le_mul (hA.trans hL) (hB.trans hL) (Real.rpow_nonneg hmin0 _) (by norm_num)
  linarith

/-- **The target just above `½` is at most `1` for `log log x < 6000`**: for `L > 0`,
`0 ≤ log L < 6000`, `½ < q ≤ 1` and `2q - 1 < 10⁻⁸`,
`10⁻¹⁰L^{q(2q-1)}min{1/(2q-1), log L}^{3/4} ≤ 10⁻¹⁰·3·6000 ≤ 1` (`L^{q(2q-1)} ≤ e^{6·10⁻⁵}`). -/
lemma aboveHalf_target_le_one_of_small {q L : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hδ : 2 * q - 1 < 1 / 10 ^ 8) (hL : 0 < L) (hΛ0 : 0 ≤ Real.log L)
    (hΛ : Real.log L < 6000) :
    1 / 10 ^ 10 * (L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ)) ≤ 1 := by
  have hδ0 : 0 < 2 * q - 1 := by linarith
  have hβ0 : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) hδ0.le
  have hβ : q * (2 * q - 1) ≤ 1 * (1 / 10 ^ 8) := mul_le_mul hq1 hδ.le hδ0.le zero_le_one
  have hA : L ^ (q * (2 * q - 1)) ≤ 3 := by
    rw [Real.rpow_def_of_pos hL]
    have h1 : Real.log L * (q * (2 * q - 1)) ≤ 6000 * (1 * (1 / 10 ^ 8)) :=
      mul_le_mul hΛ.le hβ hβ0 (by norm_num)
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : Real.exp (Real.log L * (q * (2 * q - 1))) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log L) := le_min (inv_nonneg.2 hδ0.le) hΛ0
  have hB : min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ 6000 :=
    rpow_three_quarters_le_six_thousand hmin0 ((min_le_right _ _).trans hΛ.le)
  have hAB : L ^ (q * (2 * q - 1)) * min (2 * q - 1)⁻¹ (Real.log L) ^ (3 / 4 : ℝ) ≤ 3 * 6000 :=
    mul_le_mul hA hB (Real.rpow_nonneg hmin0 _) (by norm_num)
  linarith

/-! ### Every `x ≥ 3` -/

/-- **`E|S(x)| ≥ 10⁻⁷(log log x)^{3/4}` for every `x ≥ 3`**: H for `x ≥ exp(exp 6000)`
(`RMF.le_integral_norm_halfRegime`); below it `log log x < 6000`, so the target is at most
`10⁻⁷·6000 ≤ 1 ≤ E|S(x)|`. -/
theorem integral_norm_weightedRademacherSum_ge_half_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 3 ≤ x) :
    1 / 10 ^ 7 * Real.log (Real.log x) ^ (3 / 4 : ℝ)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
  rcases le_or_gt (Real.exp (Real.exp 6000)) x with hbig | hsmall
  · exact le_integral_norm_halfRegime hX hbig
  have hL1 := one_le_log_of_three_le hx
  have h34 := rpow_three_quarters_le_six_thousand (Real.log_nonneg hL1)
    (loglog_lt_six_thousand (by linarith) hsmall).le
  have h1 := one_le_integral_norm_weightedRademacherSum hX (by linarith : (1 : ℝ) ≤ x)
  linarith

/-- **Above `½` with `c = 10⁻¹⁰`, for every `x ≥ 3`**: for every Rademacher `X`, `x ≥ 3` and
`½ < q ≤ 1`, `10⁻¹⁰(log x)^{q(2q-1)}min{1/(2q-1), log log x}^{3/4} ≤ E|S(x)|^{2q}`: for
`x ≥ exp(exp 6000)` the regimes BB, L and S of `RMF/UniformLower/FinalRegimes.lean`; below it
Bonami–Beckner for `x ≥ e^{405}` and `2q - 1 ≥ 10⁻⁸`, and `E|S(x)|^{2q} ≥ 1` otherwise, where the
target is at most `1`. -/
theorem integral_rpow_weightedRademacherSum_ge_aboveHalf_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) :
    1 / 10 ^ 10 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  rcases le_or_gt (Real.exp (Real.exp 6000)) x with hbig | hsmall
  · rcases le_or_gt (1 / 10 ^ 8) (2 * q - 1) with h | h
    · exact le_integral_rpow_bbRegime hX hbig hq1 h
    · rcases le_or_gt ((2 * q - 1) * Real.log (Real.log x)) 1 with h' | h'
      · exact le_integral_rpow_lyapunovRegime hX hbig hq0 h h'
      · exact le_integral_rpow_sliverRegime hX hbig hq0 h h'.le
  have hL1 := one_le_log_of_three_le hx
  have hE := one_le_integral_rpow_weightedRademacherSum hX (by linarith : (1 : ℝ) ≤ x) hq0.le
  rcases le_or_gt (1 / 10 ^ 8) (2 * q - 1) with hδ | hδ
  · rcases le_or_gt (Real.exp 405) x with h405 | h405
    · have hδ0 : 0 < 2 * q - 1 := lt_of_lt_of_le (by norm_num) hδ
      have hc : 10 * (1 / 10 ^ 10 : ℝ) ≤ (2 * q - 1) ^ (3 / 4 : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith)
          (by norm_num : (3 / 4 : ℝ) ≤ 1)
        rw [Real.rpow_one] at h
        linarith
      exact le_integral_rpow_weightedRademacherSum_largeQ_bb hX h405 hq0 hq1 (by norm_num) hc
    · have hL405 : Real.log x ≤ 405 := ((Real.log_lt_iff_lt_exp (by linarith)).2 h405).le
      exact (aboveHalf_target_le_one_of_le_405 hq0 hq1 hL1 hL405).trans hE
  · exact (aboveHalf_target_le_one_of_small hq0 hq1 hδ (by linarith) (Real.log_nonneg hL1)
      (loglog_lt_six_thousand (by linarith) hsmall)).trans hE

end RMF
