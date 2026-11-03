/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedBounds
import RMF.Weighted.ExtendedLowerKhintchine
import RMF.Weighted.ULowQExplicit

/-!
# The extended sum against the weighted one, without the factor `2`

For `x ≥ 1`, almost surely `Y(x) = x^{-1/2}∑_{n≤x} X^e(n) = S(x) - R(x)`
(`RMF.ae_normalisedSum_compMultExtension_eq`), and
`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le` pays a factor `2` for comparing the
moments.  Without it:

* `E|Y|^{2q} ≤ E|S|^{2q} + E|R|^{2q}` for `0 ≤ q ≤ ½`
  (`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le_add`), so
  `E|Y| ≤ E|S| + E|R|` (`RMF.integral_norm_normalisedSum_compMultExtension_le_add`);
* Minkowski, `E|Y|^{2q} ≤ ((E|S|^{2q})^{1/2q} + (E|R|^{2q})^{1/2q})^{2q}` for `q ≥ ½`
  (`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le_minkowski`);
* the trivial bound `E|Y|^{2q} ≤ (⌊x⌋/√x)^{2q}`
  (`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le_floor`).

`Y` and `R` lie in every `L^p` (`RMF.memLp_normalisedSum_compMultExtension`,
`RMF.memLp_fracPartSum`).
-/

open MeasureTheory
open scoped ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Boundedness and integrability -/

/-- `|Y(x)| ≤ ⌊x⌋/√x` almost surely, as `|X^e(n)| ≤ 1`. -/
lemma ae_norm_normalisedSum_compMultExtension_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ≤ (⌊x⌋₊ : ℝ) / Real.sqrt x := by
  filter_upwards [norm_randomSum_le_of_ae (f := fun ω => compMultExtension fun p => X p ω)
    (μ := μ) (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n) x]
    with ω hω
  rw [normalisedSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right hω (Real.sqrt_nonneg _)

/-- `|R(x)| ≤ ⌊x⌋/√x` almost surely: each of its `⌊x⌋` terms is at most `1/√x`. -/
lemma ae_norm_fracPartSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) :
    ∀ᵐ ω ∂μ, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ≤ (⌊x⌋₊ : ℝ) / Real.sqrt x := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 ⌊x⌋₊)).2
    fun n _ => hRa.norm_apply_le_one n] with ω hω
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖squarefreeExtension (fun p => X p ω) n
      * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)‖ ≤ (Real.sqrt x)⁻¹ := by
    intro n hn
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 (Real.sqrt_nonneg _))
      (mul_le_one₀ (hω n hn) (Int.fract_nonneg _) (Int.fract_lt_one _).le)
  calc ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖squarefreeExtension (fun p => X p ω) n
          * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (Real.sqrt x)⁻¹ := Finset.sum_le_sum hterm
    _ = (⌊x⌋₊ : ℝ) / Real.sqrt x := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, div_eq_mul_inv]

/-- `Y(x)` lies in every `L^p`: it is bounded by `⌊x⌋/√x` almost surely. -/
lemma memLp_normalisedSum_compMultExtension {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) (p : ℝ≥0∞) :
    MemLp (normalisedSum (fun ω => compMultExtension fun p => X p ω) x) p μ := by
  haveI := hX.isProbabilityMeasure
  have hm : Measurable (normalisedSum (fun ω => compMultExtension fun p => X p ω) x) :=
    (Finset.measurable_sum _ fun n _ => hX.measurable_compMultExtension n).div_const _
  exact (memLp_top_of_bound hm.aestronglyMeasurable _
    (ae_norm_normalisedSum_compMultExtension_le hX x)).mono_exponent le_top

/-- `R(x)` lies in every `L^p`: it is bounded by `⌊x⌋/√x` almost surely. -/
lemma memLp_fracPartSum {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) (p : ℝ≥0∞) :
    MemLp (fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x) p μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hm : Measurable (fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x) :=
    Finset.measurable_sum _ fun n _ => ((hRa.measurable_apply n).mul_const _).div_const _
  exact (memLp_top_of_bound hm.aestronglyMeasurable _
    (ae_norm_fracPartSum_le hX x)).mono_exponent le_top

/-- The moments of `Y(x)` are integrable. -/
lemma integrable_rpow_norm_normalisedSum_compMultExtension {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω =>
      ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  have hm : Measurable (normalisedSum (fun ω => compMultExtension fun p => X p ω) x) :=
    (Finset.measurable_sum _ fun n _ => hX.measurable_compMultExtension n).div_const _
  refine (memLp_top_of_bound
    ((Real.continuous_rpow_const hr).measurable.comp hm.norm).aestronglyMeasurable
    (((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ r) ?_).integrable le_top
  filter_upwards [ae_norm_normalisedSum_compMultExtension_le hX x] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
  exact Real.rpow_le_rpow (norm_nonneg _) hω hr

/-! ### The comparisons -/

/-- **The trivial bound**: `E|Y(x)|^{2q} ≤ (⌊x⌋/√x)^{2q}` for `q ≥ 0`. -/
theorem integral_rpow_norm_normalisedSum_compMultExtension_le_floor {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) (x : ℝ) {q : ℝ} (hq0 : 0 ≤ q) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ (2 * q) := by
  haveI := hX.isProbabilityMeasure
  have hr : (0 : ℝ) ≤ 2 * q := by linarith
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ _ω, ((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ (2 * q) ∂μ :=
        integral_mono_ae (integrable_rpow_norm_normalisedSum_compMultExtension hX x hr)
          (integrable_const _) (by
            filter_upwards [ae_norm_normalisedSum_compMultExtension_le hX x] with ω hω
            exact Real.rpow_le_rpow (norm_nonneg _) hω hr)
    _ = ((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ (2 * q) := by simp

/-- **Subadditivity up to `q = ½`**: for `x ≥ 1` and `0 ≤ q ≤ ½`,
`E|Y(x)|^{2q} ≤ E|S(x)|^{2q} + E|R(x)|^{2q}`, from `Y = S - R` almost surely and
`(a + b)^{2q} ≤ a^{2q} + b^{2q}`. -/
theorem integral_rpow_norm_normalisedSum_compMultExtension_le_add {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        + ∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hr0 : (0 : ℝ) ≤ 2 * q := by linarith
  have hr1 : 2 * q ≤ 1 := by linarith
  have hS := integrable_rpow_norm_weightedRademacherSum hX x hr0
  have hR := integrable_rpow_norm_fracPartSum hX x hr0
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ∫ ω, (‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) + ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q)) ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)
          (hS.add hR) ?_
        filter_upwards [ae_normalisedSum_compMultExtension_eq hX hx] with ω hω
        rw [hω]
        exact (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) hr0).trans
          (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hr0 hr1)
    _ = (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ)
        + ∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ :=
        integral_add hS hR

/-- **The first moment**: `E|Y(x)| ≤ E|S(x)| + E|R(x)|` for `x ≥ 1`. -/
theorem integral_norm_normalisedSum_compMultExtension_le_add {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
        + ∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
  have h := integral_rpow_norm_normalisedSum_compMultExtension_le_add hX hx
    (q := 1 / 2) (by norm_num) le_rfl
  simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] using h

/-- **Minkowski from `q = ½`**: for `x ≥ 1` and `q ≥ ½`,
`E|Y(x)|^{2q} ≤ ((E|S(x)|^{2q})^{1/2q} + (E|R(x)|^{2q})^{1/2q})^{2q}`
(`RMF.rpow_inv_integral_rpow_norm_add_le` at `S + (-R)`, which is `Y` almost surely). -/
theorem integral_rpow_norm_normalisedSum_compMultExtension_le_minkowski {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x)
    (hq : 1 / 2 ≤ q) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ((∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          + (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ) ^ (2 * q)⁻¹) ^ (2 * q) := by
  have hr : 1 ≤ 2 * q := by linarith
  have hr0 : (0 : ℝ) < 2 * q := by linarith
  have hmink := rpow_inv_integral_rpow_norm_add_le hr (memLp_weightedRademacherSum hX x _)
    (g := fun ω => -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω)
    (memLp_fracPartSum hX x _).neg
  simp only [norm_neg] at hmink
  have hY : (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      = ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
          + -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_normalisedSum_compMultExtension_eq hX hx] with ω hω
    rw [hω, sub_eq_add_neg]
  have hI : (0 : ℝ) ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      + -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  rw [hY]
  calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
          + -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      = ((∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
          + -fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ^ (2 * q)⁻¹) ^ (2 * q) := by
        rw [← Real.rpow_mul hI, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hmink hr0.le

end RMF
