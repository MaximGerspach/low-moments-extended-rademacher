/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.Periodisation

/-!
# The periodisation at the exact window weights

`RMF.integral_rpow_line_le` bounds `|σ+it|^{-2}` on `[n, n+1]` by `8/(1+n²)`, and pays
`8∑_{n ∈ ℤ} (1+n²)^{-q}`: `≈ 58` at `q = 2/3`.  The maximum of `|1/2+it|^{-2}` on the window is
`w_n = (1/4 + d_n²)⁻¹`, with `d_n` the distance from `0` to `[n, n+1]` (`RMF.lineWeight`), and the
same argument at these weights pays `∑_n w_n^q = 2∑_{k ≥ 0} (1/4+k²)^{-q}`: `≈ 11.9` at `q = 2/3`,
`≈ 10.9` at `q = 1`.

The proofs are those of `RMF.rpow_line_leOf` and `RMF.integral_rpow_line_le_maxOf` with the weight
replaced; the Steinhaus instance takes the window moments from `RMF.integral_rpow_window_eq`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

variable (σ : ℝ)

/-! ### The weights -/

/-- The distance from `0` to the window `[n, n+1]`: `n` for `n ≥ 0`, `-(n+1)` for `n < 0`. -/
noncomputable def lineDist (n : ℤ) : ℝ := if 0 ≤ n then (n : ℝ) else -((n : ℝ) + 1)

/-- **The exact window weight** `max_{t ∈ [n, n+1]} |1/2+it|^{-2} = (1/4 + d_n²)⁻¹`, with `d_n` the
distance from `0` to the window (`RMF.lineDist`). -/
noncomputable def lineWeight (n : ℤ) : ℝ := (1 / 4 + lineDist n ^ 2)⁻¹

lemma lineWeight_pos (n : ℤ) : 0 < lineWeight n := by
  unfold lineWeight
  positivity

lemma lineWeight_nonneg (n : ℤ) : 0 ≤ lineWeight n := (lineWeight_pos n).le

/-- `d_n² ≤ t²` on the window `[n, n+1]`. -/
lemma lineDist_sq_le {n : ℤ} {t : ℝ} (h0 : (n : ℝ) ≤ t) (h1 : t ≤ (n : ℝ) + 1) :
    lineDist n ^ 2 ≤ t ^ 2 := by
  unfold lineDist
  split_ifs with hn
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact pow_le_pow_left₀ hn0 h0 2
  · have hn1 : (n : ℝ) + 1 ≤ 0 := by
      have h : n + 1 ≤ 0 := by omega
      exact_mod_cast h
    have ht : -((n : ℝ) + 1) ≤ -t := by linarith
    have hsq := mul_le_mul ht ht (by linarith) (by linarith)
    nlinarith [hsq]

/-- **The weight on the window**: `|z/(σ+it)|² ≤ w_n |z|²` for `σ ≥ 1/2` and `t ∈ [n, n+1]`. -/
lemma norm_div_sq_le_lineWeight (hσ : 1 / 2 ≤ σ) {n : ℤ} {t : ℝ} (h0 : (n : ℝ) ≤ t)
    (h1 : t ≤ (n : ℝ) + 1) (z : ℂ) :
    ‖z / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤ lineWeight n * ‖z‖ ^ 2 := by
  have hd := lineDist_sq_le h0 h1
  have hσ2 : (1 : ℝ) / 4 ≤ σ ^ 2 := by nlinarith
  have hden : (0 : ℝ) < 1 / 4 + lineDist n ^ 2 := by positivity
  have hlow : 1 / 4 + lineDist n ^ 2 ≤ σ ^ 2 + t ^ 2 := by linarith
  have hstep : ‖z‖ ^ 2 / (σ ^ 2 + t ^ 2) ≤ ‖z‖ ^ 2 / (1 / 4 + lineDist n ^ 2) := by
    gcongr
  rw [norm_div, div_pow, normSq_ofReal_add_mul_I]
  refine le_trans hstep (le_of_eq ?_)
  rw [lineWeight, div_eq_inv_mul]

/-- **The exact weights are at most the crude ones**: `w_n ≤ 8/(1+n²)`, by
`RMF.one_add_sq_div_eight_le` at the endpoint of the window nearest `0`. -/
lemma lineWeight_le_eight_div (n : ℤ) : lineWeight n ≤ 8 / (1 + (n : ℝ) ^ 2) := by
  have hn : (1 + (n : ℝ) ^ 2) / 8 ≤ 1 / 4 + lineDist n ^ 2 := by
    unfold lineDist
    split_ifs with h
    · exact one_add_sq_div_eight_le le_rfl (by linarith)
    · have h' := one_add_sq_div_eight_le (n := n) (t := (n : ℝ) + 1) (by linarith) le_rfl
      rw [neg_sq]
      exact h'
  have hpos : (0 : ℝ) < (1 + (n : ℝ) ^ 2) / 8 := by positivity
  rw [lineWeight, show 8 / (1 + (n : ℝ) ^ 2) = ((1 + (n : ℝ) ^ 2) / 8)⁻¹ by rw [inv_div]]
  exact inv_anti₀ hpos hn

lemma lineWeight_rpow_le (n : ℤ) {q : ℝ} (hq : 0 ≤ q) :
    lineWeight n ^ q ≤ 8 ^ q * shiftWeight q n := by
  rw [← rpow_eight_div n]
  exact Real.rpow_le_rpow (lineWeight_nonneg n) (lineWeight_le_eight_div n) hq

/-- **The exact weights are `q`-summable for `q > 1/2`**, by comparison with `RMF.shiftWeight`. -/
lemma summable_lineWeight_rpow {q : ℝ} (hq : 1 / 2 < q) :
    Summable fun n : ℤ => lineWeight n ^ q :=
  Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (lineWeight_nonneg n) q)
    (fun n => lineWeight_rpow_le n (by linarith)) ((summable_shiftWeight hq).mul_left _)

lemma summable_lineWeight : Summable lineWeight := by
  have h := summable_lineWeight_rpow (q := 1) (by norm_num)
  simpa using h

/-! ### The pointwise bound -/

omit [MeasurableSpace Ω] in
/-- **The per-window bound at the exact weight**, for a general product: dividing by `σ+it` costs
at most `w_n` on `(n, n+1]`. -/
lemma window_boundOf_sharp {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hσ : 1 / 2 ≤ σ)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C) (n : ℤ) :
    (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineDivSqOf σ F N ω t)
      ≤ lineWeight n * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrable_lineDivSqOf σ hσ hmeas hbd).integrableOn
    ((integrableOn_windowOf σ hmeas hbd ((n : ℝ)) ((n : ℝ) + 1)).const_mul _) measurableSet_Ioc
    fun t ht => ?_
  exact norm_div_sq_le_lineWeight σ hσ ht.1.le ht.2 _

omit [MeasurableSpace Ω] in
/-- **The pointwise periodisation bound at the exact weights**, for a general product bounded by
`C` along the line: `(c∫_ℝ)^q ≤ ∑_n w_n^q (c∫_n^{n+1})^q`. -/
theorem rpow_line_leOf_sharp {F : Ω → ArithmeticFunction ℂ} {N : ℕ} {ω : Ω} {C : ℝ}
    (hσ : 1 / 2 ≤ σ)
    (hmeas : Measurable fun t : ℝ =>
      randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (hbd : ∀ t : ℝ, ‖randomEulerProduct F N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C)
    {c : ℝ} (hc : 0 ≤ c) {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    (c * ∫ t : ℝ, lineDivSqOf σ F N ω t) ^ q
      ≤ ∑' n : ℤ, lineWeight n ^ q
          * (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t) ^ q := by
  have hq0' : (0 : ℝ) < q := lt_trans (by norm_num) hq0
  set W : ℤ → ℝ := fun n => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ F N ω t with hWdef
  have hWnn : ∀ n, 0 ≤ W n := fun n => integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1)
  have hWle : ∀ n, W n ≤ C ^ 2 := fun n => window_leOf σ hmeas hbd (n : ℝ)
  have hwq : Summable fun n : ℤ => lineWeight n ^ q := summable_lineWeight_rpow hq0
  have hcW : ∀ n, 0 ≤ c * W n := fun n => mul_nonneg hc (hWnn n)
  -- the weighted sum of `q`-th powers converges
  have hkey : Summable fun n : ℤ => lineWeight n ^ q * (c * W n) ^ q := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (lineWeight_nonneg n) q)
        (Real.rpow_nonneg (hcW n) q))
      (fun n => ?_) (hwq.mul_right ((c * C ^ 2) ^ q))
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hcW n) (mul_le_mul_of_nonneg_left (hWle n) hc) hq0'.le)
      (Real.rpow_nonneg (lineWeight_nonneg n) q)
  -- the windows sum to the line integral, and are bounded termwise
  have hIsum : HasSum (fun n : ℤ => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineDivSqOf σ F N ω t)
      (∫ t : ℝ, lineDivSqOf σ F N ω t) :=
    hasSum_integral_Ioc (integrable_lineDivSqOf σ hσ hmeas hbd)
  have hMnn : ∀ n : ℤ, 0 ≤ lineWeight n * W n :=
    fun n => mul_nonneg (lineWeight_nonneg n) (hWnn n)
  have hMsum : Summable fun n : ℤ => lineWeight n * W n := by
    refine Summable.of_nonneg_of_le hMnn (fun n => ?_) (summable_lineWeight.mul_right (C ^ 2))
    exact mul_le_mul_of_nonneg_left (hWle n) (lineWeight_nonneg n)
  have hline : (∫ t : ℝ, lineDivSqOf σ F N ω t) ≤ ∑' n : ℤ, lineWeight n * W n := by
    rw [← hIsum.tsum_eq]
    exact hIsum.summable.tsum_le_tsum (fun n => window_boundOf_sharp σ hσ hmeas hbd n) hMsum
  -- scale by `c`
  set a : ℤ → ℝ := fun n => lineWeight n * (c * W n) with hadef
  have hann : ∀ n, 0 ≤ a n := fun n => mul_nonneg (lineWeight_nonneg n) (hcW n)
  have hasum : Summable a := by
    have hc' : Summable fun n : ℤ => c * (lineWeight n * W n) := hMsum.mul_left c
    refine hc'.congr fun n => ?_
    rw [hadef]
    ring
  have hcline : c * (∫ t : ℝ, lineDivSqOf σ F N ω t) ≤ ∑' n : ℤ, a n := by
    have hrw : ∑' n : ℤ, a n = c * ∑' n : ℤ, lineWeight n * W n := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by rw [hadef]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hline hc
  -- the `q`-th power, termwise
  have haq : ∀ n : ℤ, a n ^ q = lineWeight n ^ q * (c * W n) ^ q := fun n =>
    Real.mul_rpow (lineWeight_nonneg n) (hcW n)
  have haqsum : Summable fun n : ℤ => a n ^ q := hkey.congr fun n => (haq n).symm
  have hnn0 : 0 ≤ c * ∫ t : ℝ, lineDivSqOf σ F N ω t :=
    mul_nonneg hc (integral_nonneg fun t => by unfold lineDivSqOf; positivity)
  calc (c * ∫ t : ℝ, lineDivSqOf σ F N ω t) ^ q
      ≤ (∑' n : ℤ, a n) ^ q := Real.rpow_le_rpow hnn0 hcline hq0'.le
    _ ≤ ∑' n : ℤ, a n ^ q := rpow_tsum_le_tsum_rpow_real hann hasum hq0' hq1 haqsum
    _ = ∑' n : ℤ, lineWeight n ^ q * (c * W n) ^ q := tsum_congr haq

/-! ### The bound, integrated -/

set_option maxHeartbeats 400000 in
-- the chain threads a `tsum` through a Bochner integral and back through `ℝ≥0∞`
/-- **The periodisation bound at the exact weights**, for a general product: if every window's
`q`-th moment is at most `S`, the line integral's is at most `(∑_n w_n^q)·S`.  The measurability
inputs are those of `RMF.integral_rpow_line_le_maxOf`. -/
theorem integral_rpow_line_le_sharpOf {G : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hσ : 1 / 2 ≤ σ) (N : ℕ) {C : ℝ}
    (hae : ∀ᵐ ω ∂μ,
      (Measurable fun t : ℝ => randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω) ∧
        ∀ t : ℝ, ‖randomEulerProduct G N ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ C)
    (hWmeas : ∀ n : ℤ, AEStronglyMeasurable
      (fun ω => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ G N ω t) μ)
    (hLmeas : AEStronglyMeasurable (fun ω => ∫ t : ℝ, lineDivSqOf σ G N ω t) μ)
    {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ n : ℤ, (∫ ω, (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
        lineSqOf σ G N ω t) ^ q ∂μ) ≤ S) :
    (∫ ω, (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q ∂μ)
      ≤ (∑' n : ℤ, lineWeight n ^ q) * S := by
  have hq0' : (0 : ℝ) < q := lt_trans (by norm_num) hq0
  have hwq : Summable fun n : ℤ => lineWeight n ^ q := summable_lineWeight_rpow hq0
  have hwnn : ∀ n : ℤ, (0 : ℝ) ≤ lineWeight n ^ q :=
    fun n => Real.rpow_nonneg (lineWeight_nonneg n) q
  set K : ℝ := (c * C ^ 2) ^ q with hKdef
  set W : ℤ → Ω → ℝ := fun n ω => ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSqOf σ G N ω t
    with hWdef
  set F : ℤ → Ω → ℝ := fun n ω => lineWeight n ^ q * (c * W n ω) ^ q with hFdef
  have hWnn : ∀ n ω, 0 ≤ W n ω := fun n ω => integral_lineSqOf_nonneg σ (n : ℝ) ((n : ℝ) + 1)
  have hFnn : ∀ n ω, 0 ≤ F n ω := fun n ω =>
    mul_nonneg (hwnn n) (Real.rpow_nonneg (mul_nonneg hc (hWnn n ω)) q)
  -- the termwise bound and the pointwise inequality, on the good set
  have hgood : ∀ᵐ ω ∂μ, (∀ n : ℤ, F n ω ≤ lineWeight n ^ q * K) ∧
      (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q ≤ ∑' n : ℤ, F n ω := by
    filter_upwards [hae] with ω hω
    refine ⟨fun n => ?_, rpow_line_leOf_sharp σ hσ hω.1 hω.2 hc hq0 hq1⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hc (hWnn n ω))
        (mul_le_mul_of_nonneg_left (window_leOf σ hω.1 hω.2 (n : ℝ)) hc) hq0'.le)
      (hwnn n)
  have hFmeas : ∀ n : ℤ, AEStronglyMeasurable (F n) μ := fun n =>
    (((Real.continuous_rpow_const hq0'.le).comp_aestronglyMeasurable
      ((hWmeas n).const_mul c)).const_mul (lineWeight n ^ q))
  have hFint : ∀ n : ℤ, Integrable (F n) μ := by
    intro n
    refine (memLp_top_of_bound (hFmeas n) (lineWeight n ^ q * K) ?_).integrable le_top
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n ω)]
    exact hω.1 n
  have hFle : ∀ n : ℤ, ∫ ω, F n ω ∂μ ≤ lineWeight n ^ q * S := by
    intro n
    rw [hFdef]
    simp only
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hS n) (hwnn n)
  -- the left side is integrable
  have hLnn : ∀ ω, 0 ≤ (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q := fun ω =>
    Real.rpow_nonneg
      (mul_nonneg hc (integral_nonneg fun t => by unfold lineDivSqOf; positivity)) q
  have hLmeas' : AEStronglyMeasurable (fun ω => (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q) μ :=
    (Real.continuous_rpow_const hq0'.le).comp_aestronglyMeasurable (hLmeas.const_mul c)
  have hLbd : ∀ᵐ ω ∂μ,
      ‖(c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q‖ ≤ (∑' n : ℤ, lineWeight n ^ q) * K := by
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hLnn ω)]
    refine le_trans hω.2 ?_
    rw [← tsum_mul_right]
    exact (Summable.of_nonneg_of_le (fun n => hFnn n ω) hω.1
      (hwq.mul_right K)).tsum_le_tsum hω.1 (hwq.mul_right K)
  have hLint : Integrable (fun ω => (c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q) μ :=
    (memLp_top_of_bound hLmeas' _ hLbd).integrable le_top
  -- compare in `ℝ≥0∞`, where `lintegral_tsum` has no side conditions
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (tsum_nonneg hwnn) hS0),
    ofReal_integral_eq_lintegral_ofReal hLint (Filter.Eventually.of_forall hLnn)]
  calc ∫⁻ ω, ENNReal.ofReal ((c * ∫ t : ℝ, lineDivSqOf σ G N ω t) ^ q) ∂μ
      ≤ ∫⁻ ω, ∑' n : ℤ, ENNReal.ofReal (F n ω) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood] with ω hω
        refine le_trans (ENNReal.ofReal_le_ofReal hω.2) (le_of_eq ?_)
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => hFnn n ω)
          (Summable.of_nonneg_of_le (fun n => hFnn n ω) hω.1 (hwq.mul_right K))
    _ = ∑' n : ℤ, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ :=
        lintegral_tsum (f := fun (n : ℤ) (ω : Ω) => ENNReal.ofReal (F n ω))
          (fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hFmeas n).aemeasurable)
    _ ≤ ∑' n : ℤ, ENNReal.ofReal (lineWeight n ^ q * S) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hFint n)
          (Filter.Eventually.of_forall fun ω => hFnn n ω)]
        exact ENNReal.ofReal_le_ofReal (hFle n)
    _ = ENNReal.ofReal ((∑' n : ℤ, lineWeight n ^ q) * S) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun n => mul_nonneg (hwnn n) hS0) (hwq.mul_right S), tsum_mul_right]

set_option maxHeartbeats 400000 in
-- the two measurability inputs unify a functional over a function space
/-- **The periodisation bound at the exact weights, for the Steinhaus law**: every window has the
unit window's moment (`RMF.integral_rpow_window_eq`), so
`E[(c∫_ℝ)^q] ≤ (∑_n w_n^q)·E[(c∫_0^1)^q]`.  `RMF.integral_rpow_line_le` pays `8∑_n (1+n²)^{-q}`. -/
theorem integral_rpow_line_le_sharp {X : ℕ → Ω → ℂ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hσ : 1 / 2 ≤ σ) (hX : IsSteinhausPrimeValues X μ) (N : ℕ) {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    (∫ ω, (c * ∫ t : ℝ, lineDivSq σ X N ω t) ^ q ∂μ)
      ≤ (∑' n : ℤ, lineWeight n ^ q)
        * ∫ ω, (c * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ := by
  have hMnn : (0 : ℝ) ≤ ∫ ω, (c * ∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg hc (integral_lineSq_nonneg σ 0 1)) q
  have hae := ae_forall_norm_le_one hX norm_le_one_steinhausLaw N
  refine integral_rpow_line_le_sharpOf (C := eulerBound N) σ hσ N ?_ ?_ ?_ hc hq0 hq1 hMnn ?_
  · filter_upwards [hae] with ω hω
    exact ⟨measurable_randomEulerProduct_compMult_line σ hσ hω,
      fun t => norm_randomEulerProduct_le hω (by simpa using hσ)⟩
  · intro n
    have hrot : Measurable fun ω =>
        (fun p : Nat.Primes => shiftConst (n : ℝ) (p : ℕ) * X (p : ℕ) ω) :=
      measurable_pi_lambda _ fun p => (hX.measurable (p : ℕ) p.2).const_mul _
    have h1 : Measurable fun ω => unitFunctional σ N
        (fun p : Nat.Primes => shiftConst (n : ℝ) (p : ℕ) * X (p : ℕ) ω) :=
      (measurable_unitFunctional σ N).comp hrot
    refine h1.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    simp only [lineSqOf]
    exact (window_eq_unitFunctional σ hσ (X := X) (N := N) (ω := ω) (n : ℝ) hω).symm
  · have h1 : Measurable fun ω => lineFunctional σ N (fun p : Nat.Primes => X (p : ℕ) ω) :=
      (measurable_lineFunctional σ N).comp
        (measurable_pi_lambda _ fun p : Nat.Primes => hX.measurable (p : ℕ) p.2)
    refine h1.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    simp only [lineDivSqOf]
    exact lineFunctional_eq σ hσ hω
  · intro n
    change (∫ ω, (c * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSq σ X N ω t) ^ q ∂μ) ≤ _
    have hs : ∀ m : ℝ, (∫ ω, (c * ∫ t in Set.Ioc m (m + 1), lineSq σ X N ω t) ^ q ∂μ)
        = c ^ q * ∫ ω, (∫ t in Set.Ioc m (m + 1), lineSq σ X N ω t) ^ q ∂μ := by
      intro m
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        Real.mul_rpow hc (integral_lineSq_nonneg σ m (m + 1)))
    have hw : (∫ ω, (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), lineSq σ X N ω t) ^ q ∂μ)
        = ∫ ω, (∫ h in Set.Ioc (0 : ℝ) 1, lineSq σ X N ω h) ^ q ∂μ := by
      simp only [lineSq]
      exact integral_rpow_window_eq σ hσ hX N (n : ℝ) q
    refine le_of_eq ?_
    rw [hs (n : ℝ), hw, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (Real.mul_rpow hc (integral_lineSq_nonneg σ 0 1)).symm)

end RMF
