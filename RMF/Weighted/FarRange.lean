/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.WindowDescent

/-!
# `Z_f`: the far range at the reduction's own denominator

The reduction to random Euler products leaves the line integral
`∫ ‖F(½+σ+it)/(σ+it)‖² dt`, with the numerator at `½+σ` and the denominator `σ+it`, because
Parseval is applied at the shift `σ` to the Dirichlet series of `X(m)m^{-1/2}`; in
`RMF.lineDivSqOf` the abscissa and the denominator are the same.  This file bounds the part
`1 < |t| ≤ M` of its far range `Z_f` (`RMF.exists_const_integral_rpow_lineMidDiv_le_rademacher`).

The denominator enters in one place only: the covering of `1 < |t| ≤ M` by the unit windows
`(n, n+1]` of `RMF.midWindows M`, the `n`-th paying `8/(1+n²)`.  That bound,
`|σ+it|^{-2} ≤ 8/(1+n²)` on `(n, n+1]`, holds for **any real** `σ` as long as `n ≥ 1` or
`n ≤ -2`, which is exactly the range `RMF.midWindows M` covers: the windows at `n = 0` and
`n = -1`, which the `½ ≤ σ` of `RMF.norm_div_sq_le` is there to control, are the ones `|t| > 1`
excludes.  Everything after the covering (`RMF.chaosWindowShift_eq_window`, the integrability,
the descent) is about the numerator only.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The windows of `midWindows` avoid the origin -/

/-- The windows `RMF.midWindows M` covers are exactly those at `n ≥ 1` or `n ≤ -2`. -/
lemma one_le_or_le_neg_two_of_mem_midWindows {M : ℕ} {n : ℤ} (hn : n ∈ midWindows M) :
    1 ≤ n ∨ n ≤ -2 := by
  rw [midWindows, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico] at hn
  rcases hn with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

/-- **The denominator bound, decoupled from the abscissa.**  On a window `(n, n+1]` with `n ≥ 1`
or `n ≤ -2`, dividing by `σ+it` costs at most `8/(1+n²)` for **every real** `σ`.

The `½ ≤ σ` of `RMF.norm_div_sq_le` exists only to cover the windows at `n = 0, -1`, where `t`
can vanish; away from them `|σ+it|² ≥ t²` is already enough, and the sign of `σ` never enters. -/
lemma norm_div_sq_le_of_mid {σ : ℝ} {n : ℤ} (hn : 1 ≤ n ∨ n ≤ -2)
    {t : ℝ} (h0 : (n : ℝ) < t) (h1 : t ≤ (n : ℝ) + 1) (z : ℂ) :
    ‖z / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤ 8 / (1 + (n : ℝ) ^ 2) * ‖z‖ ^ 2 := by
  have hnsq : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  have hlow : (1 + (n : ℝ) ^ 2) / 8 ≤ σ ^ 2 + t ^ 2 := by
    rcases hn with h | h
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg σ, sq_nonneg (t - (n : ℝ))]
    · have hn2 : ((n : ℝ)) ≤ -2 := by exact_mod_cast h
      nlinarith [sq_nonneg σ, sq_nonneg (t - (n : ℝ) - 1), sq_nonneg ((n : ℝ) + 2)]
  have hden : (0 : ℝ) < σ ^ 2 + t ^ 2 := by linarith
  have hstep : ‖z‖ ^ 2 / (σ ^ 2 + t ^ 2) ≤ ‖z‖ ^ 2 / ((1 + (n : ℝ) ^ 2) / 8) := by gcongr
  rw [norm_div, div_pow, normSq_ofReal_add_mul_I]
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ### The covering step, decoupled -/

omit [MeasurableSpace Ω] in
/-- **The mid-range of the decoupled line integral, as a window sum.**  With the numerator at `c`
and the denominator at `σ`, independently, `∫_{1<|t|≤M} ‖F(c+it)/(σ+it)‖² dt` is at most
`∑_{n ∈ midWindows M} 8/(1+n²)·∫_{(n,n+1]} ‖F(c+it)‖² dt`. -/
lemma setIntegral_mid_div_le_windowSum {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} {c σ : ℝ}
    (hc : 1 / 2 ≤ c) (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) (M : ℕ) :
    (∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∑ n ∈ midWindows M, 8 / (1 + (n : ℝ) ^ 2)
          * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
              lineSqOf c (fun ω => squarefreeExtension fun p => X p ω) N ω t := by
  have hmeas := measurable_randomEulerProduct_sqfree_line (X := X) (N := N) (ω := ω) c
  have hbd : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound N :=
    fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using hc)
  have hC0 : (0 : ℝ) ≤ eulerBound N := le_trans (norm_nonneg _) (hbd 0)
  -- the integrand is measurable, and bounded on every window away from the origin
  have hm : Measurable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    (hmeas.div (by fun_prop)).norm.pow_const 2
  have hint : ∀ n ∈ midWindows M, IntegrableOn
      (fun t : ℝ => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (Set.Ioc ((n : ℝ)) ((n : ℝ) + 1)) := by
    intro n hn
    refine Measure.integrableOn_of_bounded (M := 8 / (1 + (n : ℝ) ^ 2) * eulerBound N ^ 2)
      measure_Ioc_lt_top.ne hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine le_trans (norm_div_sq_le_of_mid (one_le_or_le_neg_two_of_mem_midWindows hn)
      ht.1 ht.2 _) ?_
    have h8 : (0 : ℝ) ≤ 8 / (1 + (n : ℝ) ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h8
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2
  refine le_trans (setIntegral_le_sum_window_of_cover _ (mid_subset_iUnion_midWindows M)
    (fun t => by positivity) hint) (Finset.sum_le_sum fun n hn => ?_)
  -- and the per-window bound
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hint n hn)
    ((integrableOn_windowOf c hmeas hbd ((n : ℝ)) ((n : ℝ) + 1)).const_mul _)
    measurableSet_Ioc fun t ht => ?_
  exact norm_div_sq_le_of_mid (one_le_or_le_neg_two_of_mem_midWindows hn) ht.1 ht.2 _

/-! ### The decoupled line integrand is integrable

Splitting `∫_ℝ` into the three ranges `Z_c + Z_m + Z_f` needs this once. -/

omit [MeasurableSpace Ω] in
/-- **The decoupled line integrand is integrable on `ℝ`.**  Bounded numerator over `σ²+t²`,
dominated by `C²·(2/min{σ²,1})·(1+t²)^{-1}`.

`RMF.integrable_line_integrand` is the coupled case; there `σ ≥ ½` makes the denominator
`≥ (1+t²)/8` outright, and here the small `σ` is what the `min` pays for. -/
lemma integrable_line_div_sq {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} {c σ : ℝ}
    (hc : 1 / 2 ≤ c) (hσ : 0 < σ) (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hmeas := measurable_randomEulerProduct_sqfree_line (X := X) (N := N) (ω := ω) c
  have hbd : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound N :=
    fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using hc)
  have hC0 : (0 : ℝ) ≤ eulerBound N := le_trans (norm_nonneg _) (hbd 0)
  have hmin : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (by positivity) one_pos
  have hm : Measurable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    (hmeas.div (by fun_prop)).norm.pow_const 2
  refine Integrable.mono'
    (g := fun t : ℝ => eulerBound N ^ 2 * (2 / min (σ ^ 2) 1) * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul _) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hlow : min (σ ^ 2) 1 * (1 + t ^ 2) / 2 ≤ σ ^ 2 + t ^ 2 := by
    rcases le_total (t ^ 2) 1 with h | h
    · nlinarith [min_le_left (σ ^ 2) 1, min_le_right (σ ^ 2) 1, sq_nonneg t]
    · nlinarith [min_le_left (σ ^ 2) 1, min_le_right (σ ^ 2) 1, sq_nonneg σ]
  have hlow0 : (0 : ℝ) < min (σ ^ 2) 1 * (1 + t ^ 2) / 2 := by positivity
  have hnum : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ≤ eulerBound N ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_div, div_pow,
    normSq_ofReal_add_mul_I]
  calc ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 / (σ ^ 2 + t ^ 2)
      ≤ eulerBound N ^ 2 / (min (σ ^ 2) 1 * (1 + t ^ 2) / 2) := by gcongr
    _ = eulerBound N ^ 2 * (2 / min (σ ^ 2) 1) * (1 + t ^ 2)⁻¹ := by
        field_simp

/-! ### The mid range, at the reduction's denominator -/

/-- **`Z_f`'s mid range, `1 < |t| ≤ M`, with the numerator at `½+σ` and the denominator at `σ`.**

The covering by the windows of `RMF.midWindows M` (`RMF.setIntegral_mid_div_le_windowSum`), the
only place the denominator appears, then the window-sum bound
`RMF.exists_const_integral_rpow_windowSum_chaos_le_rademacher`. -/
theorem exists_const_integral_rpow_lineMidDiv_le_rademacher (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (d : ℕ) (hE₁ : 10 * E₀ ≤ Real.exp d) :
    ∃ (D₀ : ℕ) (x₀ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ η q : ℝ) (M : ℕ), x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 2 / 3 →
          (M : ℝ) + 1 ≤ Real.log (Real.log x) ^ 2 →
          (∫ ω, ((Real.log x)⁻¹ * ∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)},
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
            ≤ (C * (1 + (1 - 2 / 3) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
                  ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2) := by
  classical
  obtain ⟨D₀, x₀, C, hC, H⟩ :=
    exists_const_integral_rpow_windowSum_chaos_le_rademacher (Ω := Ω) E₀ hE₀ d hE₁
  refine ⟨D₀, max x₀ 2, C, hC, ?_⟩
  intro Y ν hY x σ η q M hx hσ hη hηE hση hq0 hq hM
  haveI := hY.isProbabilityMeasure
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hlog0 : (0 : ℝ) ≤ (Real.log x)⁻¹ := inv_nonneg.2 (Real.log_nonneg (by linarith))
  have hσ' : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  -- the numerator's abscissa, as a real cast
  have hcast : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I)
      = (((1 / 2 + σ : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hmid0 : ∀ ω : Ω, (0 : ℝ) ≤ (Real.log x)⁻¹
      * ∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)},
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := fun ω =>
    mul_nonneg hlog0 (integral_nonneg fun t => by positivity)
  have hν : ∀ᵐ z ∂rademacherLaw, ‖z‖ ≤ 1 := by
    filter_upwards [norm_eq_one_rademacherLaw] with z hz
    exact le_of_eq hz
  have hae := ae_forall_norm_le_one hY hν (⌊x⌋₊ + 1)
  -- the pointwise comparison, through the decoupled covering
  have hpt : ∀ᵐ ω ∂ν, ((Real.log x)⁻¹ * ∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
      ≤ (∑ n ∈ midWindows M, 8 / (1 + (n : ℝ) ^ 2)
          * chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω)
        ^ q := by
    filter_upwards [hae] with ω hω
    refine Real.rpow_le_rpow (hmid0 ω) ?_ hq0
    have hstep := setIntegral_mid_div_le_windowSum (X := Y) (N := ⌊x⌋₊ + 1) (ω := ω)
      (c := 1 / 2 + σ) (σ := σ) hσ' hω M
    simp only [← hcast] at hstep
    have hmul := mul_le_mul_of_nonneg_left hstep hlog0
    refine le_trans hmul (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by
      rw [chaosWindowShift_eq_window (X := Y) x σ ω n]; ring
  have hint : Integrable (fun ω => (∑ n ∈ midWindows M, 8 / (1 + (n : ℝ) ^ 2)
      * chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω) ^ q) ν := by
    refine integrable_rpow_of_integrable
      (integrable_finsetSum _ fun n _ =>
        (integrable_chaosWindowShift_rademacher hY x σ ((n : ℝ)) hσ0).const_mul _)
      (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun n _ =>
        mul_nonneg (by positivity) (chaosWindowShift_nonneg hx2 σ ((n : ℝ)) ω)) hq0 (by linarith)
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hmid0 ω) _) hint hpt) ?_
  exact H Y ν hY x σ η q (midWindows M) hx0 hσ hη hηE hση hq0 hq
    fun n hn => le_trans (abs_le_of_mem_midWindows hn) hM

end RMF
