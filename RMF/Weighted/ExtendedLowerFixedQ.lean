/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedLowerMain
import RMF.Weighted.ExtendedLowerDamped
import RMF.Weighted.ExtendedFracPart

/-!
# The extended Rademacher sum at fixed `q < ½`: the lower bound

For fixed `0 < q < ½` there are `c > 0` and `x₀` with

`c (log log x)^{-q/2} ≤ E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q}`   for `x ≥ x₀`

(`RMF.exists_le_integral_rpow_normalisedSum_compMultExtension_smallQ_fixed`), the lower half of
Theorem 1.1 below `½`.  It is
`RMF.exists_le_integral_rpow_extendedSum_euler` at a constant `V` depending on `q`, assembled by
the weighted chain's `RMF.smallQ_fixed_assembly`: the main term against Harper's window through
`RMF.exists_rpow_log_mul_integral_chaosShift_le_extended`, the subtracted term against
`RMF.exists_const_integral_rpow_lineDivSq_extended_le`.

With the uniform upper bound this gives the order of magnitude
(`RMF.exists_integral_rpow_normalisedSum_compMultExtension_asymp_smallQ`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `|x^{-1/2}S|^{2q} = x^{-q}|S|^{2q}`. -/
lemma norm_normalisedSum_rpow_eq {f : Ω → ArithmeticFunction ℂ} {x : ℝ} (hx : 0 < x) (q : ℝ)
    (ω : Ω) :
    ‖normalisedSum f x ω‖ ^ (2 * q) = x ^ (-q) * ‖randomSum f x ω‖ ^ (2 * q) := by
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [normalisedSum, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    Real.div_rpow (norm_nonneg _) hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le,
    show (1 / 2 : ℝ) * (2 * q) = q by ring, Real.rpow_neg hx.le, div_eq_inv_mul]

/-- `E|x^{-1/2}S|^{2q} = x^{-q}E|S|^{2q}`. -/
lemma integral_norm_normalisedSum_rpow_eq {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    {x : ℝ} (hx : 0 < x) (q : ℝ) :
    ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
      = x ^ (-q) * ∫ ω, ‖randomSum f x ω‖ ^ (2 * q) ∂μ := by
  simp_rw [norm_normalisedSum_rpow_eq hx q]
  exact integral_const_mul _ _

/-- The reduction's factor `(x/log x)^q` against the normalisation `x^{-q}`. -/
lemma sub_le_rpow_neg_mul_of_reduction {ES EW EJ x L c C e q : ℝ} (hx : 0 < x) (hL : 0 < L)
    (h : c * (x / L) ^ q * EW - C * e * (x / L) ^ q * EJ - C * (x / L) ^ q ≤ ES) :
    c * L ^ (-q) * EW - C * e * L ^ (-q) * EJ - C * L ^ (-q) ≤ x ^ (-q) * ES := by
  have hxL : (x / L) ^ q * x ^ (-q) = L ^ (-q) := by
    rw [Real.div_rpow hx.le hL.le, Real.rpow_neg hx.le, Real.rpow_neg hL.le,
      div_mul_eq_mul_div, mul_inv_cancel₀ (Real.rpow_pos_of_pos hx q).ne', one_div]
  calc c * L ^ (-q) * EW - C * e * L ^ (-q) * EJ - C * L ^ (-q)
      = x ^ (-q) * (c * (x / L) ^ q * EW - C * e * (x / L) ^ q * EJ - C * (x / L) ^ q) := by
        rw [← hxL]
        ring
    _ ≤ x ^ (-q) * ES := mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos hx _).le

/-- `min 1 c ≤ c^q` for `c > 0` and `0 ≤ q ≤ 1`. -/
lemma min_one_le_rpow {c q : ℝ} (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : min 1 c ≤ c ^ q := by
  rcases le_total c 1 with h | h
  · calc min 1 c ≤ c := min_le_right _ _
      _ = c ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ c ^ q := Real.rpow_le_rpow_of_exponent_ge hc h hq1
  · exact le_trans (min_le_left _ _) (Real.one_le_rpow h hq0)

/-- **The lower bound at fixed `q < ½`, for the extended sum** (Theorem 1.1, lower
bound, for `0 < q < ½`).  For fixed `0 < q < ½` there are `c > 0` and `x₀` such that for every
Rademacher `X` and every `x ≥ x₀`,

`c (log log x)^{-q/2} ≤ E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q}`.

`RMF.exists_le_integral_rpow_extendedSum_euler` at a constant `V`: the window against Harper's
(`RMF.exists_rpow_log_mul_integral_chaosShift_le_extended`,
`RMF.exists_le_integral_rpow_chaosShift_rademacher_eventually`), the subtracted term against
`RMF.exists_const_integral_rpow_lineDivSq_extended_le`, `V` chosen by
`RMF.exp_neg_mul_le_mul_rpow_neg`, and the arithmetic of `RMF.smallQ_fixed_assembly`. -/
theorem exists_le_integral_rpow_normalisedSum_compMultExtension_smallQ_fixed {q : ℝ}
    (hq0 : 0 < q) (hq2 : q < 1 / 2) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        c * Real.log (Real.log x) ^ (-(q / 2))
          ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨c₀, C₀, x₁, hc₀, hC₀, hred⟩ := exists_le_integral_rpow_extendedSum_euler (Ω := Ω)
  obtain ⟨cL, hcL, hch⟩ := exists_le_integral_rpow_chaosShift_rademacher_eventually (Ω := Ω)
  obtain ⟨c₂, hc₂, hwin⟩ := exists_rpow_log_mul_integral_chaosShift_le_extended (Ω := Ω)
  obtain ⟨K, x₃, hK, hup⟩ := exists_const_integral_rpow_lineDivSq_extended_le (Ω := Ω)
  have hα : 0 < q * (1 - 2 * q) := mul_pos hq0 (by linarith)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = K * (1 + (q * (1 - 2 * q))⁻¹) := ⟨_, rfl⟩
  have hK' : 0 < K' := by
    rw [hK'def]
    exact mul_pos hK (by positivity)
  obtain ⟨cL', hcL'def⟩ : ∃ cL' : ℝ, cL' = min 1 c₂ * cL := ⟨_, rfl⟩
  have hcL' : 0 < cL' := by
    rw [hcL'def]
    exact mul_pos (lt_min one_pos hc₂) hcL
  obtain ⟨hV2, hVe⟩ := exp_neg_mul_le_mul_rpow_neg
    (show 0 < c₀ * cL' / (2 * C₀ * K') by positivity) hq0
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = 2 + 2 * |Real.log (c₀ * cL' / (2 * C₀ * K'))| / q :=
    ⟨_, rfl⟩
  rw [← hVdef] at hV2 hVe
  have hV0 : 0 < V := by linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = c₀ * cL' * V ^ (-q) / 4 := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    positivity
  have hLL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((hch (V / 2) (by linarith) q hq0 (by linarith)).and
      ((Filter.eventually_ge_atTop (max (max x₁ x₃) 2)).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop
            (max (3 * V + 3) ((C₀ / ε) ^ (2 / q)))).and
          (hLL.eventually_ge_atTop 1))))
  refine ⟨ε, x₀, hε, fun X μ hX x hx => ?_⟩
  obtain ⟨hchx, hxm, hLm, hΛ1⟩ := hx₀ x hx
  have hΛ1' : (1 : ℝ) ≤ Real.log (Real.log x) := hΛ1
  haveI := hX.isProbabilityMeasure
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxm
  have hx₃ : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxm
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hxm
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogV : 3 * V + 3 ≤ Real.log x := le_trans (le_max_left _ _) hLm
  have hLC : (C₀ / ε) ^ (2 / q) ≤ Real.log x := le_trans (le_max_right _ _) hLm
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 < Real.log x := by linarith
  -- the reduction, normalised by `x^{-q}`
  have h1 := sub_le_rpow_neg_mul_of_reduction hx0 hL0 (hred X μ hX V x q hV0 hx₁ hlogV hq0 hq2.le)
  rw [← integral_norm_normalisedSum_rpow_eq hx0 q] at h1
  -- the main term, against Harper's window
  have hσ1 : 2 * V / Real.log x ≤ 1 := by
    rw [div_le_one hL0]
    linarith
  have h2 := hwin X μ hX x (2 * V / Real.log x) q (by linarith) (by positivity) hσ1 hq0.le
  have h2' : Real.log x ^ q * (c₂ ^ q * ∫ ω, chaosShift
        (fun ω => squarefreeExtension fun p => X p ω) x (2 * V / Real.log x) ω ^ q ∂μ)
      ≤ ∫ ω, (∫ t in Set.Ioo (-1 : ℝ) 1,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
            (((1 / 2 + 2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ := by
    refine le_trans (le_of_eq ?_) h2
    ring
  have h3 := hchx X μ hX
  rw [show 4 * (V / 2) / Real.log x = 2 * V / Real.log x by ring] at h3
  have h3' : cL' * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) * (V / 2) ^ (-q)
      ≤ c₂ ^ q * ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => X p ω) x
          (2 * V / Real.log x) ω ^ q ∂μ := by
    have hT0 : 0 ≤ cL * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
        * (V / 2) ^ (-q) :=
      mul_nonneg (mul_nonneg hcL.le (Real.rpow_nonneg
          (add_nonneg zero_le_one (mul_nonneg (by linarith) (Real.sqrt_nonneg _))) _))
        (Real.rpow_nonneg (by linarith) _)
    rw [hcL'def]
    calc min 1 c₂ * cL * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          * (V / 2) ^ (-q)
        = min 1 c₂ * (cL * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
          * (V / 2) ^ (-q)) := by ring
      _ ≤ c₂ ^ q * ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => X p ω) x
          (2 * V / Real.log x) ω ^ q ∂μ :=
        mul_le_mul (min_one_le_rpow hc₂ hq0.le (by linarith)) h3 hT0
          (Real.rpow_nonneg hc₂.le _)
  have hT := two_rpow_neg_mul_le_target hΛ1' hq0.le (by linarith)
  -- the subtracted term
  have h6 : (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
      ≤ Real.log x ^ q * (K' * Real.log (Real.log x) ^ (-(q / 2))) := by
    refine (hup X μ hX V x q (by linarith) hx₃ hq0 hq2).trans (le_of_eq ?_)
    rw [hK'def]
    ring
  -- the error term
  have hneg := mul_rpow_neg_le_mul_log_rpow_neg hC₀ hε hq0 hL1 hLC
  rw [hεdef] at hneg ⊢
  exact smallQ_fixed_assembly hL0 hΛ1' hV0 hc₀ hC₀ hcL' hK' h1 h2' h3' hT le_rfl h6 le_rfl
    hVe hneg

/-- **The order of magnitude at fixed `q < ½`, for the extended sum** (Theorem 1.1 for
`0 < q < ½`, here for `x ≥ x₀`).  For fixed `0 < q < ½`,

`E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≍ (log log x)^{-q/2}`:

the lower bound is `RMF.exists_le_integral_rpow_normalisedSum_compMultExtension_smallQ_fixed`,
the upper bound `RMF.exists_const_integral_rpow_normalisedSum_compMultExtension_le_smallQ_uniform`
at `((log log x)⁻¹ + (1-2q))⁻¹ ≤ (1-2q)⁻¹`. -/
theorem exists_integral_rpow_normalisedSum_compMultExtension_asymp_smallQ {q : ℝ} (hq0 : 0 < q)
    (hq2 : q < 1 / 2) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
        c * Real.log (Real.log x) ^ (-(q / 2))
            ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
          ∧ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
            ≤ C * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨c, x₁, hc, Hlow⟩ :=
    exists_le_integral_rpow_normalisedSum_compMultExtension_smallQ_fixed (Ω := Ω) hq0 hq2
  obtain ⟨C, x₂, hC, Hup⟩ :=
    exists_const_integral_rpow_normalisedSum_compMultExtension_le_smallQ_uniform (Ω := Ω)
  have h12 : 0 < 1 - 2 * q := by linarith
  refine ⟨c, C * (1 - 2 * q)⁻¹, max (max x₁ x₂) (Real.exp (Real.exp 1)), hc,
    mul_pos hC (inv_pos.2 h12), fun X μ hX x hx => ⟨Hlow X μ hX x
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx), ?_⟩⟩
  have hxe : Real.exp (Real.exp 1) ≤ x := le_trans (le_max_right _ _) hx
  have hΛ1 := one_le_log_log_of_exp_exp_le hxe
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  refine le_trans (Hup X μ hX x q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
    hq0 hq2.le) ?_
  have hA : ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ ≤ (1 - 2 * q)⁻¹ :=
    inv_anti₀ h12 (by linarith [inv_pos.2 hΛ0])
  have hP0 : 0 ≤ Real.log (Real.log x) ^ (-(q / 2)) := Real.rpow_nonneg hΛ0.le _
  calc C * (((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ * Real.log (Real.log x) ^ (-(q / 2)))
      ≤ C * ((1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hP0) hC.le
    _ = C * (1 - 2 * q)⁻¹ * Real.log (Real.log x) ^ (-(q / 2)) := by ring

end RMF
