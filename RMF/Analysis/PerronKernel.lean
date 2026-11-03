/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Perron kernel `1/s²`

The Mellin pair `max(-log u, 0) ↔ 1/s²` and the Perron formula it gives: for `σ > 0`, `u > 0`,

`(1/2π) ∫_ℝ u^{-(σ+iy)}/(σ+iy)² dy = max(-log u, 0)` (`RMF.perron_kernel_sq`).

At `u = n/x` it turns `(1/2πi)∫ (∑ aₙ n^{-s}) x^s ds/s²` into the Riesz mean
`∑_{n≤x} aₙ log(x/n)`.  The forward transform (`RMF.hasMellin_neg_log_Ioc`) is minus the
derivative in `s` of Mathlib's `hasMellin_one_Ioc`; the inversion is `mellinInv_mellin_eq`, for
which the kernel `1/(σ+iy)²` is integrable on the line and `max(-log u, 0)` is continuous on
`(0, ∞)`.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace RMF

/-- **The Mellin transform of `-log` on `(0, 1]`** is `1/s²` for `Re s > 0`: minus the derivative
of `1/s`, the transform of the indicator (`hasMellin_one_Ioc`), differentiated under the integral
(`mellin_hasDerivAt_of_isBigO_rpow`). -/
theorem hasMellin_neg_log_Ioc {s : ℂ} (hs : 0 < s.re) :
    HasMellin (indicator (Ioc 0 1) fun t => -(Real.log t : ℂ)) s (1 / s ^ 2) := by
  set f : ℝ → ℂ := indicator (Ioc 0 1) fun _ => (1 : ℂ) with hfdef
  have hfi : Integrable f := by
    rw [hfdef, integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp)
  have hfc : LocallyIntegrableOn f (Ioi 0) := hfi.locallyIntegrable.locallyIntegrableOn _
  have htop : f =O[atTop] (· ^ (-(s.re + 1))) := by
    refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [hfdef, indicator_of_notMem fun h => by linarith [h.2]]
  have hbot : f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, hfdef]
    by_cases ht : t ∈ Ioc 0 1
    · rw [indicator_of_mem ht, norm_one]
    · rw [indicator_of_notMem ht, norm_zero]
      exact zero_le_one
  obtain ⟨hconv, hderiv⟩ :=
    mellin_hasDerivAt_of_isBigO_rpow hfc htop (by linarith) hbot (by simpa using hs)
  have heq : mellin f =ᶠ[𝓝 s] fun z => z⁻¹ := by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show s ∈ Complex.re ⁻¹' Ioi 0 from hs)] with z hz
    rw [(hasMellin_one_Ioc hz).2, one_div]
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have huniq := hderiv.unique ((hasDerivAt_inv hs0).congr_of_eventuallyEq heq)
  have hg : (indicator (Ioc 0 1) fun t => -(Real.log t : ℂ))
      = fun t => (-1 : ℂ) • (Real.log t • f t) := by
    funext t
    rw [hfdef]
    by_cases ht : t ∈ Ioc 0 1
    · rw [indicator_of_mem ht, indicator_of_mem ht, Complex.real_smul, smul_eq_mul]
      ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero, smul_zero]
  rw [hg]
  refine ⟨hconv.const_smul (-1 : ℂ), ?_⟩
  rw [mellin_const_smul, huniq, smul_eq_mul, neg_one_mul, neg_neg, one_div]

/-- The kernel `1/(σ+iy)²` has modulus `(σ² + y²)⁻¹`. -/
lemma norm_one_div_sq_vertical (σ y : ℝ) :
    ‖1 / ((σ : ℂ) + y * Complex.I) ^ 2‖ = (σ ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_div, norm_one, norm_pow, Complex.sq_norm, Complex.normSq_add_mul_I, one_div]

/-- `y ↦ 1/(σ+iy)²` is integrable on `ℝ` for `σ ≠ 0`: its modulus is `σ⁻²(1 + (y/σ)²)⁻¹`. -/
lemma integrable_one_div_sq_vertical {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable fun y : ℝ => 1 / ((σ : ℂ) + y * Complex.I) ^ 2 := by
  have hne : ∀ y : ℝ, ((σ : ℂ) + y * Complex.I) ^ 2 ≠ 0 := fun y => by
    refine pow_ne_zero 2 fun h => hσ ?_
    simpa using congrArg Complex.re h
  have hcont : Continuous fun y : ℝ => 1 / ((σ : ℂ) + y * Complex.I) ^ 2 :=
    continuous_const.div (by fun_prop) hne
  have hdom : Integrable fun y : ℝ => (σ ^ 2)⁻¹ * (1 + (y / σ) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_div hσ).const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_one_div_sq_vertical, ← mul_inv, mul_add, mul_one, div_pow,
    mul_div_cancel₀ _ (pow_ne_zero 2 hσ)]

/-- The Perron integrand `y ↦ u^{-(σ+iy)}/(σ+iy)²` is integrable on `ℝ` for `σ ≠ 0` and `u > 0`:
the power has modulus `u^{-σ}`. -/
lemma integrable_cpow_neg_div_sq_vertical {σ u : ℝ} (hσ : σ ≠ 0) (hu : 0 < u) :
    Integrable fun y : ℝ =>
      (u : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) / ((σ : ℂ) + y * Complex.I) ^ 2 := by
  have hcont : Continuous fun y : ℝ => (u : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.2 hu.ne'))
  have h := (integrable_one_div_sq_vertical hσ).bdd_mul (c := u ^ (-σ))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  · simpa only [mul_one_div] using h
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp

/-- **The Perron kernel `1/s²`.**  For `σ > 0` and `u > 0`,
`(1/2π) ∫_ℝ u^{-(σ+iy)}/(σ+iy)² dy = max(-log u, 0)`: Mellin inversion
(`mellinInv_mellin_eq`) for the pair of `RMF.hasMellin_neg_log_Ioc`. -/
theorem perron_kernel_sq {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < u) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
        (u : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) / ((σ : ℂ) + y * Complex.I) ^ 2
      = ((max (-Real.log u) 0 : ℝ) : ℂ) := by
  set f : ℝ → ℂ := indicator (Ioc 0 1) fun t => -(Real.log t : ℂ) with hfdef
  have hM : ∀ y : ℝ, mellin f ((σ : ℂ) + y * Complex.I) = 1 / ((σ : ℂ) + y * Complex.I) ^ 2 :=
    fun y => (hasMellin_neg_log_Ioc (by simpa using hσ)).2
  have hconv : MellinConvergent f σ := (hasMellin_neg_log_Ioc (by simpa using hσ)).1
  have hvert : Complex.VerticalIntegrable (mellin f) σ := by
    rw [Complex.VerticalIntegrable]
    simp_rw [hM]
    exact integrable_one_div_sq_vertical hσ.ne'
  -- `f = max(-log, 0)` on `(0, ∞)`, which is continuous there
  have hfmax : ∀ t : ℝ, 0 < t → f t = ((max (-Real.log t) 0 : ℝ) : ℂ) := by
    intro t ht
    rw [hfdef]
    by_cases ht1 : t ≤ 1
    · rw [indicator_of_mem (show t ∈ Ioc 0 1 from ⟨ht, ht1⟩),
        max_eq_left (neg_nonneg.2 (Real.log_nonpos ht.le ht1)), Complex.ofReal_neg]
    · rw [indicator_of_notMem fun h => ht1 h.2,
        max_eq_right (neg_nonpos.2 (Real.log_nonneg (not_le.1 ht1).le)), Complex.ofReal_zero]
  have hcont : ContinuousAt f u := by
    have hc : ContinuousAt (fun t : ℝ => ((max (-Real.log t) 0 : ℝ) : ℂ)) u :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log hu.ne').neg).max continuousAt_const)
    refine hc.congr ?_
    filter_upwards [Ioi_mem_nhds hu] with t ht
    exact (hfmax t ht).symm
  have key := mellinInv_mellin_eq σ f hu hconv hvert hcont
  rw [mellinInv] at key
  simp_rw [hM, smul_eq_mul, mul_one_div] at key
  rw [← hfmax u hu, ← key, Complex.real_smul]
  push_cast
  rfl

end RMF
