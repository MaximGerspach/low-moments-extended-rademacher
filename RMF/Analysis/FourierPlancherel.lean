/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Plancherel for a concrete `L¹ ∩ L²` function

Mathlib has Plancherel, as `MeasureTheory.Lp.norm_fourier_eq`, but only for the abstract `L²`
transform `Lp.fourierTransformₗᵢ`, which is built by extending the Schwartz-space transform along
a dense embedding.  The only bridges out of it are `SchwartzMap.toLp_fourier_eq` and
`Lp.fourier_toTemperedDistribution_eq`; nothing connects it to `Real.fourierIntegral`, so the
isometry cannot be applied to a function given by a formula.

This file supplies the missing link: for `f ∈ L¹ ∩ L²` the abstract transform of `f`'s class in
`L²` agrees almost everywhere with the concrete integral `𝓕 f`.  The proof is the standard one,
and every ingredient is already in Mathlib:

* both sides are locally integrable (`MemLp.locallyIntegrable`, and `𝓕 f` is continuous);
* they define the same tempered distribution — on the `L²` side by
  `Lp.fourier_toTemperedDistribution_eq` and `TemperedDistribution.fourier_apply`, on the `L¹`
  side by the multiplication formula `VectorFourier.integral_fourierIntegral_smul_eq_flip`,
  which needs only integrability of both arguments;
* a locally integrable function is determined almost everywhere by the distribution it defines
  (`ae_eq_of_integral_contDiff_smul_eq`).

The route through test functions is copied from Mathlib's own
`MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot`, which performs the same manoeuvre.

The application is Parseval for Dirichlet series (Montgomery–Vaughan (5.26),
`RMF.integral_normSq_partialSum_eq_line`): after the substitution `u = e^v` its integrand is
`‖g‖₂²` for `g v = A(e^v) e^{-σv}`, and the hypothesis `∑ ‖aₙ‖/n^σ < ∞` puts `g` in `L¹ ∩ L²`.
-/

open MeasureTheory FourierTransform SchwartzMap

namespace RMF

/-- **The `L¹ ∩ L²` bridge.**  For `f` both integrable and square-integrable, the abstract `L²`
Fourier transform of `f`'s class agrees a.e. with the concrete Fourier integral. -/
theorem coeFn_fourier_toLp {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    ⇑(𝓕 (h2.toLp) : Lp ℂ 2 volume) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ ℝ) continuous_inner h1
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hcont.locallyIntegrable ?_
  intro g hg hgs
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgs.comp_left rfl
  have hg₂ := Complex.ofRealCLM.contDiff.comp hg
  set G : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hGdef
  calc ∫ x, g x • (⇑(𝓕 (h2.toLp) : Lp ℂ 2 volume)) x
      = ((𝓕 (h2.toLp) : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) G := by simp [hGdef]
    _ = ((h2.toLp : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) (𝓕 G) := by
        rw [← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply]
    _ = ∫ x, (𝓕 (G : ℝ → ℂ)) x • f x := by
        rw [Lp.toTemperedDistribution_apply, ← SchwartzMap.fourier_coe]
        exact integral_congr_ae (by filter_upwards [h2.coeFn_toLp] with x hx; rw [hx])
    _ = ∫ x, g x • 𝓕 f x := by
        have hmul := VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ ℝ) (μ := volume) (ν := volume) (f := f) (g := (G : ℝ → ℂ))
          Real.continuous_fourierChar continuous_inner h1 G.integrable
        have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
          ext
          simp
        rw [hflip] at hmul
        have hmul' : (∫ ξ, 𝓕 f ξ • (G : ℝ → ℂ) ξ)
            = ∫ x, f x • 𝓕 (G : ℝ → ℂ) x := hmul
        have hcomm : ∀ x : ℝ, 𝓕 (G : ℝ → ℂ) x • f x = f x • 𝓕 (G : ℝ → ℂ) x := by
          intro x
          simp only [smul_eq_mul]
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hcomm), ← hmul']
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change 𝓕 f x * (g x : ℂ) = (g x : ℝ) • 𝓕 f x
        rw [Complex.real_smul, mul_comm]

/-- The `L²` norm of a class in `Lp ℂ 2` as an integral of `‖·‖²`. -/
lemma norm_sq_eq_integral_norm_sq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ a : ℝ, ‖f a‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm)

/-- **Plancherel in integral form**, for a concrete function.  This is
`MeasureTheory.Lp.norm_fourier_eq` made usable: the abstract isometry says nothing about a
function given by a formula until `RMF.coeFn_fourier_toLp` identifies the two transforms. -/
theorem integral_normSq_fourier {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 = ∫ v : ℝ, ‖f v‖ ^ 2 := by
  have hfour : ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2
      = ‖(𝓕 (h2.toLp) : Lp ℂ 2 volume)‖ ^ 2 := by
    rw [norm_sq_eq_integral_norm_sq]
    refine (integral_congr_ae ?_).symm
    filter_upwards [coeFn_fourier_toLp h1 h2] with x hx
    rw [hx]
  have hself : ∫ v : ℝ, ‖f v‖ ^ 2 = ‖(h2.toLp : Lp ℂ 2 volume)‖ ^ 2 := by
    rw [norm_sq_eq_integral_norm_sq]
    refine (integral_congr_ae ?_).symm
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [hfour, hself, Lp.norm_fourier_eq]

end RMF
