/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerReduction
import RMF.Weighted.CentralWindow
import RMF.Probability.RademacherRestrictedSecondMoment.Drift

/-!
# The damped line integral: the Cauchy weight, Fubini and Jensen

The subtracted term of the weighted lower bound
(`RMF.exists_le_integral_rpow_weightedRademacherSum_euler`) is
`C e^{-Vq} (log x)^{-q} E[J^q]`, with `J = ∫_ℝ |F(½+σ+it)|²/|σ+it|² dt` at `σ = V/log x`.
Gerspach (*Low pseudomoments of the Riemann zeta function and its powers*, arXiv:1909.10224)
bounds such a term, for his `d_α`-weighted pseudomoments, by Hölder and the second moment of the
Euler product on dyadic ranges of `t`.  At `α = 1`, for the Rademacher function, Jensen does it in
one step:

`E[J^q] ≤ (E J)^q = ((π/σ) E|F(½+σ)|²)^q ≤ (C log x/σ)^q`,

because `E|F(½+σ+it)|²` does not depend on `t`: the dyadic split is there to produce the factor
`1/σ`, and `∫_ℝ dt/(σ²+t²) = π/σ` supplies it directly.  So for `V ≥ 2 log log x` the subtracted
term is at most `C (log x)^{-q}`.

This file proves the general steps, for any jointly measurable, almost surely bounded integrand:
the Cauchy integral (`RMF.integral_inv_sq_add_sq`), Fubini for a damped line integral over any set
of heights (`RMF.setIntegral_integral_lineDiv_le`), and the Jensen bound for its `q`-th moment
(`RMF.integral_rpow_setIntegral_lineDiv_le`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The Cauchy weight -/

/-- `(σ²+t²)⁻¹ = σ⁻² (1+(t/σ)²)⁻¹`. -/
lemma inv_sq_add_sq_eq {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    (σ ^ 2 + t ^ 2)⁻¹ = (σ ^ 2)⁻¹ * (1 + (t / σ) ^ 2)⁻¹ := by
  rw [← mul_inv, mul_add, mul_one, div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hσ)]

/-- `t ↦ (σ²+t²)⁻¹` is integrable on `ℝ`. -/
lemma integrable_inv_sq_add_sq {σ : ℝ} (hσ : σ ≠ 0) :
    Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
  ((integrable_inv_one_add_sq.comp_div hσ).const_mul (σ ^ 2)⁻¹).congr
    (Filter.Eventually.of_forall fun t => (inv_sq_add_sq_eq hσ t).symm)

/-- `∫_ℝ dt/(σ²+t²) = π/σ`: the Cauchy integral, by `t = σu`. -/
lemma integral_inv_sq_add_sq {σ : ℝ} (hσ : 0 < σ) :
    ∫ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ = Real.pi / σ := by
  simp_rw [inv_sq_add_sq_eq hσ.ne']
  rw [integral_const_mul, Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2)⁻¹) σ,
    integral_univ_inv_one_add_sq, abs_of_pos hσ, smul_eq_mul]
  field_simp

/-! ### The first moment of the damped line integral -/

/-- **Fubini for a damped line integral over a set.**  If `F(ω, t)` is jointly measurable, bounded
by `U` almost surely uniformly in `t`, and `E|F(·, t)|² ≤ M` at every height, then for any set `S`
of heights `E ∫_S |F(·, t)|²/|σ+it|² dt ≤ (∫_S dt/(σ²+t²))·M`. -/
lemma setIntegral_integral_lineDiv_le {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ → ℂ}
    {S : Set ℝ} {σ U M : ℝ} (hσ : 0 < σ) (hF : Measurable (Function.uncurry F))
    (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U) (hM : ∀ t, ∫ ω, ‖F ω t‖ ^ 2 ∂μ ≤ M) :
    ∫ ω, (∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ∂μ
      ≤ (∫ t in S, (σ ^ 2 + t ^ 2)⁻¹) * M := by
  have hpos : ∀ t : ℝ, 0 < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hpt : ∀ ω t, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := fun ω t => by
    rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
      Complex.normSq_add_mul_I, div_eq_mul_inv]
  simp_rw [hpt]
  have hρ := integrable_inv_sq_add_sq hσ.ne'
  have hcont : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => (hpos t).ne'
  -- the product integrand is integrable, dominated by `U² (σ²+t²)⁻¹`
  have hmeas : Measurable (Function.uncurry fun ω t => ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹) :=
    (hF.norm.pow_const 2).mul (hcont.measurable.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun ω t => ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹)
      (μ.prod (volume.restrict S)) := by
    refine Integrable.mono' ((integrable_const (U ^ 2)).mul_prod hρ.integrableOn)
      hmeas.aestronglyMeasurable
      ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := volume.restrict S)).ae hU] with z hz
    change ‖‖F z.1 z.2‖ ^ 2 * (σ ^ 2 + z.2 ^ 2)⁻¹‖ ≤ U ^ 2 * (σ ^ 2 + z.2 ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hpos _).le))]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hz z.2) 2)
      (inv_nonneg.2 (hpos _).le)
  rw [integral_integral_swap hint]
  calc (∫ t in S, ∫ ω, ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ ∂μ)
      = ∫ t in S, (∫ ω, ‖F ω t‖ ^ 2 ∂μ) * (σ ^ 2 + t ^ 2)⁻¹ :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => integral_mul_const _ _)
    _ ≤ ∫ t in S, M * (σ ^ 2 + t ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => ?_)
          (hρ.const_mul M).integrableOn (Filter.Eventually.of_forall fun t => ?_)
        · exact mul_nonneg (integral_nonneg fun ω => sq_nonneg _) (inv_nonneg.2 (hpos t).le)
        · exact mul_le_mul_of_nonneg_right (hM t) (inv_nonneg.2 (hpos t).le)
    _ = (∫ t in S, (σ ^ 2 + t ^ 2)⁻¹) * M := by
        rw [integral_const_mul]
        ring

/-- **Fubini for a damped line integral.**  If `F(ω, t)` is jointly measurable, bounded by `U`
almost surely uniformly in `t`, and `E|F(·, t)|² ≤ M` at every height, then
`E ∫_ℝ |F(·, t)|²/|σ+it|² dt ≤ (π/σ) M`.

The whole line `S = ℝ` of `RMF.setIntegral_integral_lineDiv_le`, where the weight integrates to
`π/σ`. -/
lemma integral_integral_lineDiv_le {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ → ℂ}
    {σ U M : ℝ} (hσ : 0 < σ) (hF : Measurable (Function.uncurry F))
    (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U) (hM : ∀ t, ∫ ω, ‖F ω t‖ ^ 2 ∂μ ≤ M) :
    ∫ ω, (∫ t : ℝ, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ∂μ
      ≤ Real.pi / σ * M := by
  have h := setIntegral_integral_lineDiv_le (μ := μ) (F := F) (S := Set.univ) hσ hF hU hM
  simp only [Measure.restrict_univ] at h
  rwa [integral_inv_sq_add_sq hσ] at h

/-- **A damped line integral over a set has integrable powers.**  If `F(ω, t)` is jointly
measurable and bounded by `U` almost surely uniformly in `t`, then for `L > 0` and `q ≥ 0` the
functional `(L⁻¹∫_S |F(·, t)|²/|σ+it|² dt)^q` is integrable: it is measurable by Tonelli in its
strongly measurable form, and bounded almost surely by `(L⁻¹U²∫_S dt/(σ²+t²))^q`. -/
lemma integrable_rpow_setIntegral_lineDiv_of_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ → ℂ} {S : Set ℝ} {σ U L q : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hq0 : 0 ≤ q)
    (hF : Measurable (Function.uncurry F)) (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U) :
    Integrable (fun ω =>
      (L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ := by
  have hpos : ∀ t : ℝ, 0 < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hpt : ∀ ω t, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := fun ω t => by
    rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
      Complex.normSq_add_mul_I, div_eq_mul_inv]
  have hρ := integrable_inv_sq_add_sq hσ.ne'
  -- the functional is measurable
  have hden : Measurable fun z : Ω × ℝ => (σ : ℂ) + (z.2 : ℂ) * Complex.I :=
    ((Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I).const_add _
  have hGm : Measurable fun z : Ω × ℝ =>
      ‖F z.1 z.2 / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 :=
    (hF.div hden).norm.pow_const 2
  have hZm : Measurable fun ω =>
      ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict S)
      hGm.stronglyMeasurable).measurable
  -- and bounded almost surely
  have hZ0 : ∀ ω, (0 : ℝ) ≤ L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    fun ω => mul_nonneg (inv_nonneg.2 hL.le) (integral_nonneg fun t => sq_nonneg _)
  have hZb : ∀ᵐ ω ∂μ, (L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ L⁻¹ * (U ^ 2 * ∫ t in S, (σ ^ 2 + t ^ 2)⁻¹) := by
    filter_upwards [hU] with ω hω
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hL.le)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (hρ.const_mul (U ^ 2)).integrableOn (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hpt ω t]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hω t) 2)
      (inv_nonneg.2 (hpos t).le)
  refine (memLp_top_of_bound
    ((Real.continuous_rpow_const hq0).measurable.comp (hZm.const_mul L⁻¹)).aestronglyMeasurable
    ((L⁻¹ * (U ^ 2 * ∫ t in S, (σ ^ 2 + t ^ 2)⁻¹)) ^ q) ?_).integrable le_top
  filter_upwards [hZb] with ω hω
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hZ0 ω) _)]
  exact Real.rpow_le_rpow (hZ0 ω) hω hq0

/-- **The `q`-th moment of a damped line integral over a set, by Jensen.**  Under the hypotheses of
`RMF.setIntegral_integral_lineDiv_le`, for `L > 0` and `0 ≤ q ≤ 1`,
`E[(L⁻¹∫_S |F(·, t)|²/|σ+it|² dt)^q] ≤ (L⁻¹·(∫_S dt/(σ²+t²))·M)^q`.  The functional and its
`q`-th power are integrable by `RMF.integrable_rpow_setIntegral_lineDiv_of_bound`, and Jensen
applies. -/
theorem integral_rpow_setIntegral_lineDiv_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ → ℂ} {S : Set ℝ} {σ U M L q : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hF : Measurable (Function.uncurry F)) (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U)
    (hM : ∀ t, ∫ ω, ‖F ω t‖ ^ 2 ∂μ ≤ M) :
    (∫ ω, (L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (L⁻¹ * ((∫ t in S, (σ ^ 2 + t ^ 2)⁻¹) * M)) ^ q := by
  have hZ0 : ∀ ω, (0 : ℝ) ≤ L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    fun ω => mul_nonneg (inv_nonneg.2 hL.le) (integral_nonneg fun t => sq_nonneg _)
  have hZqi := integrable_rpow_setIntegral_lineDiv_of_bound (S := S) (q := q) hσ hL hq0 hF hU
  have hZi : Integrable (fun ω =>
      L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) μ := by
    simpa only [Real.rpow_one] using
      integrable_rpow_setIntegral_lineDiv_of_bound (S := S) (q := 1) hσ hL zero_le_one hF hU
  -- the mean, by Fubini
  have hmean : (∫ ω, (L⁻¹ * ∫ t in S, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ∂μ)
      ≤ L⁻¹ * ((∫ t in S, (σ ^ 2 + t ^ 2)⁻¹) * M) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (setIntegral_integral_lineDiv_le hσ hF hU hM)
      (inv_nonneg.2 hL.le)
  -- Jensen
  refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
    (Filter.Eventually.of_forall hZ0) hZi hZqi) ?_
  exact Real.rpow_le_rpow (integral_nonneg hZ0) hmean hq0

end RMF
