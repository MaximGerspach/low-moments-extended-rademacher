/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracReductionExplicit.Line
import RMF.Weighted.UAssemblyExplicit
import RMF.Weighted.CaichChaos

/-!
# The remainder's windows, I: the pieces of `Z_R`

The reduction of the remainder (`RMF.integral_norm_fracPartSum_le_lineFrac`) leaves
`E[Z_R^{1/2}]`, `Z_R = (log y)⁻¹∫_ℝ‖F_{y+1}(½+σ+it)‖²|φ̂(½+σ+it)|²dt`.  Here `Z_R` is cut into
pieces, each bounded with the weight `ρ(t) = |φ̂(½+σ+it)|²` kept inside.

* **The fold and the cut** (`RMF.integral_rpow_fracLine_le_four`): the integrand is even in `t`
  almost surely (the Rademacher coefficients are real, and `RMF.norm_fracMellin_neg`), so
  `Z_R = 2(log y)⁻¹∫_{t>0}`, and `(0,∞) = (0,a] ∪ (a,b] ∪ (b,c] ∪ (c,∞)` costs
  `E[Z_R^{1/2}] ≤ √2·∑ E[((log y)⁻¹∫_{piece})^{1/2}]`.
* **Jensen pieces** (`RMF.integral_rpow_fracPiece_le_jensen`): `≤ (1.195∫_{piece}ρ)^{1/2}`.
* **The windows** (`RMF.integral_rpow_fracMeso_le_sum_windows`,
  `RMF.integral_rpow_fracFar_le_sum_windows`): a range is cut into the `e`-adic windows
  `[T/e, T]`, the weight inside.
* **A mesoscopic window** (`RMF.window_frac_meso`): on `[e^{-k-1}, e^{-k}]`,
  `ρ ≤ 0.7151(σ² + e^{-2k})(σ²+t²)⁻¹`, onto `RMF.window_theta_le_chaos_q` at `q = ½`.
* **A far window** (`RMF.window_far_frac`): the weighted chaos with `ρ` itself, so the window's
  mass `∫_{[T/e,T]}ρ` enters, not its supremum.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The weight and the field -/

/-- The weight `t ↦ |φ̂(½+σ+it)|²` is measurable (continuous) for `σ > -½`. -/
lemma measurable_normSq_fracMellin_line {σ : ℝ} (hσ : -1 / 2 < σ) :
    Measurable fun t : ℝ => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 :=
  ((continuous_fracMellin_line hσ).norm.pow 2).measurable

/-- The weight is at most `0.7151` on `Re s = ½ + σ`, `σ ≥ 0`
(`RMF.normSq_fracMellin_le_numeral`). -/
lemma normSq_fracMellin_line_le {σ : ℝ} (hσ : 0 ≤ σ) (t : ℝ) :
    ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 0.7151 :=
  normSq_fracMellin_le_numeral (by simp; linarith)

/-- The weighted integrand is jointly measurable. -/
lemma measurable_uncurry_weight_normSq_randomEulerProduct {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) (σ : ℝ) {ρ : ℝ → ℝ} (hρm : Measurable ρ) :
    Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) => ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
        ^ 2) := by
  have h := measurable_randomEulerProduct_sqfree_uncurry (X := X)
    (fun p hp => hX.measurable p hp) (1 / 2 + σ) n
  exact (hρm.comp measurable_snd).mul (h.norm.pow_const 2)

/-- The envelope along the line `Re s = ½ + σ`, `σ ≥ 0`. -/
lemma ae_forall_norm_randomEulerProduct_shiftLine_le_rad {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
        ≤ ∏ p ∈ Nat.primesBelow n, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) := by
  filter_upwards [ae_forall_norm_randomEulerProduct_mem_Icc hX n (c := 1 / 2 + σ)
    (by linarith)] with ω hω t
  exact (hω _ (re_shiftLine σ t)).2

/-- Under the envelope `U`, `∫_S ρ‖F‖² ≤ U²∫_S ρ` for a weight `ρ ≥ 0` integrable on `S`. -/
lemma setIntegral_weight_normSq_le_of_envelope {f : ℝ → ℂ} {ρ : ℝ → ℝ} {S : Set ℝ} {U : ℝ}
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : IntegrableOn ρ S) (hU : ∀ t, ‖f t‖ ≤ U) :
    (∫ t in S, ρ t * ‖f t‖ ^ 2) ≤ U ^ 2 * ∫ t in S, ρ t := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => ?_)
    (hρi.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
  · exact mul_nonneg (hρ0 t) (sq_nonneg _)
  · change ρ t * ‖f t‖ ^ 2 ≤ U ^ 2 * ρ t
    rw [mul_comm (U ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hU t) 2) (hρ0 t)

/-- The weighted integrand is integrable on `S` under the envelope. -/
lemma integrableOn_weight_normSq_of_envelope {f : ℝ → ℂ} {ρ : ℝ → ℝ} {S : Set ℝ} {U : ℝ}
    (hf : Measurable f) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : IntegrableOn ρ S)
    (hU : ∀ t, ‖f t‖ ≤ U) :
    IntegrableOn (fun t => ρ t * ‖f t‖ ^ 2) S := by
  refine Integrable.mono' (hρi.mul_const (U ^ 2))
    ((hρm.mul (hf.norm.pow_const 2)).aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hU t) 2) (hρ0 t)

/-- **A piece is integrable**: for a measurable weight `ρ ≥ 0` integrable on `S`, `a ≥ 0` and
`r ≥ 0`, `ω ↦ (a∫_S ρ‖F_n(½+σ+it)‖²dt)^r` is measurable and bounded by `(aU²∫_Sρ)^r`. -/
lemma integrable_rpow_setIntegral_weight_normSq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (S : Set ℝ)
    {ρ : ℝ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : IntegrableOn ρ S) {a r : ℝ}
    (ha : 0 ≤ a) (hr0 : 0 ≤ r) :
    Integrable (fun ω => (a * ∫ t in S, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
        ^ 2) ^ r) μ := by
  haveI := hX.isProbabilityMeasure
  set U : ℝ := ∏ p ∈ Nat.primesBelow n, (1 + (p : ℝ) ^ (-(1 / 2 + σ))) with hU
  have hjoint := measurable_uncurry_weight_normSq_randomEulerProduct hX n σ hρm
  have hmeas : Measurable fun ω => ∫ t in S, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
        ^ 2 :=
    (hjoint.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)).measurable
  have hI0 : ∀ ω, 0 ≤ ∫ t in S, ρ t *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
        ^ 2 :=
    fun ω => integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  refine Integrable.mono' (integrable_const ((a * (U ^ 2 * ∫ t in S, ρ t)) ^ r))
    ((Real.continuous_rpow_const hr0).measurable.comp
      (measurable_const.mul hmeas)).aestronglyMeasurable ?_
  filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_le_rad hX n hσ] with ω hω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg ha (hI0 ω)) _)]
  exact Real.rpow_le_rpow (mul_nonneg ha (hI0 ω))
    (mul_le_mul_of_nonneg_left (setIntegral_weight_normSq_le_of_envelope hρ0 hρi hω) ha) hr0

/-! ### The fold and the cut -/

/-- **The fold and the cut, pathwise**: almost surely, for `0 ≤ a ≤ b ≤ c`,
`∫_ℝ‖F(½+σ+it)‖²|φ̂(½+σ+it)|²dt = 2(∫_{(0,a]} + ∫_{(a,b]} + ∫_{(b,c]} + ∫_{(c,∞)})ρ‖F‖²`: the
integrand is even (`RMF.ae_forall_norm_randomEulerProduct_shiftLine_neg`,
`RMF.norm_fracMellin_neg`) and integrable (`ρ` is, and `‖F‖` is bounded). -/
lemma ae_integral_fracLine_eq_fold {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∀ᵐ ω ∂μ, (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
      = 2 * ((∫ t in Set.Ioc 0 a, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
              (shiftLine σ t) ω‖ ^ 2)
          + (∫ t in Set.Ioc a b, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
              (shiftLine σ t) ω‖ ^ 2)
          + (∫ t in Set.Ioc b c, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
              (shiftLine σ t) ω‖ ^ 2)
          + ∫ t in Set.Ioi c, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
              (shiftLine σ t) ω‖ ^ 2) := by
  filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_neg hX n σ,
    ae_forall_norm_randomEulerProduct_shiftLine_le_rad hX n hσ] with ω hrefl henv
  set g : ℝ → ℝ := fun t => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖ ^ 2
    with hg
  have hpt : ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 = g t := by
    intro t
    have hs : (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I = shiftLine σ t := by
      rw [shiftLine]
      push_cast
      ring
    rw [hg]
    dsimp only
    rw [hs, mul_comm]
  simp only [hpt]
  -- evenness
  have heven : ∀ t : ℝ, g |t| = g t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, hg]
      simp only []
      rw [norm_fracMellin_neg, hrefl t]
  have hfold : (∫ t, g t) = 2 * ∫ t in Set.Ioi 0, g t := by
    have h := integral_comp_abs (f := g)
    simp only [heven] at h
    exact h
  -- integrability
  have hρm := measurable_normSq_fracMellin_line (σ := σ) (by linarith)
  have hρi := integrable_normSq_fracMellin (σ := σ) (by linarith)
  have hFm := (continuous_randomEulerProduct_sqfree_shiftLine (X := X) n σ ω).measurable
  have hgi : Integrable g := by
    have h := integrableOn_weight_normSq_of_envelope (S := Set.univ) hFm hρm
      (fun t => sq_nonneg _) hρi.integrableOn henv
    rwa [integrableOn_univ] at h
  rw [hfold, setIntegral_Ioi_eq_Ioc_add_Ioi ha hgi.integrableOn,
    setIntegral_Ioi_eq_Ioc_add_Ioi hab hgi.integrableOn,
    setIntegral_Ioi_eq_Ioc_add_Ioi hbc hgi.integrableOn]
  ring

/-- **The fold and the cut, in expectation**: for `y ≥ 2`, `σ ≥ 0` and `0 ≤ a ≤ b ≤ c`,
`E[Z_R^{1/2}] ≤ √2·∑ E[((log y)⁻¹∫_{piece}ρ‖F‖²)^{1/2}]` over the four pieces
`(0,a], (a,b], (b,c], (c,∞)`: the fold (`RMF.ae_integral_fracLine_eq_fold`) and
`(u₁+u₂+u₃+u₄)^{1/2} ≤ ∑ uᵢ^{1/2}`. -/
theorem integral_rpow_fracLine_le_four {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ : ℝ} (hσ : 0 ≤ σ) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ Real.sqrt 2 * ((∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc 0 a,
            ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
          + (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc a b,
            ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
          + (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioc b c,
            ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
          + ∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Ioi c,
            ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ) := by
  haveI := hX.isProbabilityMeasure
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hL0 : 0 ≤ (Real.log y)⁻¹ := inv_nonneg.2 hlogy.le
  have hρm := measurable_normSq_fracMellin_line (σ := σ) (by linarith)
  have hρi := integrable_normSq_fracMellin (σ := σ) (by linarith)
  have hρ0 : ∀ t : ℝ, 0 ≤ ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := fun t => sq_nonneg _
  -- the four pieces, named
  set P : Set ℝ → Ω → ℝ := fun S ω => (Real.log y)⁻¹ * ∫ t in S,
    ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (shiftLine σ t) ω‖ ^ 2 with hPdef
  have hP0 : ∀ S ω, 0 ≤ P S ω := fun S ω =>
    mul_nonneg hL0 (integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _))
  have hPi : ∀ S : Set ℝ, Integrable (fun ω => P S ω ^ (1 / 2 : ℝ)) μ := fun S =>
    integrable_rpow_setIntegral_weight_normSq hX (y + 1) hσ S hρm hρ0 hρi.integrableOn hL0
      (by norm_num)
  have hfold := ae_integral_fracLine_eq_fold hX (y + 1) hσ ha hab hbc (μ := μ)
  have hpath : ∀ᵐ ω ∂μ, ((Real.log y)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ Real.sqrt 2 * (P (Set.Ioc 0 a) ω ^ (1 / 2 : ℝ) + P (Set.Ioc a b) ω ^ (1 / 2 : ℝ)
          + P (Set.Ioc b c) ω ^ (1 / 2 : ℝ) + P (Set.Ioi c) ω ^ (1 / 2 : ℝ)) := by
    filter_upwards [hfold] with ω hω
    rw [hω]
    have heq : (Real.log y)⁻¹ * (2 * ((∫ t in Set.Ioc 0 a,
            ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2)
          + (∫ t in Set.Ioc a b, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2)
          + (∫ t in Set.Ioc b c, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2)
          + ∫ t in Set.Ioi c, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2))
        = 2 * (P (Set.Ioc 0 a) ω + P (Set.Ioc a b) ω + P (Set.Ioc b c) ω
          + P (Set.Ioi c) ω) := by
      rw [hPdef]
      ring
    have hsum0 : 0 ≤ P (Set.Ioc 0 a) ω + P (Set.Ioc a b) ω + P (Set.Ioc b c) ω
        + P (Set.Ioi c) ω := by
      have := hP0 (Set.Ioc 0 a) ω
      have := hP0 (Set.Ioc a b) ω
      have := hP0 (Set.Ioc b c) ω
      have := hP0 (Set.Ioi c) ω
      linarith
    rw [heq, Real.mul_rpow (by norm_num) hsum0,
      show (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 from (Real.sqrt_eq_rpow 2).symm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h1 := Real.rpow_add_le_add_rpow (hP0 (Set.Ioc 0 a) ω) (hP0 (Set.Ioc a b) ω)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h2 := Real.rpow_add_le_add_rpow
      (add_nonneg (hP0 (Set.Ioc 0 a) ω) (hP0 (Set.Ioc a b) ω)) (hP0 (Set.Ioc b c) ω)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h3 := Real.rpow_add_le_add_rpow
      (add_nonneg (add_nonneg (hP0 (Set.Ioc 0 a) ω) (hP0 (Set.Ioc a b) ω)) (hP0 (Set.Ioc b c) ω))
      (hP0 (Set.Ioi c) ω) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    linarith
  have hRHS : Integrable (fun ω => Real.sqrt 2 * (P (Set.Ioc 0 a) ω ^ (1 / 2 : ℝ)
      + P (Set.Ioc a b) ω ^ (1 / 2 : ℝ) + P (Set.Ioc b c) ω ^ (1 / 2 : ℝ)
      + P (Set.Ioi c) ω ^ (1 / 2 : ℝ))) μ :=
    ((((hPi _).add (hPi _)).add (hPi _)).add (hPi _)).const_mul _
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    Real.rpow_nonneg (mul_nonneg hL0 (integral_nonneg fun t => by positivity)) _) hRHS hpath)
    (le_of_eq ?_)
  have hA : Integrable (fun ω => P (Set.Ioc 0 a) ω ^ (1 / 2 : ℝ)) μ := hPi _
  have hB : Integrable (fun ω => P (Set.Ioc a b) ω ^ (1 / 2 : ℝ)) μ := hPi _
  have hC : Integrable (fun ω => P (Set.Ioc b c) ω ^ (1 / 2 : ℝ)) μ := hPi _
  have hD : Integrable (fun ω => P (Set.Ioi c) ω ^ (1 / 2 : ℝ)) μ := hPi _
  have hAB : Integrable (fun ω => P (Set.Ioc 0 a) ω ^ (1 / 2 : ℝ)
      + P (Set.Ioc a b) ω ^ (1 / 2 : ℝ)) μ := hA.add hB
  have hABC : Integrable (fun ω => P (Set.Ioc 0 a) ω ^ (1 / 2 : ℝ)
      + P (Set.Ioc a b) ω ^ (1 / 2 : ℝ) + P (Set.Ioc b c) ω ^ (1 / 2 : ℝ)) μ := hAB.add hC
  rw [integral_const_mul, integral_add hABC hD, integral_add hAB hC, integral_add hA hB]

/-! ### Jensen pieces -/

/-- **A piece by Jensen**: for `y ≥ e^{99}`, `σ ≥ 0`, a measurable `S` with
`∫_S|φ̂(½+σ+it)|²dt ≤ M`, `E[((log y)⁻¹∫_S|φ̂|²‖F_{y+1}(½+σ+it)‖²dt)^{1/2}] ≤ (1.195M)^{1/2}`:
Tonelli, the second moment `∏_{p≤y}(1 + p^{-1-2σ}) ≤ 1.195 log y` at every height. -/
theorem integral_rpow_fracPiece_le_jensen {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : Real.exp 99 ≤ (y : ℝ)) {σ : ℝ}
    (hσ : 0 ≤ σ) {S : Set ℝ} (hS : MeasurableSet S) {M : ℝ}
    (hM : ∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ M) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ (1.195 * M) ^ (1 / 2 : ℝ) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ :=
    hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hρm := measurable_normSq_fracMellin_line (σ := σ) (by linarith)
  have hρi := integrable_normSq_fracMellin (σ := σ) (by linarith)
  have hρ0 : ∀ t : ℝ, 0 ≤ ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := fun t => sq_nonneg _
  -- the second moment, the same at every height
  set Pm : ℝ := ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ))) with hPm
  have hmom : ∀ t : ℝ, (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      (y + 1) (shiftLine σ t) ω‖ ^ 2 ∂μ) = Pm := fun t => by
    rw [hRa.integral_norm_randomEulerProduct_sq' (y + 1) (shiftLine σ t), re_shiftLine]
  have hPle : Pm ≤ 1.195 * Real.log y := by
    rw [hPm]
    refine le_trans (Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_)
      (prod_one_add_inv_primesBelow_le hy)
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have : (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ ((p : ℝ))⁻¹ :=
      calc (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        _ = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
    linarith
  have hPm0 : 0 ≤ Pm := by rw [hPm]; exact Finset.prod_nonneg fun p _ => by positivity
  -- Tonelli
  have hjm := measurable_uncurry_weight_normSq_randomEulerProduct hX (y + 1) σ hρm
  have hslice : ∀ t : ℝ, (∫ ω, ‖‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2‖ ∂μ) = ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 * Pm := by
    intro t
    have h1 : (fun ω => ‖‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2‖)
        = fun ω => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2 :=
      funext fun ω => Real.norm_of_nonneg (mul_nonneg (hρ0 t) (sq_nonneg _))
    rw [h1, integral_const_mul, hmom t]
  have hProd : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) (μ.prod (volume.restrict S)) := by
    refine (integrable_prod_iff' hjm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair]
      exact (hRa.integrable_norm_randomEulerProduct_sq (y + 1) _).const_mul _
    · have h2 : (fun t : ℝ => ∫ ω, ‖Function.uncurry (fun (ω : Ω) (t : ℝ) =>
            ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2) (ω, t)‖ ∂μ)
          = fun t : ℝ => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 * Pm :=
        funext fun t => by simp only [Function.uncurry_apply_pair]; exact hslice t
      rw [h2]
      exact (hρi.mul_const Pm).integrableOn
  -- the mean
  have hZ0 : ∀ ω : Ω, 0 ≤ (Real.log y)⁻¹ * ∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2 :=
    fun ω => mul_nonneg (inv_nonneg.2 hlogy.le)
      (integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _))
  have hZi : Integrable (fun ω => (Real.log y)⁻¹ * ∫ t in S,
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) μ := by
    have h := hProd.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h
    exact h.const_mul _
  have hmean : (∫ ω, (Real.log y)⁻¹ * (∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ∂μ) ≤ 1.195 * M := by
    rw [integral_const_mul, integral_integral_swap hProd]
    have h1 : (∫ t in S, (∫ ω, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2 ∂μ))
        = ∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 * Pm :=
      setIntegral_congr_fun hS fun t _ => by rw [integral_const_mul, hmom t]
    rw [h1, integral_mul_const]
    have hI0 : 0 ≤ ∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 :=
      integral_nonneg hρ0
    have hM0 : 0 ≤ M := le_trans hI0 hM
    calc (Real.log y)⁻¹ * ((∫ t in S, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) * Pm)
        ≤ (Real.log y)⁻¹ * (M * (1.195 * Real.log y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hM hPle hPm0 hM0) (inv_nonneg.2 hlogy.le)
      _ = 1.195 * M := by field_simp
  have hZqi := integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  refine le_trans (integral_rpow_le_rpow_integral (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall hZ0) hZi hZqi) ?_
  exact Real.rpow_le_rpow (integral_nonneg fun ω => hZ0 ω) hmean (by norm_num)

/-! ### The windows -/

/-- **The mesoscopic range as a sum of windows**, the weight `ρ = |φ̂|²` inside:
`E[(∫_{(e^{-K}, e^{-k₀}]}ρ‖F_n‖²)^{1/2}] ≤ ∑_{k₀≤k<K} E[(∫_{[e^{-k}/e, e^{-k}]}ρ‖F_n‖²)^{1/2}]`
(`RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside`). -/
theorem integral_rpow_fracMeso_le_sum_windows {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (k₀ K : ℕ) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-(K : ℝ))) (Real.exp (-(k₀ : ℝ))),
        ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
          ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ ∑ k ∈ Finset.Ico k₀ K, ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
          (Real.exp (-(k : ℝ))), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
  have hk0 : ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ 1 := fun k =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg k))
  refine integral_rpow_setIntegral_weight_le_sum_windows_inside hX n hσ (by norm_num)
    (by norm_num) (Finset.Ico k₀ K) (fun k => Real.exp (-(k : ℝ)) / Real.exp 1)
    (fun k => Real.exp (-(k : ℝ))) (A := 0) (B := 1) (fun t => sq_nonneg _)
    (measurable_normSq_fracMellin_line (by linarith)) (normSq_fracMellin_line_le hσ)
    measurableSet_Ioc ?_ ?_ ?_
  · intro t ht
    exact ⟨le_trans (Real.exp_pos _).le ht.1.le, le_trans ht.2 (hk0 k₀)⟩
  · intro k _ t ht
    exact ⟨le_trans (by positivity) ht.1.le, le_trans ht.2 (hk0 k)⟩
  · intro t ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
    have hlo : -(K : ℝ) < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos _) ht.1
      rwa [Real.log_exp] at this
    have hhi : Real.log t ≤ -(k₀ : ℝ) := by
      have := Real.log_le_log ht0 ht.2
      rwa [Real.log_exp] at this
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = -Real.log t := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by
      have : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
      linarith
    have hfl1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
    have hfl2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have htu : t = Real.exp (-u) := by rw [hu, neg_neg, Real.exp_log ht0]
    refine ⟨⌊u⌋₊, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      constructor
      · exact Nat.le_floor (by linarith)
      · have h2 : (⌊u⌋₊ : ℝ) < K := by linarith
        exact_mod_cast h2
    · constructor
      · change Real.exp (-((⌊u⌋₊ : ℕ) : ℝ)) / Real.exp 1 < t
        rw [htu, ← Real.exp_sub]
        exact Real.exp_lt_exp.2 (by linarith)
      · change t ≤ Real.exp (-((⌊u⌋₊ : ℕ) : ℝ))
        rw [htu]
        exact Real.exp_le_exp.2 (by linarith)

/-- **The far range as a sum of windows**, the weight `ρ = |φ̂|²` inside:
`E[(∫_{(e^{-4}, e^{J-4}]}ρ‖F_n‖²)^{1/2}] ≤ ∑_{j<J} E[(∫_{[e^{j-3}/e, e^{j-3}]}ρ‖F_n‖²)^{1/2}]`
(`RMF.integral_rpow_setIntegral_weight_le_sum_windows_inside`). -/
theorem integral_rpow_fracFar_le_sum_windows {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (J : ℕ) :
    (∫ ω, (∫ t in Set.Ioc (Real.exp (-4)) (Real.exp ((J : ℝ) - 4)),
        ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n (shiftLine σ t) ω‖
          ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ ∑ j ∈ Finset.range J, ∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
          (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n
            (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
  refine integral_rpow_setIntegral_weight_le_sum_windows_inside hX n hσ (by norm_num)
    (by norm_num) (Finset.range J) (fun j => Real.exp ((j : ℝ) - 3) / Real.exp 1)
    (fun j => Real.exp ((j : ℝ) - 3)) (A := 0) (B := Real.exp ((J : ℝ) - 4))
    (fun t => sq_nonneg _) (measurable_normSq_fracMellin_line (by linarith))
    (normSq_fracMellin_line_le hσ) measurableSet_Ioc ?_ ?_ ?_
  · intro t ht
    exact ⟨le_trans (Real.exp_pos _).le ht.1.le, ht.2⟩
  · intro j hj t ht
    have hjn : (j : ℝ) + 1 ≤ (J : ℝ) := by
      have := Finset.mem_range.1 hj
      exact_mod_cast this
    exact ⟨le_trans (by positivity) ht.1.le, le_trans ht.2 (Real.exp_le_exp.2 (by linarith))⟩
  · intro t ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
    have hlo : -4 < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos _) ht.1
      rwa [Real.log_exp] at this
    have hhi : Real.log t ≤ (J : ℝ) - 4 := by
      have := Real.log_le_log ht0 ht.2
      rwa [Real.log_exp] at this
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log t + 4 := ⟨_, rfl⟩
    have hu0 : 0 < u := by linarith
    have hc1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.2 hu0
    have hclt : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0.le
    have hcge : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have hcn : ⌈u⌉₊ ≤ J := Nat.ceil_le.2 (by linarith)
    have hcast : ((⌈u⌉₊ - 1 : ℕ) : ℝ) = (⌈u⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hc1, Nat.cast_one]
    have htu : t = Real.exp (u - 4) := by
      rw [hu, add_sub_cancel_right, Real.exp_log ht0]
    refine ⟨⌈u⌉₊ - 1, Finset.mem_range.2 (by omega), ?_, ?_⟩
    · change Real.exp (((⌈u⌉₊ - 1 : ℕ) : ℝ) - 3) / Real.exp 1 < t
      rw [hcast, htu, ← Real.exp_sub]
      exact Real.exp_lt_exp.2 (by linarith)
    · change t ≤ Real.exp (((⌈u⌉₊ - 1 : ℕ) : ℝ) - 3)
      rw [hcast, htu]
      exact Real.exp_le_exp.2 (by linarith)

/-! ### One mesoscopic window -/

/-- **One mesoscopic window, by the sup transfer onto the chaos at `q = ½`**: on
`[e^{-k}/e, e^{-k}]`, `|φ̂|² ≤ 0.7151 ≤ 0.7151(σ² + e^{-2k})(σ²+t²)⁻¹`, and
`RMF.window_theta_le_chaos_q` at slope `3/2`, `q = ½` (where `RMF.thetaPF = 1`) bounds the
window of `(σ²+t²)⁻¹‖F‖²`:

`(log y)^{-1/2}E[(∫ρ‖F_{y+1}‖²)^{1/2}]
  ≤ (0.7151(σ² + e^{-2k})/2)^{1/2}·G_k^{1/2}·shiftMomentConst … ½·(1 + ½√n)^{-1/2}`. -/
theorem window_frac_meso (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 10)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {k y D : ℕ}
    {σ A lam : ℝ} (hσ : 0 < σ) (hk : 2 ≤ k) (hkD : k + 8 ≤ D) (hD105 : 105 ≤ D)
    (hDy : D ≤ ⌊Real.log (Real.log y)⌋₊) (hσy : σ * Real.log y ≤ E₀)
    (hNn : N ≤ harperBlockCount D y) (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax)
    (hlam : 1 ≤ lam) :
    (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
      ≤ (0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) / 2) ^ (1 / 2 : ℝ)
        * thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ)
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
            (radBlockBadConst E₀ βc * Real.exp ((D : ℝ) - k)) A
            (radAveragedShift E₀ βc Tr κ) lam δ (1 / 2)
          * (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  haveI := hX.isProbabilityMeasure
  -- the window of `(σ²+t²)⁻¹‖F‖²` by the chaos
  have hC := window_theta_le_chaos_q E₀ βc hE₀ hE₀1 hβc hβc2 hTr hκ hδ0 hδ hN hmono hX
    (θ := 3 / 2) (by norm_num) (by norm_num) (q := 1 / 2) (by norm_num) le_rfl hσ hk hkD hD105
    hDy hσy hNn hA hAmax hlam
  have hPF : thetaPF σ (3 / 2) (1 / 2) k = 1 := by
    unfold thetaPF
    norm_num
  rw [hPF, one_mul, thetaWindowConstQ_half] at hC
  -- the sup transfer, pathwise
  set ck : ℝ := 0.7151 * (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) with hck
  have hck0 : 0 ≤ ck := by positivity
  have hwc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => by positivity
  have hρc : Continuous fun t : ℝ => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 :=
    (continuous_fracMellin_line (by linarith)).norm.pow 2
  have hpt : ∀ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2)
      ≤ ck * ∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2 := by
    intro ω
    have hFc := continuous_randomEulerProduct_sqfree_shiftLine (X := X) (y + 1) σ ω
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hρc.mul (hFc.norm.pow 2)).integrableOn_Icc
      ((hwc.mul (hFc.norm.pow 2)).const_smul ck).integrableOn_Icc measurableSet_Icc
      fun t ht => ?_
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
    have hts : t ^ 2 ≤ Real.exp (-(k : ℝ)) ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
    have hpos : 0 < σ ^ 2 + t ^ 2 := by positivity
    have h1 : (1 : ℝ) ≤ (σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) * (σ ^ 2 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      linarith
    have hρ := normSq_fracMellin_line_le hσ.le t
    have hρw : ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ ck * (σ ^ 2 + t ^ 2)⁻¹ := by
      calc ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 ≤ 0.7151 * 1 := by linarith
        _ ≤ 0.7151 * ((σ ^ 2 + Real.exp (-(k : ℝ)) ^ 2) * (σ ^ 2 + t ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = ck * (σ ^ 2 + t ^ 2)⁻¹ := by rw [hck]; ring
    calc ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2
        ≤ ck * (σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2 := mul_le_mul_of_nonneg_right hρw (sq_nonneg _)
      _ = ck * ((σ ^ 2 + t ^ 2)⁻¹ *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) := by ring
  -- in expectation
  have hwi : Integrable (fun ω => (ck * ∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
      (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ)) μ :=
    integrable_rpow_setIntegral_weight_normSq hX (y + 1) hσ.le _ hwc.measurable
      (fun t => by positivity) hwc.integrableOn_Icc hck0 (by norm_num)
  have hE : (∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ ck ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _)
      ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · refine hwi.congr (Filter.Eventually.of_forall fun ω => ?_)
      exact Real.mul_rpow hck0 (integral_nonneg fun t => by positivity)
    · dsimp only
      rw [← Real.mul_rpow hck0 (integral_nonneg fun t => by positivity)]
      exact Real.rpow_le_rpow (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hpt ω) (by norm_num)
  -- the normalisation
  have hy2 : 2 ≤ y := by
    by_contra hcon
    have hy1 : y ≤ 1 := by omega
    have h0 : Real.log (Real.log y) = 0 := by
      interval_cases y <;> simp
    have hLL : ((D : ℕ) : ℝ) ≤ Real.log (Real.log y) := (Nat.le_floor_iff' (by omega)).1 hDy
    rw [h0] at hLL
    have : (0 : ℝ) < ((D : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < D)
    linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  set Ew := ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ with hEw
  have hEw0 : 0 ≤ Ew := integral_nonneg fun ω => Real.rpow_nonneg
    (integral_nonneg fun t => by positivity) _
  have hnorm : (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ck ^ (1 / 2 : ℝ)
      = (ck / 2) ^ (1 / 2 : ℝ) * (2 / Real.log y) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (inv_nonneg.2 hlogy.le) hck0,
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ
      ≤ (Real.log y)⁻¹ ^ (1 / 2 : ℝ) * (ck ^ (1 / 2 : ℝ) * Ew) :=
        mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg (inv_nonneg.2 hlogy.le) _)
    _ = (ck / 2) ^ (1 / 2 : ℝ) * ((2 / Real.log y) ^ (1 / 2 : ℝ) * Ew) := by
        rw [← mul_assoc, hnorm, mul_assoc]
    _ ≤ (ck / 2) ^ (1 / 2 : ℝ) * (thetaWindowConst (3 / 2) k y ^ (1 / 2 : ℝ)
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
            (radBlockBadConst E₀ βc * Real.exp ((D : ℝ) - k)) A
            (radAveragedShift E₀ βc Tr κ) lam δ (1 / 2)
          * (1 + (1 - 1 / 2) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [hck]; ring

/-! ### One far window -/

/-- **One far window by the weighted chaos with the weight `|φ̂|²`**: for the window
`[e^{j-4}, e^{j-3}]`, `0 < r ≤ 1`, `y ≥ e^99`, `105 + j ≤ ⌊log log y⌋`, `σ log y ≤ E₀ ≤ 1/10`
and the chaos's parameters,

`(log y)^{-r}·E[(∫_{e^{j-4}}^{e^{j-3}}|φ̂(½+σ+it)|²‖F_{y+1}(½+σ+it)‖²dt)^r]
  ≤ shiftMomentConst 1 C_i (C_b e^{2j+102}) A s λ δ r·(1.195∫_{e^{j-4}}^{e^{j-3}}|φ̂|²)^r
    ·(1 + (1-r)√n)^{-r}`,

`n = harperBlockCount (105 + j) y`: `RMF.window_far_chaos` with `ρ = |φ̂|²`
(`RMF.integral_rpow_block_weight_le_floor_of_height`), so the window's mass enters; a window
of mass `0` carries nothing. -/
theorem window_far_frac (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 10)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) {j y : ℕ} {σ A lam : ℝ} (hσ : 0 ≤ σ) (hy : Real.exp 99 ≤ (y : ℝ))
    (hDy : 105 + j ≤ ⌊Real.log (Real.log y)⌋₊) (hσy : σ * Real.log y ≤ E₀)
    (hNn : N ≤ harperBlockCount (105 + j) y) (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax)
    (hlam : 1 ≤ lam) :
    (Real.log y)⁻¹ ^ r * ∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
        (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ r ∂μ
      ≤ shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
            (radBlockBadConst E₀ βc * Real.exp (2 * (j : ℝ) + 102)) A
            (radAveragedShift E₀ βc Tr κ) lam δ r
          * (1.195 * ∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
              (Real.exp ((j : ℝ) - 3)), ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ r
          * (1 + (1 - r) * Real.sqrt (harperBlockCount (105 + j) y : ℝ)) ^ (-r) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ :=
    hX.isRademacherRMF
  have hLL : (((105 + j : ℕ) : ℕ) : ℝ) ≤ Real.log (Real.log y) :=
    (Nat.le_floor_iff' (by omega)).1 hDy
  have hy1 : (100 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hx1 : (1 : ℝ) < (y : ℝ) := by linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  set D := 105 + j with hDdef
  have hDR : (D : ℝ) = 105 + (j : ℝ) := by rw [hDdef]; push_cast; ring
  have hϑlo : (D : ℝ) - 1 ≤ harperOffset D y := sub_one_le_harperOffset D (y : ℝ)
  have hϑhi : harperOffset D y < (D : ℝ) := harperOffset_lt_natCast D (y : ℝ)
  have hϑj : 104 + (j : ℝ) ≤ harperOffset D y := by linarith
  have hϑ104 : (104 : ℝ) ≤ harperOffset D y := by linarith
  have hϑ : radFreeStartThreshold E₀ ≤ harperOffset D y :=
    le_trans (radFreeStartThreshold_le_104 hE₀ (by linarith)) hϑ104
  set T := Real.exp ((j : ℝ) - 3) with hTdef
  have hT0 : 0 < T := Real.exp_pos _
  have hhT : (2 * T + 1) * pntFloorConst (harperOffset D y) ≤ Real.exp (-(2 * E₀)) / 200 :=
    height_floor_far hE₀1 j hϑj
  have hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D y) := by
    have h1 : 2 * (T / Real.exp 1) * Real.exp (harperOffset D y)
        = 2 * Real.exp ((j : ℝ) - 4 + harperOffset D y) := by
      rw [hTdef, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, mul_assoc, ← Real.exp_add,
        ← Real.exp_add]
      congr 2
      ring
    rw [h1]
    have h2 : Real.exp 6 ≤ Real.exp ((j : ℝ) - 4 + harperOffset D y) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : (403 : ℝ) ≤ Real.exp 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
      have := Real.exp_one_gt_d9
      have h4 : (2.718 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
      linarith [show (403 : ℝ) ≤ 2.718 ^ 6 by norm_num]
    have h5 : Real.exp (2 * E₀) ≤ Real.exp (1 / 5) := Real.exp_le_exp.2 (by linarith)
    have h6 := exp_one_fifth_le
    linarith
  have hKθ : T * Real.exp (harperOffset D y) ≤ Real.exp (2 * (j : ℝ) + 102) := by
    rw [hTdef, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hzb : ((0 : ℕ) : ℝ) ≤ blockScale (harperOffset D y) 0 := by
    rw [Nat.cast_zero]
    exact (blockScale_pos _ _).le
  have hσx : |σ| * Real.log (y : ℝ) ≤ E₀ := by rw [abs_of_nonneg hσ]; exact hσy
  have hρm := measurable_normSq_fracMellin_line (σ := σ) (by linarith)
  have hρ0 : ∀ t : ℝ, 0 ≤ ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := fun t => sq_nonneg _
  have hρb := normSq_fracMellin_line_le hσ
  have hρi := integrable_normSq_fracMellin (σ := σ) (by linarith)
  set m := ∫ t in Set.Icc (T / Real.exp 1) T, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
    with hm
  have hm0 : 0 ≤ m := integral_nonneg hρ0
  set C := shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
    (radBlockBadConst E₀ βc * Real.exp (2 * (j : ℝ) + 102)) A
    (radAveragedShift E₀ βc Tr κ) lam δ r with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  set G := (1 + (1 - r) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-r) with hGdef
  have hG0 : 0 ≤ G := by
    have : 0 ≤ 1 - r := by linarith
    exact Real.rpow_nonneg (by positivity) _
  have hL0 : 0 ≤ (Real.log y)⁻¹ ^ r := Real.rpow_nonneg (inv_nonneg.2 hlogy.le) _
  rcases hm0.lt_or_eq with hmpos | hmzero
  · -- a window with mass: the weighted chaos
    have h := integral_rpow_block_weight_le_floor_of_height E₀ βc hE₀ hβc hβc2 hTr hκ hδ0 hδ
      hN hmono hX (x := (y : ℝ)) (σ := σ) (η := E₀) (T := T) (q := r) (A := A) (lam := lam)
      (Bd := 0.7151) (z := 0) (D := D)
      (ρ := fun t => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
      (Kθ := Real.exp (2 * (j : ℝ) + 102)) hρm hρ0 hρb hmpos hx1 hLL hϑ hϑ104 hσ hE₀ le_rfl
      hσx hT0 hhT hlo hKθ hzb (Nat.zero_le _) hNn hr0.le hr1 hA hAmax hlam
    simp only [Nat.floor_natCast, randomEulerProductIco_zero] at h
    have hM2 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ 0) ω‖ ^ 2 ∂μ) ≤ 1.195 * Real.log y := by
      rw [hRa.integral_norm_randomEulerProduct_sq' (y + 1) (shiftLine σ 0), re_shiftLine]
      refine le_trans (Finset.prod_le_prod (fun m _ => by positivity) fun m hm => ?_)
        (prod_one_add_inv_primesBelow_le hy)
      have hmp := Nat.prime_of_mem_primesBelow hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmp.one_lt.le
      have : (m : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ ((m : ℝ))⁻¹ :=
        calc (m : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (m : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
          _ = ((m : ℝ))⁻¹ := Real.rpow_neg_one _
      linarith
    have hM0 : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hkey : (Real.log y)⁻¹ * (m * ∫ ω, ‖randomEulerProduct
        (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂μ)
        ≤ 1.195 * m := by
      calc (Real.log y)⁻¹ * (m * ∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂μ)
          ≤ (Real.log y)⁻¹ * (m * (1.195 * Real.log y)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM2 hm0)
              (inv_nonneg.2 hlogy.le)
        _ = 1.195 * m := by field_simp
    calc (Real.log y)⁻¹ ^ r * ∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ r ∂μ
        ≤ (Real.log y)⁻¹ ^ r * (C * (m * ∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂μ)
              ^ r * G) := mul_le_mul_of_nonneg_left h hL0
      _ = C * ((Real.log y)⁻¹ * (m * ∫ ω, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (shiftLine σ 0) ω‖ ^ 2 ∂μ))
              ^ r * G := by
          rw [Real.mul_rpow (inv_nonneg.2 hlogy.le) (mul_nonneg hm0 hM0)]
          ring
      _ ≤ C * (1.195 * m) ^ r * G := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC0) hG0
          exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.2 hlogy.le) (mul_nonneg hm0 hM0))
            hkey hr0.le
  · -- a window without mass carries nothing
    have hzero : ∀ᵐ ω ∂μ, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) = 0 := by
      filter_upwards [ae_forall_norm_randomEulerProduct_shiftLine_le_rad hX (y + 1) hσ]
        with ω hω
      have hle := setIntegral_weight_normSq_le_of_envelope (S := Set.Icc (T / Real.exp 1) T)
        hρ0 hρi.integrableOn hω
      rw [← hm, ← hmzero, mul_zero] at hle
      exact le_antisymm hle (integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _))
    have hE : (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
        ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ r ∂μ) = 0 := by
      have hae : (fun ω => (∫ t in Set.Icc (T / Real.exp 1) T,
          ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 *
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ r) =ᵐ[μ] fun _ => (0 : ℝ) :=
        hzero.mono fun ω hω => by
          dsimp only
          rw [hω, Real.zero_rpow hr0.ne']
      rw [integral_congr_ae hae, integral_zero]
    rw [hE, mul_zero]
    exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _)) hG0

end RMF
