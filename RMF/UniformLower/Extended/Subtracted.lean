/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.KernelZeta
import RMF.UniformLower.Extended.Reduction
import RMF.UniformLower.SubtractedBelowHalf
import RMF.Weighted.FracWindowsExplicit.Assembly

/-!
# The extended sum's explicit lower bound: the subtracted term

The reduction for `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`
(`RMF.le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering`) subtracts
`E[J_Y(V/log x)^q]`, `J_Y(σ) = ∫_ℝ lineDivSq (½ + σ) X (⌊x⌋ + 1) ω t dt`; here it is bounded by
the weighted sum's numbers.

`F` below is the weighted sum's Euler product `F_{⌊x⌋+1}` (the squarefree extension) and
`s = ½ + σ + it`.

* **Jensen** (`RMF.integral_rpow_lineDivSq_le_jensen`): `E[J_Y(V/log x)^q] ≤ (1.195π(log x)²/V)^q`
  for `x ≥ e^{100}`, the weighted sum's `RMF.integral_rpow_lineDiv_le_jensen` verbatim: almost
  surely `J_Y = ∫_ℝ|F(s)|²K(σ, t)dt` (`RMF.ae_lineDivSq_eq_mul_zetaKernel`), and
  `∫_ℝK(σ, t)dt ≤ π/σ` (`RMF.integral_zetaKernel_le`) is the weighted sum's `∫_ℝdt/(σ² + t²)`.
* **Below `½`** (`RMF.integral_rpow_lineDivSq_le_subtracted_belowHalf`): for
  `Λ = log log x ≥ 6000`, `V ≥ 8` and `0 < q < ½`,
  `E[J_Y(V/log x)^q] ≤ 400(log x)^q·min{Λ, (1-2q)⁻¹}·Λ^{-q/2}`.  The kernel's decomposition gives
  `J_Y ≤ 2.01(J_S + J_R)` (`RMF.ae_integral_lineDivSq_le_decomp`),
  `J_S = ∫_ℝ|F(s)/(σ+it)|²dt` the weighted sum's (its constant: `216`) and
  `J_R = ∫_ℝ|F(s)|²|φ̂(s)|²dt` the fractional-part kernel's:
  `E[J_R^q] ≤ 55.03(log x)^qΛ^{-q/2}` (`RMF.integral_rpow_fracLine_le_subtracted`), by the shift
  down to `σ = 1/log x`, the high primes integrated out down to `fracY x`, Lyapunov from `½` and
  the window bound (`RMF.integral_rpow_fracLine_le_explicit`) for `Λ ≥ 160000`, by Jensen below.
  So `K_Y ≤ 1.42(216 + 55.03) ≤ 384.9 ≤ 400` (`2.01^q ≤ 2.01^{1/2} ≤ 1.42`).
* `cJ(q) ≤ 1/6` for `0 ≤ q ≤ ½` (`RMF.cJ_le_one_sixth`), so `400cJ(q) ≤ 216`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Fubini against a weight -/

/-- **Fubini against a weight.**  If `F(ω, t)` is jointly measurable and bounded by `U` almost
surely uniformly in `t`, `E|F(·, t)|² ≤ M` at every height and `ρ ≥ 0` is measurable and
integrable, then `E∫_ℝ|F(·, t)|²ρ(t)dt ≤ (∫_ℝρ)·M`: `RMF.setIntegral_integral_lineDiv_le` with a
general weight. -/
lemma integral_integral_normSq_mul_le {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ → ℂ}
    {ρ : ℝ → ℝ} {U M : ℝ} (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ)
    (hF : Measurable (Function.uncurry F)) (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U)
    (hM : ∀ t, ∫ ω, ‖F ω t‖ ^ 2 ∂μ ≤ M) :
    ∫ ω, (∫ t : ℝ, ‖F ω t‖ ^ 2 * ρ t) ∂μ ≤ (∫ t : ℝ, ρ t) * M := by
  have hmeas : Measurable (Function.uncurry fun ω t => ‖F ω t‖ ^ 2 * ρ t) :=
    (hF.norm.pow_const 2).mul (hρm.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun ω t => ‖F ω t‖ ^ 2 * ρ t) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const (U ^ 2)).mul_prod hρi)
      hmeas.aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := volume)).ae hU] with z hz
    change ‖‖F z.1 z.2‖ ^ 2 * ρ z.2‖ ≤ U ^ 2 * ρ z.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρ0 _))]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hz z.2) 2) (hρ0 _)
  rw [integral_integral_swap hint]
  calc (∫ t : ℝ, ∫ ω, ‖F ω t‖ ^ 2 * ρ t ∂μ)
      = ∫ t : ℝ, (∫ ω, ‖F ω t‖ ^ 2 ∂μ) * ρ t :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => integral_mul_const _ _)
    _ ≤ ∫ t : ℝ, M * ρ t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => ?_)
          (hρi.const_mul M) (Filter.Eventually.of_forall fun t => ?_)
        · exact mul_nonneg (integral_nonneg fun ω => sq_nonneg _) (hρ0 t)
        · exact mul_le_mul_of_nonneg_right (hM t) (hρ0 t)
    _ = (∫ t : ℝ, ρ t) * M := by
        rw [integral_const_mul]
        ring

/-! ### The subtracted term by Jensen -/

/-- **The subtracted term by Jensen**: for a Rademacher family, `x ≥ e^{100}`, `V > 0` and
`0 ≤ q ≤ 1`, `E[J_Y(V/log x)^q] ≤ (1.195π(log x)²/V)^q`, the weighted sum's
`RMF.integral_rpow_lineDiv_le_jensen` verbatim.  Jensen, then almost surely
`J_Y = ∫_ℝ|F(s)|²K(σ, t)dt` (`RMF.ae_lineDivSq_eq_mul_zetaKernel`) and Fubini:
`E|F(s)|² = ∏_{p≤x}(1 + p^{-1-2σ}) ≤ 1.195 log x` (`RMF.prod_one_add_inv_primesBelow_le`) and
`∫_ℝK(σ, t)dt ≤ π/σ` (`RMF.integral_zetaKernel_le`). -/
theorem integral_rpow_lineDivSq_le_jensen {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : Real.exp 100 ≤ x) (hV : 0 < V)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
      ≤ (1.195 * Real.pi * Real.log x ^ 2 / V) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL0 : 0 < Real.log x := by linarith
  -- `⌊x⌋ ≥ e^{99}`
  have hfl : Real.exp 99 ≤ (⌊x⌋₊ : ℝ) := by
    have h1 : Real.exp 100 = Real.exp 99 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : (1 : ℝ) ≤ Real.exp 99 := Real.one_le_exp (by norm_num)
    have h4 := Nat.lt_floor_add_one x
    have h5 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 99).le
    linarith
  set σ := V / Real.log x with hσdef
  have hσ : 0 < σ := div_pos hV hL0
  have hσh : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  -- the height-independent second moment, bounded by Mertens
  have hprod : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
      ≤ 1.195 * Real.log x := by
    have h1 : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
        ≤ ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ)⁻¹) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -2 * (1 / 2 + σ) ≤ -1)
      rw [Real.rpow_neg_one] at h
      linarith
    have h2 := prod_one_add_inv_primesBelow_le hfl
    have h3 : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by linarith [Real.exp_pos 99]) (Nat.floor_le hx0.le)
    linarith
  -- Jensen
  have hJ0 : ∀ ω, 0 ≤ ∫ t : ℝ, lineDivSq (1 / 2 + σ) X (⌊x⌋₊ + 1) ω t := fun ω =>
    integral_nonneg fun t => by unfold lineDivSq; positivity
  have hJ1 := integrable_lineDivSq_rpow_extended hX (⌊x⌋₊ + 1) (q := 1) hσh zero_le_one
  simp only [Real.rpow_one] at hJ1
  refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
    (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hJ0 ω)) hJ1
    (integrable_lineDivSq_rpow_extended hX (⌊x⌋₊ + 1) hσh hq0)) ?_
  refine Real.rpow_le_rpow (integral_nonneg hJ0) ?_ hq0
  -- the mean, through the kernel
  have hK : (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + σ) X (⌊x⌋₊ + 1) ω t) ∂μ)
      = ∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2 * zetaKernel (⌊x⌋₊ + 1) σ t) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_lineDivSq_eq_mul_zetaKernel hX (⌊x⌋₊ + 1)] with ω hω
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => hω σ (by linarith) t)
  rw [hK]
  have henv := ae_forall_norm_randomEulerProduct_mem_Icc hX (⌊x⌋₊ + 1) hσh
  have hmean := integral_integral_normSq_mul_le (μ := μ)
    (F := fun ω t => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      (⌊x⌋₊ + 1) (shiftLine σ t) ω)
    (ρ := zetaKernel (⌊x⌋₊ + 1) σ)
    (U := ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ))))
    (M := 1.195 * Real.log x)
    (continuous_zetaKernel _ (by linarith)).measurable (zetaKernel_nonneg _ σ)
    (integrable_zetaKernel _ (by linarith))
    (measurable_randomEulerProduct_sqfree_uncurry (X := X) hX.measurable (1 / 2 + σ)
      (⌊x⌋₊ + 1))
    (by
      filter_upwards [henv] with ω hω
      exact fun t => (hω _ (re_shiftLine σ t)).2)
    (fun t => by
      rw [hX.isRademacherRMF.integral_norm_randomEulerProduct_sq', re_shiftLine]
      exact hprod)
  have hZ := integral_zetaKernel_le (⌊x⌋₊ + 1) hσ
  calc _ ≤ _ := hmean
    _ ≤ Real.pi / σ * (1.195 * Real.log x) :=
        mul_le_mul_of_nonneg_right hZ (by positivity)
    _ = 1.195 * Real.pi * Real.log x ^ 2 / V := by
        rw [hσdef]
        field_simp

/-! ### The fractional-part kernel's line integral `J_R` -/

/-- **`∫_ℝ|φ̂|² > 0`** on every line `Re s = ½ + σ`, `σ > -½`: it is `4π∫₁^∞{w}²w^{-3-4σ}dw`
(`RMF.integral_normSq_fracMellin_eq`), whose integrand is positive on `(1, 2)`. -/
lemma integral_normSq_fracMellin_pos {σ : ℝ} (hσ : -1 / 2 < σ) :
    0 < ∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
  rw [integral_normSq_fracMellin_eq hσ]
  refine mul_pos (by positivity) ?_
  have hint : IntegrableOn (fun w : ℝ => Int.fract w ^ 2 * w ^ (-3 - 4 * σ)) (Set.Ioi 1) :=
    integrableOn_fract_pow_mul_rpow 2 (by linarith) one_pos
  have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Set.Ioi 1 := Set.Ioc_subset_Ioi_self
  have hpos : 0 < ∫ w in (1 : ℝ)..2, Int.fract w ^ 2 * w ^ (-3 - 4 * σ) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 (hint.mono_set hsub))
      (fun w hw => ?_) (by norm_num)
    have hf : Int.fract w = w - 1 := by
      have h := fract_eq_sub_natCast (n := 1) (x := w) (by push_cast; linarith [hw.1])
        (by push_cast; linarith [hw.2])
      rw [h, Nat.cast_one]
    rw [hf]
    exact mul_pos (pow_pos (by linarith [hw.1]) 2) (Real.rpow_pos_of_pos (by linarith [hw.1]) _)
  rw [intervalIntegral.integral_of_le (by norm_num)] at hpos
  refine lt_of_lt_of_le hpos (setIntegral_mono_set hint ?_
    (Filter.Eventually.of_forall fun w hw => hsub hw))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans one_pos hw).le _)

omit [MeasurableSpace Ω] in
/-- **`J_R` decreases in the shift**: for `-½ < σ₁ ≤ σ₂`,
`∫_ℝ|F_{N+1}(½+σ₂+it)|²|φ̂(½+σ₂+it)|²dt ≤ ∫_ℝ|F_{N+1}(½+σ₁+it)|²|φ̂(½+σ₁+it)|²dt`.  By Parseval
(`RMF.integral_normSq_smoothFracSum_eq_line`) the line integral is `2π∫₀^∞|H_N(u)|²u^{-1-2σ}du`,
and `H_N` vanishes below `1`: the argument of `RMF.integral_lineDiv_le_of_le`. -/
lemma integral_fracLine_le_of_le {X : ℕ → Ω → ℂ} (N : ℕ) {σ₁ σ₂ : ℝ} (hσ₁ : -1 / 2 < σ₁)
    (hσ : σ₁ ≤ σ₂) (ω : Ω) :
    (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ₂ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ₂ + t * Complex.I)‖ ^ 2)
      ≤ ∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ₁ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ₁ + t * Complex.I)‖ ^ 2 := by
  have hσ₂ : -1 / 2 < σ₂ := lt_of_lt_of_le hσ₁ hσ
  have h₁ := integral_normSq_smoothFracSum_eq_line (X := X) N hσ₁ ω
  have h₂ := integral_normSq_smoothFracSum_eq_line (X := X) N hσ₂ ω
  have hmono : (∫ u in Set.Ioi (0 : ℝ),
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) N u ω‖ ^ 2
          / u ^ (1 + 2 * σ₂))
      ≤ ∫ u in Set.Ioi (0 : ℝ),
        ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) N u ω‖ ^ 2
          / u ^ (1 + 2 * σ₁) := by
    refine setIntegral_mono_on (integrableOn_normSq_smoothFracSum (X := X) N hσ₂ ω)
      (integrableOn_normSq_smoothFracSum (X := X) N hσ₁ ω) measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rcases lt_or_ge u 1 with h | h
    · simp [smoothFracSum_eq_zero_of_lt_one _ N h ω]
    · exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hu0 _)
        (Real.rpow_le_rpow_of_exponent_le h (by linarith))
  rw [h₁, h₂] at hmono
  have hpi : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  exact le_of_mul_le_mul_left hmono hpi

/-- **`J_R^q` is integrable**, for `y ≥ 2`, `σ ≥ 0` and `q ≥ 0`: `RMF.integrable_rpow_fracEulerLine`
times `(log y)^q`. -/
lemma integrable_rpow_fracLine_of_two_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {σ : ℝ}
    (hσ : 0 ≤ σ) {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q) μ := by
  have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have key : ∀ J : ℝ, 0 ≤ J → Real.log y ^ q * ((Real.log y)⁻¹ * J) ^ q = J ^ q :=
    fun J hJ => by
      rw [Real.mul_rpow (inv_nonneg.2 hlog.le) hJ, Real.inv_rpow hlog.le,
        mul_inv_cancel_left₀ (Real.rpow_pos_of_pos hlog q).ne']
  exact ((integrable_rpow_fracEulerLine hX y hσ hq0).const_mul (Real.log y ^ q)).congr
    (Filter.Eventually.of_forall fun ω => key _ (integral_nonneg fun t => by positivity))

/-- **`E[J_R^q]` decreases in the shift**, for `N ≥ 2`, `0 ≤ σ₁ ≤ σ₂` and `q ≥ 0`
(`RMF.integral_fracLine_le_of_le`). -/
lemma integral_rpow_fracLine_le_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {N : ℕ} (hN : 2 ≤ N)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 ≤ σ₁) (hσ : σ₁ ≤ σ₂) {q : ℝ} (hq0 : 0 ≤ q) :
    (∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ₂ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ₂ + t * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          (N + 1) ((1 / 2 : ℂ) + (σ₁ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ₁ + t * Complex.I)‖ ^ 2) ^ q ∂μ :=
  integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ =>
      Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)
    (integrable_rpow_fracLine_of_two_le hX hN hσ₁ hq0)
    (Filter.Eventually.of_forall fun ω =>
      Real.rpow_le_rpow (integral_nonneg fun _ => by positivity)
        (integral_fracLine_le_of_le N (by linarith) hσ ω) hq0)

set_option maxHeartbeats 1000000 in
-- the envelopes and the independence at each height
/-- **The high primes integrated out against `|φ̂|²`**: for a Rademacher family, `2 ≤ y ≤ N`,
`σ > 0` and `0 ≤ q ≤ 1`, with `s_t = RMF.shiftLine σ t`,
`E[(∫_ℝ|φ̂(½+σ+it)|²|F_{N+1}(s_t)|²dt)^q] ≤ mBand(y, N)^q·E[(∫_ℝ|φ̂(½+σ+it)|²|F_{y+1}(s_t)|²dt)^q]`:
`RMF.integral_rpow_weight_le_mBand_rpow_mul` with the weight `|φ̂(½+σ+it)|²` for `(σ² + t²)⁻¹`
(`RMF.integral_rpow_integral_mul_le_of_indep` is generic in the weight). -/
theorem integral_rpow_fracWeight_le_mBand_rpow_mul {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N) {σ q : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ mBand y N ^ q * ∫ ω, (∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hρm : Measurable fun t : ℝ => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 :=
    ((continuous_fracMellin_line (by linarith)).norm.pow 2).measurable
  -- the split at `y + 1`
  have hsplit : ∀ ω t, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
      (shiftLine σ t) ω‖ ^ 2
      = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (N + 1)
          (shiftLine σ t) ω‖ ^ 2 := fun ω t =>
    normSq_randomEulerProduct_split (by omega) _ ω
  simp only [hsplit]
  -- measurability
  have hPm : Measurable fun z : Ω × ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
        (shiftLine σ z.2) z.1‖ ^ 2 := by
    have h := measurable_uncurry_primePoly hX (Nat.primesBelow (y + 1))
      (fun p hp => Nat.prime_of_mem_primesBelow hp) σ
    simp only [primePoly_primesBelow] at h
    exact h.norm.pow_const 2
  have hQm : Measurable fun z : Ω × ℝ =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (N + 1)
        (shiftLine σ z.2) z.1‖ ^ 2 := by
    have h := measurable_uncurry_primePoly hX (primesIco (y + 1) (N + 1))
      (fun p hp => prime_of_mem_primesIco hp) σ
    simp only [primePoly_primesIco] at h
    exact h.norm.pow_const 2
  -- the envelopes
  have henvP := ae_forall_norm_randomEulerProduct_mem_Icc hX (y + 1) (c := 1 / 2 + σ)
    (by linarith)
  have henvQ := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX (y + 1) (N + 1) hc0
  have hLP : 0 < ∏ p ∈ Nat.primesBelow (y + 1), (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_pos (by linarith)
  have hLQ : 0 < ∏ p ∈ primesIco (y + 1) (N + 1), (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  -- `mBand` is positive
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_trans hy hyN)
  have hm0 : 0 < mBand y N := by
    unfold mBand
    have h1 : 0 < Real.log y := Real.log_pos (by linarith)
    have h2 : 0 < Real.log N := Real.log_pos (by linarith)
    positivity
  refine integral_rpow_integral_mul_le_of_indep
    (ρ := fun t => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
    (f := fun ω t => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (shiftLine σ t) ω‖ ^ 2)
    (g := fun ω t => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (y + 1) (N + 1) (shiftLine σ t) ω‖ ^ 2)
    (lf := (∏ p ∈ Nat.primesBelow (y + 1), (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    (uf := (∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    (lg := (∏ p ∈ primesIco (y + 1) (N + 1), (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    (ug := (∏ p ∈ primesIco (y + 1) (N + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    hq0 hq1 hρm (fun t => sq_nonneg _) (integrable_normSq_fracMellin (by linarith))
    (integral_normSq_fracMellin_pos (by linarith)) hPm hQm
    (fun ω t => sq_nonneg _) (fun ω t => sq_nonneg _) (pow_pos hLP 2) (pow_pos hLQ 2) ?_ ?_ hm0
    ?_ ?_
  · filter_upwards [henvP] with ω hω
    intro t
    have h := hω (shiftLine σ t) (re_shiftLine σ t)
    exact ⟨pow_le_pow_left₀ hLP.le h.1 2, pow_le_pow_left₀ (norm_nonneg _) h.2 2⟩
  · filter_upwards [henvQ] with ω hω
    intro t
    have h := hω (shiftLine σ t) (re_shiftLine σ t)
    exact ⟨pow_le_pow_left₀ hLQ.le h.1 2, pow_le_pow_left₀ (norm_nonneg _) h.2 2⟩
  · -- the two blocks are independent, at every height
    intro t
    have hS : ∀ p ∈ Nat.primesBelow (y + 1), 0 < p := fun p hp =>
      (Nat.prime_of_mem_primesBelow hp).pos
    have hφ : Measurable fun v : ↥(Nat.primesBelow (y + 1)) → ℂ =>
        (primePolyWindowWeight (Nat.primesBelow (y + 1)) σ Set.univ
            (fun u => ‖fracMellin (1 / 2 + σ + u * Complex.I)‖ ^ 2) v) ^ (q - 1)
          * ‖primePoly (Nat.primesBelow (y + 1)) (shiftLine σ t) v‖ ^ 2 :=
      ((measurable_primePolyWindowWeight hS σ Set.univ hρm).pow_const _).mul
        ((continuous_primePoly _ _).norm.pow 2).measurable
    have hψ : Measurable fun v : ↥(primesIco (y + 1) (N + 1)) → ℂ =>
        ‖primePoly (primesIco (y + 1) (N + 1)) (shiftLine σ t) v‖ ^ 2 :=
      ((continuous_primePoly _ _).norm.pow 2).measurable
    have h := hX.integral_mul_split (y + 1) (N + 1) hφ hψ
      (hφ.comp (measurable_primeTuple hX _ fun p hp =>
        Nat.prime_of_mem_primesBelow hp)).aestronglyMeasurable
      (hψ.comp (measurable_primeTuple hX _ fun p hp =>
        prime_of_mem_primesIco hp)).aestronglyMeasurable
    simpa only [primePolyWindowWeight, primePoly_primesBelow, primePoly_primesIco,
      Measure.restrict_univ] using h
  · -- the upper block's second moment, by Mertens
    intro t
    have h := integral_normSq_line_le_mBand hX hy hyN hσ.le t
    simp only [shiftLine_eq_half_add]
    exact h

/-- **The high primes integrated out of `J_R`**: for a Rademacher family, `2 ≤ y ≤ N`, `σ > 0` and
`0 ≤ q ≤ 1`, `E[J_{R,N}(σ)^q] ≤ mBand(y, N)^q·E[J_{R,y}(σ)^q]`,
`J_{R,M}(σ) = ∫_ℝ|F_{M+1}(½+σ+it)|²|φ̂(½+σ+it)|²dt`
(`RMF.integral_rpow_fracWeight_le_mBand_rpow_mul`). -/
theorem integral_rpow_fracLine_le_mBand_rpow_mul {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N) {σ q : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ mBand y N ^ q * ∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q ∂μ := by
  have hw : ∀ (M : ℕ) (ω : Ω), (∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) M
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) M
          (shiftLine σ t) ω‖ ^ 2 := fun M ω =>
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [shiftLine_eq_half_add]
      ring)
  simp only [hw]
  exact integral_rpow_fracWeight_le_mBand_rpow_mul hX hy hyN hσ hq0 hq1

/-! ### `J_R` for `Λ ≥ 160000`: down to the window bound -/

/-- `fracY x ≤ ⌊x⌋` for `x ≥ exp(e^{20})`: `log(fracY x) ≤ log x/U ≤ log x` (`RMF.fracY_facts`). -/
lemma fracY_le_floor {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) : fracY x ≤ ⌊x⌋₊ := by
  obtain ⟨hx0, -, hL, hΛ, -⟩ := log_facts_of_exp_exp_twenty_le hx
  obtain ⟨hy2, -, hyL⟩ := fracY_facts hx
  have hU : fracU x = 16 * Real.log (Real.log x) + 85 := rfl
  have hU1 : 1 ≤ fracU x := by rw [hU]; linarith
  have hy0 : (0 : ℝ) < (fracY x : ℝ) := by exact_mod_cast (by omega : 0 < fracY x)
  have h1 : Real.log x / fracU x ≤ Real.log x := div_le_self (by linarith) hU1
  have h2 : Real.log (fracY x) ≤ Real.log x := le_trans hyL h1
  exact Nat.le_floor ((Real.log_le_log_iff hy0 hx0).1 h2)

/-- **The band's Mertens factor at `fracY`**: `mBand(fracY x, ⌊x⌋)·log(fracY x) ≤ e^{1/1000}log x`
for `x ≥ exp(e^{20})`: it is `log⌊x⌋·e^{9.0028(1/log y + 1/log⌊x⌋)}` with `log y ≥ 10⁶`
(`RMF.mBand_halfY_floor_mul_log_le` at `fracY`). -/
lemma mBand_fracY_floor_mul_log_le {x : ℝ} (hx : Real.exp (Real.exp 20) ≤ x) :
    mBand (fracY x) ⌊x⌋₊ * Real.log (fracY x) ≤ Real.exp (1 / 1000) * Real.log x := by
  obtain ⟨hx0, -, -, -, -⟩ := log_facts_of_exp_exp_twenty_le hx
  obtain ⟨hy2, hly, -⟩ := fracY_facts hx
  have hyN := fracY_le_floor hx
  have hlogy : 0 < Real.log (fracY x) := by linarith
  have hy0 : (0 : ℝ) < (fracY x : ℝ) := by exact_mod_cast (by omega : 0 < fracY x)
  have hNy : (fracY x : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hyN
  have hlogN : Real.log (fracY x) ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_le_log hy0 hNy
  have hlogNx : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (lt_of_lt_of_le hy0 hNy) (Nat.floor_le hx0.le)
  have hexp : 9.0028 / Real.log (fracY x) + 9.0028 / Real.log (⌊x⌋₊ : ℝ) ≤ 1 / 1000 := by
    have h1 : 9.0028 / Real.log (fracY x) ≤ 9.0028 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
    have h2 : 9.0028 / Real.log (⌊x⌋₊ : ℝ) ≤ 9.0028 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_trans hly hlogN)
    linarith
  unfold mBand
  calc Real.log (⌊x⌋₊ : ℝ) / Real.log (fracY x)
        * Real.exp (9.0028 / Real.log (fracY x) + 9.0028 / Real.log (⌊x⌋₊ : ℝ))
        * Real.log (fracY x)
      = Real.log (⌊x⌋₊ : ℝ)
        * Real.exp (9.0028 / Real.log (fracY x) + 9.0028 / Real.log (⌊x⌋₊ : ℝ)) := by
        field_simp
    _ ≤ Real.log x * Real.exp (1 / 1000) :=
        mul_le_mul hlogNx (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le (by linarith)
    _ = Real.exp (1 / 1000) * Real.log x := by ring

set_option maxHeartbeats 1000000 in
-- five reductions of `J_R`
/-- **`J_R` for `Λ ≥ 160000`**: for a Rademacher family, `x > 1` with `Λ = log log x ≥ 160000`,
`V ≥ 1` and `0 < q ≤ ½`, `E[J_R(V/log x)^q] ≤ e^{q/1000}(log x)^q·55^{2q}Λ^{-q/2}`: the shift down
to `σ = 1/log x` (`RMF.integral_rpow_fracLine_le_of_le`), the high primes integrated out down to
`y = fracY x` (`RMF.integral_rpow_fracLine_le_mBand_rpow_mul`, `RMF.mBand_fracY_floor_mul_log_le`),
`Z_R = (log y)⁻¹J_{R,y}`, Lyapunov from `½` and the window bound at `c = 1`
(`RMF.integral_rpow_fracLine_le_explicit`: `E[Z_R^{1/2}] ≤ 55Λ^{-1/4}`). -/
theorem integral_rpow_fracLine_le_large {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : 1 < x)
    (hΛ : 160000 ≤ Real.log (Real.log x)) (hV : 1 ≤ V) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + ((V / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ Real.exp (q / 1000) * Real.log x ^ q
        * (55 ^ (2 * q) * Real.log (Real.log x) ^ (-(q / 2))) := by
  haveI := hX.isProbabilityMeasure
  have hxe := exp_exp_le_of_one_lt hx (by linarith)
  have hx20 : Real.exp (Real.exp 20) ≤ x :=
    le_trans (Real.exp_le_exp.2 (Real.exp_le_exp.2 (by norm_num))) hxe
  have hx3 : (3 : ℝ) ≤ x := by
    have h1 := Real.add_one_le_exp (Real.exp 110)
    have h2 := Real.add_one_le_exp (110 : ℝ)
    linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  obtain ⟨hy2, hly, -⟩ := fracY_facts hx20
  have hyN := fracY_le_floor hx20
  have hN2 : 2 ≤ ⌊x⌋₊ := le_trans hy2 hyN
  have hlogy : 0 < Real.log (fracY x) := by linarith
  have hσ' : (0 : ℝ) < 1 / Real.log x := by positivity
  have hσ'V : 1 / Real.log x ≤ V / Real.log x := div_le_div_of_nonneg_right hV hLpos.le
  -- the shift down to `1/log x`
  have h1 := integral_rpow_fracLine_le_of_le hX (N := ⌊x⌋₊) hN2 hσ'.le hσ'V hq0.le
  -- the high primes integrated out
  have h2 := integral_rpow_fracLine_le_mBand_rpow_mul hX hy2 hyN hσ' hq0.le (by linarith)
  -- the normalisation `Z_R = (log y)⁻¹J_R`
  have h3 := integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
    (J := fun ω => ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
    hlogy le_rfl hq0.le (fun ω => integral_nonneg fun t => by positivity)
  -- Lyapunov from `½`
  have h4 := integral_rpow_le_rpow_integral_rpow (μ := μ)
    (g := fun ω => (Real.log (fracY x))⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
    (r := 1 / 2) hq0 hq
    (fun ω => mul_nonneg (inv_nonneg.2 hlogy.le) (integral_nonneg fun t => by positivity))
    (integrable_rpow_fracEulerLine hX _ hσ'.le (by norm_num))
    (integrable_rpow_fracEulerLine hX _ hσ'.le hq0.le)
  -- the window bound at `c = 1`
  have h5 := integral_rpow_fracLine_le_explicit hX hx3 hΛ (c := 1) one_pos le_rfl
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛp : 0 < Λ := by linarith
  have hZ : (∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 55 ^ (2 * q) * Λ ^ (-(q / 2)) := by
    refine le_trans h4 (le_trans (Real.rpow_le_rpow (by
      exact integral_nonneg fun ω => Real.rpow_nonneg (mul_nonneg (inv_nonneg.2 hlogy.le)
        (integral_nonneg fun t => by positivity)) _) h5 (by positivity)) (le_of_eq ?_))
    rw [show q / (1 / 2) = 2 * q by ring,
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hΛp.le _), ← Real.rpow_mul hΛp.le]
    congr 2
    ring
  -- the Mertens factor
  have hm0 : 0 ≤ mBand (fracY x) ⌊x⌋₊ := by
    unfold mBand
    have hN0 : 0 ≤ Real.log (⌊x⌋₊ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hN2 : 1 ≤ ⌊x⌋₊))
    positivity
  have hmq : mBand (fracY x) ⌊x⌋₊ ^ q * Real.log (fracY x) ^ q
      ≤ Real.exp (q / 1000) * Real.log x ^ q := by
    rw [← Real.mul_rpow hm0 hlogy.le]
    calc (mBand (fracY x) ⌊x⌋₊ * Real.log (fracY x)) ^ q
        ≤ (Real.exp (1 / 1000) * Real.log x) ^ q :=
          Real.rpow_le_rpow (mul_nonneg hm0 hlogy.le) (mBand_fracY_floor_mul_log_le hx20) hq0.le
      _ = Real.exp (q / 1000) * Real.log x ^ q := by
          rw [Real.mul_rpow (Real.exp_pos _).le hLpos.le, ← Real.exp_mul]
          congr 2
          ring
  have hZ0 : 0 ≤ ∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 hlogy.le) (integral_nonneg fun t => by positivity)) _
  have hmq0 : 0 ≤ mBand (fracY x) ⌊x⌋₊ ^ q := Real.rpow_nonneg hm0 _
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ mBand (fracY x) ⌊x⌋₊ ^ q * (Real.log (fracY x) ^ q
          * ∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
                ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
                ^ q ∂μ) :=
        mul_le_mul_of_nonneg_left h3 hmq0
    _ = mBand (fracY x) ⌊x⌋₊ ^ q * Real.log (fracY x) ^ q
          * ∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
                ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
                ^ q ∂μ := by ring
    _ ≤ Real.exp (q / 1000) * Real.log x ^ q
          * ∫ ω, ((Real.log (fracY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (fracY x + 1)
                ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + ((1 / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2)
                ^ q ∂μ :=
        mul_le_mul_of_nonneg_right hmq hZ0
    _ ≤ Real.exp (q / 1000) * Real.log x ^ q * (55 ^ (2 * q) * Λ ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left hZ (by positivity)

/-! ### `J_R` by Jensen, and for every `Λ ≥ 6000` -/

/-- **`J_R` by Jensen**: for a Rademacher family, `x ≥ e^{100}`, `σ ≥ 0` and `0 ≤ q ≤ 1`,
`E[J_R(σ)^q] ≤ (1.261·1.195 log x)^q`: Jensen, Fubini against `|φ̂|²`
(`RMF.integral_integral_normSq_mul_le`), `E|F(s)|² ≤ 1.195 log x` and `∫_ℝ|φ̂|² ≤ 1.261`
(`RMF.integral_normSq_fracMellin_le_numeral`). -/
theorem integral_rpow_fracLine_le_jensen {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x σ q : ℝ} (hx : Real.exp 100 ≤ x) (hσ : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (1.261 * (1.195 * Real.log x)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  -- `⌊x⌋ ≥ e^{99}`
  have hfl : Real.exp 99 ≤ (⌊x⌋₊ : ℝ) := by
    have h1 : Real.exp 100 = Real.exp 99 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : (1 : ℝ) ≤ Real.exp 99 := Real.one_le_exp (by norm_num)
    have h4 := Nat.lt_floor_add_one x
    have h5 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 99).le
    linarith
  have hy2 : 2 ≤ ⌊x⌋₊ := by
    have : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) :=
      le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hfl
    exact_mod_cast this
  have hc : ∀ t : ℝ, (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ :=
    fun t => by rw [← hc]; simp
  -- the height-independent second moment, bounded by Mertens
  have hprod : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
      ≤ 1.195 * Real.log x := by
    have h1 : ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ)))
        ≤ ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ)⁻¹) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -2 * (1 / 2 + σ) ≤ -1)
      rw [Real.rpow_neg_one] at h
      linarith
    have h2 := prod_one_add_inv_primesBelow_le hfl
    have h3 : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by linarith [Real.exp_pos 99]) (Nat.floor_le hx0.le)
    linarith
  have hmeas := measurable_randomEulerProduct_sqfree_uncurry (X := X) hX.measurable
    (1 / 2 + σ) (⌊x⌋₊ + 1)
  simp only [hc] at hmeas
  have henv := ae_forall_norm_randomEulerProduct_mem_Icc hX (⌊x⌋₊ + 1) (c := 1 / 2 + σ)
    (by linarith)
  -- Jensen
  have hJ0 : ∀ ω, 0 ≤ ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := fun ω =>
    integral_nonneg fun t => by positivity
  have hJ1 := integrable_rpow_fracLine_of_two_le hX hy2 hσ (q := 1) zero_le_one
  simp only [Real.rpow_one] at hJ1
  refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
    (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hJ0 ω)) hJ1
    (integrable_rpow_fracLine_of_two_le hX hy2 hσ hq0)) ?_
  refine Real.rpow_le_rpow (integral_nonneg hJ0) ?_ hq0
  -- the mean
  have hmean := integral_integral_normSq_mul_le (μ := μ)
    (F := fun ω t => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      (⌊x⌋₊ + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
    (ρ := fun t => ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)
    (U := ∏ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ))))
    (M := 1.195 * Real.log x)
    ((continuous_fracMellin_line (by linarith)).norm.pow 2).measurable (fun t => sq_nonneg _)
    (integrable_normSq_fracMellin (by linarith)) hmeas
    (by
      filter_upwards [henv] with ω hω
      exact fun t => (hω _ (hre t)).2)
    (fun t => by
      rw [hX.isRademacherRMF.integral_norm_randomEulerProduct_sq', hre t]
      exact hprod)
  have hφ := integral_normSq_fracMellin_le_numeral hσ
  calc _ ≤ _ := hmean
    _ ≤ 1.261 * (1.195 * Real.log x) := mul_le_mul_of_nonneg_right hφ (by positivity)

/-- `(1.261·1.195)^qΛ^{q/2} ≤ 24.6` for `q ≤ ½` and `1 ≤ Λ ≤ 160000`: the exponent is
`q(log(1.261·1.195) + (1/2)log Λ) ≤ (1/2)(log(1.261·1.195) + (1/2)log 160000)`. -/
lemma frac_jensen_numeral {q Λ : ℝ} (hq : q ≤ 1 / 2) (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ ≤ 160000) :
    (1.261 * 1.195 : ℝ) ^ q * Λ ^ (q / 2) ≤ 24.6 := by
  have hΛ0 : 0 < Λ := by linarith
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hΛ0, ← Real.exp_add]
  have ha : 0 ≤ Real.log (1.261 * 1.195 : ℝ) := Real.log_nonneg (by norm_num)
  have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hl : Real.log Λ ≤ Real.log 160000 := Real.log_le_log hΛ0 hΛ
  have hnum : Real.exp ((Real.log (1.261 * 1.195) + Real.log 160000 * (1 / 2)) * (1 / 2))
      ≤ (24.6 : ℝ) := by
    interval_decide (trust := kernel)
  refine le_trans (Real.exp_le_exp.2 ?_) hnum
  have h3 : 0 ≤ Real.log (1.261 * 1.195) + Real.log Λ * (1 / 2) := by linarith
  calc Real.log (1.261 * 1.195) * q + Real.log Λ * (q / 2)
      = q * (Real.log (1.261 * 1.195) + Real.log Λ * (1 / 2)) := by ring
    _ ≤ 1 / 2 * (Real.log (1.261 * 1.195) + Real.log Λ * (1 / 2)) :=
        mul_le_mul_of_nonneg_right hq h3
    _ ≤ (Real.log (1.261 * 1.195) + Real.log 160000 * (1 / 2)) * (1 / 2) := by linarith

/-- `e^{q/1000}·55^{2q} ≤ 55.03` for `q ≤ ½`. -/
lemma exp_mul_rpow_fiftyfive_le {q : ℝ} (hq : q ≤ 1 / 2) :
    Real.exp (q / 1000) * (55 : ℝ) ^ (2 * q) ≤ 55.03 := by
  have h1 : Real.exp (q / 1000) ≤ Real.exp (1 / 2000) := Real.exp_le_exp.2 (by linarith)
  have h2 : (55 : ℝ) ^ (2 * q) ≤ 55 := by
    calc (55 : ℝ) ^ (2 * q) ≤ 55 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 55 := Real.rpow_one 55
  have h3 : Real.exp (1 / 2000) * 55 ≤ (55.03 : ℝ) := by interval_decide (trust := kernel)
  calc Real.exp (q / 1000) * (55 : ℝ) ^ (2 * q) ≤ Real.exp (1 / 2000) * 55 :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ ≤ 55.03 := h3

/-- **`J_R` for `Λ ≥ 6000`**: for a Rademacher family, `x > 1` with `Λ = log log x ≥ 6000`, `V ≥ 1`
and `0 < q ≤ ½`, `E[J_R(V/log x)^q] ≤ 55.03(log x)^qΛ^{-q/2}`: for `Λ ≥ 160000`
`RMF.integral_rpow_fracLine_le_large` and `e^{1/2000}·55 ≤ 55.03`, below it Jensen
(`RMF.integral_rpow_fracLine_le_jensen`) and `(1.261·1.195)^qΛ^{q/2} ≤ 24.6`. -/
theorem integral_rpow_fracLine_le_subtracted {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : 1 < x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hV : 1 ≤ V) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + ((V / Real.log x : ℝ) : ℂ) + t * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 55.03 * Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hΛp : 0 < Real.log (Real.log x) := by linarith
  have hLq : 0 ≤ Real.log x ^ q := Real.rpow_nonneg hLpos.le _
  have hg : 0 ≤ Real.log (Real.log x) ^ (-(q / 2)) := Real.rpow_nonneg hΛp.le _
  rcases le_or_gt 160000 (Real.log (Real.log x)) with hbig | hsmall
  · refine le_trans (integral_rpow_fracLine_le_large hX hx hbig hV hq0 hq) ?_
    have h := exp_mul_rpow_fiftyfive_le hq
    calc Real.exp (q / 1000) * Real.log x ^ q
          * (55 ^ (2 * q) * Real.log (Real.log x) ^ (-(q / 2)))
        = Real.exp (q / 1000) * 55 ^ (2 * q)
          * (Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2))) := by ring
      _ ≤ 55.03 * (Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2))) :=
          mul_le_mul_of_nonneg_right h (mul_nonneg hLq hg)
      _ = 55.03 * Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2)) := by ring
  · have hxe := exp_exp_le_of_one_lt hx (by linarith)
    have hx100 : Real.exp 100 ≤ x :=
      le_trans (Real.exp_le_exp.2 (by linarith [Real.add_one_le_exp (110 : ℝ)])) hxe
    have hσ : 0 ≤ V / Real.log x := div_nonneg (by linarith) hLpos.le
    refine le_trans (integral_rpow_fracLine_le_jensen hX hx100 hσ hq0.le (by linarith)) ?_
    have hnum := frac_jensen_numeral hq (by linarith) hsmall.le
    have hΛq : Real.log (Real.log x) ^ (q / 2) * Real.log (Real.log x) ^ (-(q / 2)) = 1 := by
      rw [← Real.rpow_add hΛp, add_neg_cancel, Real.rpow_zero]
    have ha : (1.261 * 1.195 : ℝ) ^ q ≤ 24.6 * Real.log (Real.log x) ^ (-(q / 2)) := by
      calc (1.261 * 1.195 : ℝ) ^ q
          = (1.261 * 1.195 : ℝ) ^ q * Real.log (Real.log x) ^ (q / 2)
            * Real.log (Real.log x) ^ (-(q / 2)) := by rw [mul_assoc, hΛq, mul_one]
        _ ≤ 24.6 * Real.log (Real.log x) ^ (-(q / 2)) := mul_le_mul_of_nonneg_right hnum hg
    rw [show (1.261 : ℝ) * (1.195 * Real.log x) = (1.261 * 1.195) * Real.log x by ring,
      Real.mul_rpow (by norm_num) hLpos.le]
    calc (1.261 * 1.195 : ℝ) ^ q * Real.log x ^ q
        ≤ 24.6 * Real.log (Real.log x) ^ (-(q / 2)) * Real.log x ^ q :=
          mul_le_mul_of_nonneg_right ha hLq
      _ = 24.6 * (Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2))) := by ring
      _ ≤ 55.03 * (Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2))) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hLq hg)
      _ = 55.03 * Real.log x ^ q * Real.log (Real.log x) ^ (-(q / 2)) := by ring

/-! ### The decomposition, and the subtracted term for `Y` -/

/-- **The decomposition, integrated**: for a Rademacher family and `σ log N ≥ 4`, almost surely
`J_Y(σ) ≤ 2.01(J_S(σ) + J_R(σ))` on the line `½ + σ + it`, `J_S = ∫_ℝ|F_N(s)/(σ+it)|²dt` the
weighted sum's line integral and `J_R = ∫_ℝ|F_N(s)|²|φ̂(s)|²dt` (`RMF.ae_lineDivSq_le_decomp`). -/
theorem ae_integral_lineDivSq_le_decomp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {N : ℕ} {σ : ℝ} (hσN : 4 ≤ σ * Real.log N) :
    ∀ᵐ ω ∂μ, (∫ t : ℝ, lineDivSq (1 / 2 + σ) X N ω t)
      ≤ 2.01 * ((∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        + ∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) := by
  obtain ⟨hσ, -⟩ := pos_and_two_le_of_le_mul_log (by norm_num : (0 : ℝ) < 4) hσN
  have hc : ∀ t : ℝ, (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ :=
    fun t => by rw [← hc]; simp
  have hmeas := measurable_randomEulerProduct_sqfree_uncurry (X := X) hX.measurable
    (1 / 2 + σ) N
  simp only [hc] at hmeas
  filter_upwards [ae_lineDivSq_le_decomp hX N, ae_forall_norm_le_one hX norm_le_one_rademacherLaw N]
    with ω hdec hω
  have hA : Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := integrable_line_div_sq_half_add hσ hω
  have hB : Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := by
    refine Integrable.mono' ((integrable_normSq_fracMellin (σ := σ) (by linarith)).const_mul
      (eulerBound N ^ 2)) ((((hmeas.comp measurable_prodMk_left).norm.pow_const 2).mul
        ((continuous_fracMellin_line (by linarith)).norm.pow 2).measurable).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    have hb := norm_randomEulerProduct_sqfree_le hω
      (s := (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre t]; linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg _)
  have hpt : ∀ t : ℝ, lineDivSq (1 / 2 + σ) X N ω t
      ≤ 2.01 * (‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        + ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) := fun t => by
    have h := hdec σ hσN t
    simp only [shiftLine_eq_half_add] at h
    exact h
  calc (∫ t : ℝ, lineDivSq (1 / 2 + σ) X N ω t)
      ≤ ∫ t : ℝ, 2.01 * (‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        + ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => by unfold lineDivSq; positivity)
          ((hA.add hB).const_mul _) (Filter.Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul, integral_add hA hB]

/-- **The decomposition at the `q`-th power**: for a Rademacher family, `N ≥ 2`,
`σ log(N + 1) ≥ 4` and `0 ≤ q ≤ 1`, `E[J_Y(σ)^q] ≤ 2.01^q(E[J_S(σ)^q] + E[J_R(σ)^q])`
(`RMF.ae_integral_lineDivSq_le_decomp` and `(a + b)^q ≤ a^q + b^q`). -/
theorem integral_rpow_lineDivSq_le_decomp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {N : ℕ} (hN : 2 ≤ N) {σ q : ℝ}
    (hσN : 4 ≤ σ * Real.log ((N + 1 : ℕ) : ℝ)) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + σ) X (N + 1) ω t) ^ q ∂μ)
      ≤ 2.01 ^ q * ((∫ ω, (∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        + ∫ ω, (∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q ∂μ) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨hσ, -⟩ := pos_and_two_le_of_le_mul_log (by norm_num : (0 : ℝ) < 4) hσN
  have hS := integrable_rpow_eulerProductLine_of_two_le hX hN hσ hq0
  have hR := integrable_rpow_fracLine_of_two_le hX hN hσ.le hq0
  have hY := integrable_lineDivSq_rpow_extended hX (N + 1)
    (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + σ) hq0
  rw [← integral_add hS hR, ← integral_const_mul]
  refine integral_mono_ae hY ((hS.add hR).const_mul _) ?_
  filter_upwards [ae_integral_lineDivSq_le_decomp hX hσN] with ω hω
  have hA0 : 0 ≤ ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := integral_nonneg fun t => by positivity
  have hB0 : 0 ≤ ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2 := integral_nonneg fun t => by positivity
  have hJ0 : 0 ≤ ∫ t : ℝ, lineDivSq (1 / 2 + σ) X (N + 1) ω t :=
    integral_nonneg fun t => by unfold lineDivSq; positivity
  calc (∫ t : ℝ, lineDivSq (1 / 2 + σ) X (N + 1) ω t) ^ q
      ≤ (2.01 * ((∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
          + ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2)) ^ q :=
        Real.rpow_le_rpow hJ0 hω hq0
    _ = 2.01 ^ q * ((∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
          + ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
              * ‖fracMellin (1 / 2 + σ + t * Complex.I)‖ ^ 2) ^ q :=
        Real.mul_rpow (by norm_num) (add_nonneg hA0 hB0)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow hA0 hB0 hq0 hq1)
        (Real.rpow_nonneg (by norm_num) _)

/-- **The subtracted term's arithmetic for `Y`**: from `E ≤ 2.01^q(A + B)`, `A ≤ 216·P·m·g`,
`B ≤ 55.03·P·g`, `m ≥ 1`, `P, g ≥ 0` and `q ≤ ½`, `E ≤ 400·P·m·g`: `2.01^q ≤ 2.01^{1/2} ≤ 1.42`
and `1.42(216 + 55.03) ≤ 384.9`. -/
lemma subtracted_belowHalf_ext_arith {E A B P m g q : ℝ} (hq : q ≤ 1 / 2)
    (hE : E ≤ 2.01 ^ q * (A + B)) (hA : A ≤ 216 * P * m * g) (hB : B ≤ 55.03 * P * g)
    (hm : 1 ≤ m) (hP : 0 ≤ P) (hg : 0 ≤ g) :
    E ≤ 400 * P * m * g := by
  have hc : (2.01 : ℝ) ^ q ≤ 1.42 := by
    have h1 : (2.01 : ℝ) ^ q ≤ 2.01 ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
    have h2 : (2.01 : ℝ) ^ (1 / 2 : ℝ) ≤ 1.42 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hc0 : 0 ≤ (2.01 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  have hPmg : 0 ≤ P * m * g := mul_nonneg (mul_nonneg hP (by linarith)) hg
  have hB' : B ≤ 55.03 * (P * m * g) := by
    have h : 55.03 * (P * g) * 1 ≤ 55.03 * (P * g) * m :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (mul_nonneg hP hg))
    calc B ≤ 55.03 * P * g := hB
      _ = 55.03 * (P * g) * 1 := by ring
      _ ≤ 55.03 * (P * g) * m := h
      _ = 55.03 * (P * m * g) := by ring
  have hAB : A + B ≤ 271.03 * (P * m * g) := by
    have hA' : A ≤ 216 * (P * m * g) := by
      calc A ≤ 216 * P * m * g := hA
        _ = 216 * (P * m * g) := by ring
    linarith
  calc E ≤ 2.01 ^ q * (A + B) := hE
    _ ≤ 2.01 ^ q * (271.03 * (P * m * g)) := mul_le_mul_of_nonneg_left hAB hc0
    _ ≤ 1.42 * (271.03 * (P * m * g)) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num) hPmg)
    _ = (1.42 * 271.03) * (P * m * g) := by ring
    _ ≤ 400 * (P * m * g) := mul_le_mul_of_nonneg_right (by norm_num) hPmg
    _ = 400 * P * m * g := by ring

/-- **The subtracted term below `½` for `Y`**: for a Rademacher family, `x > 1` with
`Λ = log log x ≥ 6000`, `V ≥ 8` and `0 < q < ½`,

`E[J_Y(V/log x)^q] ≤ 400(log x)^q·min{Λ, (1-2q)⁻¹}·Λ^{-q/2}`,

`J_Y(σ) = ∫_ℝ lineDivSq (½ + σ) X (⌊x⌋ + 1) ω t dt` the line integral of
`RMF.le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering`: the decomposition
(`RMF.integral_rpow_lineDivSq_le_decomp`, `σ log(⌊x⌋ + 1) ≥ V ≥ 4`), the weighted sum's bound
`RMF.integral_rpow_lineDiv_le_subtracted_belowHalf` (`216`),
`RMF.integral_rpow_fracLine_le_subtracted` (`55.03`, with `min{Λ, (1-2q)⁻¹} ≥ 1`) and
`2.01^{1/2}(216 + 55.03) ≤ 400`. -/
theorem integral_rpow_lineDivSq_le_subtracted_belowHalf {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : 1 < x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hV : 8 ≤ V) (hq0 : 0 < q) (hq : q < 1 / 2) :
    (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
      ≤ 400 * Real.log x ^ q * min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hxe := exp_exp_le_of_one_lt hx (by linarith)
  have hx0 : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hΛp : 0 < Real.log (Real.log x) := by linarith
  have hx3 : (3 : ℝ) ≤ x := by
    have h1 := Real.add_one_le_exp (Real.exp 110)
    have h2 := Real.add_one_le_exp (110 : ℝ)
    linarith
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  -- `σ log(⌊x⌋ + 1) ≥ V ≥ 4`
  have hσN : 4 ≤ V / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    have h1 : Real.log x ≤ Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
      Real.log_le_log hx0 (by push_cast; exact (Nat.lt_floor_add_one x).le)
    have h2 : V / Real.log x * Real.log x = V := div_mul_cancel₀ V hLpos.ne'
    have h3 : V / Real.log x * Real.log x ≤ V / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) hLpos.le)
    linarith
  have hdec := integral_rpow_lineDivSq_le_decomp hX hN2 hσN hq0.le (by linarith)
  have hS := integral_rpow_lineDiv_le_subtracted_belowHalf hX hx hΛ (V := V) (by linarith) hq0 hq
  have hR := integral_rpow_fracLine_le_subtracted hX hx hΛ (V := V) (by linarith) hq0 hq.le
  have hm : 1 ≤ min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ :=
    le_min (by linarith) ((one_le_inv₀ (by linarith)).2 (by linarith))
  exact subtracted_belowHalf_ext_arith hq.le hdec hS hR hm (Real.rpow_nonneg hLpos.le _)
    (Real.rpow_nonneg hΛp.le _)

/-! ### The reduction's constant -/

/-- **`cJ(q) ≤ 1/6`** for `0 ≤ q ≤ ½`: `cJ(q) = 3^{q-1}2^{2q-1}(8π)^{-q} = (1/6)(3/(2π))^q`. -/
lemma cJ_le_one_sixth {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) : cJ q ≤ 1 / 6 := by
  unfold cJ
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 8 * Real.pi), ← Real.exp_add,
    ← Real.exp_add]
  have h6 : (1 : ℝ) / 6 = Real.exp (-(Real.log 3 + Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
    norm_num
  rw [h6, Real.exp_le_exp]
  have h8 : Real.log (8 * Real.pi) = 3 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hπ : Real.log 3 ≤ Real.log 2 + Real.log Real.pi := by
    rw [← Real.log_mul (by norm_num) Real.pi_pos.ne']
    exact Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  rw [h8]
  nlinarith [mul_le_mul_of_nonneg_left hπ hq0]

end RMF
