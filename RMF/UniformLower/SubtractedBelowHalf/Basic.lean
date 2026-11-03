/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UHalfCellExplicit
import RMF.Weighted.AboveHalfBandLevelExplicit
import RMF.Weighted.LowerFixedQ

/-!
# The subtracted term below `½`: the pieces

The explicit reduction subtracts `E[J(σ)^q]`, `J(σ) = ∫_ℝ‖F_{⌊x⌋+1}(½+σ+it)/(σ+it)‖²dt`; here are
the pieces that bound it through `Z = (log y)⁻¹J_y(σ)` at `y = halfY x`, `σ = halfSigma x`.

* **The high primes integrated out** (`RMF.integral_rpow_lineDiv_le_mBand_rpow_mul`): for
  `2 ≤ y ≤ N`, `E[J_N^q] ≤ mBand(y, N)^q·E[J_y^q]`, by the balanced Hölder inequality at `κ = 1`
  (`RMF.integral_rpow_integral_mul_le_of_indep`): independence of disjoint prime blocks and the
  upper block's second moment, no conditional expectation.
* **`Z` at `q = ½`** from the bracket of the ten chain,
  `RMF.integral_norm_weightedRademacherSum_le_ten_assembly` (`RMF.integral_sqrt_Z_halfY_le_ten`):
  `E[Z^{1/2}] ≤ 17.2Λ^{3/4}` for `Λ ≥ 2400` (`RMF.integral_sqrt_Z_halfY_le`).
* **`Z` below `½`**: the bracket of the U chain,
  `RMF.integral_rpow_weightedRademacherSum_le_u_assembly` (`RMF.integral_rpow_Z_halfY_le_u`), and
  its cell core near `½` (`RMF.z_half_core`, the twin of `RMF.u_half_core` without the reduction's
  constant, with the central window `RMF.uCen_pf_le_half`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The high primes integrated out -/

omit [MeasurableSpace Ω] in
/-- The damped line integral in the weight form: `‖u/(σ+it)‖² = (σ²+t²)⁻¹‖u‖²` along
`RMF.shiftLine σ t = ½ + σ + it`. -/
lemma integral_lineDiv_eq_weight (X : ℕ → Ω → ℂ) (N : ℕ) (σ : ℝ) (ω : Ω) :
    (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = ∫ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            (shiftLine σ t) ω‖ ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hs : shiftLine σ t = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
    rw [shiftLine]
    push_cast
    ring
  simp only [hs]
  rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
    Complex.normSq_add_mul_I, div_eq_mul_inv, mul_comm]

set_option maxHeartbeats 1000000 in
-- Fubini twice around the factorisation, and the balanced Hölder
/-- **The high block integrated out, abstractly.**  On a probability space, with a weight `ρ ≥ 0`
integrable on `ℝ`, `∫ρ > 0`, and jointly measurable `f, g ≥ 0` with `0 < l_f ≤ f ≤ u_f` and
`0 < l_g ≤ g ≤ u_g` almost surely at every height, if `E[A^{q-1}f(t)g(t)] = E[A^{q-1}f(t)]E[g(t)]`
(`A = ∫ρf`) and `E[g(t)] ≤ m` at every height, then for `0 ≤ q ≤ 1`
`E[(∫ρfg)^q] ≤ m^q·E[(∫ρf)^q]`: `RMF.integral_rpow_le_of_mixed_le` at `N = mA`, `κ = 1`. -/
theorem integral_rpow_integral_mul_le_of_indep {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ρ : ℝ → ℝ} {f g : Ω → ℝ → ℝ} {q m lf uf lg ug : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ) (hI : 0 < ∫ t, ρ t)
    (hfm : Measurable (Function.uncurry f)) (hgm : Measurable (Function.uncurry g))
    (hf0 : ∀ ω t, 0 ≤ f ω t) (hg0 : ∀ ω t, 0 ≤ g ω t) (hlf : 0 < lf) (hlg : 0 < lg)
    (hf : ∀ᵐ ω ∂μ, ∀ t, lf ≤ f ω t ∧ f ω t ≤ uf) (hg : ∀ᵐ ω ∂μ, ∀ t, lg ≤ g ω t ∧ g ω t ≤ ug)
    (hm0 : 0 < m)
    (hind : ∀ t, (∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * f ω t * g ω t ∂μ)
      = (∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * f ω t ∂μ) * ∫ ω, g ω t ∂μ)
    (hm : ∀ t, (∫ ω, g ω t ∂μ) ≤ m) :
    (∫ ω, (∫ t, ρ t * (f ω t * g ω t)) ^ q ∂μ) ≤ m ^ q * ∫ ω, (∫ t, ρ t * f ω t) ^ q ∂μ := by
  -- measurability
  have hjf : Measurable fun z : Ω × ℝ => ρ z.2 * f z.1 z.2 := (hρm.comp measurable_snd).mul hfm
  have hjfg : Measurable fun z : Ω × ℝ => ρ z.2 * (f z.1 z.2 * g z.1 z.2) :=
    (hρm.comp measurable_snd).mul (hfm.mul hgm)
  have hAm : Measurable fun ω => ∫ t, ρ t * f ω t :=
    (hjf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hWm : Measurable fun ω => ∫ t, ρ t * (f ω t * g ω t) :=
    (hjfg.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hA0 : ∀ ω, 0 ≤ ∫ t, ρ t * f ω t := fun ω =>
    integral_nonneg fun t => mul_nonneg (hρ0 t) (hf0 ω t)
  have hW0 : ∀ ω, 0 ≤ ∫ t, ρ t * (f ω t * g ω t) := fun ω =>
    integral_nonneg fun t => mul_nonneg (hρ0 t) (mul_nonneg (hf0 ω t) (hg0 ω t))
  have huf : lf ≤ uf := by
    obtain ⟨ω, hω⟩ := hf.exists
    exact le_trans (hω 0).1 (hω 0).2
  -- the two functionals are two-sided almost surely
  have hbd : ∀ᵐ ω ∂μ, lf * (∫ t, ρ t) ≤ ∫ t, ρ t * f ω t
      ∧ (∫ t, ρ t * f ω t) ≤ uf * ∫ t, ρ t
      ∧ lf * lg * (∫ t, ρ t) ≤ ∫ t, ρ t * (f ω t * g ω t)
      ∧ (∫ t, ρ t * (f ω t * g ω t)) ≤ uf * ug * ∫ t, ρ t := by
    filter_upwards [hf, hg] with ω hfω hgω
    have hfω' : Measurable fun t => f ω t := hfm.comp measurable_prodMk_left
    have hgω' : Measurable fun t => g ω t := hgm.comp measurable_prodMk_left
    have h1 : Integrable fun t => ρ t * f ω t := by
      refine Integrable.mono' (hρi.mul_const uf) (hρm.mul hfω').aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (hf0 ω t))]
      exact mul_le_mul_of_nonneg_left (hfω t).2 (hρ0 t)
    have h2 : Integrable fun t => ρ t * (f ω t * g ω t) := by
      refine Integrable.mono' (hρi.mul_const (uf * ug))
        (hρm.mul (hfω'.mul hgω')).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (mul_nonneg (hf0 ω t) (hg0 ω t)))]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hfω t).2 (hgω t).2 (hg0 ω t)
        (le_trans (hf0 ω t) (hfω t).2)) (hρ0 t)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← integral_const_mul]
      refine integral_mono (hρi.const_mul lf) h1 fun t => ?_
      have := mul_le_mul_of_nonneg_left (hfω t).1 (hρ0 t)
      change lf * ρ t ≤ ρ t * f ω t
      linarith
    · rw [← integral_const_mul]
      refine integral_mono h1 (hρi.const_mul uf) fun t => ?_
      have := mul_le_mul_of_nonneg_left (hfω t).2 (hρ0 t)
      change ρ t * f ω t ≤ uf * ρ t
      linarith
    · rw [← integral_const_mul]
      refine integral_mono (hρi.const_mul (lf * lg)) h2 fun t => ?_
      have := mul_le_mul_of_nonneg_left (mul_le_mul (hfω t).1 (hgω t).1 hlg.le
        (hf0 ω t)) (hρ0 t)
      change lf * lg * ρ t ≤ ρ t * (f ω t * g ω t)
      linarith
    · rw [← integral_const_mul]
      refine integral_mono h2 (hρi.const_mul (uf * ug)) fun t => ?_
      have := mul_le_mul_of_nonneg_left (mul_le_mul (hfω t).2 (hgω t).2 (hg0 ω t)
        (le_trans (hf0 ω t) (hfω t).2)) (hρ0 t)
      change ρ t * (f ω t * g ω t) ≤ uf * ug * ρ t
      linarith
  have ha₀ : 0 < lf * ∫ t, ρ t := mul_pos hlf hI
  have hNlo : 0 < m * (lf * ∫ t, ρ t) := mul_pos hm0 ha₀
  -- the integrabilities of the balanced Hölder
  have hNi : Integrable (fun ω => (m * ∫ t, ρ t * f ω t) ^ q) μ := by
    refine (memLp_top_of_bound ((hAm.const_mul m).pow_const q).aestronglyMeasurable
      ((m * (uf * ∫ t, ρ t)) ^ q) ?_).integrable le_top
    filter_upwards [hbd] with ω h
    have h0 : 0 ≤ m * ∫ t, ρ t * f ω t := mul_nonneg hm0.le (hA0 ω)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 _)]
    exact Real.rpow_le_rpow h0 (mul_le_mul_of_nonneg_left h.2.1 hm0.le) hq0
  have hi : Integrable (fun ω => (∫ t, ρ t * (f ω t * g ω t)) ^ q) μ := by
    refine (memLp_top_of_bound (hWm.pow_const q).aestronglyMeasurable
      ((uf * ug * ∫ t, ρ t) ^ q) ?_).integrable le_top
    filter_upwards [hbd] with ω h
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hW0 ω) _)]
    exact Real.rpow_le_rpow (hW0 ω) h.2.2.2 hq0
  have hABi : Integrable (fun ω => (m * ∫ t, ρ t * f ω t) ^ (q - 1)
      * ∫ t, ρ t * (f ω t * g ω t)) μ := by
    refine (memLp_top_of_bound (((hAm.const_mul m).pow_const (q - 1)).mul hWm).aestronglyMeasurable
      ((m * (lf * ∫ t, ρ t)) ^ (q - 1) * (uf * ug * ∫ t, ρ t)) ?_).integrable le_top
    filter_upwards [hbd] with ω h
    simp only [Pi.mul_apply]
    have hN : m * (lf * ∫ t, ρ t) ≤ m * ∫ t, ρ t * f ω t := mul_le_mul_of_nonneg_left h.1 hm0.le
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (le_trans hNlo.le hN) _) (hW0 ω))]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hNlo hN (by linarith)) h.2.2.2 (hW0 ω)
      (Real.rpow_nonneg hNlo.le _)
  have hα : 0 < ∫ ω, (m * ∫ t, ρ t * f ω t) ^ q ∂μ := by
    refine lt_of_lt_of_le (Real.rpow_pos_of_pos hNlo q) ?_
    calc (m * (lf * ∫ t, ρ t)) ^ q = ∫ _ω, (m * (lf * ∫ t, ρ t)) ^ q ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hNi (by
          filter_upwards [hbd] with ω h
          exact Real.rpow_le_rpow hNlo.le (mul_le_mul_of_nonneg_left h.1 hm0.le) hq0)
  have hβ : 0 < ∫ ω, (m * ∫ t, ρ t * f ω t) ^ (q - 1) * (∫ t, ρ t * (f ω t * g ω t)) ∂μ := by
    have hNup : 0 < m * (uf * ∫ t, ρ t) := mul_pos hm0 (mul_pos (lt_of_lt_of_le hlf huf) hI)
    have hlo : 0 < (m * (uf * ∫ t, ρ t)) ^ (q - 1) * (lf * lg * ∫ t, ρ t) :=
      mul_pos (Real.rpow_pos_of_pos hNup _) (mul_pos (mul_pos hlf hlg) hI)
    refine lt_of_lt_of_le hlo ?_
    calc (m * (uf * ∫ t, ρ t)) ^ (q - 1) * (lf * lg * ∫ t, ρ t)
        = ∫ _ω, (m * (uf * ∫ t, ρ t)) ^ (q - 1) * (lf * lg * ∫ t, ρ t) ∂μ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hABi (by
          filter_upwards [hbd] with ω h
          have hpos : 0 < m * ∫ t, ρ t * f ω t :=
            lt_of_lt_of_le hNlo (mul_le_mul_of_nonneg_left h.1 hm0.le)
          exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hpos
            (mul_le_mul_of_nonneg_left h.2.1 hm0.le) (by linarith)) h.2.2.1
            (mul_pos (mul_pos hlf hlg) hI).le (Real.rpow_nonneg hpos.le _))
  -- the two product integrands
  have hH₁ : Integrable (Function.uncurry fun ω t =>
      (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * (f ω t * g ω t))) (μ.prod volume) := by
    refine Integrable.mono'
      ((integrable_const ((lf * ∫ t, ρ t) ^ (q - 1) * (uf * ug))).mul_prod hρi)
      (((hAm.pow_const (q - 1)).comp measurable_fst).mul hjfg).aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := volume)).ae
      (hbd.and (hf.and hg))] with z hz
    obtain ⟨h, hfz, hgz⟩ := hz
    change ‖(∫ u, ρ u * f z.1 u) ^ (q - 1) * (ρ z.2 * (f z.1 z.2 * g z.1 z.2))‖
      ≤ (lf * ∫ t, ρ t) ^ (q - 1) * (uf * ug) * ρ z.2
    have hp : 0 < ∫ u, ρ u * f z.1 u := lt_of_lt_of_le ha₀ h.1
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hp.le _)
      (mul_nonneg (hρ0 _) (mul_nonneg (hf0 _ _) (hg0 _ _))))]
    have hfg : ρ z.2 * (f z.1 z.2 * g z.1 z.2) ≤ uf * ug * ρ z.2 := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul (hfz z.2).2 (hgz z.2).2 (hg0 _ _)
        (le_trans (hf0 _ _) (hfz z.2).2)) (hρ0 z.2)
      linarith
    calc (∫ u, ρ u * f z.1 u) ^ (q - 1) * (ρ z.2 * (f z.1 z.2 * g z.1 z.2))
        ≤ (lf * ∫ t, ρ t) ^ (q - 1) * (uf * ug * ρ z.2) :=
          mul_le_mul (Real.rpow_le_rpow_of_nonpos ha₀ h.1 (by linarith)) hfg
            (mul_nonneg (hρ0 _) (mul_nonneg (hf0 _ _) (hg0 _ _))) (Real.rpow_nonneg ha₀.le _)
      _ = _ := by ring
  have hH₂ : Integrable (Function.uncurry fun ω t =>
      (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * f ω t)) (μ.prod volume) := by
    refine Integrable.mono'
      ((integrable_const ((lf * ∫ t, ρ t) ^ (q - 1) * uf)).mul_prod hρi)
      (((hAm.pow_const (q - 1)).comp measurable_fst).mul hjf).aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := volume)).ae
      (hbd.and hf)] with z hz
    obtain ⟨h, hfz⟩ := hz
    change ‖(∫ u, ρ u * f z.1 u) ^ (q - 1) * (ρ z.2 * f z.1 z.2)‖
      ≤ (lf * ∫ t, ρ t) ^ (q - 1) * uf * ρ z.2
    have hp : 0 < ∫ u, ρ u * f z.1 u := lt_of_lt_of_le ha₀ h.1
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hp.le _)
      (mul_nonneg (hρ0 _) (hf0 _ _)))]
    have hfb : ρ z.2 * f z.1 z.2 ≤ uf * ρ z.2 := by
      have := mul_le_mul_of_nonneg_left (hfz z.2).2 (hρ0 z.2)
      linarith
    calc (∫ u, ρ u * f z.1 u) ^ (q - 1) * (ρ z.2 * f z.1 z.2)
        ≤ (lf * ∫ t, ρ t) ^ (q - 1) * (uf * ρ z.2) :=
          mul_le_mul (Real.rpow_le_rpow_of_nonpos ha₀ h.1 (by linarith)) hfb
            (mul_nonneg (hρ0 _) (hf0 _ _)) (Real.rpow_nonneg ha₀.le _)
      _ = _ := by ring
  -- the mixed moment: Fubini, the factorisation at each height, Fubini back
  have hmix : (∫ ω, (∫ t, ρ t * f ω t) ^ (q - 1) * (∫ t, ρ t * (f ω t * g ω t)) ∂μ)
      ≤ m * ∫ ω, (∫ t, ρ t * f ω t) ^ q ∂μ := by
    have hstep : ∀ t, (∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * (f ω t * g ω t)) ∂μ)
        ≤ m * ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * f ω t) ∂μ := by
      intro t
      have e1 : (∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * (f ω t * g ω t)) ∂μ)
          = ρ t * ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * f ω t * g ω t ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
      have e2 : (∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * f ω t) ∂μ)
          = ρ t * ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * f ω t ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
      rw [e1, e2, hind t]
      have hE : 0 ≤ ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * f ω t ∂μ :=
        integral_nonneg fun ω => mul_nonneg (Real.rpow_nonneg (hA0 ω) _) (hf0 ω t)
      have := mul_le_mul_of_nonneg_left (hm t) (mul_nonneg (hρ0 t) hE)
      linarith
    calc (∫ ω, (∫ t, ρ t * f ω t) ^ (q - 1) * (∫ t, ρ t * (f ω t * g ω t)) ∂μ)
        = ∫ ω, (∫ t, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * (f ω t * g ω t))) ∂μ := by
          congr 1
          funext ω
          exact (integral_const_mul _ _).symm
      _ = ∫ t, ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * (f ω t * g ω t)) ∂μ :=
          integral_integral_swap hH₁
      _ ≤ ∫ t, m * ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * f ω t) ∂μ :=
          integral_mono hH₁.integral_prod_right (hH₂.integral_prod_right.const_mul m) hstep
      _ = m * ∫ t, ∫ ω, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * f ω t) ∂μ :=
          integral_const_mul _ _
      _ = m * ∫ ω, (∫ t, (∫ u, ρ u * f ω u) ^ (q - 1) * (ρ t * f ω t)) ∂μ := by
          rw [integral_integral_swap hH₂]
      _ = m * ∫ ω, (∫ t, ρ t * f ω t) ^ q ∂μ := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hbd] with ω h
          have hp : 0 < ∫ t, ρ t * f ω t := lt_of_lt_of_le ha₀ h.1
          rw [integral_const_mul]
          nth_rewrite 2 [← Real.rpow_one (∫ t, ρ t * f ω t)]
          rw [← Real.rpow_add hp]
          norm_num
  -- the balanced Hölder at `κ = 1`
  have hpow : ∀ ω, (m * ∫ t, ρ t * f ω t) ^ (q - 1)
      = m ^ (q - 1) * (∫ t, ρ t * f ω t) ^ (q - 1) := fun ω => Real.mul_rpow hm0.le (hA0 ω)
  have eR : (∫ ω, (m * ∫ t, ρ t * f ω t) ^ q ∂μ) = m ^ q * ∫ ω, (∫ t, ρ t * f ω t) ^ q ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    exact Real.mul_rpow hm0.le (hA0 ω)
  have hbd' : (∫ ω, (m * ∫ t, ρ t * f ω t) ^ (q - 1) * (∫ t, ρ t * (f ω t * g ω t)) ∂μ)
      ≤ 1 * ∫ ω, (m * ∫ t, ρ t * f ω t) ^ q ∂μ := by
    have eL : (∫ ω, (m * ∫ t, ρ t * f ω t) ^ (q - 1) * (∫ t, ρ t * (f ω t * g ω t)) ∂μ)
        = m ^ (q - 1) * ∫ ω, (∫ t, ρ t * f ω t) ^ (q - 1) * (∫ t, ρ t * (f ω t * g ω t)) ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext ω
      rw [hpow ω]
      ring
    have hmq : m ^ (q - 1) * m = m ^ q := by
      rw [← Real.rpow_add_one hm0.ne', sub_add_cancel]
    rw [eL, eR, one_mul]
    have := mul_le_mul_of_nonneg_left hmix (Real.rpow_nonneg hm0.le (q - 1))
    calc _ ≤ m ^ (q - 1) * (m * ∫ ω, (∫ t, ρ t * f ω t) ^ q ∂μ) := this
      _ = m ^ q * ∫ ω, (∫ t, ρ t * f ω t) ^ q ∂μ := by rw [← mul_assoc, hmq]
  have hN : ∀ᵐ ω ∂μ, 0 < m * ∫ t, ρ t * f ω t := by
    filter_upwards [hbd] with ω h
    exact lt_of_lt_of_le hNlo (mul_le_mul_of_nonneg_left h.1 hm0.le)
  have hkey := integral_rpow_le_of_mixed_le (μ := μ) (N := fun ω => m * ∫ t, ρ t * f ω t)
    (W := fun ω => ∫ t, ρ t * (f ω t * g ω t)) (κ := 1) hq0 hq1 hN
    (Filter.Eventually.of_forall hW0) hNi hABi hi hα hβ zero_le_one hbd'
  rw [Real.one_rpow, one_mul, eR] at hkey
  exact hkey

set_option maxHeartbeats 1000000 in
-- the envelopes and the independence at each height
/-- **The high primes integrated out, in the weight form**: for a Rademacher family, `2 ≤ y ≤ N`,
`σ > 0` and `0 ≤ q ≤ 1`,
`E[(∫_ℝ(σ²+t²)⁻¹‖F_{N+1}(s_t)‖²dt)^q] ≤ mBand(y, N)^q·E[(∫_ℝ(σ²+t²)⁻¹‖F_{y+1}(s_t)‖²dt)^q]`,
`s_t = RMF.shiftLine σ t`: `RMF.integral_rpow_integral_mul_le_of_indep` with `f = ‖F_{y+1}‖²`,
`g = ‖F_{(y,N]}‖²`, their envelopes, independence of the two blocks and Mertens for `E g`
(`RMF.integral_normSq_line_le_mBand`). -/
theorem integral_rpow_weight_le_mBand_rpow_mul {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N) {σ q : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ mBand y N ^ q * ∫ ω, (∫ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hρpos : ∀ t : ℝ, 0 < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hρm : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
    (Continuous.inv₀ (by fun_prop) fun t => (hρpos t).ne').measurable
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
  refine integral_rpow_integral_mul_le_of_indep (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (f := fun ω t => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
      (shiftLine σ t) ω‖ ^ 2)
    (g := fun ω t => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (y + 1) (N + 1) (shiftLine σ t) ω‖ ^ 2)
    (lf := (∏ p ∈ Nat.primesBelow (y + 1), (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    (uf := (∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    (lg := (∏ p ∈ primesIco (y + 1) (N + 1), (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    (ug := (∏ p ∈ primesIco (y + 1) (N + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2)
    hq0 hq1 hρm (fun t => (inv_pos.2 (hρpos t)).le) (integrable_inv_sq_add_sq hσ.ne') ?_ hPm hQm
    (fun ω t => sq_nonneg _) (fun ω t => sq_nonneg _) (pow_pos hLP 2) (pow_pos hLQ 2) ?_ ?_ hm0
    ?_ ?_
  · rw [integral_inv_sq_add_sq hσ]
    positivity
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
            (fun u => (σ ^ 2 + u ^ 2)⁻¹) v) ^ (q - 1)
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
    have hs : shiftLine σ t = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
      rw [shiftLine]
      push_cast
      ring
    simp only [hs]
    exact h

/-- **The high primes integrated out**: for a Rademacher family, `2 ≤ y ≤ N`,
`σ > 0` and `0 ≤ q ≤ 1`, `E[J_N(σ)^q] ≤ mBand(y, N)^q·E[J_y(σ)^q]`,
`J_M(σ) = ∫_ℝ‖F_{M+1}(½+σ+it)/(σ+it)‖²dt` (`RMF.integral_rpow_weight_le_mBand_rpow_mul`). -/
theorem integral_rpow_lineDiv_le_mBand_rpow_mul {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N) {σ q : ℝ}
    (hσ : 0 < σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (N + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ mBand y N ^ q * ∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  simp only [integral_lineDiv_eq_weight]
  exact integral_rpow_weight_le_mBand_rpow_mul hX hy hyN hσ hq0 hq1

/-! ### `Z` at `q = ½`: the ten chain -/

set_option maxHeartbeats 1000000 in
-- three ranges and their bounds
/-- **`Z` at `q = ½` from the ten chain**: for `x ≥ exp(e^{110})`, with `y = halfY x`,
`σ = halfSigma x` and `Z = (log y)⁻¹∫_ℝ‖F_{y+1}(½+σ+it)/(σ+it)‖²dt`,
`E[Z^{1/2}] ≤ C_c^{1/2} + ∑_{4≤k<J₀} b_k + (2·1.195e⁴)^{1/2}` (`C_c = RMF.tenCen`,
`b_k = RMF.tenWindowBound`, `J₀ = RMF.tenJ`): the bracket of
`RMF.integral_norm_weightedRademacherSum_le_ten_assembly`. -/
theorem integral_sqrt_Z_halfY_le_ten {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ tenCen x ^ (1 / 2 : ℝ) + ∑ k ∈ Finset.Ico 4 (tenJ x), tenWindowBound x k
        + (2 * 1.195 / Real.exp (-((4 : ℕ) : ℝ))) ^ (1 / 2 : ℝ) := by
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  obtain ⟨hy2, -, -, -, hy99, -⟩ := halfY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hJ4 : 4 ≤ tenJ x := by
    rw [tenJ]
    have h1 : (3 : ℝ) ≤ Real.log (2 / 3 * Real.log (halfY x)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h2 : Real.exp 3 ≤ 21 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_lt_d9
        have h4 : Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
        linarith [show (2.72 : ℝ) ^ 3 ≤ 21 by norm_num]
      have := (halfY_loglog_le hx).2
      linarith
    have : 3 ≤ ⌊Real.log (2 / 3 * Real.log (halfY x))⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    omega
  have hJ4R : (4 : ℝ) ≤ ((tenJ x : ℕ) : ℝ) := by exact_mod_cast hJ4
  have hwv : Real.exp (-((tenJ x : ℕ) : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  -- the central window
  have hb1 := integral_rpow_centralRange_le_sharp hX (σ := halfSigma x) (q := 1 / 2)
    (w := Real.exp (-((tenJ x : ℕ) : ℝ))) hy2 hσ (Real.exp_pos _) (by norm_num) le_rfl
  have hPFc : Real.exp (1 / 2 * (1 - 2 * (1 / 2)) * (9.0028 / Real.log (halfY x)
      + 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4) - 3 / 20))
      * Real.log (halfY x) ^ (1 / 2 * (2 * (1 / 2) - 1) : ℝ) = 1 := by norm_num
  rw [hPFc, mul_one] at hb1
  -- the windows
  have hb2 := mesoRange_half_le_sum hX hy2 hσ (k₀ := 4) (J := tenJ x) hJ4
    (fun k hk => tenWindow_le hX hx hk)
  -- the far range
  have hb3 := integral_rpow_eulerProductLine_tail_le_explicit hX (q := 1 / 2) (by norm_num)
    (by norm_num) hy99 hσ (T := Real.exp (-((4 : ℕ) : ℝ))) (Real.exp_pos _)
  have hZ := integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := halfSigma x) (q := 1 / 2)
    (w := Real.exp (-((tenJ x : ℕ) : ℝ))) (v := Real.exp (-((4 : ℕ) : ℝ))) hy2 hσ (by norm_num)
    (by norm_num) hwv hb1 hb2 hb3
  have hcen : ((Real.pi / halfSigma x + 2 * (Real.exp (2 * (1 - 1 / 2)
      * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
      * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1) / Real.exp (-((tenJ x : ℕ) : ℝ)))
      / Real.log (halfY x)) = tenCen x := by
    rw [tenCen]
  rw [hcen] at hZ
  exact hZ

/-- **`Z` at `q = ½`: `E[Z^{1/2}] ≤ 17.2Λ^{3/4}`** for `x ≥ exp(e^{110})` with
`Λ = log log x ≥ 2400`: `RMF.integral_sqrt_Z_halfY_le_ten` with `C_c^{1/2} ≤ 7.09√Λ + 0.2`, the
far range `≤ 11.43` and the windows `≤ 4042 + 16.847(Λ^{3/4} - 298.9)` (`RMF.tenMeso_le_large` at
the chaos constant `4.68`). -/
theorem integral_sqrt_Z_halfY_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 2400 ≤ Real.log (Real.log x)) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ 172 / 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have h := integral_sqrt_Z_halfY_le_ten hX hx
  have hCen := tenCen_rpow_le hx
  have hfar := half_far_le
  have hmeso := tenMeso_le_large hx hΛ (A := 468 / 100) (by norm_num)
    (tenChaosConst_le (by linarith))
  obtain ⟨s, hs0, hs4, hs3, hs2⟩ := quarter_facts (Λ := Real.log (Real.log x)) (by linarith)
  rw [← hs3] at hmeso ⊢
  rw [← hs2] at hCen
  have hpoly : 709 / 100 * s ^ 2 + 2 / 10 + (93 * (22437 / 10000) + 2008 * (1909 / 1000)
      + 1909 / 1000 * (468 / 100) * (14143 / 10000) * (4 / 3 * (s ^ 3 - 2989 / 10))) + 1143 / 100
      ≤ 172 / 10 * s ^ 3 := by
    nlinarith [mul_nonneg hs0.le (sq_nonneg (s - 13)), sq_nonneg (s - 14)]
  linarith

/-! ### `Z` below `½`: the U chain -/

set_option maxHeartbeats 1000000 in
-- three ranges and their bounds
/-- **`Z` below `½` from the U chain**: for `x ≥ exp(e^{110})`, `0 < q ≤ ½`, valid window and far
chaos parameters `P`, `P_f` and any `n`,
`E[Z^q] ≤ C_c(q)^q·PF_c(q) + ∑_{4≤k<J₀} b_k + b_far` (`C_c = RMF.uCenAt`, `PF_c = RMF.uPFcAt`,
`b_k = RMF.uWindowBound`, `b_far = RMF.uFarBound`): the bracket of
`RMF.integral_rpow_weightedRademacherSum_le_u_assembly`. -/
theorem integral_rpow_Z_halfY_le_u {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hq0 : 0 < q) (hq : q ≤ 1 / 2) {P : ℕ → WinChaos} (hP : ∀ k, (P k).Valid) {Pf : FarChaos}
    (hPf : Pf.Valid) (n : ℕ) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
        + ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k + uFarBound Pf n q x := by
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  obtain ⟨hy2, -, -, -, -, -⟩ := halfY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hJ4 : 4 ≤ tenJ x := by
    rw [tenJ]
    have h1 : (3 : ℝ) ≤ Real.log (2 / 3 * Real.log (halfY x)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h2 : Real.exp 3 ≤ 21 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_lt_d9
        have h4 : Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
        linarith [show (2.72 : ℝ) ^ 3 ≤ 21 by norm_num]
      have := (halfY_loglog_le hx).2
      linarith
    have : 3 ≤ ⌊Real.log (2 / 3 * Real.log (halfY x))⌋₊ := Nat.le_floor (by exact_mod_cast h1)
    omega
  have hJ4R : (4 : ℝ) ≤ ((tenJ x : ℕ) : ℝ) := by exact_mod_cast hJ4
  have hwv : Real.exp (-((tenJ x : ℕ) : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  -- the central window
  have hb1 : (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t in Set.Icc (-Real.exp (-((tenJ x : ℕ) : ℝ)))
        (Real.exp (-((tenJ x : ℕ) : ℝ))),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x) :=
    integral_rpow_centralRange_le_sharp hX (σ := halfSigma x) (q := q)
      (w := Real.exp (-((tenJ x : ℕ) : ℝ))) hy2 hσ (Real.exp_pos _) hq0.le hq
  -- the windows
  have hb2 : (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t in {t : ℝ | Real.exp (-((tenJ x : ℕ) : ℝ)) < |t|
          ∧ |t| ≤ Real.exp (-((4 : ℕ) : ℝ))},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k := by
    refine le_trans (integral_rpow_mesoRange_le_sum_windows hX hy2 hσ hq0 (by linarith)
      hJ4) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => uWindow_le hX hx hq0.le hq hP hk
  -- the far range
  have hb3 := uFar_le hX hx hq0 hq hPf n
  exact integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := halfSigma x) (q := q)
    (w := Real.exp (-((tenJ x : ℕ) : ℝ))) (v := Real.exp (-((4 : ℕ) : ℝ))) hy2 hσ hq0.le
    (by linarith) hwv hb1 hb2 hb3

/-! ### `Z` near `½`: the cell core -/

set_option maxHeartbeats 1000000 in
-- (PF) and the central window against `τ`
/-- **The central window near `q = ½` against `τ = (Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`**: for `Λ ≥ 6000`,
`q ∈ [q_l, ½)`, `q_l ≥ 0.49`, `a = q(1-2q) ≤ a₁ ≤ 1/8` and `w = (1-2q)Λ ≥ w_l ≥ 1/q_l - 1`,
`C_c(q)^q·PF_c(q) ≤ τ·(1 + w_l)e^{-q_l w_l}·√51·6000^{a₁-1/4}`: the central window of
`RMF.uSmall_half_le`, without the reduction's constant. -/
lemma uCen_pf_le_half {x q ql a₁ wl : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hql : 49 / 100 ≤ ql) (hqlq : ql ≤ q) (hq : q < 1 / 2)
    (ha₁ : q * (1 - 2 * q) ≤ a₁) (ha₁8 : a₁ ≤ 1 / 8)
    (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl) :
    uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
      ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ * Real.log (Real.log x) ^ (-(q / 2))
        * ((1 + wl) * Real.exp (-(ql * wl))
          * (Real.exp (1 / 2 * Real.log 51) * Real.exp ((a₁ - 1 / 4) * Real.log 6000))) := by
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hll := halfY_loglog_ge_sub hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hq49 : 49 / 100 ≤ q := le_trans hql hqlq
  have hq0 : 0 < q := by linarith
  have hq5 : q ≤ 1 / 2 := hq.le
  have hql0 : 0 < ql := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 ≤ a := mul_nonneg hq0.le (by linarith)
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛ0; linarith
  set R := V * Λ ^ (q / 2) with hRdef
  have hR0 : 0 < R := mul_pos hV0 (Real.rpow_pos_of_pos hΛ0 _)
  have hτ : V⁻¹ * Λ ^ (-(q / 2)) = R⁻¹ := by
    rw [hRdef, mul_inv, Real.rpow_neg hΛ0.le]
  rw [hτ]
  -- the (PF) decay `e^{-a(Λ - log Λ)}`
  have hdec : Real.exp (-(a * Real.log (Real.log (halfY x))))
      ≤ Real.exp (-(a * (Λ - Real.log Λ))) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hll ha0))
  have hPFc := le_trans (uPFcAt_le_loglog hx hq0.le hq5) hdec
  have hpf1 := pf_tau_le (Λl := 6000) (qu := 1 / 2) (c := 1) (by norm_num) hΛ hql0 hqlq hq5
    (by norm_num) ha₁ zero_le_one (by linarith) hwl hwl1
  have e1 : (6000 : ℝ) ^ (a₁ + (1 + 1 / 2) * (1 / 2) - 1)
      = Real.exp ((a₁ - 1 / 4) * Real.log 6000) := by
    rw [rpow_eq_exp_mul_log (by norm_num)]; congr 1; ring
  rw [e1] at hpf1
  set D := (1 + wl) * Real.exp (-(ql * wl)) with hDdef
  have hC0 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) := by
    unfold uCenAt
    have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
    have hl : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ (halfY x : ℝ) := Nat.cast_nonneg _
      linarith)
    have h2 : 0 ≤ Real.exp (2 * (1 - q)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1 := by
      have : 0 ≤ 2 * (1 - q)
          * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
          * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2 := by
        have : 0 ≤ 1 - q := by linarith
        positivity
      linarith [Real.add_one_le_exp (2 * (1 - q)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2)]
    have hlogy : 0 < Real.log (halfY x) := by linarith
    positivity
  have hCen : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
      ≤ Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) := by
    have h1 := uCen_le hx hq0.le
    rw [← hΛdef] at h1
    have h51 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ≤ 51 * Λ := by linarith
    calc uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q ≤ (51 * Λ) ^ q :=
          Real.rpow_le_rpow hC0 h51 hq0.le
      _ = (51 : ℝ) ^ q * Λ ^ (1 * q) := by rw [Real.mul_rpow (by norm_num) hΛ0.le, one_mul]
      _ ≤ (51 : ℝ) ^ (1 / 2 : ℝ) * Λ ^ (1 * q) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq5) (Real.rpow_nonneg hΛ0.le _)
      _ = Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  have hPFc0 : 0 ≤ uPFcAt q (halfSigma x) (halfY x) := by
    unfold uPFcAt
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)
  refine le_inv_mul_of_mul_le hR0 ?_
  have h1 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
      ≤ Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ))) :=
    mul_le_mul hCen hPFc hPFc0 (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hΛ0.le _))
  have h3 := mul_le_mul_of_nonneg_left hpf1 (Real.exp_pos (1 / 2 * Real.log 51)).le
  calc uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x) * R
      ≤ Real.exp (1 / 2 * Real.log 51) * Λ ^ (1 * q) * Real.exp (-(a * (Λ - Real.log Λ))) * R :=
        mul_le_mul_of_nonneg_right h1 hR0.le
    _ = Real.exp (1 / 2 * Real.log 51)
        * (Real.exp (-(a * (Λ - Real.log Λ))) * Λ ^ (1 * q) * R) := by ring
    _ ≤ Real.exp (1 / 2 * Real.log 51) * (D * Real.exp ((a₁ - 1 / 4) * Real.log 6000)) := h3
    _ = D * (Real.exp (1 / 2 * Real.log 51) * Real.exp ((a₁ - 1 / 4) * Real.log 6000)) := by
        ring

set_option maxHeartbeats 16000000 in
-- the U chain's bracket and its pieces
/-- **`Z`'s cell near `q = ½` past `Λ = 6000`** (the twin of `RMF.u_half_core` for `Z`): for
`q ∈ [q_l, ½)`, `q_l ≥ 0.49`, `w = (1 - 2q)Λ ≥ w_l ≥ 1/q_l - 1`, `a = q(1-2q) ≤ a₁ ≤ 1/8`, the
windows' parameters of `RMF.uLow_half_le` and `RMF.uHigh_groups_le`, the bounds `E_t`, `V_b`,
`H_b`, `T_b`, `E_0` of `RMF.u_half_core`, and the certificate `hfin` without the reduction's
constant, `E[Z^q] ≤ K(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, `Z` at `(halfY x, halfSigma x)`. -/
theorem z_half_core {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql a₁ wl Vb Et Hb Tb E0b K : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hql : 49 / 100 ≤ ql) (hqlq : ql ≤ q) (hq : q < 1 / 2)
    (hwl0 : 0 < wl) (hwl : wl ≤ (1 - 2 * q) * Real.log (Real.log x)) (hwl1 : 1 / ql - 1 ≤ wl)
    (ha₁ : q * (1 - 2 * q) ≤ a₁) (ha₁8 : a₁ ≤ 1 / 8)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} (hv₁ : c₁.Valid) (hv₂ : c₂.Valid)
    (hv₃ : c₃.Valid) (hv₄ : c₄.Valid) (hv₅ : c₅.Valid) (hv₆ : c₆.Valid) (hv₇ : c₇.Valid)
    (hN₁ : c₁.N ≤ 2980) (hN₂ : c₂.N ≤ 2980) (hN₃ : c₃.N ≤ 2980) (hN₄ : c₄.N ≤ 2980)
    (hN₅ : c₅.N ≤ 2980) (hN₆ : c₆.N ≤ 2980) (hN₇ : c₇.N ≤ 2980)
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ G₁ G₂ G₃ G₄ G₅ G₆ G₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇ bH : ℝ}
    (hA₁ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      c₁.const E₀ q K ≤ A₁)
    (hA₂ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      c₂.const E₀ q K ≤ A₂)
    (hA₃ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      c₃.const E₀ q K ≤ A₃)
    (hA₄ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      c₄.const E₀ q K ≤ A₄)
    (hA₅ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      c₅.const E₀ q K ≤ A₅)
    (hA₆ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      c₆.const E₀ q K ≤ A₆)
    (hA₇ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      c₇.const E₀ q K ≤ A₇)
    (hG₁ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 4 y ^ (1 / 2 : ℝ) ≤ G₁)
    (hG₂ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 5 y ^ (1 / 2 : ℝ) ≤ G₂)
    (hG₃ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 6 y ^ (1 / 2 : ℝ) ≤ G₃)
    (hG₄ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 7 y ^ (1 / 2 : ℝ) ≤ G₄)
    (hG₅ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 31 y ^ (1 / 2 : ℝ) ≤ G₅)
    (hG₆ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 61 y ^ (1 / 2 : ℝ) ≤ G₆)
    (hG₇ : ∀ y : ℕ, 22000 ≤ Real.log y →
      thetaWindowConstQ (3 / 2) (49 / 100) 97 y ^ (1 / 2 : ℝ) ≤ G₇)
    (hb₁ : G₁ * A₁ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₁)
    (hb₂ : G₂ * A₂ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₂)
    (hb₃ : G₃ * A₃ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₃)
    (hb₄ : G₄ * A₄ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₄)
    (hb₅ : G₅ * A₅ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₅)
    (hb₆ : G₆ * A₆ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10075 / 10000) ≤ b₆)
    (hb₇ : G₇ * A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (10763 / 10000) ≤ b₇)
    (h12 : b₂ ≤ b₁) (h23 : b₃ ≤ b₂) (h34 : b₄ ≤ b₃) (h45 : b₅ ≤ b₄) (h56 : b₆ ≤ b₅)
    (h67 : b₇ ≤ b₆) (hN : (c₇.N : ℝ) ≤ (A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 4)
    (hbH : G₇ * A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ bH)
    (hEt : Et ≤ Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) / 4)))
    (hVb : (Real.log (Real.log x))⁻¹ + (1 - 2 * q) ≤ Vb)
    (hHb : ∑ g ∈ Finset.range 8, halfRho (g + 1)
        * ((1 + (1 - 2 * q) * Real.log (Real.log x))
          * ((Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo g))
            - Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigHi (g + 1))))
            / (q * ((1 - 2 * q) * Real.log (Real.log x))))) ≤ Hb)
    (hTb : (1 + (1 - 2 * q) * Real.log (Real.log x))
        * Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo 8)) ≤ Tb)
    (hE0 : Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo 0)) ≤ E0b)
    (hfin : (1 + wl) * Real.exp (-(ql * wl))
        * (Real.exp (1 / 2 * Real.log 51) * Real.exp ((a₁ - 1 / 4) * Real.log 6000))
      + Vb * Real.exp (3 / 4 * Real.log 880)
      + (1 / ql + 1 / (ql * wl) + Vb * (1 / 2 + a₁ / 10))
        * (b₁ - (b₁ - b₂) * Real.exp (-(5 * a₁)) - (b₂ - b₃) * Real.exp (-(6 * a₁))
          - (b₃ - b₄) * Real.exp (-(7 * a₁)) - (b₄ - b₅) * Real.exp (-(31 * a₁))
          - (b₅ - b₆) * Real.exp (-(61 * a₁)) - (b₆ - b₇) * Real.exp (-(97 * a₁)) - b₇ * Et)
      + bH * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000)) ≤ K) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ K * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hL1, hL2⟩ := halfLpp_bounds hΛ
  have hq49 : 49 / 100 ≤ q := le_trans hql hqlq
  have hq0 : 0 < q := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  have hql0 : 0 < ql := by linarith
  have hΛ0' : 0 < Real.log (Real.log x) := by linarith
  have hLpp0 : 0 ≤ halfLpp x := by linarith
  have hA₇0 : 0 ≤ A₇ := le_trans (winChaos_const_zero_nonneg hv₇ q)
    (hA₇ 0 le_rfl (by norm_num) 1 zero_le_one (Real.one_le_exp (by norm_num)))
  have hG₇0 : 0 ≤ G₇ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by norm_num) 97 (halfY x))) _)
    (hG₇ _ hly)
  -- the pieces, before abbreviating
  have hP7 : ∀ k, 97 ≤ k → uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ k = c₇ := fun k hk => uGroups_of_ge hk
  have hPv := uGroups_valid hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇
  have hZb := integral_rpow_Z_halfY_le_u hX hx hq0 hq.le hPv uFarP_valid
    (⌈Real.log (Real.log (Real.log x))⌉₊ + 4)
  have hcen := uCen_pf_le_half hx hΛ hql hqlq hq ha₁ ha₁8 hwl hwl1
  have hfarb := uFarBound_uFarP_le hx (by linarith) hq0 hq.le
  have hK4 : (⌊Real.log (Real.log x) / 4⌋₊ : ℝ) ≤ Real.log (Real.log x) / 4 :=
    Nat.floor_le (by linarith)
  have hEt' : Et ≤ Real.exp (-(q * (1 - 2 * q) * ⌊Real.log (Real.log x) / 4⌋₊)) := by
    refine le_trans hEt (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left hK4 (mul_pos hq0 hv0).le
    linarith
  have hlow := uLow_half_le (ql := 49 / 100) (qu := 1 / 2) hx (by linarith) (by norm_num) hq49
    hq.le (by norm_num) hq ha₁ hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇ hN₁ hN₂ hN₃ hN₄ hN₅ hN₆ hN₇ hA₁ hA₂
    hA₃ hA₄ hA₅ hA₆ hA₇ hG₁ hG₂ hG₃ hG₄ hG₅ hG₆ hG₇ hb₁ hb₂ hb₃ hb₄ hb₅ hb₆ hb₇ h12 h23 h34 h45
    h56 h67 hEt'
  have e4 : Real.exp (-(4 * ((1 / 2 : ℝ) * (1 - 2 * (1 / 2))))) = 1 := by norm_num
  rw [e4, mul_one] at hlow
  have hhigh := uHigh_groups_le (ql := 49 / 100) (qu := 1 / 2) hx hΛ hq0 hq hq49 hq.le le_rfl
    hv₇ hP7 hA₇ hG₇ hN
  have htail := uHigh_tail_le (ql := 49 / 100) (qu := 1 / 2) hx hΛ hq0 hq hq49 hq.le le_rfl
    hv₇ hP7 hA₇ hG₇ hN
  -- the windows' ranges
  have hK0 : halfKb x 0 = ⌊Real.log (Real.log x) / 4⌋₊ := by unfold halfKb; rw [if_pos rfl]
  have hmono := halfKb_mono hΛ
  have hJ := floor_halfLpp_lt_tenJ hx hΛ
  obtain ⟨-, hk8L⟩ := halfKb_le hΛ (g := 8) (by norm_num)
  have h4K : 4 ≤ halfKb x 0 := by rw [hK0]; exact Nat.le_floor (by push_cast; linarith)
  have hsplit : ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
      = ∑ k ∈ Finset.Ico 4 ⌊Real.log (Real.log x) / 4⌋₊,
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
        + ∑ k ∈ Finset.Ico (halfKb x 0) (halfKb x 8),
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
        + ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x),
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k := by
    rw [← hK0, Finset.sum_Ico_consecutive _ h4K (hmono (Nat.zero_le 8)),
      Finset.sum_Ico_consecutive _ (le_trans h4K (hmono (Nat.zero_le 8))) (by omega)]
  -- the high groups against `τ⁻¹`, term by term
  have hterm : ∀ g, g < 8 →
      (1 + (1 - 2 * q) * Real.log (Real.log x)) / (q * ((1 - 2 * q) * Real.log (Real.log x)))
        * (Real.exp (-(q * (1 - 2 * q) * halfKb x g))
          - Real.exp (-(q * (1 - 2 * q) * halfKb x (g + 1))))
      ≤ (1 + (1 - 2 * q) * Real.log (Real.log x))
        * ((Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigLo g))
          - Real.exp (-(q * ((1 - 2 * q) * Real.log (Real.log x)) * halfSigHi (g + 1))))
          / (q * ((1 - 2 * q) * Real.log (Real.log x)))) := fun g _ =>
    high_term_le hΛ0' hq0 hq (halfSigLo_le hΛ g) (le_halfSigHi hΛ (by omega))
  have hekb : ∀ g, q * (1 - 2 * q) * (halfKb x g : ℝ)
      = q * ((1 - 2 * q) * Real.log (Real.log x)) * ((halfKb x g : ℝ) / Real.log (Real.log x)) :=
    fun g => by field_simp
  have hwpos : 0 ≤ q * ((1 - 2 * q) * Real.log (Real.log x)) :=
    (mul_pos hq0 (mul_pos hv0 hΛ0')).le
  have hE0' : Real.exp (-(q * (1 - 2 * q) * halfKb x 0)) ≤ E0b := by
    refine le_trans (Real.exp_le_exp.2 ?_) hE0
    rw [hekb 0]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (halfSigLo_le hΛ 0) hwpos)
  have hTb' : (1 + (1 - 2 * q) * Real.log (Real.log x))
      * Real.exp (-(q * (1 - 2 * q) * halfKb x 8)) ≤ Tb := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (add_nonneg zero_le_one (mul_pos hv0 hΛ0').le)) hTb
    rw [hekb 8]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (halfSigLo_le hΛ 8) hwpos)
  have hgeo := geom_half_le_of hΛ0' hql0 hqlq hq hwl0 hwl ha₁ hVb
  have hQ := geom_half_le hΛ0' hq0 hq
  have htf := halfTail_factor_le (L := halfLpp x) hΛ hq (by linarith) hL2 (halfTheta_pos 8).le
  have hρ8 := halfRho_eight_le
  have hT8 := halfT8_le
  -- abbreviations
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := hΛ0'
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 < a := mul_pos hq0 hv0
  set w := (1 - 2 * q) * Λ with hwdef
  have hw0 : 0 < w := mul_pos hv0 hΛ0
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛ0; linarith
  have hΛq0 : 0 < Λ ^ (-(q / 2)) := Real.rpow_pos_of_pos hΛ0 _
  set τ := V⁻¹ * Λ ^ (-(q / 2)) with hτdef
  have hτ0 : 0 < τ := mul_pos (inv_pos.2 hV0) hΛq0
  set P := uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ with hPdef
  set S1 := ∑ k ∈ Finset.Ico 4 ⌊Λ / 4⌋₊, uWindowBound P q x k with hS1def
  set S2 := ∑ k ∈ Finset.Ico (halfKb x 0) (halfKb x 8), uWindowBound P q x k with hS2def
  set S3 := ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x), uWindowBound P q x k with hS3def
  set Sw := ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k with hSwdef
  set C := (3 / 2 : ℝ) ^ (-a) with hCdef
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  have hC1 : C ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  set b := G₇ * A₇ * (1 - 1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) with hbdef
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg hG₇0 hA₇0) (Real.rpow_nonneg (by norm_num) _)
  have hd : 0 < 1 - Real.exp (-a) := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hSnn : ∀ s t : ℕ, 0 ≤ ∑ k ∈ Finset.Ico s t, uWindowBound P q x k := fun s t =>
    Finset.sum_nonneg fun k _ => uWindowBound_nonneg hPv hq0.le (by linarith) k
  -- the low windows
  set Geo := 1 / ql + 1 / (ql * wl) + Vb * (1 / 2 + a₁ / 10) with hGeo
  set Abel := b₁ - (b₁ - b₂) * Real.exp (-(5 * a₁)) - (b₂ - b₃) * Real.exp (-(6 * a₁))
    - (b₃ - b₄) * Real.exp (-(7 * a₁)) - (b₄ - b₅) * Real.exp (-(31 * a₁))
    - (b₅ - b₆) * Real.exp (-(61 * a₁)) - (b₆ - b₇) * Real.exp (-(97 * a₁)) - b₇ * Et
    with hAbel
  have hS1 : S1 ≤ τ * (Geo * Abel) := by
    have hS10 : 0 ≤ S1 := hSnn _ _
    have hAb0 : 0 ≤ Abel := by
      have h1 : 0 ≤ (1 - Real.exp (-a)) * S1 := mul_nonneg hd.le hS10
      have h2 : 0 < C * Λ ^ (-(q / 2)) := mul_pos hC0 hΛq0
      by_contra hneg
      have := mul_neg_of_pos_of_neg h2 (lt_of_not_ge hneg)
      linarith
    have h1 : S1 ≤ C * Λ ^ (-(q / 2)) * Abel / (1 - Real.exp (-a)) := by
      rw [le_div_iff₀ hd]; linarith
    have e2 : C * Λ ^ (-(q / 2)) * Abel / (1 - Real.exp (-a))
        = τ * (C * (V / (1 - Real.exp (-a))) * Abel) := by
      rw [hτdef]; field_simp
    rw [e2] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hτ0.le)
    have hVd0 : 0 ≤ V / (1 - Real.exp (-a)) := div_nonneg hV0.le hd.le
    calc C * (V / (1 - Real.exp (-a))) * Abel ≤ 1 * Geo * Abel :=
          mul_le_mul_of_nonneg_right (mul_le_mul hC1 hgeo hVd0 zero_le_one) hAb0
      _ = Geo * Abel := by ring
  -- the high groups
  set Sig := ∑ g ∈ Finset.range 8, halfRho (g + 1)
    * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1)))) with hSigdef
  have hΔ0 : ∀ g, 0 ≤ Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))) :=
    fun g => sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hmono (Nat.le_succ g)) ha0.le)))
  have hSg0 : 0 ≤ Sig :=
    Finset.sum_nonneg fun g _ => mul_nonneg (halfRho_nonneg _) (hΔ0 g)
  have hSg1 : Sig ≤ 1497 / 500 * E0b := by
    have h1 : Sig ≤ ∑ g ∈ Finset.range 8, halfRho 8
        * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1)))) :=
      Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_right
        (halfRho_mono (by have := Finset.mem_range.1 hg; omega)) (hΔ0 g)
    rw [← Finset.mul_sum] at h1
    have htel := Finset.sum_range_sub' (fun g : ℕ => Real.exp (-(a * (halfKb x g : ℝ)))) 8
    rw [htel] at h1
    have h8 : 0 ≤ Real.exp (-(a * halfKb x 8)) := (Real.exp_pos _).le
    have hρ0 := halfRho_nonneg 8
    have h2 : halfRho 8 * (Real.exp (-(a * halfKb x 0)) - Real.exp (-(a * halfKb x 8)))
        ≤ 1497 / 500 * E0b :=
      mul_le_mul hρ8 (by linarith) (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hmono (Nat.zero_le 8)) ha0.le))))
        (by norm_num)
    linarith
  have hS2 : S2 ≤ τ * (b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b)) := by
    have hsum : ∑ g ∈ Finset.range 8, C * Λ ^ (-(q / 2)) * b * halfRho (g + 1)
        * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))))
        = C * Λ ^ (-(q / 2)) * b * Sig := by
      rw [hSigdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    rw [hsum] at hhigh
    have h1 : S2 ≤ C * Λ ^ (-(q / 2)) * b * Sig / (1 - Real.exp (-a)) := by
      rw [le_div_iff₀ hd]; linarith
    have e2 : C * Λ ^ (-(q / 2)) * b * Sig / (1 - Real.exp (-a))
        = τ * (C * b * (V / (1 - Real.exp (-a)) * Sig)) := by
      rw [hτdef]; field_simp
    rw [e2] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hτ0.le)
    have hin : V / (1 - Real.exp (-a)) * Sig
        ≤ Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b := by
      have hQS := mul_le_mul_of_nonneg_right hQ hSg0
      have eQ : (1 + w) / (q * w) * Sig = ∑ g ∈ Finset.range 8, halfRho (g + 1)
          * ((1 + w) / (q * w)
            * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))))) := by
        rw [hSigdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by ring
      have hA : ∑ g ∈ Finset.range 8, halfRho (g + 1)
          * ((1 + w) / (q * w)
            * (Real.exp (-(a * halfKb x g)) - Real.exp (-(a * halfKb x (g + 1))))) ≤ Hb :=
        le_trans (Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left
          (hterm g (Finset.mem_range.1 hg)) (halfRho_nonneg _)) hHb
      have hB : V * (1 / 2 + a / 10) * Sig ≤ Vb * (1 / 2 + a₁ / 10) * (1497 / 500 * E0b) :=
        mul_le_mul (mul_le_mul hVb (by linarith) (by linarith) (by linarith)) hSg1 hSg0
          (mul_nonneg (le_trans hV0.le hVb) (by have := le_trans ha0.le ha₁; linarith))
      have e5 : ((1 + w) / (q * w) + V * (1 / 2 + a / 10)) * Sig
          = (1 + w) / (q * w) * Sig + V * (1 / 2 + a / 10) * Sig := by ring
      rw [e5] at hQS
      linarith
    have hin0 : 0 ≤ V / (1 - Real.exp (-a)) * Sig := mul_nonneg (div_nonneg hV0.le hd.le) hSg0
    calc C * b * (V / (1 - Real.exp (-a)) * Sig) ≤ 1 * b * (V / (1 - Real.exp (-a)) * Sig) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hb0) hin0
      _ ≤ 1 * b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b) :=
          mul_le_mul_of_nonneg_left hin (by linarith)
      _ = _ := by ring
  -- the tail
  have hS3 : S3 ≤ τ * (b * Tb * (797 / 10000)) := by
    have e3 : C * Λ ^ (-(q / 2)) * b * Real.exp (-(a * halfKb x 8)) * Λ ^ (1 / 4 : ℝ)
        * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11))
        = τ * (C * b * Real.exp (-(a * halfKb x 8)) * (V * Λ ^ (1 / 4 : ℝ)
          * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11)))) := by
      rw [hτdef]; field_simp
    rw [e3] at htail
    refine le_trans htail (mul_le_mul_of_nonneg_left ?_ hτ0.le)
    have hE80 : 0 ≤ Real.exp (-(a * halfKb x 8)) := (Real.exp_pos _).le
    have hT80 : 0 ≤ 4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
        + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)) := by
      have h1 : 0 ≤ (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ) :=
        Real.rpow_nonneg (by have := halfTheta_pos 8; linarith) _
      have h2 : 0 ≤ Real.log 6000 := Real.log_nonneg (by norm_num)
      have h3 : 0 ≤ (6000 : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
      exact add_nonneg (mul_nonneg (by norm_num) h1) (mul_nonneg (by linarith) h3)
    have hTb0 : 0 ≤ Tb := le_trans (mul_nonneg (by linarith) hE80) hTb'
    calc C * b * Real.exp (-(a * halfKb x 8)) * (V * Λ ^ (1 / 4 : ℝ)
          * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11)))
        ≤ 1 * b * Real.exp (-(a * halfKb x 8)) * ((1 + w)
          * (4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
            + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hb0) hE80) htf
            (mul_nonneg (mul_nonneg hV0.le (Real.rpow_nonneg hΛ0.le _)) (by
              have h1 : 0 ≤ (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) :=
                Real.rpow_nonneg (add_nonneg (mul_nonneg hLpp0 (halfTheta_pos 8).le)
                  zero_le_one) _
              have h2 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
              exact add_nonneg (mul_nonneg (by norm_num) h1) (by linarith)))
            (mul_nonneg (mul_nonneg zero_le_one hb0) hE80)
      _ = b * ((1 + w) * Real.exp (-(a * halfKb x 8)))
          * (4 / 3 * (halfTheta 8 + 1 / 6000) ^ (3 / 4 : ℝ)
            + (Real.log 6000 + 11) * (6000 : ℝ) ^ (-(3 / 4 : ℝ))) := by ring
      _ ≤ b * Tb * (797 / 10000) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTb' hb0) hT8 hT80 (mul_nonneg hb0 hTb0)
  -- the windows together
  have hSw : Sw ≤ τ * (Geo * Abel
      + bH * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000))) := by
    have hsp : Sw = S1 + S2 + S3 := hsplit
    have hB0 : 0 ≤ Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000) := by
      have hHb0 : 0 ≤ Hb := le_trans (Finset.sum_nonneg fun g _ => mul_nonneg (halfRho_nonneg _)
        (mul_nonneg (by linarith) (div_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg
          (mul_le_mul_of_nonneg_left (halfSigLo_le_hi g) (mul_pos hq0 hw0).le))))
          (mul_pos hq0 hw0).le))) hHb
      have hE00 : 0 ≤ E0b := le_trans (Real.exp_pos _).le hE0
      have hTb0 : 0 ≤ Tb := le_trans (mul_nonneg (by linarith) (Real.exp_pos _).le) hTb
      have hVb0 : 0 ≤ Vb := le_trans hV0.le hVb
      have ha₁0 : 0 ≤ a₁ := le_trans ha0.le ha₁
      have t1 : 0 ≤ Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b :=
        mul_nonneg (mul_nonneg (mul_nonneg hVb0 (by linarith)) (by norm_num)) hE00
      have t2 : 0 ≤ Tb * (797 / 10000) := mul_nonneg hTb0 (by norm_num)
      linarith
    have hbb : b * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b) + b * Tb * (797 / 10000)
        ≤ bH * (Hb + Vb * (1 / 2 + a₁ / 10) * (1497 / 500) * E0b + Tb * (797 / 10000)) := by
      have := mul_le_mul_of_nonneg_right hbH hB0
      linarith
    rw [hsp]
    have := mul_le_mul_of_nonneg_left hbb hτ0.le
    linarith [hS1, hS2, hS3]
  -- the far range
  have hR_F : uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x
      ≤ τ * (Vb * Real.exp (3 / 4 * Real.log 880)) := by
    have h880 : (880 : ℝ) ^ (3 / 2 * q) ≤ Real.exp (3 / 4 * Real.log 880) := by
      rw [← rpow_eq_exp_mul_log (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h1 : Λ ^ (-(q / 2)) = τ * V := by rw [hτdef]; field_simp
    have hVb0 : 0 ≤ Vb := le_trans hV0.le hVb
    calc uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x
        ≤ Λ ^ (-(q / 2)) * (880 : ℝ) ^ (3 / 2 * q) := hfarb
      _ = τ * (V * (880 : ℝ) ^ (3 / 2 * q)) := by rw [h1]; ring
      _ ≤ τ * (Vb * Real.exp (3 / 4 * Real.log 880)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hVb h880 (Real.rpow_nonneg (by norm_num) _) hVb0) hτ0.le
  -- together
  calc _ ≤ _ := hZb
    _ ≤ τ * K := by
        have := mul_le_mul_of_nonneg_left hfin hτ0.le
        linarith [hcen, hSw, hR_F]
    _ = K * V⁻¹ * Λ ^ (-(q / 2)) := by rw [hτdef]; ring

end RMF
