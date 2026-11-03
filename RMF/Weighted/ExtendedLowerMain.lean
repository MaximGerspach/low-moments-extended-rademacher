/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedEulerRatio
import RMF.Weighted.ExtendedLowerParseval
import RMF.Weighted.LowerFixedQ

/-!
# The extended lower bound: the main term

The main term of
`RMF.exists_le_integral_rpow_extendedSum_euler` is the window `∫_{|t|<1} |F^e(½+σ+it)|² dt` of the
extended Euler product.  On `|t| ≤ ½` the Euler-product ratio is bounded below
(`RMF.exists_le_prod_inv_normSq_of_abs_le_half`), so the window dominates `c₀` times Harper's
window `log x · chaosShift` of the Rademacher Euler product
(`RMF.exists_rpow_log_mul_integral_chaosShift_le_extended`), whose `q`-th moment is bounded below
by `RMF.exists_le_integral_rpow_chaosShift_rademacher_eventually`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The line `½ + σ + it`, written both ways. -/
lemma half_add_line_eq (σ t : ℝ) :
    (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
  push_cast
  ring

/-- **The window of `F^e` has integrable `q`-th powers**: it is almost surely the window of the
closed-form Euler product of the prime values, which is measurable, and it is bounded by
`2·eulerBound²`. -/
lemma integrable_rpow_setIntegral_Ioo_extended {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (N : ℕ) {σ q : ℝ} (hσ : 1 / 2 ≤ σ) (hq : 0 ≤ q) :
    Integrable (fun ω => (∫ t in Set.Ioo (-1 : ℝ) 1,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
          ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q) μ := by
  haveI := hX.isProbabilityMeasure
  have hs : ∀ t : ℝ, 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := fun t => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith
  have hX' : Measurable fun ω => fun p : Nat.Primes => X (p : ℕ) ω :=
    measurable_pi_lambda _ fun p => hX.measurable (p : ℕ) p.2
  have hjoint : StronglyMeasurable fun z : Ω × ℝ =>
      ‖eulerClosed (fun p : Nat.Primes => X (p : ℕ) z.1) N
        ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 := by
    have h := (measurable_eulerClosed_uncurry σ N).comp (hX'.prodMap measurable_id)
    exact (h.norm.pow_const 2).stronglyMeasurable
  have hW := hjoint.integral_prod_right' (ν := volume.restrict (Set.Ioo (-1 : ℝ) 1))
  have hae := ae_forall_norm_le_one hX norm_le_one_rademacherLaw N
  have hmeasW : AEStronglyMeasurable (fun ω => ∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) μ := by
    refine hW.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ω hω
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [eulerClosed_eq_randomEulerProduct (hs t) hω]
  have hmeas : AEStronglyMeasurable (fun ω => (∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q) μ :=
    (Real.continuous_rpow_const hq).comp_aestronglyMeasurable hmeasW
  refine (memLp_top_of_bound hmeas ((2 * eulerBound N ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hae] with ω hω
  have hbd : ∀ t : ℝ, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
      ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound N := fun t =>
    norm_randomEulerProduct_le hω (by simpa using hσ)
  have hint := integrableOn_windowOf σ (measurable_randomEulerProduct_compMult_line σ hσ hω)
    hbd (-1) 1
  have hW0 : 0 ≤ ∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun t _ => sq_nonneg _
  have hle : (∫ t in Set.Ioo (-1 : ℝ) 1,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
        ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ≤ 2 * eulerBound N ^ 2 := by
    calc (∫ t in Set.Ioo (-1 : ℝ) 1,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) N
            ((σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2)
        ≤ ∫ _t in Set.Ioo (-1 : ℝ) 1, eulerBound N ^ 2 :=
          setIntegral_mono_on (hint.mono_set Set.Ioo_subset_Ioc_self)
            (integrableOn_const (by simp)) measurableSet_Ioo fun t _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2
      _ = 2 * eulerBound N ^ 2 := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioo]
          norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hW0 q)]
  exact Real.rpow_le_rpow hW0 hle hq

/-- **The main term against Harper's window.**  There is `c₀ > 0`, independent of `X`, `x`, `σ`
and `q`, such that for every Rademacher `X`, `x > 1`, `0 < σ ≤ 1` and `q ≥ 0`,
`c₀^q (log x)^q E[chaosShift(σ)^q] ≤ E[(∫_{|t|<1} |F^e(½+σ+it)|² dt)^q]`:
on `|t| ≤ ½`, `|F^e|² = |F|²·∏|1 - (p^{-s})²|^{-2} ≥ c₀|F|²`
(`RMF.ae_normSq_randomEulerProduct_compMult_eq`, `RMF.exists_le_prod_inv_normSq_of_abs_le_half`). -/
theorem exists_rpow_log_mul_integral_chaosShift_le_extended :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x σ q : ℝ, 1 < x → 0 < σ → σ ≤ 1 → 0 ≤ q →
        c₀ ^ q * Real.log x ^ q
            * ∫ ω, chaosShift (fun ω => squarefreeExtension fun p => X p ω) x σ ω ^ q ∂μ
          ≤ ∫ ω, (∫ t in Set.Ioo (-1 : ℝ) 1,
              ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ^ q ∂μ := by
  obtain ⟨c₀, hc₀, Hc⟩ := exists_le_prod_inv_normSq_of_abs_le_half
  refine ⟨c₀, hc₀, fun X μ hX x σ q hx hσ0 hσ1 hq => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hlog0 : 0 < Real.log x := Real.log_pos hx
  have hσh : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  have hsre : ∀ t : ℝ, 0 < ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re := fun t => by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    linarith
  rw [← Real.mul_rpow hc₀.le hlog0.le, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    (integrable_rpow_setIntegral_Ioo_extended hX (⌊x⌋₊ + 1) hσh hq) ?_
  · exact mul_nonneg (Real.rpow_nonneg (mul_nonneg hc₀.le hlog0.le) _)
      (Real.rpow_nonneg (chaosShift_nonnegOf (inv_nonneg.2 hlog0.le) ω) _)
  filter_upwards [ae_normSq_randomEulerProduct_compMult_eq hX (⌊x⌋₊ + 1),
    ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊x⌋₊ + 1)] with ω hratio hω
  have h0 := chaosShift_nonnegOf
    (F := fun ω => squarefreeExtension fun p => X p ω) (δ := σ) (inv_nonneg.2 hlog0.le) ω
  rw [← Real.mul_rpow (mul_nonneg hc₀.le hlog0.le) h0]
  refine Real.rpow_le_rpow (mul_nonneg (mul_nonneg hc₀.le hlog0.le) h0) ?_ hq
  -- `log x · chaosShift` is the window `[-½, ½]` of `|F|²`
  have hwin : Real.log x * chaosShift (fun ω => squarefreeExtension fun p => X p ω) x σ ω
      = ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2), ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := by
    rw [chaosShift, ← mul_assoc, mul_inv_cancel₀ hlog0.ne', one_mul,
      intervalIntegral.integral_of_le (by norm_num)]
  rw [mul_assoc, hwin]
  -- the ratio, on the window
  have hbdF : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
      (⌊x⌋₊ + 1) (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound (⌊x⌋₊ + 1) :=
    fun t => norm_randomEulerProduct_sqfree_le hω
      (by rw [show ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I = shiftLine σ t from rfl,
        re_shiftLine]; linarith)
  have hintF := integrableOn_windowOf (σ := 1 / 2 + σ)
    (measurable_randomEulerProduct_sqfree_line (X := X) (N := ⌊x⌋₊ + 1) (ω := ω) (1 / 2 + σ))
    hbdF (-(1 : ℝ) / 2) (1 / 2)
  have hbdE : ∀ t : ℝ, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω)
      (⌊x⌋₊ + 1) (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound (⌊x⌋₊ + 1) :=
    fun t => norm_randomEulerProduct_le hω (by simpa using hσh)
  have hintE := integrableOn_windowOf (σ := 1 / 2 + σ)
    (measurable_randomEulerProduct_compMult_line (1 / 2 + σ) hσh hω) hbdE (-1) 1
  have hpt : ∀ t ∈ Set.Ioc (-(1 : ℝ) / 2) (1 / 2),
      c₀ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        ≤ ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := by
    intro t ht
    have htabs : |t| ≤ 1 / 2 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    rw [half_add_line_eq, hratio _ (hsre t)]
    have hR := Hc (⌊x⌋₊ + 1) σ t hσ0.le htabs
    have hF0 : 0 ≤ ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (⌊x⌋₊ + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := sq_nonneg _
    nlinarith
  calc c₀ * ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2), ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
      = ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2), c₀ * ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := (integral_const_mul _ _).symm
    _ ≤ ∫ t in Set.Ioc (-(1 : ℝ) / 2) (1 / 2), ‖randomEulerProduct
          (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 :=
        setIntegral_mono_on (hintF.const_mul c₀)
          (hintE.mono_set (Set.Ioc_subset_Ioc (by norm_num) (by norm_num)))
          measurableSet_Ioc hpt
    _ ≤ ∫ t in Set.Ioo (-1 : ℝ) 1, ‖randomEulerProduct
          (fun ω => compMultExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 :=
        setIntegral_mono_set (hintE.mono_set Set.Ioo_subset_Ioc_self)
          (Filter.Eventually.of_forall fun t => sq_nonneg _)
          (Filter.Eventually.of_forall fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)

end RMF
