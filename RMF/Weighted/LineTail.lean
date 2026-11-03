/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.EulerLine
import RMF.NumberTheory.CosinePrimeSum

/-!
# The far range of the line integral

`Z = (log y)⁻¹ ∫_ℝ |F_y(½+σ+it)|²|σ+it|^{-2} dt` is a multiplicative chaos, and the chaos
estimates are what control it.  But the **far range** needs none of them: there the weight
`|σ+it|^{-2} ≤ t^{-2}` is already small, so Hölder against the *second* moment suffices.

Three facts:

* Hölder (Lyapunov) on a probability space: `E[U^q] ≤ (E U)^q` for `0 < q ≤ 1`;
* the Rademacher second moment **does not depend on the height** — for a centred `±1` variable
  `E|1 + Xw|² = 1 + ‖w‖²`, so
  `E|F_y(½+σ+it)|² = ∏_{p≤y} (1 + p^{-1-2σ}) ≤ ∏_{p≤y}(1 + 1/p) ≪ log y`
  (`RMF.exists_prod_one_add_le_rpow_log`);
* `∫_{|t|>T} dt/(σ² + t²) ≤ ∫_{|t|>T} dt/t² = 2/T`.

Together `E[Z_{|t|>T}^q] ≪ T^{-q}`.  `T` is left a **parameter**: the application takes
`T = (log log x)²`, where `T^{-q} = (log log x)^{-2q}` beats the `(log log x)^{-q/2}` the far range
must deliver, but nothing here depends on that choice.

This is what lets the expensive route — Hölder up to `2/3`, subadditivity over unit intervals
(`∑ N^{-2q}` diverges for `q ≤ ½`, `∑ N^{-4/3}` does not), then Harper's Key Proposition 3
(Harper, *Moments of random multiplicative functions, I*, arXiv:1703.06654) — be confined to the
**bounded** range `1 < |t| ≤ (log log x)²`.

## How the three fit together

The `ω`- and `t`-integrals are exchanged by **Tonelli in its Bochner form**
(`MeasureTheory.integral_integral_swap`), and the product integrability it needs is read off the
slices: at every fixed height the `ω`-integral is `(E|F_y|²)·|σ+it|^{-2}`, a *constant* multiple of
the weight, so `RMF.IsRademacherRMF.integral_norm_randomEulerProduct_sq'` supplies both slice
conditions of `MeasureTheory.integrable_prod_iff'` at once.  That the constant does not move with
`t` is also what makes the same integrability give `Integrable Z` for Jensen, through
`MeasureTheory.Integrable.integral_prod_left`.

The joint measurability of `(ω, t) ↦ |F_y(½+σ+it)(ω)/(σ+it)|²` is
`RMF.measurable_randomEulerProduct_sqfree_uncurry` (`RMF/Reduction/RademacherSteps.lean`), stated
on a vertical line; `RMF.integrable_rpow_eulerProductLine` takes its measurability on the Parseval
(`u`-integral) side instead.
-/

open Finset MeasureTheory

namespace RMF

/-- **The tail of the Cauchy weight**, `∫_{|t|>T} dt/(σ²+t²) ≤ 2/T` for any real `σ` and `T > 0`.

The weight is at most `t^{-2}` on `|t| > T`, and `∫_{|t|>T} t^{-2} dt = 2/T`; the fold onto `t > T`
is `integral_comp_abs`, which asks for no integrability, and on `t > T` the weight is integrable
because `t^{-2}` is. -/
lemma setIntegral_inv_sq_add_sq_abs_gt_le (σ : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹) ≤ 2 / T := by
  have hSmeas : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hind : ∀ t : ℝ,
      Set.indicator (Set.Ioi T) (fun u : ℝ => (σ ^ 2 + u ^ 2)⁻¹) |t|
        = Set.indicator {t : ℝ | T < |t|} (fun u : ℝ => (σ ^ 2 + u ^ 2)⁻¹) t := by
    intro t
    by_cases h : T < |t|
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 h),
        Set.indicator_of_mem (show t ∈ {t : ℝ | T < |t|} from h), sq_abs]
    · rw [Set.indicator_of_notMem (by simpa using h),
        Set.indicator_of_notMem (show t ∉ {t : ℝ | T < |t|} from h)]
  have habs := integral_comp_abs
    (f := Set.indicator (Set.Ioi T) fun u : ℝ => (σ ^ 2 + u ^ 2)⁻¹)
  simp only [hind] at habs
  rw [integral_indicator hSmeas] at habs
  rw [habs, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.2 (Set.Ioi_subset_Ioi hT.le), div_eq_mul_inv]
  have hmaj : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hle : ∀ t ∈ Set.Ioi T, (σ ^ 2 + t ^ 2)⁻¹ ≤ t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hT (Set.mem_Ioi.1 ht)
    have hrw : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [hrw]
    exact inv_anti₀ (pow_pos ht0 2) (le_add_of_nonneg_left (sq_nonneg σ))
  have hsmall : IntegrableOn (fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹) (Set.Ioi T) := by
    refine Integrable.mono' hmaj
      (by fun_prop : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans hT (Set.mem_Ioi.1 ht)
    have hpos : (0 : ℝ) < σ ^ 2 + t ^ 2 := by positivity
    rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
    exact hle t ht
  have hcmp : (∫ t in Set.Ioi T, (σ ^ 2 + t ^ 2)⁻¹) ≤ ∫ t in Set.Ioi T, t ^ (-2 : ℝ) :=
    setIntegral_mono_on hsmall hmaj measurableSet_Ioi hle
  have hval : (∫ t in Set.Ioi T, t ^ (-2 : ℝ)) = T⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hT, show (-2 : ℝ) + 1 = -1 by norm_num,
      Real.rpow_neg_one]
    ring
  rw [hval] at hcmp
  linarith

/-- **The far range of the line integral, by Hölder against the second moment.**  For `0 < q ≤ 1`,
`y ≥ 2` and `σ, T > 0`, `E[((log y)⁻¹∫_{|t|>T}‖F_y(½+σ+it)/(σ+it)‖²dt)^q] ≤ (C/T)^q`, with `C`
absolute. -/
theorem exists_integral_rpow_eulerProductLine_tail_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ y : ℕ, 2 ≤ y → ∀ σ T : ℝ, 0 < σ → 0 < T →
        (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|},
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
          ≤ (C / T) ^ q := by
  obtain ⟨C₂, -, hprod⟩ := exists_prod_one_add_le_rpow_log
  refine ⟨2 * Real.exp C₂, by positivity, ?_⟩
  intro Ω _ X μ hX q hq0 hq1 y hy σ T hσ hT
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hSmeas : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  -- the integrand, abbreviated once so that the rest of the proof is readable
  obtain ⟨G, hG⟩ : ∃ G : Ω → ℝ → ℝ, ∀ (ω : Ω) (t : ℝ), G ω t =
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, fun _ _ => rfl⟩
  simp only [← hG]
  -- ### (c) the weight and its tail
  have hwpos : ∀ t : ℝ, (0 : ℝ) < σ ^ 2 + t ^ 2 := fun t =>
    add_pos_of_pos_of_nonneg (pow_pos hσ 2) (sq_nonneg t)
  have hwmeas : Measurable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by fun_prop
  have hwint : Integrable fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ := by
    have hcmin : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (pow_pos hσ 2) one_pos
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (min (σ ^ 2) 1)⁻¹)
      hwmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have ha : min (σ ^ 2) 1 ≤ σ ^ 2 := min_le_left _ _
    have hb : min (σ ^ 2) 1 * t ^ 2 ≤ 1 * t ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
    have h2 : min (σ ^ 2) 1 * (1 + t ^ 2) ≤ σ ^ 2 + t ^ 2 := by
      have hexp : min (σ ^ 2) 1 * (1 + t ^ 2) = min (σ ^ 2) 1 + min (σ ^ 2) 1 * t ^ 2 := by ring
      rw [hexp]
      linarith
    rw [Real.norm_of_nonneg (inv_nonneg.2 (hwpos t).le), ← mul_inv]
    exact inv_anti₀ (mul_pos hcmin h1) h2
  have hwtail := setIntegral_inv_sq_add_sq_abs_gt_le σ hT
  -- ### (a) the second moment, the same at every height
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by
    intro t
    rw [hsline t]
    simp
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ,
      P = ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ))) := ⟨_, rfl⟩
  have hmom : ∀ t : ℝ,
      (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) = P := by
    intro t
    rw [hRa.integral_norm_randomEulerProduct_sq' (y + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I), hre t, hPdef]
  have hnormsq : ∀ (u : ℂ) (t : ℝ), ‖u / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖u‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro u t
    have hd : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
      have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      have h2 : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
      ring
    rw [norm_div, div_pow, hd, div_eq_mul_inv]
  have hslice : ∀ t : ℝ, (∫ ω, G ω t ∂μ) = P * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro t
    have h1 : (fun ω : Ω => G ω t)
        = fun ω : Ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ :=
      funext fun ω => by rw [hG ω t, hnormsq]
    rw [h1, integral_mul_const, hmom t]
  have hslice' : ∀ t : ℝ, (∫ ω, ‖G ω t‖ ∂μ) = P * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro t
    have h1 : (fun ω : Ω => ‖G ω t‖) = fun ω : Ω => G ω t :=
      funext fun ω => Real.norm_of_nonneg (by rw [hG ω t]; positivity)
    rw [h1, hslice t]
  -- ### Tonelli: joint measurability, then the two slice conditions
  have hjm : Measurable (Function.uncurry G) := by
    have huncurry : Measurable fun z : Ω × ℝ =>
        randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1 := by
      have h := measurable_randomEulerProduct_sqfree_uncurry (X := X)
        (fun p hp => hX.measurable p hp) (1 / 2 + σ) (y + 1)
      have hcongr : (fun z : Ω × ℝ =>
          randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1)
          = fun z : Ω × ℝ =>
            randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (z.2 : ℂ) * Complex.I) z.1 :=
        funext fun z => by rw [hsline z.2]
      rw [hcongr]
      exact h
    have hden : Measurable fun z : Ω × ℝ => (σ : ℂ) + (z.2 : ℂ) * Complex.I :=
      ((Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I).const_add _
    have hcongr2 : Function.uncurry G
        = fun z : Ω × ℝ =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1
            / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 :=
      funext fun z => hG z.1 z.2
    rw [hcongr2]
    exact (huncurry.div hden).norm.pow_const 2
  have hProd : Integrable (Function.uncurry G) (μ.prod (volume.restrict {t : ℝ | T < |t|})) := by
    refine (integrable_prod_iff' hjm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · have h1 : (fun ω : Ω => Function.uncurry G (ω, t))
          = fun ω : Ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ :=
        funext fun ω => by rw [Function.uncurry_apply_pair, hG ω t, hnormsq]
      rw [h1]
      exact (hRa.integrable_norm_randomEulerProduct_sq (y + 1) _).mul_const _
    · have h2 : (fun t : ℝ => ∫ ω, ‖Function.uncurry G (ω, t)‖ ∂μ)
          = fun t : ℝ => P * (σ ^ 2 + t ^ 2)⁻¹ :=
        funext fun t => by simp only [Function.uncurry_apply_pair]; exact hslice' t
      rw [h2]
      exact (hwint.const_mul P).integrableOn
  -- ### (b) Mertens: the second moment is `≪ log y`
  have hPle : P ≤ Real.exp C₂ * Real.log y := by
    rw [hPdef]
    have h := hprod y hy 1 zero_le_one (fun p => (p : ℝ) ^ (-2 * (1 / 2 + σ)))
      (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) ?_
    · rwa [one_mul, Real.rpow_one] at h
    -- the only content: the exponent is `≤ -1`, so each factor is `≤ 1/p`
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    rw [one_mul]
    calc (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
  -- ### the mean of the far-range functional
  have hZ0 : ∀ ω : Ω, (0 : ℝ) ≤ (Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t :=
    fun ω => mul_nonneg (inv_nonneg.2 hlogy.le)
      (setIntegral_nonneg hSmeas fun t _ => by rw [hG ω t]; positivity)
  have hZi : Integrable (fun ω => (Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) μ := by
    have h := hProd.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h
    exact h.const_mul _
  have hmean : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) ∂μ)
      ≤ 2 * Real.exp C₂ / T := by
    rw [integral_const_mul, integral_integral_swap hProd]
    have h1 : (∫ t in {t : ℝ | T < |t|}, ∫ ω, G ω t ∂μ)
        = ∫ t in {t : ℝ | T < |t|}, P * (σ ^ 2 + t ^ 2)⁻¹ :=
      setIntegral_congr_fun hSmeas fun t _ => hslice t
    rw [h1, integral_const_mul]
    have hP0 : (0 : ℝ) ≤ P := by
      rw [hPdef]
      exact Finset.prod_nonneg fun p _ => by positivity
    have hw0 : (0 : ℝ) ≤ ∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹ :=
      setIntegral_nonneg hSmeas fun t _ => inv_nonneg.2 (hwpos t).le
    have hstep : P * (∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹)
        ≤ Real.exp C₂ * Real.log y * (2 / T) :=
      mul_le_mul hPle hwtail hw0 (mul_nonneg (Real.exp_pos C₂).le hlogy.le)
    calc (Real.log y)⁻¹ * (P * ∫ t in {t : ℝ | T < |t|}, (σ ^ 2 + t ^ 2)⁻¹)
        ≤ (Real.log y)⁻¹ * (Real.exp C₂ * Real.log y * (2 / T)) :=
          mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hlogy.le)
      _ = 2 * Real.exp C₂ / T := by
          rw [show Real.exp C₂ * Real.log y * (2 / T)
              = Real.log y * (2 * Real.exp C₂ / T) by ring, ← mul_assoc,
            inv_mul_cancel₀ hlogy.ne', one_mul]
  -- ### Jensen
  have hZqi : Integrable (fun ω => ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) ^ q) μ :=
    integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0.le hq1
  refine le_trans (integral_rpow_le_rpow_integral hq0.le hq1
    (Filter.Eventually.of_forall hZ0) hZi hZqi) ?_
  exact Real.rpow_le_rpow (integral_nonneg fun ω => hZ0 ω) hmean hq0.le

end RMF
