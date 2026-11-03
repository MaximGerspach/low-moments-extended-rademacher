/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerDamped
import RMF.Weighted.EulerMomentBand

/-!
# The far range of a band

The far range of a band `(y, z]` at its shift `½ - c`.  Past height `T ≍ 1/log y` nothing about
the chaos is needed: by Jensen,

`E[((log z)⁻¹∫_{|t|>T}|F_{y,z}(½-c+it)|²/|c+it|² dt)^q]
  ≤ ((log z)⁻¹·(∫_{|t|>T} dt/(c²+t²))·sup_t E|F_{y,z}(½-c+it)|²)^q`,

and each factor is explicit.  The Rademacher second moment does not depend on the height, and at
the band's shift it is `≤ exp ∑_{y<p≤z} p^{-(1-2c)} ≤ e^{45}·log z/log y`, by Mertens read
additively (`RMF.sum_primesIco_rpow_signed_shift_le_log_div_add`); the weight's tail is at most
`2/T` (`RMF.setIntegral_inv_sq_add_sq_abs_gt_le`).  The bound is `(2e^{45}/(T·log y))^q`, which
is `O(1)` at `T ≍ 1/log y`.

The Fubini and Jensen steps are `RMF.integral_rpow_setIntegral_lineDiv_le`, which is generic in the
integrand; what is specific to the band is only the joint measurability, the envelope and the
second moment.  They are stated once, over any set of heights
(`RMF.integral_rpow_setIntegral_lineDiv_primesIco_le`): the far range is the set `|t| > T`, and
on the whole line, where the weight integrates to `π/c`, the same statement gives a crude bound.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### A block product on the line `Re s = ½ - c` -/

/-- **A block product on the line `Re s = ½ - c` is jointly measurable** in the sample and the
height, through the closed form `RMF.randomEulerProductIco_sqfree_eq`. -/
lemma measurable_uncurry_randomEulerProductIco_line {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) (c : ℝ) :
    Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω) := by
  have hs : ∀ t : ℝ, (1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I = shiftLine (-c) t := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  have hmeas0 : Measurable fun w : Ω × ℝ =>
      ∏ p ∈ primesIco y₀ y₁, (1 + X p w.1 * (p : ℂ) ^ (-(shiftLine (-c) w.2))) := by
    refine Finset.measurable_prod _ fun p hp => ?_
    have h1 : Measurable fun w : Ω × ℝ => X p w.1 :=
      (hX.measurable p (prime_of_mem_primesIco hp)).comp measurable_fst
    have h2 : Measurable fun w : Ω × ℝ => (p : ℂ) ^ (-(shiftLine (-c) w.2)) :=
      ((continuous_cpow_neg_shiftLine (prime_of_mem_primesIco hp).pos (-c)).measurable).comp
        measurable_snd
    exact (h1.mul h2).const_add 1
  have heq : (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
      = fun w : Ω × ℝ =>
        ∏ p ∈ primesIco y₀ y₁, (1 + X p w.1 * (p : ℂ) ^ (-(shiftLine (-c) w.2))) := by
    funext w
    change randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
        ((1 / 2 : ℂ) - (c : ℂ) + (w.2 : ℂ) * Complex.I) w.1 = _
    rw [hs w.2]
    exact randomEulerProductIco_sqfree_eq y₀ y₁ _ w.1
  rw [heq]
  exact hmeas0

/-- **The envelope of a block product along `Re s = ½ - c`**, for `c < ½`: one almost-sure event
bounds it at every height. -/
lemma ae_forall_norm_randomEulerProductIco_line_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y₀ y₁ : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ ∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + -c))) := by
  have hs : ∀ t : ℝ, (1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I = shiftLine (-c) t := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + -c := by
    intro t
    rw [hs t]
    exact re_shiftLine (-c) t
  filter_upwards [ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hX y₀ y₁
    (by linarith : (0 : ℝ) < 1 / 2 + -c)] with ω hω
  exact fun t => (hω _ (hre t)).2

/-! ### Over any set of heights -/

/-- **A band's damped line integral over any set of heights, by Jensen.**  For `0 ≤ q ≤ 1`,
`2 ≤ y ≤ z`, `0 < c < ½` with `2c·log z ≤ 1`, and any `S`,
`E[((log z)⁻¹∫_S‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q]
  ≤ ((log z)⁻¹·(∫_S dt/(c²+t²))·e^{45}·log z/log y)^q`:
`RMF.integral_rpow_setIntegral_lineDiv_le` with the band's joint measurability, its envelope, and
its second moment `≤ exp ∑_{y<p≤z} p^{-(1-2c)} ≤ e^{45}·log z/log y` at every height. -/
theorem integral_rpow_setIntegral_lineDiv_primesIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {y z : ℕ}
    (hy : 2 ≤ y) (hyz : y ≤ z) (hc : 0 < c) (hc2 : c < 1 / 2)
    (hcz : 2 * c * Real.log z ≤ 1) (S : Set ℝ) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t in S,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ((Real.log z)⁻¹
          * ((∫ t in S, (c ^ 2 + t ^ 2)⁻¹) * (Real.exp 45 * (Real.log z / Real.log y)))) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hs : ∀ t : ℝ, (1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I = shiftLine (-c) t := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + -c := by
    intro t
    rw [hs t]
    exact re_shiftLine (-c) t
  -- the second moment, the same at every height: `≤ e^{45}·log z/log y`
  have hM : ∀ t : ℝ,
      (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
        ≤ Real.exp 45 * (Real.log z / Real.log y) := by
    intro t
    refine le_trans (hRa.integral_norm_randomEulerProductIco_sq_le (y + 1) (z + 1) _) ?_
    have hσz : 2 * |(-c)| * Real.log z ≤ 1 := by rw [abs_neg, abs_of_pos hc]; exact hcz
    have hmert := sum_primesIco_rpow_signed_shift_le_log_div_add hy hyz hσz
    have hexp : ∀ p ∈ primesIco (y + 1) (z + 1),
        ((p : ℕ) : ℝ) ^ (-2 * ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I).re)
          = (p : ℝ) ^ (-(1 + 2 * -c)) := by
      intro p _
      rw [hre t]
      congr 1
      ring
    rw [Finset.sum_congr rfl hexp]
    calc Real.exp (∑ p ∈ primesIco (y + 1) (z + 1), (p : ℝ) ^ (-(1 + 2 * -c)))
        ≤ Real.exp (Real.log (Real.log z / Real.log y) + 45) := Real.exp_le_exp.2 hmert
      _ = Real.exp 45 * (Real.log z / Real.log y) := by
          rw [Real.exp_add, Real.exp_log (div_pos hlogz hlogy)]
          ring
  exact integral_rpow_setIntegral_lineDiv_le (μ := μ)
    (F := fun ω t => randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (y + 1) (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω)
    (S := S) (L := Real.log z) hc hlogz hq0 hq1
    (measurable_uncurry_randomEulerProductIco_line hX (y + 1) (z + 1) c)
    (ae_forall_norm_randomEulerProductIco_line_le hX (y + 1) (z + 1) hc2) hM

/-! ### The far range -/

/-- **The far range of a band, at the band's own shift.**  For `0 ≤ q ≤ 1`,
`2 ≤ y ≤ z`, `0 < c ≤ 1/12` with `2c·log z ≤ 1`, and `T > 0`,
`E[((log z)⁻¹∫_{|t|>T}‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q] ≤ (2e^{45}/(T·log y))^q`, `F_{y,z}` the
product over the primes `y < p ≤ z`: the set `|t| > T` of
`RMF.integral_rpow_setIntegral_lineDiv_primesIco_le`, with the weight's tail at most `2/T`. -/
theorem integral_rpow_farRange_primesIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q c T : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {y z : ℕ}
    (hy : 2 ≤ y) (hyz : y ≤ z) (hc : 0 < c) (hc12 : c ≤ 1 / 12)
    (hcz : 2 * c * Real.log z ≤ 1) (hT : 0 < T) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t in {t : ℝ | T < |t|},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (2 * Real.exp 45 / (T * Real.log y)) ^ q := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  refine le_trans (integral_rpow_setIntegral_lineDiv_primesIco_le hX hq0 hq1 hy hyz hc
    (by linarith) hcz {t : ℝ | T < |t|}) ?_
  -- `(log z)⁻¹·(2/T)·e^{45}·(log z/log y) = 2e^{45}/(T·log y)`
  have hw := setIntegral_inv_sq_add_sq_abs_gt_le c hT
  have hw0 : (0 : ℝ) ≤ ∫ t in {t : ℝ | T < |t|}, (c ^ 2 + t ^ 2)⁻¹ :=
    integral_nonneg fun t => inv_nonneg.2 (by positivity)
  have hM0 : (0 : ℝ) ≤ Real.exp 45 * (Real.log z / Real.log y) :=
    mul_nonneg (Real.exp_pos 45).le (div_nonneg hlogz.le hlogy.le)
  refine Real.rpow_le_rpow (mul_nonneg (inv_nonneg.2 hlogz.le) (mul_nonneg hw0 hM0)) ?_ hq0
  calc (Real.log z)⁻¹ * ((∫ t in {t : ℝ | T < |t|}, (c ^ 2 + t ^ 2)⁻¹)
        * (Real.exp 45 * (Real.log z / Real.log y)))
      ≤ (Real.log z)⁻¹ * ((2 / T) * (Real.exp 45 * (Real.log z / Real.log y))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hM0) (inv_nonneg.2 hlogz.le)
    _ = (Real.log z * (Real.log z)⁻¹) * (2 * Real.exp 45 / (T * Real.log y)) := by ring
    _ = 2 * Real.exp 45 / (T * Real.log y) := by rw [mul_inv_cancel₀ hlogz.ne', one_mul]

end RMF
