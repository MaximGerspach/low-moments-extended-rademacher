/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CentralWindow
import RMF.Weighted.EulerMomentBand

/-!
# The central window of a band, at the band's own shift

For the band `y < p ≤ z` with `2 ≤ y ≤ z` and `z ≥ 3`, a shift `c > 0` with `2c·log z ≤ 1` and
`c ≤ 1/12`, and a half-width `w > 0` with `w·log(z+1) ≤ 2`,

`E[((log z)⁻¹∫_{|t|≤w}‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q] ≤ A·(c·log z)^{-q}·κ^{q(2q-1)}`,

`κ = log z/log y`, uniformly in `½ ≤ q ≤ 1`, with `A = π·e^{143800e}·e^{48}`
(`RMF.integral_rpow_centralWindow_primesIco_le`).  At `c = 1/(2 log z)` the factor
`(c·log z)^{-q}` is `2^q ≤ 2`, and the window `|t| ≤ 1/log z` has `w·log(z+1) ≤ 2` once `z ≥ 2`.

## The route

Two inputs, one hinge.  The band's central window with the weight decoupled from the product's
shift, `RMF.integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le`, and the band's moment
bound `E|F_{y,z}(½-c)|^{2q} ≪ κ^{q(2q-1)}` at the same shift,
`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_signed_shift_rpow_le_log_div`.  The
hinge is the window lemma's `K`, the bound `p^{-2(½-c)} ≤ K/p` on the band: `2c·log p ≤ 1` there,
so `K = e` by `RMF.rpow_neg_shift_le_exp_one_mul_inv`.  The hypothesis `c ≤ 1/12` is the two-point
ratio's `½ - c ≥ 5/12`; at `c = 1/(2 log z)` it asks `log z ≥ 6`.

The assembly is that of `RMF.exists_const_integral_rpow_centralRange_le_rademacher`, moved to the
left of `½` and to a band.  Only an upper bound is proved.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The central window of a band, at the band's own shift.**  For `½ ≤ q ≤ 1`, `2 ≤ y ≤ z`
with `z ≥ 3`, `0 < c ≤ 1/12` with `2c·log z ≤ 1`, and `w > 0` with `w·log(z+1) ≤ 2`,

`E[((log z)⁻¹∫_{|t|≤w}‖F_{y,z}(½-c+it)/(c+it)‖²dt)^q]
  ≤ π·e^{143800e}·e^{48}·(c·log z)^{-q}·(log z/log y)^{q(2q-1)}`,

`F_{y,z} = randomEulerProductIco f (y+1) (z+1)` the product over the primes `y < p ≤ z`. -/
theorem integral_rpow_centralWindow_primesIco_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q c w : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) (hz : 3 ≤ z) (hc : 0 < c) (hc12 : c ≤ 1 / 12)
    (hcz : 2 * c * Real.log z ≤ 1) (hw : 0 < w) (hwz : w * Real.log ((z : ℝ) + 1) ≤ 2) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48 * ((c * Real.log z)⁻¹) ^ q
        * (Real.log z / Real.log y) ^ (q * (2 * q - 1)) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  -- the abscissa, as the window lemma writes it
  have habs : ∀ t : ℝ, ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) = shiftLine (-c) t := by
    intro t
    rw [shiftLine]
    push_cast
    ring
  simp only [habs]
  -- the normalisation comes out of the `q`-th power
  have hInn : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in Set.Icc (-w) w,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
        (shiftLine (-c) t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hsplit : ∀ ω : Ω, ((Real.log z)⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          (shiftLine (-c) t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
      = ((Real.log z)⁻¹) ^ q * (∫ t in Set.Icc (-w) w,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          (shiftLine (-c) t) ω / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q := fun ω =>
    Real.mul_rpow (by positivity) (hInn ω)
  simp only [hsplit]
  rw [integral_const_mul]
  -- on the band `2c·log p ≤ 1`, so the window lemma's `K` is `e`
  have hσz : 2 * |(-c)| * Real.log z ≤ 1 := by
    rw [abs_neg, abs_of_pos hc]
    exact hcz
  have hK : ∀ p ∈ primesIco (y + 1) (z + 1),
      (p : ℝ) ^ (-(1 / 2 + -c)) * (p : ℝ) ^ (-(1 / 2 + -c)) ≤ Real.exp 1 * ((p : ℝ))⁻¹ := by
    intro p hp
    obtain ⟨hprime, _, hpz⟩ := mem_primesIco.1 hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hlp : Real.log p ≤ Real.log z :=
      Real.log_le_log hp0 (by exact_mod_cast (by omega : p ≤ z))
    rw [← Real.rpow_add hp0, show -(1 / 2 + -c) + -(1 / 2 + -c) = -(1 + 2 * (-c)) by ring]
    exact rpow_neg_shift_le_exp_one_mul_inv hprime.one_lt.le
      (le_trans (mul_le_mul_of_nonneg_left hlp (by positivity)) hσz)
  have hwin := integral_rpow_setIntegral_normSq_div_shiftLine_primesIco_le hX
    (y₀ := y + 1) (y₁ := z + 1) (by omega) (σ := -c) (c := c) (K := Real.exp 1)
    (by linarith) hK (Real.exp_pos 1).le hc hw (by push_cast; exact hwz) (by linarith) hq1
  have hpf := hRa.integral_norm_randomEulerProductIco_signed_shift_rpow_le_log_div
    (σ := -c) hq0 hq1 hy hyz hz hσz
  have hz0 : shiftLine (-c) 0 = (((1 / 2 + -c : ℝ)) : ℂ) := by
    rw [shiftLine]
    norm_num
  rw [hz0] at hwin
  have hR0 : (0 : ℝ) ≤ (Real.pi / c * Real.exp (143800 * Real.exp 1)) ^ q :=
    Real.rpow_nonneg (by positivity) _
  have hNq : (0 : ℝ) ≤ ((Real.log z)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  have hstep := mul_le_mul_of_nonneg_left (hwin.trans (mul_le_mul_of_nonneg_left hpf hR0)) hNq
  refine hstep.trans ?_
  -- `(log z)^{-q}·(π e^{143800e}/c)^q = (π e^{143800e})^q·(c log z)^{-q}`, and the base is `≥ 1`
  have hfold : ((Real.log z)⁻¹) ^ q * (Real.pi / c * Real.exp (143800 * Real.exp 1)) ^ q
      = (Real.pi * Real.exp (143800 * Real.exp 1)) ^ q * ((c * Real.log z)⁻¹) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hbase : (1 : ℝ) ≤ Real.pi * Real.exp (143800 * Real.exp 1) := by
    have h1 : (1 : ℝ) ≤ Real.exp (143800 * Real.exp 1) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_gt_three]
  have hcst : (Real.pi * Real.exp (143800 * Real.exp 1)) ^ q
      ≤ Real.pi * Real.exp (143800 * Real.exp 1) := by
    calc (Real.pi * Real.exp (143800 * Real.exp 1)) ^ q
        ≤ (Real.pi * Real.exp (143800 * Real.exp 1)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hq1
      _ = Real.pi * Real.exp (143800 * Real.exp 1) := Real.rpow_one _
  have hSq : (0 : ℝ) ≤ ((c * Real.log z)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  calc ((Real.log z)⁻¹) ^ q
        * ((Real.pi / c * Real.exp (143800 * Real.exp 1)) ^ q
          * (Real.exp 48 * (Real.log z / Real.log y) ^ (q * (2 * q - 1))))
      = (((Real.log z)⁻¹) ^ q * (Real.pi / c * Real.exp (143800 * Real.exp 1)) ^ q)
        * (Real.exp 48 * (Real.log z / Real.log y) ^ (q * (2 * q - 1))) := by ring
    _ = (Real.pi * Real.exp (143800 * Real.exp 1)) ^ q * ((c * Real.log z)⁻¹) ^ q
        * (Real.exp 48 * (Real.log z / Real.log y) ^ (q * (2 * q - 1))) := by rw [hfold]
    _ ≤ Real.pi * Real.exp (143800 * Real.exp 1) * ((c * Real.log z)⁻¹) ^ q
        * (Real.exp 48 * (Real.log z / Real.log y) ^ (q * (2 * q - 1))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcst hSq) ?_
        positivity
    _ = Real.pi * Real.exp (143800 * Real.exp 1) * Real.exp 48 * ((c * Real.log z)⁻¹) ^ q
        * (Real.log z / Real.log y) ^ (q * (2 * q - 1)) := by ring

end RMF
