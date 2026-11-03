/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FracPartExplicit
import RMF.Weighted.ExtendedAboveHalfExplicit

/-!
# The extended sum's uniform upper bounds with the constant `30`

`RMF.weighted_rademacher_moments_upper_uniform_explicit` for `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)` with
`30` in place of `25`, every `x ≥ 3` (`RMF.extended_rademacher_moments_upper_uniform_explicit`).
At and above `q = ½` it is `RMF.extended_rademacher_moments_upper_aboveHalf_explicit`.  Below `½`,
with `Λ = log log x`:

* `Λ ≥ 1`: `E|Y|^{2q} ≤ E|S|^{2q} + E|R|^{2q} ≤ (25 + 3.5)(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, by the
  weighted bound (`RMF.integral_rpow_weightedRademacherSum_le_u`) and
  `E|R|^{2q} ≤ min(1, 20Λ^{-1/4})^{2q} ≤ 3.5(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`
  (`RMF.min_rpow_le_harmonic`); no descent is needed;
* `Λ < 1`: the trivial bound, `E|Y|^{2q} ≤ √x ≤ 30Λ ≤ 30Λ^{1-q/2}`.
-/

open MeasureTheory

namespace RMF

/-! ### Numerals -/

/-- `(1 - 2q)20^{2q} ≤ 5/2` for every `q`: with `s = 1 - 2q`, `20^{2q}e^{s log 20} = 20`, and
`8s ≤ e^{s log 20}` since `e^y ≥ ey` (`1 + (y - 1) ≤ e^{y-1}`) and `e·log 20 ≥ 8`. -/
lemma one_sub_two_mul_mul_twenty_rpow_le (q : ℝ) : (1 - 2 * q) * (20 : ℝ) ^ (2 * q) ≤ 5 / 2 := by
  have hae : (8 : ℝ) ≤ Real.log 20 * Real.exp 1 := by interval_decide (trust := kernel)
  have hP0 : 0 < (20 : ℝ) ^ (2 * q) := Real.rpow_pos_of_pos (by norm_num) _
  have hPE : (20 : ℝ) ^ (2 * q) * Real.exp (Real.log 20 * (1 - 2 * q)) = 20 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 20), ← Real.exp_add,
      show Real.log 20 * (2 * q) + Real.log 20 * (1 - 2 * q) = Real.log 20 by ring,
      Real.exp_log (by norm_num)]
  have hkey : 8 * (1 - 2 * q) ≤ Real.exp (Real.log 20 * (1 - 2 * q)) := by
    rcases le_or_gt (1 - 2 * q) 0 with h0 | h0
    · have := Real.exp_pos (Real.log 20 * (1 - 2 * q))
      linarith
    · have h1 := Real.add_one_le_exp (Real.log 20 * (1 - 2 * q) - 1)
      have h2 : Real.exp (Real.log 20 * (1 - 2 * q) - 1) * Real.exp 1
          = Real.exp (Real.log 20 * (1 - 2 * q)) := by
        rw [← Real.exp_add]
        ring_nf
      have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos 1).le
      have h4 := mul_le_mul_of_nonneg_right hae h0.le
      nlinarith
  have := mul_le_mul_of_nonneg_left hkey hP0.le
  nlinarith

/-- **The remainder against the harmonic form**: for `Λ ≥ 1` and `0 ≤ q ≤ ½`,
`min(1, 20Λ^{-1/4})^{2q} ≤ 3.5(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`.  With `B` the left side and
`P = Λ^{q/2}`: `BP ≤ P ≤ Λ` and `BP ≤ 20^{2q}`, so `B(Λ⁻¹ + 1 - 2q)P ≤ 1 + (1 - 2q)20^{2q} ≤ 3.5`
(`RMF.one_sub_two_mul_mul_twenty_rpow_le`). -/
lemma min_rpow_le_harmonic {Λ q : ℝ} (hΛ : 1 ≤ Λ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q)
      ≤ 3.5 * (Λ⁻¹ + (1 - 2 * q))⁻¹ * Λ ^ (-(q / 2)) := by
  have hΛ0 : 0 < Λ := by linarith
  have hr : 0 ≤ 2 * q := by linarith
  have hM0 : 0 ≤ Λ ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hΛ0.le _
  have hmin0 : 0 ≤ min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) := le_min zero_le_one (by positivity)
  have hP0 : 0 < Λ ^ (q / 2) := Real.rpow_pos_of_pos hΛ0 _
  have hV0 : 0 < Λ⁻¹ + (1 - 2 * q) := by
    have := inv_pos.2 hΛ0
    linarith
  -- `B ≤ 1` and `BP ≤ 20^{2q}`
  have hB1 : min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) ≤ 1 :=
    Real.rpow_le_one hmin0 (min_le_left _ _) hr
  have hBP : min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2) ≤ (20 : ℝ) ^ (2 * q) := by
    have h1 : min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) ≤ (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) :=
      Real.rpow_le_rpow hmin0 (min_le_right _ _) hr
    have h2 : (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2) = (20 : ℝ) ^ (2 * q) := by
      rw [Real.mul_rpow (by norm_num) hM0, ← Real.rpow_mul hΛ0.le, mul_assoc,
        ← Real.rpow_add hΛ0, show -(1 / 4 : ℝ) * (2 * q) + q / 2 = 0 by ring, Real.rpow_zero,
        mul_one]
    calc min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2)
        ≤ (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2) :=
          mul_le_mul_of_nonneg_right h1 hP0.le
      _ = (20 : ℝ) ^ (2 * q) := h2
  -- `P ≤ Λ`
  have hPΛ : Λ ^ (q / 2) ≤ Λ := Real.rpow_le_self_of_one_le hΛ (by linarith)
  have hnum := one_sub_two_mul_mul_twenty_rpow_le q
  -- `B(Λ⁻¹ + 1 - 2q)P ≤ 3.5`
  have hkey : min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * ((Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2))
      ≤ 3.5 := by
    have e : min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * ((Λ⁻¹ + (1 - 2 * q)) * Λ ^ (q / 2))
        = min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2) * Λ⁻¹
          + (1 - 2 * q) * (min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2)) := by ring
    rw [e]
    have h1 : min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2) * Λ⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hΛ0]
      calc min 1 (20 * Λ ^ (-(1 / 4 : ℝ))) ^ (2 * q) * Λ ^ (q / 2) ≤ 1 * Λ ^ (q / 2) :=
            mul_le_mul_of_nonneg_right hB1 hP0.le
        _ ≤ Λ := by linarith
    have h2 := mul_le_mul_of_nonneg_left hBP (by linarith : (0 : ℝ) ≤ 1 - 2 * q)
    linarith
  rw [Real.rpow_neg hΛ0.le (q / 2), mul_assoc, ← mul_inv, ← div_eq_mul_inv,
    le_div_iff₀ (mul_pos hV0 hP0)]
  exact hkey

/-- `√x ≤ 30Λ` for `x ≥ 3` and `Λ = log log x ≤ 1`: on `[3, 4]`, `√x ≤ 2 ≤ 30·0.094`; on
`[4, e^e]`, `√x ≤ 3.9 ≤ 30·0.32 ≤ 30 log log 4`. -/
lemma sqrt_le_thirty_mul_loglog {x : ℝ} (hx : 3 ≤ x) (hΛ : Real.log (Real.log x) ≤ 1) :
    Real.sqrt x ≤ 30 * Real.log (Real.log x) := by
  have h3 := loglog_ge_of_three_le hx
  rcases le_or_gt x 4 with h4 | h4
  · have hs : Real.sqrt x ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by linarith)
    linarith
  · have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hlx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hn : (0.32 : ℝ) ≤ Real.log (Real.log 4) := by interval_decide (trust := kernel)
    have hmono : Real.log (Real.log 4) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) h4.le)
    have hee : Real.exp (Real.exp 1) ≤ 15.16 := by interval_decide (trust := kernel)
    have hL : Real.log x ≤ Real.exp 1 := (Real.log_le_iff_le_exp (lt_of_lt_of_le hl3 hlx)).1 hΛ
    have hxe : x ≤ Real.exp (Real.exp 1) := (Real.log_le_iff_le_exp (by linarith)).1 hL
    have hs : Real.sqrt x ≤ 3.9 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num; linarith)
    linarith

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The trivial bound below `q = ½` -/

/-- **The trivial bound, below `q = ½`**: `E|Y(x)|^{2q} ≤ (⌊x⌋/√x)^{2q} ≤ √x` for `x ≥ 1` and
`0 ≤ q ≤ ½` (`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le_floor`). -/
theorem integral_rpow_normalisedSum_compMultExtension_le_sqrt {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hfl : (⌊x⌋₊ : ℝ) / Real.sqrt x ≤ Real.sqrt x := by
    rw [div_le_iff₀ hs0, Real.mul_self_sqrt hx0]
    exact Nat.floor_le hx0
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ (2 * q) :=
        integral_rpow_norm_normalisedSum_compMultExtension_le_floor hX x hq0
    _ ≤ Real.sqrt x ^ (2 * q) :=
        Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) hs0.le) hfl (by linarith)
    _ ≤ Real.sqrt x := Real.rpow_le_self_of_one_le (Real.one_le_sqrt.2 hx) (by linarith)

end

/-! ### The theorem -/

/-- **The uniform upper bounds for the extended sum with the constant `30`**: for every `x ≥ 3`,
with `Λ = log log x` and `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`,

* `E|Y(x)|^{2q} ≤ 30·min(Λ, 1/(1 - 2q))·Λ^{-q/2}` for `0 < q < ½`: for `Λ ≥ 1`,
  `E|Y|^{2q} ≤ E|S|^{2q} + E|R|^{2q}` with the weighted bound
  (`RMF.integral_rpow_weightedRademacherSum_le_u`) and
  `RMF.integral_rpow_norm_fracPartSum_le_min_of_three_le`, `RMF.min_rpow_le_harmonic`; for
  `Λ < 1`, `E|Y|^{2q} ≤ √x ≤ 30Λ` (`RMF.sqrt_le_thirty_mul_loglog`);
* `E|Y(x)| ≤ 30Λ^{3/4}`, from `20` (`RMF.extended_rademacher_moments_upper_aboveHalf_explicit`);
* `E|Y(x)|^{2q} ≤ 30(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}` for `½ < q ≤ 1` (the same).

`RMF.weighted_rademacher_moments_upper_uniform_explicit` for the extended sum, with `30`. -/
theorem extended_rademacher_moments_upper_uniform_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∀ q : ℝ, 0 < q → q < 1 / 2 →
          (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ 30 * (min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
              * Real.log (Real.log x) ^ (-(q / 2)))) ∧
        (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ)
          ≤ 30 * Real.log (Real.log x) ^ (3 / 4 : ℝ) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ)
            ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) := by
  intro Ω _ X μ hX x hx
  obtain ⟨hhalf, habove⟩ := extended_rademacher_moments_upper_aboveHalf_explicit Ω X μ hX x hx
  have hL0 : 0 < Real.log (Real.log x) := by linarith [loglog_ge_of_three_le hx]
  refine ⟨fun q hq0 hq2 => ?_, le_trans hhalf
    (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hL0.le _)), habove⟩
  have hb : 0 < 1 - 2 * q := by linarith
  have hpow : 0 ≤ Real.log (Real.log x) ^ (-(q / 2)) := Real.rpow_nonneg hL0.le _
  rcases lt_or_ge (Real.log (Real.log x)) 1 with h1 | h1
  · -- `Λ < 1`: the trivial bound, against `30Λ^{1-q/2}`
    have hm : min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ = Real.log (Real.log x) :=
      min_eq_left (h1.le.trans ((one_le_inv₀ hb).2 (by linarith)))
    have hp1 : 1 ≤ Real.log (Real.log x) ^ (-(q / 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hL0 h1.le (by linarith)
    have hY := integral_rpow_normalisedSum_compMultExtension_le_sqrt hX (μ := μ)
      (by linarith : (1 : ℝ) ≤ x) hq0.le hq2.le
    have hsq := sqrt_le_thirty_mul_loglog hx h1.le
    have hΛp := le_mul_of_one_le_right hL0.le hp1
    rw [hm]
    linarith
  -- `Λ ≥ 1`: `E|Y|^{2q} ≤ E|S|^{2q} + E|R|^{2q} ≤ (25 + 3.5)(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`
  have hY := integral_rpow_norm_normalisedSum_compMultExtension_le_add hX
    (by linarith : (1 : ℝ) ≤ x) hq0.le hq2.le
  have hS := integral_rpow_weightedRademacherSum_le_u hX hx hq0 hq2.le
  have hR := (integral_rpow_norm_fracPartSum_le_min_of_three_le hX hx hq0.le hq2.le).trans
    (min_rpow_le_harmonic h1 hq0.le hq2.le)
  -- the harmonic form against the `min` form, as in the weighted theorem
  have hmin : ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
      ≤ min (Real.log (Real.log x)) (1 - 2 * q)⁻¹ := by
    refine le_min ?_ (inv_anti₀ hb (le_add_of_nonneg_left (inv_nonneg.2 hL0.le)))
    calc ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹ ≤ (Real.log (Real.log x))⁻¹⁻¹ :=
          inv_anti₀ (inv_pos.2 hL0) (le_add_of_nonneg_right hb.le)
      _ = Real.log (Real.log x) := inv_inv _
  have hτ := mul_le_mul_of_nonneg_right hmin hpow
  have hτ0 : 0 ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
      * Real.log (Real.log x) ^ (-(q / 2)) :=
    mul_nonneg (inv_nonneg.2 (by have := inv_pos.2 hL0; linarith)) hpow
  linarith

end RMF
