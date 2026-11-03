/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SubtractedBelowHalf.Numerals

/-!
# The subtracted term below `½`

The subtracted term of the explicit reduction
(`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`),
`E[J(V/log x)^q]`, `J(σ) = ∫_ℝ‖F_{⌊x⌋+1}(½+σ+it)/(σ+it)‖²dt`, with absolute constants, for
`Λ = log log x ≥ 6000` and `V ≥ 1/32`:

* `E[J(V/log x)^q] ≤ 216(log x)^q·min{Λ, (1-2q)⁻¹}Λ^{-q/2}` for `0 < q < ½`
  (`RMF.integral_rpow_lineDiv_le_subtracted_belowHalf`);
* `E[J(V/log x)^{1/2}] ≤ 17.3(log x)^{1/2}Λ^{3/4}` (`RMF.integral_sqrt_lineDiv_le_subtracted_half`).

The shift down to `σ = halfSigma x` (`RMF.integral_rpow_lineDiv_le_of_le`), the high primes
integrated out down to `y = halfY x` (`RMF.integral_rpow_lineDiv_le_mBand_rpow_mul`, with
`mBand·log y ≤ e^{1/1000}log x`), then `Z = (log y)⁻¹J_y` (`RMF.integral_rpow_lineDiv_le_Z_halfY`):
at `q = ½`, `E Z^{1/2} ≤ 17.2Λ^{3/4}` (`RMF.integral_sqrt_Z_halfY_le`); below `½` one constant
`215` (`RMF.integral_rpow_Z_halfY_le_belowHalf`): Lyapunov from `½` for `w = (1-2q)Λ ≤ 23/2`
(`RMF.z_small_w`), the cell `RMF.z_cell_half_top` for `w ≥ 23/2`, and below `q = 0.49` the
descent (`RMF.z_descent`) from its anchor `RMF.z_cell_half_anchor`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The descent below `q = 0.49` -/

/-- **The descent below `q₀ = 0.49`**: on a probability space, for `g ≥ 0` with integrable powers
and `Λ ≥ 6000`, if `E[g^{0.49}] ≤ 40τ(0.49)` then `E[g^q] ≤ 160τ(q)` for `0 < q ≤ 0.49`,
`τ(q) = (Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`.  Lyapunov gives `E[g^q] ≤ (40/a)^sΛ^{-q/2}`, `s = q/0.49`,
`a = Λ⁻¹ + 0.02`, and `(40/a)^s(a + 0.98(1 - s)) ≤ 160` from `40/a ≤ e^8` and `te^{-t} ≤ e^{-1}`
at `t = 8(1 - s) + 8a/0.98`. -/
lemma z_descent {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg0 : ∀ ω, 0 ≤ g ω)
    (hgi : ∀ r : ℝ, 0 ≤ r → Integrable (fun ω => g ω ^ r) μ) {Λ q : ℝ} (hΛ : 6000 ≤ Λ)
    (hq0 : 0 < q) (hq : q ≤ 49 / 100)
    (h49 : ∫ ω, g ω ^ (49 / 100 : ℝ) ∂μ
      ≤ 40 * (Λ⁻¹ + (1 - 2 * (49 / 100 : ℝ)))⁻¹ * Λ ^ (-((49 / 100 : ℝ) / 2))) :
    ∫ ω, g ω ^ q ∂μ ≤ 160 * (Λ⁻¹ + (1 - 2 * q))⁻¹ * Λ ^ (-(q / 2)) := by
  have hΛp : 0 < Λ := by linarith
  have hL := integral_rpow_le_rpow_integral_rpow (r := 49 / 100) hq0 hq hg0
    (hgi _ (by norm_num)) (hgi q hq0.le)
  set E0 := ∫ ω, g ω ^ (49 / 100 : ℝ) ∂μ with hE0def
  have hE0 : 0 ≤ E0 := integral_nonneg fun ω => Real.rpow_nonneg (hg0 ω) _
  set s := q / (49 / 100) with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hsdef, div_le_one (by norm_num)]; exact hq
  set u := 1 - s with hudef
  have hu0 : 0 ≤ u := by linarith
  have hqs : q = 49 / 100 * s := by rw [hsdef]; field_simp
  set a := Λ⁻¹ + (1 - 2 * (49 / 100 : ℝ)) with hadef
  have hΛi0 : 0 < Λ⁻¹ := inv_pos.2 hΛp
  have hΛi : Λ⁻¹ ≤ 1 / 6000 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΛ
  have ha1 : 2 / 100 ≤ a := by rw [hadef]; linarith
  have ha2 : a ≤ 2 / 100 + 1 / 6000 := by rw [hadef]; linarith
  have ha0 : 0 < a := by linarith
  -- the anchor as an exponential: `40a⁻¹Λ^{-0.245} = e^{L - 0.245 log Λ}`, `L = log(40/a) ≤ 8`
  set Lg := Real.log (40 / a) with hLgdef
  have hLg : Lg ≤ 8 := by
    rw [hLgdef, Real.log_le_iff_le_exp (by positivity)]
    have h8 : (2000 : ℝ) ≤ Real.exp 8 := by interval_decide (trust := kernel)
    have : 40 / a ≤ 2000 := by rw [div_le_iff₀ ha0]; linarith
    linarith
  have hτ0 : 40 * a⁻¹ * Λ ^ (-((49 / 100 : ℝ) / 2))
      = Real.exp (Lg - 49 / 100 / 2 * Real.log Λ) := by
    rw [Real.exp_sub, hLgdef, Real.exp_log (by positivity), rpow_eq_exp_mul_log hΛp,
      show -((49 / 100 : ℝ) / 2) * Real.log Λ = -(49 / 100 / 2 * Real.log Λ) by ring,
      Real.exp_neg]
    field_simp
  rw [hτ0] at h49
  have h1 : E0 ^ s ≤ Real.exp (Lg - 49 / 100 / 2 * Real.log Λ) ^ s :=
    Real.rpow_le_rpow hE0 h49 hs0
  rw [← Real.exp_mul] at h1
  -- `e^{sL}(a + 0.98u) ≤ e^{8s}(a + 0.98u) = e^{8 + 8a/0.98}(0.98/8)te^{-t} ≤ 160`
  have hkey : Real.exp (s * Lg) * (a + 2 * (49 / 100) * u) ≤ 160 := by
    set t := 8 * u + 8 * a / (98 / 100) with htdef
    have hte : t * Real.exp (-t) ≤ Real.exp (-1) := by
      have h := Real.add_one_le_exp (t - 1)
      have e : Real.exp (t - 1) * Real.exp (-t) = Real.exp (-1) := by
        rw [← Real.exp_add]
        ring_nf
      calc t * Real.exp (-t) ≤ Real.exp (t - 1) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = Real.exp (-1) := e
    have hsL : Real.exp (s * Lg) ≤ Real.exp (s * 8) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hLg hs0)
    have e1 : Real.exp (s * 8) * (a + 2 * (49 / 100) * u)
        = Real.exp (8 + 8 * a / (98 / 100)) * (98 / 100 / 8) * (t * Real.exp (-t)) := by
      have hsplit : Real.exp (s * 8)
          = Real.exp (8 + 8 * a / (98 / 100)) * Real.exp (-t) := by
        rw [← Real.exp_add, htdef, hudef]
        congr 1
        ring
      rw [hsplit, htdef]
      ring
    have hA : Real.exp (8 + 8 * a / (98 / 100))
        ≤ Real.exp (8 + 8 * (2 / 100 + 1 / 6000) / (98 / 100)) :=
      Real.exp_le_exp.2 (by linarith)
    have hnum : Real.exp (8 + 8 * (2 / 100 + 1 / 6000) / (98 / 100)) * (98 / 100 / 8)
        * Real.exp (-1) ≤ 160 := by
      interval_decide (trust := kernel)
    have ht0 : 0 ≤ t * Real.exp (-t) := by
      have : 0 ≤ t := by rw [htdef]; positivity
      exact mul_nonneg this (Real.exp_pos _).le
    have hpos : 0 ≤ a + 2 * (49 / 100) * u := by positivity
    calc Real.exp (s * Lg) * (a + 2 * (49 / 100) * u)
        ≤ Real.exp (s * 8) * (a + 2 * (49 / 100) * u) := mul_le_mul_of_nonneg_right hsL hpos
      _ = Real.exp (8 + 8 * a / (98 / 100)) * (98 / 100 / 8) * (t * Real.exp (-t)) := e1
      _ ≤ Real.exp (8 + 8 * (2 / 100 + 1 / 6000) / (98 / 100)) * (98 / 100 / 8)
          * Real.exp (-1) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hA (by norm_num)) hte ht0
            (mul_nonneg (Real.exp_pos _).le (by norm_num))
      _ ≤ 160 := hnum
  have hV : Λ⁻¹ + (1 - 2 * q) = a + 2 * (49 / 100) * u := by rw [hadef, hudef, hqs]; ring
  rw [hV]
  have hVpos : 0 < a + 2 * (49 / 100) * u := by positivity
  have hsL' : Real.exp (s * Lg) ≤ 160 * (a + 2 * (49 / 100) * u)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hVpos]
    exact hkey
  have e2 : (Lg - 49 / 100 / 2 * Real.log Λ) * s = s * Lg + -(q / 2) * Real.log Λ := by
    rw [hqs]; ring
  calc _ ≤ E0 ^ (q / (49 / 100)) := hL
    _ = E0 ^ s := rfl
    _ ≤ Real.exp ((Lg - 49 / 100 / 2 * Real.log Λ) * s) := h1
    _ = Real.exp (s * Lg) * Λ ^ (-(q / 2)) := by
        rw [e2, Real.exp_add, rpow_eq_exp_mul_log hΛp]
    _ ≤ 160 * (a + 2 * (49 / 100) * u)⁻¹ * Λ ^ (-(q / 2)) :=
        mul_le_mul_of_nonneg_right hsL' (Real.rpow_nonneg hΛp.le _)

/-! ### `Z` below `½` with one constant -/

/-- **`Z` for `w = (1 - 2q)Λ ≤ 23/2`**, Lyapunov from `½`: for `x ≥ exp(e^{110})` with
`Λ ≥ 2400` and `0 < q ≤ ½`, `E[Z^q] ≤ (E Z^{1/2})^{2q} ≤ (17.2Λ^{3/4})^{2q}
= (17.2Λ)^{2q}Λ^{-q/2}` (`RMF.integral_sqrt_Z_halfY_le`) and
`(17.2Λ)^{2q}(Λ⁻¹ + 1 - 2q) ≤ 17.2(1 + w) ≤ 215`. -/
theorem z_small_w {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) (hΛ : 2400 ≤ Real.log (Real.log x))
    (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hw : (1 - 2 * q) * Real.log (Real.log x) ≤ 23 / 2) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 215 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hlogy : 0 < Real.log (halfY x) := by linarith
  have hLya := integral_rpow_le_rpow_integral_rpow (μ := μ)
    (g := fun ω => (Real.log (halfY x))⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
          ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
        / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
    (r := 1 / 2) hq0 hq
    (fun ω => mul_nonneg (inv_nonneg.2 hlogy.le) (integral_nonneg fun t => sq_nonneg _))
    (integrable_rpow_eulerProductLine hX _ hσ (by norm_num))
    (integrable_rpow_eulerProductLine hX _ hσ hq0.le)
  have hH := integral_sqrt_Z_halfY_le hX hx hΛ
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛp : 0 < Λ := by linarith
  have hE0 : 0 ≤ ∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
          ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
        / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 hlogy.le) (integral_nonneg fun t => sq_nonneg _)) _
  have h2q : q / (1 / 2) = 2 * q := by ring
  rw [h2q] at hLya
  refine le_trans hLya (le_trans (Real.rpow_le_rpow hE0 hH (by linarith)) ?_)
  -- `(17.2Λ^{3/4})^{2q} = (17.2Λ)^{2q}·Λ^{-q/2}`
  have e : (172 / 10 * Λ ^ (3 / 4 : ℝ)) ^ (2 * q) = (172 / 10 * Λ) ^ (2 * q) * Λ ^ (-(q / 2)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hΛp.le _),
      Real.mul_rpow (by norm_num) hΛp.le, ← Real.rpow_mul hΛp.le, mul_assoc,
      ← Real.rpow_add hΛp]
    congr 2
    ring
  rw [e]
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by have := inv_pos.2 hΛp; linarith
  have hΛq : 0 < Λ ^ (-(q / 2)) := Real.rpow_pos_of_pos hΛp _
  -- `(17.2Λ)^{2q}V ≤ 17.2ΛV = 17.2(1 + w) ≤ 215`
  have hkey : (172 / 10 * Λ) ^ (2 * q) * V ≤ 215 := by
    have h1 : (1 : ℝ) ≤ 172 / 10 * Λ := by linarith
    have ha : (172 / 10 * Λ) ^ (2 * q) ≤ 172 / 10 * Λ := by
      calc (172 / 10 * Λ) ^ (2 * q) ≤ (172 / 10 * Λ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = 172 / 10 * Λ := Real.rpow_one _
    have e2 : 172 / 10 * Λ * V = 172 / 10 + 172 / 10 * ((1 - 2 * q) * Λ) := by
      rw [hVdef]; field_simp
    calc (172 / 10 * Λ) ^ (2 * q) * V ≤ 172 / 10 * Λ * V := mul_le_mul_of_nonneg_right ha hV0.le
      _ ≤ 215 := by rw [e2]; linarith
  calc (172 / 10 * Λ) ^ (2 * q) * Λ ^ (-(q / 2))
      = (172 / 10 * Λ) ^ (2 * q) * V * (V⁻¹ * Λ ^ (-(q / 2))) := by field_simp
    _ ≤ 215 * (V⁻¹ * Λ ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_right hkey (mul_nonneg (inv_pos.2 hV0).le hΛq.le)
    _ = 215 * V⁻¹ * Λ ^ (-(q / 2)) := by ring

/-- **`Z` below `½` with one constant**: for `x ≥ exp(e^{110})` with `Λ = log log x ≥ 6000` and
`0 < q < ½`, `E[Z^q] ≤ 215(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, `Z` at `(halfY x, halfSigma x)`: for
`q ≤ 0.49` the descent from the anchor at `q = 0.49` (`w = Λ/50 ≥ 120`, `RMF.z_cell_half_anchor`,
`RMF.z_descent`: `160`), above it Lyapunov from `½` for `w ≤ 23/2` (`RMF.z_small_w`) and the cell
`RMF.z_cell_half_top` for `w ≥ 23/2`. -/
theorem integral_rpow_Z_halfY_le_belowHalf {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hq0 : 0 < q) (hq : q < 1 / 2) :
    (∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 215 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨-, hL, -, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hlogy : 0 < Real.log (halfY x) := by linarith
  have hΛp : 0 < Real.log (Real.log x) := by linarith
  rcases le_or_gt q (49 / 100) with h49 | h49
  · -- the descent from the anchor
    have hanc := z_cell_half_anchor hX hx hΛ (le_refl (49 / 100 : ℝ)) (by norm_num)
      (by linarith)
    have hd := z_descent (μ := μ)
      (g := fun ω => (Real.log (halfY x))⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
            ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
          / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (fun ω => mul_nonneg (inv_nonneg.2 hlogy.le) (integral_nonneg fun t => sq_nonneg _))
      (fun r hr => integrable_rpow_eulerProductLine hX _ hσ hr) hΛ hq0 h49 hanc
    refine le_trans hd ?_
    have hV : 0 < (Real.log (Real.log x))⁻¹ + (1 - 2 * q) := by
      have := inv_pos.2 hΛp; linarith
    have h0 : 0 ≤ ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) :=
      mul_nonneg (inv_pos.2 hV).le (Real.rpow_nonneg hΛp.le _)
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by norm_num) h0
  · rcases le_or_gt ((1 - 2 * q) * Real.log (Real.log x)) (23 / 2) with hw | hw
    · exact z_small_w hX hx (by linarith) hq0 hq.le hw
    · exact z_cell_half_top hX hx hΛ h49.le hq hw.le

/-! ### The subtracted term -/

/-- `x ≥ exp(e^{110})` from `x > 1` and `log log x ≥ 110`. -/
lemma exp_exp_le_of_one_lt {x : ℝ} (hx : 1 < x) (hΛ : 110 ≤ Real.log (Real.log x)) :
    Real.exp (Real.exp 110) ≤ x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have h1 : Real.exp 110 ≤ Real.log x := (Real.le_log_iff_exp_le hL).1 hΛ
  exact (Real.le_log_iff_exp_le hx0).1 h1

/-- **The band's Mertens factor at the ends**: `mBand(halfY x, ⌊x⌋)·log(halfY x) ≤ e^{1/1000}log x`
for `x ≥ exp(e^{110})`: it is `log⌊x⌋·e^{9.0028(1/log y + 1/log⌊x⌋)}` with `log y ≥ 22000`. -/
lemma mBand_halfY_floor_mul_log_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    mBand (halfY x) ⌊x⌋₊ * Real.log (halfY x) ≤ Real.exp (1 / 1000) * Real.log x := by
  obtain ⟨hx0, -, -, -, -, -⟩ := half_params hx
  obtain ⟨hy2, hyx, -, -, -, -⟩ := halfY_facts hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hyN : halfY x ≤ ⌊x⌋₊ := Nat.le_floor hyx
  have hlogy : 0 < Real.log (halfY x) := by linarith
  have hy0 : (0 : ℝ) < (halfY x : ℝ) := by
    have : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
    linarith
  have hNy : (halfY x : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hyN
  have hlogN : Real.log (halfY x) ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_le_log hy0 hNy
  have hlogNx : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (lt_of_lt_of_le hy0 hNy) (Nat.floor_le hx0.le)
  have hexp : 9.0028 / Real.log (halfY x) + 9.0028 / Real.log (⌊x⌋₊ : ℝ) ≤ 1 / 1000 := by
    have h1 : 9.0028 / Real.log (halfY x) ≤ 9.0028 / 22000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
    have h2 : 9.0028 / Real.log (⌊x⌋₊ : ℝ) ≤ 9.0028 / 22000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_trans hly hlogN)
    linarith
  unfold mBand
  calc Real.log (⌊x⌋₊ : ℝ) / Real.log (halfY x)
        * Real.exp (9.0028 / Real.log (halfY x) + 9.0028 / Real.log (⌊x⌋₊ : ℝ))
        * Real.log (halfY x)
      = Real.log (⌊x⌋₊ : ℝ)
        * Real.exp (9.0028 / Real.log (halfY x) + 9.0028 / Real.log (⌊x⌋₊ : ℝ)) := by
        field_simp
    _ ≤ Real.log x * Real.exp (1 / 1000) :=
        mul_le_mul hlogNx (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le
          (by linarith)
    _ = Real.exp (1 / 1000) * Real.log x := by ring

set_option maxHeartbeats 1000000 in
-- four reductions of the subtracted term to `Z`
/-- **The subtracted term reduced to `Z`**: for a Rademacher family, `x > 1` with
`Λ = log log x ≥ 6000`, `V ≥ 1/32` and `0 < q ≤ ½`,
`E[J(V/log x)^q] ≤ e^{q/1000}(log x)^q·E[Z^q]`, `Z` at `(halfY x, halfSigma x)`: the shift down to
`halfSigma x = (1/32)/log x` (`RMF.integral_rpow_lineDiv_le_of_le`), the high primes integrated
out (`RMF.integral_rpow_lineDiv_le_mBand_rpow_mul`) and `RMF.mBand_halfY_floor_mul_log_le`. -/
theorem integral_rpow_lineDiv_le_Z_halfY {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : 1 < x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hV : 1 / 32 ≤ V) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ Real.exp (q / 1000) * Real.log x ^ q
        * ∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
              ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
            / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hxe := exp_exp_le_of_one_lt hx (by linarith)
  obtain ⟨hx0, hL, -, -, -, -⟩ := half_params hxe
  obtain ⟨hy2, hyx, -, -, -, -⟩ := halfY_facts hxe
  obtain ⟨-, hly⟩ := halfY_loglog_le hxe
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
  have hlogy : 0 < Real.log (halfY x) := by linarith
  have hyN : halfY x ≤ ⌊x⌋₊ := Nat.le_floor hyx
  have hN2 : 2 ≤ ⌊x⌋₊ := le_trans hy2 hyN
  -- the shift down to `halfSigma x`
  have hσV : halfSigma x ≤ V / Real.log x := by
    rw [halfSigma]
    exact div_le_div_of_nonneg_right hV hLpos.le
  have h1 := integral_rpow_lineDiv_le_of_le hX (N := ⌊x⌋₊) hN2 hσ hσV hq0.le
  -- the high primes integrated out
  have h2 := integral_rpow_lineDiv_le_mBand_rpow_mul hX hy2 hyN hσ hq0.le (by linarith)
  -- the normalisation `Z = (log y)⁻¹J_y`
  have h3 := integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
    (J := fun ω => ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
          ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
        / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
    hlogy le_rfl hq0.le (fun ω => integral_nonneg fun t => sq_nonneg _)
  -- the Mertens factor
  have hm0 : 0 ≤ mBand (halfY x) ⌊x⌋₊ := by
    unfold mBand
    have hN0 : 0 ≤ Real.log (⌊x⌋₊ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hN2 : 1 ≤ ⌊x⌋₊))
    positivity
  have hmq : mBand (halfY x) ⌊x⌋₊ ^ q * Real.log (halfY x) ^ q
      ≤ Real.exp (q / 1000) * Real.log x ^ q := by
    rw [← Real.mul_rpow hm0 hlogy.le]
    calc (mBand (halfY x) ⌊x⌋₊ * Real.log (halfY x)) ^ q
        ≤ (Real.exp (1 / 1000) * Real.log x) ^ q :=
          Real.rpow_le_rpow (mul_nonneg hm0 hlogy.le) (mBand_halfY_floor_mul_log_le hxe) hq0.le
      _ = Real.exp (q / 1000) * Real.log x ^ q := by
          rw [Real.mul_rpow (Real.exp_pos _).le hLpos.le, ← Real.exp_mul]
          congr 2
          ring
  have hZ0 : 0 ≤ ∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
          ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
        / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 hlogy.le) (integral_nonneg fun t => sq_nonneg _)) _
  have hmq0 : 0 ≤ mBand (halfY x) ⌊x⌋₊ ^ q := Real.rpow_nonneg hm0 _
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ mBand (halfY x) ⌊x⌋₊ ^ q * (Real.log (halfY x) ^ q
          * ∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
                ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
              / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ) :=
        mul_le_mul_of_nonneg_left h3 hmq0
    _ = mBand (halfY x) ⌊x⌋₊ ^ q * Real.log (halfY x) ^ q
          * ∫ ω, ((Real.log (halfY x))⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (halfY x + 1)
                ((1 / 2 : ℂ) + (halfSigma x : ℂ) + (t : ℂ) * Complex.I) ω
              / ((halfSigma x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmq hZ0

/-- **The subtracted term below `½`**: for a Rademacher family, `x > 1` with
`Λ = log log x ≥ 6000`, `V ≥ 1/32` and `0 < q < ½`,

`E[J(V/log x)^q] ≤ 216(log x)^q·min{Λ, (1-2q)⁻¹}·Λ^{-q/2}`,

`J(σ) = ∫_ℝ‖F_{⌊x⌋+1}(½+σ+it)/(σ+it)‖²dt` as in
`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`:
`RMF.integral_rpow_lineDiv_le_Z_halfY`, `RMF.integral_rpow_Z_halfY_le_belowHalf` (`215`) and
`215e^{1/2000} ≤ 216`. -/
theorem integral_rpow_lineDiv_le_subtracted_belowHalf {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : 1 < x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hV : 1 / 32 ≤ V) (hq0 : 0 < q) (hq : q < 1 / 2) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 216 * Real.log x ^ q * min (Real.log (Real.log x)) (1 - 2 * q)⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  have hxe := exp_exp_le_of_one_lt hx (by linarith)
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hΛp : 0 < Real.log (Real.log x) := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  have h1 := integral_rpow_lineDiv_le_Z_halfY hX hx hΛ hV hq0 hq.le
  have h2 := integral_rpow_Z_halfY_le_belowHalf hX hxe hΛ hq0 hq
  set Λ := Real.log (Real.log x) with hΛdef
  set V' := Λ⁻¹ + (1 - 2 * q) with hV'def
  have hV'0 : 0 < V' := by have := inv_pos.2 hΛp; linarith
  -- `(Λ⁻¹ + 1 - 2q)⁻¹ ≤ min{Λ, (1-2q)⁻¹}`
  have hmin : V'⁻¹ ≤ min Λ (1 - 2 * q)⁻¹ := by
    refine le_min ?_ (inv_anti₀ hv0 (by have := inv_pos.2 hΛp; linarith))
    calc V'⁻¹ ≤ (Λ⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hΛp) (by linarith)
      _ = Λ := inv_inv Λ
  have hexp : Real.exp (q / 1000) * 215 ≤ 216 := by
    have h : Real.exp (q / 1000) ≤ Real.exp (1 / 2000) := Real.exp_le_exp.2 (by linarith)
    have h' : Real.exp (1 / 2000) ≤ 216 / 215 := by interval_decide (trust := kernel)
    linarith
  have hLq : 0 ≤ Real.log x ^ q := Real.rpow_nonneg hLpos.le _
  have hΛq : 0 ≤ Λ ^ (-(q / 2)) := Real.rpow_nonneg hΛp.le _
  have hE : 0 ≤ Real.exp (q / 1000) * Real.log x ^ q := mul_nonneg (Real.exp_pos _).le hLq
  calc _ ≤ _ := h1
    _ ≤ Real.exp (q / 1000) * Real.log x ^ q * (215 * V'⁻¹ * Λ ^ (-(q / 2))) :=
        mul_le_mul_of_nonneg_left h2 hE
    _ = Real.exp (q / 1000) * 215 * Real.log x ^ q * (V'⁻¹ * Λ ^ (-(q / 2))) := by ring
    _ ≤ 216 * Real.log x ^ q * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hexp hLq)
          (mul_le_mul_of_nonneg_right hmin hΛq)
          (mul_nonneg (inv_pos.2 hV'0).le hΛq) (by positivity)
    _ = 216 * Real.log x ^ q * min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)) := by ring

/-- **The subtracted term at `q = ½`**: for a Rademacher family, `x > 1` with
`Λ = log log x ≥ 6000` and `V ≥ 1/32`,

`E[J(V/log x)^{1/2}] ≤ 17.3(log x)^{1/2}Λ^{3/4}`,

`J` as in `RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`:
`RMF.integral_rpow_lineDiv_le_Z_halfY`, `RMF.integral_sqrt_Z_halfY_le` (`17.2`) and
`17.2e^{1/2000} ≤ 17.3`. -/
theorem integral_sqrt_lineDiv_le_subtracted_half {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V : ℝ} (hx : 1 < x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hV : 1 / 32 ≤ V) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
      ≤ 173 / 10 * Real.log x ^ (1 / 2 : ℝ) * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have hxe := exp_exp_le_of_one_lt hx (by linarith)
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have h1 := integral_rpow_lineDiv_le_Z_halfY hX hx hΛ hV (q := 1 / 2) (by norm_num) le_rfl
  have h2 := integral_sqrt_Z_halfY_le hX hxe (by linarith)
  have hexp : Real.exp ((1 / 2 : ℝ) / 1000) * (172 / 10) ≤ 173 / 10 := by
    have h' : Real.exp ((1 / 2 : ℝ) / 1000) ≤ 173 / 172 := by interval_decide (trust := kernel)
    linarith
  have hLq : 0 ≤ Real.log x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hΛq : 0 ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hE : 0 ≤ Real.exp ((1 / 2 : ℝ) / 1000) * Real.log x ^ (1 / 2 : ℝ) :=
    mul_nonneg (Real.exp_pos _).le hLq
  calc _ ≤ _ := h1
    _ ≤ Real.exp ((1 / 2 : ℝ) / 1000) * Real.log x ^ (1 / 2 : ℝ)
          * (172 / 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 hE
    _ = Real.exp ((1 / 2 : ℝ) / 1000) * (172 / 10) * Real.log x ^ (1 / 2 : ℝ)
          * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by ring
    _ ≤ 173 / 10 * Real.log x ^ (1 / 2 : ℝ) * Real.log (Real.log x) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hLq) hΛq

end RMF
