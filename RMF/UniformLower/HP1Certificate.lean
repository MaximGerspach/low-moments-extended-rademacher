/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.GaussianHP1V2
import LeanCert.Tactic.IntervalAuto
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# HP1's per-cell certificate, analysis

What makes a numerical certificate a proof of `RMF.hp1LowerBoundV2 ≥ p₁` on a cell of `ϑ`:

* **`Φ`.**  `RMF.normCDF`, bounded by the alternating Taylor polynomials of `e^{-t²/2}`,
  integrated (`RMF.le_normCDF_of_poly`, `RMF.normCDF_le_of_poly`).
* **The exit expectation** `RMF.exitMean = E[RMF.hp1ExitV2(m + N(0, R))]`: a lower bound at any
  threshold (`RMF.le_exitMean`), antitone in `m`, and Lipschitz in `R` from below with constant
  `t²(1 - e^{-A_W})/2` (`RMF.exitMean_sub_le`).
* **The main term by a lower sum** over nodes of the standardised height `U/√V`, with the exact
  normal mass and first moment of each cell (`RMF.sum_le_startMainV2`).
* **The other terms at their worst case** over the data ranges (`RMF.hp1LowerBoundV2_ge`), and
  `RMF.hp1Slope`, `RMF.hp1Loss` by bounds on their atoms.
* **One cell per point inequality** (`RMF.cell_le`), at the nodes `RMF.sampleNodes`.

The residual variance's range is paid by the one-sided Lipschitz bound (the exit expectation is not
monotone in `R`), and the density is integrated exactly after `u = √Vz`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace RMF

/-! ### The standard normal distribution function -/

/-- The standard normal distribution function `Φ(z) = P(N(0, 1) ≤ z)`. -/
noncomputable def normCDF (z : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic z)

/-- The standard normal density, `e^{-z²/2}/√(2π)`. -/
lemma gaussianPDFReal_zero_one (z : ℝ) :
    gaussianPDFReal 0 1 z = (√(2 * π))⁻¹ * Real.exp (-(z ^ 2 / 2)) := by
  rw [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, mul_one, neg_div]

lemma normCDF_eq_integral (z : ℝ) : normCDF z = ∫ t in Set.Iic z, gaussianPDFReal 0 1 t := by
  rw [normCDF, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      fun t _ => gaussianPDFReal_nonneg 0 1 t)]

/-- `Φ(0) = 1/2`: the standard normal law is symmetric and has no atom at `0`. -/
lemma normCDF_zero : normCDF 0 = 1 / 2 := by
  set P := gaussianReal 0 1 with hP
  have hmap : P.map (fun x : ℝ => -x) = P := by rw [hP, gaussianReal_map_neg, neg_zero]
  have hsymm : P.real (Set.Iic (0 : ℝ)) = P.real (Set.Ici (0 : ℝ)) := by
    have h : P (Set.Iic (0 : ℝ)) = P (Set.Ici (0 : ℝ)) := by
      calc P (Set.Iic (0 : ℝ))
          = (P.map (fun x : ℝ => -x)) (Set.Ici (0 : ℝ)) := by
            rw [Measure.map_apply measurable_neg measurableSet_Ici]
            congr 1
            ext x
            simp
        _ = P (Set.Ici (0 : ℝ)) := by rw [hmap]
    rw [measureReal_def, measureReal_def, h]
  have hatom : P.real {(0 : ℝ)} = 0 := by
    rw [measureReal_def, hP, gaussianReal_apply _ one_ne_zero]
    simp
  have hIci : P.real (Set.Ici (0 : ℝ)) = P.real (Set.Ioi (0 : ℝ)) := by
    rw [← Set.Ioi_insert, Set.insert_eq,
      measureReal_union (Set.disjoint_singleton_left.2 Set.self_notMem_Ioi) measurableSet_Ioi,
      hatom, zero_add]
  have hcompl : P.real (Set.Ioi (0 : ℝ)) = 1 - P.real (Set.Iic (0 : ℝ)) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [normCDF, ← hP]
  linarith

/-- `Φ(z) = 1/2 + (2π)^{-1/2}∫₀^z e^{-t²/2} dt`. -/
lemma normCDF_eq_half_add (z : ℝ) :
    normCDF z = 1 / 2 + (√(2 * π))⁻¹ * ∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2)) := by
  have h := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := gaussianPDFReal 0 1)
    (a := 0) (b := z) (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn
  rw [← normCDF_eq_integral, ← normCDF_eq_integral, normCDF_zero] at h
  have e : ∫ t in (0 : ℝ)..z, gaussianPDFReal 0 1 t
      = (√(2 * π))⁻¹ * ∫ t in (0 : ℝ)..z, Real.exp (-(t ^ 2 / 2)) := by
    simp_rw [gaussianPDFReal_zero_one]
    exact intervalIntegral.integral_const_mul _ _
  linarith

/-- A centred Gaussian's distribution function, by `Φ`. -/
lemma gaussianReal_real_Iic_eq_normCDF {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal 0 v).real (Set.Iic x) = normCDF (x / √(v : ℝ)) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [← gaussianReal_map_sqrt_mul v, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    normCDF]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hs, mul_comm]

lemma normCDF_mono : Monotone normCDF := fun _ _ h =>
  measureReal_mono (Set.Iic_subset_Iic.2 h)

lemma normCDF_nonneg (z : ℝ) : 0 ≤ normCDF z := measureReal_nonneg

lemma normCDF_le_one (z : ℝ) : normCDF z ≤ 1 := measureReal_le_one

/-- The standard normal mass of `(x, y]` is `Φ(y) - Φ(x)`. -/
lemma measureReal_Ioc_eq_normCDF_sub {x y : ℝ} (hxy : x ≤ y) :
    (gaussianReal 0 1).real (Set.Ioc x y) = normCDF y - normCDF x := by
  rw [normCDF, normCDF, ← measureReal_sdiff (Set.Iic_subset_Iic.2 hxy) measurableSet_Iic]
  congr 1
  ext z
  simp only [Set.mem_Ioc, Set.mem_sdiff, Set.mem_Iic, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ### Rational bounds for `Φ`

`Φ` is bracketed by Taylor's polynomials of `e^{-t²/2}`, whose partial sums alternate around it,
integrated: `RMF.gaussPoly`, evaluated by `norm_num`. -/

/-- Taylor's polynomial of `e^{-s}` of degree `n`. -/
noncomputable def expNegTaylor (n : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (-s) ^ k / (k.factorial : ℝ)

lemma expNegTaylor_zero_right (n : ℕ) : expNegTaylor n 0 = 1 := by
  rw [expNegTaylor, Finset.sum_range_succ']
  simp

lemma continuous_expNegTaylor (n : ℕ) : Continuous (expNegTaylor n) := by
  unfold expNegTaylor
  fun_prop

lemma hasDerivAt_expNegTaylor_succ (n : ℕ) (s : ℝ) :
    HasDerivAt (expNegTaylor (n + 1)) (-expNegTaylor n s) s := by
  have h : HasDerivAt (fun s => ∑ k ∈ Finset.range (n + 1 + 1), (-s) ^ k / (k.factorial : ℝ))
      (∑ k ∈ Finset.range (n + 1 + 1), (k : ℝ) * (-s) ^ (k - 1) * (-1) / (k.factorial : ℝ)) s :=
    HasDerivAt.fun_sum fun k _ => ((hasDerivAt_neg' s).fun_pow k).div_const _
  have e : expNegTaylor (n + 1)
      = fun s => ∑ k ∈ Finset.range (n + 1 + 1), (-s) ^ k / (k.factorial : ℝ) := rfl
  rw [e]
  convert h using 1
  rw [Finset.sum_range_succ', expNegTaylor, ← Finset.sum_neg_distrib]
  simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
  push_cast
  field_simp

/-- A function vanishing at `0` with a nonnegative derivative on `[0, ∞)` is nonnegative there. -/
lemma nonneg_of_hasDerivAt_of_nonneg {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : ∀ x, 0 ≤ x → 0 ≤ F' x) (h0 : F 0 = 0) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ F s := by
  have hmono : MonotoneOn F (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hF x).continuousAt.continuousWithinAt)
      (fun x _ => (hF x).differentiableAt.differentiableWithinAt) (fun x hx => by
        rw [interior_Ici] at hx
        rw [(hF x).deriv]
        exact hF' x (le_of_lt hx))
  have := hmono Set.self_mem_Ici (Set.mem_Ici.2 hs) hs
  linarith

/-- **Taylor's polynomials of `e^{-s}` alternate around it** on `s ≥ 0`:
`(-1)^{n+1}(e^{-s} - T_n(s)) ≥ 0`. -/
theorem expNegTaylor_alternating (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (-1) ^ (n + 1) * (Real.exp (-s) - expNegTaylor n s) := by
  induction n generalizing s with
  | zero =>
    have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : expNegTaylor 0 s = 1 := by simp [expNegTaylor]
    rw [h2, zero_add, pow_one]
    linarith
  | succ n ih =>
    refine nonneg_of_hasDerivAt_of_nonneg
      (F := fun s => (-1) ^ (n + 1 + 1) * (Real.exp (-s) - expNegTaylor (n + 1) s))
      (F' := fun s => (-1) ^ (n + 1) * (Real.exp (-s) - expNegTaylor n s)) (fun x => ?_)
      (fun x hx => ih hx) ?_ hs
    · have h1 : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-x)) x := by
        simpa using (hasDerivAt_neg x).exp
      have h2 := (h1.sub (hasDerivAt_expNegTaylor_succ n x)).const_mul ((-1 : ℝ) ^ (n + 1 + 1))
      exact h2.congr_deriv (by ring)
    · simp [expNegTaylor_zero_right]

lemma exp_neg_le_expNegTaylor_even (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s) ≤ expNegTaylor (2 * n) s := by
  have h := expNegTaylor_alternating (2 * n) hs
  rw [pow_succ, pow_mul] at h
  norm_num at h
  linarith

lemma expNegTaylor_odd_le_exp_neg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    expNegTaylor (2 * n + 1) s ≤ Real.exp (-s) := by
  have h := expNegTaylor_alternating (2 * n + 1) hs
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul] at h
  norm_num at h
  linarith

/-- `∫₀^q T_j(t²/2) dt = Σ_{k≤j} (-1/2)^k q^{2k+1}/((2k+1)k!)`. -/
noncomputable def gaussPoly (j : ℕ) (q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), (-1 / 2 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1) * (k.factorial : ℝ))

lemma integral_expNegTaylor_sq (j : ℕ) (q : ℝ) :
    ∫ t in (0 : ℝ)..q, expNegTaylor j (t ^ 2 / 2) = gaussPoly j q := by
  simp only [expNegTaylor]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun t : ℝ => (-(t ^ 2 / 2)) ^ k / (k.factorial : ℝ)
      ).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ t : ℝ, (-(t ^ 2 / 2)) ^ k / (k.factorial : ℝ)
      = ((-1 / 2) ^ k / (k.factorial : ℝ)) * t ^ (2 * k) := by
    intro t
    rw [pow_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

lemma gaussPoly_neg (j : ℕ) (q : ℝ) : gaussPoly j (-q) = -gaussPoly j q := by
  rw [gaussPoly, gaussPoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Odd.neg_pow ⟨k, rfl⟩]
  ring

lemma integral_exp_neg_sq_half_neg (q : ℝ) :
    ∫ t in (0 : ℝ)..(-q), Real.exp (-(t ^ 2 / 2))
      = -∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := q)
    (fun t : ℝ => Real.exp (-(t ^ 2 / 2)))
  simp only [neg_sq, neg_zero] at h
  rw [h, intervalIntegral.integral_symm 0 (-q), neg_neg]

lemma gaussPoly_odd_le_integral {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    gaussPoly (2 * n + 1) q ≤ ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) := by
  rw [← integral_expNegTaylor_sq]
  exact intervalIntegral.integral_mono_on hq
    (((continuous_expNegTaylor _).comp (by fun_prop)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t ^ 2 / 2))).intervalIntegrable _ _)
    fun t _ => expNegTaylor_odd_le_exp_neg n (by positivity)

lemma integral_le_gaussPoly_even {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) ≤ gaussPoly (2 * n) q := by
  rw [← integral_expNegTaylor_sq]
  exact intervalIntegral.integral_mono_on hq
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t ^ 2 / 2))).intervalIntegrable _ _)
    (((continuous_expNegTaylor _).comp (by fun_prop)).intervalIntegrable _ _)
    fun t _ => exp_neg_le_expNegTaylor_even n (by positivity)

/-- `0.3989422804 ≤ (2π)^{-1/2} ≤ 0.3989422805`. -/
lemma inv_sqrt_two_pi_bounds :
    (0.3989422804 : ℝ) ≤ (√(2 * π))⁻¹ ∧ (√(2 * π))⁻¹ ≤ 0.3989422805 := by
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  have hs0 : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have hup : √(2 * π) ≤ 2.506628274632 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hlo : 2.50662827463 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  constructor
  · rw [le_inv_comm₀ (by norm_num) hs0]
    refine le_trans hup ?_
    norm_num
  · rw [inv_le_comm₀ hs0 (by norm_num)]
    refine le_trans ?_ hlo
    norm_num

/-- **`Φ` from below on `q ≥ 0`**, by the odd Taylor polynomial. -/
lemma le_normCDF_of_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) {b : ℝ}
    (hP : 0 ≤ gaussPoly (2 * n + 1) q)
    (hb : b ≤ 1 / 2 + 0.3989422804 * gaussPoly (2 * n + 1) q) :
    b ≤ normCDF q := by
  rw [normCDF_eq_half_add]
  have h1 := gaussPoly_odd_le_integral hq n
  have h2 := inv_sqrt_two_pi_bounds.1
  have h3 : 0.3989422804 * gaussPoly (2 * n + 1) q
      ≤ (√(2 * π))⁻¹ * ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) :=
    mul_le_mul h2 h1 hP (by linarith)
  linarith

/-- **`Φ` from above on `q ≥ 0`**, by the even Taylor polynomial. -/
lemma normCDF_le_of_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) {b : ℝ}
    (hb : 1 / 2 + 0.3989422805 * gaussPoly (2 * n) q ≤ b) :
    normCDF q ≤ b := by
  rw [normCDF_eq_half_add]
  have h1 := integral_le_gaussPoly_even hq n
  have h2 := inv_sqrt_two_pi_bounds.2
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) :=
    intervalIntegral.integral_nonneg hq fun t _ => (Real.exp_pos _).le
  have h3 : (√(2 * π))⁻¹ * ∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2))
      ≤ 0.3989422805 * gaussPoly (2 * n) q :=
    mul_le_mul h2 h1 h0 (by norm_num)
  linarith

/-- **`Φ` from below on `q ≤ 0`**, by the even Taylor polynomial at `-q`. -/
lemma le_normCDF_of_nonpos {q : ℝ} (hq : q ≤ 0) (n : ℕ) {b : ℝ}
    (hb : b ≤ 1 / 2 + 0.3989422805 * gaussPoly (2 * n) q) :
    b ≤ normCDF q := by
  rw [normCDF_eq_half_add]
  have h1 := integral_le_gaussPoly_even (neg_nonneg.2 hq) n
  rw [integral_exp_neg_sq_half_neg, gaussPoly_neg] at h1
  have h2 := inv_sqrt_two_pi_bounds
  have h0 : 0 ≤ -∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) := by
    rw [← integral_exp_neg_sq_half_neg]
    exact intervalIntegral.integral_nonneg (by linarith) fun t _ => (Real.exp_pos _).le
  have h3 : (√(2 * π))⁻¹ * -∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2))
      ≤ 0.3989422805 * -gaussPoly (2 * n) q :=
    mul_le_mul h2.2 (by linarith) h0 (by norm_num)
  linarith

/-- **`Φ` from above on `q ≤ 0`**, by the odd Taylor polynomial at `-q`. -/
lemma normCDF_le_of_nonpos {q : ℝ} (hq : q ≤ 0) (n : ℕ) {b : ℝ}
    (hP : gaussPoly (2 * n + 1) q ≤ 0)
    (hb : 1 / 2 + 0.3989422804 * gaussPoly (2 * n + 1) q ≤ b) :
    normCDF q ≤ b := by
  rw [normCDF_eq_half_add]
  have h1 := gaussPoly_odd_le_integral (neg_nonneg.2 hq) n
  rw [integral_exp_neg_sq_half_neg, gaussPoly_neg] at h1
  have h2 := inv_sqrt_two_pi_bounds
  have h3 : 0.3989422804 * -gaussPoly (2 * n + 1) q
      ≤ (√(2 * π))⁻¹ * -∫ t in (0 : ℝ)..q, Real.exp (-(t ^ 2 / 2)) :=
    mul_le_mul h2.1 h1 (by linarith) (by linarith)
  linarith

/-- **`Φ` from below by a Taylor polynomial**, either sign of `q`: the two cases of
`RMF.le_normCDF_of_nonneg` and `RMF.le_normCDF_of_nonpos`, for one `norm_num` call. -/
lemma le_normCDF_of_poly {q b : ℝ} (n : ℕ)
    (h : (0 ≤ q ∧ 0 ≤ gaussPoly (2 * n + 1) q
        ∧ b ≤ 1 / 2 + 0.3989422804 * gaussPoly (2 * n + 1) q)
      ∨ (q ≤ 0 ∧ b ≤ 1 / 2 + 0.3989422805 * gaussPoly (2 * n) q)) :
    b ≤ normCDF q := by
  rcases h with ⟨hq, hP, hb⟩ | ⟨hq, hb⟩
  · exact le_normCDF_of_nonneg hq n hP hb
  · exact le_normCDF_of_nonpos hq n hb

/-- **`Φ` from above by a Taylor polynomial**, either sign of `q`. -/
lemma normCDF_le_of_poly {q b : ℝ} (n : ℕ)
    (h : (0 ≤ q ∧ 1 / 2 + 0.3989422805 * gaussPoly (2 * n) q ≤ b)
      ∨ (q ≤ 0 ∧ gaussPoly (2 * n + 1) q ≤ 0
        ∧ 1 / 2 + 0.3989422804 * gaussPoly (2 * n + 1) q ≤ b)) :
    normCDF q ≤ b := by
  rcases h with ⟨hq, hb⟩ | ⟨hq, hP, hb⟩
  · exact normCDF_le_of_nonneg hq n hb
  · exact normCDF_le_of_nonpos hq n hP hb

/-! ### The exit expectation -/

/-- **The exit expectation** `E[RMF.hp1ExitV2(m + Y)]`, `Y ~ N(0, R)`: the inner integral of
`RMF.startMainV2` at the location `m`. -/
noncomputable def exitMean (t L ρ Λ AW m R : ℝ) : ℝ :=
  ∫ y, hp1ExitV2 t L ρ Λ AW (m + y) ∂(gaussianReal 0 R.toNNReal)

lemma antitone_hp1ExitV2 {t : ℝ} (ht : 0 ≤ t) (L ρ Λ AW : ℝ) :
    Antitone (hp1ExitV2 t L ρ Λ AW) := by
  intro x y hxy
  unfold hp1ExitV2
  refine max_le_max_right _ ?_
  have : Real.exp (t * (x + L + ρ) + Λ) ≤ Real.exp (t * (y + L + ρ) + Λ) :=
    Real.exp_le_exp.2 (by nlinarith)
  linarith

lemma integrable_hp1ExitV2_comp (μ : Measure ℝ) [IsFiniteMeasure μ] (t L ρ Λ AW c : ℝ) :
    Integrable (fun y => hp1ExitV2 t L ρ Λ AW (c + y)) μ :=
  Integrable.of_bound (((measurable_hp1ExitV2 t L ρ Λ AW).comp
    (measurable_const.add measurable_id)).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp1ExitV2_nonneg _ _ _ _ _ _)]
      exact hp1ExitV2_le_one _ _ _ _ _ _)

lemma exitMean_nonneg (t L ρ Λ AW m R : ℝ) : 0 ≤ exitMean t L ρ Λ AW m R :=
  integral_nonneg fun _ => hp1ExitV2_nonneg _ _ _ _ _ _

lemma exitMean_le_one (t L ρ Λ AW m R : ℝ) : exitMean t L ρ Λ AW m R ≤ 1 := by
  unfold exitMean
  calc ∫ y, hp1ExitV2 t L ρ Λ AW (m + y) ∂(gaussianReal 0 R.toNNReal)
      ≤ ∫ _y, (1 : ℝ) ∂(gaussianReal 0 R.toNNReal) :=
        integral_mono (integrable_hp1ExitV2_comp _ _ _ _ _ _ _) (integrable_const _)
          fun y => hp1ExitV2_le_one _ _ _ _ _ _
    _ = 1 := by simp

/-- The exit expectation is antitone in the location. -/
lemma exitMean_antitone {t : ℝ} (ht : 0 ≤ t) (L ρ Λ AW R : ℝ) :
    Antitone fun m => exitMean t L ρ Λ AW m R := fun _ _ hmm =>
  integral_mono (integrable_hp1ExitV2_comp _ _ _ _ _ _ _)
    (integrable_hp1ExitV2_comp _ _ _ _ _ _ _)
    fun y => antitone_hp1ExitV2 ht L ρ Λ AW (by linarith)

/-- A Gaussian measure's value on a set as the integral of its density. -/
lemma gaussianReal_real_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    (gaussianReal μ v).real s = ∫ x in s, gaussianPDFReal μ v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ hv,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun x =>
      gaussianPDFReal_nonneg μ v x))]

/-- Completing the square: `φ_v(y)e^{ty} = e^{t²v/2}φ_{tv, v}(y)`. -/
lemma gaussianPDFReal_mul_exp {v : ℝ≥0} (hv : (v : ℝ) ≠ 0) (t y : ℝ) :
    gaussianPDFReal 0 v y * Real.exp (t * y)
      = Real.exp (t ^ 2 * v / 2) * gaussianPDFReal (t * v) v y := by
  simp only [gaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **The truncated exponential moment**: for `Y ~ N(0, R)`, `R > 0`,
`E[e^{tY}1{Y ≤ w}] = e^{t²R/2}Φ((w - tR)/√R)`. -/
theorem integral_indicator_exp_gaussianReal {R : ℝ} (hR : 0 < R) (t w : ℝ) :
    ∫ y, (Set.Iic w).indicator (fun y => Real.exp (t * y)) y ∂(gaussianReal 0 R.toNNReal)
      = Real.exp (t ^ 2 * R / 2) * normCDF ((w - t * R) / √R) := by
  have hv : R.toNNReal ≠ 0 := by simpa using hR
  have hvR : ((R.toNNReal : ℝ≥0) : ℝ) = R := Real.coe_toNNReal R hR.le
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hpt : ∀ y, gaussianPDFReal 0 R.toNNReal y
      • (Set.Iic w).indicator (fun y => Real.exp (t * y)) y
      = (Set.Iic w).indicator (fun y => Real.exp (t ^ 2 * R / 2)
          * gaussianPDFReal (t * R) R.toNNReal y) y := by
    intro y
    by_cases hy : y ∈ Set.Iic w
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, smul_eq_mul,
        gaussianPDFReal_mul_exp (by rw [hvR]; exact hR.ne'), hvR]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
  rw [integral_congr_ae (ae_of_all _ hpt), integral_indicator measurableSet_Iic,
    integral_const_mul, ← gaussianReal_real_eq_integral _ hv]
  congr 1
  have hshift : (gaussianReal (t * R) R.toNNReal).real (Set.Iic w)
      = (gaussianReal 0 R.toNNReal).real (Set.Iic (w - t * R)) := by
    rw [← zero_add (t * R), ← gaussianReal_map_add_const,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hshift, gaussianReal_real_Iic_eq_normCDF hv, hvR]

/-- **The exit expectation from below, at any threshold `w`**: keeping only `Y ≤ w`,
`E[RMF.hp1ExitV2(m + Y)] ≥ (1 - e^{-A_W})Φ(w/√R) - e^{t(m+L+ρ)+Λ+t²R/2}Φ(w/√R - t√R)`. -/
theorem le_exitMean {R : ℝ} (hR : 0 < R) (t L ρ Λ AW m w : ℝ) :
    (1 - Real.exp (-AW)) * normCDF (w / √R)
        - Real.exp (t * (m + L + ρ) + Λ + t ^ 2 * R / 2) * normCDF (w / √R - t * √R)
      ≤ exitMean t L ρ Λ AW m R := by
  have hv : R.toNNReal ≠ 0 := by simpa using hR
  have hsR : 0 < √R := Real.sqrt_pos.2 hR
  set K := Real.exp (t * (m + L + ρ) + Λ) with hK
  have hpt : ∀ y, (Set.Iic w).indicator (fun _ => (1 - Real.exp (-AW))) y
      - K * (Set.Iic w).indicator (fun y => Real.exp (t * y)) y
      ≤ hp1ExitV2 t L ρ Λ AW (m + y) := by
    intro y
    have he : Real.exp (t * (m + y + L + ρ) + Λ) = K * Real.exp (t * y) := by
      rw [hK, ← Real.exp_add]
      congr 1
      ring
    unfold hp1ExitV2
    by_cases hy : y ∈ Set.Iic w
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, he]
      exact le_trans (le_of_eq (by ring)) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero, sub_zero]
      exact le_max_right _ _
  have hi1 : Integrable (fun y => (Set.Iic w).indicator (fun _ => (1 - Real.exp (-AW))) y)
      (gaussianReal 0 R.toNNReal) := (integrable_const _).indicator measurableSet_Iic
  have hi2 : Integrable (fun y => (Set.Iic w).indicator (fun y => Real.exp (t * y)) y)
      (gaussianReal 0 R.toNNReal) :=
    (integrable_exp_mul_gaussianReal (μ := 0) (v := R.toNNReal) t).indicator measurableSet_Iic
  have h := integral_mono (hi1.sub (hi2.const_mul K)) (integrable_hp1ExitV2_comp _ _ _ _ _ _ _)
    hpt
  simp only [Pi.sub_apply] at h
  rw [integral_sub hi1 (hi2.const_mul K), integral_const_mul,
    integral_indicator_exp_gaussianReal hR, integral_indicator_const _ measurableSet_Iic,
    smul_eq_mul, gaussianReal_real_Iic_eq_normCDF hv, Real.coe_toNNReal R hR.le] at h
  have e1 : (w - t * R) / √R = w / √R - t * √R := by
    field_simp
    rw [Real.sq_sqrt hR.le]
  have e2 : Real.exp (t * (m + L + ρ) + Λ + t ^ 2 * R / 2)
      = K * Real.exp (t ^ 2 * R / 2) := by rw [hK, ← Real.exp_add]
  rw [e1] at h
  rw [e2]
  unfold exitMean
  linarith

/-! ### The exit expectation is Lipschitz in the variance, from one side -/

/-- `e^u ≤ 1 + u + u²/2` for `u ≤ 0`. -/
lemma exp_le_quadratic_of_nonpos {u : ℝ} (hu : u ≤ 0) : Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  have h := exp_neg_le_expNegTaylor_even 1 (s := -u) (by linarith)
  rw [neg_neg] at h
  simp only [expNegTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  norm_num at h
  linarith

/-- `e^u - 1 - u ≤ (u²/2)e^u` for `u ≥ 0`. -/
lemma exp_sub_one_sub_le {u : ℝ} (hu : 0 ≤ u) : Real.exp u - 1 - u ≤ u ^ 2 / 2 * Real.exp u := by
  have h := expNegTaylor_odd_le_exp_neg 1 hu
  simp only [expNegTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  norm_num at h
  have hE : 0 < Real.exp u := Real.exp_pos u
  have hEE : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have key : 1 - u ^ 2 / 2 ≤ (1 + u) * Real.exp (-u) := by
    rcases le_or_gt u 2 with h2 | h2
    · have h3 := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 + u)
      have h4 : 0 ≤ u ^ 3 * (2 - u) := mul_nonneg (pow_nonneg hu 3) (by linarith)
      nlinarith
    · have : 0 ≤ (1 + u) * Real.exp (-u) := by positivity
      nlinarith
  have h5 := mul_le_mul_of_nonneg_left key hE.le
  have h6 : Real.exp u * ((1 + u) * Real.exp (-u)) = 1 + u := by
    rw [mul_left_comm, hEE, mul_one]
  nlinarith

/-- **A quadratic minorant of the exit factor** below its threshold: with
`E = e^{t(x+L+ρ)+Λ} < 1 - e^{-A_W}`, for every `y`,
`g(x + y) ≥ g(x) - tEy - (t²(1 - e^{-A_W})/2)y²`, `g = RMF.hp1ExitV2`.  On `g > 0` it is Taylor's
bound for `c - Ee^{ty}` (`e^u - 1 - u ≤ u²/2` below `0`, `≤ (u²/2)e^u` above, and `Ee^u ≤ c`);
past the threshold the parabola is already below `0`. -/
lemma hp1ExitV2_quadratic_minorant {t L ρ Λ AW x : ℝ}
    (hx : Real.exp (t * (x + L + ρ) + Λ) < 1 - Real.exp (-AW)) (y : ℝ) :
    hp1ExitV2 t L ρ Λ AW x - t * Real.exp (t * (x + L + ρ) + Λ) * y
        - t ^ 2 * (1 - Real.exp (-AW)) / 2 * y ^ 2
      ≤ hp1ExitV2 t L ρ Λ AW (x + y) := by
  set E := Real.exp (t * (x + L + ρ) + Λ) with hE
  set c := 1 - Real.exp (-AW) with hc
  set u := t * y with hu
  have hE0 : 0 < E := Real.exp_pos _
  have hgx : hp1ExitV2 t L ρ Λ AW x = c - E := by
    unfold hp1ExitV2
    rw [max_eq_left (by linarith)]
    ring
  have hexp : Real.exp (t * (x + y + L + ρ) + Λ) = E * Real.exp u := by
    rw [hE, hu, ← Real.exp_add]
    congr 1
    ring
  have hgy : hp1ExitV2 t L ρ Λ AW (x + y) = max (c - E * Real.exp u) 0 := by
    unfold hp1ExitV2
    rw [hexp]
    congr 1
    ring
  have hlhs : c - E - t * E * y - t ^ 2 * c / 2 * y ^ 2 = c - E - E * u - c / 2 * u ^ 2 := by
    rw [hu]
    ring
  rw [hgx, hgy, hlhs]
  -- Taylor's bound above `0`, in the form used twice below
  have hpos : ∀ v : ℝ, 0 ≤ v → E * Real.exp v ≤ c → c - E - E * v - c / 2 * v ^ 2
      ≤ c - E * Real.exp v := by
    intro v hv hvc
    have h1 := exp_sub_one_sub_le hv
    have h2 : E * (Real.exp v - 1 - v) ≤ v ^ 2 / 2 * (E * Real.exp v) := by
      have := mul_le_mul_of_nonneg_left h1 hE0.le
      linarith
    have h3 : v ^ 2 / 2 * (E * Real.exp v) ≤ v ^ 2 / 2 * c :=
      mul_le_mul_of_nonneg_left hvc (by positivity)
    nlinarith
  rcases le_or_gt u 0 with hu0 | hu0
  · -- below `0`
    have h1 := exp_le_quadratic_of_nonpos hu0
    have h2 : E * Real.exp u ≤ E * (1 + u + u ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 hE0.le
    have h3 : E * (u ^ 2 / 2) ≤ c * (u ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hx.le (by positivity)
    refine le_trans ?_ (le_max_left _ _)
    nlinarith
  rcases le_or_gt (E * Real.exp u) c with hc' | hc'
  · exact le_trans (hpos u hu0.le hc') (le_max_left _ _)
  · -- past the threshold: compare with the crossing point `u₀ = log(c/E)`
    have hcE : 1 < c / E := by rw [one_lt_div hE0]; exact hx
    set u₀ := Real.log (c / E) with hu₀
    have hu₀0 : 0 < u₀ := Real.log_pos hcE
    have heu₀ : E * Real.exp u₀ = c := by
      rw [hu₀, Real.exp_log (by linarith)]
      field_simp
    have hu₀u : u₀ ≤ u := by
      by_contra hlt
      have := Real.exp_lt_exp.2 (not_le.1 hlt)
      have := mul_lt_mul_of_pos_left this hE0
      linarith
    have h1 := hpos u₀ hu₀0.le heu₀.le
    rw [heu₀, sub_self] at h1
    have hc0 : 0 ≤ c := by linarith
    have h2 : c - E - E * u - c / 2 * u ^ 2 ≤ c - E - E * u₀ - c / 2 * u₀ ^ 2 := by
      have : u₀ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hu₀0.le hu₀u 2
      have : E * u₀ ≤ E * u := mul_le_mul_of_nonneg_left hu₀u hE0.le
      nlinarith
    exact le_trans (le_trans h2 h1) (le_max_right _ _)

/-- **The exit expectation is Lipschitz in the variance, from one side**: for
`0 ≤ R₁ ≤ R`, `E_R[g(m + Y)] ≥ E_{R₁}[g(m + Y)] - (t²(1 - e^{-A_W})/2)(R - R₁)`.  Write
`N(0, R) = N(0, R₁) ∗ N(0, R - R₁)` and integrate the quadratic minorant
`RMF.hp1ExitV2_quadratic_minorant` against the second factor (mean `0`, variance `R - R₁`).
Only this direction is needed: the certificate evaluates at the lower end `R₁` of the range. -/
theorem exitMean_sub_le {AW : ℝ} (hAW : 0 ≤ AW) (t L ρ Λ m : ℝ) {R₁ R : ℝ}
    (hR₁ : 0 ≤ R₁) (hR : R₁ ≤ R) :
    exitMean t L ρ Λ AW m R₁ - t ^ 2 * (1 - Real.exp (-AW)) / 2 * (R - R₁)
      ≤ exitMean t L ρ Λ AW m R := by
  set c := 1 - Real.exp (-AW) with hc
  have hc0 : 0 ≤ c := by
    have := Real.exp_le_one_iff.2 (by linarith : -AW ≤ 0)
    linarith
  set K := t ^ 2 * c / 2 with hKdef
  have hK0 : 0 ≤ K := by positivity
  set ε := R - R₁ with hε
  have hε0 : 0 ≤ ε := by linarith
  set ν := gaussianReal 0 ε.toNNReal with hν
  have hint1 : Integrable (fun y : ℝ => y) ν :=
    (memLp_id_gaussianReal' (μ := 0) (v := ε.toNNReal) 1 (by simp)).integrable le_rfl
  have hint2 : Integrable (fun y : ℝ => y ^ 2) ν :=
    (memLp_id_gaussianReal' (μ := 0) (v := ε.toNNReal) 2 (by simp)).integrable_sq
  -- the inner bound
  have hinner : ∀ x, hp1ExitV2 t L ρ Λ AW x - K * ε
      ≤ ∫ y, hp1ExitV2 t L ρ Λ AW (x + y) ∂ν := by
    intro x
    by_cases hx : Real.exp (t * (x + L + ρ) + Λ) < c
    · set E := Real.exp (t * (x + L + ρ) + Λ)
      have hmin := hp1ExitV2_quadratic_minorant (L := L) (ρ := ρ) (Λ := Λ) (AW := AW) hx
      have hi1 : Integrable (fun y => hp1ExitV2 t L ρ Λ AW x - t * E * y) ν :=
        (integrable_const _).sub (hint1.const_mul _)
      have hi : Integrable (fun y => hp1ExitV2 t L ρ Λ AW x - t * E * y - K * y ^ 2) ν :=
        hi1.sub (hint2.const_mul _)
      have h := integral_mono hi (integrable_hp1ExitV2_comp ν t L ρ Λ AW x) hmin
      have e1 : ∫ y, (hp1ExitV2 t L ρ Λ AW x - t * E * y - K * y ^ 2) ∂ν
          = ∫ y, (hp1ExitV2 t L ρ Λ AW x - t * E * y) ∂ν - ∫ y, K * y ^ 2 ∂ν :=
        integral_sub hi1 (hint2.const_mul K)
      have e2 : ∫ y, (hp1ExitV2 t L ρ Λ AW x - t * E * y) ∂ν
          = ∫ _y, hp1ExitV2 t L ρ Λ AW x ∂ν - ∫ y, t * E * y ∂ν :=
        integral_sub (integrable_const _) (hint1.const_mul _)
      have e3 : ∫ y, t * E * y ∂ν = t * E * ∫ y, y ∂ν := integral_const_mul _ _
      have e4 : ∫ y, K * y ^ 2 ∂ν = K * ∫ y, y ^ 2 ∂ν := integral_const_mul _ _
      have e5 : ∫ y, y ∂ν = 0 := by rw [hν, integral_id_gaussianReal]
      have e6 : ∫ y, y ^ 2 ∂ν = ε := by
        rw [hν, integral_sq_gaussianReal_eq, Real.coe_toNNReal _ hε0]
      have e7 : ∫ _y, hp1ExitV2 t L ρ Λ AW x ∂ν = hp1ExitV2 t L ρ Λ AW x := by
        simp [integral_const]
      rw [e1, e2, e3, e4, e5, e6, e7] at h
      linarith
    · have hgx : hp1ExitV2 t L ρ Λ AW x = 0 := by
        unfold hp1ExitV2
        apply max_eq_right
        have := not_lt.1 hx
        linarith
      rw [hgx]
      have := integral_nonneg (μ := ν) (f := fun y => hp1ExitV2 t L ρ Λ AW (x + y))
        fun y => hp1ExitV2_nonneg t L ρ Λ AW (x + y)
      have := mul_nonneg hK0 hε0
      linarith
  -- the convolution
  have hconv : gaussianReal 0 R.toNNReal = (gaussianReal 0 R₁.toNNReal) ∗ ν := by
    rw [hν, gaussianReal_conv_gaussianReal, add_zero, ← Real.toNNReal_add hR₁ hε0]
    congr 2
    ring
  have hFm : Measurable fun p : ℝ × ℝ => hp1ExitV2 t L ρ Λ AW (m + (p.1 + p.2)) :=
    (measurable_hp1ExitV2 t L ρ Λ AW).comp (measurable_const.add
      (measurable_fst.add measurable_snd))
  have hFi : Integrable (fun p : ℝ × ℝ => hp1ExitV2 t L ρ Λ AW (m + (p.1 + p.2)))
      ((gaussianReal 0 R₁.toNNReal).prod ν) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp1ExitV2_nonneg _ _ _ _ _ _)]
      exact hp1ExitV2_le_one _ _ _ _ _ _)
  have hgm : Measurable fun y => hp1ExitV2 t L ρ Λ AW (m + y) :=
    (measurable_hp1ExitV2 t L ρ Λ AW).comp (measurable_const_add m)
  unfold exitMean
  rw [hconv, Measure.conv, integral_map (by fun_prop) hgm.aestronglyMeasurable,
    integral_prod _ hFi]
  have hsub : ∫ y, hp1ExitV2 t L ρ Λ AW (m + y) ∂(gaussianReal 0 R₁.toNNReal) - K * ε
      = ∫ x, (hp1ExitV2 t L ρ Λ AW (m + x) - K * ε) ∂(gaussianReal 0 R₁.toNNReal) := by
    rw [integral_sub (integrable_hp1ExitV2_comp _ t L ρ Λ AW m) (integrable_const _),
      integral_const]
    simp
  rw [hsub]
  refine integral_mono ((integrable_hp1ExitV2_comp _ t L ρ Λ AW m).sub (integrable_const _))
    hFi.integral_prod_left fun x => ?_
  have h := hinner (m + x)
  simp only [add_assoc] at h
  exact h

/-! ### A lower sum for the start's main term -/

/-- A set integral against the standard normal law, by its density. -/
lemma setIntegral_gaussianReal_eq {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ z in s, f z ∂(gaussianReal 0 1) = ∫ z in s, gaussianPDFReal 0 1 z * f z := by
  rw [← integral_indicator hs, ← integral_indicator hs,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  congr 1
  ext z
  by_cases hz : z ∈ s <;> simp [Set.indicator, hz]

/-- **The first moment of the standard normal law on `(x, y]`**:
`E[Z; x < Z ≤ y] = φ(x) - φ(y)`. -/
lemma setIntegral_Ioc_id_gaussianReal {x y : ℝ} (hxy : x ≤ y) :
    ∫ z in Set.Ioc x y, z ∂(gaussianReal 0 1)
      = gaussianPDFReal 0 1 x - gaussianPDFReal 0 1 y := by
  rw [setIntegral_gaussianReal_eq measurableSet_Ioc, ← intervalIntegral.integral_of_le hxy]
  have hd : ∀ z ∈ Set.uIcc x y, HasDerivAt (fun z => -gaussianPDFReal 0 1 z)
      (gaussianPDFReal 0 1 z * z) z := by
    intro z _
    have e : (fun z => -gaussianPDFReal 0 1 z)
        = fun z => -((√(2 * π))⁻¹ * Real.exp (-(z ^ 2 / 2))) := by
      funext w
      rw [gaussianPDFReal_zero_one]
    rw [e, gaussianPDFReal_zero_one]
    have h1 : HasDerivAt (fun w : ℝ => -(w ^ 2 / 2)) (-z) z :=
      ((hasDerivAt_pow 2 z).div_const 2).fun_neg.congr_deriv (by push_cast; ring)
    exact (h1.exp.const_mul (√(2 * π))⁻¹).fun_neg.congr_deriv (by ring)
  have hc : Continuous fun z => gaussianPDFReal 0 1 z * z := by
    simp_rw [gaussianPDFReal_zero_one]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring

/-- `E[(a - sZ)·c; x < Z ≤ y] = c(a(Φ(y) - Φ(x)) - s(φ(x) - φ(y)))`. -/
lemma intervalIntegral_affine_gaussianReal {x y : ℝ} (hxy : x ≤ y) (a s c : ℝ) :
    ∫ z in x..y, (a - s * z) * c ∂(gaussianReal 0 1)
      = c * (a * (normCDF y - normCDF x)
        - s * (gaussianPDFReal 0 1 x - gaussianPDFReal 0 1 y)) := by
  have hi1 : IntegrableOn (fun _ : ℝ => a) (Set.Ioc x y) (gaussianReal 0 1) :=
    (integrable_const a).integrableOn
  have hi2 : IntegrableOn (fun z : ℝ => s * z) (Set.Ioc x y) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable le_rfl).const_mul s
      |>.integrableOn
  rw [intervalIntegral.integral_of_le hxy, integral_mul_const, integral_sub hi1 hi2,
    setIntegral_const, integral_const_mul, setIntegral_Ioc_id_gaussianReal hxy,
    Measure.real, ← measureReal_def, measureReal_Ioc_eq_normCDF_sub hxy, smul_eq_mul]
  ring

/-- **A lower sum for the start's main term** `RMF.startMainV2`, on nodes `z₀ ≤ … ≤ z_N` of the
standardised height `U/√V`.  On `(zᵢ, zᵢ₊₁]` the weight is `a - √Vz` (the nodes stay in
`[(a - C)/√V, a/√V]`), the location `D + β̄√Vz` is at most `m̄ᵢ`, so the exit expectation is at
least its value at `m̄ᵢ` (antitone, `RMF.exitMean_antitone`) at the lower end `R₁` of the residual
variance's range, less `(t²(1 - e^{-A_W})/2)(R₂ - R₁)` (`RMF.exitMean_sub_le`); what is left is the
exact normal mass `Φ(zᵢ₊₁) - Φ(zᵢ)` and first moment `φ(zᵢ) - φ(zᵢ₊₁)` of the cell.  The data
enter only through `√V`, `D + β̄√Vz ≤ m̄ᵢ` and `R ∈ [R₁, R₂]`. -/
theorem sum_le_startMainV2 {a C V S κ D t L ρ Λ AW R₁ R₂ : ℝ} (hC : 0 ≤ C) (hV : 0 < V)
    (ht : 0 ≤ t) (hAW : 0 ≤ AW) (hR₁ : 0 ≤ R₁) (hR₁R : R₁ ≤ pairResidVar V S κ)
    (hRR₂ : pairResidVar V S κ ≤ R₂) {zs : ℕ → ℝ} (hzs : Monotone zs) {N : ℕ}
    (hlo : a - C ≤ √V * zs 0) (hhi : √V * zs N ≤ a) {mbar : ℕ → ℝ}
    (hm : ∀ i < N, ∀ z ∈ Set.Icc (zs i) (zs (i + 1)), D + pairSlope V κ * (√V * z) ≤ mbar i) :
    ∑ i ∈ Finset.range N,
        max (exitMean t L ρ Λ AW (mbar i) R₁ - t ^ 2 * (1 - Real.exp (-AW)) / 2 * (R₂ - R₁)) 0
          * (a * (normCDF (zs (i + 1)) - normCDF (zs i))
            - √V * (gaussianPDFReal 0 1 (zs i) - gaussianPDFReal 0 1 (zs (i + 1))))
      ≤ startMainV2 a C V S κ D t L ρ Λ AW := by
  set R := pairResidVar V S κ with hRdef
  set K := t ^ 2 * (1 - Real.exp (-AW)) / 2 with hK
  have hK0 : 0 ≤ K := by
    have := Real.exp_le_one_iff.2 (by linarith : -AW ≤ 0)
    have : 0 ≤ 1 - Real.exp (-AW) := by linarith
    positivity
  set Ibar : ℕ → ℝ := fun i => max (exitMean t L ρ Λ AW (mbar i) R₁ - K * (R₂ - R₁)) 0
    with hIbar
  set μ := gaussianReal 0 1 with hμ
  -- the integrand in the standardised height
  set G : ℝ → ℝ := fun z => startWeight a C (√V * z)
    * exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R with hG
  have hEm : Measurable fun m => exitMean t L ρ Λ AW m R :=
    (exitMean_antitone ht L ρ Λ AW R).measurable
  have hGm : Measurable G :=
    ((measurable_startWeight a C).comp (measurable_const_mul _)).mul
      (hEm.comp (measurable_const.add (measurable_const.mul (measurable_const_mul _))))
  have hG0 : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg (startWeight_nonneg hC _) (exitMean_nonneg _ _ _ _ _ _ _)
  have hGC : ∀ z, G z ≤ C := fun z =>
    (mul_le_of_le_one_right (startWeight_nonneg hC _) (exitMean_le_one _ _ _ _ _ _ _)).trans
      (startWeight_le _)
  have hGi : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable C (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 z)]
      exact hGC z)
  -- the main term as an integral over the standardised height
  have hmain : startMainV2 a C V S κ D t L ρ Λ AW = ∫ z, G z ∂μ := by
    have hsq : √((V.toNNReal : ℝ≥0) : ℝ) = √V := by rw [Real.coe_toNNReal V hV.le]
    have hFm : Measurable fun u => startWeight a C u
        * exitMean t L ρ Λ AW (D + pairSlope V κ * u) R :=
      (measurable_startWeight a C).mul (hEm.comp (measurable_const.add (measurable_const_mul _)))
    have e : startMainV2 a C V S κ D t L ρ Λ AW = ∫ u, startWeight a C u
        * exitMean t L ρ Λ AW (D + pairSlope V κ * u) R ∂(gaussianReal 0 V.toNNReal) := rfl
    rw [e, ← gaussianReal_map_sqrt_mul V.toNNReal, integral_map (by fun_prop)
      hFm.aestronglyMeasurable, hsq]
  -- each cell
  have hzN : ∀ i, i ≤ N → zs 0 ≤ zs i ∧ zs i ≤ zs N := fun i hi =>
    ⟨hzs (Nat.zero_le i), hzs hi⟩
  have hcell : ∀ i < N, Ibar i * (a * (normCDF (zs (i + 1)) - normCDF (zs i))
      - √V * (gaussianPDFReal 0 1 (zs i) - gaussianPDFReal 0 1 (zs (i + 1))))
      ≤ ∫ z in zs i..zs (i + 1), G z ∂μ := by
    intro i hi
    have hle : zs i ≤ zs (i + 1) := hzs (Nat.le_succ i)
    rw [← intervalIntegral_affine_gaussianReal hle a (√V) (Ibar i)]
    refine intervalIntegral.integral_mono_on hle
      ((by fun_prop : Continuous fun z => (a - √V * z) * Ibar i).intervalIntegrable _ _)
      (hGi.intervalIntegrable) fun z hz => ?_
    have hz0 : zs 0 ≤ z := le_trans (hzN i hi.le).1 hz.1
    have hzN' : z ≤ zs N := le_trans hz.2 (hzN (i + 1) hi).2
    have hw1 : a - C ≤ √V * z := le_trans hlo (mul_le_mul_of_nonneg_left hz0 (Real.sqrt_nonneg _))
    have hw2 : √V * z ≤ a := le_trans (mul_le_mul_of_nonneg_left hzN' (Real.sqrt_nonneg _)) hhi
    have hsw : startWeight a C (√V * z) = a - √V * z := startWeight_eq hw1 hw2
    have hE1 : exitMean t L ρ Λ AW (mbar i) R
        ≤ exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R :=
      exitMean_antitone ht L ρ Λ AW R (hm i hi z hz)
    have hE2 := exitMean_sub_le hAW t L ρ Λ (mbar i) hR₁ hR₁R
    rw [← hK] at hE2
    have hE3 : K * (R - R₁) ≤ K * (R₂ - R₁) := mul_le_mul_of_nonneg_left (by linarith) hK0
    have hIb : Ibar i ≤ exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R :=
      max_le (by linarith) (exitMean_nonneg _ _ _ _ _ _ _)
    rw [hG]
    simp only
    rw [hsw]
    exact mul_le_mul_of_nonneg_left hIb (by linarith)
  -- sum the cells
  have hsum : ∑ i ∈ Finset.range N, ∫ z in zs i..zs (i + 1), G z ∂μ
      = ∫ z in zs 0..zs N, G z ∂μ :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hGi.intervalIntegrable
  have hwhole : ∫ z in zs 0..zs N, G z ∂μ ≤ ∫ z, G z ∂μ := by
    rw [intervalIntegral.integral_of_le (hzN N le_rfl).1]
    exact setIntegral_le_integral hGi (Filter.Eventually.of_forall hG0)
  rw [hmain]
  calc _ ≤ ∑ i ∈ Finset.range N, ∫ z in zs i..zs (i + 1), G z ∂μ :=
        Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.1 hi)
    _ = ∫ z in zs 0..zs N, G z ∂μ := hsum
    _ ≤ ∫ z, G z ∂μ := hwhole

/-- The location bound of a cell at its corners: for `b ∈ [P₁, P₂]`, `z ∈ [z₁, z₂]` and `D ≤ D₂`,
`D + bz ≤ D₂ + max(P₁z₁, P₁z₂, P₂z₁, P₂z₂)` (`bz` is bilinear). -/
lemma add_mul_le_corners {D D₂ b P₁ P₂ z z₁ z₂ : ℝ} (hD : D ≤ D₂) (hb : b ∈ Set.Icc P₁ P₂)
    (hz : z ∈ Set.Icc z₁ z₂) :
    D + b * z ≤ D₂ + max (max (P₁ * z₁) (P₁ * z₂)) (max (P₂ * z₁) (P₂ * z₂)) := by
  have hlin : ∀ P : ℝ, P * z ≤ max (P * z₁) (P * z₂) := by
    intro P
    rcases le_total 0 P with hP | hP
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hz.2 hP)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hz.1 hP)
  have hbz : b * z ≤ max (P₁ * z) (P₂ * z) := by
    rcases le_total 0 z with hz0 | hz0
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hb.2 hz0)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right hb.1 hz0)
  have h1 := hlin P₁
  have h2 := hlin P₂
  have : max (P₁ * z) (P₂ * z) ≤ max (max (P₁ * z₁) (P₁ * z₂)) (max (P₂ * z₁) (P₂ * z₂)) :=
    max_le_max h1 h2
  linarith

/-! ### The other terms of the start, at their worst case -/

/-- `E[Z⁺] = (2π)^{-1/2}` for a standard normal `Z`. -/
lemma integral_posPart_stdGauss : ∫ z, max z 0 ∂(gaussianReal 0 1) = (√(2 * π))⁻¹ := by
  have hpt : (fun z : ℝ => max z 0) = (Set.Ioi 0).indicator id := by
    funext z
    by_cases hz : 0 < z
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hz), max_eq_left hz.le, id]
    · rw [Set.indicator_of_notMem (fun h => hz (Set.mem_Ioi.1 h)), max_eq_right (not_lt.1 hz)]
  rw [hpt, integral_indicator measurableSet_Ioi, setIntegral_gaussianReal_eq measurableSet_Ioi]
  have hφ : ∀ z, gaussianPDFReal 0 1 z * id z
      = (√(2 * π))⁻¹ * (z * Real.exp (-(1 / 2) * z ^ 2)) := by
    intro z
    rw [gaussianPDFReal_zero_one, id, show -(z ^ 2 / 2) = -(1 / 2) * z ^ 2 by ring]
    ring
  have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => -gaussianPDFReal 0 1 z)
      (gaussianPDFReal 0 1 x * id x) x := by
    intro x _
    have e : (fun z => -gaussianPDFReal 0 1 z)
        = fun z => -((√(2 * π))⁻¹ * Real.exp (-(z ^ 2 / 2))) := by
      funext w
      rw [gaussianPDFReal_zero_one]
    rw [e, gaussianPDFReal_zero_one, id]
    have h1 : HasDerivAt (fun w : ℝ => -(w ^ 2 / 2)) (-x) x :=
      ((hasDerivAt_pow 2 x).div_const 2).fun_neg.congr_deriv (by push_cast; ring)
    exact (h1.exp.const_mul (√(2 * π))⁻¹).fun_neg.congr_deriv (by ring)
  have hint : IntegrableOn (fun z => gaussianPDFReal 0 1 z * id z) (Set.Ioi 0) := by
    simp_rw [hφ]
    exact ((integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
      ).integrableOn
  have hlim : Filter.Tendsto (fun z => -gaussianPDFReal 0 1 z) Filter.atTop (nhds 0) := by
    simp_rw [gaussianPDFReal_zero_one]
    have h1 : Filter.Tendsto (fun z : ℝ => -(z ^ 2 / 2)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp
        ((Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (√(2 * π))⁻¹
    rw [mul_zero] at h2
    simpa using h2.neg
  have hcont : ContinuousWithinAt (fun z => -gaussianPDFReal 0 1 z) (Set.Ici 0) 0 := by
    simp_rw [gaussianPDFReal_zero_one]
    fun_prop
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim, gaussianPDFReal_zero_one]
  simp

/-- `E[min((-X)⁺, C)] ≤ √(v/(2π))` for `X ~ N(0, v)`. -/
lemma integral_startWeight_zero_le {v C : ℝ} (hv : 0 ≤ v) (hC : 0 ≤ C) :
    ∫ x, startWeight 0 C x ∂(gaussianReal 0 v.toNNReal) ≤ √v * (√(2 * π))⁻¹ := by
  have hsq : √((v.toNNReal : ℝ≥0) : ℝ) = √v := by rw [Real.coe_toNNReal v hv]
  have hnegm : Measurable fun x : ℝ => max (-x) 0 := measurable_neg.max measurable_const
  have hi : Integrable (fun x : ℝ => max (-x) 0) (gaussianReal 0 v.toNNReal) := by
    have := (memLp_id_gaussianReal' (μ := 0) (v := v.toNNReal) 1 (by simp)).integrable le_rfl
    exact this.neg.sup (integrable_const 0)
  have hsw : ∀ x, startWeight 0 C x ≤ max (-x) 0 := fun x => by
    unfold startWeight
    rw [zero_sub]
    exact min_le_left _ _
  have hswi : Integrable (startWeight 0 C) (gaussianReal 0 v.toNNReal) := by
    refine hi.mono' (measurable_startWeight 0 C).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (startWeight_nonneg hC x)]
    exact hsw x
  calc ∫ x, startWeight 0 C x ∂(gaussianReal 0 v.toNNReal)
      ≤ ∫ x, max (-x) 0 ∂(gaussianReal 0 v.toNNReal) := integral_mono hswi hi hsw
    _ = ∫ z, max (-(√v * z)) 0 ∂(gaussianReal 0 1) := by
        rw [← gaussianReal_map_sqrt_mul v.toNNReal, integral_map (by fun_prop)
          hnegm.aestronglyMeasurable, hsq]
    _ = √v * ∫ z, max (-z) 0 ∂(gaussianReal 0 1) := by
        rw [← integral_const_mul]
        congr 1
        funext z
        rw [mul_max_of_nonneg _ _ (Real.sqrt_nonneg v), mul_zero, mul_neg]
    _ = √v * (√(2 * π))⁻¹ := by
        congr 1
        have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
          rw [gaussianReal_map_neg, neg_zero]
        have h := integral_map (μ := gaussianReal 0 1) (φ := fun x : ℝ => -x)
          (f := fun y : ℝ => max y 0) measurable_neg.aemeasurable
          ((measurable_id.max measurable_const).aestronglyMeasurable)
        rw [hmap] at h
        rw [← h, integral_posPart_stdGauss]

/-- **The ceiling loss at its worst case**: for `0 < v₀ ≤ v₀'`, `0 ≤ v₁ ≤ v₁'`, `a ≥ 0`,
`P(N(0, v₀) > a)E[min((-N(0, v₁))⁺, C)] ≤ (1 - Φ(a/√v₀'))√(v₁'/(2π))`. -/
theorem ceilLoss_le {v₀ v₀' v₁ v₁' a C : ℝ} (hv₀ : 0 < v₀) (hv₀' : v₀ ≤ v₀') (hv₁ : 0 ≤ v₁)
    (hv₁' : v₁ ≤ v₁') (ha : 0 ≤ a) (hC : 0 ≤ C) :
    (gaussianReal 0 v₀.toNNReal).real (Set.Ioi a)
        * ∫ x, startWeight 0 C x ∂(gaussianReal 0 v₁.toNNReal)
      ≤ (1 - normCDF (a / √v₀')) * (√v₁' * (√(2 * π))⁻¹) := by
  have hv : v₀.toNNReal ≠ 0 := by simpa using hv₀
  have hP : (gaussianReal 0 v₀.toNNReal).real (Set.Ioi a) = 1 - normCDF (a / √v₀) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
      gaussianReal_real_Iic_eq_normCDF hv, Real.coe_toNNReal v₀ hv₀.le]
  have hmono : normCDF (a / √v₀') ≤ normCDF (a / √v₀) :=
    normCDF_mono (div_le_div_of_nonneg_left ha (Real.sqrt_pos.2 hv₀)
      (Real.sqrt_le_sqrt hv₀'))
  have hE := integral_startWeight_zero_le hv₁ hC
  have hE' : √v₁ * (√(2 * π))⁻¹ ≤ √v₁' * (√(2 * π))⁻¹ :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv₁') (by positivity)
  have hE0 : 0 ≤ ∫ x, startWeight 0 C x ∂(gaussianReal 0 v₁.toNNReal) :=
    integral_nonneg fun x => startWeight_nonneg hC x
  rw [hP]
  exact mul_le_mul (by linarith) (le_trans hE hE') hE0 (by linarith [normCDF_le_one (a / √v₀')])

/-- `e^{-c²/(2x)}` increases in the variance `x > 0` and decreases in `c ≥ 0`. -/
lemma exp_neg_sq_div_le_of_le {c c' x X : ℝ} (hx : 0 < x) (hxX : x ≤ X) (hc' : 0 ≤ c')
    (hcc : c' ≤ c) : Real.exp (-(c ^ 2 / (2 * x))) ≤ Real.exp (-(c' ^ 2 / (2 * X))) := by
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h1 : c' ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hc' hcc 2
  calc c' ^ 2 / (2 * X) ≤ c' ^ 2 / (2 * x) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    _ ≤ c ^ 2 / (2 * x) := div_le_div_of_nonneg_right h1 (by positivity)

/-- **The start's tails at their worst case**: `RMF.startTails` is increasing in each variance
(`v₀`, `V = v₀ + v₁`, `σ₁² = β₀²v₀ + s₀`, `S`) and in `|d₀|` and `-(d₀ + d₁)`, as long as the
margins `M₁ - |d₀|`, `K₂ + d₀ + d₁` stay nonnegative. -/
theorem startTails_le {v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ A B M₁ K₂ v₀' V' σ' S' d₀' D' : ℝ}
    (hv₀ : 0 < v₀) (hv₀' : v₀ ≤ v₀') (hV : 0 < v₀ + v₁) (hV' : v₀ + v₁ ≤ V')
    (hσ : 0 < β₀ ^ 2 * v₀ + s₀) (hσ' : β₀ ^ 2 * v₀ + s₀ ≤ σ')
    (hS : 0 < β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁))
    (hS' : β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁) ≤ S') (hAB : 0 ≤ A + B) (hAB2 : 0 ≤ A + 2 * B)
    (hd₀ : |d₀| ≤ d₀') (hM : d₀' ≤ M₁) (hD : D' ≤ d₀ + d₁) (hK : 0 ≤ K₂ + D') :
    startTails v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ A B M₁ K₂
      ≤ Real.exp (-((A + B) ^ 2 / (2 * v₀'))) + Real.exp (-((A + 2 * B) ^ 2 / (2 * V')))
        + 2 * Real.exp (-((M₁ - d₀') ^ 2 / (2 * σ'))) + Real.exp (-((K₂ + D') ^ 2 / (2 * S'))) := by
  unfold startTails
  have h1 := exp_neg_sq_div_le_of_le hv₀ hv₀' hAB le_rfl
  have h2 := exp_neg_sq_div_le_of_le hV hV' hAB2 le_rfl
  have h3 := exp_neg_sq_div_le_of_le hσ hσ' (by linarith : 0 ≤ M₁ - d₀')
    (by linarith : M₁ - d₀' ≤ M₁ - |d₀|)
  have h4 := exp_neg_sq_div_le_of_le hS hS' hK (by linarith : K₂ + D' ≤ K₂ + d₀ + d₁)
  linarith

/-- `RMF.hp1Loss` is increasing in its variance argument `V` (the floor loss carries `e^{V/2}`). -/
lemma hp1Loss_le_of_le {n₀ m₀ : ℕ} {vmin vmax V V' a A B L Klate σR2 : ℝ}
    (hC : 0 ≤ a + A + 2 * B) (hB : 2 * vmax ≤ B) (hV : V ≤ V') :
    hp1Loss n₀ m₀ vmin vmax V a A B L Klate σR2 ≤ hp1Loss n₀ m₀ vmin vmax V' a A B L Klate σR2 := by
  have hE : 0 ≤ Real.exp ((B - 2 * vmax) / 2) - 1 := by
    have := Real.one_le_exp (show 0 ≤ (B - 2 * vmax) / 2 by linarith)
    linarith
  have hM : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hX : 0 ≤ √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
      * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        / (Real.exp ((B - 2 * vmax) / 2) - 1)) :=
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (by positivity)) hM) hE)
  unfold hp1Loss
  have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith : V / 2 ≤ V' / 2)) hX
  linarith

/-- **`RMF.hp1Slope` from below, by bounds on its atoms**: `√(2πv₊) ≤ u₁`,
`√(2n₀/(π(n₀-2-m₀)v₋)) ≤ u₂`, `e^{-(L-K)²/(2σ²)} ≤ e`, and a nonnegative ballot factor. -/
lemma le_hp1Slope {n₀ m₀ : ℕ} {vmin vmax a A B L Klate σR2 u₁ u₂ e : ℝ}
    (hnum : 0 ≤ 1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)))
    (hvmax : 0 < vmax) (hu₁ : √(2 * π * vmax) ≤ u₁)
    (hu₂ : √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) ≤ u₂)
    (he : Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ e) :
    2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / u₁ - u₂ * e
      ≤ hp1Slope n₀ m₀ vmin vmax a A B L Klate σR2 := by
  have hs : 0 < √(2 * π * vmax) := Real.sqrt_pos.2 (by positivity)
  have h1 : 2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / u₁
      ≤ 2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / √(2 * π * vmax) :=
    div_le_div_of_nonneg_left (by linarith) hs hu₁
  have h2 : √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
      * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ u₂ * e :=
    mul_le_mul hu₂ he (Real.exp_pos _).le (le_trans (Real.sqrt_nonneg _) hu₂)
  unfold hp1Slope
  exact le_max_of_le_left (by linarith)

/-- **`RMF.hp1Loss` from above, by bounds on its atoms**: `√(n₀/(n₀-2)) ≤ w₁`, `e^{-(A+2B)} ≤ w₂`,
`√(πv₊/2) ≤ w₃`, both square roots of the maximum `≤ w₄`, `e^{(B-2v₊)/2} - 1 ≥ l > 0`,
`e^{V/2} ≤ w₆`, `√(2n₀/(π(n₀-2-m₀)v₋)) ≤ w₇`, `P_R ≤ e`, `√(P_R m₀v₊) ≤ w₈`. -/
lemma hp1Loss_le {n₀ m₀ : ℕ} {vmin vmax V a A B L Klate σR2 w₁ w₂ w₃ w₄ l w₆ w₇ e w₈ : ℝ}
    (hC : 0 ≤ a + A + 2 * B) (h₁ : √((n₀ : ℝ) / ((n₀ : ℝ) - 2)) ≤ w₁)
    (h₂ : Real.exp (-(A + 2 * B)) ≤ w₂) (h₃ : √(π * vmax / 2) ≤ w₃)
    (h₄ : √(4 / (π * vmin)) ≤ w₄) (h₄' : √(2 / (Real.exp 1 * (B - 2 * vmax))) ≤ w₄)
    (hl : 0 < l) (h₅ : l ≤ Real.exp ((B - 2 * vmax) / 2) - 1) (h₆ : Real.exp (V / 2) ≤ w₆)
    (h₇ : √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) ≤ w₇)
    (he : Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ e)
    (h₈ : √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax)) ≤ w₈) :
    hp1Loss n₀ m₀ vmin vmax V a A B L Klate σR2
      ≤ w₁ * (w₂ * (a + A + 2 * B + w₃ + 2) * w₄ / l) * w₆ + w₇ * (w₃ * e + w₈) := by
  have hs₁ := Real.sqrt_nonneg ((n₀ : ℝ) / ((n₀ : ℝ) - 2))
  have hs₃ := Real.sqrt_nonneg (π * vmax / 2)
  have hs₇ := Real.sqrt_nonneg (2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
  have hM : max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) ≤ w₄ := max_le h₄ h₄'
  have hM0 : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hE2 := Real.exp_pos (-(A + 2 * B))
  have hEV := Real.exp_pos (V / 2)
  have hER := Real.exp_pos (-((L - Klate) ^ 2 / (2 * σR2)))
  have hden : 0 < Real.exp ((B - 2 * vmax) / 2) - 1 := lt_of_lt_of_le hl h₅
  -- the floor loss
  have hn1 : Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
      ≤ w₂ * (a + A + 2 * B + w₃ + 2) :=
    mul_le_mul h₂ (by linarith) (by positivity) (le_trans hE2.le h₂)
  have hn2 : Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
      ≤ w₂ * (a + A + 2 * B + w₃ + 2) * w₄ :=
    mul_le_mul hn1 hM hM0 (le_trans (by positivity) hn1)
  have hn3 : Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        / (Real.exp ((B - 2 * vmax) / 2) - 1)
      ≤ w₂ * (a + A + 2 * B + w₃ + 2) * w₄ / l :=
    div_le_div₀ (le_trans (by positivity) hn2) hn2 hl h₅
  have hf : √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
        * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
          * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
          / (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (V / 2)
      ≤ w₁ * (w₂ * (a + A + 2 * B + w₃ + 2) * w₄ / l) * w₆ := by
    have h0 : 0 ≤ Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        / (Real.exp ((B - 2 * vmax) / 2) - 1) := by positivity
    exact mul_le_mul (mul_le_mul h₁ hn3 h0 (le_trans hs₁ h₁)) h₆ hEV.le
      (mul_nonneg (le_trans hs₁ h₁) (le_trans h0 hn3))
  -- the slope loss
  have hs : √(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
        + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax)) ≤ w₃ * e + w₈ :=
    add_le_add (mul_le_mul h₃ he hER.le (le_trans hs₃ h₃)) h₈
  have hsl := mul_le_mul h₇ hs (by positivity) (le_trans hs₇ h₇)
  unfold hp1Loss
  linarith

/-- **HP1's v2 bound from a lower bound of its main term**, the other terms at their worst case
over the data ranges: if `X ≤ RMF.startMainV2` at the block data, then
`RMF.hp1LowerBoundV2 ≥ RMF.hp1Slope·(X - (1 - Φ(a/√v₀'))√(v₁'/(2π)) - C·tails') - RMF.hp1Loss(V')`,
`C = a + A + 2B`, `tails'` the worst case of `RMF.startTails_le`.  (`RMF.hp1Slope ≥ 0`.) -/
theorem hp1LowerBoundV2_ge {n₀ m₀ : ℕ}
    {vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW Klate σR2 : ℝ}
    {X v₀' v₁' V' σ' S' d₀' D' : ℝ}
    (hX : X ≤ startMainV2 a (a + A + 2 * B) (v₀ + v₁) (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁))
      (β₀ * v₀ + β₁ * v₁) (d₀ + d₁) t L ρ Λ AW)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 2 * vmax ≤ B) (hvmax : 0 ≤ vmax)
    (hv₀ : 0 < v₀) (hv₀' : v₀ ≤ v₀') (hv₁ : 0 ≤ v₁) (hv₁' : v₁ ≤ v₁') (hV' : v₀ + v₁ ≤ V')
    (hσ : 0 < β₀ ^ 2 * v₀ + s₀) (hσ' : β₀ ^ 2 * v₀ + s₀ ≤ σ')
    (hS : 0 < β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁))
    (hS' : β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁) ≤ S')
    (hd₀ : |d₀| ≤ d₀') (hM : d₀' ≤ M₁) (hD : D' ≤ d₀ + d₁) (hK : 0 ≤ K₂ + D') :
    hp1Slope n₀ m₀ vmin vmax a A B L Klate σR2
        * (X - (1 - normCDF (a / √v₀')) * (√v₁' * (√(2 * π))⁻¹)
          - (a + A + 2 * B) * (Real.exp (-((A + B) ^ 2 / (2 * v₀')))
            + Real.exp (-((A + 2 * B) ^ 2 / (2 * V')))
            + 2 * Real.exp (-((M₁ - d₀') ^ 2 / (2 * σ')))
            + Real.exp (-((K₂ + D') ^ 2 / (2 * S')))))
        - hp1Loss n₀ m₀ vmin vmax V' a A B L Klate σR2
      ≤ hp1LowerBoundV2 n₀ m₀ vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW Klate
        σR2 := by
  have hB0 : 0 ≤ B := by linarith
  have hC : 0 ≤ a + A + 2 * B := by linarith
  have hceil := ceilLoss_le hv₀ hv₀' hv₁ hv₁' ha hC
  have htails := startTails_le (s₁ := s₁) (β₁ := β₁) (A := A) (B := B) (M₁ := M₁) (K₂ := K₂)
    hv₀ hv₀' (by linarith) hV' hσ hσ' hS hS' (by linarith) (by linarith) hd₀ hM hD hK
  have hstart : X - (1 - normCDF (a / √v₀')) * (√v₁' * (√(2 * π))⁻¹)
      - (a + A + 2 * B) * (Real.exp (-((A + B) ^ 2 / (2 * v₀')))
        + Real.exp (-((A + 2 * B) ^ 2 / (2 * V')))
        + 2 * Real.exp (-((M₁ - d₀') ^ 2 / (2 * σ')))
        + Real.exp (-((K₂ + D') ^ 2 / (2 * S'))))
      ≤ hp1StartV2 v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW := by
    unfold hp1StartV2
    have := mul_le_mul_of_nonneg_left htails hC
    linarith
  have hslope : 0 ≤ hp1Slope n₀ m₀ vmin vmax a A B L Klate σR2 := le_max_right _ _
  have hloss := hp1Loss_le_of_le (n₀ := n₀) (m₀ := m₀) (vmin := vmin) (L := L)
    (Klate := Klate) (σR2 := σR2) hC hB hV'
  unfold hp1LowerBoundV2
  have := mul_le_mul_of_nonneg_left hstart hslope
  linarith

/-! ### One cell of the lower sum, by rational bounds -/

/-- `φ(z) ≤ 0.3989422805·e` from `e^{-z²/2} ≤ e`. -/
lemma gaussianPDFReal_zero_one_le {z e : ℝ} (he : Real.exp (-(z ^ 2 / 2)) ≤ e) :
    gaussianPDFReal 0 1 z ≤ 0.3989422805 * e := by
  rw [gaussianPDFReal_zero_one]
  exact mul_le_mul inv_sqrt_two_pi_bounds.2 he (Real.exp_pos _).le (by norm_num)

/-- `0.3989422804·e ≤ φ(z)` from `e ≤ e^{-z²/2}`, `e ≥ 0`. -/
lemma le_gaussianPDFReal_zero_one {z e : ℝ} (he : e ≤ Real.exp (-(z ^ 2 / 2))) (he0 : 0 ≤ e) :
    0.3989422804 * e ≤ gaussianPDFReal 0 1 z := by
  rw [gaussianPDFReal_zero_one]
  exact mul_le_mul inv_sqrt_two_pi_bounds.1 he he0 (by positivity)

/-- **One cell of `RMF.sum_le_startMainV2`, by rational bounds.**  The cell's exit factor is
bounded below by `RMF.le_exitMean` at `R₁ = s²` and the threshold `w = sq` (any `q`), with
`Φ(q) ≥ p_q`, `Φ(q - ts) ≤ p'_q`, `e^{t(m+L+ρ)+Λ+t²R₁/2} ≤ E`, `1 - e^{-A_W} ≥ c`,
`t²(1 - e^{-A_W})/2 ≤ K'`, and the location `m̄ ≤ m` (antitone); the cell's weight by
`Φ(z₂) ≥ p₂`, `Φ(z₁) ≤ p₁`, `φ(z₁) ≤ φ₁`, `φ(z₂) ≥ φ₂` and `√V ∈ [r₁, r₂]`.  All the inputs are
point inequalities between numerals. -/
theorem cell_le {a sV r₁ r₂ t L ρ Λ AW R₁ R₂ s q m mb z₁ z₂ c Eq K' pq pq' p₁ p₂ φ₁ φ₂ : ℝ}
    (hs : 0 < s) (hR₁ : R₁ = s ^ 2) (hR : R₁ ≤ R₂) (ht : 0 ≤ t) (hmb : mb ≤ m)
    (hpq : pq ≤ normCDF q) (hpq0 : 0 ≤ pq) (hpq' : normCDF (q - t * s) ≤ pq')
    (hE : Real.exp (t * (m + L + ρ) + Λ + t ^ 2 * R₁ / 2) ≤ Eq)
    (hc : c ≤ 1 - Real.exp (-AW)) (hc0 : 0 ≤ c) (hK : t ^ 2 * (1 - Real.exp (-AW)) / 2 ≤ K')
    (hγ : 0 ≤ c * pq - Eq * pq' - K' * (R₂ - R₁))
    (hp₂ : p₂ ≤ normCDF z₂) (hp₁ : normCDF z₁ ≤ p₁)
    (hφ₁ : gaussianPDFReal 0 1 z₁ ≤ φ₁) (hφ₂ : φ₂ ≤ gaussianPDFReal 0 1 z₂)
    (hsV : r₁ ≤ sV ∧ sV ≤ r₂) (hr₁ : 0 ≤ r₁) (ha : 0 ≤ a)
    (hf : 0 ≤ a * (p₂ - p₁) - max (r₁ * (φ₁ - φ₂)) (r₂ * (φ₁ - φ₂))) :
    (c * pq - Eq * pq' - K' * (R₂ - R₁))
        * (a * (p₂ - p₁) - max (r₁ * (φ₁ - φ₂)) (r₂ * (φ₁ - φ₂)))
      ≤ max (exitMean t L ρ Λ AW mb R₁ - t ^ 2 * (1 - Real.exp (-AW)) / 2 * (R₂ - R₁)) 0
        * (a * (normCDF z₂ - normCDF z₁)
          - sV * (gaussianPDFReal 0 1 z₁ - gaussianPDFReal 0 1 z₂)) := by
  have hR₁0 : 0 < R₁ := by rw [hR₁]; positivity
  have hsq : √R₁ = s := by rw [hR₁, Real.sqrt_sq hs.le]
  -- the exit factor
  have hex := le_exitMean hR₁0 t L ρ Λ AW m (s * q)
  rw [hsq, mul_div_cancel_left₀ q hs.ne'] at hex
  have hmono := exitMean_antitone ht L ρ Λ AW R₁ hmb
  have hPq' : 0 ≤ normCDF (q - t * s) := normCDF_nonneg _
  have hE0 : 0 ≤ Real.exp (t * (m + L + ρ) + Λ + t ^ 2 * R₁ / 2) := (Real.exp_pos _).le
  have h1 : c * pq ≤ (1 - Real.exp (-AW)) * normCDF q := mul_le_mul hc hpq hpq0 (by linarith)
  have h2 : Real.exp (t * (m + L + ρ) + Λ + t ^ 2 * R₁ / 2) * normCDF (q - t * s)
      ≤ Eq * pq' := mul_le_mul hE hpq' hPq' (le_trans hE0 hE)
  have h3 : t ^ 2 * (1 - Real.exp (-AW)) / 2 * (R₂ - R₁) ≤ K' * (R₂ - R₁) :=
    mul_le_mul_of_nonneg_right hK (by linarith)
  have hIb : c * pq - Eq * pq' - K' * (R₂ - R₁)
      ≤ max (exitMean t L ρ Λ AW mb R₁ - t ^ 2 * (1 - Real.exp (-AW)) / 2 * (R₂ - R₁)) 0 :=
    le_max_of_le_left (by linarith)
  -- the weight
  have hφ : sV * (gaussianPDFReal 0 1 z₁ - gaussianPDFReal 0 1 z₂)
      ≤ max (r₁ * (φ₁ - φ₂)) (r₂ * (φ₁ - φ₂)) := by
    have hsV0 : 0 ≤ sV := le_trans hr₁ hsV.1
    have h4 : sV * (gaussianPDFReal 0 1 z₁ - gaussianPDFReal 0 1 z₂) ≤ sV * (φ₁ - φ₂) :=
      mul_le_mul_of_nonneg_left (by linarith) hsV0
    rcases le_total 0 (φ₁ - φ₂) with hd | hd
    · exact le_trans h4 (le_max_of_le_right (mul_le_mul_of_nonneg_right hsV.2 hd))
    · exact le_trans h4 (le_max_of_le_left (mul_le_mul_of_nonpos_right hsV.1 hd))
  have hF : a * (p₂ - p₁) - max (r₁ * (φ₁ - φ₂)) (r₂ * (φ₁ - φ₂))
      ≤ a * (normCDF z₂ - normCDF z₁) - sV * (gaussianPDFReal 0 1 z₁ - gaussianPDFReal 0 1 z₂) := by
    have := mul_le_mul_of_nonneg_left (by linarith : p₂ - p₁ ≤ normCDF z₂ - normCDF z₁) ha
    linarith
  exact mul_le_mul hIb hF hf (le_trans hγ hIb)

/-! ### The nodes of the lower sums -/

/-- The nodes `z_i = -17/4 + 3i/20` of the lower sums. -/
noncomputable def sampleNodes (i : ℕ) : ℝ := -17 / 4 + 3 / 20 * i

lemma monotone_sampleNodes : Monotone sampleNodes := fun i j hij => by
  unfold sampleNodes
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

lemma sample_c : (0.9975 : ℝ) ≤ 1 - Real.exp (-6) := by
  have : Real.exp (-6) ≤ 0.0025 := by interval_decide (trust := kernel)
  linarith

end RMF
