/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedReduction
import RMF.Weighted.SharpAboveHalf
import RMF.Weighted.FixedQAboveHalf
import RMF.Weighted.HalfInterface

/-!
# Extended Rademacher sums: the bounds that need no short-interval input

The fractional-part sum `R(x) = x^{-1/2}∑_{m≤x} X(m){√(x/m)}` has
`E|R(x)|² = x⁻¹∑_{m≤x, squarefree}{√(x/m)}² ≤ 1` (`RMF.integral_normSq_fracPartSum_le_one`), so
`E|R(x)|^{2q} ≤ 1` for `0 ≤ q ≤ 1` (`RMF.integral_rpow_norm_fracPartSum_le_one`): Proposition 3.2
of the paper for `½ ≤ q ≤ 1`.  Through the comparison of
`Weighted/ExtendedReduction.lean` (Proposition 3.1 of the paper), every weighted bound that
absorbs a constant transfers to `x^{-1/2}∑_{n≤x} X^e(n)`:

* the uniform upper bound for `½ < q ≤ 1` and `x ≥ e^e`
  (`RMF.exists_integral_rpow_norm_normalisedSum_compMultExtension_le_sharp_of_exp_exp_le`);
* the lower bound for fixed `½ < q ≤ 1`
  (`RMF.exists_le_integral_rpow_norm_normalisedSum_compMultExtension_of_le_one`);
* the lower bound at `q = ½`, `≫ (log log x)^{3/4}`
  (`RMF.exists_le_integral_norm_normalisedSum_compMultExtension_half`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `R(x) = ∑_{m≤x} c(m)f(m)` with `c(m) = {√(x/m)}/√x`. -/
lemma fracPartSum_eq_sum_mul (f : Ω → ArithmeticFunction ℂ) (x : ℝ) (ω : Ω) :
    fracPartSum f x ω = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ) * f ω n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **The mean square of `R(x)`**, which gives Proposition 3.2 of the paper for `½ ≤ q ≤ 1`.  For
`x ≥ 1`, `E|R(x)|² = x⁻¹∑_{m≤x, squarefree}{√(x/m)}² ≤ ⌊x⌋/x ≤ 1`, by orthogonality
(`RMF.integral_normSq_weightedSum_of_orthogonality'`) and `0 ≤ {·} < 1`. -/
theorem integral_normSq_fracPartSum_le_one {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ ω, ‖fracPartSum f x ω‖ ^ 2 ∂μ) ≤ 1 := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hne : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, n ≠ 0 := fun n hn =>
    Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hn).1
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ)
    (s := Finset.Icc 1 ⌊x⌋₊)
    (c := fun n : ℕ => ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ))
    (d := fun m => ((if Squarefree m then 1 else 0 : ℝ) : ℂ))
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hne m hm) (hne n hn)]
      by_cases h : m = n
      · subst h
        by_cases hs : Squarefree m <;> simp [hs]
      · simp [h])
  simp_rw [← fracPartSum_eq_sum_mul] at key
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hc : ∀ m : ℕ, ‖((Int.fract (Real.sqrt (x / m)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)‖
      = Int.fract (Real.sqrt (x / m)) / Real.sqrt x := fun m => by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg _), abs_of_nonneg hsx.le]
  simp_rw [hc] at key
  have hreal : (∫ ω, ‖fracPartSum f x ω‖ ^ 2 ∂μ)
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Int.fract (Real.sqrt (x / m)) / Real.sqrt x) ^ 2
          * (if Squarefree m then 1 else 0) := by
    exact_mod_cast key
  rw [hreal]
  have hx0 : (0 : ℝ) ≤ x⁻¹ := inv_nonneg.2 (by linarith)
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊x⌋₊,
      (Int.fract (Real.sqrt (x / m)) / Real.sqrt x) ^ 2 * (if Squarefree m then 1 else 0)
        ≤ x⁻¹ := by
    intro m _
    split_ifs
    · rw [mul_one, div_pow, Real.sq_sqrt (by linarith), div_eq_mul_inv]
      exact mul_le_of_le_one_left hx0 (pow_le_one₀ (Int.fract_nonneg _) (Int.fract_lt_one _).le)
    · rw [mul_zero]
      exact hx0
  calc ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Int.fract (Real.sqrt (x / m)) / Real.sqrt x) ^ 2
          * (if Squarefree m then 1 else 0)
      ≤ ∑ _m ∈ Finset.Icc 1 ⌊x⌋₊, x⁻¹ := Finset.sum_le_sum hterm
    _ = (⌊x⌋₊ : ℝ) * x⁻¹ := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by linarith)]
        exact Nat.floor_le (by linarith)

/-- `E|R(x)|^{2q} ≤ 1` for `x ≥ 1` and `0 ≤ q ≤ 1`, by Jensen from the mean square. -/
theorem integral_rpow_norm_fracPartSum_le_one {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ) ≤ 1 := by
  haveI := hX.isProbabilityMeasure
  have hint : Integrable (fun ω =>
      ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2) μ :=
    (integrable_rpow_norm_fracPartSum hX x (by norm_num : (0 : ℝ) ≤ 2)).congr
      (Filter.Eventually.of_forall fun ω => Real.rpow_two _)
  have hpow : ∀ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
      = (‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2) ^ q := fun ω => by
    rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  simp_rw [hpow]
  calc (∫ ω, (‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2) ^ q ∂μ)
      ≤ 1 ^ q := integral_rpow_le_rpow_of_integral_le hq0 hq1
        (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint
        (integral_normSq_fracPartSum_le_one hX.isRademacherRMF hx)
    _ = 1 := Real.one_rpow q

/-- **The uniform upper bound above `q = ½`, for the extended sum** (Theorem 1.1, upper
bound, `½ < q ≤ 1`).  There is `C`, independent of `X`, `q` and `x`, such that for every
Rademacher `X`, every `½ < q ≤ 1` and every `x ≥ e^e`,

`E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≤ C·(log x)^{q(2q-1)}·b(min{1/(2q-1), log log x})`,

`b = RMF.ballotFactor`: the weighted bound
`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp_of_exp_exp_le` for `S(x)`, the
comparison `RMF.integral_rpow_norm_normalisedSum_compMultExtension_le`, and `E|R(x)|^{2q} ≤ 1`,
absorbed since the right side is at least `C/2`. -/
theorem exists_integral_rpow_norm_normalisedSum_compMultExtension_le_sharp_of_exp_exp_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (q x : ℝ), 1 / 2 < q → q ≤ 1 → Real.exp (Real.exp 1) ≤ x →
        (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
          ≤ C * (Real.log x ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x)))) := by
  obtain ⟨C₀, hC₀, hS⟩ := exists_integral_rpow_norm_weightedRademacherSum_le_sharp_of_exp_exp_le
  refine ⟨2 * C₀ + 4, by linarith, ?_⟩
  intro X μ hX q x hq2 hq1 hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (Real.exp_pos 1).le) hx
  have hx0 : 0 < x := by linarith
  have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlx1 : 1 ≤ Real.log x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hlogx
  have hll1 : 1 ≤ Real.log (Real.log x) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlogx
    rwa [Real.log_exp] at h
  have hm1 : 1 ≤ min (2 * q - 1)⁻¹ (Real.log (Real.log x)) :=
    le_min ((one_le_inv₀ (by linarith)).2 (by linarith)) hll1
  have hb2 := half_le_ballotFactor (by linarith) hq1 hm1
  have hL1 : 1 ≤ Real.log x ^ (q * (2 * q - 1)) :=
    Real.one_le_rpow hlx1 (mul_nonneg (by linarith) (by linarith))
  have hR : 1 * (1 / 2) ≤ Real.log x ^ (q * (2 * q - 1))
      * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x))) :=
    mul_le_mul hL1 hb2 (by norm_num) (by linarith)
  have hcmp := integral_rpow_norm_normalisedSum_compMultExtension_le hX hx1 (by linarith) hq1
  have hSq := hS Ω X μ hX q x hq2 hq1 hx
  have hRq := integral_rpow_norm_fracPartSum_le_one hX hx1 (by linarith : (0 : ℝ) ≤ q) hq1
  linarith

/-- **The lower bound for fixed `½ < q ≤ 1`, for the extended sum** (Theorem 1.1, lower
bound).  For fixed `½ < q ≤ 1` there are `c > 0` and `x₀` with
`c·(log x)^{q(2q-1)} ≤ E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q}` for `x ≥ x₀`:
`RMF.exists_le_integral_rpow_weightedRademacherSum_of_le_one` for `S(x)`, the comparison
`RMF.le_integral_rpow_norm_normalisedSum_compMultExtension`, and `E|R(x)|^{2q} ≤ 1`, which is at
most a quarter of the weighted main term once `(log x)^{q(2q-1)} ≥ 4/c`. -/
theorem exists_le_integral_rpow_norm_normalisedSum_compMultExtension_of_le_one {q : ℝ}
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        c * Real.log x ^ (q * (2 * q - 1))
          ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
              ^ (2 * q) ∂μ := by
  obtain ⟨c, x₀, hc, hlow⟩ :=
    exists_le_integral_rpow_weightedRademacherSum_of_le_one (Ω := Ω) hq0 hq1
  have hα : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have h4c : (0 : ℝ) < 4 / c := div_pos (by norm_num) hc
  refine ⟨c / 4, max (max x₀ 1) (Real.exp ((4 / c) ^ (q * (2 * q - 1))⁻¹)),
    div_pos hc (by norm_num), ?_⟩
  intro X μ hX x hx
  have hx₀ : x₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp ((4 / c) ^ (q * (2 * q - 1))⁻¹) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlog : (4 / c) ^ (q * (2 * q - 1))⁻¹ ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hbig : 4 / c ≤ Real.log x ^ (q * (2 * q - 1)) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg h4c.le _) hlog hα.le
    rwa [← Real.rpow_mul h4c.le, inv_mul_cancel₀ hα.ne', Real.rpow_one] at h
  have hc4 : 1 ≤ c / 4 * Real.log x ^ (q * (2 * q - 1)) := by
    have h := mul_le_mul_of_nonneg_left hbig (div_pos hc (by norm_num : (0 : ℝ) < 4)).le
    rwa [div_mul_div_comm, mul_comm c 4, div_self (mul_ne_zero four_ne_zero hc.ne')] at h
  have hcmp := le_integral_rpow_norm_normalisedSum_compMultExtension hX hx1 (by linarith) hq1
  have hSq := hlow X μ hX x hx₀
  have hRq := integral_rpow_norm_fracPartSum_le_one hX hx1 (by linarith : (0 : ℝ) ≤ q) hq1
  linarith

/-- **The lower bound at `q = ½`, for the extended sum** (Theorem 1.1).  There are `c > 0`
and `x₀` with `c·(log log x)^{3/4} ≤ E|x^{-1/2}∑_{n≤x} X^e(n)|` for `x ≥ x₀`: the lower half of
`RMF.exists_integral_weightedRademacherSum_asymp_half`, the comparison at `q = ½`, and
`E|R(x)| ≤ 1`, at most a quarter of the weighted main term once `(log log x)^{3/4} ≥ 4/c`. -/
theorem exists_le_integral_norm_normalisedSum_compMultExtension_half :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x : ℝ, x₀ ≤ x →
        c * Real.log (Real.log x) ^ (3 / 4 : ℝ)
          ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ := by
  obtain ⟨c, C, x₀, hc, -, hS⟩ := exists_integral_weightedRademacherSum_asymp_half (Ω := Ω)
  have h4c : (0 : ℝ) < 4 / c := div_pos (by norm_num) hc
  refine ⟨c / 4, max (max x₀ 1) (Real.exp (Real.exp ((4 / c) ^ (4 / 3 : ℝ)))),
    div_pos hc (by norm_num), ?_⟩
  intro X μ hX x hx
  have hx₀ : x₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp (Real.exp ((4 / c) ^ (4 / 3 : ℝ))) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlx : Real.exp ((4 / c) ^ (4 / 3 : ℝ)) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hll : (4 / c) ^ (4 / 3 : ℝ) ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hlx)).2 hlx
  have hΛ : 4 / c ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg h4c.le _) hll (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rwa [← Real.rpow_mul h4c.le, show (4 / 3 : ℝ) * (3 / 4) = 1 by norm_num, Real.rpow_one] at h
  have hc4 : 1 ≤ c / 4 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hΛ (div_pos hc (by norm_num : (0 : ℝ) < 4)).le
    rwa [div_mul_div_comm, mul_comm c 4, div_self (mul_ne_zero four_ne_zero hc.ne')] at h
  have hcmp := le_integral_rpow_norm_normalisedSum_compMultExtension hX hx1 (q := 1 / 2)
    (by norm_num) (by norm_num)
  have hRq := integral_rpow_norm_fracPartSum_le_one hX hx1 (q := 1 / 2) (by norm_num) (by norm_num)
  simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at hcmp hRq
  have hSl := (hS X μ hX x hx₀).1
  linarith

end RMF
