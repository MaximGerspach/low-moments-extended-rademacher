/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperExplicit
import RMF.Probability.GaussianNumerals
import RMF.NumberTheory.MertensExplicit
import LeanCert.Tactic.IntervalAuto

/-!
# Numeral bounds for constants of Harper's upper bound

Numeral bounds on constants of the chain beneath `RMF.harper_upper_numeral`:

* Mertens' constants: `|M| ≤ 3/2` (with `RMF.mertens_const_le`), `primesBelowInvLogLogConst ≤ 15.5`,
  `blockRangeSumConst ≤ 50`;
* the chaining, `chainSharpConst 7 (2/10⁴) ≤ e^{20.3}` and `indexSharpConst 2 ≤ e^{33.1}`;
* the upper half of Proposition 5 (`RMF/Probability/BlockComparisonSharp.lean`):
  `prop5UpperThreshold 0 ≤ 17`, so the block offset is `freeStartHarperD 0 ≤ 18`;
* the bad sets' level `harperBadLevel 0 ≤ 32`, and `ζ(4) ≤ 4/3`;
* the reduction's constants, `reductionUpperConst ≤ e^{122}`, and the level of
  `RMF.harper_upper_numeral`: `N = 99²` blocks, the chaos's start `ℓ₀ = 9900` and the reduction's
  `Λ = 10⁴`, with `log 10⁴ ≤ 37/4`.
-/

open MeasureTheory
open scoped Real

namespace RMF

/-! ### Mertens' constants -/

lemma sum_range_inv_sq_add_two_le (m : ℕ) :
    ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 2) ^ 2 ≤ 1 - 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hkey : 1 / ((m : ℝ) + 2) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / (((m + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      push_cast at hkey ⊢
      linarith

lemma log_four_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)

lemma mertensSecondConst_nonneg : 0 ≤ mertensSecondConst := by
  unfold mertensSecondConst
  have h1 : 0 ≤ Real.log 4 + 6 + Mertens.E₁ := by
    have := Mertens.E₁.nonneg
    linarith [log_four_nonneg]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- `∑_p 1/p² ≤ 1`. -/
lemma primeInvSqSum_le_one : primeInvSqSum ≤ 1 := by
  unfold primeInvSqSum
  refine Real.tsum_le_of_sum_range_le (fun n => by split_ifs <;> positivity) fun N => ?_
  rcases N with _ | _ | N
  · simp
  · simp [Nat.not_prime_zero]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hterm : ∀ i ∈ Finset.range N,
        (if (i + 1 + 1).Prime then 1 / (((i + 1 + 1 : ℕ) : ℝ)) ^ 2 else 0)
          ≤ 1 / ((i : ℝ) + 2) ^ 2 := by
      intro i _
      split_ifs
      · push_cast
        ring_nf
        exact le_rfl
      · positivity
    have h := sum_range_inv_sq_add_two_le N
    have hsum := Finset.sum_le_sum hterm
    have h0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
    simp only [Nat.not_prime_zero, Nat.not_prime_one, if_false, zero_add, add_zero]
    linarith

lemma summable_primeInvSq : Summable fun n : ℕ => (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0) := by
  refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
    (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  split_ifs
  · exact le_rfl
  · positivity

/-- **`|M| ≤ 3/2`**: `M ≤ 0.2641` (`RMF.mertens_const_le`), and `M = γ + ∑_p (log(1-1/p) + 1/p)`
with every summand at least `-2/p²` (`Mertens.M_eq_summand_bound`) and `γ > 1/2`. -/
lemma abs_mertens_M_le : |Mertens.M| ≤ 3 / 2 := by
  have hM := Mertens.M.eq
  rw [Mertens.γ.eq_eulerMascheroni] at hM
  have hMeq : Mertens.M = Real.eulerMascheroniConstant + ∑' p : ℕ, Mertens.M_eq_summand p := hM
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hS : Summable Mertens.M_eq_summand := Mertens.M_eq_summable
  have hP := summable_primeInvSq
  have hle : ∀ n : ℕ, -(2 * (if n.Prime then 1 / ((n : ℝ)) ^ 2 else 0))
      ≤ Mertens.M_eq_summand n := by
    intro n
    have hb := (abs_le.1 (Mertens.M_eq_summand_bound n)).1
    unfold Mertens.M_eq_summand at hb ⊢
    split_ifs with h
    · rw [if_pos h, div_eq_mul_one_div] at hb
      linarith
    · simp
  have hT := Summable.tsum_le_tsum hle (hP.mul_left 2).neg hS
  rw [tsum_neg, tsum_mul_left] at hT
  have hup := mertens_const_le
  have hsq : primeInvSqSum ≤ 1 := primeInvSqSum_le_one
  unfold primeInvSqSum at hsq
  rw [abs_le]
  constructor <;> linarith

/-- `mertensSecondConst ≤ 14.5`: `|M| ≤ 3/2` and `log 4 + 6 + E₁ ≤ 9.0028`. -/
lemma mertensSecondConst_le : mertensSecondConst ≤ 14.5 := by
  unfold mertensSecondConst
  have hM := abs_mertens_M_le
  have hE := mertens_error_const_le
  have hE0 := Mertens.E₁.nonneg
  have hl2 := Real.log_two_gt_d9
  have hnum : (Real.log 4 + 6 + Mertens.E₁) / Real.log 2 ≤ 9.0028 / 0.6931471803 :=
    div_le_div₀ (by norm_num) hE (by norm_num) hl2.le
  have h : (9.0028 : ℝ) / 0.6931471803 ≤ 13 := by norm_num
  linarith

lemma primesBelowInvLogLogConst_nonneg : 0 ≤ primesBelowInvLogLogConst := by
  unfold primesBelowInvLogLogConst
  positivity

/-- `primesBelowInvLogLogConst ≤ 15.5`. -/
lemma primesBelowInvLogLogConst_le : primesBelowInvLogLogConst ≤ 15.5 := by
  unfold primesBelowInvLogLogConst
  rw [abs_of_nonneg mertensSecondConst_nonneg]
  linarith [mertensSecondConst_le]

/-! ### The chaining constant -/

/-- `chainSharpConst 7 (2/10⁴) ≤ e^{20.3}`. -/
lemma chainSharpConst_le : chainSharpConst 7 (2 / 10000) ≤ Real.exp 20.3 := by
  unfold chainSharpConst chainSharpBase chainSharpSum
  have hn1 : (1 : ℝ) + 2 * 7 = 15 := by norm_num
  have hn2 : (2 : ℝ) * (17 * 7 / 16) = 119 / 8 := by norm_num
  have hn3 : ((119 : ℝ) / 8) ^ 2 / (2 * (1 / (96 * (2 / 10000)))) = 42483 / 20000 := by norm_num
  have hn4 : (1 : ℝ) / (96 * (2 / 10000)) / 2 = 625 / 24 := by norm_num
  rw [hn1, hn2, hn3, hn4]
  have hsmall : Real.exp (-(625 / 24)) ≤ 1 / 1000 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h26 := pow_le_exp_nat_of_le (n := 26) (by norm_num : (0 : ℝ) ≤ 2.718) exp_one_gt_2718.le
    have hmono : Real.exp ((26 : ℕ) : ℝ) ≤ Real.exp (625 / 24) := Real.exp_le_exp.2 (by norm_num)
    have hnum : (1 / 1000 : ℝ)⁻¹ ≤ 2.718 ^ 26 := by norm_num
    linarith
  have hinv : (1 - Real.exp (-(625 / 24)))⁻¹ ≤ 1.0011 := by
    have hpos : (0 : ℝ) < 1 - Real.exp (-(625 / 24)) := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    have : (1.0011 : ℝ)⁻¹ ≤ 1 - 1 / 1000 := by norm_num
    linarith
  have hinv0 : (0 : ℝ) ≤ (1 - Real.exp (-(625 / 24)))⁻¹ := by
    have hpos : (0 : ℝ) < 1 - Real.exp (-(625 / 24)) := by linarith
    positivity
  -- the dominant term is `8·e^{1 + 119/8 + 42483/20000}·(1 - ε)⁻¹ ≤ 8.0088·e^{18}`
  have hcomb : Real.exp 1 * (8 * Real.exp (119 / 8) * (Real.exp (42483 / 20000)
      * (1 - Real.exp (-(625 / 24)))⁻¹))
      = 8 * Real.exp (1 + 119 / 8 + 42483 / 20000) * (1 - Real.exp (-(625 / 24)))⁻¹ := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hcomb]
  have he18 : Real.exp (1 + 119 / 8 + 42483 / 20000) ≤ Real.exp 18 :=
    Real.exp_le_exp.2 (by norm_num)
  have hdom : 8 * Real.exp (1 + 119 / 8 + 42483 / 20000) * (1 - Real.exp (-(625 / 24)))⁻¹
      ≤ 8 * Real.exp 18 * 1.0011 :=
    mul_le_mul (mul_le_mul_of_nonneg_left he18 (by norm_num)) hinv hinv0 (by positivity)
  have h15 : Real.exp 15 ≤ Real.exp 18 * (1 / 20) := by
    have he3 : (20 : ℝ) ≤ Real.exp 3 := by
      have h := pow_le_exp_nat_of_le (n := 3) (by norm_num : (0 : ℝ) ≤ 2.718) exp_one_gt_2718.le
      norm_num at h ⊢
      linarith
    have hsplit : Real.exp 18 = Real.exp 15 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    rw [hsplit]
    nlinarith [Real.exp_pos 15]
  have h7 : Real.exp 7 ≤ Real.exp 18 * (1 / 20) :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) h15
  have h23 : (8.12 : ℝ) ≤ Real.exp 2.3 := by
    have he2 : (7.389 : ℝ) ≤ Real.exp 2 := by
      have h := pow_le_exp_nat_of_le (n := 2) (by norm_num : (0 : ℝ) ≤ 2.71828) (by
        have := Real.exp_one_gt_d9
        linarith)
      norm_num at h ⊢
      linarith
    have he03 : (1.345 : ℝ) ≤ Real.exp 0.3 := by
      have := Real.quadratic_le_exp_of_nonneg (x := (0.3 : ℝ)) (by norm_num)
      norm_num at this ⊢
      linarith
    have hsplit : Real.exp 2.3 = Real.exp 2 * Real.exp 0.3 := by
      rw [← Real.exp_add]
      norm_num
    rw [hsplit]
    nlinarith
  have hfin : Real.exp 20.3 = Real.exp 18 * Real.exp 2.3 := by
    rw [← Real.exp_add]
    norm_num
  rw [hfin]
  have hE : (0 : ℝ) < Real.exp 18 := Real.exp_pos 18
  nlinarith

/-- `indexSharpConst 2 ≤ e^{33.1}`. -/
lemma indexSharpConst_two_le : indexSharpConst 2 ≤ Real.exp 33.1 := by
  unfold indexSharpConst
  rw [show indexSharpRefine = 10000 from rfl]
  have hc := chainSharpConst_le
  have hc0 : (0 : ℝ) ≤ chainSharpConst 7 (2 / 10000) := (chainSharpConst_pos (by norm_num)).le
  have h108 : (40000 : ℝ) ≤ Real.exp 10.8 := by
    have he10 := pow_le_exp_nat_of_le (n := 10) (by norm_num : (0 : ℝ) ≤ 2.718)
      exp_one_gt_2718.le
    have he08 : (2.12 : ℝ) ≤ Real.exp 0.8 := by
      have := Real.quadratic_le_exp_of_nonneg (x := (0.8 : ℝ)) (by norm_num)
      norm_num at this ⊢
      linarith
    have hsplit : Real.exp 10.8 = Real.exp ((10 : ℕ) : ℝ) * Real.exp 0.8 := by
      rw [← Real.exp_add]
      norm_num
    rw [hsplit]
    have h1 : (21900 : ℝ) ≤ Real.exp ((10 : ℕ) : ℝ) := by
      have h2 : (21900 : ℝ) ≤ 2.718 ^ 10 := by norm_num
      exact le_trans h2 he10
    nlinarith [Real.exp_pos ((10 : ℕ) : ℝ)]
  have hfin : Real.exp 33.1 = Real.exp 10.8 * Real.exp 20.3 * Real.exp 2 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [hfin]
  have h1 : 4 * (10000 : ℝ) * chainSharpConst 7 (2 / 10000) ≤ Real.exp 10.8 * Real.exp 20.3 :=
    mul_le_mul (by linarith) hc hc0 (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos 2).le

/-! ### The upper half of Proposition 5 -/

/-- `2.4·10⁷ ≤ e^{17}`. -/
lemma exp_seventeen_ge : (24000000 : ℝ) ≤ Real.exp 17 := by
  have h := pow_le_exp_nat_of_le (n := 17) (by norm_num : (0 : ℝ) ≤ 2.718) exp_one_gt_2718.le
  have hnum : (24000000 : ℝ) ≤ 2.718 ^ 17 := by norm_num
  push_cast at h
  linarith

/-- The direct threshold of the upper half at the slope `20` is at most `17`:
`10·(65 + 128 + e² + 1)²/0.03 ≤ 2.4·10⁷`. -/
lemma thrDirectThreshold_upper_zero_le :
    thrDirectThreshold (2 * Real.exp (2 * 0)) (25 + 2 * prop5UpperSlope)
      (48 + 4 * prop5UpperSlope) 1 (3 / 100) ≤ 17 := by
  unfold thrDirectThreshold
  rw [prop5UpperSlope_eq]
  have he2 := exp_two_le_eight
  have hbase : 25 + 2 * (20 : ℝ) + (48 + 4 * 20) + Real.exp 2 + 1 ≤ 202 := by linarith
  have hbase0 : (0 : ℝ) < 25 + 2 * (20 : ℝ) + (48 + 4 * 20) + Real.exp 2 + 1 := by
    linarith [Real.exp_pos 2]
  rw [show 2 * Real.exp (2 * 0) = (2 : ℝ) by norm_num, Real.log_le_iff_le_exp (by positivity)]
  calc 5 * 2 * (25 + 2 * (20 : ℝ) + (48 + 4 * 20) + Real.exp 2 + 1) ^ 2 / (3 / 100)
      ≤ 5 * 2 * (202 : ℝ) ^ 2 / (3 / 100) := by gcongr
    _ ≤ 24000000 := by norm_num
    _ ≤ Real.exp 17 := exp_seventeen_ge

/-- **`prop5UpperThreshold 0 ≤ 17`**: every term of the nested maximum is at most `17`. -/
lemma prop5UpperThreshold_zero_le : prop5UpperThreshold 0 ≤ 17 := by
  have h1 := thrDirectThreshold_upper_zero_le
  have h17 := exp_seventeen_ge
  have hlog14 : Real.log (14 + 2 * 0) ≤ 17 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    norm_num
    linarith
  have hbn : Real.log (200 * (10 + 0 + (3 * 0 + 8) / 4)) ≤ 17 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    norm_num
    linarith
  unfold prop5UpperThreshold proposition5UpperThreshold blockQThrThreshold blockNumThreshold
  exact max_le (max_le (max_le (max_le h1 (by norm_num)) hlog14) hbn)
    (max_le (by norm_num) hlog14)

/-- **The block offset is at most `18`**: `⌈prop5UpperThreshold 0⌉₊ + 1` with the threshold at most
`17`.  It is at least `17` (`RMF.le_freeStartHarperD`). -/
lemma freeStartHarperD_zero_le : freeStartHarperD 0 ≤ 18 := by
  unfold freeStartHarperD
  have : ⌈prop5UpperThreshold 0⌉₊ ≤ 17 :=
    Nat.ceil_le.2 (by exact_mod_cast prop5UpperThreshold_zero_le)
  omega

/-! ### The good set and the chaos moments -/

lemma harperSharpDeficit_zero : harperSharpDeficit 0 = 1 := by
  unfold harperSharpDeficit
  simp

/-- **The bad sets' level**: `harperBadLevel 0 ≤ 32`, the index barrier's `4·8Δ₁` at `Δ₁ = 1`. -/
lemma harperBadLevel_zero_le : harperBadLevel 0 ≤ 32 := by
  unfold harperBadLevel indexSharpLevel
  rw [harperSharpDeficit_zero]
  refine max_le (by norm_num) ?_
  have : max (8 * 1 : ℝ) 0 ≤ 8 := max_le (by norm_num) (by norm_num)
  linarith

/-! ### The reduction's constants -/

lemma exp_quarter_le : Real.exp (1 / 4) ≤ 1.2841 := by
  have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he := Real.exp_one_lt_d9
  have hle : Real.exp (1 / 4) ^ 4 ≤ (1.2841 : ℝ) ^ 4 := by
    rw [h4]
    norm_num
    linarith
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num)).1 hle

/-- `smoothCountConst ≤ e^{120}`. -/
lemma smoothCountConst_le : smoothCountConst ≤ Real.exp 120 := by
  unfold smoothCountConst
  refine Real.exp_le_exp.2 ?_
  have h1 := exp_quarter_le
  have h2 := primesBelowInvLogLogConst_le
  have h0 := primesBelowInvLogLogConst_nonneg
  have hE0 := (Real.exp_pos (1 / 4)).le
  calc 6 * Real.exp (1 / 4) * primesBelowInvLogLogConst ≤ 6 * 1.2841 * 15.5 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 h0 (by norm_num)
    _ ≤ 120 := by norm_num

lemma exp_two_ge_seven : (7 : ℝ) ≤ Real.exp 2 := by
  have h := pow_le_exp_nat_of_le (n := 2) (by norm_num : (0 : ℝ) ≤ 2.718) exp_one_gt_2718.le
  norm_num at h ⊢
  linarith

/-- `reductionUpperConst ≤ e^{122}`. -/
lemma reductionUpperConst_le : reductionUpperConst ≤ Real.exp 122 := by
  unfold reductionUpperConst smoothCountDecay roughCountConst
  have hS := smoothCountConst_le
  have hS0 : 0 ≤ smoothCountConst := by
    unfold smoothCountConst
    exact (Real.exp_pos _).le
  have h5 : (5 : ℝ) ≤ Real.exp 2 := by linarith [exp_two_ge_seven]
  have hsum : smoothCountConst + smoothCountConst / (1 / 4) ≤ Real.exp 122 := by
    have heq : smoothCountConst + smoothCountConst / (1 / 4) = 5 * smoothCountConst := by ring
    rw [heq]
    calc 5 * smoothCountConst ≤ Real.exp 2 * Real.exp 120 :=
          mul_le_mul h5 hS hS0 (Real.exp_pos _).le
      _ = Real.exp 122 := by
          rw [← Real.exp_add]
          norm_num
  have h3 : (3 : ℝ) / π ≤ Real.exp 122 :=
    le_trans ((div_le_one Real.pi_pos).2 Real.pi_gt_three.le) (Real.one_le_exp (by norm_num))
  exact max_le (Real.one_le_exp (by norm_num)) (max_le hsum h3)

/-! ### The level of `RMF.harper_upper_numeral` -/

/-- `log 10⁴ ≤ 37/4`: `e^{37/4} = e⁹·e^{1/4} ≥ 2.7182818283⁹·1.25 ≥ 10⁴`. -/
lemma log_ten_thousand_le : Real.log 10000 ≤ 37 / 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h9' : (2.7182818283 : ℝ) ^ 9 ≤ Real.exp 9 := by
    rw [h9]
    exact pow_le_pow_left₀ (by norm_num) he.le 9
  have hq : (1 : ℝ) + 1 / 4 ≤ Real.exp (1 / 4) := by
    linarith [Real.add_one_le_exp (1 / 4 : ℝ)]
  have hsplit : Real.exp (37 / 4) = Real.exp 9 * Real.exp (1 / 4) := by
    rw [← Real.exp_add]
    norm_num
  rw [hsplit]
  calc (10000 : ℝ) ≤ 2.7182818283 ^ 9 * (1 + 1 / 4) := by norm_num
    _ ≤ Real.exp 9 * Real.exp (1 / 4) := mul_le_mul h9' hq (by norm_num) (Real.exp_pos _).le

/-- `√(99²) = 99`, the square root of the block count `N = 9801`. -/
lemma sqrt_nine_thousand_eight_hundred_one : Real.sqrt ((9801 : ℕ) : ℝ) = 99 := by
  rw [show ((9801 : ℕ) : ℝ) = 99 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The block count `N = 9801` grows the room at `δ = 1/100`: `3 ≤ 8δ√N = 7.92`. -/
lemma harper_level_room_mono : (3 : ℝ) ≤ 8 * (1 / 100) * Real.sqrt ((9801 : ℕ) : ℝ) := by
  rw [sqrt_nine_thousand_eight_hundred_one]
  norm_num

/-- The chaos's start pays for the blocks: `D + N ≤ 9900` for `D = freeStartHarperD 0 ≤ 18`. -/
lemma harper_level_blocks : (freeStartHarperD 0 : ℝ) + ((9801 : ℕ) : ℝ) ≤ 9900 := by
  have h : (freeStartHarperD 0 : ℝ) ≤ 18 := by exact_mod_cast freeStartHarperD_zero_le
  push_cast
  linarith

/-- The chaos's start pays for `k = 1.001`: `k²(D + 1)/(k² - 1) ≤ 9900`, the left side being at
most `9514.3`. -/
lemma harper_level_k :
    (1001 / 1000 : ℝ) ^ 2 * ((freeStartHarperD 0 : ℝ) + 1) / ((1001 / 1000) ^ 2 - 1) ≤ 9900 := by
  have h : (freeStartHarperD 0 : ℝ) ≤ 18 := by exact_mod_cast freeStartHarperD_zero_le
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- The chaos's start pays for Mertens' product at `L₀ = 10⁶`: `10⁶ + 1 ≤ e^{9900}`. -/
lemma harper_level_mertens : (1000000 : ℝ) + 1 ≤ Real.exp 9900 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 9900) (by norm_num)
  norm_num at h ⊢
  linarith

/-- The reduction's level reaches the chaos's start: `9900 + 1 + 2 log 10⁴ ≤ 10⁴`. -/
lemma harper_level_start : (9900 : ℝ) + 1 + 2 * Real.log 10000 ≤ 10000 := by
  linarith [log_ten_thousand_le]

/-- The reduction's level pays for the cutoff's cost `k = 1.001`:
`k²(2 log 10⁴ + 1) ≤ (k² - 1)·10⁴`, that is `19.54 ≤ 20.01`. -/
lemma harper_level_cutoff :
    (1001 / 1000 : ℝ) ^ 2 * (2 * Real.log 10000 + 1) ≤ ((1001 / 1000) ^ 2 - 1) * 10000 := by
  have h := log_ten_thousand_le
  norm_num
  linarith

/-- The reduction's level pays for the Rankin term: `3(|log C_R| + K_R)/c_R ≤ 10⁴`, from
`C_R ≤ e^{122}`, `K_R = 6e^{1/4} + 1 ≤ 8.71` and `c_R = 1/16`. -/
lemma harper_level_rankin :
    3 * (|Real.log reductionUpperConst| + reductionUpperExponent) / reductionUpperDecay
      ≤ 10000 := by
  have hC1 : (1 : ℝ) ≤ reductionUpperConst := le_max_left _ _
  have hlog : Real.log reductionUpperConst ≤ 122 := by
    calc Real.log reductionUpperConst ≤ Real.log (Real.exp 122) :=
          Real.log_le_log (by linarith) reductionUpperConst_le
      _ = 122 := Real.log_exp 122
  rw [abs_of_nonneg (Real.log_nonneg hC1)]
  unfold reductionUpperExponent reductionUpperDecay smoothCountExponent smoothCountDecay
  have hq := exp_quarter_le
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- The reduction's level pays for `η = 1/100`: `6(1 + |log(1/100)|)/c_R ≤ 10⁴`. -/
lemma harper_level_eta : 6 * (1 + |Real.log (1 / 100)|) / reductionUpperDecay ≤ 10000 := by
  have h1 : |Real.log (1 / 100)| = Real.log 100 := by
    rw [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg (by norm_num))]
  have h2 : Real.log 100 ≤ 99 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)]
  unfold reductionUpperDecay smoothCountDecay
  rw [h1, div_le_iff₀ (by norm_num)]
  linarith

/-- **Below `x₀ = exp(exp 10⁴)` the trivial bound costs at most `16`**:
`(1 + 100(1-q))^q ≤ 16` for `q ∈ [0, 1]` (the maximum is `11.6`, near `q = 0.77`), on the six
intervals `[0, 1/2]`, `[1/2, 3/5]`, …, `[9/10, 1]` (`RMF.one_add_mul_rpow_le_of_end`). -/
lemma harper_level_small_range {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 + (1 - q) * Real.sqrt (Real.log (Real.log (Real.exp (Real.exp 10000))))) ^ q ≤ 16 := by
  rw [Real.log_exp, Real.log_exp, show (10000 : ℝ) = 100 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  rcases le_or_gt q (1 / 2) with h1 | h1
  · exact le_trans (one_add_mul_rpow_le_of_end (q₁ := 0) (q₂ := 1 / 2) (by norm_num) le_rfl hq0 h1
      (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (3 / 5) with h2 | h2
  · exact le_trans (one_add_mul_rpow_le_of_end (q₁ := 1 / 2) (q₂ := 3 / 5) (by norm_num)
      (by norm_num) h1.le h2 (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (7 / 10) with h3 | h3
  · exact le_trans (one_add_mul_rpow_le_of_end (q₁ := 3 / 5) (q₂ := 7 / 10) (by norm_num)
      (by norm_num) h2.le h3 (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (4 / 5) with h4 | h4
  · exact le_trans (one_add_mul_rpow_le_of_end (q₁ := 7 / 10) (q₂ := 4 / 5) (by norm_num)
      (by norm_num) h3.le h4 (by norm_num)) (by interval_decide (trust := kernel))
  rcases le_or_gt q (9 / 10) with h5 | h5
  · exact le_trans (one_add_mul_rpow_le_of_end (q₁ := 4 / 5) (q₂ := 9 / 10) (by norm_num)
      (by norm_num) h4.le h5 (by norm_num)) (by interval_decide (trust := kernel))
  exact le_trans (one_add_mul_rpow_le_of_end (q₁ := 9 / 10) (q₂ := 1) (by norm_num)
    (by norm_num) h5.le hq1 le_rfl) (by interval_decide (trust := kernel))

end RMF
