/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChainingSharp

/-!
# Numerals for the sharp chaining

Crude numeral bounds on the constants of `RMF/EulerProduct/JointLaplaceSharp.lean` at the one
instantiation the chaos moments use, `σ₀ = 1/2`, `Λ₁ = 7`:

* `RMF.tsum_nat_rpow_neg_le`: `∑_n n^{-s} ≤ s/(s-1)` for `s > 1`, by comparison with `∫_1^∞ x^{-s}`;
* `RMF.multiTailConst_seven_le`: `multiTailConst 7 (1/2) 1 ≤ 5·10²³`;
* `RMF.pairTailConst_fourteen_le`: `pairTailConst (1/2) 14 ≤ 2·10¹³`;
* `RMF.chainSharpThreshold_le`: `chainSharpThreshold (1/2) 7 ≤ 10¹⁰⁷ ≤ exp(e^{16})`, so every
  block of Harper's scales, which starts past `exp(e^{D-1})`, `D ≥ 17`, is past the threshold
  (`RMF.chainSharpThreshold_le_exp_exp_sixteen`).
-/

open Finset

namespace RMF

/-- **`∑_{n ≥ 0} n^{-s} ≤ s/(s-1)`** for `s > 1`: the term `n = 0` is `0`, the term `n = 1` is `1`,
and `∑_{n ≥ 2} n^{-s} ≤ ∫_1^∞ x^{-s} dx = 1/(s-1)`. -/
lemma tsum_nat_rpow_neg_le {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ s / (s - 1) := by
  have hs0 : (-s : ℝ) ≠ 0 := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hint : ∀ M : ℕ, ∑ i ∈ Finset.range M, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s)
      ≤ 1 / (s - 1) := by
    intro M
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc 1 (1 + (M : ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    refine le_trans hanti.sum_le_integral ?_
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (M : ℝ)) := by
      rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) M])]
      intro h
      linarith [h.1]
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), Real.one_rpow]
    have hpow : (0 : ℝ) ≤ (1 + (M : ℝ)) ^ (-s + 1) := Real.rpow_nonneg (by positivity) _
    have heq : ((1 + (M : ℝ)) ^ (-s + 1) - 1) / (-s + 1)
        = (1 - (1 + (M : ℝ)) ^ (-s + 1)) / (s - 1) := by
      have h1 : (-s + 1 : ℝ) ≠ 0 := by linarith
      have h2 : (s - 1 : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) fun N => ?_
  have hpos : (0 : ℝ) ≤ s / (s - 1) := div_nonneg (by linarith) hs1.le
  rcases N with _ | _ | M
  · simpa using hpos
  · simpa [Real.zero_rpow hs0] using hpos
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hterm : ∀ i ∈ Finset.range M, ((i + 1 + 1 : ℕ) : ℝ) ^ (-s)
        = ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
      intro i _
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm]
    have h := hint M
    have hsplit : s / (s - 1) = 1 / (s - 1) + 1 := by
      field_simp
      ring
    simp only [Nat.cast_zero, Real.zero_rpow hs0, Nat.cast_one, Real.one_rpow, zero_add]
    rw [hsplit]
    linarith

/-- `2^{-1/2} ≤ 3/4`. -/
lemma two_rpow_neg_half_le : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have h : (4 / 3 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

lemma exp_one_le_three : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)

/-- `localMultiConst 7 1 ≤ 4·10⁶`. -/
lemma localMultiConst_seven_le : localMultiConst 7 1 ≤ 4000000 := by
  have he := exp_one_le_three
  have he35 : Real.exp (7 * (1 : ℕ) / 2) ≤ 81 := by
    have h1 : Real.exp (7 * (1 : ℕ) / 2) ≤ Real.exp 4 := Real.exp_le_exp.2 (by norm_num)
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
    linarith
  unfold localMultiConst
  have hd : (1 : ℝ) / (1 / (4 * (7 * ((1 : ℕ) : ℝ) + 1))) ^ 3 = 32768 := by norm_num
  have hrw : (Real.exp (7 * ((1 : ℕ) : ℝ) / 2) + (1 + (7 * ((1 : ℕ) : ℝ)) ^ 2 / 25))
      / (1 / (4 * (7 * ((1 : ℕ) : ℝ) + 1))) ^ 3
      = (Real.exp (7 * ((1 : ℕ) : ℝ) / 2) + (1 + (7 * ((1 : ℕ) : ℝ)) ^ 2 / 25)) * 32768 := by
    rw [div_eq_mul_one_div, hd]
  rw [hrw]
  push_cast at he35 ⊢
  nlinarith [Real.exp_pos 1]

/-- `localMultiLogConst 7 2^{-1/2} 1 ≤ 10²³`. -/
lemma localMultiLogConst_seven_le :
    localMultiLogConst 7 ((2 : ℝ) ^ (-(1 / 2 : ℝ))) 1 ≤ 100000000000000000000000 := by
  have hθ := two_rpow_neg_half_le
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hC₀ := localMultiConst_seven_le
  have hC₀0 : (0 : ℝ) ≤ localMultiConst 7 1 := by
    have := exists_local_multi_expansion_steinhausLaw_explicit ({0} : Finset ℕ)
      (Q := 7) (by norm_num)
    simpa using this.1.le
  have hlog : Real.log ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) ≤ 2 := by
    have h1 : (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have h2 : Real.log ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) ≤ Real.log 4 :=
      Real.log_le_log (by rw [inv_pos]; linarith) h1
    have h3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [this]
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) :=
    Real.log_nonneg (one_le_inv_iff₀.mpr ⟨by linarith, by linarith⟩)
  unfold localMultiLogConst logSubPolyConst
  push_cast
  set C₀ := localMultiConst 7 1 with hC₀def
  set L := Real.log ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) with hLdef
  have hmin : (1 : ℝ) / 10000000 ≤ min (1 / 5) (1 / (2 * ((7 * 1) ^ 2 + C₀ + 1))) := by
    refine le_min (by norm_num) ?_
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hmin0 : (0 : ℝ) < (1 : ℝ) / 10000000 := by norm_num
  have hcube : ((1 : ℝ) / 10000000) ^ 3
      ≤ (min (1 / 5) (1 / (2 * ((7 * 1) ^ 2 + C₀ + 1)))) ^ 3 :=
    pow_le_pow_left₀ hmin0.le hmin 3
  have hnum : (0 : ℝ) ≤ 2 * (7 * 1) * L + (7 * 1) ^ 2 := by positivity
  have hfrac : (2 * (7 * 1) * L + (7 * 1) ^ 2)
      / (min (1 / 5) (1 / (2 * ((7 * 1) ^ 2 + C₀ + 1)))) ^ 3
      ≤ 77 * 1000000000000000000000 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hcube)]
    have h1 : (77 : ℝ) * 1000000000000000000000 * ((1 : ℝ) / 10000000) ^ 3 = 77 := by norm_num
    nlinarith
  have hsq : 2 * ((7 * 1) ^ 2 + C₀) ^ 2 ≤ 2 * (4000049 : ℝ) ^ 2 := by
    have : (7 * 1 : ℝ) ^ 2 + C₀ ≤ 4000049 := by norm_num; linarith
    nlinarith
  linarith

/-- `multiTailConst 7 (1/2) 1 ≤ 5·10²³`. -/
lemma multiTailConst_seven_le : multiTailConst 7 (1 / 2) 1 ≤ 500000000000000000000000 := by
  have hC := localMultiLogConst_seven_le
  have hT := tsum_nat_rpow_neg_le (s := 3 * ((1 / 2 + 1 / 3) / 2)) (by norm_num)
  have hT' : ∑' k : ℕ, (k : ℝ) ^ (-3 * ((1 / 2 + 1 / 3) / 2 : ℝ)) ≤ 5 := by
    have he : (-3 * ((1 / 2 + 1 / 3) / 2 : ℝ)) = -(3 * ((1 / 2 + 1 / 3) / 2)) := by ring
    rw [he]
    refine le_trans hT (le_of_eq ?_)
    norm_num
  have hT0 : (0 : ℝ) ≤ ∑' k : ℕ, (k : ℝ) ^ (-3 * ((1 / 2 + 1 / 3) / 2 : ℝ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hC0 : (0 : ℝ) ≤ localMultiLogConst 7 ((2 : ℝ) ^ (-(1 / 2 : ℝ))) 1 := by
    have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hθ : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := lt_of_le_of_lt two_rpow_neg_half_le (by norm_num)
    have := exists_abs_log_local_multi_le_explicit ({0} : Finset ℕ) (Q := 7) (by norm_num) hθ0 hθ
    simpa using this.1.le
  unfold multiTailConst
  calc localMultiLogConst 7 ((2 : ℝ) ^ (-(1 / 2 : ℝ))) 1
        * ∑' k : ℕ, (k : ℝ) ^ (-3 * ((1 / 2 + 1 / 3) / 2 : ℝ))
      ≤ 100000000000000000000000 * 5 := mul_le_mul hC hT' hT0 (by norm_num)
    _ = 500000000000000000000000 := by norm_num

/-- `localPairConst 2^{-1/2} ≤ 2·10⁶`. -/
lemma localPairConst_le : localPairConst ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 2000000 := by
  have hθ := two_rpow_neg_half_le
  have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have he := exp_one_le_three
  set θ := (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hθdef
  have h1θ : (1 : ℝ) / 4 ≤ 1 - θ := by linarith
  have hCf : localPairFine θ ≤ 113 := by
    unfold localPairFine
    have h : 4 * Real.exp 1 / (1 - θ) ≤ 48 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hCf0 : (65 : ℝ) ≤ localPairFine θ := by
    unfold localPairFine
    have : (0 : ℝ) ≤ 4 * Real.exp 1 / (1 - θ) := div_nonneg (by positivity) (by linarith)
    linarith
  have hd : (1 : ℝ) / 456 ≤ localPairScale θ := by
    unfold localPairScale
    refine le_min (by linarith) ?_
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hd0 : (0 : ℝ) < localPairScale θ := lt_of_lt_of_le (by norm_num) hd
  have htail : localPairTail θ ≤ 1664000 := by
    unfold localPairTail
    have hsq : ((1 : ℝ) / 456) ^ 2 ≤ localPairScale θ ^ 2 := pow_le_pow_left₀ (by norm_num) hd 2
    have h1 : 2 / ((1 - θ) * localPairScale θ ^ 2) ≤ 2 / ((1 / 4) * (1 / 456) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul h1θ hsq (by positivity) (by linarith)
    have h2 : 1 / localPairScale θ ≤ 1 / (1 / 456) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    have h3 : (2 : ℝ) / ((1 / 4) * (1 / 456) ^ 2) + 1 / (1 / 456) ≤ 1664000 := by norm_num
    linarith
  unfold localPairConst
  have hsq : 2 * (1 + localPairFine θ) ^ 2 ≤ 2 * 114 ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 + localPairFine θ := by linarith
    nlinarith
  linarith

/-- `pairTailConst (1/2) 14 ≤ 2·10¹³`. -/
lemma pairTailConst_fourteen_le : pairTailConst (1 / 2) 14 ≤ 20000000000000 := by
  have hL := localPairConst_le
  have hL0 : (0 : ℝ) ≤ localPairConst ((2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hθ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hθ : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := lt_of_le_of_lt two_rpow_neg_half_le (by norm_num)
    exact (exists_abs_log_local_pair_le_explicit hθ0 hθ).1.le
  have hT := tsum_nat_rpow_neg_le (s := 3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2)) (by norm_num)
  have hT' : ∑' n : ℕ, (n : ℝ) ^ (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ)) ≤ 9 := by
    have he : (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ))
        = -(3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2)) := by ring
    rw [he]
    refine le_trans hT (le_of_eq ?_)
    norm_num
  have hT0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hK : (1 + (14 : ℝ) / 2 + 14 / 2 / ((1 / 2 - 1 / 3) / 2)) ^ 3 = 778688 := by norm_num
  unfold pairTailConst
  rw [hK]
  calc localPairConst ((2 : ℝ) ^ (-(1 / 2 : ℝ))) * 778688
        * ∑' n : ℕ, (n : ℝ) ^ (-3 * (((1 / 2 + 1 / 3) / 2 + 1 / 3) / 2 : ℝ))
      ≤ 2000000 * 778688 * 9 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (by norm_num)) hT' hT0 (by norm_num)
    _ ≤ 20000000000000 := by norm_num

/-- **The sharp chaining threshold, evaluated**: `chainSharpThreshold (1/2) 7 ≤ 10¹⁰⁷`. -/
lemma chainSharpThreshold_le : chainSharpThreshold (1 / 2) 7 ≤ (10 : ℝ) ^ 107 := by
  have hM := multiTailConst_seven_le
  have hM0 : (0 : ℝ) ≤ multiTailConst 7 (1 / 2) 1 := by
    simpa using multiTailConst_nonneg ({0} : Finset ℕ) (Q := 7) (σ₀ := 1 / 2) (by norm_num)
      (by norm_num)
  have hP := pairTailConst_fourteen_le
  have hP0 : (0 : ℝ) ≤ pairTailConst (1 / 2) (2 * 7) :=
    pairTailConst_nonneg (by norm_num) (by norm_num)
  have e1 : (3 * ((1 / 2 - 1 / 3) / 2 : ℝ))⁻¹ = ((4 : ℕ) : ℝ) := by norm_num
  have e2 : (3 * (((1 / 2 + 1 / 3) / 2 - 1 / 3) / 2 : ℝ))⁻¹ = ((8 : ℕ) : ℝ) := by norm_num
  have e3 : (2 : ℝ) * 7 = 14 := by norm_num
  unfold chainSharpThreshold
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast, e3]
  rw [e3] at hP0
  refine max_le (by norm_num) (max_le ?_ ?_)
  · calc multiTailConst 7 (1 / 2) 1 ^ 4 ≤ (500000000000000000000000 : ℝ) ^ 4 :=
          pow_le_pow_left₀ hM0 hM 4
      _ ≤ (10 : ℝ) ^ 107 := by norm_num
  · calc pairTailConst (1 / 2) 14 ^ 8 ≤ (20000000000000 : ℝ) ^ 8 :=
          pow_le_pow_left₀ hP0 hP 8
      _ ≤ (10 : ℝ) ^ 107 := by norm_num

/-- `10¹⁰⁷ ≤ exp(e^{16})`: `e^{16} = (e⁸)² ≥ 41² ≥ 1070`, and `exp(y/107) ≥ 1 + y/107 ≥ 10`. -/
lemma ten_pow_le_exp_exp_sixteen : (10 : ℝ) ^ 107 ≤ Real.exp (Real.exp 16) := by
  have h8 : (41 : ℝ) ≤ Real.exp 8 := by
    have h := Real.quadratic_le_exp_of_nonneg (x := (8 : ℝ)) (by norm_num)
    norm_num at h
    linarith
  have hy : (1681 : ℝ) ≤ Real.exp 16 := by
    have hsq : Real.exp 16 = Real.exp 8 * Real.exp 8 := by
      rw [← Real.exp_add]
      norm_num
    have h := mul_le_mul h8 h8 (by norm_num) (Real.exp_pos 8).le
    rw [hsq]
    linarith
  have h1 : (1 : ℝ) + Real.exp 16 / 107 ≤ Real.exp (Real.exp 16 / 107) := by
    linarith [Real.add_one_le_exp (Real.exp 16 / 107)]
  have h2 : (10 : ℝ) ≤ 1 + Real.exp 16 / 107 := by
    have : (1681 : ℝ) / 107 ≤ Real.exp 16 / 107 := div_le_div_of_nonneg_right hy (by norm_num)
    have h3 : (9 : ℝ) ≤ 1681 / 107 := by norm_num
    linarith
  have h4 : (10 : ℝ) ^ 107 ≤ Real.exp (Real.exp 16 / 107) ^ 107 :=
    pow_le_pow_left₀ (by norm_num) (le_trans h2 h1) 107
  have h5 : Real.exp (Real.exp 16 / 107) ^ 107 = Real.exp (Real.exp 16) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  linarith

/-- **`chainSharpThreshold (1/2) 7 ≤ exp(e^{16})`**: every block of Harper's scales at an offset
`ϑ ≥ 16` starts past the sharp chaining threshold. -/
lemma chainSharpThreshold_le_exp_exp_sixteen :
    chainSharpThreshold (1 / 2) 7 ≤ Real.exp (Real.exp 16) :=
  le_trans chainSharpThreshold_le ten_pow_le_exp_exp_sixteen

end RMF
