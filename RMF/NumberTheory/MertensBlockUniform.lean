/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensExplicit

/-!
# Mertens over a block, with a small absolute constant

`RMF.sum_prime_Ioc_inv_le_of_log_le'`: for `2 ≤ y ≤ z`, `1 ≤ Λ` and `log z ≤ Λ·log y`,

`∑_{y < p ≤ z} 1/p ≤ log Λ + 1.86`,

with **no largeness hypothesis** on `y`, `z` or `Λ`.  It is a drop-in replacement for
`RMF.sum_prime_Ioc_inv_le_of_log_le` (`RMF/NumberTheory/MertensBlock.lean`), whose constant is
`20/log 2 = 28.85`; downstream the constant sits inside an exponential.

## The constant

Exactly, `∑_{y<p≤z} 1/p = (log log z − log log y) + (E₂p(z) − E₂p(y))`, and `log z ≤ Λ·log y` is
exactly `log log z − log log y ≤ log Λ`.  So the constant needed is a bound on
`E₂p(z) − E₂p(y)` for `2 ≤ y ≤ z`.  `MertensBlock.lean` bounds each error term by
`(log 4 + 6 + E₁)/log x ≤ 10/log x` and evaluates at `x = 2`, which is where its `28.85` comes
from — but that bound only says anything when `log x` is large, and it is being applied at the one
place where it says nothing.

The true supremum of `E₂p(z) − E₂p(y)` is `≈ 0.605`, attained at `y = z = 2`.  Here it is bounded
by `1.86` with a three-way split, each region using the tool that is sharp there.

* **`log y ≥ 9.75`.**  Both endpoints are large, `PrimeNumberTheoremAnd`'s `Mertens.E₂p.abs_le`
  gives `≤ 2·9.003/9.75 = 1.847`, and the constant `M` cancels.
* **`log y < 9.75` and `log z ≥ 8.6`.**  The upper endpoint is large (`E₂p(z) ≤ 9.003/8.6`), the
  lower one is handled by `RMF.log_log_sub_sum_prime_le`: a three-step staircase
  `∑_{p≤y} 1/p ≥ 1/2, 1.267, 1.756` for `y ≥ 2, 11, 73`, against `log log y < log 9.75`.  With
  `M ≤ 0.2641` (`RMF.mertens_const_le`) this is `≤ 1.846`.
* **`log z < 8.6`.**  No Mertens error is usable at either end, and none is needed: every prime in
  `(y, z]` is odd, so `∑_{y<p≤z} 1/p ≤ ½∫_y^{z+1} dt/t` (`RMF.sum_prime_Ioc_inv_le_half_log`),
  and `½(log z − log y) − log log z + log log y` is maximised over `2 ≤ y ≤ z ≤ e^{8.6}` at
  `log y = 2`, giving `≤ 1.852`.

The three thresholds are balanced: all three cases land within `0.006` of each other.
-/

namespace RMF

open Finset

/-! ### Numeric preliminaries -/

/-- `log w ≤ n·log 2 + w/2ⁿ − 1`: the tangent-line bound `log t ≤ t − 1`, rescaled by `2ⁿ`.  It is
sharp when `2ⁿ` is near `w`; at `n = 2`, the instance used below, it is what turns
`log log y ≤ …` into a *linear* statement about `log y`. -/
lemma log_le_mul_log_two_add_div (n : ℕ) {w : ℝ} (hw : 0 < w) :
    Real.log w ≤ n * Real.log 2 + w / 2 ^ n - 1 := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hw h2)
  rw [Real.log_div hw.ne' h2.ne', Real.log_pow] at h
  linarith

/-- `t/2 − log t` is monotone on `[2, ∞)`. -/
lemma half_sub_log_le_half_sub_log {v V : ℝ} (hv : 2 ≤ v) (hvV : v ≤ V) :
    v / 2 - Real.log v ≤ V / 2 - Real.log V := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hV0 : (0 : ℝ) < V := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hV0 hv0)
  rw [Real.log_div hV0.ne' hv0.ne'] at h
  have he : V / v - 1 = (V - v) / v := by field_simp
  have hd : (V - v) / v ≤ (V - v) / 2 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hv
  rw [he] at h
  linarith

/-- `log 8 = 3 log 2`. -/
lemma log_eight : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
  push_cast
  ring

/-- `log 8.6 ≥ 2.1492`, from `log 8.6 = 3 log 2 + log 1.075` and `log t ≥ 1 − 1/t`. -/
lemma log_eight_point_six_gt : (2.1492 : ℝ) ≤ Real.log 8.6 := by
  have h1 : Real.log (8.6 : ℝ) = Real.log 8 + Real.log 1.075 := by
    rw [show (8.6 : ℝ) = 8 * 1.075 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have h4 : (1 : ℝ) - (1.075 : ℝ)⁻¹ ≤ Real.log 1.075 :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h5 : (1 : ℝ) - (1.075 : ℝ)⁻¹ = 3 / 43 := by norm_num
  rw [h1, log_eight]
  linarith [Real.log_two_gt_d9]

/-- `log 64 = 6 log 2`. -/
lemma log_sixty_four : Real.log 64 = 6 * Real.log 2 := by
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
  push_cast
  ring

/-- `log 9.75 ≤ 2.2826416`, from `log 9.75 = 3 log 2 + log(39/32)` and `39/32 ≤ 1.0508⁴`. -/
lemma log_nine_point_seven_five_lt : Real.log 9.75 ≤ 2.2826416 := by
  have h1 : Real.log ((8 : ℝ) * (39 / 32)) = Real.log 8 + Real.log (39 / 32) :=
    Real.log_mul (by norm_num) (by norm_num)
  rw [show (8 : ℝ) * (39 / 32) = 9.75 by norm_num] at h1
  have h2 : Real.log (39 / 32 : ℝ) ≤ Real.log ((1.0508 : ℝ) ^ (4 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h2
  push_cast at h2
  have h3 : Real.log (1.0508 : ℝ) ≤ 1.0508 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [h1, log_eight]
  linarith [Real.log_two_lt_d9]

/-- `log 72 = 3 log 2 + 2 log 3`. -/
lemma log_seventy_two : Real.log 72 = 3 * Real.log 2 + 2 * Real.log 3 := by
  have h1 : Real.log (72 : ℝ) = Real.log 8 + Real.log 9 := by
    rw [show (72 : ℝ) = 8 * 9 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have h2 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h1, log_eight, h2]

/-- **The two-sided step bound.**  For `t ≥ 2`, `2/t ≤ log(t+1) − log(t−1)`, i.e.
`∫_{t−1}^{t+1} ds/s ≥ 2/t`; proved as `exp(2/t) ≤ (t+1)/(t−1)`, which `Real.exp_bound` at order `3`
closes.  It gives the odd-prime sum bound below its factor `1/2`, without which the small-`z`
regime could not be discharged. -/
lemma two_div_le_log_add_one_sub_log_sub_one {t : ℝ} (ht : 2 ≤ t) :
    2 / t ≤ Real.log (t + 1) - Real.log (t - 1) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  have ht2 : (0 : ℝ) < t + 1 := by linarith
  have hx0 : (0 : ℝ) < 2 / t := by positivity
  have habs : |2 / t| ≤ 1 := by
    rw [abs_of_pos hx0, div_le_one ht0]
    linarith
  have hb := Real.exp_bound habs (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (2 / t) ^ m / (Nat.factorial m)
      = 1 + 2 / t + (2 / t) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum, abs_of_pos hx0] at hb
  have hb' : Real.exp (2 / t) - (1 + 2 / t + (2 / t) ^ 2 / 2) ≤ (2 / t) ^ 3 * (2 / 9) := by
    refine (abs_le.1 hb).2.trans (le_of_eq ?_)
    norm_num [Nat.factorial]
  have hkey : 1 + 2 / t + (2 / t) ^ 2 / 2 + (2 / t) ^ 3 * (2 / 9) ≤ (t + 1) / (t - 1) := by
    rw [← sub_nonneg]
    have heq : (t + 1) / (t - 1) - (1 + 2 / t + (2 / t) ^ 2 / 2 + (2 / t) ^ 3 * (2 / 9))
        = (2 * t + 16) / (9 * t ^ 3 * (t - 1)) := by
      field_simp
      ring
    rw [heq]
    exact div_nonneg (by linarith) (mul_nonneg (by positivity) (by linarith))
  have hexp : Real.exp (2 / t) ≤ (t + 1) / (t - 1) := by linarith
  have h := (Real.le_log_iff_exp_le (div_pos ht2 ht1)).2 hexp
  rwa [Real.log_div ht2.ne' ht1.ne'] at h

/-! ### The odd-prime sum bound

Every prime in `(y, z]` with `y ≥ 2` is odd, so the intervals `[p−1, p+1]` are pairwise disjoint
and sit inside `[y, z+1]`.  Summing `1/p ≤ ½(log(p+1) − log(p−1))` gives `½ log((z+1)/y)`. -/

/-- The induction carrying the odd-prime sum bound.  The right endpoint is stated as
`2⌊(z+1)/2⌋` — the largest even number `≤ z+1` — because that is the quantity which stays put
exactly when no new prime can enter, namely when `z` steps to an even value. -/
lemma sum_prime_Ioc_inv_le_half_log_aux {y : ℕ} (hy : 2 ≤ y) (z : ℕ) (hz : y ≤ z) :
    (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p)
      ≤ (Real.log ((2 * ((z + 1) / 2) : ℕ) : ℝ) - Real.log (y : ℝ)) / 2 := by
  induction z, hz using Nat.le_induction with
  | base =>
    have hy0 : (0 : ℝ) < (y : ℝ) := by
      have h : 0 < y := by omega
      exact_mod_cast h
    have h1 : (y : ℝ) ≤ ((2 * ((y + 1) / 2) : ℕ) : ℝ) := by
      have h : y ≤ 2 * ((y + 1) / 2) := by omega
      exact_mod_cast h
    have h2 := Real.log_le_log hy0 h1
    simp only [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty]
    linarith
  | succ z hz ih =>
    have hz2 : 2 ≤ z := le_trans hy hz
    have hsplit : (∑ p ∈ Finset.Ioc y (z + 1) with Nat.Prime p, (1 : ℝ) / p)
        = (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p)
          + (if Nat.Prime (z + 1) then (1 : ℝ) / ((z : ℝ) + 1) else 0) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_Ioc_succ_top hz]
      push_cast
      ring
    by_cases hp : Nat.Prime (z + 1)
    · have hze : z % 2 = 0 := by
        by_contra hcon
        have hev : Even (z + 1) := by
          rw [Nat.even_iff]
          omega
        have h := (Nat.Prime.even_iff hp).1 hev
        omega
      have hL : ((2 * ((z + 1) / 2) : ℕ) : ℝ) = (z : ℝ) := by
        have h : 2 * ((z + 1) / 2) = z := by omega
        rw [h]
      have hR : ((2 * ((z + 1 + 1) / 2) : ℕ) : ℝ) = (z : ℝ) + 2 := by
        have h : 2 * ((z + 1 + 1) / 2) = z + 2 := by omega
        rw [h]
        push_cast
        ring
      have hzR : (2 : ℝ) ≤ (z : ℝ) + 1 := by
        have h : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
        linarith
      have hkey := two_div_le_log_add_one_sub_log_sub_one hzR
      rw [show (z : ℝ) + 1 + 1 = (z : ℝ) + 2 by ring,
        show (z : ℝ) + 1 - 1 = (z : ℝ) by ring] at hkey
      rw [hL] at ih
      rw [hsplit, if_pos hp, hR]
      have hhalf : (1 : ℝ) / ((z : ℝ) + 1) = 2 / ((z : ℝ) + 1) / 2 := by
        field_simp
      rw [hhalf]
      linarith
    · rw [hsplit, if_neg hp, add_zero]
      refine ih.trans ?_
      have h1 : ((2 * ((z + 1) / 2) : ℕ) : ℝ) ≤ ((2 * ((z + 1 + 1) / 2) : ℕ) : ℝ) := by
        have h : 2 * ((z + 1) / 2) ≤ 2 * ((z + 1 + 1) / 2) := by omega
        exact_mod_cast h
      have h2 : (0 : ℝ) < ((2 * ((z + 1) / 2) : ℕ) : ℝ) := by
        have h : 0 < 2 * ((z + 1) / 2) := by omega
        exact_mod_cast h
      have h3 := Real.log_le_log h2 h1
      linarith

/-- **The odd-prime sum bound.**  For `2 ≤ y ≤ z`,
`∑_{y < p ≤ z} 1/p ≤ ½(log(z+1) − log y)`.

No Mertens input at all — only that primes above `2` are odd.  This is the estimate that covers
the range where the Mertens error term is useless, `z ≤ e^{8.6} ≈ 5432`. -/
lemma sum_prime_Ioc_inv_le_half_log {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z) :
    (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p)
      ≤ (Real.log ((z : ℝ) + 1) - Real.log (y : ℝ)) / 2 := by
  refine (sum_prime_Ioc_inv_le_half_log_aux hy z hyz).trans ?_
  have h1 : ((2 * ((z + 1) / 2) : ℕ) : ℝ) ≤ (z : ℝ) + 1 := by
    have h : 2 * ((z + 1) / 2) ≤ z + 1 := by omega
    calc ((2 * ((z + 1) / 2) : ℕ) : ℝ) ≤ ((z + 1 : ℕ) : ℝ) := by exact_mod_cast h
      _ = (z : ℝ) + 1 := by push_cast; ring
  have h2 : (0 : ℝ) < ((2 * ((z + 1) / 2) : ℕ) : ℝ) := by
    have h : 0 < 2 * ((z + 1) / 2) := by omega
    exact_mod_cast h
  have h3 := Real.log_le_log h2 h1
  linarith

/-! ### The staircase lower bound on `∑_{p ≤ y} 1/p` -/

/-- Any finite set of primes `≤ y` gives a lower bound for `∑_{p ≤ y} 1/p`. -/
lemma sum_le_sum_prime_Ioc_zero {y : ℕ} (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p ∧ p ≤ y) :
    ∑ p ∈ s, (1 : ℝ) / p ≤ ∑ p ∈ Finset.Ioc 0 y with Nat.Prime p, (1 : ℝ) / p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity
  intro p hp
  obtain ⟨h1, h2⟩ := hs p hp
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨h1.pos, h2⟩, h1⟩

/-- `∑_{p ≤ y} 1/p ≥ 1/2` for `y ≥ 2`. -/
lemma half_le_sum_prime_Ioc_zero {y : ℕ} (hy : 2 ≤ y) :
    (1 : ℝ) / 2 ≤ ∑ p ∈ Finset.Ioc 0 y with Nat.Prime p, (1 : ℝ) / p := by
  refine le_trans (le_of_eq ?_) (sum_le_sum_prime_Ioc_zero ({2} : Finset ℕ) ?_)
  · rw [Finset.sum_singleton]
    norm_num
  · intro p hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, hy⟩

/-- `∑_{p ≤ y} 1/p ≥ 1.267` for `y ≥ 11`. -/
lemma sum_prime_Ioc_zero_ge_eleven {y : ℕ} (hy : 11 ≤ y) :
    (1.267 : ℝ) ≤ ∑ p ∈ Finset.Ioc 0 y with Nat.Prime p, (1 : ℝ) / p := by
  refine le_trans ?_ (sum_le_sum_prime_Ioc_zero ({2, 3, 5, 7, 11} : Finset ℕ) ?_)
  · repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    norm_num
  · intro p hp
    fin_cases hp <;> exact ⟨by norm_num, by omega⟩

/-- `∑_{p ≤ y} 1/p ≥ 1.756` for `y ≥ 73`. -/
lemma sum_prime_Ioc_zero_ge_seventy_three {y : ℕ} (hy : 73 ≤ y) :
    (1.756 : ℝ) ≤ ∑ p ∈ Finset.Ioc 0 y with Nat.Prime p, (1 : ℝ) / p := by
  refine le_trans ?_ (sum_le_sum_prime_Ioc_zero
    ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73} :
      Finset ℕ) ?_)
  · repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    norm_num
  · intro p hp
    fin_cases hp <;> exact ⟨by norm_num, by omega⟩

/-- **The staircase.**  For `2 ≤ y` with `log y ≤ 9.75`, `log log y − ∑_{p ≤ y} 1/p ≤ 0.535`.
Three steps suffice: `1/2` against `log log 10`, `1.267` against `log log 72`, and `1.756` against
`log 9.75`.  The last is the binding one and fixes the `9.75` threshold: the worst case is `y` just
below `e^{9.75}`, where the prime harmonic sum lags `log log y` most.  Past that threshold the
Mertens error term takes over. -/
lemma log_log_sub_sum_prime_le {y : ℕ} (hy : 2 ≤ y) (hy' : Real.log (y : ℝ) ≤ 9.75) :
    Real.log (Real.log (y : ℝ)) - (∑ p ∈ Finset.Ioc 0 y with Nat.Prime p, (1 : ℝ) / p)
      ≤ 0.535 := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hly : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  rcases le_or_gt y 10 with h10 | h10
  · have hyR : (y : ℝ) ≤ 10 := by exact_mod_cast h10
    have hlog10 : Real.log (y : ℝ) ≤ 2.3025851 := by
      have h := Real.log_le_log (by linarith : (0 : ℝ) < (y : ℝ)) hyR
      have he : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := Real.log_ten_eq
      linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    have h4 := log_le_mul_log_two_add_div 2 hly
    have hS := half_le_sum_prime_Ioc_zero hy
    push_cast at h4
    norm_num at h4
    linarith [Real.log_two_lt_d9]
  · rcases le_or_gt y 72 with h72 | h72
    · have hyR : (y : ℝ) ≤ 72 := by exact_mod_cast h72
      have hlog72 : Real.log (y : ℝ) ≤ 4.2766662 := by
        have h := Real.log_le_log (by linarith : (0 : ℝ) < (y : ℝ)) hyR
        linarith [log_seventy_two, Real.log_two_lt_d9, Real.log_three_lt_d9]
      have h4 := log_le_mul_log_two_add_div 2 hly
      have hS := sum_prime_Ioc_zero_ge_eleven h10
      push_cast at h4
      norm_num at h4
      linarith [Real.log_two_lt_d9]
    · have h4 : Real.log (Real.log (y : ℝ)) ≤ Real.log 9.75 := Real.log_le_log hly hy'
      have hS := sum_prime_Ioc_zero_ge_seventy_three h72
      linarith [log_nine_point_seven_five_lt]

/-! ### The block bound -/

/-- **Mertens over a block, uniformly in the scale.**  For `2 ≤ y ≤ z` and `1 ≤ Λ` with
`log z ≤ Λ·log y`, `∑_{y < p ≤ z} 1/p ≤ log Λ + 1.86`.  Binder order and index set are those of
`RMF.sum_prime_Ioc_inv_le_of_log_le` (constant `20/log 2 = 28.85`), so this is a drop-in
replacement.  There is no largeness hypothesis: `y = 2` is allowed, which the `q`-uniform
theorem's scales reach. -/
theorem sum_prime_Ioc_inv_le_of_log_le' {y z : ℕ} {Λ : ℝ} (hy : 2 ≤ y) (hyz : y ≤ z)
    (hΛ : 1 ≤ Λ) (hlog : Real.log z ≤ Λ * Real.log y) :
    (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p) ≤ Real.log Λ + 1.86 := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := le_trans hy2 hyzR
  have hly : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlyz : Real.log (y : ℝ) ≤ Real.log (z : ℝ) := Real.log_le_log (by linarith) hyzR
  have hlz : (0 : ℝ) < Real.log (z : ℝ) := lt_of_lt_of_le hly hlyz
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hmain : Real.log (Real.log (z : ℝ)) ≤ Real.log Λ + Real.log (Real.log (y : ℝ)) := by
    have h := Real.log_le_log hlz hlog
    rwa [Real.log_mul (ne_of_gt hΛ0) (ne_of_gt hly)] at h
  have hsum : (∑ p ∈ Finset.Ioc 0 y with Nat.Prime p, (1 : ℝ) / p)
      + (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p)
      = ∑ p ∈ Finset.Ioc 0 z with Nat.Prime p, (1 : ℝ) / p := by
    simp only [Finset.sum_filter]
    exact Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hyz
  have hkey : (∑ p ∈ Finset.Ioc y z with Nat.Prime p, (1 : ℝ) / p)
      - (Real.log (Real.log (z : ℝ)) - Real.log (Real.log (y : ℝ))) ≤ 1.86 := by
    rcases le_or_gt (8.6 : ℝ) (Real.log (z : ℝ)) with hbig | hsmall
    · have hzE := Mertens.sum_prime_div_eq (z : ℝ)
      rw [Nat.floor_natCast, ← hsum] at hzE
      have hEz : Mertens.E₂p (z : ℝ) ≤ 9.003 / Real.log (z : ℝ) := by
        have hd : (0 : ℝ) ≤ (9.003 - (Real.log 4 + 6 + Mertens.E₁)) / Real.log (z : ℝ) :=
          div_nonneg (by linarith [mertens_error_const_le]) hlz.le
        rw [sub_div] at hd
        linarith [le_abs_self (Mertens.E₂p (z : ℝ)), Mertens.E₂p.abs_le hz2]
      rcases le_or_gt (9.75 : ℝ) (Real.log (y : ℝ)) with hbigy | hsmally
      · -- both endpoints large: the constant `M` cancels
        have hyE := Mertens.sum_prime_div_eq (y : ℝ)
        rw [Nat.floor_natCast] at hyE
        have hEy : -Mertens.E₂p (y : ℝ) ≤ 9.003 / Real.log (y : ℝ) := by
          have hd : (0 : ℝ) ≤ (9.003 - (Real.log 4 + 6 + Mertens.E₁)) / Real.log (y : ℝ) :=
            div_nonneg (by linarith [mertens_error_const_le]) hly.le
          rw [sub_div] at hd
          linarith [(abs_le.1 (Mertens.E₂p.abs_le hy2)).1]
        have h1 : (9.003 : ℝ) / Real.log (z : ℝ) ≤ 9.003 / 9.75 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_trans hbigy hlyz)
        have h2 : (9.003 : ℝ) / Real.log (y : ℝ) ≤ 9.003 / 9.75 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hbigy
        rw [hyE] at hzE
        linarith
      · -- upper endpoint large, lower endpoint on the staircase
        have hbeta := log_log_sub_sum_prime_le hy (le_of_lt hsmally)
        have h1 : (9.003 : ℝ) / Real.log (z : ℝ) ≤ 9.003 / 8.6 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hbig
        have hM := mertens_const_le
        linarith
    · -- no Mertens error is usable at either end
      have hhalf := sum_prime_Ioc_inv_le_half_log hy hyz
      have hll : Real.log (Real.log (y : ℝ)) ≤ Real.log (Real.log (z : ℝ)) :=
        Real.log_le_log hly hlyz
      rcases le_or_gt z 63 with hz63 | hz63
      · have hzR : (z : ℝ) + 1 ≤ 64 := by
          have h := (Nat.cast_le (α := ℝ)).2 hz63
          push_cast at h
          linarith
        have h1 : Real.log ((z : ℝ) + 1) ≤ Real.log 64 :=
          Real.log_le_log (by linarith) hzR
        have h2 : Real.log 2 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) hy2
        linarith [log_sixty_four, Real.log_two_lt_d9, Real.log_two_gt_d9]
      · have hz64 : (64 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz63
        have hv2 : (2 : ℝ) ≤ Real.log (z : ℝ) := by
          have h8 : Real.log 8 ≤ Real.log (z : ℝ) := Real.log_le_log (by norm_num) (by linarith)
          rw [log_eight] at h8
          linarith [Real.log_two_gt_d9]
        have hstep : Real.log ((z : ℝ) + 1) ≤ Real.log (z : ℝ) + 1 / 64 := by
          have h := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < ((z : ℝ) + 1) / (z : ℝ) by positivity)
          rw [Real.log_div (by linarith) (by linarith)] at h
          have he : ((z : ℝ) + 1) / (z : ℝ) - 1 = 1 / (z : ℝ) := by
            field_simp
            ring
          have hd : (1 : ℝ) / (z : ℝ) ≤ 1 / 64 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz64
          linarith
        have hmono := half_sub_log_le_half_sub_log (v := Real.log (z : ℝ)) (V := 8.6) hv2
          (le_of_lt hsmall)
        have hu : Real.log (Real.log (y : ℝ)) - Real.log (y : ℝ) / 2 ≤ Real.log 2 - 1 := by
          have h := Real.log_le_sub_one_of_pos
            (show (0 : ℝ) < Real.log (y : ℝ) / 2 by positivity)
          rw [Real.log_div (ne_of_gt hly) (by norm_num)] at h
          linarith
        linarith [log_eight_point_six_gt, Real.log_two_lt_d9]
  linarith

end RMF
