/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensBlockUniform

/-!
# Mertens' second theorem, one-sided and threshold-free

`RMF.sum_primesBelow_inv_le_log_log_add`: for every natural `N ≥ 2`,

`∑_{p ≤ N} 1/p ≤ log log N + 1.42`,

with **no largeness hypothesis**: `N = 2` is allowed, and the constant is absolute.

## Why the one-sided form is worth proving separately

The two-sided `RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`
(`RMF/NumberTheory/CosinePrimeSum.lean`) has witness `|M| + (log 4 + 6 + E₁)/log 2 + 1 = 14.25` —
the Mertens error term evaluated at `N = 2`, where it says nothing.

## The proof

Write `L = log N`.  There are three regimes, split at `N = 100` and at `L = 7.9`.

* **`L ≥ 7.9`.**  `Mertens.sum_prime_div_eq` is exact:
  `∑_{p ≤ N} 1/p = log L + M + E₂p N`, and `M ≤ 0.2641` (`RMF.mertens_const_le`) together with
  `|E₂p N| ≤ 9.0028/L ≤ 9.0028/7.9` (`Mertens.E₂p.abs_le`, `RMF.mertens_error_const_le`) gives
  `≤ log L + 1.4037`.
* **`L < 7.9` and `N > 100`.**  No Mertens input at all.  The primes `≤ 100` are summed
  outright (`RMF.sum_prime_Ioc_hundred_le`: `≤ 1.80282`), and every prime in `(100, N]` is odd,
  so `RMF.sum_prime_Ioc_inv_le_half_log` gives `∑_{100 < p ≤ N} 1/p ≤ ½(log(N+1) − log 100)`.
  With `log(N+1) ≤ L + 1/N ≤ L + 1/100` the excess over `log L` is
  `1.80282 + 0.005 − ½log 100 + (L/2 − log L) ≤ −0.4948 + 1.904 = 1.4093`.
* **`L < 7.9` and `N ≤ 100`.**  The same, split at `2` instead of `100`:
  `½ + 1/(2N) − ½log 2 + (L/2 − log L) ≤ 0.4035 + 0.807 = 1.2105`, using `L ≤ log 100 < 4.6052`.

The `L/2 − log L` bounds come from `RMF.half_sub_log_le_of_Icc` on the intervals
`[log 2, 2], [2, 4], [4, 4.6052]` (low regime) and `[4.6, 6.4], [6.4, 7.9]` (middle regime).
The three regimes land at `1.4037`, `1.4093`, `1.2105`; `100` and `7.9` are where they balance.
The true supremum of `∑_{p ≤ N} 1/p − log log N` is `½ − log log 2 = 0.8665`, at `N = 2`.
-/

namespace RMF

open Finset

/-! ### A convexity substitute for `L/2 − log L`

`L/2 − log L` is convex, so on an interval it is largest at an endpoint; rather than import
convexity we use the secant-from-below `log L ≥ log a + (L − a)/b`, which is what
`Real.one_sub_inv_le_log_of_pos` gives once `1 − a/L ≥ (L − a)/b` for `L ≤ b`.  The resulting
bound `b/2 − log a − 1 + a/b` overshoots the true endpoint maximum `b/2 − log b` by
`log(b/a) − 1 + a/b`, which is `O((b−a)²)` — negligible on the intervals used below. -/

/-- On `[a, b]` with `0 < a` and `2 ≤ b`, `L/2 − log L ≤ b/2 − log a − 1 + a/b`.

The `−1 + a/b` is what makes this nearly lossless: without it (`log L ≥ log a` alone) the
interval `[6.4, 7.9]` would give `2.09` instead of `1.90`, and the argument would not close. -/
lemma half_sub_log_le_of_Icc {a b L : ℝ} (ha : 0 < a) (haL : a ≤ L) (hLb : L ≤ b) (hb : 2 ≤ b) :
    L / 2 - Real.log L ≤ b / 2 - Real.log a - 1 + a / b := by
  have hL : (0 : ℝ) < L := lt_of_lt_of_le ha haL
  have hb0 : (0 : ℝ) < b := by linarith
  have h1 : 1 - (L / a)⁻¹ ≤ Real.log L - Real.log a := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hL ha)
    rwa [Real.log_div hL.ne' ha.ne'] at h
  rw [inv_div] at h1
  have h3 : (L - a) / b ≤ (L - a) / L :=
    div_le_div_of_nonneg_left (by linarith) hL hLb
  have h4 : (L - a) / L = 1 - a / L := by field_simp
  have hsd : (L - a) / b = L / b - a / b := sub_div L a b
  have hid : b / 2 - 1 - (L / 2 - L / b) = (b - L) * (b - 2) / (2 * b) := by
    field_simp
  have hnn : (0 : ℝ) ≤ (b - L) * (b - 2) / (2 * b) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

/-! ### Numeric logarithms

Only `5`-smooth arguments, so that `Real.log_two_*_d9`, `Real.log_three_*_d9` and
`Real.log_five_*_d9` cover them in both directions. -/

/-- `log 4.5 = 2 log 3 − log 2`. -/
lemma log_four_point_five : Real.log 4.5 = 2 * Real.log 3 - Real.log 2 := by
  rw [show (4.5 : ℝ) = 3 ^ (2 : ℕ) / 2 by norm_num, Real.log_div (by positivity) (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- `log 6.4 = 5 log 2 − log 5`. -/
lemma log_six_point_four : Real.log 6.4 = 5 * Real.log 2 - Real.log 5 := by
  rw [show (6.4 : ℝ) = 2 ^ (5 : ℕ) / 5 by norm_num, Real.log_div (by positivity) (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- `log 100 = 2 log 2 + 2 log 5`. -/
lemma log_hundred : Real.log 100 = 2 * Real.log 2 + 2 * Real.log 5 := by
  rw [show (100 : ℝ) = 2 ^ (2 : ℕ) * 5 ^ (2 : ℕ) by norm_num,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `log log 2 ≥ −0.36933`, from `log 2 ≥ 0.6912 = 2⁴·3³/5⁴`.

Going through a `5`-smooth rational avoids `Real.one_sub_inv_le_log_of_pos`, which would only
give `1 − 1/log 2 ≥ −0.4427` here. -/
lemma neg_le_log_log_two : (-0.36933 : ℝ) ≤ Real.log (Real.log 2) := by
  have h1 : (0.6912 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2 : Real.log (0.6912 : ℝ) ≤ Real.log (Real.log 2) := Real.log_le_log (by norm_num) h1
  have h3 : Real.log (0.6912 : ℝ) = 4 * Real.log 2 + 3 * Real.log 3 - 4 * Real.log 5 := by
    rw [show (0.6912 : ℝ) = 2 ^ (4 : ℕ) * 3 ^ (3 : ℕ) / 5 ^ (4 : ℕ) by norm_num,
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_lt_d9]

/-! ### The two ranges of `L/2 − log L` -/

/-- `L/2 − log L ≤ 0.807` for `log 2 ≤ L ≤ 4.6052`, the range reached by `N ≤ 100`.

Three intervals: `[log 2, 2]` gives `0.7160`, `[2, 4]` gives `0.8069`, `[4, 4.6052]` gives
`0.7849`.  The true supremum is `f(log 2) = 0.7131`; the binding interval is the middle one,
where the secant bound is weakest. -/
lemma half_sub_log_le_of_le_log_hundred {L : ℝ} (hL : Real.log 2 ≤ L) (hL' : L ≤ 4.6052) :
    L / 2 - Real.log L ≤ 0.807 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt L 2 with h2 | h2
  · have h := half_sub_log_le_of_Icc hl2 hL h2 (le_refl 2)
    linarith [neg_le_log_log_two, Real.log_two_lt_d9]
  · rcases le_or_gt L 4 with h4 | h4
    · have h := half_sub_log_le_of_Icc (by norm_num : (0 : ℝ) < 2) h2.le h4 (by norm_num)
      norm_num at h
      linarith [Real.log_two_gt_d9]
    · have h := half_sub_log_le_of_Icc (by norm_num : (0 : ℝ) < 4) h4.le hL' (by norm_num)
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        push_cast
        ring
      norm_num at h
      linarith [Real.log_two_gt_d9]

/-- `L/2 − log L ≤ 1.904` for `4.6 ≤ L ≤ 7.9`: the range reached by `N > 100` below the
Mertens threshold.

Two intervals: `[4.6, 6.4]` — run from `a = 4.5`, whose logarithm is `5`-smooth — gives `1.3991`,
and `[6.4, 7.9]` gives `1.9039`.  The true supremum is `f(7.9) = 1.8831`. -/
lemma half_sub_log_le_of_log_hundred_le {L : ℝ} (hL : 4.6 ≤ L) (hL' : L ≤ 7.9) :
    L / 2 - Real.log L ≤ 1.904 := by
  rcases le_or_gt L 6.4 with h | h
  · have hb := half_sub_log_le_of_Icc (by norm_num : (0 : ℝ) < 4.5) (by linarith) h (by norm_num)
    rw [log_four_point_five] at hb
    norm_num at hb
    linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  · have hb := half_sub_log_le_of_Icc (by norm_num : (0 : ℝ) < 6.4) h.le hL' (by norm_num)
    rw [log_six_point_four] at hb
    norm_num at hb
    linarith [Real.log_two_gt_d9, Real.log_five_lt_d9]

/-! ### The primes below `100`, summed outright -/

/-- `∑_{p ≤ 100} 1/p ≤ 1.80282`.  The true value is `1.8028172`.

This is the whole reason the constant is `1.42` and not `1.65`: the odd-prime bound
`RMF.sum_prime_Ioc_inv_le_half_log` charges `½ log((z+1)/y)` for the range `(y, z]`, and on
`[2, 100]` that is `2.50` against a true `1.30`. -/
lemma sum_prime_Ioc_hundred_le :
    (∑ p ∈ Finset.Ioc 0 100 with Nat.Prime p, (1 : ℝ) / p) ≤ 1.80282 := by
  rw [show Finset.filter Nat.Prime (Finset.Ioc 0 100) =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
        89, 97} : Finset ℕ) by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  norm_num

/-! ### The bound -/

/-- **Mertens' second theorem, one-sided and uniform.**  For every natural `N ≥ 2`,

`∑_{p ≤ N} 1/p ≤ log log N + 1.42`.

There is no largeness hypothesis: `N = 2` is allowed, where the left side is `1/2` and the right
is `log log 2 + 1.42 = 1.05`. -/
theorem sum_prime_Ioc_inv_le_log_log_add {N : ℕ} (hN : 2 ≤ N) :
    (∑ p ∈ Finset.Ioc 0 N with Nat.Prime p, (1 : ℝ) / p) ≤ Real.log (Real.log N) + 1.42 := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlN : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
  rcases le_or_gt (7.9 : ℝ) (Real.log (N : ℝ)) with hbig | hsmall
  · -- The Mertens error term is usable: it is exact, and `9.0028/7.9 = 1.1396`.
    have hE := Mertens.sum_prime_div_eq (N : ℝ)
    rw [Nat.floor_natCast] at hE
    have hEz : Mertens.E₂p (N : ℝ) ≤ 9.0028 / Real.log (N : ℝ) := by
      have hd : (0 : ℝ) ≤ (9.0028 - (Real.log 4 + 6 + Mertens.E₁)) / Real.log (N : ℝ) :=
        div_nonneg (by linarith [mertens_error_const_le]) hlN.le
      rw [sub_div] at hd
      linarith [le_abs_self (Mertens.E₂p (N : ℝ)), Mertens.E₂p.abs_le hN2]
    have h1 : (9.0028 : ℝ) / Real.log (N : ℝ) ≤ 9.0028 / 7.9 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hbig
    rw [hE]
    linarith [mertens_const_le]
  · -- No Mertens input: the primes in `(y, N]` are odd, for `y = 100` or `y = 2`.
    have hstep : Real.log ((N : ℝ) + 1) ≤ Real.log (N : ℝ) + 1 / (N : ℝ) := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((N : ℝ) + 1) / (N : ℝ) by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at h
      have he : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by
        field_simp
        ring
      linarith
    rcases le_or_gt N 100 with hlowN | hbigN
    · -- `N ≤ 100`: split at `2`, and `L ≤ log 100 < 4.6052`.
      have hsplit : (∑ p ∈ Finset.Ioc 0 2 with Nat.Prime p, (1 : ℝ) / p)
          + (∑ p ∈ Finset.Ioc 2 N with Nat.Prime p, (1 : ℝ) / p)
          = ∑ p ∈ Finset.Ioc 0 N with Nat.Prime p, (1 : ℝ) / p := by
        simp only [Finset.sum_filter]
        exact Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hN
      have hbase : (∑ p ∈ Finset.Ioc 0 2 with Nat.Prime p, (1 : ℝ) / p) = 1 / 2 := by
        rw [show (Finset.Ioc 0 2 : Finset ℕ) = {1, 2} by decide]
        norm_num [Finset.sum_filter]
      have htail := sum_prime_Ioc_inv_le_half_log (le_refl 2) hN
      rw [show (((2 : ℕ) : ℝ)) = (2 : ℝ) by norm_num] at htail
      have hinv : (1 : ℝ) / (N : ℝ) ≤ 1 / 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN2
      have hNle : (N : ℝ) ≤ 100 := by exact_mod_cast hlowN
      have hLle : Real.log (N : ℝ) ≤ 4.6052 := by
        have h := Real.log_le_log (by linarith : (0 : ℝ) < (N : ℝ)) hNle
        rw [log_hundred] at h
        linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
      linarith [half_sub_log_le_of_le_log_hundred hl2 hLle, Real.log_two_gt_d9]
    · -- `100 < N`: split at `100`, and `L ≥ log 100 > 4.6`.
      have h100 : (100 : ℕ) ≤ N := hbigN.le
      have hsplit : (∑ p ∈ Finset.Ioc 0 100 with Nat.Prime p, (1 : ℝ) / p)
          + (∑ p ∈ Finset.Ioc 100 N with Nat.Prime p, (1 : ℝ) / p)
          = ∑ p ∈ Finset.Ioc 0 N with Nat.Prime p, (1 : ℝ) / p := by
        simp only [Finset.sum_filter]
        exact Finset.sum_Ioc_consecutive _ (Nat.zero_le _) h100
      have htail := sum_prime_Ioc_inv_le_half_log (by norm_num : 2 ≤ 100) h100
      rw [show (((100 : ℕ) : ℝ)) = (100 : ℝ) by norm_num] at htail
      have hNge : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h100
      have hinv : (1 : ℝ) / (N : ℝ) ≤ 1 / 100 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNge
      have hLge : (4.6 : ℝ) ≤ Real.log (N : ℝ) := by
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100) hNge
        rw [log_hundred] at h
        linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
      linarith [half_sub_log_le_of_log_hundred_le hLge hsmall.le, sum_prime_Ioc_hundred_le,
        log_hundred, Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- **Mertens' second theorem, one-sided and uniform**, indexed as in the Euler-product
development.  For every natural `N ≥ 2`, `∑_{p ∈ primesBelow (N+1)} 1/p ≤ log log N + 1.42`: the
upper half of `RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`
(`RMF/NumberTheory/CosinePrimeSum.lean`) with `14.25` replaced by `1.42`. -/
theorem sum_primesBelow_inv_le_log_log_add {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹ ≤ Real.log (Real.log N) + 1.42 := by
  have hset : Nat.primesBelow (N + 1) = {p ∈ Finset.Ioc 0 N | p.Prime} := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hlt, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
    · rintro ⟨⟨_, hle⟩, hp⟩
      exact ⟨by omega, hp⟩
  rw [hset]
  refine le_trans (le_of_eq ?_) (sum_prime_Ioc_inv_le_log_log_add hN)
  exact Finset.sum_congr rfl fun p _ ↦ (one_div _).symm

end RMF
