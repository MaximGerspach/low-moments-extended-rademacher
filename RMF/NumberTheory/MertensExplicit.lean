/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Tactic.NormNum.Prime
import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
# An explicit upper bound for the prime harmonic sum

`RMF.sum_primesBelow_inv_le`: for every natural `y ≥ 2`,

`∑_{p < y} 1/p ≤ log log y + 0.2641 + 9.003 / log y`,

with all three constants literal.  This is the version of Mertens' second theorem the explicit
Euler-product chain needs; `RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`
(`RMF/NumberTheory/CosinePrimeSum.lean`) is the two-sided form with an unspecified constant.

## The argument

`PrimeNumberTheoremAnd` supplies

* `Mertens.sum_prime_div_eq`: `∑_{p ≤ x} 1/p = log log x + M + E₂p x`;
* `Mertens.E₂p.abs_le`: `|E₂p x| ≤ (log 4 + 6 + E₁)/log x` for `x ≥ 2`;
* `Mertens.E₁.le`: `E₁ ≤ (5 log 2 + 3)/4`, whence `log 4 + 6 + E₁ ≤ 9.003`;
* `Mertens.M.eq`: `M = γ + ∑_p (log (1 - 1/p) + 1/p)`.

`Mertens.M.le` bounds `M` by `(log 4 + 4)/log 2 + 1 - log log 2 ≈ 9.137`, which is far too lossy
here: every unit of the additive constant costs a factor `e` downstream.  Instead we read the
constant off `Mertens.M.eq`.  Each summand there is `≤ 0` because `log (1 - u) ≤ -u`, so
`M ≤ γ`, and more generally `M` is bounded by `γ` plus any partial sum
(`RMF.mertens_const_le_add_sum`).  Summing the primes below `48` and using
`γ < harmonic 1024 - log 1024` gives `M ≤ 0.2641` (`RMF.mertens_const_le`); the true value is
`M ≈ 0.26149`, so little is left on the table.
-/

namespace RMF

open Real Finset

/-! ### The error constant, made literal -/

/-- **The error constant of `PrimeNumberTheoremAnd`'s quantitative Mertens is at most `9.0028`.**
`Mertens.E₂p.abs_le` bounds `|E₂p x|` by `(log 4 + 6 + E₁)/log x`, and `Mertens.E₁.le` bounds `E₁`
by `(5 log 2 + 3)/4`, so the numerator is `3.25 log 2 + 6.75 ≤ 9.0028` (true value `≈ 8.14`,
`E₁ ≈ 0.7553`).  The literal companion of `RMF.mertens_error_const_nonneg`
(`RMF/NumberTheory/MertensBlock.lean`, which imports this file through `CosinePrimeSum.lean`). -/
lemma mertens_error_const_le : Real.log 4 + 6 + Mertens.E₁ ≤ 9.0028 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith [Mertens.E₁.le, Real.log_two_lt_d9]

/-! ### The Meissel-Mertens constant is at most `γ` -/

/-- The summand of the series `M - γ = ∑_p (log (1 - 1/p) + 1/p)` of
`PrimeNumberTheoremAnd.Mertens.M.eq`, evaluated at a prime. -/
lemma mertens_summand_eq {n : ℕ} (hn : n.Prime) :
    Mertens.M_eq_summand n = Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) := if_pos hn

/-- Every summand of that series is nonpositive, since `log (1 - u) ≤ -u`. -/
lemma mertens_summand_nonpos (n : ℕ) : Mertens.M_eq_summand n ≤ 0 := by
  unfold Mertens.M_eq_summand
  split_ifs with hn
  · have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
    have hinv : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    have hpos : (0 : ℝ) < 1 - 1 / (n : ℝ) := by linarith
    linarith [Real.log_le_sub_one_of_pos hpos]
  · exact le_rfl

/-- The series of `Mertens.M.eq` has nonpositive terms, so any partial sum over a finite index
set is already an upper bound for it: `M ≤ γ + ∑_{n ∈ s} (log (1 - 1/n) + 1/n)`. -/
lemma mertens_const_le_add_sum (s : Finset ℕ) :
    Mertens.M ≤ Real.eulerMascheroniConstant + ∑ n ∈ s, Mertens.M_eq_summand n := by
  have hneg : Summable fun n ↦ -Mertens.M_eq_summand n := Mertens.M_eq_summable.neg
  have h := hneg.sum_le_tsum s fun i _ ↦ neg_nonneg.mpr (mertens_summand_nonpos i)
  rw [tsum_neg, Mertens.tsum_M_eq_summand_eq, Mertens.γ.eq_eulerMascheroni,
    sum_neg_distrib] at h
  linarith

/-! ### Numerical evaluation -/

/-- `γ < 0.5777039`.  Mathlib's `Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'` gives
`γ < harmonic n - log n` for every `n`; taking `n = 1024 = 2 ^ 10` turns `log n` into
`10 log 2`, which `Real.log_two_gt_d9` bounds below.  (Mathlib's own
`Real.eulerMascheroniConstant_lt_two_thirds` is this argument at `n = 6`, and `2/3` would cost
another `0.089` in the final constant.  The true value is `γ ≈ 0.5772157`.) -/
lemma eulerMascheroni_lt : Real.eulerMascheroniConstant < 0.5777039 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  have hs : Real.eulerMascheroniSeq' 1024 = (harmonic 1024 : ℝ) - Real.log 1024 := by
    rw [Real.eulerMascheroniSeq', if_neg (by norm_num : (1024 : ℕ) ≠ 0), Nat.cast_ofNat]
  have hh : (harmonic 1024 : ℝ) < 7.5091757 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [hs, hlog] at h
  linarith [Real.log_two_gt_d9]

/-- The four-term Taylor bound `log (1 - x) + x ≤ -(x²/2 + x³/3 + x⁴/4) + x⁵/(1-x)`,
for `0 < x ≤ 1/2`. -/
lemma log_one_sub_add_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    Real.log (1 - x) + x ≤ -(x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4) + x ^ 5 / (1 - x) := by
  have habs : |x| = x := abs_of_pos hx0
  have hlt : |x| < 1 := by rw [habs]; linarith
  have key := Real.abs_log_sub_add_sum_range_le hlt 4
  rw [habs] at key
  have hup := (abs_le.mp key).2
  norm_num [Finset.sum_range_succ] at hup
  linarith

/-- The `p`-th summand of `M - γ` is at most
`-(1/(2p²) + 1/(3p³) + 1/(4p⁴)) + 1/(p⁴(p-1))`. -/
lemma mertens_summand_le {n : ℕ} (hn : n.Prime) :
    Mertens.M_eq_summand n
      ≤ -(1 / (2 * (n : ℝ) ^ 2) + 1 / (3 * (n : ℝ) ^ 3) + 1 / (4 * (n : ℝ) ^ 4))
        + 1 / ((n : ℝ) ^ 4 * ((n : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.two_le
  have hx0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  have hne : (n : ℝ) ≠ 0 := by positivity
  have hne1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [mertens_summand_eq hn]
  refine (log_one_sub_add_le hx0 hx1).trans (le_of_eq ?_)
  field_simp

/-- `RMF.mertens_summand_le` packaged so that a single `norm_num` discharges the arithmetic at
a fixed prime. -/
lemma mertens_summand_le' (p : ℕ) (hp : p.Prime) (c : ℝ)
    (hc : -(1 / (2 * (p : ℝ) ^ 2) + 1 / (3 * (p : ℝ) ^ 3) + 1 / (4 * (p : ℝ) ^ 4))
      + 1 / ((p : ℝ) ^ 4 * ((p : ℝ) - 1)) ≤ c) :
    Mertens.M_eq_summand p ≤ c :=
  (mertens_summand_le hp).trans hc

/-- The partial sum of `M - γ = ∑_p (log (1 - 1/p) + 1/p)` over the primes below `48`.
The three leading terms are evaluated exactly and bounded with Mathlib's decimal bounds for
`log 2, log 3, log 5`; the remaining twelve use the four-term Taylor bound `RMF.mertens_summand_le`.
The true value of the partial sum is `-0.31377`. -/
lemma sum_mertens_summand_le :
    ∑ n ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ),
      Mertens.M_eq_summand n ≤ -0.31366 := by
  have e2 : Mertens.M_eq_summand 2 = 1 / 2 - Real.log 2 := by
    rw [mertens_summand_eq Nat.prime_two,
      show (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have e3 : Mertens.M_eq_summand 3 = 1 / 3 + Real.log 2 - Real.log 3 := by
    rw [mertens_summand_eq (by norm_num),
      show (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = (2 : ℝ) / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
    norm_num
    ring
  have e5 : Mertens.M_eq_summand 5 = 1 / 5 + 2 * Real.log 2 - Real.log 5 := by
    rw [mertens_summand_eq (by norm_num),
      show (1 : ℝ) - 1 / ((5 : ℕ) : ℝ) = (2 : ℝ) ^ 2 / 5 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  have h7 : Mertens.M_eq_summand 7 ≤ -0.0112106 :=
    mertens_summand_le' 7 (by norm_num) _ (by norm_num)
  have h11 : Mertens.M_eq_summand 11 ≤ -0.00439291 :=
    mertens_summand_le' 11 (by norm_num) _ (by norm_num)
  have h13 : Mertens.M_eq_summand 13 ≤ -0.00311613 :=
    mertens_summand_le' 13 (by norm_num) _ (by norm_num)
  have h17 : Mertens.M_eq_summand 17 ≤ -0.00180019 :=
    mertens_summand_le' 17 (by norm_num) _ (by norm_num)
  have h19 : Mertens.M_eq_summand 19 ≤ -0.00143513 :=
    mertens_summand_le' 19 (by norm_num) _ (by norm_num)
  have h23 : Mertens.M_eq_summand 23 ≤ -0.0009733 :=
    mertens_summand_le' 23 (by norm_num) _ (by norm_num)
  have h29 : Mertens.M_eq_summand 29 ≤ -0.0006085 :=
    mertens_summand_le' 29 (by norm_num) _ (by norm_num)
  have h31 : Mertens.M_eq_summand 31 ≤ -0.00053171 :=
    mertens_summand_le' 31 (by norm_num) _ (by norm_num)
  have h37 : Mertens.M_eq_summand 37 ≤ -0.00037192 :=
    mertens_summand_le' 37 (by norm_num) _ (by norm_num)
  have h41 : Mertens.M_eq_summand 41 ≤ -0.00030235 :=
    mertens_summand_le' 41 (by norm_num) _ (by norm_num)
  have h43 : Mertens.M_eq_summand 43 ≤ -0.00027467 :=
    mertens_summand_le' 43 (by norm_num) _ (by norm_num)
  have h47 : Mertens.M_eq_summand 47 ≤ -0.0002296 :=
    mertens_summand_le' 47 (by norm_num) _ (by norm_num)
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

/-- **A literal upper bound for the Meissel-Mertens constant** `Mertens.M` (the additive
constant of Mertens' second theorem; not to be confused with `RMF.mertens_error_const_nonneg`, which
is about the *error* constant `log 4 + 6 + E₁`).  The true value is `M ≈ 0.26149`. -/
theorem mertens_const_le : Mertens.M ≤ 0.2641 := by
  have h := mertens_const_le_add_sum
    ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} : Finset ℕ)
  linarith [eulerMascheroni_lt, sum_mertens_summand_le]

/-! ### The prime harmonic sum -/

/-- **Mertens' second theorem with literal constants.**  For every natural `y ≥ 2`,
`∑_{p < y} 1/p ≤ log log y + 0.2641 + 9.003 / log y`.  The sum over `Nat.primesBelow y` is at most
the sum over `p ≤ y`, which `Mertens.sum_prime_div_eq` evaluates at `x = y` exactly, so the passage
costs nothing in the constants. -/
theorem sum_primesBelow_inv_le {y : ℕ} (hy : 2 ≤ y) :
    ∑ p ∈ Nat.primesBelow y, ((p : ℝ))⁻¹
      ≤ Real.log (Real.log y) + 0.2641 + 9.003 / Real.log y := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hsub : Nat.primesBelow y ⊆ {p ∈ Finset.Ioc 0 y | p.Prime} := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hp.2.pos, hp.1.le⟩, hp.2⟩
  have hstep : ∑ p ∈ Nat.primesBelow y, ((p : ℝ))⁻¹
      ≤ ∑ p ∈ {p ∈ Finset.Ioc 0 y | p.Prime}, ((p : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ by positivity
  have hkey : ∑ p ∈ {p ∈ Finset.Ioc 0 y | p.Prime}, ((p : ℝ))⁻¹
      = Real.log (Real.log y) + Mertens.M + Mertens.E₂p (y : ℝ) := by
    have h := Mertens.sum_prime_div_eq (y : ℝ)
    rw [Nat.floor_natCast] at h
    rw [← h]
    exact Finset.sum_congr rfl fun p _ ↦ (one_div _).symm
  have hnum : Real.log 4 + 6 + Mertens.E₁ ≤ 9.003 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Mertens.E₁.le, Real.log_two_lt_d9]
  have hE : Mertens.E₂p (y : ℝ) ≤ 9.003 / Real.log y :=
    calc Mertens.E₂p (y : ℝ) ≤ |Mertens.E₂p (y : ℝ)| := le_abs_self _
      _ ≤ (Real.log 4 + 6 + Mertens.E₁) / Real.log y := Mertens.E₂p.abs_le hy2
      _ ≤ 9.003 / Real.log y := by gcongr
  linarith [mertens_const_le]

end RMF
