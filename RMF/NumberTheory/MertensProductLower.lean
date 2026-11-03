/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensProductSharp

/-!
# Mertens' third theorem at `e^γ`, from below

`RMF.log_prod_primesBelow_inv_le` is the upper half, `log ∏_{p ≤ N}(1 - 1/p)⁻¹ ≤ log log N + γ +
9.0028/log N`: it drops the tail `∑_{p > N}(log(1 - 1/p) + 1/p) ≤ 0` of the series for `M - γ`.
The lower half keeps that tail, which `PrimeNumberTheoremAnd`'s `Mertens.sum_M_eq_summand_le'`
bounds by `4/N`:
`log ∏_{p ≤ N}(1 - 1/p)⁻¹ ≥ log log N + γ - 9.0028/log N - 4/N`
(`RMF.log_prod_primesBelow_inv_ge`).
-/

namespace RMF

/-- **Mertens' third theorem, lower half at `γ`**: for every natural `N ≥ 2`,
`log ∏_{p ≤ N}(1 - 1/p)⁻¹ ≥ log log N + γ - 9.0028/log N - 4/N`. -/
theorem log_prod_primesBelow_inv_ge {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log N) + Real.eulerMascheroniConstant - 9.0028 / Real.log N - 4 / N
      ≤ Real.log (∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hne : ∀ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹ ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact inv_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 1 - ((p : ℝ))⁻¹))
  rw [Real.log_prod hne]
  -- each logarithm is `1/p` minus the summand of `M - γ`
  have hsplit : ∀ p ∈ Nat.primesBelow (N + 1),
      Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) = ((p : ℝ))⁻¹ - Mertens.M_eq_summand p := by
    intro p hp
    rw [mertens_summand_eq (Nat.prime_of_mem_primesBelow hp), Real.log_inv, one_div]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have hset : Nat.primesBelow (N + 1) = {p ∈ Finset.Ioc 0 N | p.Prime} := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by omega, h3⟩
  -- Mertens' second theorem, exactly
  have hsum : ∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹
      = Real.log (Real.log N) + Mertens.M + Mertens.E₂p (N : ℝ) := by
    have h := Mertens.sum_prime_div_eq (N : ℝ)
    rw [Nat.floor_natCast] at h
    rw [hset, ← h]
    exact Finset.sum_congr rfl fun p _ ↦ (one_div _).symm
  have hnum := mertens_error_const_le
  have hE : -(9.0028 / Real.log N) ≤ Mertens.E₂p (N : ℝ) :=
    calc -(9.0028 / Real.log N) ≤ -((Real.log 4 + 6 + Mertens.E₁) / Real.log N) :=
          neg_le_neg (div_le_div_of_nonneg_right hnum hlog.le)
      _ ≤ -|Mertens.E₂p (N : ℝ)| := neg_le_neg (Mertens.E₂p.abs_le hN2)
      _ ≤ Mertens.E₂p (N : ℝ) := neg_abs_le _
  -- the partial sum of the series for `M - γ` is within `4/N` of it
  have hpart : ∑ p ∈ Nat.primesBelow (N + 1), Mertens.M_eq_summand p
      = ∑ n ∈ Finset.Ioc 0 N, Mertens.M_eq_summand n := by
    rw [hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hn
    · rfl
    · simp
  have htail := Mertens.sum_M_eq_summand_le' hN2
  rw [Nat.floor_natCast, ← hpart, Mertens.γ.eq_eulerMascheroni] at htail
  have htail' := (abs_le.1 htail).2
  linarith

/-- **The Mertens product at `e^γ`, from below**:
`∏_{p ≤ N}(1 - 1/p)⁻¹ ≥ e^{γ - 13.0028/log N} log N` for `N ≥ 2` (`4/N ≤ 4/log N`). -/
theorem exp_eulerMascheroni_le_prod_primesBelow_inv {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (Real.eulerMascheroniConstant - 13.0028 / Real.log N) * Real.log N
      ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hppos : (0 : ℝ) < ∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹ := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact inv_pos.2 (by linarith)
  have h1 := log_prod_primesBelow_inv_ge hN
  have h4 : 4 / (N : ℝ) ≤ 4 / Real.log N :=
    div_le_div_of_nonneg_left (by norm_num) hlog (Real.log_le_self (by linarith))
  have hsplit : 13.0028 / Real.log N = 9.0028 / Real.log N + 4 / Real.log N := by
    rw [← add_div]
    norm_num
  have hle : (Real.eulerMascheroniConstant - 13.0028 / Real.log N) + Real.log (Real.log N)
      ≤ Real.log (∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹) := by
    rw [hsplit]
    linarith
  have h := Real.exp_le_exp.2 hle
  rwa [Real.exp_log hppos, Real.exp_add, Real.exp_log hlog] at h

end RMF
