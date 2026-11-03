/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MertensExplicit

/-!
# Mertens' third theorem at `e^γ`

The two-sided `RMF.exists_abs_log_prod_primesBelow_sub_log_log_le` bounds
`|log ∏_{p ≤ N}(1 - 1/p)⁻¹ - log log N|` by an unspecified constant.  The upper half is
`log log N + γ + O(1/log N)`:
* `∑_{p ≤ N} 1/p = log log N + M + E₂p N` (`Mertens.sum_prime_div_eq`), with
  `|E₂p N| ≤ 9.0028/log N` (`Mertens.E₂p.abs_le`, `RMF.mertens_error_const_le`);
* the remainder `∑_{p ≤ N}(log(1 - 1/p) + 1/p)` is at least its full series `M - γ`
  (`Mertens.M.eq`), since every term is `≤ 0` (`RMF.mertens_const_le_add_sum`).

So `∏_{p ≤ N}(1 - 1/p)⁻¹ ≤ e^{γ + 9.0028/L₀} log N` once `log N ≥ L₀`
(`RMF.prod_primesBelow_inv_le_exp_eulerMascheroni`).
-/

namespace RMF

/-- **Mertens' third theorem, upper half at `γ`**: for every natural `N ≥ 2`,
`log ∏_{p ≤ N}(1 - 1/p)⁻¹ ≤ log log N + γ + 9.0028/log N`. -/
theorem log_prod_primesBelow_inv_le {N : ℕ} (hN : 2 ≤ N) :
    Real.log (∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
      ≤ Real.log (Real.log N) + Real.eulerMascheroniConstant + 9.0028 / Real.log N := by
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
  -- Mertens' second theorem, exactly
  have hset : Nat.primesBelow (N + 1) = {p ∈ Finset.Ioc 0 N | p.Prime} := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by omega, h3⟩
  have hsum : ∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹
      = Real.log (Real.log N) + Mertens.M + Mertens.E₂p (N : ℝ) := by
    have h := Mertens.sum_prime_div_eq (N : ℝ)
    rw [Nat.floor_natCast] at h
    rw [hset, ← h]
    exact Finset.sum_congr rfl fun p _ ↦ (one_div _).symm
  have hnum := mertens_error_const_le
  have hE : Mertens.E₂p (N : ℝ) ≤ 9.0028 / Real.log N :=
    calc Mertens.E₂p (N : ℝ) ≤ |Mertens.E₂p (N : ℝ)| := le_abs_self _
      _ ≤ (Real.log 4 + 6 + Mertens.E₁) / Real.log N := Mertens.E₂p.abs_le hN2
      _ ≤ 9.0028 / Real.log N := by gcongr
  -- the remainder is at least `M - γ`
  have hM := mertens_const_le_add_sum (Nat.primesBelow (N + 1))
  linarith

/-- **The Mertens product at `e^γ`**: `∏_{p ≤ N}(1 - 1/p)⁻¹ ≤ e^{γ + 9.0028/L₀} log N` for `N ≥ 2`
and `0 < L₀ ≤ log N`. -/
theorem prod_primesBelow_inv_le_exp_eulerMascheroni {N : ℕ} (hN : 2 ≤ N) {L₀ : ℝ} (hL₀ : 0 < L₀)
    (hL : L₀ ≤ Real.log N) :
    ∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹
      ≤ Real.exp (Real.eulerMascheroniConstant + 9.0028 / L₀) * Real.log N := by
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
  have h1 := log_prod_primesBelow_inv_le hN
  have h2 : 9.0028 / Real.log N ≤ 9.0028 / L₀ :=
    div_le_div_of_nonneg_left (by norm_num) hL₀ hL
  have hle : Real.log (∏ p ∈ Nat.primesBelow (N + 1), (1 - ((p : ℝ))⁻¹)⁻¹)
      ≤ (Real.eulerMascheroniConstant + 9.0028 / L₀) + Real.log (Real.log N) := by linarith
  have h := Real.exp_le_exp.2 hle
  rwa [Real.exp_log hppos, Real.exp_add, Real.exp_log hlog] at h

end RMF
