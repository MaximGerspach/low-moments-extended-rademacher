/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.CosinePrimeSum

/-!
# Mertens' second theorem with its constant named

The explicit twins of the constant-carrying statements of `RMF/NumberTheory/CosinePrimeSum.lean`
that Harper's theorem uses.

* `RMF.mertensSecondConst`: `|M| + (log 4 + 6 + E₁)/log 2`, the constant
  `Mertens.sum_prime_div_eq_log_log` builds, with its proof copied;
* `RMF.primesBelowInvLogLogConst`: `|mertensSecondConst| + 1`, the constant of
  `RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`.
-/

namespace RMF

/-- **The constant of Mertens' second theorem**: `|M| + (log 4 + 6 + E₁)/log 2`, the witness of
`Mertens.sum_prime_div_eq_log_log`. -/
noncomputable def mertensSecondConst : ℝ :=
  |Mertens.M| + (Real.log 4 + 6 + Mertens.E₁) / Real.log 2

/-- **Mertens' second theorem at its constant**: `Mertens.sum_prime_div_eq_log_log`, with its
proof. -/
theorem sum_prime_div_eq_log_log_explicit {x : ℝ} (hx : 2 ≤ x) :
    |∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x)|
      ≤ mertensSecondConst := by
  rw [Mertens.sum_prime_div_eq]
  calc
    _ = |Mertens.M + Mertens.E₂p x| := by ring_nf
    _ ≤ |Mertens.M| + (Real.log 4 + 6 + Mertens.E₁) / Real.log x := by
        grw [abs_add_le, Mertens.E₂p.abs_le hx]
    _ ≤ _ := by
        unfold mertensSecondConst
        gcongr
        have : 0 < Real.log 4 := by apply Real.log_pos; norm_num
        linarith [Mertens.E₁.nonneg]

/-- The constant of `RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le`. -/
noncomputable def primesBelowInvLogLogConst : ℝ := |mertensSecondConst| + 1

/-- **`RMF.exists_abs_sum_primesBelow_inv_sub_log_log_le` at its constant**,
`|mertensSecondConst| + 1`. -/
theorem exists_abs_sum_primesBelow_inv_sub_log_log_le_explicit :
    primesBelowInvLogLogConst > 0 ∧ ∀ N : ℕ, 2 ≤ N →
      |∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹ - Real.log (Real.log N)|
        ≤ primesBelowInvLogLogConst := by
  unfold primesBelowInvLogLogConst
  set C := mertensSecondConst with hCdef
  have h : ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
    fun x hx => sum_prime_div_eq_log_log_explicit hx
  refine ⟨by positivity, fun N hN => ?_⟩
  have hx : (2:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hres := h (N : ℝ) hx
  rw [Nat.floor_natCast, ← primesBelow_succ_eq_filter_Ioc] at hres
  simp only [one_div] at hres
  exact hres.trans (by linarith [le_abs_self C])

end RMF
