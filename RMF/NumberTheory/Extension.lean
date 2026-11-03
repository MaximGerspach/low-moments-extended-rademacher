/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Extending values at the primes to a multiplicative function

A random multiplicative function is built in two stages: choose the values at the primes at
random, then extend them to all of `ℕ` by multiplicativity.  This file is the *deterministic*
half — no probability appears — so that the probabilistic content is isolated in
`Probability/PrimeValues.lean`.

There are two extension conventions in the literature, and both are needed:

* `RMF.compMultExtension x` is **completely multiplicative**:
  `f (p ^ k) = x p ^ k`.  This is the convention for the Steinhaus and extended Rademacher
  functions.
* `RMF.squarefreeExtension x` is **multiplicative and supported on the squarefree integers**:
  `f (p) = x p` and `f (p ^ k) = 0` for `k ≥ 2`.  This is Wintner's original convention,
  used for the Rademacher function.

Both are defined for an arbitrary `x : ℕ → R` with `R` a commutative monoid with zero — no
analysis is involved at this stage — and only the values of `x` at primes matter.

Mathlib's `ArithmeticFunction.prodPrimeFactors` (`∏ᵖ p ∣ n, f p`) is a third, different
convention: it sends `p ^ k` to `f p` for every `k ≥ 1`.  Neither of the two conventions
here is in Mathlib.
-/

open Nat Finset

namespace RMF

variable {R : Type*} [CommMonoidWithZero R]

/-- The completely multiplicative extension of `x`: the arithmetic function sending
`n = ∏ pᵢ ^ kᵢ` to `∏ x pᵢ ^ kᵢ`, and `0` to `0`. -/
noncomputable def compMultExtension (x : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p k => x p ^ k
  map_zero' := if_pos rfl

/-- The multiplicative extension of `x` supported on squarefree integers: `n` squarefree is
sent to the product of `x p` over the primes `p ∣ n`, and every other `n` to `0`. -/
noncomputable def squarefreeExtension (x : ℕ → R) : ArithmeticFunction R where
  toFun n := if Squarefree n then ∏ p ∈ n.primeFactors, x p else 0
  map_zero' := if_neg (by simp)

@[simp]
lemma compMultExtension_apply_of_ne_zero (x : ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    compMultExtension x n = n.factorization.prod fun p k => x p ^ k := if_neg hn

@[simp]
lemma squarefreeExtension_apply_of_squarefree (x : ℕ → R) {n : ℕ} (hn : Squarefree n) :
    squarefreeExtension x n = ∏ p ∈ n.primeFactors, x p := if_pos hn

lemma squarefreeExtension_apply_of_not_squarefree (x : ℕ → R) {n : ℕ} (hn : ¬ Squarefree n) :
    squarefreeExtension x n = 0 := if_neg hn

lemma compMultExtension_apply_one (x : ℕ → R) : compMultExtension x 1 = 1 := by
  simp [compMultExtension_apply_of_ne_zero]

lemma squarefreeExtension_apply_one (x : ℕ → R) : squarefreeExtension x 1 = 1 := by
  simp [squarefreeExtension_apply_of_squarefree]

@[simp]
lemma compMultExtension_apply_prime (x : ℕ → R) {p : ℕ} (hp : p.Prime) :
    compMultExtension x p = x p := by
  rw [compMultExtension_apply_of_ne_zero x hp.ne_zero, hp.factorization]
  simp

@[simp]
lemma squarefreeExtension_apply_prime (x : ℕ → R) {p : ℕ} (hp : p.Prime) :
    squarefreeExtension x p = x p := by
  rw [squarefreeExtension_apply_of_squarefree x hp.squarefree, hp.primeFactors, prod_singleton]

/-- The defining property of the completely multiplicative convention. -/
@[simp]
lemma compMultExtension_apply_prime_pow (x : ℕ → R) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    compMultExtension x (p ^ k) = x p ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [compMultExtension_apply_of_ne_zero x (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
  simp

/-- The defining property of the squarefree-supported convention: it vanishes on every
higher prime power. -/
lemma squarefreeExtension_apply_prime_pow (x : ℕ → R) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    squarefreeExtension x (p ^ k) = 0 := by
  refine squarefreeExtension_apply_of_not_squarefree x fun hsf => ?_
  have hu : IsUnit p := hsf p (by rw [← sq]; exact pow_dvd_pow p hk)
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)

/-- The value of `compMultExtension x` at `n ≠ 0` as a product over any
finite set of primes containing those dividing `n`.  Two integers can then be compared
factor by factor over a common index set. -/
lemma compMultExtension_apply_eq_prod (x : ℕ → R) {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ}
    (hS : n.primeFactors ⊆ S) :
    compMultExtension x n = ∏ p ∈ S, x p ^ n.factorization p := by
  rw [compMultExtension_apply_of_ne_zero x hn]
  exact Finsupp.prod_of_support_subset _ (by rwa [Nat.support_factorization]) _
    fun _ _ => pow_zero _

/-- `compMultExtension x` is completely multiplicative on nonzero arguments. -/
lemma compMultExtension_apply_mul (x : ℕ → R) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    compMultExtension x (m * n) = compMultExtension x m * compMultExtension x n := by
  rw [compMultExtension_apply_of_ne_zero x (mul_ne_zero hm hn),
    compMultExtension_apply_of_ne_zero x hm,
    compMultExtension_apply_of_ne_zero x hn, Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]

lemma isMultiplicative_compMultExtension (x : ℕ → R) :
    (compMultExtension x).IsMultiplicative := by
  refine ⟨compMultExtension_apply_one x, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [(Nat.coprime_zero_left n).mp hmn]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [(Nat.coprime_zero_right m).mp hmn]
  exact compMultExtension_apply_mul x hm hn

lemma isMultiplicative_squarefreeExtension (x : ℕ → R) :
    (squarefreeExtension x).IsMultiplicative := by
  refine ⟨squarefreeExtension_apply_one x, fun {m n} hmn => ?_⟩
  by_cases hsf : Squarefree (m * n)
  · obtain ⟨-, hm, hn⟩ := Nat.squarefree_mul_iff.mp hsf
    rw [squarefreeExtension_apply_of_squarefree x hsf, squarefreeExtension_apply_of_squarefree x hm,
      squarefreeExtension_apply_of_squarefree x hn,
      Nat.primeFactors_mul hm.ne_zero hn.ne_zero,
      prod_union (Nat.Coprime.disjoint_primeFactors hmn)]
  · rw [squarefreeExtension_apply_of_not_squarefree x hsf]
    by_cases hm : Squarefree m
    · by_cases hn : Squarefree n
      · exact absurd (Nat.squarefree_mul_iff.mpr ⟨hmn, hm, hn⟩) hsf
      · rw [squarefreeExtension_apply_of_not_squarefree x hn, mul_zero]
    · rw [squarefreeExtension_apply_of_not_squarefree x hm, zero_mul]

/-- On a squarefree argument the two extensions agree. -/
lemma compMultExtension_eq_squarefreeExtension_of_squarefree (x : ℕ → R) {n : ℕ}
    (hn : Squarefree n) :
    compMultExtension x n = squarefreeExtension x n := by
  rw [compMultExtension_apply_of_ne_zero x hn.ne_zero,
    squarefreeExtension_apply_of_squarefree x hn, Finsupp.prod,
    Nat.support_factorization]
  refine prod_congr rfl fun p hp => ?_
  rw [Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

/-- The completely multiplicative extension is completely multiplicative, `0` included: the
unconditional form of `RMF.compMultExtension_apply_mul`. -/
lemma compMultExtension_apply_mul' (x : ℕ → R) (m n : ℕ) :
    compMultExtension x (m * n) = compMultExtension x m * compMultExtension x n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact compMultExtension_apply_mul x hm hn

/-- On the squarefrees, the squarefree extension is the product of its own values at the prime
factors. -/
lemma squarefreeExtension_apply_eq_prod_primeFactors (x : ℕ → R) {n : ℕ} (hn : Squarefree n) :
    squarefreeExtension x n = ∏ p ∈ n.primeFactors, squarefreeExtension x p := by
  rw [squarefreeExtension_apply_of_squarefree _ hn]
  exact Finset.prod_congr rfl fun p hp =>
    (squarefreeExtension_apply_prime _ (Nat.prime_of_mem_primeFactors hp)).symm

/-- **A completely multiplicative function is the extension of its values at the primes.** -/
lemma eq_compMultExtension_of_apply_mul {g : ArithmeticFunction R} (h1 : g 1 = 1)
    (hmul : ∀ m n, g (m * n) = g m * g n) : g = compMultExtension fun p => g p := by
  have hg : g.IsMultiplicative := ⟨h1, fun {m n} _ => hmul m n⟩
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hg _
    (isMultiplicative_compMultExtension _)).2 fun p i hp => ?_
  have hpow : ∀ k : ℕ, g (p ^ k) = g p ^ k := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  rw [compMultExtension_apply_prime_pow _ hp, hpow]

/-- **A function given by `∏_{p ∣ n} g p` on the squarefrees and `0` elsewhere is the squarefree
extension of its values at the primes.** -/
lemma eq_squarefreeExtension_of_apply {g : ArithmeticFunction R}
    (hsq : ∀ n, Squarefree n → g n = ∏ p ∈ n.primeFactors, g p)
    (hns : ∀ n, ¬ Squarefree n → g n = 0) : g = squarefreeExtension fun p => g p := by
  ext n
  by_cases hn : Squarefree n
  · rw [squarefreeExtension_apply_of_squarefree _ hn, hsq n hn]
  · rw [squarefreeExtension_apply_of_not_squarefree _ hn, hns n hn]

end RMF
