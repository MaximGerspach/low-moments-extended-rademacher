/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.SuppliersExplicit
import RMF.NumberTheory.MertensProductLower
import PrimeNumberTheoremAnd.EulerMascheroniBounds

/-!
# The rough-number sieve at a large level

`RMF.roughCount_sub_le_brun` sifts `[x, x + H]` by the primes `≤ y` with Selberg's sieve at level
`y` (`BrunTitchmarsh.primeInterSieve`), whose bounding sum is only `≥ (log y)/2`; hence the
constant `RMF.roughCountConst = 3`.  At a level `D` far above `y`, the bounding sum is nearly the
whole Mertens product `M = ∏_{p ≤ y}(1 - 1/p)⁻¹ ~ e^γ log y`, and the constant becomes
`e^{-γ}(1 + ε)`.

* `RMF.roughLevelSieve` is the sieve at level `D`.  Its remainders are those of
  `BrunTitchmarsh.primeInterSieve`, so the error is `≤ 5D(1 + log D)³`
  (`RMF.rem_sum_roughLevelSieve_le`).
* `RMF.selbergBoundingSum_roughLevelSieve_ge`: for `l ∣ P(y)`, `g(l) = ∏_{p ∣ l} 1/(p - 1)`.
  Rankin's trick on the terms with `l² > D` gives `S ≥ M - D^{-c} ∏_{p ≤ y}(1 + p^{2c}/(p - 1))`.
* `RMF.prod_one_add_rpow_div_le_rpow`: at `2c = 1/log y`, `p^{2c} ≤ e` and Bernoulli's inequality
  bound that product by `M^e`.
* `RMF.roughCount_sub_le_selberg`:
  `Φ(u + H, y) - Φ(u, y) ≤ H/(M - D^{-1/(2 log y)} M^e) + 5D(1 + log D)³`.
* `RMF.roughCount_sub_le_sieveConst`: with Mertens' product at `e^γ log y` from both sides, the
  count is `≤ 1.001·e^{-γ} H/log y` once `log y ≥ 10⁶`, `D^{1/(2 log y)} ≥ 40000 log² y` and
  `H ≥ 5D(1 + log D)³·20000 log y`.
-/

open Sieve SelbergSieve BoundingSieve
open scoped ArithmeticFunction.zeta ArithmeticFunction.omega

namespace RMF

/-! ### The sieve at level `D` -/

/-- **Selberg's sieve for rough numbers at level `D`**: the integers of `[⌈u⌉, ⌊u + H⌋]`, sifted
by the primes `≤ y`, at level `D`.  It differs from `BrunTitchmarsh.primeInterSieve u H D` only in
the primes it sifts by. -/
noncomputable def roughLevelSieve (u H : ℝ) (y : ℕ) (D : ℝ) (hD : 1 ≤ D) : SelbergSieve where
  support := Finset.Icc ⌈u⌉₊ ⌊u + H⌋₊
  prodPrimes := primorial y
  prodPrimes_squarefree := Sieve.primorial_squarefree _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := H
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := D
  one_le_level := hD

open Classical in
/-- The sifted sum counts the integers of `[⌈u⌉, ⌊u + H⌋]` with no prime factor `≤ y`. -/
lemma siftedSum_roughLevelSieve (u H : ℝ) {y : ℕ} (hy : 1 ≤ y) {D : ℝ} (hD : 1 ≤ D) :
    siftedSum (s := (roughLevelSieve u H y D hD).toBoundingSieve)
      = ((Finset.Icc ⌈u⌉₊ ⌊u + H⌋₊).filter
          (fun d ↦ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (y : ℝ) → ¬ p ∣ d)).card :=
  Sieve.siftedSum_eq (roughLevelSieve u H y D hD) (fun _ _ ↦ rfl) (y : ℝ)
    (by exact_mod_cast hy) (by rw [Nat.floor_natCast]; rfl)

/-- The remainders are those of `BrunTitchmarsh.primeInterSieve`, which sifts by other primes. -/
lemma rem_roughLevelSieve (u H : ℝ) (y : ℕ) {D : ℝ} (hD : 1 ≤ D) (d : ℕ) :
    rem (s := (roughLevelSieve u H y D hD).toBoundingSieve) d
      = rem (s := (BrunTitchmarsh.primeInterSieve u H D hD).toBoundingSieve) d := rfl

/-- **The error term at level `D`**: `∑_{d ∣ P(y), d ≤ D} 3^{ω(d)}|R_d| ≤ 5D(1 + log D)³`. -/
lemma rem_sum_roughLevelSieve_le {u H : ℝ} (hu : 0 < u) (hH : 0 < H) (y : ℕ) {D : ℝ}
    (hD : 1 ≤ D) :
    ∑ d ∈ (roughLevelSieve u H y D hD).prodPrimes.divisors,
        (if (d : ℝ) ≤ (roughLevelSieve u H y D hD).level then
          (3 : ℝ) ^ ω d * |rem (s := (roughLevelSieve u H y D hD).toBoundingSieve) d| else 0)
      ≤ 5 * D * (1 + Real.log D) ^ 3 :=
  Sieve.rem_sum_le_of_const (roughLevelSieve u H y D hD) 5 fun d hd ↦ by
    rw [rem_roughLevelSieve]
    exact BrunTitchmarsh.abs_rem_le u H D hu hH hD (Nat.pos_iff_ne_zero.1 hd)

/-! ### The bounding sum -/

/-- `ν(n) = 1/n` for `n ≠ 0`. -/
lemma nu_roughLevelSieve (u H : ℝ) (y : ℕ) {D : ℝ} (hD : 1 ≤ D) {n : ℕ} (hn : n ≠ 0) :
    (roughLevelSieve u H y D hD).nu n = 1 / (n : ℝ) := by
  simp [roughLevelSieve, ArithmeticFunction.pdiv_apply, hn]

/-- **The Selberg terms**: for `l ∣ P(y)`, `g(l) = ∏_{p ∣ l} 1/(p - 1)`. -/
lemma selbergTerms_roughLevelSieve (u H : ℝ) {y : ℕ} {D : ℝ} (hD : 1 ≤ D) {l : ℕ}
    (hl : l ∣ primorial y) :
    selbergTerms (roughLevelSieve u H y D hD).toBoundingSieve l
      = ∏ p ∈ l.primeFactors, 1 / ((p : ℝ) - 1) := by
  have hsq : Squarefree l := Squarefree.squarefree_of_dvd hl (Sieve.primorial_squarefree y)
  rw [SelbergSieve.selbergTerms_apply, nu_roughLevelSieve u H y hD hsq.ne_zero]
  have hlprod : ((l : ℝ))⁻¹ = ∏ p ∈ l.primeFactors, ((p : ℝ))⁻¹ := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  rw [one_div (l : ℝ), hlprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [nu_roughLevelSieve u H y hD hpp.ne_zero]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hp0 : (p : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < p - 1).ne'
  field_simp

/-- **Sums over the divisors of a primorial**:
`∑_{l ∣ P(y)} ∏_{p ∣ l} a(p) = ∏_{p ≤ y}(1 + a(p))`. -/
lemma sum_divisors_primorial_prod_eq (a : ℕ → ℝ) (y : ℕ) :
    ∑ l ∈ (primorial y).divisors, ∏ p ∈ l.primeFactors, a p
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + a p) := by
  have h := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors a)
    |>.prodPrimeFactors_one_add_of_squarefree (Sieve.primorial_squarefree y)
  rw [primeFactors_primorial] at h
  have hl : ∀ l ∈ (primorial y).divisors,
      ArithmeticFunction.prodPrimeFactors a l = ∏ p ∈ l.primeFactors, a p :=
    fun l hl => ArithmeticFunction.prodPrimeFactors_apply (Nat.pos_of_mem_divisors hl).ne'
  have hp : ∀ p ∈ Nat.primesLE y, 1 + ArithmeticFunction.prodPrimeFactors a p = 1 + a p := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.1 hp).2
    rw [ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors,
      Finset.prod_singleton]
  rw [Finset.sum_congr rfl hl, Finset.prod_congr rfl hp] at h
  exact h.symm

/-- **The bounding sum from below**, by Rankin's trick on the terms with `l² > D`: for `c ≥ 0`,
`S ≥ ∏_{p ≤ y}(1 - 1/p)⁻¹ - D^{-c} ∏_{p ≤ y}(1 + p^{2c}/(p - 1))`. -/
theorem selbergBoundingSum_roughLevelSieve_ge (u H : ℝ) (y : ℕ) {D : ℝ} (hD : 1 ≤ D) {c : ℝ}
    (hc : 0 ≤ c) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹
        - D ^ (-c) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (2 * c) / ((p : ℝ) - 1))
      ≤ (roughLevelSieve u H y D hD).selbergBoundingSum := by
  have hM : ∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + 1 / ((p : ℝ) - 1)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
    have hp1 : (p : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < p - 1).ne'
    field_simp
    ring
  rw [hM, ← sum_divisors_primorial_prod_eq, ← sum_divisors_primorial_prod_eq, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  unfold selbergBoundingSum
  refine Finset.sum_le_sum fun l hl => ?_
  have hlP : l ∣ primorial y := Nat.dvd_of_mem_divisors hl
  have hsq : Squarefree l := Squarefree.squarefree_of_dvd hlP (Sieve.primorial_squarefree y)
  have hG0 : 0 ≤ ∏ p ∈ l.primeFactors, 1 / ((p : ℝ) - 1) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg zero_le_one (by linarith)
  have hW : ∏ p ∈ l.primeFactors, (p : ℝ) ^ (2 * c) / ((p : ℝ) - 1)
      = (l : ℝ) ^ (2 * c) * ∏ p ∈ l.primeFactors, 1 / ((p : ℝ) - 1) := by
    have h1 : ∀ p ∈ l.primeFactors, (p : ℝ) ^ (2 * c) / ((p : ℝ) - 1)
        = (p : ℝ) ^ (2 * c) * (1 / ((p : ℝ) - 1)) := fun p _ => by ring
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib,
      Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
  rw [selbergTerms_roughLevelSieve u H hD hlP, hW]
  have hDc0 : 0 ≤ D ^ (-c) := Real.rpow_nonneg (by linarith) _
  have hlc0 : 0 ≤ (l : ℝ) ^ (2 * c) := Real.rpow_nonneg (Nat.cast_nonneg l) _
  split_ifs with hlD
  · have h0 := mul_nonneg hDc0 (mul_nonneg hlc0 hG0)
    linarith
  · have hlt : D < (l : ℝ) ^ 2 := lt_of_not_ge hlD
    have h1 : D ^ c ≤ (l : ℝ) ^ (2 * c) := by
      rw [Real.rpow_mul (Nat.cast_nonneg l), Real.rpow_two]
      exact Real.rpow_le_rpow (by linarith) hlt.le hc
    have h2 : 1 ≤ D ^ (-c) * (l : ℝ) ^ (2 * c) := by
      rw [Real.rpow_neg (by linarith), inv_mul_eq_div,
        one_le_div (Real.rpow_pos_of_pos (by linarith) c)]
      exact h1
    have h3 := mul_le_mul_of_nonneg_right h2 hG0
    linarith

/-- **Rankin's product at `2c = 1/log y`**: `p^{1/log y} ≤ e` for `p ≤ y`, and Bernoulli's
inequality `1 + e·t ≤ (1 + t)^e` gives
`∏_{p ≤ y}(1 + p^{1/log y}/(p - 1)) ≤ (∏_{p ≤ y}(1 - 1/p)⁻¹)^e`. -/
lemma prod_one_add_rpow_div_le_rpow {y : ℕ} (hy : 2 ≤ y) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (2 * (1 / (2 * Real.log y))) / ((p : ℝ) - 1))
      ≤ (∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹) ^ Real.exp 1 := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hnonneg : ∀ p ∈ Nat.primesBelow (y + 1), 0 ≤ (1 - ((p : ℝ))⁻¹)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    exact inv_nonneg.2 (by linarith)
  rw [← Real.finsetProd_rpow _ _ hnonneg]
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) (2 * (1 / (2 * Real.log y))))
      (by linarith : (0 : ℝ) ≤ p - 1)
    linarith
  · have hpp := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hpy : (p : ℝ) ≤ (y : ℝ) := by
      have := Nat.lt_of_mem_primesBelow hp
      exact_mod_cast Nat.lt_succ_iff.1 this
    have hexp : (p : ℝ) ^ (2 * (1 / (2 * Real.log y))) ≤ Real.exp 1 := by
      rw [show 2 * (1 / (2 * Real.log y)) = 1 / Real.log y by field_simp,
        Real.rpow_def_of_pos (by linarith)]
      refine Real.exp_le_exp.2 ?_
      rw [mul_one_div, div_le_one hly]
      exact Real.log_le_log (by linarith) hpy
    have hq0 : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    have hbern := one_add_mul_self_le_rpow_one_add (s := 1 / ((p : ℝ) - 1)) (by linarith) he1
    have hid : 1 + 1 / ((p : ℝ) - 1) = (1 - ((p : ℝ))⁻¹)⁻¹ := by
      have hp0 : (p : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
      have hp1 : (p : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < p - 1).ne'
      field_simp
      ring
    rw [← hid]
    calc 1 + (p : ℝ) ^ (2 * (1 / (2 * Real.log y))) / ((p : ℝ) - 1)
        = 1 + (p : ℝ) ^ (2 * (1 / (2 * Real.log y))) * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ 1 + Real.exp 1 * (1 / ((p : ℝ) - 1)) := by
          have := mul_le_mul_of_nonneg_right hexp hq0
          linarith
      _ ≤ (1 + 1 / ((p : ℝ) - 1)) ^ Real.exp 1 := hbern

/-! ### The rough count -/

/-- **The rough count at level `D`**: for `y ≥ 2`, `u, H > 0`, `D ≥ 1` and
`M = ∏_{p ≤ y}(1 - 1/p)⁻¹` with `M - D^{-1/(2 log y)} M^e > 0`,
`Φ(u + H, y) - Φ(u, y) ≤ H/(M - D^{-1/(2 log y)} M^e) + 5D(1 + log D)³`. -/
theorem roughCount_sub_le_selberg {y : ℕ} (hy : 2 ≤ y) {u H D : ℝ} (hu : 0 < u) (hH : 0 < H)
    (hD : 1 ≤ D)
    (hS : 0 < ∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹
      - D ^ (-(1 / (2 * Real.log y)))
        * (∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹) ^ Real.exp 1) :
    (roughCount y (u + H) : ℝ) - (roughCount y u : ℝ)
      ≤ H / (∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹
          - D ^ (-(1 / (2 * Real.log y)))
            * (∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹) ^ Real.exp 1)
        + 5 * D * (1 + Real.log D) ^ 3 := by
  classical
  have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hxH : u ≤ u + H := by linarith
  set A : Finset ℕ := {n ∈ Finset.Icc 1 ⌊u + H⌋₊ | IsRough y n} with hA
  set B : Finset ℕ := {n ∈ Finset.Icc 1 ⌊u⌋₊ | IsRough y n} with hB
  have hBA : B ⊆ A := by
    intro n hn
    rw [hB, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [hA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor hxH)⟩, hn.2⟩
  -- the difference of counts is the count over the gap
  have hdiff : (roughCount y (u + H) : ℝ) - (roughCount y u : ℝ) = ((A \ B).card : ℝ) := by
    have hcard := Finset.card_sdiff_add_card_eq_card hBA
    rw [roughCount, roughCount, ← hA, ← hB]
    have : ((A \ B).card : ℝ) + (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hcard
    linarith
  -- the gap sits inside the sifted set
  have hsub : A \ B ⊆ {d ∈ Finset.Icc ⌈u⌉₊ ⌊u + H⌋₊ |
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (y : ℝ) → ¬ p ∣ d} := by
    intro n hn
    rw [Finset.mem_sdiff, hA, hB, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hn2⟩, hrough⟩, hnotB⟩ := hn
    have hgt : ⌊u⌋₊ < n := by
      by_contra hle
      push Not at hle
      exact hnotB ⟨⟨hn1, hle⟩, hrough⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_trans (Nat.ceil_le_floor_add_one u) (by omega), hn2⟩, fun p hp hpy hpn => ?_⟩
    have := (isRough_iff.1 hrough) p hp hpn
    have : (y : ℝ) < (p : ℝ) := by exact_mod_cast this
    linarith
  -- the bounding sum
  have hc : (0 : ℝ) ≤ 1 / (2 * Real.log y) := by positivity
  have hDc0 : 0 ≤ D ^ (-(1 / (2 * Real.log y))) := Real.rpow_nonneg (by linarith) _
  have hSge : ∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹
        - D ^ (-(1 / (2 * Real.log y)))
          * (∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹) ^ Real.exp 1
      ≤ (roughLevelSieve u H y D hD).selbergBoundingSum := by
    refine le_trans ?_ (selbergBoundingSum_roughLevelSieve_ge u H y hD hc)
    have := mul_le_mul_of_nonneg_left (prod_one_add_rpow_div_le_rpow hy) hDc0
    linarith
  calc (roughCount y (u + H) : ℝ) - (roughCount y u : ℝ) = ((A \ B).card : ℝ) := hdiff
    _ ≤ (({d ∈ Finset.Icc ⌈u⌉₊ ⌊u + H⌋₊ |
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (y : ℝ) → ¬ p ∣ d}).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = siftedSum (s := (roughLevelSieve u H y D hD).toBoundingSieve) := by
        rw [siftedSum_roughLevelSieve u H (by omega) hD]
    _ ≤ (roughLevelSieve u H y D hD).totalMass / (roughLevelSieve u H y D hD).selbergBoundingSum
          + ∑ d ∈ (roughLevelSieve u H y D hD).prodPrimes.divisors,
            (if (d : ℝ) ≤ (roughLevelSieve u H y D hD).level then
              (3 : ℝ) ^ ω d * |rem (s := (roughLevelSieve u H y D hD).toBoundingSieve) d|
            else 0) :=
        selberg_bound_simple _
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_left hH.le hS hSge)
        (rem_sum_roughLevelSieve_le hu hH y hD)

/-! ### The constant `1.001·e^{-γ}` -/

/-- **The sieve constant at a large level**, `1.001·e^{-γ}`. -/
noncomputable def sieveConst : ℝ := 1001 / 1000 * Real.exp (-Real.eulerMascheroniConstant)

lemma sieveConst_pos : 0 < sieveConst := by
  unfold sieveConst
  positivity

/-- **The rough count at `1.001·e^{-γ}`**: for `y ≥ 2` with `log y ≥ 10⁶`, `u, H > 0` and a level
`D ≥ 1` with `D^{1/(2 log y)} ≥ 40000 log² y` and `H ≥ 5D(1 + log D)³·20000 log y`,
`Φ(u + H, y) - Φ(u, y) ≤ 1.001·e^{-γ} H/log y`.

`RMF.roughCount_sub_le_selberg`, with `M ≤ 2 log y`
(`RMF.prod_primesBelow_inv_le_exp_eulerMascheroni`) so that `D^{-1/(2 log y)} M^e ≤ M/10⁴`, and
`M ≥ e^{γ - 13.0028/log y} log y` (`RMF.exp_eulerMascheroni_le_prod_primesBelow_inv`). -/
theorem roughCount_sub_le_sieveConst {y : ℕ} (hy : 2 ≤ y) {u H D : ℝ} (hu : 0 < u) (hH : 0 < H)
    (hD : 1 ≤ D) (hℓ : 1000000 ≤ Real.log y)
    (hθ : 40000 * Real.log y ^ 2 ≤ D ^ (1 / (2 * Real.log y)))
    (herr : 5 * D * (1 + Real.log D) ^ 3 * (20000 * Real.log y) ≤ H) :
    (roughCount y (u + H) : ℝ) - (roughCount y u : ℝ) ≤ sieveConst * H / Real.log y := by
  have hcountS := roughCount_sub_le_selberg (u := u) (H := H) (D := D) hy hu hH hD
  set ℓ := Real.log (y : ℝ) with hℓdef
  set M := ∏ p ∈ Nat.primesBelow (y + 1), (1 - ((p : ℝ))⁻¹)⁻¹ with hMdef
  have hℓ0 : 0 < ℓ := by linarith
  have hγhi := hγ_hi
  have hγlo := hγ_lo
  have hlog2 := Real.log_two_gt_d9
  -- Mertens' product from above and below
  have hMup : M ≤ 2 * ℓ := by
    have h := prod_primesBelow_inv_le_exp_eulerMascheroni hy (L₀ := 1000000) (by norm_num) hℓ
    have he : Real.exp (Real.eulerMascheroniConstant + 9.0028 / 1000000) ≤ 2 := by
      calc Real.exp (Real.eulerMascheroniConstant + 9.0028 / 1000000)
          ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by norm_num at hγhi hlog2 ⊢; linarith)
        _ = 2 := Real.exp_log (by norm_num)
    exact h.trans (mul_le_mul_of_nonneg_right he hℓ0.le)
  have hMlo := exp_eulerMascheroni_le_prod_primesBelow_inv hy
  rw [← hℓdef, ← hMdef] at hMlo
  have hM1 : 1 ≤ M := by
    have h1 : 13.0028 / ℓ ≤ 1 / 2 := by
      rw [div_le_iff₀ hℓ0]
      linarith
    have h2 : 1 ≤ Real.exp (Real.eulerMascheroniConstant - 13.0028 / ℓ) :=
      Real.one_le_exp (by norm_num at hγlo; linarith)
    nlinarith
  -- the Rankin term is at most `M/10⁴`
  have hDc0 : 0 ≤ D ^ (-(1 / (2 * ℓ))) := Real.rpow_nonneg (by linarith) _
  have hθM : D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1 ≤ M / 10000 := by
    have hMe : M ^ Real.exp 1 ≤ M ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by have := Real.exp_one_lt_d9; linarith)
    have hM3 : M ^ (3 : ℝ) = M * M ^ 2 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hM2 : M ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have hDc : D ^ (-(1 / (2 * ℓ))) * (40000 * ℓ ^ 2) ≤ 1 := by
      rw [Real.rpow_neg (by linarith), inv_mul_le_iff₀ (Real.rpow_pos_of_pos (by linarith) _),
        mul_one]
      exact hθ
    calc D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1
        ≤ D ^ (-(1 / (2 * ℓ))) * (M * (4 * ℓ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (hMe.trans (le_of_eq hM3 |>.trans ?_)) hDc0
          exact mul_le_mul_of_nonneg_left hM2 (by linarith)
      _ = M * (D ^ (-(1 / (2 * ℓ))) * (40000 * ℓ ^ 2)) / 10000 := by ring
      _ ≤ M * 1 / 10000 := by
          gcongr
      _ = M / 10000 := by ring
  have hS : 9999 / 10000 * M ≤ M - D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1 := by linarith
  have hSpos : 0 < M - D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1 := by linarith
  have hcount := hcountS hSpos
  -- the main term
  set E := Real.exp (-Real.eulerMascheroniConstant) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEhalf : 1 / 2 ≤ E := by
    have h : Real.exp (-Real.log 2) ≤ E :=
      Real.exp_le_exp.2 (by norm_num at hγhi hlog2 ⊢; linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at h
  have hexp : Real.exp (13.0028 / ℓ) ≤ 1 + 2 * (13.0028 / 1000000) := by
    have ht : 13.0028 / ℓ ≤ 13.0028 / 1000000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hℓ
    have ht0 : 0 ≤ 13.0028 / ℓ := by positivity
    have habs : |13.0028 / ℓ| ≤ 1 := by
      rw [abs_of_nonneg ht0]
      linarith
    have h := Real.abs_exp_sub_one_le habs
    rw [abs_of_nonneg ht0] at h
    linarith [(abs_le.1 h).2]
  have hX0 : 0 ≤ E * (H / ℓ) := by positivity
  have hmain : H / (M - D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1)
      ≤ 10000 / 9999 * (1 + 2 * (13.0028 / 1000000)) * (E * (H / ℓ)) := by
    have hlo0 : 0 < Real.exp (Real.eulerMascheroniConstant - 13.0028 / ℓ) * ℓ := by positivity
    have h1 : H / (M - D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1) ≤ H / (9999 / 10000 * M) :=
      div_le_div_of_nonneg_left hH.le (by positivity) hS
    have h2 : H / (9999 / 10000 * M)
        ≤ H / (9999 / 10000 * (Real.exp (Real.eulerMascheroniConstant - 13.0028 / ℓ) * ℓ)) :=
      div_le_div_of_nonneg_left hH.le (by positivity)
        (mul_le_mul_of_nonneg_left hMlo (by norm_num))
    have h3 : H / (9999 / 10000 * (Real.exp (Real.eulerMascheroniConstant - 13.0028 / ℓ) * ℓ))
        = 10000 / 9999 * Real.exp (13.0028 / ℓ) * (E * (H / ℓ)) := by
      rw [hE, Real.exp_sub, Real.exp_neg]
      field_simp
    calc H / (M - D ^ (-(1 / (2 * ℓ))) * M ^ Real.exp 1)
        ≤ 10000 / 9999 * Real.exp (13.0028 / ℓ) * (E * (H / ℓ)) := h1.trans (h2.trans_eq h3)
      _ ≤ 10000 / 9999 * (1 + 2 * (13.0028 / 1000000)) * (E * (H / ℓ)) := by
          gcongr
  have herr' : 5 * D * (1 + Real.log D) ^ 3 ≤ E * (H / ℓ) / 10000 := by
    have h1 : 5 * D * (1 + Real.log D) ^ 3 ≤ H / (20000 * ℓ) := by
      rw [le_div_iff₀ (by positivity)]
      exact herr
    have h2 : H / (20000 * ℓ) = (H / ℓ) / 20000 := by
      field_simp
    have h3 : 0 ≤ H / ℓ := by positivity
    have h4 : (H / ℓ) / 20000 ≤ E * (H / ℓ) / 10000 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith
    linarith
  have hfinal : sieveConst * H / ℓ = 1001 / 1000 * (E * (H / ℓ)) := by
    unfold sieveConst
    rw [hE]
    ring
  rw [hfinal]
  have hc1 : 10000 / 9999 * (1 + 2 * (13.0028 / 1000000)) + 1 / 10000 ≤ (1001 / 1000 : ℝ) := by
    norm_num
  nlinarith [hcount, hmain, herr', hX0, hc1]

end RMF
