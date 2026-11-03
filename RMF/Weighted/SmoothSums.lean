/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.SmoothTail
import RMF.NumberTheory.LogPrimeSum

/-!
# Smooth squarefree sums with a logarithmic weight

The fluctuation bound (`RMF/Weighted/Fluctuations.lean`) needs

`∑_{P(m) ≤ y} (1 + log m)/m ≪ (log y)²`,

which follows from `≤ (1 + ∑_{p≤y} log p/p)·∏_{p≤y}(1 + 1/p)` and Mertens.

The squarefree `y`-smooth `m` are the divisors of `y#`, i.e. the products of subsets of
`Nat.primesBelow (y+1)`, so everything happens on that powerset:
`RMF.sum_smoothSquarefree_eq_sum_powerset` moves *any* sum over the range there along
`m ↦ m.primeFactors` — the bijection whose inverse `t ↦ ∏ p ∈ t, p` already carries
`RMF.sum_smoothSquarefree_rpow_eq_prod` — and under it `1/m = ∏_{p ∈ t} 1/p` and
`log m = ∑_{p ∈ t} log p`, so the summand splits as

`(1 + log m)/m = ∏_{p ∈ t} 1/p + (∑_{p ∈ t} log p) ∏_{p ∈ t} 1/p`.

The first piece is `∏_{p ≤ y}(1 + 1/p)` (`Finset.prod_one_add`).  The second is bounded by
`RMF.sum_powerset_sum_mul_prod_le`,

`∑_{t ⊆ s} (∑_{i ∈ t} aᵢ) ∏_{i ∈ t} bᵢ ≤ (∑_{i ∈ s} aᵢbᵢ) ∏_{i ∈ s} (1 + bᵢ)`,

an induction on `s`, which does the work of the reindexing `{d ∣ n : p ∣ d} ↔ {e ∣ n/p}`.
At `aₚ = log p`, `bₚ = 1/p` its two factors are Mertens' first theorem
(`RMF.sum_log_div_prime_le`, `≤ log y + log 4 + 4`) and `∏_{p ≤ y}(1 + 1/p) ≪ log y`
(`RMF.exists_prod_one_add_le_rpow_log` at `c = 1`), so the total is `(log y)·(log y)`.
-/

open Finset

namespace RMF

/-- **A subset sum carrying one additive weight, against a multiplicative one.**  For
nonnegative `a` and `b`,
`∑_{t ⊆ s} (∑_{i ∈ t} aᵢ) ∏_{i ∈ t} bᵢ ≤ (∑_{i ∈ s} aᵢbᵢ) ∏_{i ∈ s} (1 + bᵢ)`.

Equality would carry `∏_{j ≠ i}(1 + b_j)` where the right-hand side has the full product.  The
induction splits the subsets of `insert j s` by whether they contain `j`. -/
theorem sum_powerset_sum_mul_prod_le {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (s : Finset ι) :
    ∑ t ∈ s.powerset, (∑ i ∈ t, a i) * ∏ i ∈ t, b i
      ≤ (∑ i ∈ s, a i * b i) * ∏ i ∈ s, (1 + b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hbj : (0 : ℝ) ≤ b j := hb j
    have hG : (0 : ℝ) ≤ ∏ i ∈ s, (1 + b i) :=
      Finset.prod_nonneg fun i _ => by linarith [hb i]
    have hGeq : ∑ t ∈ s.powerset, ∏ i ∈ t, b i = ∏ i ∈ s, (1 + b i) :=
      (Finset.prod_one_add s).symm
    have hsplit : ∑ t ∈ s.powerset, (∑ i ∈ insert j t, a i) * ∏ i ∈ insert j t, b i
        = b j * ∑ t ∈ s.powerset, (∑ i ∈ t, a i) * ∏ i ∈ t, b i
          + a j * b j * ∏ i ∈ s, (1 + b i) := by
      rw [← hGeq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hjt : j ∉ t := fun h => hj (Finset.mem_powerset.1 ht h)
      rw [Finset.sum_insert hjt, Finset.prod_insert hjt]
      ring
    rw [Finset.sum_powerset_insert hj (fun t => (∑ i ∈ t, a i) * ∏ i ∈ t, b i), hsplit,
      Finset.sum_insert hj, Finset.prod_insert hj]
    have hmain : (∑ t ∈ s.powerset, (∑ i ∈ t, a i) * ∏ i ∈ t, b i) * (1 + b j)
        ≤ ((∑ i ∈ s, a i * b i) * ∏ i ∈ s, (1 + b i)) * (1 + b j) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hextra : (0 : ℝ) ≤ a j * (b j * b j * ∏ i ∈ s, (1 + b i)) :=
      mul_nonneg (ha j) (mul_nonneg (mul_nonneg hbj hbj) hG)
    linarith only [hmain, hextra]

/-- **The smooth squarefree harmonic mass.**  `∑_{P(m) ≤ y, m squarefree} 1/m ≤ C·log y`, which is
`∏_{p ≤ y}(1 + 1/p)` transported to the powerset by `RMF.sum_smoothSquarefree_eq_sum_powerset` and
bounded by `RMF.exists_prod_one_add_le_rpow_log` at `c = 1`.  The crude alternative to Rankin in
the fluctuation bound (`RMF/Weighted/Fluctuations.lean`): dropping `m > x` loses the factor
`e^{-U}` but is uniform in `x`, which that bound needs when `U = log x / log y` is bounded — the
range `q → 1` of the upper bound for fixed `½ < q < 1`. -/
theorem exists_sum_smoothSquarefree_inv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      ∑ m ∈ {m ∈ Finset.Icc 1 (primorial y)
          | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, ((m : ℝ))⁻¹
        ≤ C * Real.log y := by
  obtain ⟨C₁, -, hprod⟩ := exists_prod_one_add_le_rpow_log
  refine ⟨Real.exp C₁, Real.exp_pos _, ?_⟩
  intro y hy
  have hterm : ∀ t ∈ (Nat.primesBelow (y + 1)).powerset,
      (((∏ p ∈ t, p : ℕ) : ℝ))⁻¹ = ∏ p ∈ t, ((p : ℝ))⁻¹ := fun t _ => by
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  have hGeq : ∑ t ∈ (Nat.primesBelow (y + 1)).powerset, ∏ p ∈ t, ((p : ℝ))⁻¹
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + ((p : ℝ))⁻¹) := (Finset.prod_one_add _).symm
  rw [sum_smoothSquarefree_eq_sum_powerset y fun m => ((m : ℝ))⁻¹,
    Finset.sum_congr rfl hterm, hGeq]
  have h := hprod y hy 1 zero_le_one (fun p => ((p : ℝ))⁻¹)
    (fun p _ => inv_nonneg.2 (Nat.cast_nonneg p)) (fun p _ => le_of_eq (one_mul _).symm)
  rwa [one_mul, Real.rpow_one] at h

/-- **The logarithmically weighted smooth squarefree sum.**  `∑_{P(m)≤y} (1+log m)/m ≪ (log y)²`. -/
theorem exists_sum_smoothSquarefree_one_add_log_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      ∑ m ∈ {m ∈ Finset.Icc 1 (primorial y)
          | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (1 + Real.log m) / m
        ≤ C * (Real.log y) ^ 2 := by
  obtain ⟨C₁, -, hprod⟩ := exists_prod_one_add_le_rpow_log
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfac : (0 : ℝ) < 1 + (5 + Real.log 4) / Real.log 2 := by
    have h := div_nonneg (by linarith : (0 : ℝ) ≤ 5 + Real.log 4) hlog2.le
    linarith
  refine ⟨Real.exp C₁ * (1 + (5 + Real.log 4) / Real.log 2), mul_pos (Real.exp_pos _) hfac, ?_⟩
  intro y hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  -- `∏_{p ≤ y}(1 + 1/p) ≪ log y`: Mertens' second theorem, through the packaged product bound
  have hprodle : ∏ p ∈ Nat.primesBelow (y + 1), (1 + ((p : ℝ))⁻¹)
      ≤ Real.exp C₁ * Real.log y := by
    have h := hprod y hy 1 zero_le_one (fun p => ((p : ℝ))⁻¹)
      (fun p _ => inv_nonneg.2 (Nat.cast_nonneg p)) (fun p _ => le_of_eq (one_mul _).symm)
    rwa [one_mul, Real.rpow_one] at h
  have hGnn : (0 : ℝ) ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + ((p : ℝ))⁻¹) :=
    Finset.prod_nonneg fun p _ => add_nonneg zero_le_one (inv_nonneg.2 (Nat.cast_nonneg p))
  -- `∑_{p ≤ y}(log p)/p ≤ log y + log 4 + 4`: Mertens' first theorem
  have hlogdiv : ∑ p ∈ Nat.primesBelow (y + 1), Real.log p * ((p : ℝ))⁻¹
      ≤ Real.log y + Real.log 4 + 4 := by
    have hsub : Nat.primesBelow (y + 1) ⊆ {p ∈ Finset.Ioc 0 ⌊(y : ℝ)⌋₊ | p.Prime} := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      rw [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
      exact ⟨⟨hp.2.pos, Nat.lt_succ_iff.1 hp.1⟩, hp.2⟩
    have h : ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p ≤ Real.log y + Real.log 4 + 4 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => log_div_natCast_nonneg p)
        (sum_log_div_prime_le (by linarith))
    simpa only [div_eq_mul_inv] using h
  -- the summand, transported to the powerset of the primes below `y`
  have hterm : ∀ t ∈ (Nat.primesBelow (y + 1)).powerset,
      (1 + Real.log ((∏ p ∈ t, p : ℕ) : ℝ)) / ((∏ p ∈ t, p : ℕ) : ℝ)
        = (∏ p ∈ t, ((p : ℝ))⁻¹) + (∑ p ∈ t, Real.log p) * ∏ p ∈ t, ((p : ℝ))⁻¹ := by
    intro t ht
    have hne : ∀ p ∈ t, ((p : ℝ)) ≠ 0 := fun p hp =>
      Nat.cast_ne_zero.2 (Nat.prime_of_mem_primesBelow (Finset.mem_powerset.1 ht hp)).ne_zero
    rw [Nat.cast_prod, Real.log_prod hne, Finset.prod_inv_distrib, add_div, one_div,
      div_eq_mul_inv]
  have hstep : ∑ m ∈ {m ∈ Finset.Icc 1 (primorial y)
        | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (1 + Real.log m) / m
      = ∑ t ∈ (Nat.primesBelow (y + 1)).powerset,
          ((∏ p ∈ t, ((p : ℝ))⁻¹) + (∑ p ∈ t, Real.log p) * ∏ p ∈ t, ((p : ℝ))⁻¹) :=
    (sum_smoothSquarefree_eq_sum_powerset y _).trans (Finset.sum_congr rfl hterm)
  have hwt := sum_powerset_sum_mul_prod_le (a := fun p : ℕ => Real.log p)
    (b := fun p : ℕ => ((p : ℝ))⁻¹) (fun p => Real.log_natCast_nonneg p)
    (fun p => inv_nonneg.2 (Nat.cast_nonneg p)) (Nat.primesBelow (y + 1))
  have hGeq : ∑ t ∈ (Nat.primesBelow (y + 1)).powerset, ∏ p ∈ t, ((p : ℝ))⁻¹
      = ∏ p ∈ Nat.primesBelow (y + 1), (1 + ((p : ℝ))⁻¹) := (Finset.prod_one_add _).symm
  rw [hstep, Finset.sum_add_distrib, hGeq]
  calc ∏ p ∈ Nat.primesBelow (y + 1), (1 + ((p : ℝ))⁻¹)
        + ∑ t ∈ (Nat.primesBelow (y + 1)).powerset,
            (∑ p ∈ t, Real.log p) * ∏ p ∈ t, ((p : ℝ))⁻¹
      ≤ (1 + ∑ p ∈ Nat.primesBelow (y + 1), Real.log p * ((p : ℝ))⁻¹)
          * ∏ p ∈ Nat.primesBelow (y + 1), (1 + ((p : ℝ))⁻¹) := by linarith only [hwt]
    _ ≤ (1 + (Real.log y + Real.log 4 + 4)) * (Real.exp C₁ * Real.log y) :=
        mul_le_mul (by linarith only [hlogdiv]) hprodle hGnn (by linarith only [hL, hlog4])
    _ ≤ Real.exp C₁ * (1 + (5 + Real.log 4) / Real.log 2) * (Real.log y) ^ 2 := by
        have hK : (0 : ℝ) ≤ 5 + Real.log 4 := by linarith
        have h1 : (5 + Real.log 4) * Real.log y * Real.log 2
            ≤ (5 + Real.log 4) * Real.log y * Real.log y :=
          mul_le_mul_of_nonneg_left hL2 (mul_nonneg hK hL.le)
        have h2 : (5 + Real.log 4) * Real.log y
            ≤ (5 + Real.log 4) / Real.log 2 * (Real.log y) ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          linarith only [h1]
        linarith only [mul_le_mul_of_nonneg_left h2 (Real.exp_pos C₁).le]

end RMF
