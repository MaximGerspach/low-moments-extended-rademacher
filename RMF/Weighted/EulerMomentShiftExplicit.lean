/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.LogPrimeSum
import RMF.Weighted.EulerMomentHalfExplicit

/-!
# The Euler product moment below the critical exponent, at a shifted abscissa

`RMF.integral_rpow_setIntegral_normSq_split_le` peels a block off with the factor
`E‖F_z(½+σ)‖^{2q}`, and what makes the sum over blocks converge is that this is
`≍ (log z)^{q(2q-1)} = T^{q(1-2q)}`.  This file proves that bound at `½+σ`.

**The shift is not free, and not by monotonicity.**  For `q ≤ ½` the local factor
`u ↦ ((1+u)^{2q}+(1-u)^{2q})/2` is *decreasing*, so moving the abscissa right — which shrinks
every `u_p = p^{-½-σ}` — makes each factor **larger**.  The `σ = 0` bound is therefore a lower
bound for the shifted moment, not an upper one.

## The local bounds at a shift

The two local bounds `RMF.rademacher_local_le_one` and `RMF.rademacher_local_fine` hold for an
arbitrary `t` in `[0,1]` and in `[0,½]` respectively, and
`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_rpow_of_pos` factorises the moment at an
arbitrary `s` with `Re s > 0`.  At the shift the prime-level lemmas
read `t = p^{-(½+σ)}` and the product bound reads `∑ p^{-(1+2σ)}`, dominated by `∑ 1/p` wherever
the error terms are summed, so the two numeric certificates (`∑_{p<31}1/p ≤ 77/50`,
`∑_{p≥31}p^{-2} ≤ 1/30`) are those of `σ = 0`.

The chord and fine bounds are also stated at **any** real `σ`, through the bound on `t` they need
(`RMF.integral_norm_one_add_prime_shift_le_chord_of_rpow_le_one`,
`RMF.integral_norm_one_add_prime_shift_le_fine_of_rpow_le_half`), for the shifts to the left
that `Weighted/EulerMomentBand.lean` takes; the `σ ≥ 0` versions here are their instances.

## Mertens from below, shifted

`∑_{p ≤ y} p^{-(1+2σ)} ≥ log log y - 49` for `σ·log y ≤ 1`, from `e^{-u} ≥ 1-u` applied per
prime:

`p^{-(1+2σ)} = p^{-1}e^{-2σ log p} ≥ 1/p - 2σ(log p)/p`,

so the loss is `2σ∑_{p≤y}(log p)/p ≤ 2σ(log y + log 4 + 4)`, bounded by Mertens' *first* theorem
(`RMF.sum_log_div_prime_le`) and `σ log y ≤ 1`.  It is a constant, which is all that is needed:
the coefficient `q(2q-1)` is bounded, so a constant in the exponent is a constant factor.
-/

open MeasureTheory

namespace RMF

/-! ### The abscissa as a real number -/

/-- `p^{-c}` at a real abscissa is a real number, which is what the two-point integral needs. -/
lemma cpow_neg_ofReal_eq (p : ℕ) (c : ℝ) :
    ((p : ℂ) ^ (-((c : ℝ) : ℂ))) = (((p : ℝ) ^ (-c) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  norm_num

/-- `(p^{-(½+σ)})² = p^{-(1+2σ)}`. -/
lemma rpow_neg_shift_sq (p : ℕ) (σ : ℝ) :
    ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 2 = (p : ℝ) ^ (-(1 + 2 * σ)) := by
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) 2,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  congr 1
  push_cast
  ring

/-- Shifting right only shrinks the prime weight: `p^{-(1+2σ)} ≤ 1/p`. -/
lemma rpow_neg_shift_le_inv {p : ℕ} (hp : 1 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) :
    (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ((p : ℝ))⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith : -(1 + 2 * σ) ≤ (-1 : ℝ))
  rwa [Real.rpow_neg_one] at h

/-- And `p^{-(½+σ)} ≤ p^{-1/2}`, which is what the two `t`-ranges are read through. -/
lemma rpow_neg_shift_le_half_pow {p : ℕ} (hp : 1 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) :
    (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-! ### The two local bounds at a shifted abscissa -/

/-- **The chord bound wherever it applies**: `E‖1 + X p^{-(½+σ)}‖^{2q} ≤ 1 + (2q-1)p^{-(1+2σ)}` for
`½ ≤ q ≤ 1`, at any real `σ` with `p^{-(½+σ)} ≤ 1`.

No sign on `σ`: the chord reads only `t ≤ 1` at `t = p^{-(½+σ)}`, which a shift to the left keeps
as long as `½ + σ ≥ 0`.  The left shifts are what the band moments of
`Weighted/EulerMomentBand.lean` need. -/
theorem integral_norm_one_add_prime_shift_le_chord_of_rpow_le_one {p : ℕ} {σ q : ℝ}
    (ht1 : (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ 1) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ 1 + (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ))) := by
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hkey := integral_norm_one_add_mul_rpow_rademacherLaw_le ht0 ht1 hq0 hq1
  rw [rpow_neg_shift_sq p σ] at hkey
  rwa [cpow_neg_ofReal_eq p (1 / 2 + σ)]

/-- **The fine bound wherever it applies**: `E‖1 + X p^{-(½+σ)}‖^{2q} ≤
exp(q(2q-1)p^{-(1+2σ)} + 10p^{-2(1+2σ)})` for `0 ≤ q ≤ 1`, at any real `σ` with
`p^{-(½+σ)} ≤ ½`. -/
theorem integral_norm_one_add_prime_shift_le_fine_of_rpow_le_half {p : ℕ} {σ q : ℝ}
    (ht1 : (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
          + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2) := by
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hkey := rademacher_local_fine ht0 ht1 hq0 hq1
  rw [show ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 4
      = (((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 2) ^ 2 from by ring,
    rpow_neg_shift_sq p σ] at hkey
  rw [cpow_neg_ofReal_eq p (1 / 2 + σ),
    integral_norm_one_add_mul_rpow_rademacherLaw_real ht0 (le_trans ht1 (by norm_num))]
  exact hkey

/-- **The local moment is at most `1` at a shifted abscissa**: `E‖1 + X p^{-(½+σ)}‖^{2q} ≤ 1` for
`σ ≥ 0` and `0 ≤ q ≤ ½` (`RMF.rademacher_local_le_one`). -/
theorem integral_norm_one_add_prime_shift_le_one {p : ℕ} (hp : p.Prime) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hhalf : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 := by
    have hsq := rpow_neg_half_sq hp.pos
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      simpa using h
    nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ)) (-(1 / 2) : ℝ)]
  have ht1 : (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ 1 :=
    le_trans (rpow_neg_shift_le_half_pow hp.one_lt.le hσ) hhalf
  rw [cpow_neg_ofReal_eq p (1 / 2 + σ),
    integral_norm_one_add_mul_rpow_rademacherLaw_real ht0 ht1]
  exact rademacher_local_le_one ht0 ht1 hq0 hq1

/-- **The fine bound at a shifted abscissa**, `RMF.integral_norm_one_add_prime_le_fine` with the
abscissa freed.  The coefficient is `p^{-(1+2σ)}`, exactly `t²`.  The case `σ ≥ 0`, `p ≥ 5` of
`RMF.integral_norm_one_add_prime_shift_le_fine_of_rpow_le_half`. -/
theorem integral_norm_one_add_prime_shift_le_fine {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
          + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2) := by
  have hp5R : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hhalf : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 / 2 := by
    have hsq := rpow_neg_half_sq hp.pos
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 4 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
        (by linarith : (4 : ℝ) ≤ (p : ℝ))
      simpa using h
    nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ)) (-(1 / 2) : ℝ)]
  exact integral_norm_one_add_prime_shift_le_fine_of_rpow_le_half
    (le_trans (rpow_neg_shift_le_half_pow (by omega) hσ) hhalf) hq0 hq1

/-! ### The product, at a shifted abscissa

The two numeric certificates are the `σ = 0` ones: every term `p^{-(1+2σ)}` is dominated by
`1/p`, so `∑_{p<31}` and `∑_{p≥31}(·)²` are bounded by the same numbers. -/

/-- **The local product below the critical exponent, at a shifted abscissa.**

`∏_{p<y} E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)·∑_{p<y}p^{-(1+2σ)} + 3/5)` for `0 ≤ q ≤ ½`. -/
theorem prod_integral_norm_one_add_prime_shift_le_of_le_half {σ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (y : ℕ) :
    (∏ p ∈ Nat.primesBelow y,
        ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ)))
          + 3 / 5) := by
  classical
  have hnn : ∀ p ∈ Nat.primesBelow y,
      (0 : ℝ) ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw :=
    fun p _ => integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hbound : ∀ p ∈ Nat.primesBelow y,
      (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
        ≤ Real.exp (if p < 31 then 0
            else q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
              + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    by_cases h5 : p < 31
    · rw [if_pos h5, Real.exp_zero]
      exact integral_norm_one_add_prime_shift_le_one hprime hσ hq0 hq1
    · rw [if_neg h5]
      exact integral_norm_one_add_prime_shift_le_fine hprime (by omega) hσ hq0 (by linarith)
  refine le_trans (Finset.prod_le_prod hnn hbound) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_ite, Finset.sum_const_zero]
  have hsplit : ∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ))
      = (∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)))
        + ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlarge : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
        (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
          + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)
      = q * (2 * q - 1)
          * (∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (p : ℝ) ^ (-(1 + 2 * σ)))
        + 10 * ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
            ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hdom : ∀ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ((p : ℝ))⁻¹ := fun p hp =>
    rpow_neg_shift_le_inv (Nat.prime_of_mem_primesBelow hp).one_lt.le hσ
  have hsub1 : (Nat.primesBelow y).filter (fun p => p < 31)
      ⊆ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp.1
    have h31 : p < 31 := hp.2
    revert hprime
    interval_cases p <;> decide
  have hS1nn : (0 : ℝ)
      ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  have hS1 : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ 77 / 50 := by
    have hstep : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ))
        ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), ((p : ℝ))⁻¹ :=
      Finset.sum_le_sum fun p hp => hdom p (Finset.mem_filter.1 hp).1
    refine le_trans hstep ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun i _ _ => by positivity) ?_
    norm_num
  have hsub2 : (Nat.primesBelow y).filter (fun p => ¬ p < 31) ⊆ Finset.Ico 31 y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_Ico]
    exact ⟨by omega, (Nat.mem_primesBelow.1 hp.1).1⟩
  have hS2 : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
      ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ 1 / 30 := by
    have hstep : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
          ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2
        ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2 := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h1 := hdom p (Finset.mem_filter.1 hp).1
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg (by positivity) _
      nlinarith
    refine le_trans hstep ?_
    calc ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2
        = ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2 :=
          Finset.sum_congr rfl fun p _ => by rw [inv_pow, one_div]
      _ ≤ ∑ n ∈ Finset.Ico 31 y, (1 : ℝ) / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i _ _ => by positivity
      _ ≤ 1 / (((31 : ℕ) : ℝ) - 1) := sum_inv_sq_Ico_le (by norm_num) y
      _ = 1 / 30 := by norm_num
  have hcoef : q * (1 - 2 * q) ≤ 1 / 8 := by nlinarith [sq_nonneg (4 * q - 1)]
  have hcoef0 : (0 : ℝ) ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  rw [hlarge, hsplit]
  nlinarith [hS1, hS1nn, hS2, hcoef, hcoef0,
    mul_le_mul_of_nonneg_right hcoef hS1nn, mul_le_mul_of_nonneg_left hS1 hcoef0]

/-- **The Rademacher Euler-product moment at a shifted real abscissa, below the critical
exponent.** -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_of_le_half
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (y : ℕ) :
    (∫ ω, ‖randomEulerProduct f y (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ)))
          + 3 / 5) := by
  rw [hf.integral_norm_randomEulerProduct_rpow_of_pos y
    (by rw [Complex.ofReal_re]; linarith) (2 * q)]
  exact prod_integral_norm_one_add_prime_shift_le_of_le_half hσ hq0 hq1 y

/-! ### Mertens from below, shifted -/

/-- Mertens' first theorem over `RMF`'s own index set. -/
lemma sum_log_div_primesBelow_le {y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p ≤ Real.log y + Real.log 4 + 4 := by
  classical
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have h := sum_log_div_prime_le hy1
  rw [Nat.floor_natCast] at h
  have hset : Finset.filter (fun p => Nat.Prime p) (Finset.Ioc 0 y) = Nat.primesBelow (y + 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesBelow]
    exact ⟨fun hp => ⟨by omega, hp.2⟩, fun hp => ⟨⟨hp.2.pos, by omega⟩, hp.2⟩⟩
  rwa [hset] at h

/-- **Mertens' second theorem from below, at a shifted abscissa.**

`∑_{p ≤ y} p^{-(1+2σ)} ≥ log log y - 49`, for `σ ≥ 0` with `σ·log y ≤ 1` and `y ≥ 2`.

`e^{-u} ≥ 1 - u` per prime turns the shift into `2σ·∑(log p)/p`, which Mertens' *first* theorem
caps at `2σ(log y + log 4 + 4)`; `σ log y ≤ 1` and `σ ≤ 1/log 2` make that a constant. -/
theorem log_log_sub_le_sum_primesBelow_rpow {y : ℕ} (hy : 2 ≤ y) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσy : σ * Real.log y ≤ 1) :
    Real.log (Real.log y) - 49 ≤ ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ)) := by
  classical
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy2
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hσle : σ ≤ 3 / 2 := by
    have h1 : σ * Real.log 2 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hlog2 hσ) hσy
    rcases le_total σ (3 / 2) with h | h
    · exact h
    · exfalso
      have h2 : (3 / 2 : ℝ) * Real.log 2 ≤ σ * Real.log 2 :=
        mul_le_mul_of_nonneg_right h hlog2pos.le
      linarith [Real.log_two_gt_d9]
  -- the per-prime comparison
  have hterm : ∀ p ∈ Nat.primesBelow (y + 1),
      ((p : ℝ))⁻¹ - 2 * σ * (Real.log p / p) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hfac : (p : ℝ) ^ (-(1 + 2 * σ)) = ((p : ℝ))⁻¹ * Real.exp (-(2 * σ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (inv_pos.2 hp0), ← Real.exp_add,
        Real.log_inv]
      congr 1
      ring
    have hexp : 1 - 2 * σ * Real.log p ≤ Real.exp (-(2 * σ * Real.log p)) := by
      linarith [Real.add_one_le_exp (-(2 * σ * Real.log p))]
    have hmul := mul_le_mul_of_nonneg_left hexp (inv_nonneg.2 hp0.le)
    rw [← hfac] at hmul
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  -- the two Mertens inputs
  have hlow := log_log_sub_le_sum_primesBelow_inv hy
  have hfirst := sum_log_div_primesBelow_le (by omega : 1 ≤ y)
  have hlogsum0 : (0 : ℝ) ≤ ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hshift : (∑ p ∈ Nat.primesBelow (y + 1), 2 * σ * (Real.log p / p))
      ≤ 2 * σ * (Real.log y + Real.log 4 + 4) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hfirst (by linarith)
  have hlog4 : Real.log 4 ≤ 2 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h2]
    linarith [Real.log_two_lt_d9]
  have hbudget : 2 * σ * (Real.log y + Real.log 4 + 4) ≤ 20 := by nlinarith
  linarith

/-! ### The log form -/

/-- **The moment below the critical exponent, at a shifted abscissa, in the `log` form.**
`E‖F_{y+1}(½+σ)‖^{2q} ≤ e⁷·(log y)^{q(2q-1)}` for `0 ≤ q ≤ ½`, `y ≥ 2` and `σ ≥ 0` with
`σ·log y ≤ 1`: the input of the `j`-th mesoscopic block, at `z_j` with `T_j·log z_j ≍ 1`,
`E‖F_{z_j}(½+σ)‖^{2q} ≪ (log z_j)^{q(2q-1)} = T_j^{q(1-2q)}`.  As at `σ = 0`, the coefficient
`q(2q-1)` is negative, so the Mertens errors (`49/8` and `3/5`) can be given away, at the cost
`e⁷`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_of_le_half
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    {y : ℕ} (hy : 2 ≤ y) (hσy : σ * Real.log y ≤ 1) :
    (∫ ω, ‖randomEulerProduct f (y + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp 7 * (Real.log y) ^ (q * (2 * q - 1)) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hloc := hf.integral_norm_randomEulerProduct_shift_rpow_le_of_le_half hσ hq0 hq1 (y + 1)
  have hmert := log_log_sub_le_sum_primesBelow_rpow hy hσ hσy
  have hcneg : q * (2 * q - 1) ≤ 0 := by nlinarith
  have hcabs : -(q * (2 * q - 1)) ≤ 1 / 8 := by nlinarith [sq_nonneg (4 * q - 1)]
  have hstep : q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ)))
      ≤ q * (2 * q - 1) * (Real.log (Real.log y) - 49) :=
    mul_le_mul_of_nonpos_left hmert hcneg
  have hrpow : (Real.log y) ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log y)) := by
    rw [Real.rpow_def_of_pos hL0]
    ring_nf
  refine hloc.trans ?_
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [hstep, hcabs]

/-! ### Above the critical exponent, at a shifted abscissa

Everything above is the sign `q(2q-1) ≤ 0`.  For `½ ≤ q ≤ 1` three steps change:

* the **chord** `E‖1+Xt‖^{2q} ≤ 1 + (2q-1)t²`, true above `½` and false below it, replaces
  `RMF.integral_norm_one_add_prime_shift_le_one`; the **fine** bound
  `RMF.integral_norm_one_add_prime_shift_le_fine` is stated for `0 ≤ q ≤ 1`;
* the two numeric certificates are unchanged, every `p^{-(1+2σ)}` being at most `1/p`;
* **Mertens is read from above**: `∑ p^{-(1+2σ)} ≤ ∑ 1/p ≤ log log y + 1.42`
  (`RMF.sum_primesBelow_inv_le_log_log_add`) replaces `RMF.log_log_sub_le_sum_primesBelow_rpow`,
  the one place the route below `½` needs `σ·log y ≤ 1`, so here `σ ≥ 0` and `y ≥ 2` suffice.
-/

/-- **The chord bound at a shifted abscissa**, `RMF.integral_norm_one_add_prime_le_chord` with the
abscissa freed: `E‖1 + X p^{-(½+σ)}‖^{2q} ≤ 1 + (2q-1)p^{-(1+2σ)}` for `½ ≤ q ≤ 1`.  The case
`σ ≥ 0` of `RMF.integral_norm_one_add_prime_shift_le_chord_of_rpow_le_one`. -/
theorem integral_norm_one_add_prime_shift_le_chord {p : ℕ} (hp : p.Prime) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ 1 + (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ))) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hhalf : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 1 := by
    have hsq := rpow_neg_half_sq hp.pos
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      simpa using h
    nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ)) (-(1 / 2) : ℝ)]
  exact integral_norm_one_add_prime_shift_le_chord_of_rpow_le_one
    (le_trans (rpow_neg_shift_le_half_pow hp.one_lt.le hσ) hhalf) hq0 hq1

/-- **The local product above the critical exponent, at a shifted abscissa.**
`∏_{p<y} E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)·∑_{p<y}p^{-(1+2σ)} + 3/5)` for `½ ≤ q ≤ 1`.

`RMF.prod_integral_norm_one_add_prime_le` with the abscissa freed (`σ ≥ 0`), same split at `31`:
the fine bound above it, the chord below.  Both numeric certificates are the `σ = 0` ones, since
`p^{-(1+2σ)} ≤ 1/p`; the chord penalty is `(2q-1)(1-q)·∑_{p<31} ≤ ⅛·(77/50)` as there. -/
theorem prod_integral_norm_one_add_prime_shift_le {σ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (y : ℕ) :
    (∏ p ∈ Nat.primesBelow y,
        ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ)))
          + 3 / 5) := by
  classical
  have hnn : ∀ p ∈ Nat.primesBelow y,
      (0 : ℝ) ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw :=
    fun p _ => integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hbound : ∀ p ∈ Nat.primesBelow y,
      (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
        ≤ Real.exp (if p < 31 then (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
            else q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
              + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    by_cases h5 : p < 31
    · rw [if_pos h5]
      refine le_trans (integral_norm_one_add_prime_shift_le_chord hprime hσ hq0 hq1) ?_
      have := Real.add_one_le_exp ((2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ))))
      linarith
    · rw [if_neg h5]
      exact integral_norm_one_add_prime_shift_le_fine hprime (by omega) hσ (by linarith) hq1
  refine le_trans (Finset.prod_le_prod hnn hbound) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_ite]
  have hsplit : ∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ))
      = (∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)))
        + ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsmall : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31),
        (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
      = (2 * q - 1)
          * ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    (Finset.mul_sum _ _ _).symm
  have hlarge : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
        (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
          + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)
      = q * (2 * q - 1)
          * (∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (p : ℝ) ^ (-(1 + 2 * σ)))
        + 10 * ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
            ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hdom : ∀ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ((p : ℝ))⁻¹ := fun p hp =>
    rpow_neg_shift_le_inv (Nat.prime_of_mem_primesBelow hp).one_lt.le hσ
  have hsub1 : (Nat.primesBelow y).filter (fun p => p < 31)
      ⊆ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp.1
    have h31 : p < 31 := hp.2
    revert hprime
    interval_cases p <;> decide
  have hS1nn : (0 : ℝ)
      ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  have hS1 : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ 77 / 50 := by
    have hstep : ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ))
        ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => p < 31), ((p : ℝ))⁻¹ :=
      Finset.sum_le_sum fun p hp => hdom p (Finset.mem_filter.1 hp).1
    refine le_trans hstep ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun i _ _ => by positivity) ?_
    norm_num
  have hsub2 : (Nat.primesBelow y).filter (fun p => ¬ p < 31) ⊆ Finset.Ico 31 y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_Ico]
    exact ⟨by omega, (Nat.mem_primesBelow.1 hp.1).1⟩
  have hS2 : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
      ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ 1 / 30 := by
    have hstep : ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31),
          ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2
        ≤ ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2 := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h1 := hdom p (Finset.mem_filter.1 hp).1
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg (by positivity) _
      nlinarith
    refine le_trans hstep ?_
    calc ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (((p : ℝ))⁻¹) ^ 2
        = ∑ p ∈ (Nat.primesBelow y).filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2 :=
          Finset.sum_congr rfl fun p _ => by rw [inv_pow, one_div]
      _ ≤ ∑ n ∈ Finset.Ico 31 y, (1 : ℝ) / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i _ _ => by positivity
      _ ≤ 1 / (((31 : ℕ) : ℝ) - 1) := sum_inv_sq_Ico_le (by norm_num) y
      _ = 1 / 30 := by norm_num
  have hcoef : (2 * q - 1) * (1 - q) ≤ 1 / 8 := by nlinarith [sq_nonneg (4 * q - 3)]
  have hcoef0 : (0 : ℝ) ≤ (2 * q - 1) * (1 - q) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hsmall, hlarge, hsplit]
  nlinarith [hS1, hS1nn, hS2, hcoef, hcoef0,
    mul_le_mul_of_nonneg_right hcoef hS1nn, mul_le_mul_of_nonneg_left hS1 hcoef0]

/-- **The Rademacher Euler-product moment at a shifted real abscissa, above the critical
exponent.**

`E‖F_y(½+σ)‖^{2q} ≤ exp(q(2q-1)·∑_{p<y}p^{-(1+2σ)} + 3/5)`  for `½ ≤ q ≤ 1`, `σ ≥ 0`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (y : ℕ) :
    (∫ ω, ‖randomEulerProduct f y (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-(1 + 2 * σ)))
          + 3 / 5) := by
  rw [hf.integral_norm_randomEulerProduct_rpow_of_pos y
    (by rw [Complex.ofReal_re]; linarith) (2 * q)]
  exact prod_integral_norm_one_add_prime_shift_le hσ hq0 hq1 y

/-- **The moment above the critical exponent, at a shifted abscissa, in the `log` form.**
`E‖F_{y+1}(½+σ)‖^{2q} ≤ e^{101/50}·(log y)^{q(2q-1)}` for `½ ≤ q ≤ 1`, `σ ≥ 0`, `y ≥ 2`: the input
of the `j`-th mesoscopic block for `q > ½`, `E‖F_{z_j}(½+σ)‖^{2q} ≪ (log z_j)^{q(2q-1)}`, which
`RMF.log_mesoW_rpow_le_above` turns into `e^{(J-j)q(2q-1)}`.  No bound on `σ`: Mertens is read
from above, where shifting right only helps.  The constant is `1.42·q(2q-1) + 3/5 ≤ 2.02`, the
`1.42` being `RMF.sum_primesBelow_inv_le_log_log_add`'s. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    {y : ℕ} (hy : 2 ≤ y) :
    (∫ ω, ‖randomEulerProduct f (y + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp (101 / 50) * (Real.log y) ^ (q * (2 * q - 1)) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hL0 : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hloc := hf.integral_norm_randomEulerProduct_shift_rpow_le hσ hq0 hq1 (y + 1)
  have hdom : ∀ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ((p : ℝ))⁻¹ := fun p hp =>
    rpow_neg_shift_le_inv (Nat.prime_of_mem_primesBelow hp).one_lt.le hσ
  have hmert : ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ Real.log (Real.log y) + 1.42 :=
    le_trans (Finset.sum_le_sum hdom) (sum_primesBelow_inv_le_log_log_add hy)
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hγ1 : q * (2 * q - 1) ≤ 1 := by nlinarith
  have hstep : q * (2 * q - 1) * (∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ) ^ (-(1 + 2 * σ)))
      ≤ q * (2 * q - 1) * Real.log (Real.log y) + 1.42 * (q * (2 * q - 1)) := by
    have h := mul_le_mul_of_nonneg_left hmert hγ0
    nlinarith [h]
  have h142 : 1.42 * (q * (2 * q - 1)) ≤ 1.42 := by nlinarith
  have hrpow : (Real.log y) ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log y)) := by
    rw [Real.rpow_def_of_pos hL0]
    ring_nf
  refine hloc.trans ?_
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith [hstep, h142]

end RMF
