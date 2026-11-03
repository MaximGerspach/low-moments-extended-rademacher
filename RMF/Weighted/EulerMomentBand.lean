/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.Block
import RMF.Weighted.EulerMomentShiftExplicit

/-!
# The Euler product moment of a band of primes, at a shift inside its own scale

A band's central window (`RMF.integral_rpow_centralWindow_primesIco_le`) needs, for the product
`F_{y,z}` over the primes `y < p ≤ z` and `c = 1/(2 log z)`,

`E|F_{y,z}(½ - c)|^{2q} ≪ κ^{q(2q-1)}`,  `κ = log z/log y`,

uniformly in `½ ≤ q ≤ 1`.  This file proves it for `z ≥ 3` and every shift `σ` of either sign
with `2|σ|·log z ≤ 1`, `σ = -c` being the extreme case, and the same for the bottom band `y = 1`
with `κ = log z`:

* `RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_signed_shift_rpow_le_log_div`, a band
  with `2 ≤ y ≤ z`: `≤ e^{48}·(log z/log y)^{q(2q-1)}`;
* `RMF.IsRademacherRMF.integral_norm_randomEulerProduct_signed_shift_rpow_le_log`, the bottom band
  `y = 1`: `≤ e^{21}·(log z)^{q(2q-1)}`.

## The route

As for the full product at a right shift (`Weighted/EulerMomentShiftExplicit.lean`): the moment
factors over the primes, the chord bounds the primes below `31` and the fine bound the rest, and
Mertens is read from above.  Two things change to the left of `½`.

**The local bounds need their `t`.**  For `σ < 0`, `t = p^{-(½+σ)}` exceeds `p^{-1/2}`.  But
`2|σ| log p ≤ 1` gives `t² = p^{-(1+2σ)} ≤ e/p` (`RMF.rpow_neg_shift_le_exp_one_mul_inv`), so
`t ≤ ½` from `p = 31` on, and the two certificates survive with factors `e` and `e²`.  The chord
needs `t ≤ 1`, i.e. `½ + σ ≥ 0`, which `2|σ| log z ≤ 1` gives once `z ≥ 3`.  That is the only
reason for the hypothesis `3 ≤ z`, and it bites only at `p = 2`.

**Mertens has to be read additively.**  The block estimate with the tilt carried through,
`RMF.sum_prime_Ioc_rpow_bounds_of_le`, is two-sided but *multiplicative*, `e^{±2η}·∑ 1/p`; here it
would put `e·log κ` in the exponent and prove only `κ^{e·q(2q-1)}`.  What is true is additive:
`p^{-(1+2σ)} ≤ 1/p + (e-1)·2|σ|·(log p)/p`, from `e^u ≤ 1 + (e-1)u` on `[0, 1]`
(`RMF.rpow_neg_shift_le_inv_add_mul_log_div`), and Mertens' *first* theorem caps the summed error
at `(e-1)·2|σ|·(log z + log 4 + 4) ≤ 16` (`RMF.sum_prime_rpow_signed_shift_le_sum_inv_add`).  The
main term is then block Mertens, `∑_{y<p≤z} 1/p ≤ log κ + 20/log 2`
(`RMF.sum_prime_Ioc_inv_le_of_log_le`), or at the bottom `∑_{p≤z} 1/p ≤ log log z + 1.42`
(`RMF.sum_primesBelow_inv_le_log_log_add`).

Only the upper bound is proved.
-/

open MeasureTheory

namespace RMF

/-! ### The weight at a shift -/

/-- **A shift inside the scale costs at most `e` per prime**: `p^{-(1+2σ)} ≤ e/p` whenever
`2|σ| log p ≤ 1`. -/
lemma rpow_neg_shift_le_exp_one_mul_inv {p : ℕ} (hp : 1 ≤ p) {σ : ℝ}
    (hσp : 2 * |σ| * Real.log p ≤ 1) :
    (p : ℝ) ^ (-(1 + 2 * σ)) ≤ Real.exp 1 * ((p : ℝ))⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hfac : (p : ℝ) ^ (-(1 + 2 * σ)) = Real.exp (-(2 * σ * Real.log p)) * ((p : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (inv_pos.2 hp0), ← Real.exp_add, Real.log_inv]
    congr 1
    ring
  have hle : -(2 * σ * Real.log p) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le σ)
      (by positivity : (0 : ℝ) ≤ 2 * Real.log p)
    linarith
  rw [hfac]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (inv_nonneg.2 hp0.le)

/-- **The same shift, additively**: `p^{-(1+2σ)} ≤ 1/p + (e-1)·2|σ|·(log p)/p` whenever
`2|σ| log p ≤ 1`.  `e^u ≤ 1 + (e-1)u` on `[0, 1]` is the convexity of `exp`. -/
lemma rpow_neg_shift_le_inv_add_mul_log_div {p : ℕ} (hp : 1 ≤ p) {σ : ℝ}
    (hσp : 2 * |σ| * Real.log p ≤ 1) :
    (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ ((p : ℝ))⁻¹ + (Real.exp 1 - 1) * (2 * |σ|) * (Real.log p / p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hfac : (p : ℝ) ^ (-(1 + 2 * σ)) = Real.exp (-(2 * σ * Real.log p)) * ((p : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (inv_pos.2 hp0), ← Real.exp_add, Real.log_inv]
    congr 1
    ring
  have hv0 : (0 : ℝ) ≤ 2 * |σ| * Real.log p := by positivity
  have hle : -(2 * σ * Real.log p) ≤ 2 * |σ| * Real.log p := by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le σ)
      (by positivity : (0 : ℝ) ≤ 2 * Real.log p)
    linarith
  -- the chord of `exp` over `[0, 1]`
  have hconv : Real.exp (2 * |σ| * Real.log p)
      ≤ 1 + (Real.exp 1 - 1) * (2 * |σ| * Real.log p) := by
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
      (by linarith : (0 : ℝ) ≤ 1 - 2 * |σ| * Real.log p) hv0 (by ring)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
    linarith
  rw [hfac]
  calc Real.exp (-(2 * σ * Real.log p)) * ((p : ℝ))⁻¹
      ≤ (1 + (Real.exp 1 - 1) * (2 * |σ| * Real.log p)) * ((p : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right ((Real.exp_le_exp.2 hle).trans hconv) (inv_nonneg.2 hp0.le)
    _ = ((p : ℝ))⁻¹ + (Real.exp 1 - 1) * (2 * |σ|) * (Real.log p / p) := by
        rw [div_eq_mul_inv]
        ring

/-! ### The local product at a shift of either sign -/

/-- **The local product above the critical exponent, at a shift of either sign.**  For a finite
set `S` of primes with `2|σ| log p ≤ 1` on `S`, `σ ≥ -½` and `½ ≤ q ≤ 1`,
`∏_{p∈S} E‖1 + X p^{-(½+σ)}‖^{2q} ≤ exp(q(2q-1)·∑_{p∈S} p^{-(1+2σ)} + 3)`.  As
`RMF.prod_integral_norm_one_add_prime_shift_le`, split at `31`, each certificate paying the factor
`p^{-2σ} ≤ e` of `RMF.rpow_neg_shift_le_exp_one_mul_inv`: the chord penalty is `⅛·e·77/50 ≤ 0.524`
and the fine error `10·e²/30 ≤ 2.47`. -/
theorem prod_integral_norm_one_add_prime_signed_shift_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {σ q : ℝ} (hσh : -(1 / 2) ≤ σ) (hσS : ∀ p ∈ S, 2 * |σ| * Real.log p ≤ 1)
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∏ p ∈ S, ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
      ≤ Real.exp (q * (2 * q - 1) * (∑ p ∈ S, (p : ℝ) ^ (-(1 + 2 * σ))) + 3) := by
  classical
  have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have hnn : ∀ p ∈ S,
      (0 : ℝ) ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw :=
    fun p _ => integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hwe : ∀ p ∈ S, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ Real.exp 1 * ((p : ℝ))⁻¹ :=
    fun p hp => rpow_neg_shift_le_exp_one_mul_inv (hS p hp).one_lt.le (hσS p hp)
  have hbound : ∀ p ∈ S,
      (∫ z, ‖1 + z * (p : ℂ) ^ (-(((1 / 2 + σ : ℝ)) : ℂ))‖ ^ (2 * q) ∂rademacherLaw)
        ≤ Real.exp (if p < 31 then (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
            else q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
              + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2) := by
    intro p hp
    have hprime : p.Prime := hS p hp
    by_cases h31 : p < 31
    · rw [if_pos h31]
      -- `½ + σ ≥ 0` is `t ≤ 1`
      have ht1 : (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hprime.one_lt.le) (by linarith)
      refine le_trans (integral_norm_one_add_prime_shift_le_chord_of_rpow_le_one ht1 hq0 hq1) ?_
      have := Real.add_one_le_exp ((2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ))))
      linarith
    · rw [if_neg h31]
      -- `t² ≤ e/p ≤ e/31 ≤ ¼` is `t ≤ ½`
      have hp31 : (31 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (not_lt.1 h31)
      have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
      have hinv : ((p : ℝ))⁻¹ ≤ 1 / 31 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hp31
      have hsq : ((p : ℝ) ^ (-(1 / 2 + σ) : ℝ)) ^ 2 ≤ 1 / 4 := by
        rw [rpow_neg_shift_sq p σ]
        calc (p : ℝ) ^ (-(1 + 2 * σ)) ≤ Real.exp 1 * ((p : ℝ))⁻¹ := hwe p hp
          _ ≤ 2.72 * (1 / 31) := mul_le_mul he hinv (inv_nonneg.2 (by positivity)) (by norm_num)
          _ ≤ 1 / 4 := by norm_num
      have ht1 : (p : ℝ) ^ (-(1 / 2 + σ) : ℝ) ≤ 1 / 2 := by nlinarith
      exact integral_norm_one_add_prime_shift_le_fine_of_rpow_le_half ht1 (by linarith) hq1
  refine le_trans (Finset.prod_le_prod hnn hbound) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_ite]
  have hsplit : ∑ p ∈ S, (p : ℝ) ^ (-(1 + 2 * σ))
      = (∑ p ∈ S.filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)))
        + ∑ p ∈ S.filter (fun p => ¬ p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsmall : ∑ p ∈ S.filter (fun p => p < 31), (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
      = (2 * q - 1) * ∑ p ∈ S.filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    (Finset.mul_sum _ _ _).symm
  have hlarge : ∑ p ∈ S.filter (fun p => ¬ p < 31),
        (q * (2 * q - 1) * ((p : ℝ) ^ (-(1 + 2 * σ)))
          + 10 * ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2)
      = q * (2 * q - 1)
          * (∑ p ∈ S.filter (fun p => ¬ p < 31), (p : ℝ) ^ (-(1 + 2 * σ)))
        + 10 * ∑ p ∈ S.filter (fun p => ¬ p < 31), ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsub1 : S.filter (fun p => p < 31)
      ⊆ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hprime : p.Prime := hS p hp.1
    have h31 : p < 31 := hp.2
    revert hprime
    interval_cases p <;> decide
  have hS1nn : (0 : ℝ) ≤ ∑ p ∈ S.filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  have hS1 : ∑ p ∈ S.filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ)) ≤ 419 / 100 := by
    have hstep : ∑ p ∈ S.filter (fun p => p < 31), (p : ℝ) ^ (-(1 + 2 * σ))
        ≤ Real.exp 1 * ∑ p ∈ S.filter (fun p => p < 31), ((p : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p hp => hwe p (Finset.mem_filter.1 hp).1
    have hcert : ∑ p ∈ S.filter (fun p => p < 31), ((p : ℝ))⁻¹ ≤ 77 / 50 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun i _ _ => by positivity) ?_
      norm_num
    have hcert0 : (0 : ℝ) ≤ ∑ p ∈ S.filter (fun p => p < 31), ((p : ℝ))⁻¹ :=
      Finset.sum_nonneg fun i _ => by positivity
    calc _ ≤ Real.exp 1 * ∑ p ∈ S.filter (fun p => p < 31), ((p : ℝ))⁻¹ := hstep
      _ ≤ 2.72 * (77 / 50) := mul_le_mul he hcert hcert0 (by norm_num)
      _ ≤ 419 / 100 := by norm_num
  have hsub2 : S.filter (fun p => ¬ p < 31) ⊆ Finset.Ico 31 (S.sup id + 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_Ico]
    exact ⟨by omega, Nat.lt_succ_of_le (Finset.le_sup (f := id) hp.1)⟩
  have hS2 : ∑ p ∈ S.filter (fun p => ¬ p < 31), ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2
      ≤ 247 / 1000 := by
    have hstep : ∑ p ∈ S.filter (fun p => ¬ p < 31), ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2
        ≤ ∑ p ∈ S.filter (fun p => ¬ p < 31), Real.exp 1 ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h1 := hwe p (Finset.mem_filter.1 hp).1
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + 2 * σ)) := Real.rpow_nonneg (by positivity) _
      have hsq : ((p : ℝ) ^ (-(1 + 2 * σ))) ^ 2 ≤ (Real.exp 1 * ((p : ℝ))⁻¹) ^ 2 := by
        nlinarith
      rw [mul_pow, inv_pow, ← one_div] at hsq
      exact hsq
    have htail : ∑ p ∈ S.filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 30 := by
      calc ∑ p ∈ S.filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ n ∈ Finset.Ico 31 (S.sup id + 1), (1 : ℝ) / (n : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i _ _ => by positivity
        _ ≤ 1 / (((31 : ℕ) : ℝ) - 1) := sum_inv_sq_Ico_le (by norm_num) _
        _ = 1 / 30 := by norm_num
    have htail0 : (0 : ℝ) ≤ ∑ p ∈ S.filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    have he2 : Real.exp 1 ^ 2 ≤ 7.3984 := by
      calc Real.exp 1 ^ 2 ≤ 2.72 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
        _ = 7.3984 := by norm_num
    rw [← Finset.mul_sum] at hstep
    calc _ ≤ Real.exp 1 ^ 2 * ∑ p ∈ S.filter (fun p => ¬ p < 31), (1 : ℝ) / (p : ℝ) ^ 2 := hstep
      _ ≤ 7.3984 * (1 / 30) := mul_le_mul he2 htail htail0 (by norm_num)
      _ ≤ 247 / 1000 := by norm_num
  have hcoef : (2 * q - 1) * (1 - q) ≤ 1 / 8 := by nlinarith [sq_nonneg (4 * q - 3)]
  have hcoef0 : (0 : ℝ) ≤ (2 * q - 1) * (1 - q) := mul_nonneg (by linarith) (by linarith)
  rw [hsmall, hlarge, hsplit]
  nlinarith [hS1, hS1nn, hS2, hcoef, hcoef0,
    mul_le_mul_of_nonneg_right hcoef hS1nn, mul_le_mul_of_nonneg_left hS1 hcoef0]

/-! ### Mertens at a shift, additively -/

/-- The arithmetic of `RMF.sum_prime_rpow_signed_shift_le_sum_inv_add`:
`(e-1)·A·(L + log 4 + 4) ≤ 16` for `A ≥ 0`, `A·L ≤ 1` and `L ≥ log 2`. -/
lemma signed_shift_budget_le {A L : ℝ} (hA : 0 ≤ A) (hAL : A * L ≤ 1) (hL : Real.log 2 ≤ L) :
    (Real.exp 1 - 1) * A * (L + Real.log 4 + 4) ≤ 16 := by
  have hl2 := Real.log_two_gt_d9
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  -- `A·log 2 ≤ A·L ≤ 1`, so `A ≤ 1/log 2 ≤ 1.4428`
  have hA2 : A * Real.log 2 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hL hA) hAL
  have hAb : A ≤ 1.4428 := by
    have h1 : A ≤ 1 / Real.log 2 := by
      rw [le_div_iff₀ hpos]
      exact hA2
    have h2 : 1 / Real.log 2 ≤ 1.4428 := by
      rw [div_le_iff₀ hpos]
      linarith
    linarith
  have hsum : A * (L + Real.log 4 + 4) ≤ 8.7712 := by
    rw [hlog4]
    nlinarith
  have he : Real.exp 1 - 1 ≤ 1.7183 := by linarith [Real.exp_one_lt_d9]
  have hL0 : 0 ≤ L + Real.log 4 + 4 := by
    rw [hlog4]
    linarith
  calc (Real.exp 1 - 1) * A * (L + Real.log 4 + 4)
      = (Real.exp 1 - 1) * (A * (L + Real.log 4 + 4)) := by ring
    _ ≤ 1.7183 * 8.7712 := mul_le_mul he hsum (mul_nonneg hA hL0) (by norm_num)
    _ ≤ 16 := by norm_num

/-- **Mertens is moved only additively by a shift inside the scale.**  For a set `S` of primes
`p ≤ z`, `z ≥ 2` and `2|σ| log z ≤ 1`, `∑_{p∈S} p^{-(1+2σ)} ≤ ∑_{p∈S} 1/p + 16`.

Per prime `RMF.rpow_neg_shift_le_inv_add_mul_log_div`; summed, Mertens' first theorem
(`RMF.sum_log_div_prime_le`) caps the error at `(e-1)·2|σ|·(log z + log 4 + 4) ≤ 16`. -/
theorem sum_prime_rpow_signed_shift_le_sum_inv_add {S : Finset ℕ} {z : ℕ} (hz : 2 ≤ z)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ z) {σ : ℝ} (hσz : 2 * |σ| * Real.log z ≤ 1) :
    ∑ p ∈ S, (p : ℝ) ^ (-(1 + 2 * σ)) ≤ ∑ p ∈ S, ((p : ℝ))⁻¹ + 16 := by
  classical
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
  have hterm : ∀ p ∈ S, (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ ((p : ℝ))⁻¹ + (Real.exp 1 - 1) * (2 * |σ|) * (Real.log p / p) := by
    intro p hp
    obtain ⟨hprime, hpz⟩ := hS p hp
    have hlp : Real.log p ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpz)
    refine rpow_neg_shift_le_inv_add_mul_log_div hprime.one_lt.le ?_
    exact le_trans (mul_le_mul_of_nonneg_left hlp (by positivity)) hσz
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : ∑ p ∈ S, Real.log p / p ≤ Real.log z + Real.log 4 + 4 := by
    have h := sum_log_div_prime_le hz1
    rw [Nat.floor_natCast] at h
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by positivity) h
    intro p hp
    obtain ⟨hprime, hpz⟩ := hS p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hprime.pos, hpz⟩, hprime⟩
  have hbud := signed_shift_budget_le (A := 2 * |σ|) (L := Real.log z) (by positivity) hσz hlogz
  have hA0 : (0 : ℝ) ≤ (Real.exp 1 - 1) * (2 * |σ|) :=
    mul_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by positivity)
  have := mul_le_mul_of_nonneg_left hfirst hA0
  linarith

/-- **Mertens over a band, at a shift inside its scale.**  For `2 ≤ y ≤ z` and `2|σ| log z ≤ 1`,

`∑_{y<p≤z} p^{-(1+2σ)} ≤ log(log z/log y) + 45`.

Block Mertens (`RMF.sum_prime_Ioc_inv_le_of_log_le`, at `Λ = log z/log y`, error `20/log 2 ≤ 29`)
plus the additive shift, `16`. -/
theorem sum_primesIco_rpow_signed_shift_le_log_div_add {y z : ℕ} (hy : 2 ≤ y) (hyz : y ≤ z)
    {σ : ℝ} (hσz : 2 * |σ| * Real.log z ≤ 1) :
    ∑ p ∈ primesIco (y + 1) (z + 1), (p : ℝ) ^ (-(1 + 2 * σ))
      ≤ Real.log (Real.log z / Real.log y) + 45 := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hly : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hshift := sum_prime_rpow_signed_shift_le_sum_inv_add (S := primesIco (y + 1) (z + 1))
    (by omega : 2 ≤ z) (fun p hp => ⟨prime_of_mem_primesIco hp,
      by have := (mem_primesIco.1 hp).2.2; omega⟩) hσz
  have hmert := sum_prime_Ioc_inv_le_of_log_le hy hyz (Λ := Real.log z / Real.log y)
    ((one_le_div₀ hly).2 hlyz) (le_of_eq (div_mul_cancel₀ _ hly.ne').symm)
  rw [filter_prime_Ioc_eq_primesIco] at hmert
  have hinv : ∑ p ∈ primesIco (y + 1) (z + 1), ((p : ℝ))⁻¹
      = ∑ p ∈ primesIco (y + 1) (z + 1), (1 : ℝ) / p :=
    Finset.sum_congr rfl fun p _ => (one_div _).symm
  have h20 : 20 / Real.log 2 ≤ 29 := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  linarith

/-- **Mertens over the bottom band, at a shift inside its scale.**  For `z ≥ 2` and
`2|σ| log z ≤ 1`, `∑_{p≤z} p^{-(1+2σ)} ≤ log log z + 18`: the uniform one-sided Mertens
(`RMF.sum_primesBelow_inv_le_log_log_add`, `1.42`) plus the additive shift, `16`. -/
theorem sum_primesBelow_rpow_signed_shift_le_log_log_add {z : ℕ} (hz : 2 ≤ z) {σ : ℝ}
    (hσz : 2 * |σ| * Real.log z ≤ 1) :
    ∑ p ∈ Nat.primesBelow (z + 1), (p : ℝ) ^ (-(1 + 2 * σ)) ≤ Real.log (Real.log z) + 18 := by
  have hshift := sum_prime_rpow_signed_shift_le_sum_inv_add (S := Nat.primesBelow (z + 1)) hz
    (fun p hp => ⟨Nat.prime_of_mem_primesBelow hp,
      by have := (Nat.mem_primesBelow.1 hp).1; omega⟩) hσz
  have hmert := sum_primesBelow_inv_le_log_log_add hz
  linarith

/-! ### The moments -/

/-- **The moment of a block product factors over its primes**, at a signed exponent: the
single-exponent case of `RMF.IsRademacherRMF.integral_prod_norm_randomEulerProductIco_rpow`, as
`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_rpow_of_pos` is for the full product. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_rpow_of_pos {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    (y₀ y₁ : ℕ) {s : ℂ} (hs : 0 < s.re) (q : ℝ) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ (2 * q) ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ (2 * q) ∂rademacherLaw := by
  have h := hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y₁ (Finset.univ : Finset Unit)
    (s := fun _ => s) (fun _ _ => hs) (q := fun _ => q)
  simpa [Finset.univ_unique, Finset.prod_singleton] using h

/-- **The moment of a band's Euler product, at a shift inside its own scale.**  For `½ ≤ q ≤ 1`,
`2 ≤ y ≤ z`, `z ≥ 3` and `2|σ|·log z ≤ 1`, `E‖F_{y,z}(½+σ)‖^{2q} ≤ e^{48}·(log z/log y)^{q(2q-1)}`,
`F_{y,z}` the product over the primes `y < p ≤ z`.  At `σ = -1/(2 log z)` this is the input
`E|F_{y,z}(½-c)|^{2q} ≪ κ^{q(2q-1)}` of a band's central window.  The constant is `3` from the
local product and `29 + 16` from Mertens, the latter multiplied by `q(2q-1) ≤ 1`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_signed_shift_rpow_le_log_div
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) {y z : ℕ}
    (hy : 2 ≤ y) (hyz : y ≤ z) (hz : 3 ≤ z) (hσz : 2 * |σ| * Real.log z ≤ 1) :
    (∫ ω, ‖randomEulerProductIco f (y + 1) (z + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp 48 * (Real.log z / Real.log y) ^ (q * (2 * q - 1)) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hly : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz1 : 1 < Real.log z := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < (z : ℝ))
    rwa [Real.log_exp] at h
  -- `|σ| < ½`, so the abscissa is to the right of `0`
  have hσlt : |σ| < 1 / 2 := by
    by_contra h
    push Not at h
    have h2 := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ Real.log z)
    linarith
  have hσh : -(1 / 2) ≤ σ := by linarith [neg_abs_le σ]
  have hre : 0 < ((((1 / 2 + σ : ℝ)) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith [neg_abs_le σ]
  rw [hf.integral_norm_randomEulerProductIco_rpow_of_pos (y + 1) (z + 1) hre q]
  have hloc := prod_integral_norm_one_add_prime_signed_shift_le
    (S := primesIco (y + 1) (z + 1)) (fun p hp => prime_of_mem_primesIco hp) hσh
    (fun p hp => by
      obtain ⟨hprime, _, hpz⟩ := mem_primesIco.1 hp
      have hlp : Real.log p ≤ Real.log z :=
        Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast (by omega : p ≤ z))
      exact le_trans (mul_le_mul_of_nonneg_left hlp (by positivity)) hσz) hq0 hq1
  have hmert := sum_primesIco_rpow_signed_shift_le_log_div_add hy hyz hσz
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hγ1 : q * (2 * q - 1) ≤ 1 := by nlinarith
  have hκ : 0 < Real.log z / Real.log y := div_pos (by linarith) hly
  have hrpow : (Real.log z / Real.log y) ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log z / Real.log y)) := by
    rw [Real.rpow_def_of_pos hκ]
    ring_nf
  refine hloc.trans ?_
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h := mul_le_mul_of_nonneg_left hmert hγ0
  nlinarith [h, hγ1]

/-- **The moment of the bottom band's Euler product, at a shift inside its own scale.**  For
`½ ≤ q ≤ 1`, `z ≥ 3` and `2|σ|·log z ≤ 1`, `E‖F_{z+1}(½+σ)‖^{2q} ≤ e^{21}·(log z)^{q(2q-1)}`: the
band `y = 1`, with `κ = log z`.  For `σ ≥ 0` the sharper
`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log` needs no bound on `σ`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_signed_shift_rpow_le_log
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) {σ q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) {z : ℕ}
    (hz : 3 ≤ z) (hσz : 2 * |σ| * Real.log z ≤ 1) :
    (∫ ω, ‖randomEulerProduct f (z + 1) (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂μ)
      ≤ Real.exp 21 * (Real.log z) ^ (q * (2 * q - 1)) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlz1 : 1 < Real.log z := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < (z : ℝ))
    rwa [Real.log_exp] at h
  have hσlt : |σ| < 1 / 2 := by
    by_contra h
    push Not at h
    have h2 := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ Real.log z)
    linarith
  have hσh : -(1 / 2) ≤ σ := by linarith [neg_abs_le σ]
  have hre : 0 < ((((1 / 2 + σ : ℝ)) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith [neg_abs_le σ]
  rw [hf.integral_norm_randomEulerProduct_rpow_of_pos (z + 1) hre (2 * q)]
  have hloc := prod_integral_norm_one_add_prime_signed_shift_le
    (S := Nat.primesBelow (z + 1)) (fun p hp => Nat.prime_of_mem_primesBelow hp) hσh
    (fun p hp => by
      have hprime := Nat.prime_of_mem_primesBelow hp
      have hpz : p ≤ z := by
        have := (Nat.mem_primesBelow.1 hp).1
        omega
      have hlp : Real.log p ≤ Real.log z :=
        Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpz)
      exact le_trans (mul_le_mul_of_nonneg_left hlp (by positivity)) hσz) hq0 hq1
  have hmert := sum_primesBelow_rpow_signed_shift_le_log_log_add (by omega) hσz
  have hγ0 : (0 : ℝ) ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have hγ1 : q * (2 * q - 1) ≤ 1 := by nlinarith
  have hL0 : (0 : ℝ) < Real.log z := by linarith
  have hrpow : (Real.log z) ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log z)) := by
    rw [Real.rpow_def_of_pos hL0]
    ring_nf
  refine hloc.trans ?_
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h := mul_le_mul_of_nonneg_left hmert hγ0
  nlinarith [h, hγ1]

end RMF
