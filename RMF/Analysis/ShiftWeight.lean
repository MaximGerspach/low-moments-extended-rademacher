/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The shift weight `(1 + n²)^(-q)`

Splitting a line integral `∫_ℝ` into `∑_{n ∈ ℤ} ∫_n^{n+1}` and pulling the weight
`|1/2 + it|⁻²` out of each unit interval costs the factor `∑_{n ∈ ℤ} (1 + n²)^(-q)`.
This file proves the sum is finite, and that it is **decreasing in `q`** — which is what
makes the periodisation step uniform on a range `[q₀, 1]` with `q₀ > 1/2`.

The threshold is sharp: the sum diverges at `q = 1/2`.  Numerically, at the left endpoint of
Harper's range `∑_{n ∈ ℤ} (1 + n²)^(-2/3) ≈ 7.29`, against `≈ 101` at `q = 0.51` and
`≈ 3.15` at `q = 1`.

**Where this is and is not needed.**  This sum is the *only* place where the exponent `q`
enters Hamdan's form of the reduction, and hence the sole reason his §2.1 is stated for
`q ≥ 2/3` rather than `q ∈ [0,1]`.  Gorodetsky–Wong avoid it entirely by stopping at the
line integral, whose weight `|1/2 + it|⁻²` already makes `∫_ℝ` converge.  So
`RMF.reduction_upper` does **not** pay this factor, and only `RMF.periodisation_upper`, the
later passage to `∫_0^1`, does.
-/

namespace RMF

/-- The weight paid by the shift decomposition at the integer `n`. -/
noncomputable def shiftWeight (q : ℝ) (n : ℤ) : ℝ := (1 + (n : ℝ) ^ 2) ^ (-q)

lemma one_le_one_add_sq (t : ℝ) : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]

lemma shiftWeight_pos (q : ℝ) (n : ℤ) : 0 < shiftWeight q n :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_one_add_sq _)) _

lemma shiftWeight_nonneg (q : ℝ) (n : ℤ) : 0 ≤ shiftWeight q n := (shiftWeight_pos q n).le

/-- **The weight decreases as `q` grows.**  So a bound at the left endpoint of a range of
exponents bounds the whole range — this is exactly the uniformity the periodisation needs,
and it is why the range has a closed left end. -/
lemma shiftWeight_le_of_le {q q' : ℝ} (h : q' ≤ q) (n : ℤ) :
    shiftWeight q n ≤ shiftWeight q' n :=
  Real.rpow_le_rpow_of_exponent_le (one_le_one_add_sq _) (by linarith)

/-- The pointwise comparison behind summability: `(1 + m²)^(-q) ≤ (m^(2q))⁻¹` for `m > 0`.
Dropping the `1` *increases* the value because the exponent is negative. -/
lemma one_add_sq_rpow_le {m q : ℝ} (hm : 0 < m) (hq : 0 ≤ q) :
    (1 + m ^ 2) ^ (-q) ≤ (m ^ (2 * q))⁻¹ := by
  have hsq : (0 : ℝ) < m ^ 2 := by positivity
  have hle : m ^ 2 ≤ 1 + m ^ 2 := by linarith
  refine (Real.rpow_le_rpow_of_nonpos hsq hle (neg_nonpos.2 hq)).trans_eq ?_
  rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hm.le, ← Real.rpow_neg hm.le]
  norm_num

/-- Summability on the shifted naturals, where the comparison of `one_add_sq_rpow_le` is
available at every index. -/
lemma summable_nat_succ_shiftWeight {q : ℝ} (hq : 1 / 2 < q) :
    Summable fun n : ℕ => (1 + ((n : ℝ) + 1) ^ 2) ^ (-q) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have h2q : (1 : ℝ) < 2 * q := by linarith
  have hbase : Summable fun n : ℕ => (((n : ℝ) + 1) ^ (2 * q))⁻¹ := by
    have h := (summable_nat_add_iff
      (f := fun n : ℕ => ((n : ℝ) ^ (2 * q))⁻¹) 1).2 (Real.summable_nat_rpow_inv.2 h2q)
    simpa using h
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact Real.rpow_nonneg (by positivity) _
  · exact one_add_sq_rpow_le (by positivity) hq0

lemma summable_nat_shiftWeight {q : ℝ} (hq : 1 / 2 < q) :
    Summable fun n : ℕ => (1 + (n : ℝ) ^ 2) ^ (-q) := by
  refine (summable_nat_add_iff (f := fun n : ℕ => (1 + (n : ℝ) ^ 2) ^ (-q)) 1).1 ?_
  simpa using summable_nat_succ_shiftWeight hq

/-- **The shift weight is summable over `ℤ` for `q > 1/2`.** -/
lemma summable_shiftWeight {q : ℝ} (hq : 1 / 2 < q) : Summable (shiftWeight q) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa [shiftWeight] using summable_nat_shiftWeight hq
  · refine (summable_nat_succ_shiftWeight hq).congr fun n => ?_
    simp only [shiftWeight]
    push_cast
    ring_nf

/-- `(|n| + 1)^{1/4} ≤ 2^{1/8}(1 + n²)^{1/8}`, since `(|n|+1)² ≤ 2(1 + n²)`. -/
lemma abs_add_one_rpow_le (n : ℤ) :
    (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)
      ≤ 2 ^ ((1 : ℝ) / 8) * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 8) := by
  have hb : (0 : ℝ) ≤ |(n : ℝ)| + 1 := by positivity
  have hsq : (|(n : ℝ)| + 1) ^ 2 ≤ 2 * (1 + (n : ℝ) ^ 2) := by
    have h1 : (0 : ℝ) ≤ (|(n : ℝ)| - 1) ^ 2 := sq_nonneg _
    have h2 : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
    nlinarith
  calc (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)
      = ((|(n : ℝ)| + 1) ^ 2) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_natCast (|(n : ℝ)| + 1) 2, ← Real.rpow_mul hb]
        norm_num
    _ ≤ (2 * (1 + (n : ℝ) ^ 2)) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) hsq (by norm_num)
    _ = 2 ^ ((1 : ℝ) / 8) * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 8) :=
        Real.mul_rpow (by norm_num) (by positivity)

/-- **Harper's sum-to-max step costs an eighth of the exponent.**  Pulling
`max_N (|N|+1)^{-1/4} A_N` out of `∑_n shiftWeight q n · A_n` leaves the residual
`∑_n shiftWeight q n · (|n|+1)^{1/4}`, and this bounds its summand by `shiftWeight (q - 1/8)`.

The step is `∑_n (|n|^{2q}+1)^{-1} E[…]^q ≪ max_N (|N|+1)^{-1/4} E[…]^q`, in the proof of
Proposition 2 of Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654,
§2.4). -/
lemma shiftWeight_mul_abs_add_one_rpow_le {q : ℝ} (n : ℤ) :
    shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)
      ≤ 2 ^ ((1 : ℝ) / 8) * shiftWeight (q - 1 / 8) n := by
  have hpos : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := lt_of_lt_of_le one_pos (one_le_one_add_sq _)
  have hcomb : (1 + (n : ℝ) ^ 2) ^ (-q) * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 8)
      = (1 + (n : ℝ) ^ 2) ^ (-(q - 1 / 8)) := by
    rw [← Real.rpow_add hpos]
    ring_nf
  calc shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)
      ≤ shiftWeight q n * (2 ^ ((1 : ℝ) / 8) * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left (abs_add_one_rpow_le n) (shiftWeight_nonneg q n)
    _ = 2 ^ ((1 : ℝ) / 8) * shiftWeight (q - 1 / 8) n := by
        simp only [shiftWeight]
        rw [← hcomb]
        ring

/-- **The residual of Harper's sum-to-max step converges for `q > 5/8`**, which the range
`2/3 ≤ q ≤ 1` of his Proposition 2 satisfies.

The plain weight is summable for `q > 1/2` (`RMF.summable_shiftWeight`); paying `(|n|+1)^{1/4}` to
pull out the maximum costs an eighth of the exponent, and `q - 1/8 > 1/2` is `q > 5/8`. -/
lemma summable_shiftWeight_mul_abs_add_one_rpow {q : ℝ} (hq : 5 / 8 < q) :
    Summable fun n : ℤ => shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
  refine Summable.of_nonneg_of_le (fun n => ?_)
    (fun n => shiftWeight_mul_abs_add_one_rpow_le n)
    ((summable_shiftWeight (q := q - 1 / 8) (by linarith)).mul_left _)
  exact mul_nonneg (shiftWeight_nonneg q n) (Real.rpow_nonneg (by positivity) _)

/-- **The uniform bound.**  Over a range of exponents with a closed left end above `1/2`,
the weight sum is controlled by its value at that endpoint.  At `q₀ = 2/3` the right-hand
side is `≈ 7.29`. -/
lemma tsum_shiftWeight_le {q₀ q : ℝ} (hq₀ : 1 / 2 < q₀) (h : q₀ ≤ q) :
    ∑' n : ℤ, shiftWeight q n ≤ ∑' n : ℤ, shiftWeight q₀ n :=
  Summable.tsum_le_tsum (fun n => shiftWeight_le_of_le h n)
    (summable_shiftWeight (lt_of_lt_of_le hq₀ h)) (summable_shiftWeight hq₀)

/-- The weighted sum is decreasing in `q`, just as `RMF.tsum_shiftWeight_le` says of the plain
one.  `5/8` rather than `1/2` is the threshold because of the `(|n|+1)^{1/4}` factor. -/
lemma tsum_shiftWeight_mul_abs_add_one_rpow_le {q₀ q : ℝ} (hq₀ : 5 / 8 < q₀) (h : q₀ ≤ q) :
    (∑' n : ℤ, shiftWeight q n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
      ≤ ∑' n : ℤ, shiftWeight q₀ n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
  (summable_shiftWeight_mul_abs_add_one_rpow (by linarith)).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (shiftWeight_le_of_le h n)
      (Real.rpow_nonneg (by positivity) _))
    (summable_shiftWeight_mul_abs_add_one_rpow hq₀)

end RMF
