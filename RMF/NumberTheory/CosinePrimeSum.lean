/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import PrimeNumberTheoremAnd.IEANTN.Mertens
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime
import RMF.Analysis.CosineIntegral
import RMF.NumberTheory.MertensUniform

/-!
# The cosine prime sum

`K_y(τ) = ∑_{p ≤ y} cos (τ log p) / p = log (min (log y) (1/τ)) + O(1)` for `0 < τ ≤ 1`.

This is the kernel of a joint moment of random Euler products, and the estimate is what makes
the limiting field log-correlated: the sum grows like `log log y` until `log y` reaches `1/τ`,
and is flat afterwards.

## The argument

Write `g t = cos (τ log t) / (t log t)`, so that `log p · g p = cos (τ log p) / p`.  Abel
summation against `θ t = ∑_{p ≤ t} log p` gives

`∑_{p ≤ y} cos (τ log p) / p = g y · θ y - ∫_2^y g' t · θ t dt`,

and substituting `θ t = t + E t` splits this into

* a main term `∫_2^y g t dt`, which `RMF.abs_integral_cos_log_div_sub_log_min_le` evaluates
  (after integrating `∫ g' t · t dt` by parts), and
* an error `2 g 2 + g y · E y - ∫_2^y g' t · E t dt`.

The error is bounded because `|g' t| ≤ (|τ| + 3) / (t ^ 2 log t)` and the prime number
theorem gives `|E t| ≤ C t / log t ^ 2`, so the integrand is `O((|τ|+3) / (t log t ^ 3))`,
which is integrable on `[2, ∞)`.  Mertens' theorem alone would *not* do here: its error
`O(1/log t)` leaves `∫ dt / (t log t)`, which diverges over `[2, ∞)`.

That is the right reason for the full-range statement `RMF.exists_abs_cos_prime_sum_sub_log_min_le`
and the *wrong* one for the block estimates below: over a single block the ratio
`log y₂ / log y₁` is `e`, so `∫ dt / (t log t)` is bounded there.  Mertens still fails, but for a
different reason — it leaves the bound with no decay in `y₁` at all, against a target of
`K / (τ log y₁)`, and it fails that way even at `τ ≍ 1`.

## Main results

`RMF.exists_abs_cos_prime_sum_sub_log_min_le` is the estimate at the top; the block form, with
the weight `p^{-2σ}` carried through it, is `RMF.exists_abs_cos_prime_sum_block_weight_le`.
-/

open Real MeasureTheory Finset

namespace RMF

/-- The summand of the Abel summation: `g t = cos (τ log t) / (t log t)`, chosen so that
`log p · g p` is the term `cos (τ log p) / p` of the prime sum. -/
noncomputable def cosLogDiv (τ t : ℝ) : ℝ := Real.cos (τ * Real.log t) / (t * Real.log t)

/-- On `[2, ∞)` the denominator of `g` does not vanish. -/
lemma mul_log_ne_zero {t : ℝ} (ht : 2 ≤ t) : t * Real.log t ≠ 0 := by
  have h1 : (1 : ℝ) < t := by linarith
  exact mul_ne_zero (by linarith) (Real.log_pos h1).ne'

/-- The derivative of `g`, by the quotient rule. -/
lemma hasDerivAt_cosLogDiv (τ : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (cosLogDiv τ)
      ((-(τ * Real.sin (τ * Real.log t) * Real.log t)
        - Real.cos (τ * Real.log t) * (Real.log t + 1)) / (t * Real.log t) ^ 2) t := by
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; linarith
  have hnum : HasDerivAt (fun u => Real.cos (τ * Real.log u))
      (-Real.sin (τ * Real.log t) * (τ * t⁻¹)) t :=
    ((Real.hasDerivAt_log ht0).const_mul τ).cos
  have hden : HasDerivAt (fun u => u * Real.log u) (1 * Real.log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
  refine (hnum.fun_div hden (mul_log_ne_zero ht)).congr_deriv ?_
  field_simp

lemma differentiableAt_cosLogDiv (τ : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    DifferentiableAt ℝ (cosLogDiv τ) t := (hasDerivAt_cosLogDiv τ ht).differentiableAt

/-- **The derivative bound.**  `|g' t| ≤ (|τ| + 3) / (t ^ 2 log t)` for `t ≥ 2`.  The `3`
absorbs `1 + 1 / log 2`, which is where the lower bound on `log t` is used. -/
lemma abs_deriv_cosLogDiv_le (τ : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    |deriv (cosLogDiv τ) t| ≤ (|τ| + 3) / (t ^ 2 * Real.log t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hlow : (0.6931471803 : ℝ) < Real.log t :=
    lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) ht)
  rw [(hasDerivAt_cosLogDiv τ ht).deriv]
  have hden : (0 : ℝ) < (t * Real.log t) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have h1 : |(-(τ * Real.sin (τ * Real.log t) * Real.log t))| ≤ |τ| * Real.log t := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos hlt]
    have hs : |Real.sin (τ * Real.log t)| ≤ 1 := Real.abs_sin_le_one _
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (abs_nonneg τ)) hlt.le]
  have h2 : |Real.cos (τ * Real.log t) * (Real.log t + 1)| ≤ Real.log t + 1 := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < Real.log t + 1)]
    nlinarith [Real.abs_cos_le_one (τ * Real.log t), abs_nonneg (Real.cos (τ * Real.log t))]
  have hnum : |(-(τ * Real.sin (τ * Real.log t) * Real.log t)
      - Real.cos (τ * Real.log t) * (Real.log t + 1))| ≤ |τ| * Real.log t + (Real.log t + 1) := by
    have htri : |(-(τ * Real.sin (τ * Real.log t) * Real.log t)
        - Real.cos (τ * Real.log t) * (Real.log t + 1))|
        ≤ |(-(τ * Real.sin (τ * Real.log t) * Real.log t))|
          + |Real.cos (τ * Real.log t) * (Real.log t + 1)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (-(τ * Real.sin (τ * Real.log t) * Real.log t))
        (Real.cos (τ * Real.log t) * (Real.log t + 1))
    linarith
  calc |(-(τ * Real.sin (τ * Real.log t) * Real.log t)
        - Real.cos (τ * Real.log t) * (Real.log t + 1))| * (t ^ 2 * Real.log t)
      ≤ (|τ| * Real.log t + (Real.log t + 1)) * (t ^ 2 * Real.log t) := by gcongr
    _ ≤ (|τ| + 3) * (t * Real.log t) ^ 2 := by
        have hkey : |τ| * Real.log t + (Real.log t + 1) ≤ (|τ| + 3) * Real.log t := by
          nlinarith [abs_nonneg τ]
        nlinarith [mul_pos ht0 hlt, sq_nonneg t, mul_nonneg (sq_nonneg t) hlt.le]

/-! ### Abel summation -/

/-- `log` is continuous on any interval to the right of the origin. -/
lemma continuousOn_log_Icc {a b : ℝ} (ha : 0 < a) : ContinuousOn Real.log (Set.Icc a b) :=
  ContinuousOn.log continuousOn_id fun _ ht => (ha.trans_le ht.1).ne'

lemma continuousOn_deriv_cosLogDiv (τ : ℝ) {y : ℝ} :
    ContinuousOn (deriv (cosLogDiv τ)) (Set.Icc 2 y) := by
  have hform : Set.EqOn (deriv (cosLogDiv τ))
      (fun t => (-(τ * Real.sin (τ * Real.log t) * Real.log t)
        - Real.cos (τ * Real.log t) * (Real.log t + 1)) / (t * Real.log t) ^ 2)
      (Set.Icc 2 y) := fun t ht => (hasDerivAt_cosLogDiv τ ht.1).deriv
  refine ContinuousOn.congr ?_ hform
  have hlog := continuousOn_log_Icc (a := 2) (b := y) (by norm_num)
  have hτlog : ContinuousOn (fun t => τ * Real.log t) (Set.Icc 2 y) := continuousOn_const.mul hlog
  refine ContinuousOn.div ?_ ?_ fun t ht => pow_ne_zero 2 (mul_log_ne_zero ht.1)
  · exact ((continuousOn_const.mul (Real.continuous_sin.comp_continuousOn hτlog)).mul hlog).neg.sub
      ((Real.continuous_cos.comp_continuousOn hτlog).mul (hlog.add continuousOn_const))
  · exact (continuousOn_id.mul hlog).pow 2

lemma integrableOn_deriv_cosLogDiv (τ : ℝ) {y : ℝ} :
    IntegrableOn (deriv (cosLogDiv τ)) (Set.Icc 2 y) :=
  (continuousOn_deriv_cosLogDiv τ).integrableOn_Icc

/-- The coefficient sequence of the Abel summation: `log p` at primes, `0` elsewhere.  Its
partial sums are Chebyshev's `θ`. -/
noncomputable def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

@[simp] lemma primeLog_zero : primeLog 0 = 0 := if_neg Nat.not_prime_zero

@[simp] lemma primeLog_one : primeLog 1 = 0 := if_neg Nat.not_prime_one

lemma sum_primeLog_eq_theta (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLog k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

/-- **Abel summation for the cosine prime sum.**  With `g = cosLogDiv τ` and `θ` Chebyshev's
function, `∑_{p ≤ y} cos (τ log p) / p = g y · θ y - ∫_2^y g' t · θ t dt`. -/
theorem cos_prime_sum_eq (τ : ℝ) (y : ℝ) :
    ∑ p ∈ Finset.Icc 0 ⌊y⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p
      = cosLogDiv τ y * Chebyshev.theta y
        - ∫ t in Set.Ioc 2 y, deriv (cosLogDiv τ) t * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_integral_mul₁ (c := primeLog) (f := cosLogDiv τ)
    primeLog_zero primeLog_one y
    (fun t ht => differentiableAt_cosLogDiv τ ht.1) (integrableOn_deriv_cosLogDiv τ)
  simp_rw [sum_primeLog_eq_theta] at habel
  rw [← habel, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hp : k.Prime
  · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp.two_le
    have hlog : Real.log k ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    rw [if_pos hp, primeLog, if_pos hp, cosLogDiv]
    field_simp
  · rw [if_neg hp, primeLog, if_neg hp, mul_zero]

/-! ### The error term

Replacing `θ t` by `t` costs `∫ g' t · E t` with `E = θ - id`.  The prime number theorem
bounds `|E t|` by `C t / log t ^ 2`, which against `|g' t| ≤ (|τ| + 3) / (t ^ 2 log t)` leaves
`C (|τ| + 3) / (t log t ^ 3)` — integrable on `[2, ∞)`, with `∫ = 1 / (2 log 2 ^ 2)`.
-/

/-- The error majorant is integrable over any block `[y₁, y₂] ⊆ [2, ∞)`. -/
lemma intervalIntegrable_inv_mul_log_cube' {y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) :
    IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 3)) volume y₁ y₂ := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hy]
  have hlog3 : ContinuousOn (fun t : ℝ => Real.log t ^ 3) (Set.Icc y₁ y₂) :=
    (continuousOn_log_Icc (a := y₁) (b := y₂) (by linarith)).pow 3
  refine ContinuousOn.div continuousOn_const (continuousOn_id.mul hlog3) fun t ht => ?_
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  have hlt : (0:ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
  positivity

/-- **The error majorant, over a block.**  `∫_{y₁}^{y₂} dt/(t log³t) ≤ 1/(2 log²y₁)`, since
`-1/(2 log²u)` is an antiderivative.  The bound decays in `y₁`, which is what the block form of the
decorrelation estimate needs; at `y₁ = 2` it is merely an absolute constant. -/
lemma integral_inv_mul_log_cube_le' {y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) :
    (∫ t in y₁..y₂, 1 / (t * Real.log t ^ 3)) ≤ 1 / (2 * Real.log y₁ ^ 2) := by
  have hy₁pos : (0:ℝ) < y₁ := by linarith
  have hlog₁ : (0:ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  have hderiv : ∀ t ∈ Set.uIcc y₁ y₂,
      HasDerivAt (fun u => -(1 / (2 * Real.log u ^ 2))) (1 / (t * Real.log t ^ 3)) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : t ≠ 0 := by have := ht.1; intro h; rw [h] at this; linarith
    have hlt : (0:ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    have hl := (Real.hasDerivAt_log ht0).pow 2
    have h2 : HasDerivAt (fun u => 2 * Real.log u ^ 2)
        (2 * (2 * Real.log t ^ 1 * t⁻¹)) t := hl.const_mul 2
    refine (((h2.inv (by positivity)).const_mul (1:ℝ)).neg).congr_deriv ?_
    field_simp
  have hint := intervalIntegrable_inv_mul_log_cube' hy₁ hy
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hly : Real.log y₁ ≤ Real.log y₂ := Real.log_le_log hy₁pos hy
  have hpos : (0:ℝ) < Real.log y₂ := lt_of_lt_of_le hlog₁ hly
  have h2 : (0:ℝ) ≤ 1 / (2 * Real.log y₂ ^ 2) := by positivity
  linarith

/-- A crude uniform bound on `g'`, enough for integrability on compacts. -/
lemma abs_deriv_cosLogDiv_le_const (τ : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    |deriv (cosLogDiv τ) t| ≤ (|τ| + 3) / (4 * Real.log 2) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
  have hmono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  refine (abs_deriv_cosLogDiv_le τ ht).trans ?_
  have ht2 : (4:ℝ) ≤ t ^ 2 := by nlinarith
  have hden : 4 * Real.log 2 ≤ t ^ 2 * Real.log t :=
    calc 4 * Real.log 2 ≤ 4 * Real.log t := by linarith
      _ ≤ t ^ 2 * Real.log t := mul_le_mul_of_nonneg_right ht2 hlt.le
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

lemma integrableOn_deriv_mul_theta (τ : ℝ) {y : ℝ} :
    IntegrableOn (fun t => deriv (cosLogDiv τ) t * Chebyshev.theta t) (Set.Icc 2 y) := by
  by_cases hy : 2 ≤ y
  · have hmeas : AEStronglyMeasurable
        (fun t => deriv (cosLogDiv τ) t * Chebyshev.theta t) (volume.restrict (Set.Icc 2 y)) :=
      ((continuousOn_deriv_cosLogDiv τ).aestronglyMeasurable measurableSet_Icc).mul
        (Chebyshev.theta_mono.measurable.aestronglyMeasurable.restrict)
    refine MeasureTheory.Integrable.mono'
      (g := fun _ : ℝ => (|τ| + 3) / (4 * Real.log 2) * Chebyshev.theta y)
      (integrable_const _) hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Chebyshev.theta_nonneg t)]
    exact mul_le_mul (abs_deriv_cosLogDiv_le_const τ ht.1) (Chebyshev.theta_mono ht.2)
      (Chebyshev.theta_nonneg t) (by positivity)
  · rw [Set.Icc_eq_empty (by linarith [not_le.mp hy])]
    exact MeasureTheory.integrableOn_empty

lemma integrableOn_deriv_mul_id (τ : ℝ) {y : ℝ} :
    IntegrableOn (fun t => deriv (cosLogDiv τ) t * t) (Set.Icc 2 y) :=
  ((continuousOn_deriv_cosLogDiv τ).mul continuousOn_id).integrableOn_Icc

lemma integrableOn_deriv_mul_sub (τ : ℝ) {y : ℝ} :
    IntegrableOn (fun t => deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)) (Set.Icc 2 y) := by
  have h := (integrableOn_deriv_mul_theta τ (y := y)).sub (integrableOn_deriv_mul_id τ (y := y))
  simpa only [mul_sub, Pi.sub_def] using h

/-- **Integration by parts** against the identity: `∫_2^y g' t · t dt = g y · y - 2 g 2 - ∫_2^y g`.
This is what turns the Abel summation's integral into the main term. -/
lemma integral_deriv_mul_id (τ : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    (∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * t)
      = cosLogDiv τ y * y - 2 * cosLogDiv τ 2 - ∫ t in (2:ℝ)..y, cosLogDiv τ t := by
  have hu : ∀ t ∈ Set.uIcc (2:ℝ) y, HasDerivAt (cosLogDiv τ) (deriv (cosLogDiv τ) t) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact (hasDerivAt_cosLogDiv τ ht.1).congr_deriv ((hasDerivAt_cosLogDiv τ ht.1).deriv).symm
  have hv : ∀ t ∈ Set.uIcc (2:ℝ) y, HasDerivAt (fun u : ℝ => u) 1 t := fun t _ => hasDerivAt_id t
  have hu' : IntervalIntegrable (deriv (cosLogDiv τ)) volume 2 y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
    exact (continuousOn_deriv_cosLogDiv τ).integrableOn_Icc
  have hv' : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 2 y := intervalIntegrable_const
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [mul_one] at hparts
  rw [hparts]
  ring

/-- The Abel summation with `θ` split as `id + E`: a main term `∫_2^y g` and three error
pieces. -/
theorem cos_prime_sum_eq_integral_add (τ : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    ∑ p ∈ Finset.Icc 0 ⌊y⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p
      = (∫ t in (2:ℝ)..y, cosLogDiv τ t) + 2 * cosLogDiv τ 2
        + cosLogDiv τ y * (Chebyshev.theta y - y)
        - ∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t) := by
  have hIθ : IntervalIntegrable (fun t => deriv (cosLogDiv τ) t * Chebyshev.theta t) volume 2 y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr (integrableOn_deriv_mul_theta τ)
  have hIid : IntervalIntegrable (fun t => deriv (cosLogDiv τ) t * t) volume 2 y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr (integrableOn_deriv_mul_id τ)
  have hIE : IntervalIntegrable
      (fun t => deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)) volume 2 y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr (integrableOn_deriv_mul_sub τ)
  have hsplit : (∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * Chebyshev.theta t)
      = (∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * t)
        + ∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t) := by
    rw [← intervalIntegral.integral_add hIid hIE]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [cos_prime_sum_eq τ y, ← intervalIntegral.integral_of_le hy, hsplit,
    integral_deriv_mul_id τ hy]
  ring

/-- **The error integral, over a block.**  This is where the prime number theorem enters:
`|E t| ≤ C t / log t ^ 2` against `|g' t| ≤ (|τ| + 3) / (t ^ 2 log t)` leaves
`C (|τ| + 3) / (t log t ^ 3)`, whose integral over `[y₁, y₂]` is at most `1/(2 log²y₁)`
however long the block is. -/
theorem abs_integral_deriv_mul_sub_le' (τ : ℝ) {C : ℝ} (hC : 0 ≤ C)
    {y₁ y₂ : ℝ}
    (hE : ∀ t : ℝ, y₁ ≤ t → t ≤ y₂ → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ 2)
    (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) :
    |∫ t in y₁..y₂, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
      ≤ C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) := by
  have hlog₁ : (0:ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  have hsub : IntegrableOn
      (fun t => deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)) (Set.Icc y₁ y₂) :=
    (integrableOn_deriv_mul_sub τ (y := y₂)).mono_set (Set.Icc_subset_Icc hy₁ le_rfl)
  have hpt : ∀ t ∈ Set.Icc y₁ y₂,
      |deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
        ≤ C * (|τ| + 3) * (1 / (t * Real.log t ^ 3)) := by
    intro t ht
    have ht2 : (2:ℝ) ≤ t := hy₁.trans ht.1
    have ht0 : (0:ℝ) < t := by linarith
    have hlt : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
    rw [abs_mul]
    have hprod : |deriv (cosLogDiv τ) t| * |Chebyshev.theta t - t|
        ≤ ((|τ| + 3) / (t ^ 2 * Real.log t)) * (C * t / Real.log t ^ 2) :=
      mul_le_mul (abs_deriv_cosLogDiv_le τ ht2) (hE t ht.1 ht.2) (abs_nonneg _)
        (by positivity)
    refine hprod.trans_eq ?_
    field_simp
  calc |∫ t in y₁..y₂, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
      ≤ ∫ t in y₁..y₂, |deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)| :=
        intervalIntegral.abs_integral_le_integral_abs hy
    _ ≤ ∫ t in y₁..y₂, C * (|τ| + 3) * (1 / (t * Real.log t ^ 3)) :=
        intervalIntegral.integral_mono_on hy
          (((intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hsub).abs)
          ((intervalIntegrable_inv_mul_log_cube' hy₁ hy).const_mul _) hpt
    _ = C * (|τ| + 3) * ∫ t in y₁..y₂, 1 / (t * Real.log t ^ 3) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ C * (|τ| + 3) * (1 / (2 * Real.log y₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left (integral_inv_mul_log_cube_le' hy₁ hy)
          (mul_nonneg hC (by positivity))
    _ = C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) := by ring

/-- The error integral from `2`, the case `y₁ = 2` of `RMF.abs_integral_deriv_mul_sub_le'`. -/
theorem abs_integral_deriv_mul_sub_le (τ : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ 2)
    {y : ℝ} (hy : 2 ≤ y) :
    |∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
      ≤ C * (|τ| + 3) / (2 * Real.log 2 ^ 2) :=
  abs_integral_deriv_mul_sub_le' τ hC (fun s hs _ => hE s hs) le_rfl hy

/-- **The boundary term.**  `|g y| ≤ 1/(y log y)` against `|E y| ≤ C y / log²y` leaves
`C / log³y` — the endpoints of an Abel summation cost one more power of `log` than the
error integral does. -/
lemma abs_cosLogDiv_mul_sub_le (τ : ℝ) {C y : ℝ} (hy : 2 ≤ y)
    (hE : |Chebyshev.theta y - y| ≤ C * y / Real.log y ^ 2) :
    |cosLogDiv τ y * (Chebyshev.theta y - y)| ≤ C / Real.log y ^ 3 := by
  have hy0 : (0:ℝ) < y := by linarith
  have hlty : (0:ℝ) < Real.log y := Real.log_pos (by linarith)
  have hg : |cosLogDiv τ y| ≤ 1 / (y * Real.log y) := by
    rw [cosLogDiv, abs_div, abs_of_pos (by positivity : (0:ℝ) < y * Real.log y),
      div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < y * Real.log y)]
    exact Real.abs_cos_le_one _
  rw [abs_mul]
  calc |cosLogDiv τ y| * |Chebyshev.theta y - y|
      ≤ 1 / (y * Real.log y) * (C * y / Real.log y ^ 2) :=
        mul_le_mul hg hE (abs_nonneg _) (by positivity)
    _ = C / Real.log y ^ 3 := by field_simp

/-! ### The estimate -/

/-- **The cosine prime sum.**  There is `B > 0` such that for `0 < τ ≤ 1` and `y ≥ 2`,
`|∑_{p ≤ y} cos (τ log p) / p - log (min (log y) (1/τ) / log 2)| ≤ B`.  The sum grows like
`log log y` until `log y` reaches `1/τ` and is flat afterwards: this is the covariance of a
log-correlated field.  The prime number theorem enters through `RS_prime.pnt`, in the shape
`|θ x - x| ≤ C x / log x ^ 2` for all `x ≥ 2`. -/
theorem exists_abs_cos_prime_sum_sub_log_min_le :
    ∃ B > 0, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ y : ℝ, 2 ≤ y →
      |∑ p ∈ Finset.Icc 0 ⌊y⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p
        - Real.log (min (Real.log y) (1 / τ) / Real.log 2)| ≤ B := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC, hpnt⟩ := RS_prime.pnt
  refine ⟨4 + 1 / Real.log 2 + C / Real.log 2 ^ 3 + 2 * C / Real.log 2 ^ 2, by positivity, ?_⟩
  intro τ hτ hτ1 y hy
  have hy0 : (0:ℝ) < y := by linarith
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlty : (0:ℝ) < Real.log y := lt_of_lt_of_le hlog2 hlogy
  rw [cos_prime_sum_eq_integral_add τ hy]
  -- the main term
  have h1 : |(∫ t in (2:ℝ)..y, cosLogDiv τ t)
      - Real.log (min (Real.log y) (1 / τ) / Real.log 2)| ≤ 4 :=
    abs_integral_cos_log_div_sub_log_min_le hτ hτ1 hy
  -- the boundary term at 2
  have h2 : |2 * cosLogDiv τ 2| ≤ 1 / Real.log 2 := by
    rw [cosLogDiv, show (2:ℝ) * (Real.cos (τ * Real.log 2) / (2 * Real.log 2))
      = Real.cos (τ * Real.log 2) / Real.log 2 by field_simp, abs_div, abs_of_pos hlog2,
      div_le_div_iff_of_pos_right hlog2]
    exact Real.abs_cos_le_one _
  -- the boundary term at y
  have h3 : |cosLogDiv τ y * (Chebyshev.theta y - y)| ≤ C / Real.log 2 ^ 3 :=
    (abs_cosLogDiv_mul_sub_le τ hy (hpnt y hy)).trans (by gcongr)
  -- the error integral
  have h4 : |∫ t in (2:ℝ)..y, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
      ≤ 2 * C / Real.log 2 ^ 2 := by
    refine (abs_integral_deriv_mul_sub_le τ hC hpnt hy).trans ?_
    rw [abs_of_pos hτ, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (0:ℝ) ≤ (1 - τ) * C := mul_nonneg (by linarith) hC
    nlinarith [mul_nonneg h1 (sq_nonneg (Real.log 2))]
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> [linarith [h1.1, h2.1, h3.1, h4.2]; linarith [h1.2, h2.2, h3.2, h4.1]]

/-! ### The block estimate

Over a block `y₁ < p ≤ y₂` the sum does **not** grow: the main term is
`RMF.abs_integral_cos_log_div_tail_le`, which is `≤ 3/(τ log y₁)` however long the block is,
and every error term carries an extra power of `log y₁`.  This is the covariance *between* two
far-apart blocks of the log-correlated field, and it is what the two-point Gaussian comparison
needs — not the covariance itself, which is the section above.
-/

lemma continuousOn_cosLogDiv (τ : ℝ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (cosLogDiv τ) (Set.Icc a b) := by
  have hlog := continuousOn_log_Icc (a := a) (b := b) (by linarith)
  refine ContinuousOn.congr (f := fun t => Real.cos (τ * Real.log t) / (t * Real.log t))
    ?_ fun _ _ => rfl
  exact ContinuousOn.div (Real.continuous_cos.comp_continuousOn (hlog.const_mul τ))
    (continuousOn_id.mul hlog) fun t ht => mul_log_ne_zero (ha.trans ht.1)

lemma intervalIntegrable_cosLogDiv (τ : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (cosLogDiv τ) volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (continuousOn_cosLogDiv τ ha).integrableOn_Icc

/-- A sum over `(n₁, n₂]` is the difference of the two sums from `0`. -/
lemma sum_Ioc_eq_sub {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (c : ℕ → ℝ) :
    ∑ k ∈ Finset.Ioc n₁ n₂, c k
      = (∑ k ∈ Finset.Icc 0 n₂, c k) - ∑ k ∈ Finset.Icc 0 n₁, c k := by
  rw [← Finset.sum_sdiff_eq_sub (Finset.Icc_subset_Icc_right h)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc, Nat.zero_le, true_and, not_le]
  omega

/-- A prime sum over `(n₁, n₂]` is the difference of the two sums from `0`. -/
lemma sum_prime_Ioc_eq_sub {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (f : ℕ → ℝ) :
    ∑ p ∈ Finset.Ioc n₁ n₂ with Nat.Prime p, f p
      = (∑ p ∈ Finset.Icc 0 n₂ with Nat.Prime p, f p)
        - ∑ p ∈ Finset.Icc 0 n₁ with Nat.Prime p, f p := by
  simp only [Finset.sum_filter]
  exact sum_Ioc_eq_sub h _

/-- **Abel summation over a block, against the block's own partial sums**
`A t = ∑_{y₁ < k ≤ t} c k`.  Mathlib's `sum_mul_eq_sub_sub_integral_mul` uses the full partial
sums `T t = ∑_{k ≤ t} c k`, which are large where the block sums are small; `A t = T t - T y₁`
differs by a constant, which cancels exactly: the boundary terms give it the coefficient
`f y₂ - f y₁` and the integral gives back `∫_{y₁}^{y₂} f' = f y₂ - f y₁`.  So a weight moves across
a block estimate at the cost of `sup|f| + ∫|f'|`. -/
theorem sum_mul_eq_sub_integral_mul_block (c : ℕ → ℝ) {f : ℝ → ℝ} {y₁ y₂ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂)
    (hf_diff : ∀ t ∈ Set.Icc y₁ y₂, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc y₁ y₂)) :
    ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, f k * c k
      = f y₂ * (∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, c k)
        - ∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊t⌋₊, c k := by
  have hf_int' : IntervalIntegrable (deriv f) volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hf_int
  have habel := sum_mul_eq_sub_sub_integral_mul c hy₁ hy hf_diff hf_int
  rw [← intervalIntegral.integral_of_le hy] at habel
  have hftc : (∫ t in y₁..y₂, deriv f t) = f y₂ - f y₁ :=
    intervalIntegral.integral_deriv_eq_sub (by rwa [Set.uIcc_of_le hy]) hf_int'
  have hT : IntervalIntegrable
      (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      (integrableOn_mul_sum_Icc c (m := 0) hy₁ hf_int)
  have hconst : IntervalIntegrable
      (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k) volume y₁ y₂ := hf_int'.mul_const _
  have hsplit : (∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊t⌋₊, c k)
      = (∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        - (f y₂ - f y₁) * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k := by
    rw [← hftc, ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub hT hconst]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hy] at ht
    rw [sum_Ioc_eq_sub (Nat.floor_le_floor ht.1) c]
    ring
  rw [habel, hsplit, sum_Ioc_eq_sub (Nat.floor_le_floor hy) c]
  ring

/-- **Moving a weight across a block estimate.**  If the block partial sums of `c` never exceed
`M` on `[y₁, y₂]`, then weighting by `f` costs only `|f y₂| + ∫|f'|` — the total variation of the
weight plus its value at the right endpoint.  Nothing about `c` is used beyond the block bound, so
a bounded weight of bounded variation transfers a block estimate at a bounded cost, however long
the block. -/
theorem abs_sum_mul_le_of_abs_sum_Ioc_le (c : ℕ → ℝ) {f : ℝ → ℝ} {y₁ y₂ M : ℝ}
    (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂)
    (hf_diff : ∀ t ∈ Set.Icc y₁ y₂, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc y₁ y₂))
    (hM : ∀ u ∈ Set.Icc y₁ y₂, |∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊, c k| ≤ M) :
    |∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, f k * c k|
      ≤ M * (|f y₂| + ∫ t in y₁..y₂, |deriv f t|) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y₁ ⟨le_rfl, hy⟩)
  have hf_int' : IntervalIntegrable (deriv f) volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hf_int
  have hT : IntervalIntegrable
      (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      (integrableOn_mul_sum_Icc c (m := 0) hy₁ hf_int)
  have hconst : IntervalIntegrable
      (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k) volume y₁ y₂ := hf_int'.mul_const _
  -- the block partial sums are a shift of the full ones, which is what makes them integrable
  have hcongr : (∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊t⌋₊, c k)
      = ∫ t in y₁..y₂, (deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
          - deriv f t * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hy] at ht
    rw [sum_Ioc_eq_sub (Nat.floor_le_floor ht.1) c]
    ring
  have hpt : ∀ t ∈ Set.Icc y₁ y₂,
      |deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k - deriv f t * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k|
        ≤ M * |deriv f t| := by
    intro t ht
    rw [← mul_sub, abs_mul, ← sum_Ioc_eq_sub (Nat.floor_le_floor ht.1) c, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM t ht) (abs_nonneg _)
  have hbound : |∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊t⌋₊, c k|
      ≤ M * ∫ t in y₁..y₂, |deriv f t| := by
    rw [hcongr]
    calc |∫ t in y₁..y₂, (deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
            - deriv f t * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k)|
        ≤ ∫ t in y₁..y₂, |deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
            - deriv f t * ∑ k ∈ Finset.Icc 0 ⌊y₁⌋₊, c k| :=
          intervalIntegral.abs_integral_le_integral_abs hy
      _ ≤ ∫ t in y₁..y₂, M * |deriv f t| :=
          intervalIntegral.integral_mono_on hy (hT.sub hconst).abs
            (hf_int'.abs.const_mul M) hpt
      _ = M * ∫ t in y₁..y₂, |deriv f t| := intervalIntegral.integral_const_mul _ _
  rw [sum_mul_eq_sub_integral_mul_block c hy₁ hy hf_diff hf_int]
  calc |f y₂ * (∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, c k)
        - ∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊t⌋₊, c k|
      ≤ |f y₂ * (∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, c k)|
        + |∫ t in y₁..y₂, deriv f t * ∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊t⌋₊, c k| := abs_sub _ _
    _ ≤ |f y₂| * M + M * ∫ t in y₁..y₂, |deriv f t| := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hM y₂ ⟨hy, le_rfl⟩) (abs_nonneg _)) hbound
    _ = M * (|f y₂| + ∫ t in y₁..y₂, |deriv f t|) := by ring

/-- **Abel summation over a block.**  Subtracting two copies of
`RMF.cos_prime_sum_eq_integral_add` cancels the `2 g 2`, leaving a main term, two boundary
terms and an error integral, all supported on `[y₁, y₂]`. -/
theorem cos_prime_sum_block_eq (τ : ℝ) {y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) :
    ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p
      = (∫ t in y₁..y₂, cosLogDiv τ t)
        + (cosLogDiv τ y₂ * (Chebyshev.theta y₂ - y₂)
          - cosLogDiv τ y₁ * (Chebyshev.theta y₁ - y₁))
        - ∫ t in y₁..y₂, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t) := by
  have hy₂ : (2:ℝ) ≤ y₂ := hy₁.trans hy
  have herr : ∀ {y : ℝ}, 2 ≤ y → IntervalIntegrable
      (fun t => deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)) volume 2 y := fun hyy =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyy).mpr (integrableOn_deriv_mul_sub τ)
  rw [sum_prime_Ioc_eq_sub (Nat.floor_le_floor hy), cos_prime_sum_eq_integral_add τ hy₂,
    cos_prime_sum_eq_integral_add τ hy₁,
    ← intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_cosLogDiv τ le_rfl hy₂) (intervalIntegrable_cosLogDiv τ le_rfl hy₁),
    ← intervalIntegral.integral_interval_sub_left (herr hy₂) (herr hy₁)]
  ring

/-- **The block decorrelation estimate.**  For `0 < τ` and `2 ≤ y₁ ≤ y₂`,

`|∑_{y₁ < p ≤ y₂} cos (τ log p) / p| ≤ 3/(τ log y₁) + 2C/log³y₁ + C(τ+3)/(2 log²y₁)`,

with `C` the prime number theorem constant.  The three terms are the main term, the two
boundary terms and the error integral; only the first fails to decay in `y₁` on its own. -/
theorem abs_cos_prime_sum_block_le {τ C y₁ y₂ : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C)
    (hE : ∀ t : ℝ, y₁ ≤ t → t ≤ y₂ → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ 2)
    (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂) :
    |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
      ≤ 3 / (τ * Real.log y₁) + 2 * C / Real.log y₁ ^ 3
        + C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) := by
  have hy₂ : (2:ℝ) ≤ y₂ := hy₁.trans hy
  have hlog₁ : (0:ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  have hmono : Real.log y₁ ≤ Real.log y₂ := Real.log_le_log (by linarith) hy
  rw [cos_prime_sum_block_eq τ hy₁ hy]
  -- the main term, which does not grow with the block
  have h1 : |∫ t in y₁..y₂, cosLogDiv τ t| ≤ 3 / (τ * Real.log y₁) :=
    abs_integral_cos_log_div_tail_le hτ (by linarith) hy
  -- the two boundary terms
  have h2 : |cosLogDiv τ y₂ * (Chebyshev.theta y₂ - y₂)| ≤ C / Real.log y₁ ^ 3 :=
    (abs_cosLogDiv_mul_sub_le τ hy₂ (hE y₂ hy le_rfl)).trans (by gcongr)
  have h3 : |cosLogDiv τ y₁ * (Chebyshev.theta y₁ - y₁)| ≤ C / Real.log y₁ ^ 3 :=
    abs_cosLogDiv_mul_sub_le τ hy₁ (hE y₁ le_rfl hy)
  -- the error integral
  have h4 : |∫ t in y₁..y₂, deriv (cosLogDiv τ) t * (Chebyshev.theta t - t)|
      ≤ C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) := abs_integral_deriv_mul_sub_le' τ hC hE hy₁ hy
  have hb : 2 * C / Real.log y₁ ^ 3 = C / Real.log y₁ ^ 3 + C / Real.log y₁ ^ 3 := by ring
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;>
    [linarith [h1.1, h2.1, h3.2, h4.2]; linarith [h1.2, h2.2, h3.1, h4.1]]

/-- **The block decorrelation constant**, `3 + 2C/\log^2 2 + 2C/\log 2`, with `C` the constant
of the prime number theorem in the form `|θ(x) - x| ≤ Cx/\log^2 x` (`RS_prime.pnt`).
`RS_prime.pnt` obtains `C` from `MediumPNT`'s `isBigO` together with an `eventually_atTop`
threshold, so it is not effective. -/
noncomputable def blockCosineConst (C : ℝ) : ℝ := 3 + 2 * C / Real.log 2 ^ 2 + 2 * C / Real.log 2

/-- The weighted block constant, `e²` times `RMF.blockCosineConst C`. -/
noncomputable def blockCosineWeightConst (C : ℝ) : ℝ := Real.exp 2 * blockCosineConst C

/-- The block-coordinate constant, `3` times `RMF.blockCosineWeightConst C`.  This is the `K₁`
of `RMF.prop7Window`, hence of the denominator's block offset. -/
noncomputable def blockCosineSubConst (C : ℝ) : ℝ := 3 * blockCosineWeightConst C

lemma blockCosineConst_pos {C : ℝ} (hC : 0 ≤ C) : 0 < blockCosineConst C := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [blockCosineConst]
  positivity

lemma blockCosineWeightConst_pos {C : ℝ} (hC : 0 ≤ C) : 0 < blockCosineWeightConst C := by
  rw [blockCosineWeightConst]
  exact mul_pos (Real.exp_pos 2) (blockCosineConst_pos hC)

lemma blockCosineSubConst_pos {C : ℝ} (hC : 0 ≤ C) : 0 < blockCosineSubConst C := by
  rw [blockCosineSubConst]
  linarith [blockCosineWeightConst_pos hC]

/-- **The block decorrelation estimate with the PNT constant left free.**  If
`|θ(x) - x| ≤ Cx/\log^2 x` for all `x ≥ 2`, then for `0 < τ ≤ 1` and `2 ≤ y₁ ≤ y₂`,
`|∑_{y₁ < p ≤ y₂} cos (τ log p) / p| ≤ RMF.blockCosineConst C / (τ log y₁)`. -/
theorem le_abs_cos_prime_sum_block_of_pnt {C : ℝ} (hC : 0 ≤ C)
    (hpnt : ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * x / Real.log x ^ 2)
    :
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ y₁ y₂ : ℝ, 2 ≤ y₁ → y₁ ≤ y₂ →
    |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
      ≤ blockCosineConst C / (τ * Real.log y₁) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [blockCosineConst]
  intro τ hτ hτ1 y₁ y₂ hy₁ hy
  have hlog₁ : (0:ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  have hmono : Real.log 2 ≤ Real.log y₁ := Real.log_le_log (by norm_num) hy₁
  refine (abs_cos_prime_sum_block_le hτ hC (fun s hs _ => hpnt s (le_trans hy₁ hs)) hy₁ hy).trans ?_
  rw [le_div_iff₀ (by positivity : (0:ℝ) < τ * Real.log y₁), add_mul, add_mul]
  have e1 : 3 / (τ * Real.log y₁) * (τ * Real.log y₁) = 3 := by field_simp
  have e2 : 2 * C / Real.log y₁ ^ 3 * (τ * Real.log y₁) = 2 * C * τ / Real.log y₁ ^ 2 := by
    field_simp
  have e3 : C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) * (τ * Real.log y₁)
      = C * (τ + 3) * τ / (2 * Real.log y₁) := by
    rw [abs_of_pos hτ]; field_simp
  rw [e1, e2, e3]
  have hsq : Real.log 2 ^ 2 ≤ Real.log y₁ ^ 2 := by nlinarith
  have b1 : 2 * C * τ / Real.log y₁ ^ 2 ≤ 2 * C / Real.log 2 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hsq),
      mul_nonneg (mul_nonneg hC (sq_nonneg (Real.log 2))) (sub_nonneg.mpr hτ1)]
  have b2 : C * (τ + 3) * τ / (2 * Real.log y₁) ≤ 2 * C / Real.log 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hmono), mul_nonneg hC (sub_nonneg.mpr hτ1),
      mul_nonneg (mul_nonneg hC hlog2.le) (sub_nonneg.mpr hτ1)]
  linarith

/-- **The block decorrelation estimate past `τ = 1`.**  For `0 < τ` with `τ ^ 2 ≤ log y₁` and
`e ≤ y₁ ≤ y₂`, `|∑_{y₁ < p ≤ y₂} cos (τ log p) / p| ≤ K / (τ log y₁)` with `K` absolute: the
conclusion of `RMF.le_abs_cos_prime_sum_block_of_pnt` with `τ ≤ 1` traded for `τ ^ 2 ≤ log y₁`.
In the application it forces the block offset `D ≥ 2 log(1+|t|)`, whose cost `e^{2D}` the damping
`(|n|+1)^{-1/4}` cannot absorb; the chain uses `RMF.exists_abs_cos_prime_sum_block_le_wide`. -/
theorem exists_abs_cos_prime_sum_block_le' :
    ∃ K > 0, ∀ τ : ℝ, 0 < τ → ∀ y₁ y₂ : ℝ, Real.exp 1 ≤ y₁ → τ ^ 2 ≤ Real.log y₁ → y₁ ≤ y₂ →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ K / (τ * Real.log y₁) := by
  obtain ⟨C, hC, hpnt⟩ := RS_prime.pnt
  refine ⟨3 + 4 * C, by positivity, ?_⟩
  intro τ hτ y₁ y₂ hy₁e hτ2 hy
  have hy₁ : (2 : ℝ) ≤ y₁ := by linarith [Real.exp_one_gt_d9]
  have hL1 : (1 : ℝ) ≤ Real.log y₁ := by
    have h := Real.log_le_log (Real.exp_pos 1) hy₁e
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log y₁ := by linarith
  -- `2τ ≤ τ ^ 2 + 1 ≤ 2 log y₁`
  have hτL : τ ≤ Real.log y₁ := by nlinarith [sq_nonneg (τ - 1)]
  refine (abs_cos_prime_sum_block_le hτ hC (fun s hs _ => hpnt s (le_trans hy₁ hs)) hy₁ hy).trans ?_
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < τ * Real.log y₁), add_mul, add_mul]
  have e1 : 3 / (τ * Real.log y₁) * (τ * Real.log y₁) = 3 := by field_simp
  have e2 : 2 * C / Real.log y₁ ^ 3 * (τ * Real.log y₁) = 2 * C * τ / Real.log y₁ ^ 2 := by
    field_simp
  have e3 : C * (|τ| + 3) / (2 * Real.log y₁ ^ 2) * (τ * Real.log y₁)
      = C * (τ + 3) * τ / (2 * Real.log y₁) := by
    rw [abs_of_pos hτ]; field_simp
  rw [e1, e2, e3]
  have b1 : 2 * C * τ / Real.log y₁ ^ 2 ≤ 2 * C := by
    rw [div_le_iff₀ (by positivity)]
    have hLsq : τ ≤ Real.log y₁ ^ 2 := by
      nlinarith [mul_nonneg hL0.le (by linarith : (0 : ℝ) ≤ Real.log y₁ - 1)]
    nlinarith [mul_nonneg hC (by linarith : (0 : ℝ) ≤ Real.log y₁ ^ 2 - τ)]
  have b2 : C * (τ + 3) * τ / (2 * Real.log y₁) ≤ 2 * C := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hC (by linarith : (0 : ℝ) ≤ 4 * Real.log y₁ - (τ ^ 2 + 3 * τ))]
  linarith

/-! ### The weight `p^{-2σ}`

Harper's kernel carries `p^{-(1+2σ)}`, not `p^{-1}`, and the extra `p^{-2σ}` cannot be pulled
out of a signed sum: splitting it as `1 + (p^{-2σ} - 1)` costs `O(σ log y_2)`, which is `O(1)`
exactly where the target is smallest.  So it goes through the summation as a weight, and by
`RMF.abs_sum_mul_le_of_abs_sum_Ioc_le` that costs only `sup|f| + ∫|f'|`.
-/

/-- `t^{-2σ} ≤ e^{2η}` for `t ≥ 1` as soon as `|σ| log t ≤ η`.  The parameter matters for the
**drift**: at `η = 1` (Harper's `|σ| ≤ 1/log x_j` at the block itself) the weight only sits in
`[e^{-2}, e²]`, but `|σ| ≤ 1/log x_n` is a bound at the **top** scale and
`log x_m/log x_n = e^{m-n}`, so at block `m` one may take `η = e^{m-n}`: the weight is
`1 + O(e^{m-n})`, and `∑_m |θ_m - 1|` is bounded. -/
lemma rpow_neg_two_mul_le_of_le {σ t η : ℝ} (ht : 1 ≤ t) (hσ : |σ| * Real.log t ≤ η) :
    t ^ (-(2 * σ)) ≤ rexp (2 * η) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hlog : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht
  rw [Real.rpow_def_of_pos ht0]
  refine Real.exp_le_exp.2 ?_
  have h2 : -|σ| * Real.log t ≤ σ * Real.log t :=
    mul_le_mul_of_nonneg_right (neg_abs_le σ) hlog
  nlinarith

/-- The case `η = 1`. -/
lemma rpow_neg_two_mul_le {σ t : ℝ} (ht : 1 ≤ t) (hσ : |σ| * Real.log t ≤ 1) :
    t ^ (-(2 * σ)) ≤ rexp 2 := by
  simpa using rpow_neg_two_mul_le_of_le ht hσ

/-- `e^{-2η} ≤ t^{-2σ}`, the companion lower bound to `RMF.rpow_neg_two_mul_le_of_le`.  Together
they confine the tilt weight to `[e^{-2η}, e^{2η}]`. -/
lemma le_rpow_neg_two_mul_of_le {σ t η : ℝ} (ht : 1 ≤ t) (hσ : |σ| * Real.log t ≤ η) :
    rexp (-(2 * η)) ≤ t ^ (-(2 * σ)) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hlog : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht
  rw [Real.rpow_def_of_pos ht0]
  refine Real.exp_le_exp.2 ?_
  have h2 : σ * Real.log t ≤ |σ| * Real.log t :=
    mul_le_mul_of_nonneg_right (le_abs_self σ) hlog
  nlinarith

/-- **The block decorrelation estimate, weighted.**  If the *unweighted* sums over every initial
sub-block `(y₁, u]` are at most `M`, the `p^{-(1+2σ)}` sum is at most `M·e²(1 + 2|σ| log(y₂/y₁))`,
which is at most `3e²·M` under the hypothesis `|σ| log y₂ ≤ 1`.  Only the block's own right endpoint
enters that hypothesis, not a global scale. -/
theorem abs_cos_prime_sum_block_weight_le {τ σ M y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁) (hy : y₁ ≤ y₂)
    (hσ : |σ| * Real.log y₂ ≤ 1)
    (hM : ∀ u ∈ Set.Icc y₁ y₂,
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p| ≤ M) :
    |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
        Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
      ≤ M * (rexp 2 * (1 + 2 * |σ| * Real.log (y₂ / y₁))) := by
  have hy₁0 : (0:ℝ) < y₁ := by linarith
  have hy₂0 : (0:ℝ) < y₂ := by linarith
  set c : ℕ → ℝ := fun k => if k.Prime then Real.cos (τ * Real.log k) / k else 0 with hc
  set f : ℝ → ℝ := fun u => u ^ (-(2 * σ)) with hfdef
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (-(2 * σ) * t ^ (-(2 * σ) - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hdeq : Set.EqOn (deriv f) (fun t => -(2 * σ) * t ^ (-(2 * σ) - 1)) (Set.Icc y₁ y₂) :=
    fun t ht => (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).deriv
  have hf_diff : ∀ t ∈ Set.Icc y₁ y₂, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).differentiableAt
  have hf_int : IntegrableOn (deriv f) (Set.Icc y₁ y₂) := by
    refine (ContinuousOn.congr ?_ hdeq).integrableOn_Icc
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
      Or.inl (lt_of_lt_of_le hy₁0 ht.1).ne')
  have hf_int' : IntervalIntegrable (deriv f) volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hf_int
  have hMc : ∀ u ∈ Set.Icc y₁ y₂, |∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊, c k| ≤ M := by
    intro u hu
    have h := hM u hu
    rwa [Finset.sum_filter] at h
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMc y₁ ⟨le_rfl, hy⟩)
  -- the weighted sum is the Abel sum of `c` against `f`
  have hLHS : (∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, f k * c k)
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · have hk0 : (0:ℝ) < k := by exact_mod_cast hp.pos
      have hpow : (k : ℝ) ^ (1 + 2 * σ) = (k : ℝ) * (k : ℝ) ^ (2 * σ) := by
        rw [Real.rpow_add hk0, Real.rpow_one]
      have hinv : (k : ℝ) ^ (-(2 * σ)) = ((k : ℝ) ^ (2 * σ))⁻¹ := Real.rpow_neg hk0.le _
      have hne : (k : ℝ) ^ (2 * σ) ≠ 0 := (Real.rpow_pos_of_pos hk0 _).ne'
      simp only [hc, hfdef, if_pos hp]
      rw [hpow, hinv]
      field_simp
    · simp only [hc, if_neg hp, mul_zero]
  rw [← hLHS]
  refine (abs_sum_mul_le_of_abs_sum_Ioc_le c hy₁0.le hy hf_diff hf_int hMc).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hM0
  -- the weight is bounded, and its total variation is `2|σ| e² log (y₂/y₁)`
  have hfy₂ : |f y₂| ≤ rexp 2 := by
    rw [hfdef, abs_of_pos (Real.rpow_pos_of_pos hy₂0 _)]
    exact rpow_neg_two_mul_le (by linarith) hσ
  have hptd : ∀ t ∈ Set.Icc y₁ y₂, |deriv f t| ≤ 2 * |σ| * rexp 2 * (1 / t) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hy₁0 ht.1
    have hle : t ^ (-(2 * σ)) ≤ rexp 2 :=
      rpow_neg_two_mul_le (by linarith [ht.1])
        (le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log ht0 ht.2) (abs_nonneg σ)) hσ)
    have hsplit : t ^ (-(2 * σ) - 1) = t ^ (-(2 * σ)) * (1 / t) := by
      rw [Real.rpow_sub ht0, Real.rpow_one, div_eq_mul_one_div]
    have h2s : |(-(2 * σ))| = 2 * |σ| := by rw [abs_neg, abs_mul]; norm_num
    rw [hdeq ht, abs_mul, h2s, hsplit, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos (by positivity : (0:ℝ) < 1 / t)]
    have hkey := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * |σ|)
      (by positivity : (0:ℝ) ≤ 1 / t)) (sub_nonneg.mpr hle)
    nlinarith [hkey]
  have hintbound : (∫ t in y₁..y₂, |deriv f t|) ≤ 2 * |σ| * rexp 2 * Real.log (y₂ / y₁) := by
    calc (∫ t in y₁..y₂, |deriv f t|)
        ≤ ∫ t in y₁..y₂, 2 * |σ| * rexp 2 * (1 / t) :=
          intervalIntegral.integral_mono_on hy hf_int'.abs
            ((intervalIntegrable_one_div hy₁0 hy).const_mul _) hptd
      _ = 2 * |σ| * rexp 2 * ∫ t in y₁..y₂, 1 / t := intervalIntegral.integral_const_mul _ _
      _ = 2 * |σ| * rexp 2 * Real.log (y₂ / y₁) := by
          rw [integral_one_div (zero_notMem_uIcc hy₁0 hy)]
  nlinarith [hfy₂, hintbound]

/-- **The block decorrelation estimate, weighted, at a nonnegative tilt.**  For `σ ≥ 0` the
weight `u^{-2σ}` is nonnegative and *decreasing*, so Abel summation costs nothing: the total
variation telescopes against the boundary term and the weighted sum is at most `M·y₁^{-2σ} ≤ M`.
`RMF.abs_cos_prime_sum_block_weight_le` allows either sign and so pays
`e²(1 + 2|σ|\log(y₂/y₁))`, which is about `17`. -/
theorem abs_cos_prime_sum_block_weight_le_of_nonneg {τ σ M y₁ y₂ : ℝ} (hy₁ : 2 ≤ y₁)
    (hy : y₁ ≤ y₂) (hσ : 0 ≤ σ)
    (hM : ∀ u ∈ Set.Icc y₁ y₂,
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p| ≤ M) :
    |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
        Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)| ≤ M := by
  have hy₁0 : (0:ℝ) < y₁ := by linarith
  have hy₂0 : (0:ℝ) < y₂ := by linarith
  set c : ℕ → ℝ := fun k => if k.Prime then Real.cos (τ * Real.log k) / k else 0 with hc
  set f : ℝ → ℝ := fun u => u ^ (-(2 * σ)) with hfdef
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (-(2 * σ) * t ^ (-(2 * σ) - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hdeq : Set.EqOn (deriv f) (fun t => -(2 * σ) * t ^ (-(2 * σ) - 1)) (Set.Icc y₁ y₂) :=
    fun t ht => (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).deriv
  have hf_diff : ∀ t ∈ Set.Icc y₁ y₂, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t (lt_of_lt_of_le hy₁0 ht.1)).differentiableAt
  have hf_int : IntegrableOn (deriv f) (Set.Icc y₁ y₂) := by
    refine (ContinuousOn.congr ?_ hdeq).integrableOn_Icc
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
      Or.inl (lt_of_lt_of_le hy₁0 ht.1).ne')
  have hf_int' : IntervalIntegrable (deriv f) volume y₁ y₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr hf_int
  have hMc : ∀ u ∈ Set.Icc y₁ y₂, |∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊, c k| ≤ M := by
    intro u hu
    have h := hM u hu
    rwa [Finset.sum_filter] at h
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMc y₁ ⟨le_rfl, hy⟩)
  have hLHS : (∑ k ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, f k * c k)
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · have hk0 : (0:ℝ) < k := by exact_mod_cast hp.pos
      have hpow : (k : ℝ) ^ (1 + 2 * σ) = (k : ℝ) * (k : ℝ) ^ (2 * σ) := by
        rw [Real.rpow_add hk0, Real.rpow_one]
      have hinv : (k : ℝ) ^ (-(2 * σ)) = ((k : ℝ) ^ (2 * σ))⁻¹ := Real.rpow_neg hk0.le _
      have hne : (k : ℝ) ^ (2 * σ) ≠ 0 := (Real.rpow_pos_of_pos hk0 _).ne'
      simp only [hc, hfdef, if_pos hp]
      rw [hpow, hinv]
      field_simp
    · simp only [hc, if_neg hp, mul_zero]
  rw [← hLHS]
  refine (abs_sum_mul_le_of_abs_sum_Ioc_le c hy₁0.le hy hf_diff hf_int hMc).trans ?_
  -- the weight is nonnegative and decreasing, so `|f y₂| + ∫|f'| = f y₁ ≤ 1`
  have hneg : ∀ t ∈ Set.uIcc y₁ y₂, |deriv f t| = -deriv f t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hy₁0 ht.1
    have hle : deriv f t ≤ 0 := by
      rw [hdeq ht]
      have hp : (0:ℝ) ≤ t ^ (-(2 * σ) - 1) := (Real.rpow_pos_of_pos ht0 _).le
      simp only
      nlinarith
    exact abs_of_nonpos hle
  have hFTC : (∫ t in y₁..y₂, deriv f t) = f y₂ - f y₁ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hf_int'
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hy₁0 ht.1
    rw [hdeq ht]
    exact hderiv t ht0
  have hint : (∫ t in y₁..y₂, |deriv f t|) = f y₁ - f y₂ := by
    rw [intervalIntegral.integral_congr hneg, intervalIntegral.integral_neg, hFTC]
    ring
  have hfy₂0 : (0:ℝ) < f y₂ := Real.rpow_pos_of_pos hy₂0 _
  have hfy₁1 : f y₁ ≤ 1 := by
    rw [hfdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  rw [hint, abs_of_pos hfy₂0]
  nlinarith [hfy₁1, hfy₂0, hM0]

/-- **`RMF.exists_abs_cos_prime_sum_block_weight_le` with the PNT constant left free.** -/
theorem le_abs_cos_prime_sum_block_weight_of_block {C : ℝ} (hC : 0 ≤ C)
    (hbound :
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ y₁ y₂ : ℝ, 2 ≤ y₁ → y₁ ≤ y₂ →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ blockCosineConst C / (τ * Real.log y₁)) :
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ σ y₁ y₂ : ℝ, 2 ≤ y₁ → y₁ ≤ y₂ →
      |σ| * Real.log y₂ ≤ 1 →
    |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
        Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
      ≤ blockCosineWeightConst C * (1 + 2 * |σ| * Real.log (y₂ / y₁)) / (τ * Real.log y₁) := by
  set K : ℝ := blockCosineConst C with hKdef
  have hK : (0 : ℝ) < K := blockCosineConst_pos hC
  rw [blockCosineWeightConst, ← hKdef]
  intro τ hτ hτ1 σ y₁ y₂ hy₁ hy hσ
  have hlog₁ : (0:ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  refine (abs_cos_prime_sum_block_weight_le hy₁ hy hσ
    (fun u hu => hbound τ hτ hτ1 y₁ u hy₁ hu.1)).trans (le_of_eq ?_)
  field_simp

/-- **The weighted block decorrelation estimate.**  For `0 < τ ≤ 1`, `2 ≤ y₁ ≤ y₂` and
`|σ| log y₂ ≤ 1`: `|∑_{y₁<p≤y₂} cos (τ log p) / p^{1+2σ}| ≤ K (1 + 2|σ| log(y₂/y₁)) / (τ log y₁)`
with `K` absolute; the numerator is at most `3K`, so the weighted block sum is `O(1/(τ log y₁))`.
The unweighted bound `RMF.le_abs_cos_prime_sum_block_of_pnt` depends on `y₁` alone, so one `M`
serves every sub-block `(y₁, u]`, as `RMF.abs_cos_prime_sum_block_weight_le` asks. -/
theorem exists_abs_cos_prime_sum_block_weight_le :
    ∃ K > 0, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ σ y₁ y₂ : ℝ, 2 ≤ y₁ → y₁ ≤ y₂ →
        |σ| * Real.log y₂ ≤ 1 →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
        ≤ K * (1 + 2 * |σ| * Real.log (y₂ / y₁)) / (τ * Real.log y₁) := by
  obtain ⟨C, hC, hpnt⟩ := RS_prime.pnt
  exact ⟨blockCosineWeightConst C, blockCosineWeightConst_pos hC,
    le_abs_cos_prime_sum_block_weight_of_block hC (le_abs_cos_prime_sum_block_of_pnt hC hpnt)⟩

/-- The weighted form of `RMF.exists_abs_cos_prime_sum_block_le'`: the same statement as
`RMF.exists_abs_cos_prime_sum_block_weight_le` with `τ ≤ 1` traded for `τ ^ 2 ≤ log y₁`.

The sub-interval hypothesis is discharged at the *same* `y₁` for every `u ∈ [y₁, y₂]`, so the new
hypothesis transfers unchanged — which is why the proof is the unprimed one verbatim. -/
theorem exists_abs_cos_prime_sum_block_weight_le' :
    ∃ K > 0, ∀ τ : ℝ, 0 < τ → ∀ σ y₁ y₂ : ℝ, Real.exp 1 ≤ y₁ → τ ^ 2 ≤ Real.log y₁ → y₁ ≤ y₂ →
        |σ| * Real.log y₂ ≤ 1 →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
        ≤ K * (1 + 2 * |σ| * Real.log (y₂ / y₁)) / (τ * Real.log y₁) := by
  obtain ⟨K, hK, hbound⟩ := exists_abs_cos_prime_sum_block_le'
  refine ⟨rexp 2 * K, by positivity, ?_⟩
  intro τ hτ σ y₁ y₂ hy₁e hτ2 hy hσ
  have hy₁ : (2 : ℝ) ≤ y₁ := by linarith [Real.exp_one_gt_d9]
  have hlog₁ : (0 : ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  refine (abs_cos_prime_sum_block_weight_le hy₁ hy hσ
    (fun u hu => hbound τ hτ y₁ u hy₁e hτ2 hu.1)).trans (le_of_eq ?_)
  field_simp

/-! ### Restatement over `primesBelow`

The Euler-product development indexes prime sums by `Nat.primesBelow y` (`p < y`, `y : ℕ`),
whereas Chebyshev's functions, Mertens' theorem and the estimate above are indexed by `p ≤ x`
with `x` real.  Mathlib's `Nat.primesLE` mediates, since `primesLE n` is by definition
`primesBelow (n + 1)`, and equals `{p ≤ n : p prime}`.
-/

lemma primesBelow_succ_eq_filter_Icc (n : ℕ) :
    Nat.primesBelow (n + 1) = {p ∈ Finset.Icc 0 n | p.Prime} :=
  Nat.primesLE_eq_filter_Icc_zero n

lemma primesBelow_succ_eq_filter_Ioc (n : ℕ) :
    Nat.primesBelow (n + 1) = {p ∈ Finset.Ioc 0 n | p.Prime} := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨⟨hp.pos, by omega⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨by omega, hp⟩

/-- **The cosine prime sum**, indexed as in the Euler-product development. -/
theorem exists_abs_cos_primesBelow_sub_log_min_le :
    ∃ B > 0, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ N : ℕ, 2 ≤ N →
      |∑ p ∈ Nat.primesBelow (N + 1), Real.cos (τ * Real.log p) / p
        - Real.log (min (Real.log N) (1 / τ) / Real.log 2)| ≤ B := by
  obtain ⟨B, hB, h⟩ := exists_abs_cos_prime_sum_sub_log_min_le
  refine ⟨B, hB, fun τ hτ hτ1 N hN => ?_⟩
  have hx : (2:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hres := h τ hτ hτ1 (N : ℝ) hx
  rwa [Nat.floor_natCast, ← primesBelow_succ_eq_filter_Icc] at hres

/-- **Mertens' second theorem**, indexed as in the Euler-product development. -/
theorem exists_abs_sum_primesBelow_inv_sub_log_log_le :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N →
      |∑ p ∈ Nat.primesBelow (N + 1), ((p : ℝ))⁻¹ - Real.log (Real.log N)| ≤ C := by
  obtain ⟨C, h⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨|C| + 1, by positivity, fun N hN => ?_⟩
  have hx : (2:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hres := h (N : ℝ) hx
  rw [Nat.floor_natCast, ← primesBelow_succ_eq_filter_Ioc] at hres
  simp only [one_div] at hres
  exact hres.trans (by linarith [le_abs_self C])

/-- **A prime product with harmonic-sized factors is `≪ (log y)^c`.**  Each factor obeys
`1 + a p ≤ exp (a p)`, and `∑_{p ≤ y} a p ≤ c ∑_{p ≤ y} 1/p ≤ c(log log y + 1.42)` by Mertens
(`RMF.sum_primesBelow_inv_le_log_log_add`, threshold-free).  The per-factor bound is a hypothesis
so that both applications can use it — the smooth tail (`a p = p^(δ-1) ≤ e/p`, `c = e`) and the far
range of the line integral (`a p = p^(-1-2σ) ≤ 1/p`, `c = 1`) — which are incomparable in the import
order, so the lemma lives here, beside Mertens. -/
theorem exists_prod_one_add_le_rpow_log :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y → ∀ c : ℝ, 0 ≤ c → ∀ a : ℕ → ℝ,
      (∀ p ∈ Nat.primesBelow (y + 1), 0 ≤ a p) →
      (∀ p ∈ Nat.primesBelow (y + 1), a p ≤ c * ((p : ℝ))⁻¹) →
      ∏ p ∈ Nat.primesBelow (y + 1), (1 + a p) ≤ Real.exp (c * C) * (Real.log y) ^ c := by
  refine ⟨1.42, by norm_num, ?_⟩
  intro y hy c hc a ha0 hale
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  calc ∏ p ∈ Nat.primesBelow (y + 1), (1 + a p)
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), Real.exp (a p) :=
        Finset.prod_le_prod (fun p hp => by linarith [ha0 p hp])
          (fun p _ => by linarith [Real.add_one_le_exp (a p)])
    _ = Real.exp (∑ p ∈ Nat.primesBelow (y + 1), a p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (c * (Real.log (Real.log y) + 1.42)) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : ∑ p ∈ Nat.primesBelow (y + 1), a p
            ≤ ∑ p ∈ Nat.primesBelow (y + 1), c * ((p : ℝ))⁻¹ := Finset.sum_le_sum hale
        rw [← Finset.mul_sum] at h1
        have h2 : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
            ≤ Real.log (Real.log y) + 1.42 := sum_primesBelow_inv_le_log_log_add hy
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hc)
    _ = Real.exp (c * 1.42) * (Real.log y) ^ c := by
        rw [Real.rpow_def_of_pos hlogy, ← Real.exp_add]
        ring_nf

end RMF
