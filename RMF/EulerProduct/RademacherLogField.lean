/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.LogField

/-!
# The Rademacher log-field

The Rademacher local factor is the polynomial `1 + X_p p ^ (-s)`, so

`log ‖F_y(s)‖ = ∑_{p < y} log ‖1 + X_p p ^ (-s)‖`,

and this file computes the first two moments of a summand under the Rademacher law.  Both are
easier than their Steinhaus counterparts, because the law has two atoms: every integral is a
two-term average, and the covariance of *any* two functions is available in closed form,

`cov(g, h) = (g 1 - g (-1)) (h 1 - h (-1)) / 4`,

so the whole local analysis reduces to a single one-variable estimate on the increment
`g 1 - g (-1)`.

## What differs from the Steinhaus model

* **The mean does not cancel.**  For Steinhaus the local mean vanishes exactly
  (`RMF.integral_localLog_eq_zero`).  Here the mean is
  `E localLogAdd w = ‖w‖ ^ 2 / 2 - (Re w) ^ 2 + O(‖w‖ ^ 3)`, genuinely of order `‖w‖ ^ 2`.  At
  `w = p ^ (-s)` this is `-cos(2 (Im s) log p) p ^ (-2 Re s) / 2`, so the field has a *drift*
  `E log ‖F_y‖ = -½ ∑_{p<y} cos(2 t log p) p ^ (-2σ) + O(1)`, of size `log log y` near the
  real axis, where the Steinhaus field is exactly centred.
* **The covariance carries a reflection.**  `E [Re(z w₁) Re(z w₂)] = Re w₁ · Re w₂` here, against
  `Re (w₁ conj w₂) / 2` for Steinhaus — no factor `1/2`, because `z ^ 2 = 1`.  The
  product-to-sum identity then splits it as
  `½ p ^ (-2σ) [cos((t₁ - t₂) log p) + cos((t₁ + t₂) log p)]`: the kernel sees both the
  difference *and* the sum of the two heights.

The reason is visible before any computation.  The Rademacher coefficients are real, so
`conj (F_y s) = F_y (conj s)` and therefore `‖F_y(½ + it)‖ = ‖F_y(½ - it)‖` identically.  The
field is an *even* function of the height: a log-correlated field folded at the origin, whose
correlation at `(t₁, t₂)` must see the distance to the reflected point as well.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The local log-variable -/

/-- The contribution of one prime to `log ‖F_y(s)‖` in the Rademacher model,
`localLogAdd w z = log ‖1 + z w‖`, with `w = p ^ (-s)` and `z = ±1` the value at `p`. -/
noncomputable def localLogAdd (w : ℂ) (z : ℂ) : ℝ := Real.log ‖1 + z * w‖

lemma measurable_localLogAdd (w : ℂ) : Measurable (localLogAdd w) :=
  Real.measurable_log.comp (by fun_prop : Measurable fun z : ℂ => ‖1 + z * w‖)

/-- `localLogAdd` is the Steinhaus local variable at the reflected point. -/
lemma localLogAdd_eq_neg_localLog (w z : ℂ) : localLogAdd w z = -localLog (-w) z := by
  simp [localLogAdd, localLog, mul_neg, sub_neg_eq_add]

/-- The crude bound, valid throughout `‖w‖ ≤ θ < 1`. -/
lemma abs_localLogAdd_le {w z : ℂ} {θ : ℝ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ θ) (hθ : θ < 1) :
    |localLogAdd w z| ≤ Real.log ((1 - θ)⁻¹) := by
  rw [localLogAdd_eq_neg_localLog, abs_neg]
  exact abs_localLog_le hz (by rwa [norm_neg]) hθ

/-- On the circle, `localLogAdd` is a function of `2 Re (z w) + ‖w‖ ^ 2` alone. -/
lemma localLogAdd_eq (w : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    localLogAdd w z = Real.log (1 + (2 * (z * w).re + ‖w‖ ^ 2)) / 2 := by
  rw [localLogAdd, show (1 : ℝ) + (2 * (z * w).re + ‖w‖ ^ 2)
      = 1 + 2 * (z * w).re + ‖w‖ ^ 2 by ring, ← norm_one_add_mul_sq_eq hz, Real.log_pow]
  push_cast
  ring

/-- The value at the atom `+1`. -/
lemma localLogAdd_one (w : ℂ) :
    localLogAdd w 1 = Real.log (1 + (2 * w.re + ‖w‖ ^ 2)) / 2 := by
  rw [localLogAdd_eq w (by simp), one_mul]

/-- The value at the atom `-1`. -/
lemma localLogAdd_neg_one (w : ℂ) :
    localLogAdd w (-1) = Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2)) / 2 := by
  have h : ((-1 : ℂ) * w).re = -w.re := by simp
  rw [localLogAdd_eq w (by simp), h, show 2 * -w.re = -(2 * w.re) by ring]

/-! ### The two one-variable estimates

Writing `a = Re w` and `r = ‖w‖`, the two atoms give `log (1 + x_±) / 2` with
`x_± = ±2a + r ^ 2`.  Expanding `log (1 + x) = x - x ^ 2 / 2 + O(|x| ^ 3)` and combining:

* the **difference** has `x₊ - x₋ = 4a` and `x₊ ^ 2 - x₋ ^ 2 = 8 a r ^ 2`, giving
  `2a + O(r ^ 3)`;
* the **sum** has `x₊ + x₋ = 2 r ^ 2` and `x₊ ^ 2 + x₋ ^ 2 = 8 a ^ 2 + 2 r ^ 4`, giving
  `r ^ 2 / 2 - a ^ 2 + O(r ^ 3)`.
-/

/-- `log (1 + x) = x - x ^ 2 / 2 + O(|x| ^ 3)` for `|x| ≤ 1/2`. -/
private lemma abs_log_one_add_sub_quadratic_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3 := by
  have h := abs_neg_log_one_sub_sub_le (w := -x) (by rwa [abs_neg])
  rw [show (1 : ℝ) - -x = 1 + x by ring,
    show -Real.log (1 + x) - (-x + (-x) ^ 2 / 2)
      = -(Real.log (1 + x) - (x - x ^ 2 / 2)) by ring, abs_neg, abs_neg] at h
  exact h

/-- Both atoms give an argument `x_± = ±2a + r ^ 2` of size at most `11 r / 5`. -/
private lemma abs_two_mul_add_sq_le {a r : ℝ} (hr : 0 ≤ r) (har : |a| ≤ r) (hr5 : r ≤ 1 / 5) :
    |2 * a + r ^ 2| ≤ 11 / 5 * r ∧ |-(2 * a) + r ^ 2| ≤ 11 / 5 * r := by
  constructor
  · have h := abs_add_le (2 * a) (r ^ 2)
    rw [abs_mul, abs_two, abs_pow, abs_of_nonneg hr] at h
    nlinarith
  · have h := abs_add_le (-(2 * a)) (r ^ 2)
    rw [abs_neg, abs_mul, abs_two, abs_pow, abs_of_nonneg hr] at h
    nlinarith

/-- The quadratic expansion of `log (1 + x)`, in the form the two atoms need. -/
private lemma abs_log_sub_quadratic_le_of_le {x r : ℝ} (hr : 0 ≤ r) (hx : |x| ≤ 11 / 5 * r)
    (hr5 : r ≤ 1 / 5) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 22 * r ^ 3 := by
  have h := abs_log_one_add_sub_quadratic_le (x := x) (by nlinarith)
  have hc : |x| ^ 3 ≤ (11 / 5 * r) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hx 3
  nlinarith [pow_nonneg hr 3]

/-- **The increment**, in real variables: `x₊ - x₋ = 4a` and `x₊ ^ 2 - x₋ ^ 2 = 8 a r ^ 2`. -/
private lemma abs_log_diff_sub_le {a r : ℝ} (hr : 0 ≤ r) (har : |a| ≤ r) (hr5 : r ≤ 1 / 5) :
    |(Real.log (1 + (2 * a + r ^ 2)) - Real.log (1 + (-(2 * a) + r ^ 2))) / 2 - 2 * a|
      ≤ 24 * r ^ 3 := by
  obtain ⟨hxp, hxm⟩ := abs_two_mul_add_sq_le hr har hr5
  have hp := abs_log_sub_quadratic_le_of_le hr hxp hr5
  have hm := abs_log_sub_quadratic_le_of_le hr hxm hr5
  have hdrift : |2 * a * r ^ 2| ≤ 2 * r ^ 3 := by
    rw [abs_mul, abs_mul, abs_two, abs_pow, abs_of_nonneg hr]
    nlinarith
  rw [abs_le] at hp hm hdrift ⊢
  constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2, hdrift.1, hdrift.2]

/-- **The mean**, in real variables: `x₊ + x₋ = 2 r ^ 2` and
`x₊ ^ 2 + x₋ ^ 2 = 8 a ^ 2 + 2 r ^ 4`. -/
private lemma abs_log_sum_sub_le {a r : ℝ} (hr : 0 ≤ r) (har : |a| ≤ r) (hr5 : r ≤ 1 / 5) :
    |(Real.log (1 + (2 * a + r ^ 2)) + Real.log (1 + (-(2 * a) + r ^ 2))) / 4
        - (r ^ 2 / 2 - a ^ 2)| ≤ 12 * r ^ 3 := by
  obtain ⟨hxp, hxm⟩ := abs_two_mul_add_sq_le hr har hr5
  have hp := abs_log_sub_quadratic_le_of_le hr hxp hr5
  have hm := abs_log_sub_quadratic_le_of_le hr hxm hr5
  have hquartic : r ^ 4 ≤ r ^ 3 / 5 := by nlinarith [pow_nonneg hr 3]
  have hq0 : (0 : ℝ) ≤ r ^ 4 := by positivity
  rw [abs_le] at hp hm ⊢
  constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]

/-! ### The local moments

Because the law has two atoms, both moments come straight from the two one-variable estimates
above, with no integrability or measurability side conditions at all.
-/

/-- **The local increment.**  `localLogAdd w 1 - localLogAdd w (-1) = 2 Re w + O(‖w‖ ^ 3)`. -/
lemma abs_localLogAdd_diff_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |(localLogAdd w 1 - localLogAdd w (-1)) - 2 * w.re| ≤ 24 * ‖w‖ ^ 3 := by
  rw [localLogAdd_one, localLogAdd_neg_one,
    show Real.log (1 + (2 * w.re + ‖w‖ ^ 2)) / 2 - Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2)) / 2
      = (Real.log (1 + (2 * w.re + ‖w‖ ^ 2))
          - Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2))) / 2 by ring]
  exact abs_log_diff_sub_le (norm_nonneg w) (Complex.abs_re_le_norm w) hw

/-- **The local mean.**  `E localLogAdd w = ‖w‖ ^ 2 / 2 - (Re w) ^ 2 + O(‖w‖ ^ 3)`.

Unlike the Steinhaus model the quadratic term does **not** cancel: `E localLog = 0` there
(`RMF.integral_localLog_eq_zero`), whereas here the mean is genuinely of order `‖w‖ ^ 2`, and
summed over the primes it produces a drift of size `log log y`. -/
lemma abs_integral_localLogAdd_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLogAdd w z ∂rademacherLaw) - (‖w‖ ^ 2 / 2 - w.re ^ 2)| ≤ 12 * ‖w‖ ^ 3 := by
  rw [integral_rademacherLaw_eq, smul_eq_mul, localLogAdd_one, localLogAdd_neg_one,
    show (2 : ℝ)⁻¹ * (Real.log (1 + (2 * w.re + ‖w‖ ^ 2)) / 2
        + Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2)) / 2)
      = (Real.log (1 + (2 * w.re + ‖w‖ ^ 2))
          + Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2))) / 4 by ring]
  exact abs_log_sum_sub_le (norm_nonneg w) (Complex.abs_re_le_norm w) hw

/-! ### The field -/

/-- **The field is a sum of independent local terms.** -/
lemma logNormEuler_ae_eq_sum_rademacher {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    logNormEuler (fun ω => squarefreeExtension fun p => X p ω) y s
      =ᵐ[μ] fun ω => ∑ p ∈ Nat.primesBelow y, localLogAdd ((p : ℂ) ^ (-s)) (X p ω) := by
  have hrmf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw y] with ω hnorm
  have hpos : ∀ p ∈ Nat.primesBelow y,
      (0 : ℝ) < ‖1 + (squarefreeExtension fun q => X q ω) p * (p : ℂ) ^ (-s)‖ := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    rw [squarefreeExtension_apply_prime _ hprime]
    have hw : ‖(p : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one hprime hs
    have h := norm_sub_norm_le (1 : ℂ) (-(X p ω * (p : ℂ) ^ (-s)))
    rw [norm_one, norm_neg, norm_mul, sub_neg_eq_add] at h
    nlinarith [hnorm p hp, norm_nonneg (X p ω), norm_nonneg ((p : ℂ) ^ (-s))]
  rw [logNormEuler, hrmf.randomEulerProduct_eq y s ω, norm_prod,
    Real.log_prod fun p hp => (hpos p hp).ne']
  exact Finset.sum_congr rfl fun p hp => by
    rw [squarefreeExtension_apply_prime _ (Nat.prime_of_mem_primesBelow hp), localLogAdd]

/-- The field is a.e. measurable, being a.e. equal to a finite sum of measurable functions. -/
lemma IsRademacherRMF.aemeasurable_logNormEuler {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    AEMeasurable (logNormEuler f y s) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  refine AEMeasurable.congr ?_ (logNormEuler_ae_eq_sum_rademacher hX y hs).symm
  exact (Finset.measurable_sum _ fun p hp => (measurable_localLogAdd _).comp
    (hX.measurable p (Nat.prime_of_mem_primesBelow hp))).aemeasurable

/-! ### The prime sums

Two trigonometric identities turn the local main terms into classical prime sums.  For the
mean, `cos ^ 2 θ = (1 + cos 2θ)/2` makes the `‖w‖ ^ 2 / 2` cancel and leaves a *single*
oscillatory sum at twice the height.  For the covariance, the product-to-sum identity splits
`cos(t₁ L) cos(t₂ L)` into the difference and the sum of the heights.
-/

/-- The mean's main term at a prime: `‖w‖ ^ 2 / 2 - (Re w) ^ 2 = -cos(2 t log p) p ^ (-2σ) / 2`. -/
lemma localMean_prime_eq {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ ^ 2 / 2 - ((p : ℂ) ^ (-s)).re ^ 2
      = -((p : ℝ) ^ (-2 * s.re) * Real.cos (2 * (s.im * Real.log p)) / 2) := by
  have hsq : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
    rw [rpow_neg_pow (by positivity : (0 : ℝ) ≤ (p : ℝ))]; norm_num
  rw [norm_prime_cpow_neg_sq hp, re_natCast_cpow_neg hp.pos, mul_pow, hsq,
    Real.cos_sq (s.im * Real.log p)]
  ring

/-- The covariance's main term at a prime, split into the two kernels. -/
lemma re_mul_re_prime_eq {p : ℕ} (hp : p.Prime) (s₁ s₂ : ℂ) :
    ((p : ℂ) ^ (-s₁)).re * ((p : ℂ) ^ (-s₂)).re
      = (p : ℝ) ^ (-(s₁.re + s₂.re))
        * (Real.cos ((s₁.im - s₂.im) * Real.log p)
            + Real.cos ((s₁.im + s₂.im) * Real.log p)) / 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpow : (p : ℝ) ^ (-(s₁.re + s₂.re)) = (p : ℝ) ^ (-s₁.re) * (p : ℝ) ^ (-s₂.re) := by
    rw [show -(s₁.re + s₂.re) = -s₁.re + -s₂.re by ring, Real.rpow_add hp0]
  have hcos : Real.cos (s₁.im * Real.log p) * Real.cos (s₂.im * Real.log p)
      = (Real.cos ((s₁.im - s₂.im) * Real.log p)
          + Real.cos ((s₁.im + s₂.im) * Real.log p)) / 2 := by
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  rw [re_natCast_cpow_neg hp.pos, re_natCast_cpow_neg hp.pos, hpow]
  rw [show (p : ℝ) ^ (-s₁.re) * Real.cos (s₁.im * Real.log p)
        * ((p : ℝ) ^ (-s₂.re) * Real.cos (s₂.im * Real.log p))
      = (p : ℝ) ^ (-s₁.re) * (p : ℝ) ^ (-s₂.re)
        * (Real.cos (s₁.im * Real.log p) * Real.cos (s₂.im * Real.log p)) by ring, hcos]
  ring

end RMF
