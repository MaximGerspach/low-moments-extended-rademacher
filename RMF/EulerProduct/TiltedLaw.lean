/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import RMF.EulerProduct.Moments
import RMF.EulerProduct.Tilted

/-!
# The tilted Steinhaus law

Harper's tilt reweights the value at each prime by `‖1 - z p ^ (-1/2-σ)‖ ^ (-2)`.  Under that
reweighting the uniform law on the circle becomes the **Poisson kernel** at radius `‖a‖`, and this
file computes its Fourier coefficients:

`∫ z ^ d ∂(steinhausLaw.tilted (2 · localLog a)) = conj a ^ d`.

Everything the Gaussian comparison needs about the tilted local law — the mean, the variance, the
third absolute moment — is a series in these coefficients, so this is the one computation the rest
rests on.

## Why it matters that the law is tilted

Under `steinhausLaw` itself the local mean is **exactly zero**
(`RMF.integral_localLog_eq_zero`).  Under the tilt it is not: with `a = p ^ (-1/2-σ)` the tilt
radius and `w = p ^ (-1/2-σ-it)` the observable, the mean of `localLog w` becomes
`≈ cos (t log p) / p ^ (1+2σ)`, and summing over a block of primes gives the drift of `+1` per
increment that produces the `+j` in Harper's upper barrier.  Reaching for the plain-law lemma here
would silently delete that drift, and the proof would still compile.

Note also that the tilt radius `a` and the observable `w` have the same modulus but different
phase, and that phase difference is the entire source of the `cos (t log p)`.

## The computation

On the circle `‖(1 - z a)⁻¹‖ ^ 2 = (1 - z a)⁻¹ · conj ((1 - z a)⁻¹)`, and expanding both factors
geometrically turns the integral into `∑_{j,k} a ^ j conj a ^ k ∫ z ^ (d+j) conj (z ^ k)`.  The
characters are orthonormal (`RMF.integral_pow_mul_conj_steinhausLaw`), so only `k = d + j`
survives, leaving `conj a ^ d ∑_j ‖a‖ ^ (2j) = conj a ^ d / (1 - ‖a‖ ^ 2)`.  Dividing by the
normalising constant `(1 - ‖a‖ ^ 2)⁻¹`
(`RMF.integral_norm_inv_one_sub_mul_sq_steinhausLaw`) leaves `conj a ^ d`.

This is the same argument as `RMF.integral_inv_one_sub_mul_conj_steinhausLaw`, which is the case
`d = 0` with two different radii, and it is written to mirror it.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The weighted moments of the Steinhaus law -/

/-- The truncated bilinear form with a character `z ^ d` inserted.  Orthogonality leaves only the
pairs `k = d + j`, and the truncation cuts them off at `j < n - d`. -/
lemma integral_pow_mul_geom_sum_mul_conj_steinhausLaw (a : ℂ) (d n : ℕ) :
    (∫ z, z ^ d * ((∑ j ∈ Finset.range n, (z * a) ^ j)
        * (starRingEnd ℂ) (∑ k ∈ Finset.range n, (z * a) ^ k)) ∂steinhausLaw)
      = ∑ j ∈ Finset.range (n - d), a ^ j * (starRingEnd ℂ) (a ^ (d + j)) := by
  have hpt : ∀ z : ℂ, z ^ d * ((∑ j ∈ Finset.range n, (z * a) ^ j)
      * (starRingEnd ℂ) (∑ k ∈ Finset.range n, (z * a) ^ k))
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          (a ^ j * (starRingEnd ℂ) (a ^ k)) * (z ^ (d + j) * (starRingEnd ℂ) (z ^ k)) := by
    intro z
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_pow, map_mul, map_pow, pow_add]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    ((integrable_pow_mul_conj_steinhausLaw (d + j) k).const_mul _)]
  have hinner : ∀ j : ℕ, (∫ z, ∑ k ∈ Finset.range n,
      (a ^ j * (starRingEnd ℂ) (a ^ k)) * (z ^ (d + j) * (starRingEnd ℂ) (z ^ k)) ∂steinhausLaw)
      = if d + j ∈ Finset.range n then a ^ j * (starRingEnd ℂ) (a ^ (d + j)) else 0 := by
    intro j
    rw [integral_finsetSum _ fun k _ =>
      ((integrable_pow_mul_conj_steinhausLaw (d + j) k).const_mul _)]
    simp_rw [integral_const_mul, integral_pow_mul_conj_steinhausLaw, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq _ _ _
  simp_rw [hinner]
  have hsub : Finset.range (n - d) ⊆ Finset.range n := Finset.range_mono (Nat.sub_le n d)
  have hzero : ∀ j ∈ Finset.range n, j ∉ Finset.range (n - d) →
      (if d + j ∈ Finset.range n then a ^ j * (starRingEnd ℂ) (a ^ (d + j)) else 0) = 0 := by
    intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    exact if_neg (by simp only [Finset.mem_range]; omega)
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  exact if_pos (by simp only [Finset.mem_range]; omega)

/-- **The weighted characters of the Steinhaus law.**
`∫ z ^ d ‖(1 - z a)⁻¹‖ ^ 2 = conj a ^ d / (1 - ‖a‖ ^ 2)`.  The case `d = 0` is
`RMF.integral_norm_inv_one_sub_mul_sq_steinhausLaw`. -/
theorem integral_pow_mul_inv_one_sub_mul_conj_steinhausLaw {a : ℂ} (ha : ‖a‖ < 1) (d : ℕ) :
    (∫ z, z ^ d * ((1 - z * a)⁻¹ * (starRingEnd ℂ) ((1 - z * a)⁻¹)) ∂steinhausLaw)
      = (starRingEnd ℂ) (a ^ d) * (1 - a * (starRingEnd ℂ) a)⁻¹ := by
  have ha0 : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have hprod : ‖a * (starRingEnd ℂ) a‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith
  have hlim : Filter.Tendsto
      (fun n => ∫ z, z ^ d * ((∑ j ∈ Finset.range n, (z * a) ^ j)
        * (starRingEnd ℂ) (∑ k ∈ Finset.range n, (z * a) ^ k)) ∂steinhausLaw) Filter.atTop
      (nhds (∫ z, z ^ d * ((1 - z * a)⁻¹ * (starRingEnd ℂ) ((1 - z * a)⁻¹)) ∂steinhausLaw)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 - ‖a‖)⁻¹ * (1 - ‖a‖)⁻¹)
      (fun n => by fun_prop) (integrable_const _) (fun n => ?_) ?_
    · filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_pow, hz, one_pow, one_mul]
      exact mul_le_mul (norm_geom_sum_le_steinhausLaw ha hz n)
        (norm_geom_sum_le_steinhausLaw ha hz n) (norm_nonneg _) (by positivity)
    · filter_upwards [norm_eq_one_steinhausLaw] with z hz
      have hza : ‖z * a‖ < 1 := by rw [norm_mul, hz, one_mul]; exact ha
      exact (tendsto_const_nhds).mul
        (((hasSum_geometric_of_norm_lt_one hza).tendsto_sum_nat).mul
          ((Complex.continuous_conj.tendsto _).comp
            ((hasSum_geometric_of_norm_lt_one hza).tendsto_sum_nat)))
  refine tendsto_nhds_unique hlim ?_
  simp_rw [integral_pow_mul_geom_sum_mul_conj_steinhausLaw]
  have hterm : ∀ j : ℕ, a ^ j * (starRingEnd ℂ) (a ^ (d + j))
      = (starRingEnd ℂ) (a ^ d) * (a * (starRingEnd ℂ) a) ^ j := by
    intro j
    simp only [pow_add, map_mul, map_pow, mul_pow]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  refine Filter.Tendsto.const_mul _ ?_
  refine ((hasSum_geometric_of_norm_lt_one hprod).tendsto_sum_nat).comp ?_
  exact Filter.tendsto_atTop_atTop.2 fun b => ⟨b + d, fun n hn => by omega⟩

/-! ### The tilted law -/

/-- The tilt exponent in closed form: `exp (2 · localLog a z) = ‖(1 - z a)⁻¹‖ ^ 2` on the circle.
Pointwise, so it survives any change of measure. -/
lemma exp_two_localLog_eq {a z : ℂ} (hz : ‖z‖ = 1) (ha : ‖a‖ < 1) :
    Real.exp (2 * localLog a z) = ‖(1 - z * a)⁻¹‖ ^ 2 := by
  obtain ⟨hlow, -⟩ := norm_one_sub_mul_bounds (w := a) hz
  have h1 : (0 : ℝ) < 1 - ‖a‖ := by linarith [norm_nonneg a]
  have hpos : 0 < ‖1 - z * a‖ := by linarith
  rw [norm_inv, inv_pow, localLog,
    show (2 : ℝ) * -Real.log ‖1 - z * a‖ = -Real.log (‖1 - z * a‖ ^ 2) by
      rw [Real.log_pow]; push_cast; ring,
    Real.exp_neg, Real.exp_log (pow_pos hpos 2)]

/-- The tilt weight is bounded on the circle by `(1 - ‖a‖)⁻²`. -/
lemma exp_two_localLog_le {a z : ℂ} (hz : ‖z‖ = 1) (ha : ‖a‖ < 1) :
    Real.exp (2 * localLog a z) ≤ ((1 - ‖a‖)⁻¹) ^ 2 := by
  rw [exp_two_localLog_eq hz ha, norm_inv]
  obtain ⟨hlow, -⟩ := norm_one_sub_mul_bounds (w := a) hz
  have h1 : (0 : ℝ) < 1 - ‖a‖ := by linarith [norm_nonneg a]
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ h1 hlow) 2

/-- The closed form, a.e. for `steinhausLaw`. -/
lemma exp_two_localLog_ae_eq {a : ℂ} (ha : ‖a‖ < 1) :
    (fun z => Real.exp (2 * localLog a z))
      =ᵐ[steinhausLaw] fun z => ‖(1 - z * a)⁻¹‖ ^ 2 := by
  filter_upwards [norm_eq_one_steinhausLaw] with z hz
  exact exp_two_localLog_eq hz ha

/-- **The Fourier coefficients of the tilted Steinhaus law.**  Tilting the uniform law on the
circle by `‖1 - z a‖ ^ (-2)` turns it into the Poisson kernel at `a`, whose `d`-th moment is
`conj a ^ d`.

This is the computation the tilted local moments — mean, variance, third absolute moment — are
all series in. -/
theorem integral_pow_tilted_steinhausLaw {a : ℂ} (ha : ‖a‖ < 1) (d : ℕ) :
    (∫ z, z ^ d ∂(steinhausLaw.tilted fun z => 2 * localLog a z))
      = (starRingEnd ℂ) (a ^ d) := by
  have hZ : (∫ z, Real.exp (2 * localLog a z) ∂steinhausLaw) = (1 - ‖a‖ ^ 2 : ℝ)⁻¹ := by
    rw [integral_congr_ae (exp_two_localLog_ae_eq ha),
      integral_norm_inv_one_sub_mul_sq_steinhausLaw ha]
  have hZpos : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  rw [integral_tilted, hZ]
  calc (∫ z, (Real.exp (2 * localLog a z) / (1 - ‖a‖ ^ 2 : ℝ)⁻¹) • (z ^ d) ∂steinhausLaw)
      = ∫ z, ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)
          * (z ^ d * ((1 - z * a)⁻¹ * (starRingEnd ℂ) ((1 - z * a)⁻¹))) ∂steinhausLaw := by
        refine integral_congr_ae ?_
        filter_upwards [exp_two_localLog_ae_eq ha] with z hz
        rw [hz, div_eq_mul_inv, inv_inv, Complex.real_smul, Complex.ofReal_mul,
          show ((‖(1 - z * a)⁻¹‖ ^ 2 : ℝ) : ℂ)
            = (1 - z * a)⁻¹ * (starRingEnd ℂ) ((1 - z * a)⁻¹) by
              rw [Complex.ofReal_pow, ← Complex.mul_conj']]
        ring
    _ = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)
          * ∫ z, z ^ d * ((1 - z * a)⁻¹ * (starRingEnd ℂ) ((1 - z * a)⁻¹)) ∂steinhausLaw :=
        integral_const_mul _ _
    _ = (starRingEnd ℂ) (a ^ d) := by
        rw [integral_pow_mul_inv_one_sub_mul_conj_steinhausLaw ha d, Complex.mul_conj']
        have hne : (1 : ℂ) - (‖a‖ : ℂ) ^ 2 ≠ 0 := by
          have h := Complex.ofReal_ne_zero.2 (ne_of_gt hZpos)
          push_cast at h
          exact h
        push_cast
        field_simp

/-! ### The tilted local mean

The drift.  Under `steinhausLaw` the local mean is exactly zero
(`RMF.integral_localLog_eq_zero`); under the tilt it is not, and the difference is what produces
the `+ j` in Harper's upper barrier.

The computation is the Poisson kernel reproducing a harmonic function: the map
`ζ ↦ -log ‖1 - ζ w‖` is harmonic on the disc and the tilt is the Poisson kernel centred at
`conj a`, so the mean is its value there.  In Lean it is the series `-log (1 - v) = ∑ vⁿ/n`
integrated term by term against `RMF.integral_pow_tilted_steinhausLaw`.  Only the real part of the
series is ever integrated, so `Complex.log` never enters an integrand and no measurability
question about it arises. -/

/-- The tilt weight is bounded on the circle, so the tilt is a probability measure. -/
lemma integrable_exp_two_localLog {a : ℂ} (ha : ‖a‖ < 1) :
    Integrable (fun z => Real.exp (2 * localLog a z)) steinhausLaw := by
  refine (memLp_top_of_bound ?_ (((1 - ‖a‖)⁻¹) ^ 2) ?_).integrable le_top
  · exact ((measurable_localLog a).const_mul 2).exp.aestronglyMeasurable
  · filter_upwards [norm_eq_one_steinhausLaw] with z hz1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact exp_two_localLog_le hz1 ha

lemma isProbabilityMeasure_tilted_localLog {a : ℂ} (ha : ‖a‖ < 1) :
    IsProbabilityMeasure (steinhausLaw.tilted fun z => 2 * localLog a z) :=
  isProbabilityMeasure_tilted (integrable_exp_two_localLog ha)

/-- **The tilted local mean.**  `E[localLog w] = -log ‖1 - w conj a‖` under the tilt by
`‖(1 - z a)⁻¹‖ ^ 2`.  Exact, with no error term. -/
theorem integral_localLog_tilted_steinhausLaw {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    (∫ z, localLog w z ∂(steinhausLaw.tilted fun z => 2 * localLog a z))
      = -Real.log ‖1 - w * (starRingEnd ℂ) a‖ := by
  have hprob := isProbabilityMeasure_tilted_localLog ha
  set ν := steinhausLaw.tilted fun z => 2 * localLog a z with hνdef
  have hcirc : ∀ᵐ z ∂ν, ‖z‖ = 1 :=
    (tilted_absolutelyContinuous steinhausLaw _) norm_eq_one_steinhausLaw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hnormterm : ∀ (n : ℕ) (z : ℂ), ‖z‖ = 1 → ‖(z * w) ^ n / (n : ℂ)‖ ≤ ‖w‖ ^ n := by
    intro n z hz
    rw [norm_div, norm_pow, norm_mul, hz, one_mul, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_iff₀ (by exact_mod_cast hn)]
      nlinarith [pow_nonneg hw0 n, (Nat.one_le_cast (α := ℝ)).2 hn]
  have hterm : ∀ (n : ℕ) (z : ℂ), ‖z‖ = 1 → |((z * w) ^ n / (n : ℂ)).re| ≤ ‖w‖ ^ n :=
    fun n z hz => (Complex.abs_re_le_norm _).trans (hnormterm n z hz)
  have hintegrable : ∀ n : ℕ, Integrable (fun z : ℂ => ((z * w) ^ n / (n : ℂ)).re) ν := by
    intro n
    refine (integrable_const (‖w‖ ^ n)).mono' (by fun_prop) ?_
    filter_upwards [hcirc] with z hz
    rw [Real.norm_eq_abs]
    exact hterm n z hz
  have hintegrableC : ∀ n : ℕ, Integrable (fun z : ℂ => (z * w) ^ n / (n : ℂ)) ν := by
    intro n
    refine (integrable_const (‖w‖ ^ n)).mono' (by fun_prop) ?_
    filter_upwards [hcirc] with z hz
    exact hnormterm n z hz
  have hbdd : ∀ N : ℕ, ∀ᵐ z ∂ν,
      ‖∑ n ∈ Finset.range N, ((z * w) ^ n / (n : ℂ)).re‖ ≤ (1 - ‖w‖)⁻¹ := by
    intro N
    filter_upwards [hcirc] with z hz
    rw [Real.norm_eq_abs]
    calc |∑ n ∈ Finset.range N, ((z * w) ^ n / (n : ℂ)).re|
        ≤ ∑ n ∈ Finset.range N, |((z * w) ^ n / (n : ℂ)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range N, ‖w‖ ^ n := Finset.sum_le_sum fun n _ => hterm n z hz
      _ ≤ (1 - ‖w‖)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hw0 hw]
          exact (summable_geometric_of_lt_one hw0 hw).sum_le_tsum _ fun _ _ => by positivity
  have hpartial : ∀ N : ℕ, (∫ z, ∑ n ∈ Finset.range N, ((z * w) ^ n / (n : ℂ)).re ∂ν)
      = ∑ n ∈ Finset.range N, ((w * (starRingEnd ℂ) a) ^ n / (n : ℂ)).re := by
    intro N
    rw [integral_finsetSum _ fun n _ => hintegrable n]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hC : (∫ z, (z * w) ^ n / (n : ℂ) ∂ν) = (w * (starRingEnd ℂ) a) ^ n / (n : ℂ) := by
      rw [show (fun z : ℂ => (z * w) ^ n / (n : ℂ))
          = fun z : ℂ => (w ^ n / (n : ℂ)) * z ^ n by funext z; rw [mul_pow]; ring,
        integral_const_mul, integral_pow_tilted_steinhausLaw ha n, map_pow, mul_pow]
      ring
    rw [show (fun z : ℂ => ((z * w) ^ n / (n : ℂ)).re)
      = fun z : ℂ => RCLike.re ((z * w) ^ n / (n : ℂ)) from rfl, integral_re (hintegrableC n), hC]
    rfl
  have hlim : Filter.Tendsto
      (fun N => ∫ z, ∑ n ∈ Finset.range N, ((z * w) ^ n / (n : ℂ)).re ∂ν) Filter.atTop
      (nhds (∫ z, localLog w z ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 - ‖w‖)⁻¹)
      (fun N => by fun_prop) (integrable_const _) hbdd ?_
    filter_upwards [hcirc] with z hz
    have hzw : ‖z * w‖ < 1 := by rw [norm_mul, hz, one_mul]; exact hw
    have h := (Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hzw)).tendsto_sum_nat
    simpa [localLog, Complex.log_re] using h
  have hsum : Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N, ((w * (starRingEnd ℂ) a) ^ n / (n : ℂ)).re) Filter.atTop
      (nhds (-Real.log ‖1 - w * (starRingEnd ℂ) a‖)) := by
    have hv : ‖w * (starRingEnd ℂ) a‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg a, norm_nonneg w]
    have h := (Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hv)).tendsto_sum_nat
    simpa [Complex.log_re] using h
  simp only [hpartial] at hlim
  exact tendsto_nhds_unique hlim hsum

/-- **The drift, in the form Harper uses.**  `E[localLog w] = Re (w conj a) + O((‖w‖‖a‖) ^ 2)`.
With `a = p ^ (-1/2-σ)` the tilt radius and `w = p ^ (-1/2-σ-it)` the observable, the main term is
`cos (t log p) / p ^ (1+2σ)`, which summed over a block of primes is the `+ 1` of drift per
increment.  The error is fourth order in `p ^ (-1/2-σ)`, so it is dominated by the third-moment
sum the Gaussian comparison already pays for. -/
theorem abs_integral_localLog_tilted_sub_re_le {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    |(∫ z, localLog w z ∂(steinhausLaw.tilted fun z => 2 * localLog a z))
        - (w * (starRingEnd ℂ) a).re|
      ≤ ‖w * (starRingEnd ℂ) a‖ ^ 2 * (1 - ‖w * (starRingEnd ℂ) a‖)⁻¹ / 2 := by
  have hv : ‖w * (starRingEnd ℂ) a‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg w]
  rw [integral_localLog_tilted_steinhausLaw ha hw,
    show -Real.log ‖1 - w * (starRingEnd ℂ) a‖
      = (Complex.log (1 - w * (starRingEnd ℂ) a)⁻¹).re by
      rw [Complex.log_re, norm_inv, Real.log_inv],
    ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (Complex.norm_log_one_sub_inv_sub_self_le hv)

/-! ### The tilted local second moment

The other half of what Harper's `N_j` is defined by.  The first-order expansion
`localLog w z = Re (z w) + O(‖w‖ ^ 2)` (`RMF.abs_localLog_sub_re_le`) is pointwise on the circle,
so it survives the tilt unchanged; squaring it and integrating against the second Fourier
coefficient leaves `‖w‖ ^ 2 / 2` with a third-order error.

Third order is the right target.  The main term is `‖w‖ ^ 2 / 2 = 1/(2 p ^ (1+2σ))`, so the error is
smaller by a factor `p ^ (-1/2-σ)`, and summed over a block it is the prime tail
`∑ p ^ (-3/2)` that `RMF.sum_prime_Ioc_rpow_le` bounds. -/

/-- The polarisation that turns a squared real part into Fourier coefficients of order `2`
and `0`: `(Re v) ^ 2 = (Re (v ^ 2) + ‖v‖ ^ 2) / 2`. -/
lemma re_sq_eq (v : ℂ) : (v.re) ^ 2 = ((v ^ 2).re + ‖v‖ ^ 2) / 2 := by
  rw [pow_two v, Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The pointwise bound on `localLog` that squaring needs. -/
lemma abs_localLog_le_of_norm_le {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1 / 5) :
    |localLog w z| ≤ 11 / 5 * ‖w‖ := by
  have hre : |(z * w).re| ≤ ‖w‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  have h := abs_localLog_sub_re_le hz hw
  have habs := abs_sub_abs_le_abs_sub (localLog w z) ((z * w).re)
  nlinarith [norm_nonneg w]

/-- **The tilted local second moment.**  `E[(localLog w) ^ 2] = ‖w‖ ^ 2 / 2 + O(‖w‖ ^ 3)`, the
second of the two parameters Harper's comparison Gaussian is defined by. -/
theorem abs_integral_localLog_sq_tilted_sub_le {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ z, localLog w z ^ 2 ∂(steinhausLaw.tilted fun z => 2 * localLog a z)) - ‖w‖ ^ 2 / 2|
      ≤ 20 * ‖w‖ ^ 3 + ‖w‖ ^ 2 * ‖a‖ ^ 2 / 2 := by
  have hprob := isProbabilityMeasure_tilted_localLog ha
  set ν := steinhausLaw.tilted fun z => 2 * localLog a z with hνdef
  have hcirc : ∀ᵐ z ∂ν, ‖z‖ = 1 :=
    (tilted_absolutelyContinuous steinhausLaw _) norm_eq_one_steinhausLaw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hmeas2 : Measurable (fun z : ℂ => localLog w z ^ 2) := (measurable_localLog w).pow_const 2
  -- the squared first-order approximation, pointwise
  have hpt : ∀ᵐ z ∂ν, |localLog w z ^ 2 - ((z ^ 2 * w ^ 2).re + ‖w‖ ^ 2) / 2| ≤ 20 * ‖w‖ ^ 3 := by
    filter_upwards [hcirc] with z hz
    have hre : |(z * w).re| ≤ ‖w‖ :=
      (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
    have hsq : ((z * w).re) ^ 2 = ((z ^ 2 * w ^ 2).re + ‖w‖ ^ 2) / 2 := by
      rw [re_sq_eq (z * w), mul_pow, norm_mul, hz, one_mul]
    rw [← hsq, show localLog w z ^ 2 - ((z * w).re) ^ 2
      = (localLog w z - (z * w).re) * (localLog w z + (z * w).re) by ring, abs_mul]
    have hdiff := abs_localLog_sub_re_le hz hw
    have hbnd := abs_localLog_le_of_norm_le hz hw
    have h1 : |localLog w z + (z * w).re| ≤ 16 / 5 * ‖w‖ := by
      refine (abs_add_le _ _).trans ?_
      linarith
    calc |localLog w z - (z * w).re| * |localLog w z + (z * w).re|
        ≤ (6 * ‖w‖ ^ 2) * (16 / 5 * ‖w‖) :=
          mul_le_mul hdiff h1 (abs_nonneg _) (by positivity)
      _ ≤ 20 * ‖w‖ ^ 3 := by nlinarith
  -- integrability
  have hint2 : Integrable (fun z : ℂ => localLog w z ^ 2) ν := by
    refine (integrable_const ((11 / 5 * ‖w‖) ^ 2)).mono' hmeas2.aestronglyMeasurable ?_
    filter_upwards [hcirc] with z hz
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_localLog_le_of_norm_le hz hw) 2
  have hintC : Integrable (fun z : ℂ => z ^ 2 * w ^ 2) ν := by
    refine (integrable_const (‖w‖ ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hcirc] with z hz
    rw [norm_mul, norm_pow, norm_pow, hz, one_pow, one_mul]
  have hintR : Integrable (fun z : ℂ => ((z ^ 2 * w ^ 2).re + ‖w‖ ^ 2) / 2) ν :=
    ((hintC.re).add (integrable_const _)).div_const 2
  -- the mean of the approximation
  have hintCre : Integrable (fun z : ℂ => (z ^ 2 * w ^ 2).re) ν := hintC.re
  have hIC : (∫ z, z ^ 2 * w ^ 2 ∂ν) = w ^ 2 * ((starRingEnd ℂ) a) ^ 2 := by
    rw [show (fun z : ℂ => z ^ 2 * w ^ 2) = fun z : ℂ => w ^ 2 * z ^ 2 by funext z; ring,
      integral_const_mul, integral_pow_tilted_steinhausLaw ha 2, map_pow]
  have hI : (∫ z, (z ^ 2 * w ^ 2).re ∂ν) = (w ^ 2 * ((starRingEnd ℂ) a) ^ 2).re := by
    rw [show (fun z : ℂ => (z ^ 2 * w ^ 2).re) = fun z : ℂ => RCLike.re (z ^ 2 * w ^ 2) from rfl,
      integral_re hintC, hIC]
    rfl
  have hmean : (∫ z, ((z ^ 2 * w ^ 2).re + ‖w‖ ^ 2) / 2 ∂ν)
      = ((w ^ 2 * ((starRingEnd ℂ) a) ^ 2).re + ‖w‖ ^ 2) / 2 := by
    rw [integral_div, integral_add hintCre (integrable_const _), hI]
    simp
  -- compare
  have hcomp : |(∫ z, localLog w z ^ 2 ∂ν)
      - ((w ^ 2 * ((starRingEnd ℂ) a) ^ 2).re + ‖w‖ ^ 2) / 2| ≤ 20 * ‖w‖ ^ 3 := by
    rw [← hmean, ← integral_sub hint2 hintR]
    refine abs_integral_le_integral_abs.trans ?_
    calc (∫ z, |localLog w z ^ 2 - ((z ^ 2 * w ^ 2).re + ‖w‖ ^ 2) / 2| ∂ν)
        ≤ ∫ _z : ℂ, 20 * ‖w‖ ^ 3 ∂ν :=
          integral_mono_of_nonneg (.of_forall fun _ => abs_nonneg _) (integrable_const _) hpt
      _ = 20 * ‖w‖ ^ 3 := by simp
  have hsmall : |(w ^ 2 * ((starRingEnd ℂ) a) ^ 2).re| ≤ ‖w‖ ^ 2 * ‖a‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans_eq ?_
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj]
  rw [show (∫ z, localLog w z ^ 2 ∂ν) - ‖w‖ ^ 2 / 2
      = ((∫ z, localLog w z ^ 2 ∂ν) - ((w ^ 2 * ((starRingEnd ℂ) a) ^ 2).re + ‖w‖ ^ 2) / 2)
        + (w ^ 2 * ((starRingEnd ℂ) a) ^ 2).re / 2 by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-! ### The third absolute moment

The quantity the Lindeberg error is a sum of.  `localLog w` has no singularity on the circle for
`‖w‖ < 1`, so the third moment is bounded by the cube of the pointwise bound; summed over a block
of primes it is the prime tail `∑ p ^ (-3/2)`. -/

/-- Under the tilted law, `localLog w` is a.e. bounded by `11‖w‖/5`: the law is absolutely
continuous with respect to `steinhausLaw`, which lives on the circle, and there
`RMF.abs_localLog_le_of_norm_le` applies. -/
lemma ae_abs_localLog_le_tilted {a w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    ∀ᵐ z ∂(steinhausLaw.tilted fun z => 2 * localLog a z), |localLog w z| ≤ 11 / 5 * ‖w‖ := by
  have hcirc : ∀ᵐ z ∂(steinhausLaw.tilted fun z => 2 * localLog a z), ‖z‖ = 1 :=
    (tilted_absolutelyContinuous steinhausLaw _) norm_eq_one_steinhausLaw
  filter_upwards [hcirc] with z hz
  exact abs_localLog_le_of_norm_le hz hw

/-- **Every absolute moment of a local term is finite under the tilt.**  It is a.e. bounded by
`11‖w‖/5`, so nothing beyond that bound is needed — no tail estimate, at any order.

The telescope consumes `p = 1, 2, 3`: the first two to match moments, the third as the swap
error. -/
lemma integrable_abs_pow_localLog_tilted {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) (p : ℕ) :
    Integrable (fun z => |localLog w z| ^ p)
      (steinhausLaw.tilted fun z => 2 * localLog a z) := by
  have hprob := isProbabilityMeasure_tilted_localLog ha
  have hm : Measurable fun z : ℂ => |localLog w z| ^ p := by
    simp only [← Real.norm_eq_abs]
    exact ((measurable_localLog w).norm).pow_const p
  refine (integrable_const ((11 / 5 * ‖w‖) ^ p)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_abs_localLog_le_tilted (a := a) hw] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (abs_nonneg _) hz p

/-- The *square* of a local term is integrable under the tilt — the moment the swap matches. -/
lemma integrable_localLog_mul_self_tilted {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLog w z * localLog w z)
      (steinhausLaw.tilted fun z => 2 * localLog a z) := by
  have h := integrable_abs_pow_localLog_tilted ha hw 2
  refine h.congr ?_
  filter_upwards with z
  rw [pow_two, abs_mul_abs_self]

/-- `localLog w` is integrable against the tilted law — it is a.e. bounded and the law is a
probability measure. -/
lemma integrable_localLog_tilted {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (localLog w) (steinhausLaw.tilted fun z => 2 * localLog a z) := by
  have hprob := isProbabilityMeasure_tilted_localLog ha
  refine (integrable_const (11 / 5 * ‖w‖)).mono'
    (measurable_localLog w).aestronglyMeasurable ?_
  filter_upwards [ae_abs_localLog_le_tilted (a := a) hw] with z hz
  rwa [Real.norm_eq_abs]

/-- **The third absolute moment of a local term** under the tilt: `E|localLog w| ^ 3 ≤ (11/5) ^ 3
‖w‖ ^ 3`.  Pointwise on the circle, hence valid under the tilt exactly as under the plain law. -/
theorem integral_abs_localLog_cube_tilted_le {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1 / 5) :
    (∫ z, |localLog w z| ^ 3 ∂(steinhausLaw.tilted fun z => 2 * localLog a z))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  have hprob := isProbabilityMeasure_tilted_localLog ha
  set ν := steinhausLaw.tilted fun z => 2 * localLog a z with hνdef
  have hcirc : ∀ᵐ z ∂ν, ‖z‖ = 1 :=
    (tilted_absolutelyContinuous steinhausLaw _) norm_eq_one_steinhausLaw
  have hpt : ∀ᵐ z ∂ν, |localLog w z| ^ 3 ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    filter_upwards [hcirc] with z hz
    calc |localLog w z| ^ 3 ≤ (11 / 5 * ‖w‖) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_localLog_le_of_norm_le hz hw) 3
      _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  have hint : Integrable (fun z : ℂ => |localLog w z| ^ 3) ν := by
    have hm : Measurable (fun z : ℂ => |localLog w z| ^ 3) := by
      simp only [← Real.norm_eq_abs]
      exact ((measurable_localLog w).norm).pow_const 3
    refine (integrable_const ((11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [hpt] with z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (∫ z, |localLog w z| ^ 3 ∂ν) ≤ ∫ _z : ℂ, (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 ∂ν :=
        integral_mono_of_nonneg (.of_forall fun _ => by positivity) (integrable_const _) hpt
    _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by simp

end RMF
