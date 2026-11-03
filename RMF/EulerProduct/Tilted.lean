/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.LogField
import RMF.Probability.Tilting

/-!
# The tilted measure

Harper's Girsanov-type argument runs not under the law of the Steinhaus random multiplicative
function but under an exponential tilt of it: for `y = ⌈x ^ (1 / e)⌉` and `s = 1/2 + σ` with
`|σ| ≤ 1/100`,

`P~(A) = E[1_A · ∏_{p < y} ‖1 - f p · p ^ (-s)‖ ^ (-2)] / E[∏_{p < y} ‖1 - f p · p ^ (-s)‖ ^ (-2)]`,

which is the tilt of `μ` by `2 log ‖F_y(s)‖` (`RMF.tiltExponent`), so
`MeasureTheory.Measure.tilted` is definitionally the right object.  This file supplies the
finiteness that makes the tilt a probability measure, and the display above with the weight in
the explicit form `W = ‖F_y(s)‖ ^ 2`.

The tilt exponent and the tilted measure are generic in the multiplicative function, so the
`RMF.IsRademacherRMF` face of each result sits beside its Steinhaus twin; the law- and prime-level
Rademacher arguments are in `RMF/EulerProduct/RademacherTiltedLaw.lean` and
`RMF/EulerProduct/RademacherTiltedPrimes.lean`.

## Main results

* `RMF.IsSteinhausRMF.integrable_norm_randomEulerProduct_sq`: the weight is integrable;
* `RMF.IsSteinhausRMF.isProbabilityMeasure_tiltedMeasure`: so the tilt is a probability measure;
* `RMF.IsSteinhausRMF.tiltedMeasure_apply`: the display, `P~(A) = E[1_A W] / E[W]`;
* `RMF.tiltedMeasure_eq_tilted_sum`: the tilt exponent as a sum over the primes of functions of the
  individual values, the shape `RMF.iIndepFun_tilted_finsetSum` and
  `RMF.map_tilted_finsetSum_of_mem` consume.

## The weight

There is no pointwise control on `dP~/dP`, and Harper never bounds it: all the control is on the
law of the increments under the tilt (`RMF/Probability/Tilting.lean`).  A Bochner integral has a
junk value, so `RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq` is not finiteness; that
comes from the crude bound `‖F_y(s)‖ ≤ ∏_{p < y} (1 - ‖p ^ (-s)‖)⁻¹`, exponential in `√y` on the
critical line.  Lean's `Real.log 0 = 0` makes `exp (2 log ‖z‖) = ‖z‖ ^ 2` false at `z = 0`, so the
weight is identified with the exponential only off the null set where the Euler product vanishes
(`RMF.IsSteinhausRMF.ae_randomEulerProduct_ne_zero`).
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The Euler product is bounded, non-vanishing and square integrable -/

/-- The ambient measure of a Steinhaus random multiplicative function is a probability measure. -/
lemma IsSteinhausRMF.isProbabilityMeasure (hf : IsSteinhausRMF f μ) : IsProbabilityMeasure μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact hX.isProbabilityMeasure

/-- The ambient measure of a Rademacher random multiplicative function is a probability
measure. -/
lemma IsRademacherRMF.isProbabilityMeasure (hf : IsRademacherRMF f μ) :
    IsProbabilityMeasure μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact hX.isProbabilityMeasure

/-- **A deterministic bound on the Steinhaus Euler product.**  Each local factor has modulus at
most `(1 - ‖p ^ (-s)‖)⁻¹`, since `‖1 - z w‖ ≥ 1 - ‖w‖` for `‖z‖ ≤ 1`.  The bound is very lossy;
it is used only to get integrability. -/
lemma IsSteinhausRMF.ae_norm_randomEulerProduct_le (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    ∀ᵐ ω ∂μ, ‖randomEulerProduct f y s ω‖
      ≤ ∏ p ∈ Nat.primesBelow y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw y] with ω hω
  rw [randomEulerProduct_compMult_eq hs hω, norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hs
  have hlow : 1 - ‖(p : ℂ) ^ (-s)‖ ≤ ‖1 - X p ω * (p : ℂ) ^ (-s)‖ := by
    have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
    have h2 := norm_sub_norm_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
    rw [norm_one] at h2
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hlow

/-- **The Steinhaus Euler product does not vanish.**  Each local factor is an inverse, and the
element inverted has modulus at least `1 - ‖p ^ (-s)‖ > 0`. -/
lemma IsSteinhausRMF.ae_randomEulerProduct_ne_zero (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) : ∀ᵐ ω ∂μ, randomEulerProduct f y s ω ≠ 0 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw y] with ω hω
  rw [randomEulerProduct_compMult_eq hs hω]
  refine Finset.prod_ne_zero_iff.2 fun p hp => inv_ne_zero fun hzero => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hs
  have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
  have h2 := norm_sub_norm_le (1 : ℂ) (X p ω * (p : ℂ) ^ (-s))
  rw [norm_one, hzero, norm_zero] at h2
  linarith

/-- **The Rademacher Euler product does not vanish.**  Each local factor is `1 + f p·p^{-s}` with
`‖f p·p^{-s}‖ ≤ ‖p^{-s}‖ < 1`, so no factor can be zero.  The Steinhaus counterpart is
`RMF.IsSteinhausRMF.ae_randomEulerProduct_ne_zero`, where the factors are inverses instead. -/
lemma IsRademacherRMF.ae_randomEulerProduct_ne_zero (hf : IsRademacherRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) : ∀ᵐ ω ∂μ, randomEulerProduct f y s ω ≠ 0 := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw y] with ω hω
  rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  refine Finset.prod_ne_zero_iff.2 fun p hp hzero => ?_
  have hw : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hs
  have h1 : ‖X p ω * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hω p hp)
  have h2 := norm_sub_norm_le (1 : ℂ) (-(X p ω * (p : ℂ) ^ (-s)))
  rw [norm_one, norm_neg, show (1 : ℂ) - -(X p ω * (p : ℂ) ^ (-s))
    = 1 + X p ω * (p : ℂ) ^ (-s) by ring, hzero, norm_zero] at h2
  linarith

/-- The Euler product is a.e. measurable, being a.e. equal to a finite product of measurable
functions. -/
lemma IsSteinhausRMF.aemeasurable_randomEulerProduct (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) : AEMeasurable (randomEulerProduct f y s) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hae : randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y s
      =ᵐ[μ] fun ω => ∏ p ∈ Nat.primesBelow y, (1 - X p ω * (p : ℂ) ^ (-s))⁻¹ := by
    filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw y] with ω hω
    exact randomEulerProduct_compMult_eq hs hω
  refine AEMeasurable.congr ?_ hae.symm
  refine (Finset.measurable_prod _ fun p hp => ?_).aemeasurable
  have hm : Measurable (X p) := hX.measurable p (Nat.prime_of_mem_primesBelow hp)
  exact ((hm.mul measurable_const).const_sub 1).inv

/-- **The weight is integrable.**  `RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq`
evaluates `E ‖F_y(s)‖ ^ 2`; this is the other half — that the value is not the junk value of a
divergent integral. -/
theorem IsSteinhausRMF.integrable_norm_randomEulerProduct_sq (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun ω => ‖randomEulerProduct f y s ω‖ ^ 2) μ := by
  have := hf.isProbabilityMeasure
  have hmeas : AEStronglyMeasurable (fun ω => ‖randomEulerProduct f y s ω‖ ^ 2) μ :=
    ((hf.aemeasurable_randomEulerProduct y hs).norm.pow_const 2).aestronglyMeasurable
  refine (memLp_top_of_bound hmeas
    ((∏ p ∈ Nat.primesBelow y, (1 - ‖(p : ℂ) ^ (-s)‖)⁻¹) ^ 2) ?_).integrable le_top
  filter_upwards [hf.ae_norm_randomEulerProduct_le y hs] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hω 2

/-- **The Rademacher weight is integrable.**
`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_sq` evaluates `E ‖F_y(s)‖²`; this shows the
value is not the junk value of a divergent integral.  Unlike the Steinhaus counterpart it needs no
hypothesis on `s`: the bound `∏ (1 + ‖p^{-s}‖)` is finite for every `s`, where
`∏ (1 - ‖p^{-s}‖)⁻¹` needs `0 < Re s`. -/
theorem IsRademacherRMF.integrable_norm_randomEulerProduct_sq (hf : IsRademacherRMF f μ) (y : ℕ)
    (s : ℂ) : Integrable (fun ω => ‖randomEulerProduct f y s ω‖ ^ 2) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hpt : ∀ ω, randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω
      = ∏ p ∈ Nat.primesBelow y, (1 + X p ω * ((p : ℕ) : ℂ) ^ (-s)) := fun ω => by
    rw [randomEulerProduct, eulerProduct_squarefreeExtension]
  have hmeas : AEStronglyMeasurable
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2)
      μ := by
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hpt]
    refine ((Finset.measurable_prod _ fun p hp => ?_).norm).pow_const 2
    exact ((hX.measurable p (Nat.prime_of_mem_primesBelow hp)).mul_const _).const_add 1
  refine (memLp_top_of_bound hmeas
    ((∏ p ∈ Nat.primesBelow y, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖)) ^ 2) ?_).integrable le_top
  filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw y] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [hpt ω, norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, norm_mul]
  have := mul_le_of_le_one_left (norm_nonneg (((p : ℕ) : ℂ) ^ (-s))) (hω p hp)
  linarith

/-! ### The tilt -/

/-- **Harper's tilt exponent** `2 log ‖F_y(s)‖`.  In §3.2 the tilt is taken with
`y = ⌈x ^ (1 / e)⌉` and `s = 1/2 + σ`, `|σ| ≤ 1/100`; nothing below needs more than
`0 < Re s`. -/
noncomputable def tiltExponent (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ) (ω : Ω) : ℝ :=
  2 * logNormEuler f y s ω

/-- **The tilted measure `P~`**, `μ.tilted (tiltExponent f y s)`: `μ` reweighted by
`exp (2 log ‖F_y(s)‖)` and normalised.  The weight is a.e. `‖F_y(s)‖ ^ 2`, for Steinhaus
`∏_{p < y} ‖1 - f p · p ^ (-s)‖ ^ (-2)`. -/
noncomputable def tiltedMeasure (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ) (μ : Measure Ω) :
    Measure Ω :=
  μ.tilted (tiltExponent f y s)

/-- **The weight in closed form.**  `exp (2 log ‖z‖) = ‖z‖ ^ 2` fails at `z = 0`, Lean's
`Real.log 0` being `0`, so this is an almost-everywhere identity. -/
lemma IsSteinhausRMF.exp_tiltExponent_ae_eq (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    (fun ω => Real.exp (tiltExponent f y s ω))
      =ᵐ[μ] fun ω => ‖randomEulerProduct f y s ω‖ ^ 2 := by
  filter_upwards [hf.ae_randomEulerProduct_ne_zero y hs] with ω hω
  have hpos : 0 < ‖randomEulerProduct f y s ω‖ := norm_pos_iff.2 hω
  rw [tiltExponent, logNormEuler, show (2 : ℝ) * Real.log ‖randomEulerProduct f y s ω‖
    = Real.log (‖randomEulerProduct f y s ω‖ ^ 2) by rw [Real.log_pow]; norm_num]
  exact Real.exp_log (pow_pos hpos 2)

/-- **The tilt weight in closed form.**  `exp (2 log ‖z‖) = ‖z‖²` fails at `z = 0`, so this is an
almost-everywhere identity, exactly as on the Steinhaus side. -/
lemma IsRademacherRMF.exp_tiltExponent_ae_eq (hf : IsRademacherRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    (fun ω => Real.exp (tiltExponent f y s ω))
      =ᵐ[μ] fun ω => ‖randomEulerProduct f y s ω‖ ^ 2 := by
  filter_upwards [hf.ae_randomEulerProduct_ne_zero y hs] with ω hω
  have hpos : 0 < ‖randomEulerProduct f y s ω‖ := norm_pos_iff.2 hω
  rw [tiltExponent, logNormEuler, show (2 : ℝ) * Real.log ‖randomEulerProduct f y s ω‖
    = Real.log (‖randomEulerProduct f y s ω‖ ^ 2) by rw [Real.log_pow]; norm_num]
  exact Real.exp_log (pow_pos hpos 2)

/-- **The finiteness that makes the tilt legitimate**: `E exp (2 log ‖F_y(s)‖)` is finite, being
`E ‖F_y(s)‖ ^ 2`.  This is exactly the hypothesis of
`MeasureTheory.isProbabilityMeasure_tilted`. -/
theorem IsSteinhausRMF.integrable_exp_tiltExponent (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) : Integrable (fun ω => Real.exp (tiltExponent f y s ω)) μ :=
  (hf.integrable_norm_randomEulerProduct_sq y hs).congr (hf.exp_tiltExponent_ae_eq y hs).symm

/-- **The normalising constant is positive.**  `∏ (1 + ‖p^{-s}‖²)` is a product of terms above
`1`; the Steinhaus counterpart needs `‖p^{-s}‖ < 1` first. -/
lemma IsRademacherRMF.integral_norm_randomEulerProduct_sq_pos (hf : IsRademacherRMF f μ) (y : ℕ)
    (s : ℂ) : 0 < ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ := by
  rw [hf.integral_norm_randomEulerProduct_sq y s]
  exact Finset.prod_pos fun p _ => by positivity

/-- **`P~` is a probability measure.** -/
theorem IsSteinhausRMF.isProbabilityMeasure_tiltedMeasure (hf : IsSteinhausRMF f μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) : IsProbabilityMeasure (tiltedMeasure f y s μ) := by
  have := hf.isProbabilityMeasure
  exact isProbabilityMeasure_tilted (hf.integrable_exp_tiltExponent y hs)

/-! ### The transfer `P~(A) = E[1_A W] / E[W]`

`MeasureTheory.Measure.tilted` has the density `exp (tiltExponent) / E exp (tiltExponent)`; the
statements here replace that density by the weight `W = ‖F_y(s)‖ ^ 2` it is a.e. equal to. -/

/-- **Harper's display.**  `P~(A)` is the normalised weighted measure of `A`, the definition of
the tilted measure as §3.2 writes it. -/
theorem IsSteinhausRMF.tiltedMeasure_apply (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet A) :
    tiltedMeasure f y s μ A
      = ENNReal.ofReal ((∫ ω in A, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
          / ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ) := by
  have hZ : (∫ ω, Real.exp (tiltExponent f y s ω) ∂μ)
      = ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ :=
    integral_congr_ae (hf.exp_tiltExponent_ae_eq y hs)
  rw [tiltedMeasure, tilted_apply_eq_ofReal_integral' _ hA, hZ, ← integral_div]
  refine congrArg ENNReal.ofReal (integral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae (hf.exp_tiltExponent_ae_eq y hs)] with ω hω
  rw [hω]

/-- **Harper's display, for the Rademacher RMF.**  `ℙ'(A)` is the normalised weighted measure of
`A`.  The mirror of `RMF.IsSteinhausRMF.tiltedMeasure_apply`. -/
theorem IsRademacherRMF.tiltedMeasure_apply (hf : IsRademacherRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet A) :
    tiltedMeasure f y s μ A
      = ENNReal.ofReal ((∫ ω in A, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
          / ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ) := by
  have hZ : (∫ ω, Real.exp (tiltExponent f y s ω) ∂μ)
      = ∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ :=
    integral_congr_ae (hf.exp_tiltExponent_ae_eq y hs)
  rw [tiltedMeasure, tilted_apply_eq_ofReal_integral' _ hA, hZ, ← integral_div]
  refine congrArg ENNReal.ofReal (integral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae (hf.exp_tiltExponent_ae_eq y hs)] with ω hω
  rw [hω]

/-- `P~ ≪ P`: the tilt has a density. -/
lemma tiltedMeasure_absolutelyContinuous (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ)
    (μ : Measure Ω) : tiltedMeasure f y s μ ≪ μ :=
  tilted_absolutelyContinuous μ _

/-! ### The exponent as a sum over the primes

`RMF.iIndepFun_tilted_finsetSum` and `RMF.map_tilted_finsetSum_of_mem` want the tilt in the form
`∑ i ∈ t, g i (X i ω)`.  The Euler product factorises, so the exponent is such a sum, with
`t = Nat.primesBelow y` and `g p = fun z => 2 * localLog (p ^ (-s)) z`. -/

/-- **The tilt exponent is a prime sum** of functions of the individual values at the primes:
`2 log ‖F_y(s)‖ = ∑_{p < y} 2 · localLog (p ^ (-s)) (X p ·)`.  This is twice
`RMF.logNormEuler_ae_eq_sum`. -/
lemma tiltExponent_ae_eq_sum {X : ℕ → Ω → ℂ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    tiltExponent (fun ω => compMultExtension fun p => X p ω) y s
      =ᵐ[μ] fun ω => ∑ p ∈ Nat.primesBelow y, 2 * localLog ((p : ℂ) ^ (-s)) (X p ω) := by
  filter_upwards [logNormEuler_ae_eq_sum hX y hs] with ω hω
  rw [tiltExponent, hω, Finset.mul_sum]

/-- **The tilted measure in the form the factorisation results consume.**  The exponent may be
replaced by its prime-sum representative, the tilt depending only on the a.e. class of the
exponent. -/
lemma tiltedMeasure_eq_tilted_sum {X : ℕ → Ω → ℂ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ
      = μ.tilted fun ω => ∑ p ∈ Nat.primesBelow y, 2 * localLog ((p : ℂ) ^ (-s)) (X p ω) :=
  tilted_congr (tiltExponent_ae_eq_sum hX y hs)

end RMF
