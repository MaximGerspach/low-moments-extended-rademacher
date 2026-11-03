/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Probability.HasLawExists

/-!
# The laws at a prime

The two distributions from which the values of a random multiplicative function at the
primes are drawn:

* `RMF.rademacherLaw` — a fair coin flip between `1` and `-1`;
* `RMF.steinhausLaw` — the uniform (Haar) probability measure on the unit circle.

Both are probability measures, both are carried by the closed unit disc, and both are
centered.  For the Steinhaus law we also record the orthogonality of the characters
`z ↦ z ^ a` (`RMF.integral_pow_mul_conj_steinhausLaw`), which is the engine behind the
second-moment computations, and behind the local expansion of a general moment.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace RMF

/-! ### The law at a prime -/

/-- The Rademacher law: a fair coin flip between `1` and `-1`. -/
noncomputable def rademacherLaw : Measure ℂ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 1 + Measure.dirac (-1))

/-- The angle parametrisation of the unit circle. -/
noncomputable def circleAngle (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

@[fun_prop]
lemma measurable_circleAngle : Measurable circleAngle := by
  unfold circleAngle; fun_prop

@[simp]
lemma norm_circleAngle (θ : ℝ) : ‖circleAngle θ‖ = 1 := by
  simp [circleAngle, Complex.norm_exp, mul_comm]

/-! ### `circleAngle` is a character

Rotating the Steinhaus law by a unimodular `c` is *translating* the angle by `arg c`.  That is the
whole content of its rotation invariance, and it is why no separate treatment of the circle group
is needed: everything reduces to translation invariance of Lebesgue measure on `ℝ`, together with
the fact that a half-open interval of length `2π` is a fundamental domain. -/

/-- Addition of angles is multiplication of phases. -/
lemma circleAngle_add (α β : ℝ) : circleAngle (α + β) = circleAngle α * circleAngle β := by
  rw [circleAngle, circleAngle, circleAngle, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp]
lemma circleAngle_two_pi : circleAngle (2 * π) = 1 := by
  rw [circleAngle]
  push_cast
  exact Complex.exp_two_pi_mul_I

/-- `circleAngle` is `2π`-periodic. -/
lemma circleAngle_periodic : Function.Periodic circleAngle (2 * π) := fun θ => by
  rw [circleAngle_add, circleAngle_two_pi, mul_one]

/-- **Every unimodular `c` is an angle**, namely `arg c`.

This is what lets the rotation `z ↦ c * z` be handled as a translation, with no circle-group
machinery: `RMF.circleAngle_add` then turns it into `θ ↦ θ + arg c`. -/
lemma exists_circleAngle_eq {c : ℂ} (hc : ‖c‖ = 1) : ∃ α : ℝ, circleAngle α = c := by
  refine ⟨Complex.arg c, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc] at h
  simpa [circleAngle] using h

/-- **The pushforward does not see which interval.**  Lebesgue measure carried through
`circleAngle` from *any* half-open interval of length `2π` gives the same measure on the circle:
`Ioc t (t+2π)` is a fundamental domain for `2πℤ`, and `circleAngle` is `2π`-periodic.  This is the
only real content of the rotation argument.  The `VAddInvariantMeasure` instance, which Mathlib does
not register, is supplied as in `Function.Periodic.intervalIntegral_add_eq`. -/
lemma map_circleAngle_restrict_Ioc (a b : ℝ) :
    (volume.restrict (Set.Ioc a (a + 2 * π))).map circleAngle
      = (volume.restrict (Set.Ioc b (b + 2 * π))).map circleAngle := by
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples (2 * π)) ℝ volume :=
    ⟨fun _ _ _ => measure_preimage_add _ _ _⟩
  refine Measure.ext fun S hS => ?_
  have hA : MeasurableSet (circleAngle ⁻¹' S) := measurable_circleAngle hS
  rw [Measure.map_apply measurable_circleAngle hS, Measure.map_apply measurable_circleAngle hS,
    Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact IsAddFundamentalDomain.measure_set_eq
    (isAddFundamentalDomain_Ioc Real.two_pi_pos a)
    (isAddFundamentalDomain_Ioc Real.two_pi_pos b) hA
    (fun g => by
      ext x
      simp only [Set.mem_preimage, circleAngle_periodic.map_vadd_zmultiples g x])

/-- The Steinhaus law: the uniform (Haar) probability measure on the unit circle, as the image
under `circleAngle` of the normalised Lebesgue measure on the angle interval `(-π, π]`.  It is the
image of Mathlib's `haarAddCircle` on `AddCircle (2 * π)` under the exponential map; the elementary
description needs no Haar-measure API. -/
noncomputable def steinhausLaw : Measure ℂ :=
  (ENNReal.ofReal (2 * π))⁻¹ • (volume.restrict (Set.Ioc (-π) π)).map circleAngle

lemma toReal_steinhaus_const : ((ENNReal.ofReal (2 * π))⁻¹).toReal = (2 * π)⁻¹ := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]

instance : IsProbabilityMeasure rademacherLaw := by
  constructor
  simp only [rademacherLaw, Measure.smul_apply, Measure.coe_add, Pi.add_apply, smul_eq_mul,
    measure_univ]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero (by simp)]

instance : IsProbabilityMeasure steinhausLaw := by
  constructor
  rw [steinhausLaw, Measure.smul_apply,
    Measure.map_apply measurable_circleAngle MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
    show π - -π = 2 * π by ring]
  exact ENNReal.inv_mul_cancel (by simp [pi_pos]) ENNReal.ofReal_ne_top

/-! ### The two classical laws are bounded and centered -/

/-- Every integral against the Rademacher law is the average of the two values: the law is
supported on `{1, -1}` with equal weights. -/
lemma integral_rademacherLaw_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (g : ℂ → E) : (∫ z, g z ∂rademacherLaw) = (2 : ℝ)⁻¹ • (g 1 + g (-1)) := by
  rw [rademacherLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac, show ((2 : ℝ≥0∞)⁻¹).toReal = (2 : ℝ)⁻¹ by simp]

@[simp]
lemma integral_rademacherLaw : ∫ z, z ∂rademacherLaw = 0 := by
  rw [integral_rademacherLaw_eq]; simp

/-- The Rademacher law lives on the unit circle: a.e. `z` is `±1`. -/
lemma norm_eq_one_rademacherLaw : ∀ᵐ z ∂rademacherLaw, ‖z‖ = 1 := by
  rw [ae_iff]
  simp only [rademacherLaw, Measure.smul_apply, Measure.coe_add, Pi.add_apply, smul_eq_mul]
  simp

/-- **The Rademacher values square to one.**  Both atoms of `½(δ₁ + δ₋₁)` do, and this is
what `‖z‖ = 1` does *not* give: it is the fact that the values are real `±1` rather than merely
unimodular, and it is what makes `f(p)² = 1` at a prime. -/
lemma sq_eq_one_rademacherLaw : ∀ᵐ z ∂rademacherLaw, z ^ 2 = 1 := by
  rw [ae_iff]
  simp only [rademacherLaw, Measure.smul_apply, Measure.coe_add, Pi.add_apply, smul_eq_mul]
  simp

/-- **The Rademacher law is invariant under a sign.**  `½(δ₁ + δ₋₁)` is carried to itself by
`z ↦ -z`, which merely swaps the two atoms.

This is the `±1` shadow of `RMF.map_mul_left_steinhausLaw`: the Steinhaus law is invariant under
*every* unimodular multiplier, the Rademacher law only under `±1` — but `±1` is all the
symmetrisation step ever multiplies by. -/
lemma map_mul_left_rademacherLaw {c : ℂ} (hc : c = 1 ∨ c = -1) :
    Measure.map (fun z : ℂ => c * z) rademacherLaw = rademacherLaw := by
  rcases hc with rfl | rfl
  · simp
  · have hm : Measurable (fun z : ℂ => (-1 : ℂ) * z) := by fun_prop
    rw [rademacherLaw, Measure.map_smul, Measure.map_add _ _ hm,
      Measure.map_dirac' hm, Measure.map_dirac' hm]
    norm_num [add_comm]

lemma norm_le_one_rademacherLaw : ∀ᵐ z ∂rademacherLaw, ‖z‖ ≤ 1 := by
  rw [ae_iff]
  simp only [rademacherLaw, Measure.smul_apply, Measure.coe_add, Pi.add_apply, smul_eq_mul]
  simp

@[simp]
lemma integral_steinhausLaw : ∫ z, z ∂steinhausLaw = 0 := by
  rw [steinhausLaw, integral_smul_measure,
    integral_map (f := fun z : ℂ => z) measurable_circleAngle.aemeasurable
      aestronglyMeasurable_id,
    ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  simp [circleAngle, integral_exp_mul_I_eq_sin]

/-- **The Steinhaus law is the circle average.**  Integrating against `ν_S` is Mathlib's
`circleAverage` at centre `0` and radius `1`.  This is the bridge to the circle-average API,
and in particular to the mean value property for harmonic functions. -/
lemma integral_steinhausLaw_eq_circleAverage {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂steinhausLaw = circleAverage g 0 1 := by
  have hmap : ∀ θ : ℝ, circleMap 0 1 θ = circleAngle θ := by
    intro θ; simp [circleMap, circleAngle]
  have hper : Function.Periodic (fun θ : ℝ => g (circleAngle θ)) (2 * π) := by
    intro θ
    simp only [circleAngle]
    rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hshift
  rw [steinhausLaw, integral_smul_measure,
    integral_map measurable_circleAngle.aemeasurable hg.aestronglyMeasurable,
    toReal_steinhaus_const, ← intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π),
    hshift, circleAverage]
  simp only [hmap]

/-- The Steinhaus law is carried by the unit circle. -/
lemma norm_eq_one_steinhausLaw : ∀ᵐ z ∂steinhausLaw, ‖z‖ = 1 := by
  have hs : MeasurableSet {z : ℂ | ¬ ‖z‖ = 1} :=
    (measurable_norm (measurableSet_singleton 1)).compl
  have hpre : circleAngle ⁻¹' {z : ℂ | ¬ ‖z‖ = 1} = ∅ := by ext θ; simp
  rw [ae_iff]
  simp only [steinhausLaw, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply measurable_circleAngle hs, hpre, measure_empty, mul_zero]

lemma norm_le_one_steinhausLaw : ∀ᵐ z ∂steinhausLaw, ‖z‖ ≤ 1 :=
  norm_eq_one_steinhausLaw.mono fun _ hz => hz.le

/-- **Rotation invariance of the Steinhaus law.**  Multiplying by any unimodular `c` leaves it
unchanged: `RMF.circleAngle_add` turns the rotation into a *translation* of the angle, translation
invariance of Lebesgue measure moves the interval, and `RMF.map_circleAngle_restrict_Ioc` says the
interval never mattered.  The Rademacher law is invariant only under `±1`
(`RMF.map_mul_left_rademacherLaw`). -/
theorem map_mul_left_steinhausLaw {c : ℂ} (hc : ‖c‖ = 1) :
    steinhausLaw.map (fun z => c * z) = steinhausLaw := by
  obtain ⟨α, rfl⟩ := exists_circleAngle_eq hc
  have hmul : Measurable (fun z : ℂ => circleAngle α * z) := by fun_prop
  have hadd : Measurable (fun θ : ℝ => α + θ) := by fun_prop
  have hcomp : (fun z : ℂ => circleAngle α * z) ∘ circleAngle
      = circleAngle ∘ (fun θ : ℝ => α + θ) := by
    funext θ
    simp only [Function.comp_apply, circleAngle_add]
  have hpre : (fun θ : ℝ => α + θ) ⁻¹' Set.Ioc (α - π) (α + π) = Set.Ioc (-π) π := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  -- translation carries the base interval to the shifted one
  have hstep : (volume.restrict (Set.Ioc (-π) π)).map (fun θ : ℝ => α + θ)
      = volume.restrict (Set.Ioc (α - π) (α + π)) := by
    rw [← hpre, ← Measure.restrict_map hadd measurableSet_Ioc, map_add_left_eq_self]
  -- both intervals, in the `Ioc t (t + 2π)` shape `map_circleAngle_restrict_Ioc` wants
  have h1 : Set.Ioc (α - π) (α + π) = Set.Ioc (α - π) ((α - π) + 2 * π) := by
    congr 1
    ring
  have h2 : Set.Ioc (-π) π = Set.Ioc (-π) ((-π) + 2 * π) := by
    congr 1
    ring
  rw [steinhausLaw, Measure.map_smul, Measure.map_map hmul measurable_circleAngle, hcomp,
    ← Measure.map_map measurable_circleAngle hadd, hstep, h1, h2]
  congr 1
  exact map_circleAngle_restrict_Ioc (α - π) (-π)

/-! ### Orthogonality of the characters for the Steinhaus law -/

lemma circleAngle_pow_mul_conj (θ : ℝ) (a b : ℕ) :
    circleAngle θ ^ a * (starRingEnd ℂ) (circleAngle θ ^ b)
      = Complex.exp ((((a : ℂ) - b) * Complex.I) * θ) := by
  rw [circleAngle, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast]
  ring

/-- **Orthogonality of the characters**: the powers `z ↦ z ^ a` are orthonormal in `L²` of
the Steinhaus law. -/
lemma integral_pow_mul_conj_steinhausLaw (a b : ℕ) :
    (∫ z, z ^ a * (starRingEnd ℂ) (z ^ b) ∂steinhausLaw) = if a = b then 1 else 0 := by
  rw [steinhausLaw, integral_smul_measure,
    integral_map (f := fun z : ℂ => z ^ a * (starRingEnd ℂ) (z ^ b))
      measurable_circleAngle.aemeasurable (by fun_prop),
    toReal_steinhaus_const]
  simp only [circleAngle_pow_mul_conj]
  rw [← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  rcases eq_or_ne a b with rfl | hab
  · have hpi : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
    simp
    field_simp
    norm_num
  · set c : ℂ := ((a : ℂ) - b) * Complex.I with hcdef
    have hc : c ≠ 0 := by
      refine mul_ne_zero (sub_ne_zero.2 ?_) Complex.I_ne_zero
      exact_mod_cast hab
    have h2 : Complex.exp (2 * (c * π)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨(a : ℤ) - b, by rw [hcdef]; push_cast; ring⟩
    have key : Complex.exp (c * ((π : ℝ) : ℂ)) = Complex.exp (c * ((-π : ℝ) : ℂ)) := by
      have h3 : Complex.exp (c * ((-π : ℝ) : ℂ)) * Complex.exp (2 * (c * π))
          = Complex.exp (c * ((π : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [← h3, h2, mul_one]
    rw [integral_exp_mul_complex hc, if_neg hab, key, sub_self, zero_div, smul_zero]

/-- A law carried by the closed unit disc has moments of every order, in particular a
finite second one. -/
lemma memLp_id_of_norm_le_one {ν : Measure ℂ} [IsFiniteMeasure ν] (h : ∀ᵐ z ∂ν, ‖z‖ ≤ 1)
    (k : ℕ) : MemLp id k ν :=
  (memLp_top_of_bound aestronglyMeasurable_id 1 h).mono_exponent le_top

lemma memLp_two_rademacherLaw : MemLp id 2 rademacherLaw :=
  memLp_id_of_norm_le_one norm_le_one_rademacherLaw 2

end RMF
