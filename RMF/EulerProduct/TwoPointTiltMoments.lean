/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.TwoPointTilt
import RMF.EulerProduct.TwoPointTiltLaw

/-!
# The local moments under the two-fold tilt

`RMF/EulerProduct/TwoPointTiltLaw.lean` computes the four raw moments of `RMF.localLog` against
the two-fold tilted circle law — the mean, the second moment, the covariance of two observables,
and the third absolute moment.  `RMF/EulerProduct/TwoPointTilt.lean` identifies the law of `f p`
under `RMF.tiltedMeasure₂` as exactly that measure, at `a_i = p^{-s_i}`.  This file transports the
four across, in the form the block sums consume.

The transport is one lemma, `RMF.integral_comp_tiltedMeasure₂`, and everything else is an
application of it; the one-fold file `RMF/EulerProduct/TiltedMoments.lean` has the same shape.

## The hypothesis, and what discharges it

Every statement below carries `‖p^{-s₁}‖ + ‖p^{-s₂}‖ ≤ 1/5`.  It is the *sum* because the tilt
exponent is the sum of the two local exponents, and it is that sum which must stay inside the
range where `e^u - 1 - u = O(u²)` is available.

**It is not vacuous, and it is not free.**  At `Re s_i = 1/2 + σ` the two terms are `p^{-1/2-σ}`
each, so the hypothesis reads `p^{1/2+σ} ≥ 10`: at `σ = 0` it fails for every prime below `100`
and holds from there on.  In the application the primes come from `RMF.primeBlockSub θ j`, where
`RMF.norm_le_of_mem_primeBlockSub` gives `‖p^{-s}‖ ≤ e/√(blockScale θ j)` and the scale condition
`14 + 2η ≤ e^{j+θ}` makes that far smaller than `1/10` — the sum is under `1/5` with room to
spare, so nothing here binds.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The transport -/

/-- **The two-fold analogue of `RMF.integral_comp_tiltedMeasure`.**  An observable of `f p` under
the two-fold tilt has the same integral as the observable of a point of the circle under the
two-fold tilted circle law.  Everything below is this lemma plus a one-fold statement. -/
theorem integral_comp_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ ω, g (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)
      = ∫ z, g z ∂(steinhausLaw.tilted fun z =>
          2 * localLog (((p : ℕ) : ℂ) ^ (-s₁)) z + 2 * localLog (((p : ℕ) : ℂ) ^ (-s₂)) z) := by
  rw [← integral_map (hX.measurable (p : ℕ) p.2).aemeasurable hg.aestronglyMeasurable,
    hX.map_tiltedMeasure₂ y hs₁ hs₂ hp]
  rfl

/-! ### The four raw moments

These are the five quantities `RMF.abs_integral_swap_window_le` matches — `E N¹`, `E N²`,
`E (N¹)²`, `E (N²)²` from the first two statements at `w = w₁` and `w = w₂`, and `E N¹N²` from the
third — together with the third absolute moment that bounds the swap error. -/

/-- **The two-fold tilted local mean.**  `E~ localLog w (f p) = Re(w conj a₁) + Re(w conj a₂) +
O(δ³)` with `a_i = p^{-s_i}`: **the two drifts add**. -/
theorem abs_integral_localLog_tiltedMeasure₂_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLog w (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        - ((w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re
            + (w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re)|
      ≤ 160 * ‖w‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
          + 120 * ‖w‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 := by
  rw [integral_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp (measurable_localLog w)]
  exact abs_integral_localLog_tilted_pair_sub_le hA hw

/-- **The two-fold tilted local second moment.**  `E~ (localLog w (f p))² = ‖w‖²/2 + O(δ³)`: the
second tilt does not move it, to third order. -/
theorem abs_integral_localLog_sq_tiltedMeasure₂_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLog w (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        - ‖w‖ ^ 2 / 2|
      ≤ 20 * ‖w‖ ^ 3
          + 240 * ‖w‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) := by
  rw [integral_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp ((measurable_localLog w).pow_const 2)]
  exact abs_integral_localLog_sq_tilted_pair_sub_le hA hw

/-- **The two-fold tilted local covariance.**  `E~ localLog w₁ (f p) · localLog w₂ (f p) =
Re(w₁ conj w₂)/2 + O(δ³)`.

At `w_i = p^{-1/2-σ-it_i}` the main term is `cos((t₁-t₂) log p) / 2p^{1+2σ}`: this is the
logarithmic correlation between the two heights, and it is the only place where the two walks
see each other. -/
theorem abs_integral_localLog_mul_tiltedMeasure₂_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ ≤ 1 / 5) (h₂ : ‖w₂‖ ≤ 1 / 5) :
    |(∫ ω, localLog w₁ (X (p : ℕ) ω) * localLog w₂ (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        - (w₁ * (starRingEnd ℂ) w₂).re / 2|
      ≤ 20 * (‖w₁‖ ^ 3 + ‖w₂‖ ^ 3)
          + 240 * (‖w₁‖ * ‖w₂‖)
              * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) := by
  rw [integral_comp_tiltedMeasure₂ (g := fun z => localLog w₁ z * localLog w₂ z)
    hX y hs₁ hs₂ hp ((measurable_localLog w₁).mul (measurable_localLog w₂))]
  exact abs_integral_localLog_mul_tilted_pair_sub_le hA h₁ h₂

/-- **The two-fold tilted third absolute moment** — the Lindeberg swap's error term, with the
same constant as in the one-fold case since the bound is pointwise on the circle. -/
theorem integral_abs_localLog_cube_tiltedMeasure₂_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, |localLog w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  have hg : Measurable fun z : ℂ => |localLog w z| ^ 3 := by
    simp only [← Real.norm_eq_abs]
    exact (measurable_localLog w).norm.pow_const 3
  rw [integral_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp hg]
  exact integral_abs_localLog_cube_tilted_pair_le hA hw

/-! ### Integrability

The transport again, for `Integrable` rather than `∫`.  The block mean needs it, to exchange the
finite sum with the integral. -/

/-- **Transport of integrability**, the companion of `RMF.integral_comp_tiltedMeasure₂`. -/
theorem integrable_comp_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    {g : ℂ → ℝ} (hg : Integrable g (steinhausLaw.tilted fun z =>
      2 * localLog (((p : ℕ) : ℂ) ^ (-s₁)) z + 2 * localLog (((p : ℕ) : ℂ) ^ (-s₂)) z)) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  refine Integrable.comp_aemeasurable ?_ (hX.measurable (p : ℕ) p.2).aemeasurable
  rw [hX.map_tiltedMeasure₂ y hs₁ hs₂ hp]
  exact hg

/-- A local term is integrable under the two-fold tilt. -/
theorem integrable_localLog_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLog w (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp (integrable_localLog_tilted_pair hA hw)

/-! ### Block sums

A block increment of the pair walk is `N^i = ∑_{p ∈ B} localLog (w^i p) (f p)`.  The two
statements below are the per-prime mean and second moment summed over `B`; nothing new happens.

The observed radii are left free, as in the one-fold `RMF/EulerProduct/TiltedMoments.lean`: in the
application `w^i p = p^{-(1/2+σ+it_i)}` while the tilt sits at `s_i = 1/2 + σ`; keeping them apart
preserves the oscillations `\cos(t_i \log p)`. -/

/-- **The mean over a block**, the two-fold analogue of
`RMF.abs_integral_sum_localLog_tiltedMeasure_sub_le`.  **The two drifts add**: at `s_i = 1/2 + σ`
and `w p = p^{-(1/2+σ+it)}` the main term is `∑_{p ∈ B} (\cos(t \log p) + \cos(t \log p))/p^{1+2σ}`,
one copy per tilt. -/
theorem abs_integral_sum_localLog_tiltedMeasure₂_sub_le (hX : IsSteinhausPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(∫ ω, ∑ p ∈ B, localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        - ∑ p ∈ B, ((w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re
            + (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re)|
      ≤ ∑ p ∈ B, (160 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
          + 120 * ‖w p‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2) := by
  rw [integral_finsetSum B fun p hp =>
      integrable_localLog_tiltedMeasure₂ hX y hs₁ hs₂ (hB hp) (hA p hp) (hw p hp),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLog_tiltedMeasure₂_sub_le hX y hs₁ hs₂ (hB hp) (hA p hp) (hw p hp)

/-- **The diagonal of the covariance over a block**, the two-fold analogue of
`RMF.abs_sum_integral_localLog_sq_tiltedMeasure_sub_le`: the raw second moments, one per prime,
which a Lindeberg comparison matches. -/
theorem abs_sum_integral_localLog_sq_tiltedMeasure₂_sub_le (hX : IsSteinhausPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(∑ p ∈ B, ∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        - ∑ p ∈ B, ‖w p‖ ^ 2 / 2|
      ≤ ∑ p ∈ B, (20 * ‖w p‖ ^ 3
          + 240 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLog_sq_tiltedMeasure₂_sub_le hX y hs₁ hs₂ (hB hp) (hA p hp) (hw p hp)

end RMF
