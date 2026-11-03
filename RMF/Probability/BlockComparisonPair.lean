/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparison
import RMF.Probability.HarperChainPair
import RMF.EulerProduct.TwoPointTiltMoments

/-!
# The block data at two points

`RMF.blockMean`, `RMF.blockMatchedVar` name the Gaussian matched to a block of tilted increments
at *one* point.  Harper's Proposition 7 needs the same at two, and the two-point objects are
**not** the one-point ones applied twice: they live under the two-fold tilt `RMF.tiltedMeasure₂`,
and the one-point definitions are stated against the one-fold `RMF.tiltedMeasure`.  So they are
redefined here, and a third object appears that has no one-point analogue at all — the covariance.

* `RMF.blockMean₂`, `RMF.blockMatchedVar₂` — the marginals, one per coordinate;
* `RMF.blockMatchedCov` — the off-diagonal, `∑_p (E~ξ¹_pξ²_p - E~ξ¹_p·E~ξ²_p)`.

**The covariance is the whole difficulty of the two-point argument.**  At `w^i_p = p^{-1/2-σ-it_i}`
its main term is `∑_{p∈B} cos((t₁-t₂)\log p)/2p^{1+2σ}` — the logarithmic correlation.  Near
`t₁ = t₂` that is the full variance and the two walks coincide; the block decorrelation estimate
`RMF.abs_cos_prime_sum_block_weight_le` makes it small once the heights separate, and Harper's
`x_1 ≥ e^{C/|t|²}` in Lemma 7 is what buys that.  The multi-block box comparison is
`RMF.exists_isBoxComparison_steinhaus_of_range`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The three block statistics -/

/-- The mean of one coordinate of the block Gaussian, under the **two-fold** tilt.  Same shape as
`RMF.blockMean`, and not equal to it: the tilt is by both `F_y(s₁)` and `F_y(s₂)`, so both drifts
are present in each coordinate. -/
noncomputable def blockMean₂ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ∫ ω, localLog (w p) (X (p : ℕ) ω)
    ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)

/-- The variance of one coordinate of the block Gaussian, under the two-fold tilt. -/
noncomputable def blockMatchedVar₂ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ≥0 :=
  ∑ p ∈ B, matchingVar
    (∫ ω, localLog (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
    (∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))

/-- **The off-diagonal**, `∑_p (E~ξ¹_pξ²_p - E~ξ¹_p·E~ξ²_p)`.

Summed per prime rather than taken of the block sums, which is the same thing because the
increments are independent under the tilt, and is the form the per-prime estimates deliver. -/
noncomputable def blockMatchedCov (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (v w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ((∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      - (∫ ω, localLog (v p) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        * ∫ ω, localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))

/-! ### Cauchy–Schwarz under the two-fold tilt

`RMF.blockMatchedVar₂` is a sum of `RMF.matchingVar`s, and `matchingVar m₁ m₂ = (m₂ - m₁²)⁺`.  To
read it as a real number one needs `m₁² ≤ m₂`, which is Cauchy–Schwarz for the tilted measure.  The
one-fold chain (`RMF.sq_integral_localLog_le_integral_mul_self`) does not apply, so it is redone
here; the only new ingredient is that `localLog w · localLog w` is bounded on the circle, where the
two-fold tilt lives. -/

/-- The square of a local term is integrable against the two-fold tilted law. -/
lemma integrable_localLog_mul_self_tilted_pair {a₁ a₂ w : ℂ} (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5)
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLog w z * localLog w z)
      (steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z) := by
  have hprob := isProbabilityMeasure_tilted_localLog_pair hA
  refine (integrable_const ((11 / 5 * ‖w‖) ^ 2)).mono'
    ((measurable_localLog w).mul (measurable_localLog w)).aestronglyMeasurable ?_
  filter_upwards [ae_norm_eq_one_tilted_pair (a₁ := a₁) (a₂ := a₂)] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  have h := abs_localLog_le_of_norm_le hz hw
  nlinarith [abs_nonneg (localLog w z), norm_nonneg w, h]

/-- A local term is square-integrable under the two-fold tilt. -/
lemma memLp_two_localLog_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    MemLp (fun ω => localLog w (X (p : ℕ) ω)) 2
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  have hint := integrable_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp
    (integrable_localLog_mul_self_tilted_pair hA hw)
  have hmeas : Measurable (fun ω => localLog w (X (p : ℕ) ω)) :=
    (measurable_localLog w).comp (hX.measurable (p : ℕ) p.2)
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  simpa only [pow_two] using hint

/-- **`P~` is a probability measure**, in the `IsSteinhausPrimeValues` phrasing, for the two-fold
tilt. -/
theorem IsSteinhausPrimeValues.isProbabilityMeasure_tiltedMeasure₂ {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    IsProbabilityMeasure
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) :=
  IsSteinhausRMF.isProbabilityMeasure_tiltedMeasure₂ hX.isSteinhausRMF y hs₁ hs₂

/-- **Cauchy–Schwarz for the local terms**, under the two-fold tilt. -/
lemma sq_integral_localLog_le_integral_mul_self₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2
      ≤ ∫ ω, localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  have := hX.isProbabilityMeasure_tiltedMeasure₂ y hs₁ hs₂
  exact sq_integral_le_integral_mul_self
    (memLp_two_localLog_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hw)

/-- **`blockMatchedVar₂` as a real number** — the positive part is not doing any work, because
Cauchy–Schwarz makes each summand non-negative already. -/
lemma coe_blockMatchedVar₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    (blockMatchedVar₂ X μ y s₁ s₂ w B : ℝ)
      = ∑ p ∈ B, ((∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
          - (∫ ω, localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2) := by
  rw [blockMatchedVar₂, NNReal.coe_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [coe_matchingVar
    (sq_integral_localLog_le_integral_mul_self₂ hX y hs₁ hs₂ (hB hq) (hA q hq) (hw q hq))]

/-! ### The per-prime mean, in a usable form

`RMF.abs_integral_localLog_tiltedMeasure₂_sub_le` gives the mean as `Re(w \bar a₁) + Re(w \bar a₂)`
up to third-order errors.  What the covariance needs is only its **size**, and the useful form
keeps the factor `A = ‖a₁‖ + ‖a₂‖`: the mean is `O(‖w‖·A)`, so the product of two means is
`O(‖v‖‖w‖A²)` — one order in `A` better than the covariance's own error term, which is why
subtracting the means costs nothing. -/

/-- **The two-fold tilted mean is `O(‖w‖·A)`**, `A = ‖a₁‖ + ‖a₂‖`.

The main term is `Re(w \bar a₁) + Re(w \bar a₂)`, of size at most `‖w‖A`; the two error terms
contribute `160‖w‖A·‖w‖` and `120‖w‖A·A`, and at `‖w‖, A ≤ 1/5` those are `32‖w‖A` and `24‖w‖A`. -/
theorem abs_integral_localLog_tiltedMeasure₂_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    |∫ ω, localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)|
      ≤ 57 * ‖w‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) := by
  have hmain := abs_integral_localLog_tiltedMeasure₂_sub_le hX y hs₁ hs₂ hp hA hw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have ha₁ : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ := norm_nonneg _
  have ha₂ : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := norm_nonneg _
  -- `|Re (w conj a)| ≤ ‖w‖‖a‖`, twice
  have hre : ∀ a : ℂ, |(w * (starRingEnd ℂ) a).re| ≤ ‖w‖ * ‖a‖ := by
    intro a
    refine (Complex.abs_re_le_norm _).trans_eq ?_
    rw [norm_mul]
    simp
  have h₁ := hre (((p : ℕ) : ℂ) ^ (-s₁))
  have h₂ := hre (((p : ℕ) : ℂ) ^ (-s₂))
  have habs := abs_sub_le_iff.1 hmain
  have hle : |(w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re
      + (w * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re|
      ≤ ‖w‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) := by
    refine (abs_add_le _ _).trans ?_
    nlinarith [h₁, h₂]
  have hlin := abs_le.1 hle
  rw [abs_le]
  constructor <;> nlinarith [habs.1, habs.2, hlin.1, hlin.2, hw0, ha₁, ha₂, hA, hw,
    mul_nonneg hw0 (by linarith : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖
      + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)]

/-! ### The covariance, against the cosine sum

The estimate that names `blockMatchedCov`: it is `∑_p Re(v_p \bar w_p)/2` up to an error of the
same shape the block third moment already controls.  Three sources contribute: the error of the
two-fold mixed moment (`RMF.abs_integral_localLog_mul_tiltedMeasure₂_sub_le`), and the two means
whose product is subtracted. -/

/-- **The block covariance is the cosine sum, up to third-order errors.** -/
theorem abs_blockMatchedCov_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v w : Nat.Primes → ℂ} (hv : ∀ p ∈ B, ‖v p‖ ≤ 1 / 5) (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMatchedCov X μ y s₁ s₂ v w B - ∑ p ∈ B, (v p * (starRingEnd ℂ) (w p)).re / 2|
      ≤ ∑ p ∈ B, (20 * (‖v p‖ ^ 3 + ‖w p‖ ^ 3)
          + 240 * (‖v p‖ * ‖w p‖) * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
          + 3249 * (‖v p‖ * ‖w p‖)
              * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2) := by
  classical
  set T := tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ with hT
  rw [blockMatchedCov, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hmix := abs_integral_localLog_mul_tiltedMeasure₂_sub_le hX y hs₁ hs₂ (hB hp) (hA p hp)
    (hv p hp) (hw p hp)
  have hmv := abs_integral_localLog_tiltedMeasure₂_le hX y hs₁ hs₂ (hB hp) (hA p hp) (hv p hp)
  have hmw := abs_integral_localLog_tiltedMeasure₂_le hX y hs₁ hs₂ (hB hp) (hA p hp) (hw p hp)
  set mv := ∫ ω, localLog (v p) (X (p : ℕ) ω) ∂T with hmvdef
  set mw := ∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T with hmwdef
  have hv0 : (0 : ℝ) ≤ ‖v p‖ := norm_nonneg _
  have hw0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
  have hA0 : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := by
    positivity
  -- the product of the two means, which subtracting the means costs
  have hprod : |mv * mw| ≤ 3249 * (‖v p‖ * ‖w p‖)
      * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 := by
    rw [abs_mul]
    calc |mv| * |mw|
        ≤ (57 * ‖v p‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖))
            * (57 * ‖w p‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)) :=
          mul_le_mul hmv hmw (abs_nonneg _) (by positivity)
      _ = 3249 * (‖v p‖ * ‖w p‖)
            * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 := by ring
  have hsplit : (∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T)
      - mv * mw - (v p * (starRingEnd ℂ) (w p)).re / 2
      = ((∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T)
          - (v p * (starRingEnd ℂ) (w p)).re / 2) - mv * mw := by ring
  rw [hsplit]
  have htri : |((∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T)
        - (v p * (starRingEnd ℂ) (w p)).re / 2) - mv * mw|
      ≤ |(∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T)
          - (v p * (starRingEnd ℂ) (w p)).re / 2| + |mv * mw| := by
    have h := abs_add_le ((∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T)
      - (v p * (starRingEnd ℂ) (w p)).re / 2) (-(mv * mw))
    rwa [← sub_eq_add_neg, abs_neg] at h
  linarith [hmix, hprod, htri]

/-! ### The covariance at Harper's weights

Both coordinates carry `w^i_p = p^{-s_i}` with `Re s_i = 1/2 + σ`, so the two-point kernel
`RMF.re_natCast_cpow_neg_mul_conj` turns the main term into `∑_p \cos(τ\log p)/2p^{1+2σ}` with
`τ = t₁ - t₂`, the object of the block decorrelation estimate
`RMF.abs_cos_prime_sum_block_weight_le`.

The error collapses because all four norms coincide on the block: `‖v_p‖ = ‖w_p‖ = p^{-1/2-σ}` and
`A = 2‖w_p‖`, so the three error terms are `40‖w‖³`, `480‖w‖³` and `12996‖w‖⁴`, and
`‖w_p‖ ≤ 1/1000` on the block turns the last into `13‖w‖³`.  `533 ≤ 600`, and
`RMF.sum_norm_cube_primeBlockSub_le` makes `∑‖w_p‖³` doubly exponentially small, so the covariance
is the cosine sum up to a negligible error. -/

/-- **The block covariance at Harper's weights.** -/
theorem abs_blockMatchedCov_prime_sub_le (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ}
    {s₁ s₂ : ℂ} (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) :
    |blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m)
        - ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-(1 + 2 * σ))
            * Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / 2|
      ≤ 600 * ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 := by
  have hs₁ : 0 < s₁.re := re_pos_of_block hmθ hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hmθ hre₂ hσ
  have hB : primeBlockSub θ m ⊆ primesBelowSub (blockCutoff θ n) :=
    primeBlockSub_subset_primesBelowSub θ hmn
  have hκ := blockWeightSize_le hmθ
  -- the two weights have the same modulus, and it is at most `1/1000`
  have hsmall : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖
        ∧ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 1000 := by
    intro p hp
    have h₁ := norm_sq_prime_cpow_neg p hre₁
    have h₂ := norm_sq_prime_cpow_neg p hre₂
    have heq : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := by
      have h : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 := by rw [h₁, h₂]
      calc ‖((p : ℕ) : ℂ) ^ (-s₁)‖
          = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2) := by rw [h]
        _ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := Real.sqrt_sq (norm_nonneg _)
    refine ⟨heq, ?_⟩
    have hb : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub hσ hp h₁
    linarith
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    rw [← heq]
    linarith
  have hv : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by
    intro p hp
    linarith [(hsmall p hp).2]
  have hw : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    rw [← heq]
    linarith
  have hmain := abs_blockMatchedCov_sub_le hX (blockCutoff θ n) hs₁ hs₂ hB hA hv hw
  -- the main term is the cosine sum
  have hcos : ∑ p ∈ primeBlockSub θ m,
        ((((p : ℕ) : ℂ) ^ (-s₁)) * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re / 2
      = ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-(1 + 2 * σ))
          * Real.cos ((s₁.im - s₂.im) * Real.log ((p : ℕ) : ℝ)) / 2 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [re_natCast_cpow_neg_mul_conj p.2.pos s₁ s₂, hre₁, hre₂]
    ring_nf
  rw [hcos] at hmain
  refine hmain.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨heq, hle⟩ := hsmall p hp
  have h0 : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ := norm_nonneg _
  rw [← heq]
  -- `12996 c⁴ ≤ 80 c³` needs `c ≤ 1/1000`, which `nlinarith` cannot multiply out unaided
  have hquart : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 * ‖((p : ℕ) : ℂ) ^ (-s₁)‖
      ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 * (1 / 1000) :=
    mul_le_mul_of_nonneg_left hle (pow_nonneg h0 3)
  nlinarith [h0, hle, hquart, pow_nonneg h0 3]

/-! ### The variance, against the weight sum

`RMF.abs_blockVar_sub_le` at two points.  Three errors again: the error of the two-fold second
moment (`RMF.abs_integral_localLog_sq_tiltedMeasure₂_sub_le`), and the mean squared, which is
`O(‖w‖²A²)` by the same bound the covariance used.  The shape is the one-point estimate's; only
the constants are heavier, heavy enough that `RMF.blockWeightSize_le_millionth` rather than
`RMF.blockWeightSize_le` is what makes them harmless. -/

/-- **The two-point block variance against `∑‖w_p‖²/2`.** -/
theorem abs_blockMatchedVar₂_sub_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(blockMatchedVar₂ X μ y s₁ s₂ w B : ℝ) - ∑ p ∈ B, ‖w p‖ ^ 2 / 2|
      ≤ ∑ p ∈ B, (20 * ‖w p‖ ^ 3
          + 240 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
          + 3249 * ‖w p‖ ^ 2
            * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2) := by
  classical
  set T := tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ with hT
  -- the two-fold second moment, over the block
  have h₂ := abs_sum_integral_localLog_sq_tiltedMeasure₂_sub_le hX y hs₁ hs₂ hB hA hw
  -- the mean squared
  have hmean : ∀ p ∈ B, (∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T) ^ 2
      ≤ 3249 * ‖w p‖ ^ 2
        * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 := by
    intro p hp
    have hb := abs_integral_localLog_tiltedMeasure₂_le hX y hs₁ hs₂ (hB hp) (hA p hp) (hw p hp)
    have h0 : (0 : ℝ) ≤ |∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T| := abs_nonneg _
    have hprod : (0 : ℝ) ≤ ‖w p‖
        * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) := by positivity
    rw [← sq_abs]
    nlinarith
  have hmeanSum := Finset.sum_le_sum hmean
  have hmeanNonneg : (0 : ℝ) ≤ ∑ p ∈ B, (∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  -- the variance is the second moment minus the mean squared
  have hbridge : ∑ p ∈ B, ((∫ ω, localLog (w p) (X (p : ℕ) ω)
          * localLog (w p) (X (p : ℕ) ω) ∂T)
        - (∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T) ^ 2)
      = (∑ p ∈ B, ∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2 ∂T)
        - ∑ p ∈ B, (∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (pow_two _).symm)
  rw [coe_blockMatchedVar₂ hX y hs₁ hs₂ hB hA hw, hbridge]
  -- split the target sum, and finish linearly
  have hsum : ∑ p ∈ B, (20 * ‖w p‖ ^ 3
        + 240 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
        + 3249 * ‖w p‖ ^ 2
          * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2)
      = (∑ p ∈ B, (20 * ‖w p‖ ^ 3
          + 240 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)))
        + ∑ p ∈ B, 3249 * ‖w p‖ ^ 2
            * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 := by
    rw [← Finset.sum_add_distrib]
  rw [hsum, abs_le]
  have hb₂ := abs_le.1 h₂
  constructor <;> linarith [hb₂.1, hb₂.2, hmeanSum, hmeanNonneg]

/-! ### The variance bracket at Harper's data

`RMF.blockMatchedVar_bounds` and `RMF.blockMatchedVar_concrete` at two points.  The distortion is
`ε₀ = 1000κ + 25992κ²` where the one-point one is `40κ + 5κ²`; at
`RMF.blockWeightSize_le_millionth`'s `κ ≤ 10^{-6}` that is `≤ 0.0011`, *smaller* than the one-point
`0.041`, because the sharper `κ` more than repays the heavier constants.  So the bracket is if
anything more comfortable here. -/

/-- **The two-point variance against block Mertens.** -/
theorem blockMatchedVar₂_bounds (hX : IsSteinhausPrimeValues X μ)
    (θ σ : ℝ) (j : ℕ) (s₁ s₂ : ℂ) (w : Nat.Primes → ℂ)
    (hjθ : (4 : ℝ) ≤ (j : ℝ) + θ) (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    (1 - (1000 * blockWeightSize θ j + 25992 * blockWeightSize θ j ^ 2))
          * (Real.exp (-2) * (1 - 60 / Real.log (blockScale θ (j + 1))))
        ≤ 2 * ((blockMatchedVar₂ X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s₁ s₂ w
            (primeBlockSub θ j) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVar₂ X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s₁ s₂ w
            (primeBlockSub θ j) : ℝ≥0) : ℝ)
          ≤ (1 + (1000 * blockWeightSize θ j + 25992 * blockWeightSize θ j ^ 2))
            * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1)))) := by
  have hj3 : (3 : ℝ) ≤ (j : ℝ) + θ := by linarith
  set κ := blockWeightSize θ j with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ j
  have hκm : κ ≤ 1 / 1000000 := blockWeightSize_le_millionth hjθ
  -- all three moduli are at most `κ` on the block
  have hw : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
  have ha₁ : ∀ p ∈ primeBlockSub θ j, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (norm_sq_prime_cpow_neg p hre₁)
  have ha₂ : ∀ p ∈ primeBlockSub θ j, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (norm_sq_prime_cpow_neg p hre₂)
  have hA : ∀ p ∈ primeBlockSub θ j,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    linarith [ha₁ p hp, ha₂ p hp]
  have hw5 : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ 1 / 5 := by
    intro p hp
    linarith [hw p hp]
  have hs₁ : 0 < s₁.re := re_pos_of_block hj3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hj3 hre₂ hσ
  have habs := abs_blockMatchedVar₂_sub_le hX (⌊blockScale θ (j + 1)⌋₊ + 1)
    (B := primeBlockSub θ j) hs₁ hs₂ (harperBlock_subset _) hA hw5
  set S := ∑ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hhalf : ∑ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 / 2 = S / 2 := by
    rw [hSdef, Finset.sum_div]
  -- the error, against `ε₀ S / 2`
  have herr : ∑ p ∈ primeBlockSub θ j, (20 * ‖w p‖ ^ 3
        + 240 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
        + 3249 * ‖w p‖ ^ 2
          * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2)
      ≤ (500 * κ + 12996 * κ ^ 2) * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h1 := hw p hp
    have h2 := ha₁ p hp
    have h3 := ha₂ p hp
    have hn0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hcube : ‖w p‖ ^ 3 ≤ κ * ‖w p‖ ^ 2 := by nlinarith [sq_nonneg (‖w p‖)]
    have hsum2 : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 2 * κ := by linarith
    have hsq2 : (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 ≤ 4 * κ ^ 2 := by
      nlinarith [norm_nonneg (((p : ℕ) : ℂ) ^ (-s₁)), norm_nonneg (((p : ℕ) : ℂ) ^ (-s₂))]
    nlinarith [sq_nonneg (‖w p‖), hcube, hsum2, hsq2, hκ0]
  rw [hhalf] at habs
  have hab := abs_le.1 (habs.trans herr)
  -- block Mertens
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (j + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  obtain ⟨hSlo, hShi⟩ := sum_norm_sq_harperBlock_bounds (blockScale θ (j + 1)) σ w hbig hσ hwn
  have hfac0 : (0 : ℝ) ≤ 1 - (1000 * κ + 25992 * κ ^ 2) := by nlinarith
  have hfac0u : (0 : ℝ) ≤ 1 + (1000 * κ + 25992 * κ ^ 2) := by nlinarith
  constructor
  · have h1 : (1 - (1000 * κ + 25992 * κ ^ 2))
          * (Real.exp (-2) * (1 - 60 / Real.log (blockScale θ (j + 1))))
        ≤ (1 - (1000 * κ + 25992 * κ ^ 2)) * S :=
      mul_le_mul_of_nonneg_left hSlo hfac0
    nlinarith [hab.1, h1]
  · have h1 : (1 + (1000 * κ + 25992 * κ ^ 2)) * S
        ≤ (1 + (1000 * κ + 25992 * κ ^ 2))
          * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1)))) :=
      mul_le_mul_of_nonneg_left hShi hfac0u
    nlinarith [hab.2, h1]

/-- **`1/8 ≤ 2V ≤ 9` for both coordinates of the pair**, from `j + θ ≥ 8`. -/
theorem blockMatchedVar₂_concrete (hX : IsSteinhausPrimeValues X μ)
    (θ σ : ℝ) (j : ℕ) (s₁ s₂ : ℂ) (w : Nat.Primes → ℂ)
    (hjθ : (8 : ℝ) ≤ (j : ℝ) + θ) (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    1 / 8 ≤ 2 * ((blockMatchedVar₂ X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s₁ s₂ w
        (primeBlockSub θ j) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVar₂ X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s₁ s₂ w
        (primeBlockSub θ j) : ℝ≥0) : ℝ) ≤ 9 := by
  have hj4 : (4 : ℝ) ≤ (j : ℝ) + θ := by linarith
  obtain ⟨hlo, hhi⟩ := blockMatchedVar₂_bounds hX θ σ j s₁ s₂ w hj4 hre₁ hre₂ hσ hwn
  have hκ := blockWeightSize_le_millionth hj4
  have hκ0 := blockWeightSize_pos θ j
  -- the distortion, at `κ ≤ 10^{-6}`
  have hfac1 : (0.9988 : ℝ)
      ≤ 1 - (1000 * blockWeightSize θ j + 25992 * blockWeightSize θ j ^ 2) := by nlinarith
  have hfac1u : 1 + (1000 * blockWeightSize θ j + 25992 * blockWeightSize θ j ^ 2)
      ≤ 1.0012 := by nlinarith
  -- the Mertens term at `j + θ ≥ 8`
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by
    rw [log_blockScale]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
      _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((j + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hLpos : (0 : ℝ) < Real.log (blockScale θ (j + 1)) := by linarith
  have hdiv0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (j + 1)) := by positivity
  have hdiv : (60 : ℝ) / Real.log (blockScale θ (j + 1)) ≤ 0.0086 := by
    rw [div_le_iff₀ hLpos]; linarith
  have hfac2 : (0.9914 : ℝ) ≤ 1 - 60 / Real.log (blockScale θ (j + 1)) := by linarith
  have hfac2u : 1 + 60 / Real.log (blockScale θ (j + 1)) ≤ 1.0086 := by linarith
  have he2 : Real.exp 2 ≤ 7.39 := by
    have hrw : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hrw]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hem2 : (0.135 : ℝ) ≤ Real.exp (-2) := by
    have hpos := Real.exp_pos (2 : ℝ)
    have hrw : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
    rw [hrw, le_div_iff₀ hpos]; linarith
  constructor
  · have hA : (0.135 : ℝ) * 0.9914
        ≤ Real.exp (-2) * (1 - 60 / Real.log (blockScale θ (j + 1))) :=
      mul_le_mul hem2 hfac2 (by norm_num) (Real.exp_pos _).le
    have hB : (0.9988 : ℝ) * (0.135 * 0.9914)
        ≤ (1 - (1000 * blockWeightSize θ j + 25992 * blockWeightSize θ j ^ 2))
          * (Real.exp (-2) * (1 - 60 / Real.log (blockScale θ (j + 1)))) :=
      mul_le_mul hfac1 hA (by norm_num) (by linarith)
    nlinarith [hlo, hB]
  · have hA : Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1)))
        ≤ (7.39 : ℝ) * 1.0086 :=
      mul_le_mul he2 hfac2u (by linarith) (by norm_num)
    have hB : (1 + (1000 * blockWeightSize θ j + 25992 * blockWeightSize θ j ^ 2))
          * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1))))
        ≤ (1.0012 : ℝ) * (7.39 * 1.0086) :=
      mul_le_mul hfac1u hA (by positivity) (by norm_num)
    nlinarith [hhi, hB]

/-! ### The drift at two points

The drift bound at two points, and the one place where the answer genuinely doubles: the
two-fold tilt puts **both** drifts into each coordinate, so the main term is
`∑_p (Re(w_p \bar a₁) + Re(w_p \bar a₂))`, and at Harper's weights both summands are `‖w_p‖²`.
The bound is `2S` where the one-point bound is `S`.

That doubling is Harper's drift, counted once per tilt, and the barrier in Proposition 7 is placed
to match; discarding it would change the theorem.

The error is `800κ·S`, from the two error terms of the two-fold mean
(`RMF.abs_integral_localLog_tiltedMeasure₂_sub_le`) with `A = 2‖w_p‖`; at
`RMF.blockWeightSize_le_millionth` that is `8·10^{-4}·S`. -/

/-- **The drift of one block, at two points.** -/
theorem abs_blockMean₂_le (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ} {θ σ : ℝ} {m n : ℕ}
    {w : Nat.Primes → ℂ} (hmθ : (4 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    |blockMean₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ m)|
      ≤ (2 + 800 * blockWeightSize θ m)
        * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1)))) := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  have hB := primeBlockSub_subset_primesBelowSub θ hmn
  set κ := blockWeightSize θ m with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ m
  have hκm : κ ≤ 1 / 1000000 := blockWeightSize_le_millionth hmθ
  -- at Harper's weights all three moduli agree, prime by prime
  have hnorm₁ : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖w p‖ := by
    intro p hp
    have h : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ‖w p‖ ^ 2 := by
      rw [norm_sq_prime_cpow_neg p hre₁, hwn p hp]
    calc ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖w p‖ ^ 2) := by rw [h]
      _ = ‖w p‖ := Real.sqrt_sq (norm_nonneg _)
  have hnorm₂ : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ = ‖w p‖ := by
    intro p hp
    have h : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 = ‖w p‖ ^ 2 := by
      rw [norm_sq_prime_cpow_neg p hre₂, hwn p hp]
    calc ‖((p : ℕ) : ℂ) ^ (-s₂)‖ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖w p‖ ^ 2) := by rw [h]
      _ = ‖w p‖ := Real.sqrt_sq (norm_nonneg _)
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := by
    intro p hp
    linarith [hwκ p hp]
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    rw [hnorm₁ p hp, hnorm₂ p hp]
    linarith [hwκ p hp]
  -- the block mean is the integral of the block sum
  have hbridge : blockMean₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ m)
      = ∫ ω, ∑ p ∈ primeBlockSub θ m, localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
          (blockCutoff θ n) s₁ s₂ μ) := by
    rw [blockMean₂, integral_finsetSum _ fun p hp =>
      integrable_localLog_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp) (hA p hp) (hw5 p hp)]
  have h1 := abs_integral_sum_localLog_tiltedMeasure₂_sub_le hX (blockCutoff θ n)
    (B := primeBlockSub θ m) hs₁ hs₂ hB hA hw5
  rw [← hbridge] at h1
  set S := ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun p _ => sq_nonneg _
  -- **the two drifts add**: the main term is `2S`, not `S`
  have hmain : |∑ p ∈ primeBlockSub θ m,
      ((w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re
        + (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re)| ≤ 2 * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hre : ∀ a : ℂ, |(w p * (starRingEnd ℂ) a).re| ≤ ‖w p‖ * ‖a‖ := by
      intro a
      refine (Complex.abs_re_le_norm _).trans_eq ?_
      rw [norm_mul]
      simp
    have hb₁ := hre (((p : ℕ) : ℂ) ^ (-s₁))
    have hb₂ := hre (((p : ℕ) : ℂ) ^ (-s₂))
    rw [hnorm₁ p hp] at hb₁
    rw [hnorm₂ p hp] at hb₂
    calc |(w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re
            + (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re|
        ≤ |(w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₁))).re|
            + |(w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s₂))).re| := abs_add_le _ _
      _ ≤ 2 * ‖w p‖ ^ 2 := by nlinarith [hb₁, hb₂]
  -- the error, against `800κ S`
  have herr : ∑ p ∈ primeBlockSub θ m,
        (160 * ‖w p‖ ^ 2 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)
          + 120 * ‖w p‖ * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2)
      ≤ 800 * κ * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [hnorm₁ p hp, hnorm₂ p hp]
    have hn0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hk := hwκ p hp
    nlinarith [hn0, hk, sq_nonneg (‖w p‖), hκ0]
  -- block Mertens caps `S`
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  obtain ⟨_, hShi⟩ := sum_norm_sq_harperBlock_bounds (blockScale θ (m + 1)) σ w hbig hσ hwn
  have hab := abs_le.1 (h1.trans herr)
  have hmn' := abs_le.1 hmain
  have hfac : (0 : ℝ) ≤ 2 + 800 * κ := by linarith
  have hprod : (2 + 800 * κ) * S
      ≤ (2 + 800 * κ) * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1)))) :=
    mul_le_mul_of_nonneg_left hShi hfac
  rw [abs_le]
  constructor <;> nlinarith [hab.1, hab.2, hmn'.1, hmn'.2, hprod, hS0, hκ0]

/-! ### `hqlow` at two points

The window mass bound at two points: the block Gaussian's box carries mass `blockQ₂ θ m`.  The
variances come from `RMF.blockMatchedVar₂_concrete`, the residual bracket and the covariance
conditions from `RMF.pairResidVar_bracket` and `RMF.abs_pairSlope_le_and_cs_of_abs_le`, the drift
from `RMF.abs_blockMean₂_le`, and the two thresholds from `RMF.hthr_of_fourteen_le` and
`RMF.hthr₂_of_fourteen_le`.

`hcov : |cv| ≤ 1/100` is not a fact about blocks: at `t₁ = t₂` the covariance is the full variance.
It is the height separation, which the block decorrelation estimate
`RMF.abs_cos_prime_sum_block_weight_le` controls, and `RMF.abs_blockMatchedCov_prime_sub_le`
reduces it to a bound on that cosine sum.  The statement is at the per-block cutoff
`blockCutoff θ m`; `RMF.blockQ₂_le_measure_of_le` is the global form. -/

/-- **`hqlow` at two points** — the block Gaussian's box carries mass at least `blockQ₂ θ m`. -/
theorem blockQ₂_le_measure (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m : ℕ} {s₁ s₂ : ℂ}
    {M : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hcov : |blockMatchedCov X μ (blockCutoff θ m) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| ≤ 1 / 100)
    (henv : M + (2 + 800 * blockWeightSize θ m)
            * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1))))
          + blockWindow m
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))) + 2) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      blockQ₂ θ m ≤ (gaussianPairLaw
          (blockMean₂ X μ (blockCutoff θ m) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
            (primeBlockSub θ m))
          (blockMean₂ X μ (blockCutoff θ m) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m))
          ((blockMatchedVar₂ X μ (blockCutoff θ m) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVar₂ X μ (blockCutoff θ m) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCov X μ (blockCutoff θ m) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
          (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m))).toReal := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hm8 : (8 : ℝ) ≤ (m : ℝ) + θ := by linarith
  -- `blockCutoff θ m` *is* the per-block cutoff; unfold so the brackets unify
  simp only [blockCutoff] at hcov ⊢
  have hwn₁ : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre₁
  have hwn₂ : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun p _ => norm_sq_prime_cpow_neg p hre₂
  -- the two variance brackets
  obtain ⟨hV₁l, hV₁u⟩ := blockMatchedVar₂_concrete hX θ σ m s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) hm8 hre₁ hre₂ hσ hwn₁
  obtain ⟨hV₂l, hV₂u⟩ := blockMatchedVar₂_concrete hX θ σ m s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) hm8 hre₁ hre₂ hσ hwn₂
  -- the covariance conditions, and with them the residual bracket.  The two variances must be
  -- named: they are implicit in `abs_pairSlope_le_and_cs_of_abs_le`, and only `cv` is pinned by
  -- `hcov`, so `linarith` would be handed a goal with metavariables in it.
  have hV₁16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVar₂ X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  have hV₂16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVar₂ X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  have hV₁pos : (0 : ℝ)
      < ((blockMatchedVar₂ X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  obtain ⟨hslope, hcs⟩ := abs_pairSlope_le_and_cs_of_abs_le hV₁16 hV₂16 hcov
  obtain ⟨hRl, hRu⟩ := pairResidVar_bracket hV₁pos hV₂l hV₂u hcs
  -- the two drifts
  have hd₁ := abs_blockMean₂_le hX (m := m) (n := m) hm4 le_rfl hre₁ hre₂ hσ hwn₁
  have hd₂ := abs_blockMean₂_le hX (m := m) (n := m) hm4 le_rfl hre₁ hre₂ hσ hwn₂
  simp only [blockCutoff] at hd₁ hd₂
  -- the window, and the scale
  have hh := blockWindow_pos m
  have hh1 : blockWindow m ≤ 1 := by
    rw [blockWindow]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [div_le_one (by positivity)]
    nlinarith
  have hx : (1 : ℝ) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    exact Real.one_le_exp (Real.exp_pos _).le
  intro c d hc hd
  rw [blockQ₂]
  refine le_toReal_measure_box_gaussianPairLaw_envelope hV₁l hV₁u hRl hRu hslope hh hh1 hx
    (by linarith) (by linarith) (hthr_of_fourteen_le hmθ) (hthr₂_of_fourteen_le hmθ)

/-! ### The cutoff is irrelevant

The two-fold analogue of `RMF.blockMean_congr_cutoff`.  Raising the cutoff multiplies the tilt by
factors at *other* primes, and those are independent of `X p`, so no moment of a single prime moves.
The proof is `RMF.integral_comp_tiltedMeasure₂` read at both cutoffs: each side equals the same
integral against the tilted circle law.

No hypothesis on the weights is needed — only that the block sits below both cutoffs. -/

/-- Any moment of a single `X p` is the same under either cutoff, for the two-fold tilt. -/
lemma integral_comp_tiltedMeasure₂_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) (hp' : p ∈ primesBelowSub y') {g : ℂ → ℝ} (hg : Measurable g) :
    (∫ ω, g (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      = ∫ ω, g (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y' s₁ s₂ μ) := by
  rw [integral_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp hg,
    integral_comp_tiltedMeasure₂ hX y' hs₁ hs₂ hp' hg]

/-- Hence the two-point block drift is cutoff-free. -/
lemma blockMean₂_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) (hB' : B ⊆ primesBelowSub y') (w : Nat.Primes → ℂ) :
    blockMean₂ X μ y s₁ s₂ w B = blockMean₂ X μ y' s₁ s₂ w B :=
  Finset.sum_congr rfl fun p hp =>
    integral_comp_tiltedMeasure₂_congr_cutoff hX hs₁ hs₂ (hB hp) (hB' hp)
      (measurable_localLog (w p))

/-- And so is the matched variance: both of `matchingVar`'s arguments are such moments. -/
lemma blockMatchedVar₂_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) (hB' : B ⊆ primesBelowSub y') (w : Nat.Primes → ℂ) :
    blockMatchedVar₂ X μ y s₁ s₂ w B = blockMatchedVar₂ X μ y' s₁ s₂ w B := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_comp_tiltedMeasure₂_congr_cutoff hX hs₁ hs₂ (hB hp) (hB' hp)
      (measurable_localLog (w p)),
    integral_comp_tiltedMeasure₂_congr_cutoff (g := fun z => localLog (w p) z * localLog (w p) z)
      hX hs₁ hs₂ (hB hp) (hB' hp) ((measurable_localLog (w p)).mul (measurable_localLog (w p)))]

/-- And so is the covariance — three moments this time, and the mixed one is no different. -/
lemma blockMatchedCov_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {y y' : ℕ} {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) (hB' : B ⊆ primesBelowSub y') (v w : Nat.Primes → ℂ) :
    blockMatchedCov X μ y s₁ s₂ v w B = blockMatchedCov X μ y' s₁ s₂ v w B := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_comp_tiltedMeasure₂_congr_cutoff (g := fun z => localLog (v p) z * localLog (w p) z)
      hX hs₁ hs₂ (hB hp) (hB' hp) ((measurable_localLog (v p)).mul (measurable_localLog (w p))),
    integral_comp_tiltedMeasure₂_congr_cutoff hX hs₁ hs₂ (hB hp) (hB' hp)
      (measurable_localLog (v p)),
    integral_comp_tiltedMeasure₂_congr_cutoff hX hs₁ hs₂ (hB hp) (hB' hp)
      (measurable_localLog (w p))]

/-- **The bridge, as the assembly needs it**, for all three statistics at once: block `j` of an
`n`-block run may be read at its own cutoff. -/
lemma blockStats₂_blockCutoff_eq (hX : IsSteinhausPrimeValues X μ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {θ : ℝ} {n j : ℕ} (hj : j ≤ n)
    (v w : Nat.Primes → ℂ) :
    blockMean₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ j)
        = blockMean₂ X μ (blockCutoff θ j) s₁ s₂ w (primeBlockSub θ j)
      ∧ blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂ w (primeBlockSub θ j)
        = blockMatchedVar₂ X μ (blockCutoff θ j) s₁ s₂ w (primeBlockSub θ j)
      ∧ blockMatchedCov X μ (blockCutoff θ n) s₁ s₂ v w (primeBlockSub θ j)
        = blockMatchedCov X μ (blockCutoff θ j) s₁ s₂ v w (primeBlockSub θ j) :=
  ⟨blockMean₂_congr_cutoff hX hs₁ hs₂ (primeBlockSub_subset_primesBelowSub θ hj)
      (primeBlockSub_subset_primesBelowSub θ le_rfl) w,
   blockMatchedVar₂_congr_cutoff hX hs₁ hs₂ (primeBlockSub_subset_primesBelowSub θ hj)
      (primeBlockSub_subset_primesBelowSub θ le_rfl) w,
   blockMatchedCov_congr_cutoff hX hs₁ hs₂ (primeBlockSub_subset_primesBelowSub θ hj)
      (primeBlockSub_subset_primesBelowSub θ le_rfl) v w⟩

/-- **`hqlow` at two points, at the global cutoff.**  `RMF.blockQ₂_le_measure` read through the
congruence — which is all that separates the single-block development from the assembly. -/
theorem blockQ₂_le_measure_of_le (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ}
    {s₁ s₂ : ℂ} {M : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hcov : |blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| ≤ 1 / 100)
    (henv : M + (2 + 800 * blockWeightSize θ m)
            * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1))))
          + blockWindow m
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))) + 2) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      blockQ₂ θ m ≤ (gaussianPairLaw
          (blockMean₂ X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
            (primeBlockSub θ m))
          (blockMean₂ X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m))
          ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂ (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
          (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m))).toReal := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  obtain ⟨hm₁, hv₁, -⟩ := blockStats₂_blockCutoff_eq hX hs₁ hs₂ hmn
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
  obtain ⟨hm₂, hv₂, hcv⟩ := blockStats₂_blockCutoff_eq hX hs₁ hs₂ hmn
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
  rw [hm₁, hm₂, hv₁, hv₂, hcv]
  rw [hcv] at hcov
  exact blockQ₂_le_measure hX hmθ hre₁ hre₂ hσ hcov henv

/-! ### The per-prime moment matrix is positive semidefinite

`RMF.exists_gaussian_pair_matching_quadMonomial` will only match a target it can meet: it asks that
the five raw moments come from a genuine covariance matrix.  For a real random pair that is
Cauchy–Schwarz, and `RMF.psd_of_integrable_pair` proves it from integrability alone — so the whole
content here is the fifth integrability, the **mixed** product `localLog v · localLog w`, which the
one-fold development never needed.

Same proof as its two companions: both factors are bounded on the circle, where the two-fold tilt
lives, and the tilt is a probability measure.

*The moments are parameters of the psd statement below, not integrals written out.*  That keeps
the conclusion five reals wide instead of ten copies of the tilted measure, and it is the form the
assembly wants anyway. -/

/-- The mixed product of two local terms is integrable against the two-fold tilted law. -/
lemma integrable_localLog_mul_tilted_pair {a₁ a₂ v w : ℂ} (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5)
    (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun z => localLog v z * localLog w z)
      (steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z) := by
  have hprob := isProbabilityMeasure_tilted_localLog_pair hA
  refine (integrable_const ((11 / 5 * ‖v‖) * (11 / 5 * ‖w‖))).mono'
    ((measurable_localLog v).mul (measurable_localLog w)).aestronglyMeasurable ?_
  filter_upwards [ae_norm_eq_one_tilted_pair (a₁ := a₁) (a₂ := a₂)] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_localLog_le_of_norm_le hz hv) (abs_localLog_le_of_norm_le hz hw)
    (abs_nonneg _) (by positivity)

/-- The mixed product is integrable under the two-fold tilt. -/
lemma integrable_localLog_mul_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLog v (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp (integrable_localLog_mul_tilted_pair hA hv hw)

/-- **The per-prime moment matrix is positive semidefinite** under the two-fold tilt:
`0 ≤ q₁ - m₁²`, `0 ≤ q₂ - m₂²` and `(q₁₂ - m₁m₂)² ≤ (q₁ - m₁²)(q₂ - m₂²)`.  The five moments are
parameters pinned by hypotheses: written out, the conclusion names the tilted measure ten times and
elaboration times out before any proof runs. -/
theorem psd_of_tiltedMeasure₂_moments (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) {m₁ m₂ q₁ q₁₂ q₂ : ℝ}
    (hm₁ : m₁ = ∫ ω, localLog v (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
    (hm₂ : m₂ = ∫ ω, localLog w (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
    (hq₁ : q₁ = ∫ ω, localLog v (X (p : ℕ) ω) * localLog v (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
    (hq₁₂ : q₁₂ = ∫ ω, localLog v (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
    (hq₂ : q₂ = ∫ ω, localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)) :
    0 ≤ q₁ - m₁ ^ 2 ∧ 0 ≤ q₂ - m₂ ^ 2
      ∧ (q₁₂ - m₁ * m₂) ^ 2 ≤ (q₁ - m₁ ^ 2) * (q₂ - m₂ ^ 2) := by
  -- Name the measure, and pin `g` in every `integrable_comp_tiltedMeasure₂`: left implicit it is a
  -- higher-order unification (`?g (X p ω) ≟ localLog v (X p ω) * localLog v (X p ω)`), and that is
  -- what times out here, not the size of anything.
  obtain ⟨T, hT⟩ : ∃ T : Measure Ω,
      T = tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ := ⟨_, rfl⟩
  have hprob : IsProbabilityMeasure T := by
    rw [hT]; exact hX.isProbabilityMeasure_tiltedMeasure₂ y hs₁ hs₂
  have h₁ : Integrable (fun ω => localLog v (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLog_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hv
  have h₂ : Integrable (fun ω => localLog w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLog_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hw
  have h₁₁ : Integrable
      (fun ω => localLog v (X (p : ℕ) ω) * localLog v (X (p : ℕ) ω)) T := by
    rw [hT]
    exact integrable_comp_tiltedMeasure₂ (g := fun z => localLog v z * localLog v z)
      hX y hs₁ hs₂ hp (integrable_localLog_mul_self_tilted_pair hA hv)
  have h₁₂ : Integrable
      (fun ω => localLog v (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLog_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hv hw
  have h₂₂ : Integrable
      (fun ω => localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)) T := by
    rw [hT]
    exact integrable_comp_tiltedMeasure₂ (g := fun z => localLog w z * localLog w z)
      hX y hs₁ hs₂ hp (integrable_localLog_mul_self_tilted_pair hA hw)
  have h := psd_of_integrable_pair (P := T)
    (ξ := fun ω => (localLog v (X (p : ℕ) ω), localLog w (X (p : ℕ) ω)))
    h₁ h₂ h₁₁ h₁₂ h₂₂
  rw [hm₁, hm₂, hq₁, hq₁₂, hq₂, ← hT]
  exact h

/-- **A sum of pairs is the pair of sums.**  Needed wherever a pair-valued family is grouped into
block sums: the grouping lemma produces `∑ p ∈ B, F p ω`, while the comparison states its
hypotheses coordinatewise.  This Mathlib has no `Prod.fst_sum`, so it is an induction. -/
lemma sum_pair_eq {α : Type*} (F : Nat.Primes → α → ℝ × ℝ) (B : Finset Nat.Primes) :
    (fun ω => ∑ p ∈ B, F p ω)
      = fun ω => ((∑ p ∈ B, (F p ω).1), ∑ p ∈ B, (F p ω).2) := by
  classical
  funext ω
  induction B using Finset.induction_on with
  | empty => simp [Prod.ext_iff]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
      rfl

/-! ### The matched Gaussian family for a block

`RMF.exists_gaussian_pair_matching_quadMonomial` supplies an independent family of bivariate
Gaussians matching any positive-semidefinite target, and `RMF.psd_of_tiltedMeasure₂_moments` says
the tilted block moments are such a target.  Reading off the **block** law then costs nothing: the
parameters `RMF.map_sum_eq_gaussianPairLaw` produces are `∑_p μ₁`, `∑_p (q₁ - μ₁²)` and
`∑_p (q₁₂ - μ₁μ₂)`, which are `RMF.blockMean₂`, `RMF.blockMatchedVar₂` and `RMF.blockMatchedCov`
**by definition**.

The targets are guarded by `if p ∈ B`: off the block the weights carry no bound, so neither the
moments nor their positive semidefiniteness is available, and there is nothing to match.  Zero is a
legitimate target there — it is the degenerate Gaussian — and the block sum never sees it. -/

/-- **The matched Gaussian family for a block, with its law.** -/
theorem exists_gaussian_pair_block (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {S : Finset Nat.Primes} (hS : S ⊆ primesBelowSub y)
    (hA : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v w : Nat.Primes → ℂ} (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 5) (hw : ∀ p ∈ S, ‖w p‖ ≤ 1 / 5) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G : Nat.Primes → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ p, Measurable (G p)) ∧ iIndepFun G Q ∧
        (∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
            (localLog (v p) (X (p : ℕ) ω), localLog (w p) (X (p : ℕ) ω))
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
          = ∫ ω, quadMonomial j (G p ω) ∂Q) ∧
        (∀ p ∈ S, Q.map (G p) = gaussianPairLaw
          (∫ ω, localLog (v p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
          (∫ ω, localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
          ((∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
            - (∫ ω, localLog (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2)
          ((∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
            - (∫ ω, localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2)
          ((∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
            - (∫ ω, localLog (v p) (X (p : ℕ) ω)
                ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
              * ∫ ω, localLog (w p) (X (p : ℕ) ω)
                ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))) ∧
        (∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
          (∫ ω, localLog (v p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
          (matchingVar
            (∫ ω, localLog (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
            (∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)))) ∧
        (∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
          (∫ ω, localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
          (matchingVar
            (∫ ω, localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
            (∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)))) ∧
        ∀ B ⊆ S, Q.map (fun ω => ∑ p ∈ B, G p ω)
          = gaussianPairLaw (blockMean₂ X μ y s₁ s₂ v B) (blockMean₂ X μ y s₁ s₂ w B)
              ((blockMatchedVar₂ X μ y s₁ s₂ v B : ℝ≥0) : ℝ)
              ((blockMatchedVar₂ X μ y s₁ s₂ w B : ℝ≥0) : ℝ)
              (blockMatchedCov X μ y s₁ s₂ v w B) := by
  classical
  set T := tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ with hTdef
  -- the target moments, zero off the block
  set μ₁ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLog (v p) (X (p : ℕ) ω) ∂T else 0 with hμ₁
  set μ₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLog (w p) (X (p : ℕ) ω) ∂T else 0 with hμ₂
  set q₁ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (v p) (X (p : ℕ) ω) ∂T
    else 0 with hq₁
  set q₁₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLog (v p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T
    else 0 with hq₁₂
  set q₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω) ∂T
    else 0 with hq₂
  -- positive semidefiniteness: `psd_of_tiltedMeasure₂_moments` on the block, zero off it
  have hpsd : ∀ p, 0 ≤ q₁ p - μ₁ p ^ 2 ∧ 0 ≤ q₂ p - μ₂ p ^ 2
      ∧ (q₁₂ p - μ₁ p * μ₂ p) ^ 2 ≤ (q₁ p - μ₁ p ^ 2) * (q₂ p - μ₂ p ^ 2) := by
    intro p
    by_cases hp : p ∈ S
    · simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_pos hp]
      exact psd_of_tiltedMeasure₂_moments hX y hs₁ hs₂ (hS hp) (hA p hp) (hv p hp) (hw p hp)
        rfl rfl rfl rfl rfl
    · simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_neg hp]
      norm_num
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hGlaw, h0, h1, h2, h3, h4⟩ :=
    exists_gaussian_pair_matching_quadMonomial μ₁ μ₂ q₁ q₁₂ q₂
      (fun p => (hpsd p).1) (fun p => (hpsd p).2.1) (fun p => (hpsd p).2.2)
  refine ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, ?_, ?_, ?_, ?_, ?_⟩
  · -- the five moments agree on the block
    intro p hp j
    fin_cases j
    · have e := h0 p
      simp only [quadMonomial, hμ₁, if_pos hp] at e ⊢
      exact e.symm
    · have e := h1 p
      simp only [quadMonomial, hμ₂, if_pos hp] at e ⊢
      exact e.symm
    · have e := h2 p
      simp only [quadMonomial, hq₁, if_pos hp] at e ⊢
      exact e.symm
    · have e := h3 p
      simp only [quadMonomial, hq₁₂, if_pos hp] at e ⊢
      exact e.symm
    · have e := h4 p
      simp only [quadMonomial, hq₂, if_pos hp] at e ⊢
      exact e.symm
  · -- the per-prime pair law: the marginals alone would not give the Gaussian side's
    -- integrability, which is stated for the pair
    intro p hp
    rw [hGlaw p]
    simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_pos hp, hTdef]
  · -- the first marginal, which is what the third-moment bound consumes
    intro p hp
    have hmap : Q.map (fun ω => (G p ω).1) = (Q.map (G p)).map Prod.fst := by
      rw [Measure.map_map measurable_fst (hGm p)]
      rfl
    rw [hmap, hGlaw p, map_fst_gaussianPairLaw (hpsd p).1 (hpsd p).2.1 (hpsd p).2.2]
    simp only [hμ₁, hq₁, if_pos hp, matchingVar, hTdef]
  · -- and the second
    intro p hp
    have hmap : Q.map (fun ω => (G p ω).2) = (Q.map (G p)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hGm p)]
      rfl
    rw [hmap, hGlaw p, map_snd_gaussianPairLaw (hpsd p).1 (hpsd p).2.1 (hpsd p).2.2]
    simp only [hμ₂, hq₂, if_pos hp, matchingVar, hTdef]
  · -- the block law, for every block inside `S`; the three sums are the three block statistics
    -- by definition
    intro B hBS
    rw [map_sum_eq_gaussianPairLaw hGm hGi hGlaw (fun p => (hpsd p).1) (fun p => (hpsd p).2.1)
      (fun p => (hpsd p).2.2) B]
    have hmean₁ : ∑ p ∈ B, μ₁ p = blockMean₂ X μ y s₁ s₂ v B := by
      rw [blockMean₂]
      exact Finset.sum_congr rfl fun p hp => by simp only [hμ₁, if_pos (hBS hp), hTdef]
    have hmean₂ : ∑ p ∈ B, μ₂ p = blockMean₂ X μ y s₁ s₂ w B := by
      rw [blockMean₂]
      exact Finset.sum_congr rfl fun p hp => by simp only [hμ₂, if_pos (hBS hp), hTdef]
    have hvar₁ : ∑ p ∈ B, (q₁ p - μ₁ p ^ 2)
        = ((blockMatchedVar₂ X μ y s₁ s₂ v B : ℝ≥0) : ℝ) := by
      rw [coe_blockMatchedVar₂ hX y hs₁ hs₂ (hBS.trans hS) (fun p hp => hA p (hBS hp))
        (fun p hp => hv p (hBS hp))]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₁, hq₁, if_pos (hBS hp), hTdef]
    have hvar₂ : ∑ p ∈ B, (q₂ p - μ₂ p ^ 2)
        = ((blockMatchedVar₂ X μ y s₁ s₂ w B : ℝ≥0) : ℝ) := by
      rw [coe_blockMatchedVar₂ hX y hs₁ hs₂ (hBS.trans hS) (fun p hp => hA p (hBS hp))
        (fun p hp => hw p (hBS hp))]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₂, hq₂, if_pos (hBS hp), hTdef]
    have hcov : ∑ p ∈ B, (q₁₂ p - μ₁ p * μ₂ p) = blockMatchedCov X μ y s₁ s₂ v w B := by
      rw [blockMatchedCov]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₁, hμ₂, hq₁₂, if_pos (hBS hp), hTdef]
    rw [hmean₁, hmean₂, hvar₁, hvar₂, hcov]

/-! ### Everything the tilted side has to be integrable for

The bivariate comparison asks for six integrability facts about the tilted increments: the five
`RMF.quadMonomial`s, the Lindeberg bound, and the two third absolute moments.  Every one of them is
the same observation — **the two-fold tilt lives on the circle, where `localLog` is bounded** — so
they all factor through one helper, and the only thing that differs is the bound. -/

/-- A measurable observable bounded on the circle is integrable against the two-fold tilted law. -/
lemma integrable_of_bounded_tilted_pair {a₁ a₂ : ℂ} (hA : ‖a₁‖ + ‖a₂‖ ≤ 1 / 5)
    {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ} (hbd : ∀ z : ℂ, ‖z‖ = 1 → |g z| ≤ C) :
    Integrable g (steinhausLaw.tilted fun z => 2 * localLog a₁ z + 2 * localLog a₂ z) := by
  have hprob := isProbabilityMeasure_tilted_localLog_pair hA
  refine (integrable_const C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [ae_norm_eq_one_tilted_pair (a₁ := a₁) (a₂ := a₂)] with z hz
  rw [Real.norm_eq_abs]
  exact hbd z hz

/-- The same, transported to the two-fold tilt itself. -/
lemma integrable_comp_tiltedMeasure₂_of_bounded (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {g : ℂ → ℝ} (hg : Measurable g) {C : ℝ} (hbd : ∀ z : ℂ, ‖z‖ = 1 → |g z| ≤ C) :
    Integrable (fun ω => g (X (p : ℕ) ω))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) :=
  integrable_comp_tiltedMeasure₂ hX y hs₁ hs₂ hp
    (integrable_of_bounded_tilted_pair hA hg hbd)

/-- **The Lindeberg bound is integrable** on the tilted side.  On the circle both coordinates are
at most `11/25`, so the cube bound `RMF.windowLindebergBound_le` caps it by `900δ^{-3}(22/25)³`. -/
lemma integrable_windowLindebergBound_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ω => windowLindebergBound δ
        (localLog v (X (p : ℕ) ω), localLog w (X (p : ℕ) ω)))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  refine integrable_comp_tiltedMeasure₂_of_bounded hX y hs₁ hs₂ hp hA
    (g := fun z => windowLindebergBound δ (localLog v z, localLog w z))
    ((measurable_windowLindebergBound δ).comp
      ((measurable_localLog v).prodMk (measurable_localLog w)))
    (C := 900 / δ ^ 3 * (22 / 25) ^ 3) ?_
  intro z hz
  have hbv := abs_localLog_le_of_norm_le hz hv
  have hbw := abs_localLog_le_of_norm_le hz hw
  have hnn : (0 : ℝ) ≤ windowLindebergBound δ (localLog v z, localLog w z) := by
    rw [windowLindebergBound, lindebergBound]
    have h₃ : (0 : ℝ) < δ ^ 3 := by positivity
    positivity
  have hle := windowLindebergBound_le hδ (localLog v z, localLog w z)
  have hcube : (|localLog v z| + |localLog w z|) ^ 3 ≤ (22 / 25 : ℝ) ^ 3 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    nlinarith [hbv, hbw, hv, hw, norm_nonneg v, norm_nonneg w]
  have hcoef : (0 : ℝ) ≤ 900 / δ ^ 3 := by positivity
  rw [abs_of_nonneg hnn]
  calc windowLindebergBound δ (localLog v z, localLog w z)
      ≤ 900 / δ ^ 3 * (|localLog v z| + |localLog w z|) ^ 3 := hle
    _ ≤ 900 / δ ^ 3 * (22 / 25 : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hcube hcoef

/-- **The third absolute moment is integrable** on the tilted side. -/
lemma integrable_abs_cube_localLog_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v : ℂ} (hv : ‖v‖ ≤ 1 / 5) :
    Integrable (fun ω => |localLog v (X (p : ℕ) ω)| ^ 3)
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  refine integrable_comp_tiltedMeasure₂_of_bounded hX y hs₁ hs₂ hp hA
    (g := fun z => |localLog v z| ^ 3)
    (((measurable_localLog v).abs).pow_const 3) (C := (11 / 25 : ℝ) ^ 3) ?_
  intro z hz
  have hbv := abs_localLog_le_of_norm_le hz hv
  have h0 : (0 : ℝ) ≤ |localLog v z| := abs_nonneg _
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |localLog v z| ^ 3)]
  refine pow_le_pow_left₀ h0 ?_ 3
  nlinarith [hbv, hv, norm_nonneg v]

/-- **The five `quadMonomial`s are integrable** on the tilted side. -/
lemma integrable_quadMonomial_localLog_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) (j : Fin 5) :
    Integrable (fun ω => quadMonomial j
        (localLog v (X (p : ℕ) ω), localLog w (X (p : ℕ) ω)))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) := by
  fin_cases j <;> simp only [quadMonomial]
  · exact integrable_localLog_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hv
  · exact integrable_localLog_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hw
  · exact integrable_comp_tiltedMeasure₂ (g := fun z => localLog v z * localLog v z)
      hX y hs₁ hs₂ hp (integrable_localLog_mul_self_tilted_pair hA hv)
  · exact integrable_localLog_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hA hv hw
  · exact integrable_comp_tiltedMeasure₂ (g := fun z => localLog w z * localLog w z)
      hX y hs₁ hs₂ hp (integrable_localLog_mul_self_tilted_pair hA hw)

/-! ### Everything the Gaussian side has to be integrable for

The mirror of the previous section, and it factors through one helper for the same reason — only
the bound is different.  A Gaussian has no bounded range, so the dominating function is not a
constant but `C(1 + |z₁|³ + |z₂|³)`, and the two cubes are integrable by
`RMF.integrable_abs_cube_fst_gaussianPairLaw`.  Every observable the comparison needs — the five
`RMF.quadMonomial`s, the Lindeberg bound, the two third moments — is dominated by that. -/

/-- An observable dominated by the two cubes is integrable against `RMF.gaussianPairLaw`. -/
lemma integrable_of_cube_dominated_gaussianPairLaw {m₁ m₂ V₁ V₂ cv : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : cv ^ 2 ≤ V₁ * V₂) {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hbd : ∀ z : ℝ × ℝ, |f z| ≤ C * (1 + |z.1| ^ 3 + |z.2| ^ 3)) :
    Integrable f (gaussianPairLaw m₁ m₂ V₁ V₂ cv) := by
  have hc₁ := integrable_abs_cube_fst_gaussianPairLaw (m₁ := m₁) (m₂ := m₂) hV₁ hV₂ hCS
  have hc₂ := integrable_abs_cube_snd_gaussianPairLaw (m₁ := m₁) (m₂ := m₂) hV₁ hV₂ hCS
  have hdom : Integrable (fun z : ℝ × ℝ => C * (1 + |z.1| ^ 3 + |z.2| ^ 3))
      (gaussianPairLaw m₁ m₂ V₁ V₂ cv) :=
    (((integrable_const (1 : ℝ)).add hc₁).add hc₂).const_mul C
  refine hdom.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact hbd z

/-- **The five `quadMonomial`s are integrable** on the Gaussian side.  Each is dominated by the
cubes: `|zᵢ| ≤ 1 + |zᵢ|³` and `|zᵢzⱼ| ≤ |zᵢ|³ + |zⱼ|³ + 1`. -/
lemma integrable_quadMonomial_gaussianPairLaw {m₁ m₂ V₁ V₂ cv : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : cv ^ 2 ≤ V₁ * V₂) (j : Fin 5) :
    Integrable (fun z : ℝ × ℝ => quadMonomial j z) (gaussianPairLaw m₁ m₂ V₁ V₂ cv) := by
  have key : ∀ a b : ℝ, |a * b| ≤ 1 + |a| ^ 3 + |b| ^ 3 := by
    intro a b
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - 1), sq_nonneg (|b| - 1),
      mul_nonneg ha hb, sq_nonneg (|a| * |b| - 1)]
  have lin : ∀ a : ℝ, |a| ≤ 1 + |a| ^ 3 := by
    intro a
    nlinarith [abs_nonneg a, sq_nonneg (|a| - 1), sq_nonneg (|a| + 1)]
  -- the diagonal needs its own bound: `key a a` spends *two* cubes, and only one is available
  have sq : ∀ a : ℝ, |a * a| ≤ 1 + |a| ^ 3 := by
    intro a
    rw [abs_mul]
    nlinarith [mul_nonneg (sq_nonneg (|a| - 1)) (by linarith [abs_nonneg a] : (0 : ℝ) ≤ |a| + 1),
      abs_nonneg a]
  fin_cases j <;> simp only [quadMonomial] <;>
    refine integrable_of_cube_dominated_gaussianPairLaw hV₁ hV₂ hCS (by fun_prop)
      (C := 1) fun z => ?_
  · have := lin z.1
    have h := abs_nonneg z.2
    nlinarith [pow_nonneg h 3]
  · have := lin z.2
    have h := abs_nonneg z.1
    nlinarith [pow_nonneg h 3]
  · have := sq z.1
    nlinarith [pow_nonneg (abs_nonneg z.2) 3]
  · have := key z.1 z.2
    nlinarith
  · have := sq z.2
    nlinarith [pow_nonneg (abs_nonneg z.1) 3]

/-- **The Lindeberg bound is integrable** on the Gaussian side, by
`RMF.windowLindebergBound_le` and `RMF.add_cube_le`. -/
lemma integrable_windowLindebergBound_gaussianPairLaw {m₁ m₂ V₁ V₂ cv : ℝ} (hV₁ : 0 ≤ V₁)
    (hV₂ : 0 ≤ V₂) (hCS : cv ^ 2 ≤ V₁ * V₂) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun z : ℝ × ℝ => windowLindebergBound δ z)
      (gaussianPairLaw m₁ m₂ V₁ V₂ cv) := by
  refine integrable_of_cube_dominated_gaussianPairLaw hV₁ hV₂ hCS
    (measurable_windowLindebergBound δ) (C := 3600 / δ ^ 3) fun z => ?_
  have hnn : (0 : ℝ) ≤ windowLindebergBound δ z := by
    rw [windowLindebergBound, lindebergBound]
    have h₃ : (0 : ℝ) < δ ^ 3 := by positivity
    positivity
  have hle := windowLindebergBound_le hδ z
  have hcube := add_cube_le (abs_nonneg z.1) (abs_nonneg z.2)
  have hcoef : (0 : ℝ) < 900 / δ ^ 3 := by positivity
  rw [abs_of_nonneg hnn]
  have hstep : 900 / δ ^ 3 * (|z.1| + |z.2|) ^ 3
      ≤ 900 / δ ^ 3 * (4 * (|z.1| ^ 3 + |z.2| ^ 3)) :=
    mul_le_mul_of_nonneg_left hcube hcoef.le
  have hfin : 900 / δ ^ 3 * (4 * (|z.1| ^ 3 + |z.2| ^ 3))
      ≤ 3600 / δ ^ 3 * (1 + |z.1| ^ 3 + |z.2| ^ 3) := by
    have h₁ : (0 : ℝ) ≤ 900 / δ ^ 3 := hcoef.le
    have hrw : 900 / δ ^ 3 * (4 * (|z.1| ^ 3 + |z.2| ^ 3))
        = 3600 / δ ^ 3 * (|z.1| ^ 3 + |z.2| ^ 3) := by ring
    rw [hrw]
    have : (0 : ℝ) ≤ 3600 / δ ^ 3 := by positivity
    nlinarith
  linarith [hle, hstep, hfin]

/-! ### The third moment, and why `blockThirdConst₂` is what it is

`RMF.blockThirdConst₂` is `2·((11/5)³ + 4(c₃(11/5)³ + (57/5)³))`, and this section is what makes
those three numbers facts rather than a guess.  Per coordinate:

* the summand's own third moment, `(11/5)³‖v‖³`, unchanged from one point;
* the matched Gaussian's, `4(c₃√m₂³ + |m₁|³)`, with `√m₂ ≤ (11/5)‖v‖` — also unchanged — and
  `|m₁| ≤ (57/5)‖v‖`, which is **not**: one-fold the mean is `≤ (49/240)‖v‖`, and the two-fold
  tilt makes the two drifts add. -/

/-- The second moment under the two-fold tilt, crudely: `localLog` is bounded on the circle. -/
lemma integral_localLog_sq_tiltedMeasure₂_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v : ℂ} (hv : ‖v‖ ≤ 1 / 5) :
    (∫ ω, localLog v (X (p : ℕ) ω) * localLog v (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      ≤ (11 / 5 : ℝ) ^ 2 * ‖v‖ ^ 2 := by
  have hprob := isProbabilityMeasure_tilted_localLog_pair hA
  rw [integral_comp_tiltedMeasure₂ (g := fun z => localLog v z * localLog v z)
    hX y hs₁ hs₂ hp ((measurable_localLog v).mul (measurable_localLog v))]
  have hbd : ∀ᵐ z ∂(steinhausLaw.tilted fun z =>
      2 * localLog (((p : ℕ) : ℂ) ^ (-s₁)) z + 2 * localLog (((p : ℕ) : ℂ) ^ (-s₂)) z),
      localLog v z * localLog v z ≤ (11 / 5 : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    filter_upwards [ae_norm_eq_one_tilted_pair
      (a₁ := ((p : ℕ) : ℂ) ^ (-s₁)) (a₂ := ((p : ℕ) : ℂ) ^ (-s₂))] with z hz
    have hb := abs_localLog_le_of_norm_le hz hv
    nlinarith [abs_nonneg (localLog v z), sq_abs (localLog v z), norm_nonneg v]
  refine le_trans (integral_mono_ae (integrable_localLog_mul_self_tilted_pair hA hv)
    (integrable_const _) hbd) ?_
  simp

/-- **The matched Gaussian's third moment, under the two-fold tilt.**

`RMF.integral_abs_cube_matching_localLog_le` with `(57/5)` for `(49/240)` — and that single
substitution is the whole `76×` in `RMF.blockThirdConst₂`. -/
theorem integral_abs_cube_matching_localLog_tiltedMeasure₂_le {Ω' : Type*}
    [MeasurableSpace Ω'] {Q : Measure Ω'} {Y : Ω' → ℝ}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLog v (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLog v (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        (∫ ω, localLog v (X (p : ℕ) ω) * localLog v (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)))) :
    ∫ ω, |Y ω| ^ 3 ∂Q
      ≤ 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (57 / 5 : ℝ) ^ 3) * ‖v‖ ^ 3 := by
  set m₁ : ℝ := ∫ ω, localLog v (X (p : ℕ) ω)
    ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) with hm₁
  set m₂ : ℝ := ∫ ω, localLog v (X (p : ℕ) ω) * localLog v (X (p : ℕ) ω)
    ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) with hm₂
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hcs : m₁ ^ 2 ≤ m₂ :=
    sq_integral_localLog_le_integral_mul_self₂ hX y hs₁ hs₂ hp hA hv
  -- **the mean, and this is the one that moved**
  have hmean : |m₁| ≤ 57 / 5 * ‖v‖ := by
    have hb := abs_integral_localLog_tiltedMeasure₂_le hX y hs₁ hs₂ hp hA hv
    nlinarith [abs_nonneg m₁, norm_nonneg (((p : ℕ) : ℂ) ^ (-s₁)),
      norm_nonneg (((p : ℕ) : ℂ) ^ (-s₂))]
  have hmean₃ : |m₁| ^ 3 ≤ (57 / 5 : ℝ) ^ 3 * ‖v‖ ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg m₁) hmean 3
    calc |m₁| ^ 3 ≤ (57 / 5 * ‖v‖) ^ 3 := this
      _ = (57 / 5 : ℝ) ^ 3 * ‖v‖ ^ 3 := by ring
  -- the second moment, unchanged
  have hsq : m₂ ≤ (11 / 5 * ‖v‖) ^ 2 := by
    have h := integral_localLog_sq_tiltedMeasure₂_le hX y hs₁ hs₂ hp hA hv
    calc m₂ ≤ (11 / 5 : ℝ) ^ 2 * ‖v‖ ^ 2 := h
      _ = (11 / 5 * ‖v‖) ^ 2 := by ring
  have hroot : Real.sqrt m₂ ≤ 11 / 5 * ‖v‖ := by
    refine le_trans (Real.sqrt_le_sqrt hsq) ?_
    rw [Real.sqrt_sq (by positivity)]
  have hroot₃ : Real.sqrt m₂ ^ 3 ≤ (11 / 5 : ℝ) ^ 3 * ‖v‖ ^ 3 := by
    calc Real.sqrt m₂ ^ 3 ≤ (11 / 5 * ‖v‖) ^ 3 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 3
      _ = (11 / 5 : ℝ) ^ 3 * ‖v‖ ^ 3 := by ring
  refine le_trans (integral_abs_cube_of_hasLaw_matching hYm hcs hlaw) ?_
  have hc := absMomentConst_nonneg 3
  nlinarith [hroot₃, hmean₃]

/-- **The two halves together, per prime and per coordinate**:
`E~|ξ|³ + E|G|³ ≤ (blockThirdConst₂/2)·‖v‖³`. -/
theorem third_moment_pair_add_matching_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω' → ℝ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    {v : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLog v (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLog v (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
        (∫ ω, localLog v (X (p : ℕ) ω) * localLog v (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ)))) :
    (∫ ω, |localLog v (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ))
      + ∫ ω, |Y ω| ^ 3 ∂Q
      ≤ ((11 / 5 : ℝ) ^ 3
          + 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (57 / 5 : ℝ) ^ 3)) * ‖v‖ ^ 3 := by
  have hξ := integral_abs_localLog_cube_tiltedMeasure₂_le hX y hs₁ hs₂ hp hA hv
  have hG := integral_abs_cube_matching_localLog_tiltedMeasure₂_le hX y hs₁ hs₂ hp hA hv hYm hlaw
  nlinarith [hξ, hG]

/-! ### `hTb` at Harper's weights

The four third moments per prime, summed over the block, against `RMF.blockT₂`.  Both coordinates
carry `p^{-s_i}` with the same real part, so `‖v_p‖ = ‖w_p‖` and the two applications of
`RMF.third_moment_pair_add_matching_le` give `blockThirdConst₂·‖v_p‖³` between them — which is what
that constant was defined to be.  `RMF.sum_norm_cube_primeBlockSub_le` then finishes it. -/

/-- **`hTb` at Harper's weights.** -/
theorem sum_third_moment_pair_block_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {G : Nat.Primes → Ω' → ℝ × ℝ} (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m y : ℕ}
    {s₁ s₂ : ℂ} (hy : primeBlockSub θ m ⊆ primesBelowSub y)
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hGm : ∀ p, Measurable (G p))
    (hlaw₁ : ∀ p ∈ primeBlockSub θ m, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
          y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            y s₁ s₂ μ))
        (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
            * localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            y s₁ s₂ μ))))
    (hlaw₂ : ∀ p ∈ primeBlockSub θ m, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
          y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            y s₁ s₂ μ))
        (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
            * localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            y s₁ s₂ μ)))) :
    ∑ p ∈ primeBlockSub θ m,
        ((∫ ω, |localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)| ^ 3
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
              y s₁ s₂ μ))
          + (∫ ω, |localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)| ^ 3
            ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
              y s₁ s₂ μ))
          + (∫ ω, |(G p ω).1| ^ 3 ∂Q) + ∫ ω, |(G p ω).2| ^ 3 ∂Q)
      ≤ blockT₂ θ m := by
  have hs₁ : 0 < s₁.re := re_pos_of_block hmθ hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hmθ hre₂ hσ
  have hκ := blockWeightSize_le hmθ
  -- on the block the two weights have equal modulus, at most `κ ≤ 1/1000`
  have hsmall : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖
        ∧ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 1000 := by
    intro p hp
    have h₁ := norm_sq_prime_cpow_neg p hre₁
    have h₂ := norm_sq_prime_cpow_neg p hre₂
    have heq : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := by
      have h : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2 = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2 := by rw [h₁, h₂]
      calc ‖((p : ℕ) : ℂ) ^ (-s₁)‖
          = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (‖((p : ℕ) : ℂ) ^ (-s₂)‖ ^ 2) := by rw [h]
        _ = ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := Real.sqrt_sq (norm_nonneg _)
    have hb : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub hσ hp h₁
    exact ⟨heq, by linarith⟩
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    rw [← heq]; linarith
  -- per prime, the four moments come to `blockThirdConst₂·‖v_p‖³`
  have hper : ∀ p ∈ primeBlockSub θ m,
      ((∫ ω, |localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            y s₁ s₂ μ))
        + (∫ ω, |localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            y s₁ s₂ μ))
        + (∫ ω, |(G p ω).1| ^ 3 ∂Q) + ∫ ω, |(G p ω).2| ^ 3 ∂Q)
      ≤ blockThirdConst₂ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    have hv5 : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by linarith
    have hw5 : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by rw [← heq]; linarith
    have h₁ := third_moment_pair_add_matching_le hX y hs₁ hs₂ (hy hp)
      (hA p hp) hv5 ((hGm p).fst) (hlaw₁ p hp)
    have h₂ := third_moment_pair_add_matching_le hX y hs₁ hs₂ (hy hp)
      (hA p hp) hw5 ((hGm p).snd) (hlaw₂ p hp)
    rw [← heq] at h₂
    rw [blockThirdConst₂]
    linarith
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum, blockT₂]
  refine mul_le_mul_of_nonneg_left ?_ blockThirdConst₂_pos.le
  exact sum_norm_cube_primeBlockSub_le hmθ hσ fun p _ => norm_sq_prime_cpow_neg p hre₁

/-- **The two-point envelope noise is absolute**:
`(2 + 800κ)·e²(1 + 60/\log x_{m+1}) ≤ 15` once `θ ≥ 125`.  The `2` is the doubled drift (see
`RMF.abs_blockMean₂_le`). -/
lemma blockEnvelopeNoise₂_le {θ : ℝ} (hθ : (125 : ℝ) ≤ θ) (m : ℕ) :
    (2 + 800 * blockWeightSize θ m)
        * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1)))) ≤ 15 := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm4 : (4 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hκ : blockWeightSize θ m ≤ 1 / 1000000 := blockWeightSize_le_millionth hm4
  have hκ0 : (0 : ℝ) < blockWeightSize θ m := blockWeightSize_pos θ m
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [log_blockScale]
    calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
      _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hL0 : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
  have hdiv : (60 : ℝ) / Real.log (blockScale θ (m + 1)) ≤ 0.0086 := by
    rw [div_le_iff₀ hL0]; linarith
  have hdiv0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by positivity
  have he2 : Real.exp 2 ≤ 7.39 := by
    have hrw : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hrw]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have he20 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have h1 : 2 + 800 * blockWeightSize θ m ≤ 2.001 := by linarith
  have h2 : Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1))) ≤ 7.39 * 1.0086 :=
    mul_le_mul he2 (by linarith) (by linarith) (by norm_num)
  have h20 : (0 : ℝ) ≤ Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1))) := by
    positivity
  nlinarith [h1, h2, h20, hκ0]

/-! ### The per-block step, with the family supplied

Everything above, fed to `RMF.le_measure_box_of_gaussian_pair_of_third_moment`; this is the layer
at which the Steinhaus tilt stops being visible.  The multi-block layer needs one `Q` to serve
every block, so the per-block work is stated here against a *supplied* family.

Keeping it a separate declaration is not only tidiness.  Inlined, the multi-block theorem exceeds
four million heartbeats at `whnf`; split, each half is ordinary.

`hcov` stays a hypothesis at every layer of this file; `RMF.exists_proposition7_upper_steinhaus`
discharges it for `RMF.exists_isBoxComparison_steinhaus_of_range`. -/

/-- **The per-block step of the box comparison**, with the Gaussian family supplied. -/
theorem box_comparison_block_of_family {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {G : Nat.Primes → Ω' → ℝ × ℝ}
    (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ} {M : ℝ}
    {S : Finset Nat.Primes} (hθ : (125 : ℝ) ≤ θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hcovm : |blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| ≤ 1 / 100)
    (henvm : M + blockWindow m + 13
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))))
    (hBS : primeBlockSub θ m ⊆ S) (hSsub : S ⊆ primesBelowSub (blockCutoff θ n))
    (hAS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    (hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5)
    (hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    (hGm : ∀ p, Measurable (G p)) (hGi : iIndepFun G Q)
    (hmom : ∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)) = ∫ ω, quadMonomial j (G p ω) ∂Q)
    (hpair : ∀ p ∈ S, Q.map (G p) = gaussianPairLaw
      (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      ((∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        - (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)) ^ 2)
      ((∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        - (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)) ^ 2)
      ((∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        - (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
          * ∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)))
    (hmarg₁ : ∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      (matchingVar (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))))
    (hmarg₂ : ∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      (matchingVar (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        (∫ ω, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))))
    (hlawsum : Q.map (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
        ∑ p ∈ primeBlockSub θ m, (G p ω).2))
      = gaussianPairLaw
          (blockMean₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
          (blockMean₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
          ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m))) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      (1 - blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
          ≤ ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
        ∧ ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
          ≤ (1 + blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal := by
  have hmθ : (14 : ℝ) ≤ (m : ℝ) + θ := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block hm3 hre₁ hσ
  have hs₂ : 0 < s₂.re := re_pos_of_block hm3 hre₂ hσ
  have hB : primeBlockSub θ m ⊆ primesBelowSub (blockCutoff θ n) := hBS.trans hSsub
  have hpsd := fun (p : Nat.Primes) (hp : p ∈ primeBlockSub θ m) =>
    psd_of_tiltedMeasure₂_moments hX (blockCutoff θ n) hs₁ hs₂ (hB hp) (hAS p (hBS hp))
      (hvS p (hBS hp)) (hwS p (hBS hp)) rfl rfl rfl rfl rfl
  have hδ : (0 : ℝ) < blockT₂ θ m ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (blockT₂_pos θ m) _
  have hmG : ∀ p ∈ primeBlockSub θ m, ∀ j : Fin 5,
      Integrable (fun ω => quadMonomial j (G p ω)) Q := by
    intro p hp j
    have hint : Integrable (fun z : ℝ × ℝ => quadMonomial j z) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_quadMonomial_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2 j
    exact (integrable_map_measure
      ((measurable_quadMonomial j).aestronglyMeasurable) (hGm p).aemeasurable).1 hint
  have hLG : ∀ p ∈ primeBlockSub θ m,
      Integrable (fun ω => windowLindebergBound (blockT₂ θ m ^ (1 / 4 : ℝ)) (G p ω)) Q := by
    intro p hp
    have hint : Integrable
        (fun z : ℝ × ℝ => windowLindebergBound (blockT₂ θ m ^ (1 / 4 : ℝ)) z)
        (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_windowLindebergBound_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2 hδ
    exact (integrable_map_measure
      ((measurable_windowLindebergBound _).aestronglyMeasurable)
      (hGm p).aemeasurable).1 hint
  have hG₁ : ∀ p ∈ primeBlockSub θ m, Integrable (fun ω => |(G p ω).1| ^ 3) Q := by
    intro p hp
    have hint : Integrable (fun z : ℝ × ℝ => |z.1| ^ 3) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_abs_cube_fst_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2
    exact (integrable_map_measure (by fun_prop) (hGm p).aemeasurable).1 hint
  have hG₂ : ∀ p ∈ primeBlockSub θ m, Integrable (fun ω => |(G p ω).2| ^ 3) Q := by
    intro p hp
    have hint : Integrable (fun z : ℝ × ℝ => |z.2| ^ 3) (Q.map (G p)) := by
      rw [hpair p (hBS hp)]
      exact integrable_abs_cube_snd_gaussianPairLaw (hpsd p hp).1 (hpsd p hp).2.1
        (hpsd p hp).2.2
    exact (integrable_map_measure (by fun_prop) (hGm p).aemeasurable).1 hint
  -- the variance bracket, moved to the global cutoff
  obtain ⟨-, hv₁, -⟩ := blockStats₂_blockCutoff_eq hX hs₁ hs₂ hmn
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₁))
  obtain ⟨-, hv₂, -⟩ := blockStats₂_blockCutoff_eq hX hs₁ hs₂ hmn
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
  obtain ⟨hV₁l, hV₁u⟩ := blockMatchedVar₂_concrete hX θ σ m s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (by linarith) hre₁ hre₂ hσ
    (fun p _ => norm_sq_prime_cpow_neg p hre₁)
  obtain ⟨hV₂l, hV₂u⟩ := blockMatchedVar₂_concrete hX θ σ m s₁ s₂
    (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (by linarith) hre₁ hre₂ hσ
    (fun p _ => norm_sq_prime_cpow_neg p hre₂)
  have hV₁16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
    rw [hv₁, blockCutoff]; linarith
  have hV₂16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
    rw [hv₂, blockCutoff]; linarith
  obtain ⟨-, hcs⟩ := abs_pairSlope_le_and_cs_of_abs_le hV₁16 hV₂16 hcovm
  have hNm : Measurable (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
      ∑ p ∈ primeBlockSub θ m, (G p ω).2)) :=
    (Finset.measurable_sum _ fun p _ => (hGm p).fst).prodMk
      (Finset.measurable_sum _ fun p _ => (hGm p).snd)
  have hqlow : ∀ c' d' : ℝ, |c'| ≤ M → |d'| ≤ M →
      blockQ₂ θ m ≤ (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
        ∑ p ∈ primeBlockSub θ m, (G p ω).2))
          ⁻¹' (Set.Ioc c' (c' + blockWindow m)
            ×ˢ Set.Ioc d' (d' + blockWindow m)))).toReal := by
    intro c' d' hc' hd'
    rw [← Measure.map_apply hNm (measurableSet_Ioc.prod measurableSet_Ioc), hlawsum]
    refine blockQ₂_le_measure_of_le hX hmθ hmn hre₁ hre₂ hσ hcovm ?_ c' d' hc' hd'
    have hnoise := blockEnvelopeNoise₂_le hθ m
    linarith
  have hPprob := hX.isProbabilityMeasure_tiltedMeasure₂ (blockCutoff θ n) hs₁ hs₂
  intro c d hc hd
  exact le_measure_box_of_gaussian_pair_of_third_moment
    (ξ := fun p ω => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
      localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (t := primeBlockSub θ m) (T := blockT₂ θ m) (w := blockWindow m) (M := M)
    (ε := blockEps θ m) (q := blockQ₂ θ m)
    (fun p => ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)))
    hGm
    ((hX.iIndepFun_tiltedMeasure₂ (blockCutoff θ n) hs₁ hs₂).comp
      (fun p z => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun p => (measurable_localLog _).prodMk (measurable_localLog _))
    hGi (blockT₂_pos θ m)
    (fun p hp => integrable_quadMonomial_localLog_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hAS p (hBS hp)) (hvS p (hBS hp)) (hwS p (hBS hp)))
    hmG (fun p hp => hmom p (hBS hp))
    (fun p hp => integrable_windowLindebergBound_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hAS p (hBS hp)) (hvS p (hBS hp)) (hwS p (hBS hp)) hδ)
    hLG
    (fun p hp => integrable_abs_cube_localLog_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hAS p (hBS hp)) (hvS p (hBS hp)))
    (fun p hp => integrable_abs_cube_localLog_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hAS p (hBS hp)) (hwS p (hBS hp)))
    hG₁ hG₂
    (sum_third_moment_pair_block_le hX hB hm3 hre₁ hre₂ hσ hGm
      (fun p hp => hmarg₁ p (hBS hp)) (fun p hp => hmarg₂ p (hBS hp)))
    -- `positivity` would unfold `blockMatchedVar₂` to prove `0 ≤ ↑x`; the coercion settles it
    hlawsum (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by nlinarith [hcs, hV₁16, hV₂16])
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (blockQ₂_pos θ m) hqlow
    (blockNum₂_le' (θ := θ) (m := m) hmθ (by linarith) hV₁16 hV₂16)
    c d hc hd

/-- **The two-point block sums are independent under the two-fold tilt**, the analogue of
`RMF.iIndepFun_blockSum_tiltedMeasure`.

Stated as a lemma rather than derived inline, and that matters: derived inline, its inferred type
carries `iIndepFun.comp`'s un-beta-reduced `g i ∘ f i`, and unifying *that* against the shift
lemma's `fun m => Z (m + k)` does not terminate in any heartbeat budget. -/
theorem iIndepFun_blockSumPair_tiltedMeasure₂ (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (θ : ℝ) :
    iIndepFun (fun m ω => ∑ p ∈ primeBlockSub θ m,
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω) y s₁ s₂ μ) :=
  iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun (p : Nat.Primes) =>
      ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)).prodMk
        ((measurable_localLog _).comp (hX.measurable (p : ℕ) p.2)))
    ((hX.iIndepFun_tiltedMeasure₂ y hs₁ hs₂).comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun (_ : Nat.Primes) => (measurable_localLog _).prodMk (measurable_localLog _))
    (pairwise_disjoint_primeBlockSub θ)

/-! ### The multi-block layer

One `Q` carrying every block, and `RMF.IsBoxComparison`.  The two-point analogue of
`RMF.exists_isWindowComparison_primeBlockSub`; above it nothing knows about primes.

**No reservoir is needed.**  The one-point construction indexes its Gaussian family by
`Nat.Primes ⊕ ℕ`, the `ℕ` side carrying standard normals used only above the horizon, because
`IsGaussianWalk` demands a variance bounded below at *every* index and the block sums run to `0`
past the top block.  `RMF.IsBoxComparison` quantifies only over `m < n`, so the primes alone
suffice here and the empty blocks contribute the constant `0`, which is independent of everything.
The reservoir returns when this feeds a walk. -/

/-- **The multi-block box comparison, with the block range free of the tilt cutoff.**

The tilt sits at `blockCutoff θ n` while the comparison runs only over blocks `m < r`.  Keeping
the two apart is what a tilt scale `η > 1` needs: the per-block scale then exceeds `1` near the
top, and the fix is to stop the barrier short of the tilt rather than to weaken the blocks. -/
theorem exists_isBoxComparison_steinhaus_of_range (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ}
    {r n : ℕ} {s₁ s₂ : ℂ} {M : ℕ → ℝ} (hθ : (125 : ℝ) ≤ θ) (hrn : r ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ (r + 1)) ≤ 1)
    (hcov : ∀ m, m < r → |blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| ≤ 1 / 100)
    (henvc : ∀ m, m < r →
      M m + blockWindow m + 13 ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, m ≤ r → Q.map (N m) = gaussianPairLaw
        (blockMean₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
        (blockMean₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
        ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ((blockMatchedVar₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        (blockMatchedCov X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m))) ∧
      ∀ k, k ≤ r → IsBoxComparison
        (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
          (blockCutoff θ n) s₁ s₂ μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
            localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
        (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (r - k)
        (2 * (1 / 4)) := by
  classical
  have hσ : ∀ m, m ≤ r → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσtop
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hs₁ : 0 < s₁.re := re_pos_of_block (hm3 0) hre₁ (hσ 0 (Nat.zero_le r))
  have hs₂ : 0 < s₂.re := re_pos_of_block (hm3 0) hre₂ (hσ 0 (Nat.zero_le r))
  -- the primes of every block below the horizon, in one set
  -- `S` is named opaquely: as a `set` it stays reducible and `whnf` unfolds the `biUnion`
  -- everywhere it appears, which alone exhausts the heartbeat budget.
  obtain ⟨S, hSdef⟩ : ∃ S : Finset Nat.Primes,
      S = (Finset.range (r + 1)).biUnion (primeBlockSub θ) := ⟨_, rfl⟩
  have hmemS : ∀ p ∈ S, ∃ m, m ≤ r ∧ p ∈ primeBlockSub θ m := by
    intro p hp
    rw [hSdef, Finset.mem_biUnion] at hp
    obtain ⟨m, hm, hpm⟩ := hp
    exact ⟨m, Nat.lt_succ_iff.1 (Finset.mem_range.1 hm), hpm⟩
  have hblockS : ∀ m, m ≤ r → primeBlockSub θ m ⊆ S := by
    intro m hm p hp
    rw [hSdef, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), hp⟩
  have hSsub : S ⊆ primesBelowSub (blockCutoff θ n) := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    exact primeBlockSub_subset_primesBelowSub θ (hm.trans hrn) hpm
  have hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    have hb : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub (hσ m hm) hpm (norm_sq_prime_cpow_neg p hre₁)
    linarith [blockWeightSize_le (hm3 m)]
  have hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    have hb : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub (hσ m hm) hpm (norm_sq_prime_cpow_neg p hre₂)
    linarith [blockWeightSize_le (hm3 m)]
  have hAS : ∀ p ∈ S,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := hmemS p hp
    have hb₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub (hσ m hm) hpm (norm_sq_prime_cpow_neg p hre₁)
    have hb₂ : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ blockWeightSize θ m :=
      norm_le_of_mem_primeBlockSub (hσ m hm) hpm (norm_sq_prime_cpow_neg p hre₂)
    linarith [blockWeightSize_le (hm3 m)]
  -- one Gaussian family for the whole run
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hmom, hpair, hmarg₁, hmarg₂, hlawS⟩ :=
    exists_gaussian_pair_block hX (blockCutoff θ n) hs₁ hs₂ hSsub hAS hvS hwS
  have hPprob := hX.isProbabilityMeasure_tiltedMeasure₂ (blockCutoff θ n) hs₁ hs₂
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω, hQ,
    fun m => Finset.measurable_sum _ fun p _ => hGm p,
    iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ),
    fun m hm => hlawS _ (hblockS m hm), ?_⟩
  have hZi := iIndepFun_blockSumPair_tiltedMeasure₂ hX (blockCutoff θ n) hs₁ hs₂ θ
  -- **`hcmp` is stated and proved before the shift lemma sees it.**  Passed as a lambda with a
  -- hole, its expected type is read off `IsBoxComparison`'s unfolding, and elaborating it there
  -- costs forty seconds; stated up front it is immediate.
  have hcmp : ∀ m, m < r → ∀ c d : ℝ, |c| ≤ M m → |d| ≤ M m →
      (1 - blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
          ≤ ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
        ∧ ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
          ≤ (1 + blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal := by
    intro m hm c d hc hd
    have hmr : m ≤ r := le_of_lt hm
    have hmn : m ≤ n := hmr.trans hrn
    have hBS := hblockS m hmr
    have hlawsum := hlawS (primeBlockSub θ m) hBS
    rw [sum_pair_eq G (primeBlockSub θ m)] at hlawsum
    rw [sum_pair_eq G (primeBlockSub θ m),
      sum_pair_eq (fun p ω => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (primeBlockSub θ m)]
    exact box_comparison_block_of_family hX hθ hmn hre₁ hre₂ (hσ m hmr) (hcov m hm)
      (henvc m hm) hBS hSsub hAS hvS hwS hGm hGi hmom hpair hmarg₁ hmarg₂ hlawsum c d hc hd
  intro k hkn
  -- `Z` and `N` are given, not inferred: left to unification the shift lemma unfolds
  -- `IsBoxComparison` and does not terminate in any heartbeat budget.
  exact isBoxComparison_shift_of_indep
    (Z := fun m ω => ∑ p ∈ primeBlockSub θ m,
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (N := fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω)
    (w := blockWindow) (M := M) (ε := blockEps θ) (E := 1 / 4) hZi
    (iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ))
    hkn (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le (by linarith) r) (by norm_num) hcmp

end RMF
