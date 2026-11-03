/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.RademacherTwoPointTiltMoments
import RMF.Probability.BlockComparisonPair
import RMF.Probability.RademacherWindowComparison

/-!
# The block data at two points, for the Rademacher function

`RMF.blockMeanAdd`, `RMF.blockMatchedVarAdd` name the Gaussian matched to a block of tilted
increments at *one* point.  The two-point argument (Harper's Proposition 7, in the Rademacher case)
needs the same at two, and the two-point objects are **not** the one-point ones applied twice: they
live under the two-fold tilt `RMF.tiltedMeasure₂`, and the one-point definitions are stated against
the one-fold `RMF.tiltedMeasure`.  So they are redefined here, and a third object appears that has
no one-point analogue at all — the covariance.

* `RMF.blockMeanAdd₂`, `RMF.blockMatchedVarAdd₂` — the marginals, one per coordinate;
* `RMF.blockMatchedCovAdd` — the off-diagonal, `∑_p (E~ξ¹_pξ²_p - E~ξ¹_p·E~ξ²_p)`.

This is `RMF/Probability/BlockComparisonPair.lean`'s opening, with `RMF.localLogAdd` for
`RMF.localLog` and `RMF.squarefreeExtension` for `RMF.compMultExtension`.

## The covariance is the whole difficulty of the two-point argument

At `w^i_p = p^{-1/2-σ-it_i}` its main term is the logarithmic correlation
`∑_{p∈B} cos((t₁-t₂)\log p)/2p^{1+2σ}`.  Near `t₁ = t₂` that is the full variance and the two
walks coincide; the block decorrelation estimate `RMF.abs_cos_prime_sum_block_weight_le`, which is
law-free, makes it small once the heights separate.

## Weaker tilt-radius hypotheses than the Steinhaus twin

`RMF.sq_integral_localLog_le_integral_mul_self₂` asks for `‖a₁‖ + ‖a₂‖ ≤ 1/5`, because the
Steinhaus local factor `(1 - z a)⁻¹` is only bounded there.  The Rademacher factor is the
polynomial `1 + z a`, so `‖a‖ < 1` suffices — and that is `RMF.norm_prime_cpow_neg_lt_one`, free at
every prime.  So the integrability and Cauchy–Schwarz statements below carry no hypothesis on the
tilt radii, like the one-point `RMF.sq_integral_localLogAdd_le_integral_mul_self`; the mean and
covariance estimates carry `‖p^{-s₁}‖ + ‖p^{-s₂}‖ ≤ 1/2`, on the tilt radii only.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The three block statistics -/

/-- The mean of one coordinate of the block Gaussian, under the **two-fold** tilt.  Same shape as
`RMF.blockMeanAdd`, and not equal to it: the tilt is by both `F_y(s₁)` and `F_y(s₂)`, so both
drifts are present in each coordinate. -/
noncomputable def blockMeanAdd₂ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
    ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)

/-- The variance of one coordinate of the block Gaussian, under the two-fold tilt. -/
noncomputable def blockMatchedVarAdd₂ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ≥0 :=
  ∑ p ∈ B, matchingVar
    (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
    (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))

/-- **The off-diagonal**, `∑_p (E~ξ¹_pξ²_p - E~ξ¹_p·E~ξ²_p)`.

Summed per prime rather than taken of the block sums, which is the same thing because the
increments are independent under the tilt
(`RMF.iIndepFun_localLogAdd_tiltedMeasure₂_rademacher`), and is the form the per-prime estimates
deliver. -/
noncomputable def blockMatchedCovAdd (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s₁ s₂ : ℂ)
    (v w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ((∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      - (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        * ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))

/-! ### Cauchy–Schwarz under the two-fold tilt

`RMF.blockMatchedVarAdd₂` is a sum of `RMF.matchingVar`s, and `matchingVar m₁ m₂ = (m₂ - m₁²)⁺`.
To read it as a real number one needs `m₁² ≤ m₂`, which is Cauchy–Schwarz for the two-fold tilted
measure.  The one-fold chain does not apply, so it is redone here — and, unlike the Steinhaus
twin, with no hypothesis on the tilt radii. -/

/-- A local term is square-integrable under the two-fold tilt. -/
lemma memLp_two_localLogAdd_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    MemLp (fun ω => localLogAdd w (X (p : ℕ) ω)) 2
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  have hmeas : Measurable (fun ω => localLogAdd w (X (p : ℕ) ω)) :=
    (measurable_localLogAdd w).comp (hX.measurable (p : ℕ) p.2)
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    (integrable_localLogAdd_sq_tiltedMeasure₂ hX y hs₁ hs₂ hp hw)

/-- **Cauchy–Schwarz for the local terms**, under the two-fold tilt. -/
lemma sq_integral_localLogAdd_le_integral_mul_self₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2
      ≤ ∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  have := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  exact sq_integral_le_integral_mul_self
    (memLp_two_localLogAdd_tiltedMeasure₂ hX y hs₁ hs₂ hp hw)

/-- **`blockMatchedVarAdd₂` as a real number** — the positive part is not doing any work, because
Cauchy–Schwarz makes each summand non-negative already. -/
lemma coe_blockMatchedVarAdd₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes}
    (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    (blockMatchedVarAdd₂ X μ y s₁ s₂ w B : ℝ)
      = ∑ p ∈ B, ((∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          - (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                y s₁ s₂ μ)) ^ 2) := by
  rw [blockMatchedVarAdd₂, NNReal.coe_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [coe_matchingVar
    (sq_integral_localLogAdd_le_integral_mul_self₂ hX y hs₁ hs₂ (hB hq) (hw q hq))]

/-! ### The per-prime mean, transported

`RMF.integral_comp_tiltedMeasure₂_rademacher` moves each estimate from the circle to `Ω`, and
the tilt radii are `‖p^{-s₁}‖`, `‖p^{-s₂}‖`.  The hypothesis `hA` appears here for the first time
in this file, and it is not the Steinhaus twin's: `1/2` rather than `1/5`, and it constrains the
**tilt** radii only, never `w`.  It is where `RMF.abs_pairTiltMultiplier_le` is discharged, and
it is genuinely needed — see that lemma's counterexample. -/

/-- **The two-fold tilted mean at one prime.**  Main term
`2 (Re p^{-s₁} + Re p^{-s₂})(Re w) - Re(w ^ 2)/2` — the one-point
`RMF.abs_integral_localLogAdd_tiltedMeasure_sub_le` with the two drifts added, which is what
`RMF.integral_tilted_pair_eq_add_rademacherLaw` says they do. -/
theorem abs_integral_localLogAdd_tiltedMeasure₂_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |(∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        - (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re) * w.re
            - (w ^ 2).re / 2)|
      ≤ 36 * ‖w‖ ^ 3
        + 6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w‖ := by
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (integrable_localLogAdd_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw)]
  exact abs_integral_localLogAdd_tilted_pair_sub_le (norm_prime_cpow_neg_lt_one p.2 hs₁)
    (norm_prime_cpow_neg_lt_one p.2 hs₂) hA hw

/-- **The two-fold tilted mean at one prime is `O(‖w‖ A + ‖w‖ ^ 2)`** with
`A = ‖p^{-s₁}‖ + ‖p^{-s₂}‖` — the form the block variance needs, since it is what makes the
mean's *square* an error.
Same constants as the one-point `RMF.abs_integral_localLogAdd_tiltedMeasure_le`. -/
theorem abs_integral_localLogAdd_tiltedMeasure₂_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)|
      ≤ 4 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) * ‖w‖ + 8 * ‖w‖ ^ 2 := by
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (integrable_localLogAdd_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw)]
  exact abs_integral_localLogAdd_tilted_pair_le (norm_prime_cpow_neg_lt_one p.2 hs₁)
    (norm_prime_cpow_neg_lt_one p.2 hs₂) hA hw

/-! ### The covariance, against the cosine sum

The estimate that names `RMF.blockMatchedCovAdd`.  Its main term is `∑_p (Re v_p)(Re w_p)`, which
at `v_p = p^{-(1/2+σ+it₁)}`, `w_p = p^{-(1/2+σ+it₂)}` is

`∑_{p ∈ B} [\cos((t₁-t₂)\log p) + \cos((t₁+t₂)\log p)] / (2 p^{1+2σ})`,

the logarithmic correlation plus one oscillatory sum.  Near `t₁ = t₂` the first piece is the full
variance and the two walks coincide; the block decorrelation estimate
`RMF.abs_cos_prime_sum_block_weight_le` makes it small once the heights separate, and
`RMF.exists_abs_sum_cos_primeBlockSub_le'` disposes of the second, exactly as it does for the
drift. -/

/-- **The block covariance is the cosine sum, up to third-order errors.**

One term shorter than the Steinhaus twin `RMF.abs_blockMatchedCov_sub_le`, which carries
`240‖v‖‖w‖A` between its cubic and its `A ^ 2` term.  The reason is
`RMF.cov_localLogAdd_tilted_pair_eq`: for two atoms the tilted covariance is an exact multiple
`1 - 4m ^ 2` of the untilted one, so the tilt radii cannot enter to first order. -/
theorem abs_blockMatchedCovAdd_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2)
    {v w : Nat.Primes → ℂ} (hv : ∀ p ∈ B, ‖v p‖ ≤ 1 / 5) (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMatchedCovAdd X μ y s₁ s₂ v w B - ∑ p ∈ B, (v p).re * (w p).re|
      ≤ ∑ p ∈ B, (4 * (‖v p‖ ^ 3 + ‖w p‖ ^ 3)
          + 36 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2
              * (‖v p‖ * ‖w p‖)) := by
  rw [blockMatchedCovAdd, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have ha₁ := norm_prime_cpow_neg_lt_one p.2 hs₁
  have ha₂ := norm_prime_cpow_neg_lt_one p.2 hs₂
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ (hB hp)
      (integrable_localLogAdd_mul_tilted_pair ha₁ ha₂ (hv p hp) (hw p hp)),
    integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ (hB hp)
      (integrable_localLogAdd_tilted_pair ha₁ ha₂ (hv p hp)),
    integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ (hB hp)
      (integrable_localLogAdd_tilted_pair ha₁ ha₂ (hw p hp))]
  exact abs_cov_localLogAdd_tilted_pair_sub_le ha₁ ha₂ (hA p hp) (hv p hp) (hw p hp)

/-! ### The block statistics, from the per-prime estimates

`RMF.blockMeanAdd₂` and `RMF.blockMatchedVarAdd₂` are sums over the block, so each estimate below
is the per-prime one summed — there is nothing to bridge, unlike the one-point `RMF.blockMeanAdd`,
which is the mean of the block increment.

**The variance needs no second-moment input.**  `RMF.matchingVar` is `E~ξ² - (E~ξ) ² `, which is
`RMF.cov_localLogAdd_tilted_pair_eq` at `v = w`; so the covariance estimate delivers it whole.
The Steinhaus `RMF.abs_blockMatchedVar₂_sub_le` has to combine two: the two-fold second moment over
the block, and the mean squared. -/

/-- **The block drift**, `∑_p (2 (Re p^{-s₁} + Re p^{-s₂})(Re w_p) - Re(w_p ^ 2)/2)` up to third
order.  The two-point form of `RMF.abs_blockMeanAdd_sub_sum_le`; the main term is Harper's
`∑_{p ∈ B_j} c(t, t_j - t, p)/p^{1+2σ}` with the two drifts added. -/
theorem abs_blockMeanAdd₂_sub_sum_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMeanAdd₂ X μ y s₁ s₂ w B
        - ∑ p ∈ B, (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re) * (w p).re
            - ((w p) ^ 2).re / 2)|
      ≤ ∑ p ∈ B, (36 * ‖w p‖ ^ 3
          + 6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w p‖) := by
  rw [blockMeanAdd₂, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLogAdd_tiltedMeasure₂_sub_le hX y hs₁ hs₂ (hB hp) (hA p hp) (hw p hp)

/-- The variance's summand, read off the covariance's.  Only the squares are rewritten; extracted
so that the rewrite happens away from the two integrals. -/
private lemma var_from_cov {I₂ I₁ r c e : ℝ}
    (h : |I₂ - I₁ * I₁ - r * r| ≤ 4 * (c ^ 3 + c ^ 3) + 36 * e ^ 2 * (c * c)) :
    |I₂ - I₁ ^ 2 - r ^ 2| ≤ 8 * c ^ 3 + 36 * e ^ 2 * c ^ 2 := by
  rw [show I₂ - I₁ ^ 2 - r ^ 2 = I₂ - I₁ * I₁ - r * r from by ring]
  linarith

/-- **The block variance is `∑_p (Re w_p)²` up to third-order errors.**  At
`w_p = p^{-(1/2+σ+it_j)}` the main term is `∑_{p∈B}(1 + cos(2t_j log p))/(2p^{1+2σ})`, half block
Mertens and half an oscillatory prime sum, pinned in `RMF/Probability/RademacherBlockVariance.lean`;
the Steinhaus `∑_p ‖w_p‖²/2` does not see the height.  One error term shorter than
`RMF.abs_blockMatchedVar₂_sub_le`, because `RMF.cov_localLogAdd_tilted_pair_eq` makes the tilted
covariance an exact multiple of the untilted one. -/
theorem abs_blockMatchedVarAdd₂_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hA : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2)
    {w : Nat.Primes → ℂ} (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |(blockMatchedVarAdd₂ X μ y s₁ s₂ w B : ℝ) - ∑ p ∈ B, (w p).re ^ 2|
      ≤ ∑ p ∈ B, (8 * ‖w p‖ ^ 3
          + 36 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 * ‖w p‖ ^ 2) := by
  rw [coe_blockMatchedVarAdd₂ hX y hs₁ hs₂ hB hw, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have ha₁ := norm_prime_cpow_neg_lt_one p.2 hs₁
  have ha₂ := norm_prime_cpow_neg_lt_one p.2 hs₂
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ (hB hp)
      (integrable_localLogAdd_mul_tilted_pair ha₁ ha₂ (hw p hp) (hw p hp)),
    integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ (hB hp)
      (integrable_localLogAdd_tilted_pair ha₁ ha₂ (hw p hp))]
  exact var_from_cov
    (abs_cov_localLogAdd_tilted_pair_sub_le ha₁ ha₂ (hA p hp) (hw p hp) (hw p hp))

/-! ### The moment matrix is positive semidefinite

`RMF.exists_gaussian_pair_matching_quadMonomial` matches an independent family of bivariate
Gaussians to any positive-semidefinite target, so this is what licenses the matched Gaussian
pair. -/

/-- **The per-prime moment matrix is positive semidefinite** under the two-fold tilt, with the five
moments as parameters pinned by hypotheses, as in `RMF.psd_of_tiltedMeasure₂_moments` (written
out, the conclusion names the tilted measure ten times and elaboration times out).  Unlike the
Steinhaus twin there is no hypothesis on the tilt radii: `RMF.localLogAdd` is bounded on the
circle, so integrability is free. -/
theorem psd_of_tiltedMeasure₂_moments_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5)
    {m₁ m₂ q₁ q₁₂ q₂ : ℝ}
    (hm₁ : m₁ = ∫ ω, localLogAdd v (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
    (hm₂ : m₂ = ∫ ω, localLogAdd w (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
    (hq₁ : q₁ = ∫ ω, localLogAdd v (X (p : ℕ) ω) * localLogAdd v (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
    (hq₁₂ : q₁₂ = ∫ ω, localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
    (hq₂ : q₂ = ∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
      ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)) :
    0 ≤ q₁ - m₁ ^ 2 ∧ 0 ≤ q₂ - m₂ ^ 2
      ∧ (q₁₂ - m₁ * m₂) ^ 2 ≤ (q₁ - m₁ ^ 2) * (q₂ - m₂ ^ 2) := by
  obtain ⟨T, hT⟩ : ∃ T : Measure Ω,
      T = tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ := ⟨_, rfl⟩
  have hprob : IsProbabilityMeasure T := by
    rw [hT]; exact isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  have h₁ : Integrable (fun ω => localLogAdd v (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_tiltedMeasure₂ hX y hs₁ hs₂ hp hv
  have h₂ : Integrable (fun ω => localLogAdd w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_tiltedMeasure₂ hX y hs₁ hs₂ hp hw
  have h₁₁ : Integrable
      (fun ω => localLogAdd v (X (p : ℕ) ω) * localLogAdd v (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hv hv
  have h₁₂ : Integrable
      (fun ω => localLogAdd v (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hv hw
  have h₂₂ : Integrable
      (fun ω => localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)) T := by
    rw [hT]; exact integrable_localLogAdd_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hw hw
  have h := psd_of_integrable_pair (P := T)
    (ξ := fun ω => (localLogAdd v (X (p : ℕ) ω), localLogAdd w (X (p : ℕ) ω)))
    h₁ h₂ h₁₁ h₁₂ h₂₂
  rw [hm₁, hm₂, hq₁, hq₁₂, hq₂, ← hT]
  exact h

/-! ### The matched Gaussian family for a block

`RMF.exists_gaussian_pair_matching_quadMonomial` supplies an independent family of bivariate
Gaussians matching any positive-semidefinite target, and the lemma above says the tilted block
moments are such a target.  Reading off the block law then costs nothing: the parameters
`RMF.map_sum_eq_gaussianPairLaw` produces are `∑_p μ₁`, `∑_p (q₁ - μ₁ ² )` and
`∑_p (q₁₂ - μ₁μ₂)`, which are the three block statistics defined at the top of this file.

The targets are guarded by `if p ∈ S`: off the block the weights carry no bound, so neither the
moments nor their positive semidefiniteness is available, and there is nothing to match.  Zero is
a legitimate target there — it is the degenerate Gaussian — and the block sum never sees it. -/

/-- **The matched Gaussian family for a block, with its law**, the Rademacher form of
`RMF.exists_gaussian_pair_block`: the targets are zero off the block,
`RMF.psd_of_tiltedMeasure₂_moments_rademacher` makes them legitimate, and
`RMF.exists_gaussian_pair_matching_quadMonomial` supplies the family.  The block law comes out in
`RMF.blockMeanAdd₂`, `RMF.blockMatchedVarAdd₂` and `RMF.blockMatchedCovAdd` by definition.  There
is no tilt-radius hypothesis. -/
theorem exists_gaussian_pair_block_rademacher (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {S : Finset Nat.Primes} (hS : S ⊆ primesBelowSub y)
    {v w : Nat.Primes → ℂ} (hv : ∀ p ∈ S, ‖v p‖ ≤ 1 / 5) (hw : ∀ p ∈ S, ‖w p‖ ≤ 1 / 5) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G : Nat.Primes → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ p, Measurable (G p)) ∧ iIndepFun G Q ∧
        (∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
            (localLogAdd (v p) (X (p : ℕ) ω), localLogAdd (w p) (X (p : ℕ) ω))
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          = ∫ ω, quadMonomial j (G p ω) ∂Q) ∧
        (∀ p ∈ S, Q.map (G p) = gaussianPairLaw
          (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          ((∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
            - (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2)
          ((∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
            - (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)) ^ 2)
          ((∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
            - (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
                ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
              * ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
                ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))) ∧
        (∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
          (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          (matchingVar
            (∫ ω, localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
            (∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)))) ∧
        (∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
          (matchingVar
            (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
            (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
              ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)))) ∧
        ∀ B ⊆ S, Q.map (fun ω => ∑ p ∈ B, G p ω)
          = gaussianPairLaw (blockMeanAdd₂ X μ y s₁ s₂ v B) (blockMeanAdd₂ X μ y s₁ s₂ w B)
              ((blockMatchedVarAdd₂ X μ y s₁ s₂ v B : ℝ≥0) : ℝ)
              ((blockMatchedVarAdd₂ X μ y s₁ s₂ w B : ℝ≥0) : ℝ)
              (blockMatchedCovAdd X μ y s₁ s₂ v w B) := by
  classical
  set T := tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ with hTdef
  -- the target moments, zero off the block
  set μ₁ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) ∂T else 0 with hμ₁
  set μ₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ∂T else 0 with hμ₂
  set q₁ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (v p) (X (p : ℕ) ω) ∂T
    else 0 with hq₁
  set q₁₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (v p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω) ∂T
    else 0 with hq₁₂
  set q₂ : Nat.Primes → ℝ := fun p =>
    if p ∈ S then ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω) ∂T
    else 0 with hq₂
  -- positive semidefiniteness: `psd_of_tiltedMeasure₂_moments_rademacher` on the block
  have hpsd : ∀ p, 0 ≤ q₁ p - μ₁ p ^ 2 ∧ 0 ≤ q₂ p - μ₂ p ^ 2
      ∧ (q₁₂ p - μ₁ p * μ₂ p) ^ 2 ≤ (q₁ p - μ₁ p ^ 2) * (q₂ p - μ₂ p ^ 2) := by
    intro p
    by_cases hp : p ∈ S
    · simp only [hμ₁, hμ₂, hq₁, hq₁₂, hq₂, if_pos hp]
      exact psd_of_tiltedMeasure₂_moments_rademacher hX y hs₁ hs₂ (hS hp) (hv p hp)
        (hw p hp) rfl rfl rfl rfl rfl
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
    have hmean₁ : ∑ p ∈ B, μ₁ p = blockMeanAdd₂ X μ y s₁ s₂ v B := by
      rw [blockMeanAdd₂]
      exact Finset.sum_congr rfl fun p hp => by simp only [hμ₁, if_pos (hBS hp), hTdef]
    have hmean₂ : ∑ p ∈ B, μ₂ p = blockMeanAdd₂ X μ y s₁ s₂ w B := by
      rw [blockMeanAdd₂]
      exact Finset.sum_congr rfl fun p hp => by simp only [hμ₂, if_pos (hBS hp), hTdef]
    have hvar₁ : ∑ p ∈ B, (q₁ p - μ₁ p ^ 2)
        = ((blockMatchedVarAdd₂ X μ y s₁ s₂ v B : ℝ≥0) : ℝ) := by
      rw [coe_blockMatchedVarAdd₂ hX y hs₁ hs₂ (hBS.trans hS)
        (fun p hp => hv p (hBS hp))]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₁, hq₁, if_pos (hBS hp), hTdef]
    have hvar₂ : ∑ p ∈ B, (q₂ p - μ₂ p ^ 2)
        = ((blockMatchedVarAdd₂ X μ y s₁ s₂ w B : ℝ≥0) : ℝ) := by
      rw [coe_blockMatchedVarAdd₂ hX y hs₁ hs₂ (hBS.trans hS)
        (fun p hp => hw p (hBS hp))]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₂, hq₂, if_pos (hBS hp), hTdef]
    have hcov : ∑ p ∈ B, (q₁₂ p - μ₁ p * μ₂ p) = blockMatchedCovAdd X μ y s₁ s₂ v w B := by
      rw [blockMatchedCovAdd]
      exact Finset.sum_congr rfl fun p hp =>
        by simp only [hμ₁, hμ₂, hq₁₂, if_pos (hBS hp), hTdef]
    rw [hmean₁, hmean₂, hvar₁, hvar₂, hcov]

/-! ### The third-moment layer

`RMF.third_moment_add_matching_leAdd` at two points.  Of the three inputs, the summand's third
absolute moment `(11/5)³‖w‖³` and the matched variance `≤ (11/5)²‖w‖²` are pointwise bounds on the
circle and do not see the second tilt; the matched mean does.  One-fold it is `≤ (12/5)‖w‖`
(`RMF.abs_integral_localLogAdd_tiltedMeasure_le'`); two-fold the drifts add, and
`RMF.abs_integral_localLogAdd_tiltedMeasure₂_le` gives `4A‖w‖ + 8‖w‖²`, i.e. `(18/5)‖w‖` at
`A ≤ 1/2`, `‖w‖ ≤ 1/5`.

So the per-coordinate constant is `(11/5)³ + 4(c₃(11/5)³ + (18/5)³) ≈ 265`, against the one-point
`RMF.blockThirdConstAdd ≈ 154`.  The Steinhaus pair pays far more: its mean grows by a factor `56`
and enters cubed, so `RMF.blockThirdConst₂ ≈ 12010` against `2·RMF.blockThirdConst ≈ 157`.  The
block constant is `RMF.blockThirdConstAdd₂`, and the block sum is
`RMF.sum_third_moment_pair_blockAdd_le`. -/

/-- The two-fold tilted mean at one prime, in the `O(‖w‖)` form the Gaussian's third moment wants.
The one-fold `RMF.abs_integral_localLogAdd_tiltedMeasure_le'` gives `(12/5)‖w‖`. -/
lemma abs_integral_localLogAdd_tiltedMeasure₂_le' (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    |∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)|
      ≤ 18 / 5 * ‖w‖ := by
  have h := abs_integral_localLogAdd_tiltedMeasure₂_le hX y hs₁ hs₂ hp hA hw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hA0 : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ := by positivity
  nlinarith [h, mul_nonneg (by linarith :
      (0 : ℝ) ≤ 1 / 2 - (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)) hw0,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 5 - ‖w‖) hw0]

/-- **The second moment at one prime, crudely**, under the two-fold tilt. -/
theorem integral_localLogAdd_sq_tiltedMeasure₂_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      ≤ (11 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (integrable_localLogAdd_mul_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw hw)]
  exact integral_localLogAdd_mul_self_tilted_pair_le (norm_prime_cpow_neg_lt_one p.2 hs₁)
    (norm_prime_cpow_neg_lt_one p.2 hs₂) hw

/-- **The third absolute moment at one prime**, under the two-fold tilt. -/
theorem integral_abs_localLogAdd_cube_tiltedMeasure₂_le (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, |localLogAdd w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
  rw [integral_comp_tiltedMeasure₂_rademacher hX y hs₁ hs₂ hp
    (g := fun z => |localLogAdd w z| ^ 3)
    (integrable_abs_cube_localLogAdd_tilted_pair (norm_prime_cpow_neg_lt_one p.2 hs₁)
      (norm_prime_cpow_neg_lt_one p.2 hs₂) hw)]
  exact integral_abs_localLogAdd_cube_tilted_pair_le (norm_prime_cpow_neg_lt_one p.2 hs₁)
    (norm_prime_cpow_neg_lt_one p.2 hs₂) hw

/-- **The Gaussian half**, under the two-fold tilt.  `RMF.integral_abs_cube_matching_localLogAdd_le`
with `(18/5)` for the mean's `(12/5)`, and that single substitution is the whole difference. -/
theorem integral_abs_cube_matching_localLogAdd_tiltedMeasure₂_le {Ω' : Type*}
    [MeasurableSpace Ω'] {Q : Measure Ω'} {Y : Ω' → ℝ} (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        (∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)))) :
    ∫ ω, |Y ω| ^ 3 ∂Q
      ≤ 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (18 / 5 : ℝ) ^ 3) * ‖w‖ ^ 3 := by
  set T := tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ with hT
  set m₁ : ℝ := ∫ ω, localLogAdd w (X (p : ℕ) ω) ∂T with hm₁
  set m₂ : ℝ := ∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω) ∂T with hm₂
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hcs : m₁ ^ 2 ≤ m₂ :=
    sq_integral_localLogAdd_le_integral_mul_self₂ hX y hs₁ hs₂ hp hw
  have hmean : |m₁| ≤ 18 / 5 * ‖w‖ :=
    abs_integral_localLogAdd_tiltedMeasure₂_le' hX y hs₁ hs₂ hp hA hw
  have hmean₃ : |m₁| ^ 3 ≤ (18 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    calc |m₁| ^ 3 ≤ (18 / 5 * ‖w‖) ^ 3 := pow_le_pow_left₀ (abs_nonneg m₁) hmean 3
      _ = (18 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  have hsq : m₂ ≤ (11 / 5 * ‖w‖) ^ 2 := by
    calc m₂ ≤ (11 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 :=
          integral_localLogAdd_sq_tiltedMeasure₂_le hX y hs₁ hs₂ hp hw
      _ = (11 / 5 * ‖w‖) ^ 2 := by ring
  have hroot : √m₂ ≤ 11 / 5 * ‖w‖ := by
    refine le_trans (Real.sqrt_le_sqrt hsq) ?_
    rw [Real.sqrt_sq (by positivity)]
  have hroot₃ : √m₂ ^ 3 ≤ (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    calc √m₂ ^ 3 ≤ (11 / 5 * ‖w‖) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 3
      _ = (11 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  refine le_trans (integral_abs_cube_of_hasLaw_matching hYm hcs hlaw) ?_
  have hc := absMomentConst_nonneg 3
  nlinarith [hroot₃, hmean₃]

/-- **The two halves together, per prime and per coordinate**, under the two-fold tilt. -/
theorem third_moment_pair_add_matching_leAdd {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω' → ℝ} (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hA : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
        (∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ)))) :
    (∫ ω, |localLogAdd w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ))
      + ∫ ω, |Y ω| ^ 3 ∂Q
      ≤ ((11 / 5 : ℝ) ^ 3
          + 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (18 / 5 : ℝ) ^ 3)) * ‖w‖ ^ 3 := by
  have hξ := integral_abs_localLogAdd_cube_tiltedMeasure₂_le hX y hs₁ hs₂ hp hw
  have hG := integral_abs_cube_matching_localLogAdd_tiltedMeasure₂_le hX y hs₁ hs₂ hp hA hw hYm
    hlaw
  nlinarith [hξ, hG]

/-! ### The variance bracket at Harper's data

`RMF.exists_blockMatchedVarAdd_concrete_top` at two points, from the same two inputs:
`RMF.exists_sum_re_cpow_neg_sq_primeBlockSub_bounds` puts `∑ (Re w_p) ² ` in `[1/4, 3/4]` (where
Harper's `D(t)` is spent), and `RMF.abs_blockMatchedVarAdd₂_sub_le` bounds the gap to the matched
variance.  The gap is smaller than at one point, `∑ (8‖w‖ ³ + 36A ² ‖w‖ ² ) ≤ 37/1000` against
`52/1000`, because `RMF.cov_localLogAdd_tilted_pair_eq` removes the first-order term: the variance
sits in `[0.213, 0.787]`, and `2·var` in `[0.426, 1.574]`.

**`hA` is satisfiable on the whole block, and that is why it reads `1/2`.**  On the block
`A_p = ‖p^{-s₁}‖ + ‖p^{-s₂}‖ = 2‖w_p‖ ≤ 2/5`, by `RMF.norm_prime_cpow_le_fifth` at each abscissa,
with no lower bound on `p`.  The Steinhaus twin's `A_p ≤ 1/5` is not available that way: it holds
only from `p ≥ 100`. -/

/-- **The two-point Rademacher block variance, bracketed.**  Past an absolute threshold on
`τ e^{m+θ}` — the height condition — `1/8 ≤ 2·var ≤ 9`, the shape Probability Results 1 and 2 ask
for.  `Tsh` is fixed before the space is quantified over, which is what the packaging needs. -/
theorem exists_blockMatchedVarAdd₂_concrete_top :
    ∃ Tsh > 0,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (θ σ η : ℝ) (m y : ℕ) (s₁ s₂ u : ℂ) (w : Nat.Primes → ℂ),
      0 < s₁.re → 0 < s₂.re → s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ → u.re = 1 / 2 + σ →
      (9 : ℝ) ≤ (m : ℝ) + θ → 0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * u.im → (2 * u.im) ^ 2 ≤ Real.exp ((m : ℝ) + θ) →
      Tsh ≤ 2 * u.im * Real.exp ((m : ℝ) + θ) →
      (∀ p ∈ primeBlockSub θ m, w p = ((p : ℕ) : ℂ) ^ (-u)) →
      primeBlockSub θ m ⊆ primesBelowSub y →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9 := by
  obtain ⟨Tsh, hTsh0, hbr⟩ := exists_sum_re_cpow_neg_sq_primeBlockSub_bounds
  refine ⟨Tsh, hTsh0, ?_⟩
  intro Ω _ X μ hX θ σ η m y s₁ s₂ u w hs₁ hs₂ hre₁ hre₂ hu hmθ hθ hη hη' hσ hτ hτ2 hTsh hwv hB
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hσ1 : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := by linarith
  have hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p hp => by
    rw [hwv p hp]
    exact norm_sq_prime_cpow_neg p hu
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun p hp => by
    rw [hwv p hp]
    exact norm_prime_cpow_le_fifth hm3 hu hσ1 hp
  -- both tilt radii equal `‖w p‖` on the block: all three abscissae share a real part
  have heq : ∀ t : ℂ, t.re = 1 / 2 + σ → ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-t)‖ = ‖w p‖ := by
    intro t ht p hp
    have h : ‖((p : ℕ) : ℂ) ^ (-t)‖ ^ 2 = ‖w p‖ ^ 2 := by
      rw [norm_sq_prime_cpow_neg p ht, hwn p hp]
    rw [← Real.sqrt_sq (norm_nonneg (((p : ℕ) : ℂ) ^ (-t))), h,
      Real.sqrt_sq (norm_nonneg (w p))]
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2 := fun p hp => by
    rw [heq s₁ hre₁ p hp, heq s₂ hre₂ p hp]
    linarith [hw5 p hp]
  -- the error is at most `37/1000`
  have hcube := sum_norm_cube_primeBlockSub_le_of_nine hmθ hσ1 hwn
  have hterm : ∀ p ∈ primeBlockSub θ m,
      8 * ‖w p‖ ^ 3
          + 36 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 * ‖w p‖ ^ 2
        ≤ 37 * ‖w p‖ ^ 3 := fun p hp => by
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    rw [heq s₁ hre₁ p hp, heq s₂ hre₂ p hp]
    nlinarith [pow_nonneg h0 3,
      mul_nonneg (pow_nonneg h0 3) (by linarith [hw5 p hp] : (0 : ℝ) ≤ 1 / 5 - ‖w p‖)]
  have herr : (∑ p ∈ primeBlockSub θ m,
      (8 * ‖w p‖ ^ 3
        + 36 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 2 * ‖w p‖ ^ 2))
      ≤ 37 / 1000 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    linarith
  -- the main term, in the block's own variables
  have hsum : (∑ p ∈ primeBlockSub θ m, (w p).re ^ 2)
      = ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2 :=
    Finset.sum_congr rfl fun p hp => by rw [hwv p hp]
  obtain ⟨hlo, hhi⟩ := hbr θ σ η m u hu hmθ hθ hη hη' hσ hτ hτ2 hTsh
  have hgap := abs_blockMatchedVarAdd₂_sub_le hX y hs₁ hs₂ hB hA hw5
  rw [abs_le] at hgap
  rw [hsum] at hgap
  constructor <;> linarith [hgap.1, hgap.2]

/-! ### The drift at Harper's data

`RMF.abs_blockMeanAdd_le` at two points.  The main term's summand is
`2(Re p^{-s₁} + Re p^{-s₂})(Re w_p) - Re(w_p ² )/2`; on the block all three abscissae have the
same real part, so `|Re p^{-s_i}| ≤ ‖w_p‖` and the summand is at most `(9/2)‖w_p‖ ² ` where the
one-point one is at most `(5/2)‖w_p‖ ² ` and the Steinhaus one is `‖w_p‖ ² `.  The third-order
error of `RMF.abs_blockMeanAdd₂_sub_sum_le` adds `36κ + 48κ ² ≤ 0.037` of the block sum, with
`κ = RMF.blockWeightSize θ m ≤ 1/1000`, and
`RMF.abs_sum_rpow_primeBlockSub_sub_one_le` pins the block sum. -/

/-- **The two-point Rademacher block drift.**  `|blockMeanAdd₂| ≤ 5 e^{2η}(1 + 60/\log x_{m+1})`,
against `3` at one point: the two drifts add, and nothing else changes. -/
theorem abs_blockMeanAdd₂_le (hX : IsRademacherPrimeValues X μ) {s₁ s₂ : ℂ} {θ σ η : ℝ}
    {m n y : ℕ} {w : Nat.Primes → ℂ} (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hy : blockCutoff θ n ≤ y) (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    |blockMeanAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m)|
      ≤ 5 * (Real.exp (2 * η) * (1 + 60 / Real.log (blockScale θ (m + 1)))) := by
  have hσ1 : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := le_trans hσ hη1
  have hs₁ : 0 < s₁.re := re_pos_of_block hmθ hre₁ hσ1
  have hs₂ : 0 < s₂.re := re_pos_of_block hmθ hre₂ hσ1
  have hB := primeBlockSub_subset_primesBelowSub_of_le hmn hy
  have hκ0 : (0 : ℝ) < blockWeightSize θ m := blockWeightSize_pos θ m
  have hκ : blockWeightSize θ m ≤ 1 / 1000 := blockWeightSize_le hmθ
  -- all three abscissae share a real part, so the two tilt radii equal `‖w p‖` on the block
  have haw : ∀ t : ℂ, t.re = 1 / 2 + σ → ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-t)‖ = ‖w p‖ := by
    intro t ht p hp
    have h : ‖((p : ℕ) : ℂ) ^ (-t)‖ ^ 2 = ‖w p‖ ^ 2 := by
      rw [norm_sq_prime_cpow_neg p ht, hwn p hp]
    rw [← Real.sqrt_sq (norm_nonneg (((p : ℕ) : ℂ) ^ (-t))), h,
      Real.sqrt_sq (norm_nonneg (w p))]
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ blockWeightSize θ m := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ1 hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun p hp =>
    le_trans (hwκ p hp) (by linarith)
  have hA : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2 := fun p hp => by
    rw [haw s₁ hre₁ p hp, haw s₂ hre₂ p hp]
    linarith [hw5 p hp]
  -- the block sum, pinned
  have hblk := abs_sum_rpow_primeBlockSub_sub_one_le θ σ η m hmθ hη0 hσ
  set S : ℝ := ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) with hSdef
  set L : ℝ := Real.log (blockScale θ (m + 1)) with hLdef
  have hL0 : (0 : ℝ) < L := by
    rw [hLdef, log_blockScale]
    exact Real.exp_pos _
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun p _ => Real.rpow_nonneg (by positivity) _
  have hSle : S ≤ Real.exp (2 * η) * (1 + 60 / L) := by
    rw [abs_le] at hblk
    have h60 : (0 : ℝ) ≤ 60 / L := by positivity
    nlinarith [hblk.2, Real.exp_pos (2 * η)]
  -- the main term, termwise: `4‖w‖ ² ` from the two drifts and `‖w‖ ² /2` from the square
  have hmain : |∑ p ∈ primeBlockSub θ m,
      (2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re) * (w p).re
        - ((w p) ^ 2).re / 2)| ≤ 9 / 2 * S := by
    rw [hSdef, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hre : |(((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re| ≤ 2 * ‖w p‖ := by
      have e₁ := haw s₁ hre₁ p hp
      have e₂ := haw s₂ hre₂ p hp
      refine (abs_add_le _ _).trans ?_
      linarith [Complex.abs_re_le_norm (((p : ℕ) : ℂ) ^ (-s₁)),
        Complex.abs_re_le_norm (((p : ℕ) : ℂ) ^ (-s₂))]
    have hwre : |(w p).re| ≤ ‖w p‖ := Complex.abs_re_le_norm _
    have hsq : |((w p) ^ 2).re| ≤ ‖w p‖ ^ 2 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_pow]
    have h1 : |2 * ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re) * (w p).re|
        ≤ 4 * ‖w p‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg ((((p : ℕ) : ℂ) ^ (-s₁)).re + (((p : ℕ) : ℂ) ^ (-s₂)).re),
        abs_nonneg (w p).re]
    have h2 : |((w p) ^ 2).re / 2| ≤ ‖w p‖ ^ 2 / 2 := by
      rw [abs_div, abs_two]
      linarith
    rw [← hwn p hp]
    exact (abs_sub _ _).trans (by linarith)
  -- the third-order error, termwise: `36‖w‖³ + 48‖w‖⁴ ≤ (36κ + 48κ ² )‖w‖ ² `
  have herr : (∑ p ∈ primeBlockSub θ m,
      (36 * ‖w p‖ ^ 3
        + 6 * (‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖) ^ 3 * ‖w p‖))
      ≤ 37 / 1000 * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hk1 : ‖w p‖ ≤ 1 / 1000 := le_trans (hwκ p hp) hκ
    rw [haw s₁ hre₁ p hp, haw s₂ hre₂ p hp, ← hwn p hp]
    nlinarith [mul_nonneg (pow_nonneg h0 2) (by linarith : (0 : ℝ) ≤ 1 / 1000 - ‖w p‖),
      mul_nonneg (pow_nonneg h0 3) (by linarith : (0 : ℝ) ≤ 1 / 1000 - ‖w p‖),
      pow_nonneg h0 2, pow_nonneg h0 3]
  have hgap := abs_blockMeanAdd₂_sub_sum_le hX y hs₁ hs₂ hB hA hw5
  rw [abs_le] at hgap hmain ⊢
  have hpos : (0 : ℝ) < Real.exp (2 * η) * (1 + 60 / L) := by
    have h60 : (0 : ℝ) < 60 / L := by positivity
    have := Real.exp_pos (2 * η)
    nlinarith
  constructor <;> nlinarith [hgap.1, hgap.2, hmain.1, hmain.2, hSle, hS0, herr]

/-! ### The window mass at two points

`RMF.blockQAdd_le_measure` in two dimensions: the block Gaussian's box carries mass at least
`RMF.blockQ₂ θ m` for the Rademacher model.  The two variance brackets are hypotheses, in the
form `RMF.exists_blockMatchedVarAdd₂_concrete_top` supplies; the drifts come from
`RMF.abs_blockMeanAdd₂_le`, the residual bracket and the slope condition from
`RMF.pairResidVar_bracket` and `RMF.abs_pairSlope_le_and_cs_of_abs_le`, and the two thresholds from
`RMF.hthr_of_fourteen_le` and `RMF.hthr₂_of_fourteen_le`.

`hcov : |cv| ≤ 1/100` is not a fact about blocks: at `s₁ = s₂` the covariance is the variance.  It
is the height separation, which the block decorrelation estimate controls;
`RMF.exists_proposition7_upper_rademacher_of_ratio` derives it through
`RMF.exists_abs_blockMatchedCovAdd_shift_le`. -/

/-- **`hqlow` for the two-point Rademacher block** — the block Gaussian's box carries mass at
least `RMF.blockQ₂ θ m`. -/
theorem blockQAdd₂_le_measure (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ} {m n y : ℕ}
    {s₁ s₂ : ℂ} {v w : Nat.Primes → ℂ} {M : ℝ}
    (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n) (hy : blockCutoff θ n ≤ y)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hvn : ∀ p ∈ primeBlockSub θ m, ‖v p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (hV₁l : 1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ y s₁ s₂ v (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₁u : 2 * ((blockMatchedVarAdd₂ X μ y s₁ s₂ v (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (hV₂l : 1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₂u : 2 * ((blockMatchedVarAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (hcov : |blockMatchedCovAdd X μ y s₁ s₂ v w (primeBlockSub θ m)| ≤ 1 / 100)
    (henv : M + 5 * (Real.exp (2 * η) * (1 + 60 / Real.log (blockScale θ (m + 1))))
          + blockWindow m
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))) + 2) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      blockQ₂ θ m ≤ (gaussianPairLaw
          (blockMeanAdd₂ X μ y s₁ s₂ v (primeBlockSub θ m))
          (blockMeanAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m))
          ((blockMatchedVarAdd₂ X μ y s₁ s₂ v (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVarAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCovAdd X μ y s₁ s₂ v w (primeBlockSub θ m))
          (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m))).toReal := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hV₁16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂ v (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  have hV₂16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVarAdd₂ X μ y s₁ s₂ w (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  have hV₁pos : (0 : ℝ)
      < ((blockMatchedVarAdd₂ X μ y s₁ s₂ v (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  obtain ⟨hslope, hcs⟩ := abs_pairSlope_le_and_cs_of_abs_le hV₁16 hV₂16 hcov
  obtain ⟨hRl, hRu⟩ := pairResidVar_bracket hV₁pos hV₂l hV₂u hcs
  -- the two drifts
  have hd₁ := abs_blockMeanAdd₂_le hX hm3 hmn hy hre₁ hre₂ hη0 hη1 hσ hvn
  have hd₂ := abs_blockMeanAdd₂_le hX hm3 hmn hy hre₁ hre₂ hη0 hη1 hσ hwn
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
  exact le_toReal_measure_box_gaussianPairLaw_envelope hV₁l hV₁u hRl hRu hslope hh hh1 hx
    (by linarith) (by linarith) (hthr_of_fourteen_le hmθ) (hthr₂_of_fourteen_le hmθ)

/-! ### `hTb` at Harper's weights

The four third moments per prime, summed over the block, against `RMF.blockTAdd₂`.  Both
coordinates carry `p^{-s_i}` with the same real part, so `‖v_p‖ = ‖w_p‖` and the two applications
of `RMF.third_moment_pair_add_matching_leAdd` give `blockThirdConstAdd₂·‖v_p‖³` between them —
which is what that constant was defined to be.  `RMF.sum_norm_cube_primeBlockSub_le` finishes it.

**The block supplies `hA` with room to spare.**  There the two moduli are equal and at most
`κ ≤ 1/1000`, so their sum is at most `1/500`, where the estimate asks only `1/2`.  The
Steinhaus twin asks `1/5` and the block supplies that too — the hypothesis is not what separates
the two chains here. -/

/-- **`hTb` at Harper's weights**, the Rademacher form of
`RMF.sum_third_moment_pair_block_le`. -/
theorem sum_third_moment_pair_blockAdd_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {G : Nat.Primes → Ω' → ℝ × ℝ} (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {m y : ℕ}
    {s₁ s₂ : ℂ} (hy : primeBlockSub θ m ⊆ primesBelowSub y)
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hGm : ∀ p, Measurable (G p))
    (hlaw₁ : ∀ p ∈ primeBlockSub θ m, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
          y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            y s₁ s₂ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
            * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            y s₁ s₂ μ))))
    (hlaw₂ : ∀ p ∈ primeBlockSub θ m, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
        ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
          y s₁ s₂ μ))
      (matchingVar
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            y s₁ s₂ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
            * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            y s₁ s₂ μ)))) :
    ∑ p ∈ primeBlockSub θ m,
        ((∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)| ^ 3
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
              y s₁ s₂ μ))
          + (∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)| ^ 3
            ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
              y s₁ s₂ μ))
          + (∫ ω, |(G p ω).1| ^ 3 ∂Q) + ∫ ω, |(G p ω).2| ^ 3 ∂Q)
      ≤ blockTAdd₂ θ m := by
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
      ‖((p : ℕ) : ℂ) ^ (-s₁)‖ + ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 2 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    rw [← heq]; linarith
  -- per prime, the four moments come to `blockThirdConstAdd₂·‖v_p‖³`
  have hper : ∀ p ∈ primeBlockSub θ m,
      ((∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            y s₁ s₂ μ))
        + (∫ ω, |localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            y s₁ s₂ μ))
        + (∫ ω, |(G p ω).1| ^ 3 ∂Q) + ∫ ω, |(G p ω).2| ^ 3 ∂Q)
      ≤ blockThirdConstAdd₂ * ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ^ 3 := by
    intro p hp
    obtain ⟨heq, hle⟩ := hsmall p hp
    have hv5 : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5 := by linarith
    have hw5 : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5 := by rw [← heq]; linarith
    have h₁ := third_moment_pair_add_matching_leAdd hX y hs₁ hs₂ (hy hp)
      (hA p hp) hv5 ((hGm p).fst) (hlaw₁ p hp)
    have h₂ := third_moment_pair_add_matching_leAdd hX y hs₁ hs₂ (hy hp)
      (hA p hp) hw5 ((hGm p).snd) (hlaw₂ p hp)
    rw [← heq] at h₂
    rw [blockThirdConstAdd₂]
    linarith
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.mul_sum, blockTAdd₂]
  refine mul_le_mul_of_nonneg_left ?_ blockThirdConstAdd₂_pos.le
  exact sum_norm_cube_primeBlockSub_le hmθ hσ fun p _ => norm_sq_prime_cpow_neg p hre₁

/-! ### What the tilted side has to be integrable for

The comparison asks six integrability facts of the tilted increments: the five
`RMF.quadMonomial`s, the Lindeberg bound, and the two third absolute moments.  Every one is the
same observation — **the two-fold tilt lives on the circle, where `RMF.localLogAdd` is bounded** —
and they all factor through `RMF.integrable_comp_tiltedMeasure₂_of_bounded_rademacher`.  The
Steinhaus twins each carry `‖a₁‖ + ‖a₂‖ ≤ 1/5`; none of these does. -/

/-- **The Lindeberg bound is integrable** on the tilted side.  Same constant as the Steinhaus
twin, because `RMF.abs_localLogAdd_le_of_norm_le` has the same `11/5`. -/
lemma integrable_windowLindebergBound_localLogAdd_tiltedMeasure₂
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5)
    (hw : ‖w‖ ≤ 1 / 5) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ω => windowLindebergBound δ
        (localLogAdd v (X (p : ℕ) ω), localLogAdd w (X (p : ℕ) ω)))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  refine integrable_comp_tiltedMeasure₂_of_bounded_rademacher hX y hs₁ hs₂ hp
    (g := fun z => windowLindebergBound δ (localLogAdd v z, localLogAdd w z))
    ((measurable_windowLindebergBound δ).comp
      ((measurable_localLogAdd v).prodMk (measurable_localLogAdd w)))
    (C := 900 / δ ^ 3 * (22 / 25) ^ 3) ?_
  intro z hz
  have hbv := abs_localLogAdd_le_of_norm_le hz hv
  have hbw := abs_localLogAdd_le_of_norm_le hz hw
  have hnn : (0 : ℝ) ≤ windowLindebergBound δ (localLogAdd v z, localLogAdd w z) := by
    rw [windowLindebergBound, lindebergBound]
    have h₃ : (0 : ℝ) < δ ^ 3 := by positivity
    positivity
  have hle := windowLindebergBound_le hδ (localLogAdd v z, localLogAdd w z)
  have hcube : (|localLogAdd v z| + |localLogAdd w z|) ^ 3 ≤ (22 / 25 : ℝ) ^ 3 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    nlinarith [hbv, hbw, hv, hw, norm_nonneg v, norm_nonneg w]
  have hcoef : (0 : ℝ) ≤ 900 / δ ^ 3 := by positivity
  rw [abs_of_nonneg hnn]
  calc windowLindebergBound δ (localLogAdd v z, localLogAdd w z)
      ≤ 900 / δ ^ 3 * (|localLogAdd v z| + |localLogAdd w z|) ^ 3 := hle
    _ ≤ 900 / δ ^ 3 * (22 / 25 : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hcube hcoef

/-- **The five `RMF.quadMonomial`s are integrable** on the tilted side.  Three of the five are one
lemma applied three times: under this tilt `ξ₁ξ₁`, `ξ₁ξ₂` and `ξ₂ξ₂` are all the cross term. -/
lemma integrable_quadMonomial_localLogAdd_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ)
    (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {p : Nat.Primes}
    (hp : p ∈ primesBelowSub y) {v w : ℂ} (hv : ‖v‖ ≤ 1 / 5) (hw : ‖w‖ ≤ 1 / 5) (j : Fin 5) :
    Integrable (fun ω => quadMonomial j
        (localLogAdd v (X (p : ℕ) ω), localLogAdd w (X (p : ℕ) ω)))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) := by
  fin_cases j <;> simp only [quadMonomial]
  · exact integrable_localLogAdd_tiltedMeasure₂ hX y hs₁ hs₂ hp hv
  · exact integrable_localLogAdd_tiltedMeasure₂ hX y hs₁ hs₂ hp hw
  · exact integrable_localLogAdd_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hv hv
  · exact integrable_localLogAdd_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hv hw
  · exact integrable_localLogAdd_mul_tiltedMeasure₂ hX y hs₁ hs₂ hp hw hw

/-- **The two-point Rademacher envelope noise is absolute**, the analogue of
`RMF.blockEnvelopeNoise₂_le`: `5·e²(1 + 60/\log x_{m+1}) ≤ 38` once `θ ≥ 125`.  The `5` is the drift
constant of `RMF.abs_blockMeanAdd₂_le`, against the Steinhaus pair's `2 + 800κ`, which is the whole
difference between this `38` and the Steinhaus `15`; both are absorbed by `(1/40)√(\log x_{m+1})`,
which exceeds `40` at `θ ≥ 125`. -/
lemma blockEnvelopeNoiseAdd₂_le {θ : ℝ} (hθ : (125 : ℝ) ≤ θ) (m : ℕ) :
    5 * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (m + 1)))) ≤ 38 := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
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
  nlinarith [he2, he20, hdiv, hdiv0]

/-! ### The per-block step, with the family supplied

Everything above, fed to `RMF.le_measure_box_of_gaussian_pair_of_third_moment`: the layer at which
the Rademacher tilt stops being visible.  The per-block work is stated against a *supplied*
Gaussian family, because the multi-block layer needs one `Q` to serve every block.

**The variance bracket is a hypothesis, stated at the global cutoff.**  The Rademacher bracket
`RMF.exists_blockMatchedVarAdd₂_concrete_top` is existential in the height threshold `Tsh`, so a
theorem that called it would have to be existential too; the one-point
`RMF.exists_isWindowComparison_rademacher_of_cutoff` takes its bracket as a hypothesis for the same
reason.  `hcov` is also a hypothesis; `RMF.exists_proposition7_upper_rademacher_of_ratio`
discharges it for `RMF.exists_isBoxComparison_rademacher_of_range`. -/

/-- **The per-block step of the box comparison** for the Rademacher model, with the Gaussian
family supplied. -/
theorem box_comparison_blockAdd_of_family {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {G : Nat.Primes → Ω' → ℝ × ℝ}
    (hX : IsRademacherPrimeValues X μ) {θ σ : ℝ} {m n : ℕ} {s₁ s₂ : ℂ} {M : ℝ}
    {S : Finset Nat.Primes} (hθ : (125 : ℝ) ≤ θ) (hmn : m ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hV₁l : 1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₁u : 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (hV₂l : 1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₂u : 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
      (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (hcovm : |blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| ≤ 1 / 100)
    (henvm : M + blockWindow m + 36
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))))
    (hBS : primeBlockSub θ m ⊆ S) (hSsub : S ⊆ primesBelowSub (blockCutoff θ n))
    (hvS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₁)‖ ≤ 1 / 5)
    (hwS : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s₂)‖ ≤ 1 / 5)
    (hGm : ∀ p, Measurable (G p)) (hGi : iIndepFun G Q)
    (hmom : ∀ p ∈ S, ∀ j : Fin 5, (∫ ω, quadMonomial j
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)) = ∫ ω, quadMonomial j (G p ω) ∂Q)
    (hpair : ∀ p ∈ S, Q.map (G p) = gaussianPairLaw
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)) ^ 2)
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)) ^ 2)
      ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
          * ∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)))
    (hmarg₁ : ∀ p ∈ S, Q.map (fun ω => (G p ω).1) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      (matchingVar (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))))
    (hmarg₂ : ∀ p ∈ S, Q.map (fun ω => (G p ω).2) = gaussianReal
      (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
      (matchingVar (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))
        (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)
          ∂(tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ))))
    (hlawsum : Q.map (fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
        ∑ p ∈ primeBlockSub θ m, (G p ω).2))
      = gaussianPairLaw
          (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
          (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
          ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
          (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
            (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
            (primeBlockSub θ m))) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      (1 - blockEps θ m)
            * (Q ((fun ω => ((∑ p ∈ primeBlockSub θ m, (G p ω).1),
                ∑ p ∈ primeBlockSub θ m, (G p ω).2))
              ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
          ≤ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
        ∧ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
            (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ((∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω)),
                  ∑ p ∈ primeBlockSub θ m,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
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
    psd_of_tiltedMeasure₂_moments_rademacher hX (blockCutoff θ n) hs₁ hs₂ (hB hp)
      (hvS p (hBS hp)) (hwS p (hBS hp)) rfl rfl rfl rfl rfl
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  have hδ : (0 : ℝ) < blockTAdd₂ θ m ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (blockTAdd₂_pos hlogpos) _
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
      Integrable (fun ω => windowLindebergBound (blockTAdd₂ θ m ^ (1 / 4 : ℝ)) (G p ω)) Q := by
    intro p hp
    have hint : Integrable
        (fun z : ℝ × ℝ => windowLindebergBound (blockTAdd₂ θ m ^ (1 / 4 : ℝ)) z)
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
  -- the variance bracket arrives at the global cutoff already
  have hV₁16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
  have hV₂16 : (1 : ℝ) / 16
      ≤ ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) := by linarith
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
    refine blockQAdd₂_le_measure hX hmθ hmn (le_refl (blockCutoff θ n)) hre₁ hre₂
      zero_le_one le_rfl hσ (fun p _ => norm_sq_prime_cpow_neg p hre₁)
      (fun p _ => norm_sq_prime_cpow_neg p hre₂) hV₁l hV₁u hV₂l hV₂u hcovm ?_ c' d' hc' hd'
    have hnoise := blockEnvelopeNoiseAdd₂_le hθ m
    rw [show (2 : ℝ) * 1 = 2 by norm_num]
    linarith
  have hPprob := isProbabilityMeasure_tiltedMeasure₂_rademacher hX (blockCutoff θ n) hs₁ hs₂
  intro c d hc hd
  exact le_measure_box_of_gaussian_pair_of_third_moment
    (ξ := fun p ω => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
      localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (t := primeBlockSub θ m) (T := blockTAdd₂ θ m) (w := blockWindow m) (M := M)
    (ε := blockEps θ m) (q := blockQ₂ θ m)
    (fun p => ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)))
    hGm
    ((iIndepFun_tiltedMeasure₂_rademacher hX (blockCutoff θ n) hs₁ hs₂).comp
      (fun p z => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun p => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    hGi (blockTAdd₂_pos hlogpos)
    (fun p hp => integrable_quadMonomial_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hvS p (hBS hp)) (hwS p (hBS hp)))
    hmG (fun p hp => hmom p (hBS hp))
    (fun p hp => integrable_windowLindebergBound_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂
      (hB hp) (hvS p (hBS hp)) (hwS p (hBS hp)) hδ)
    hLG
    (fun p hp => integrable_abs_cube_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hvS p (hBS hp)))
    (fun p hp => integrable_abs_cube_localLogAdd_tiltedMeasure₂ hX _ hs₁ hs₂ (hB hp)
      (hwS p (hBS hp)))
    hG₁ hG₂
    (sum_third_moment_pair_blockAdd_le hX hB hm3 hre₁ hre₂ hσ hGm
      (fun p hp => hmarg₁ p (hBS hp)) (fun p hp => hmarg₂ p (hBS hp)))
    -- `positivity` would unfold `blockMatchedVarAdd₂` to prove `0 ≤ ↑x`; the coercion settles it
    hlawsum (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by nlinarith [hcs, hV₁16, hV₂16])
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; linarith)
    (blockQ₂_pos θ m) hqlow
    (blockNumAdd₂_le (θ := θ) (m := m) hmθ (by linarith) hV₁16 hV₂16)
    c d hc hd

/-- **The two-point block sums are independent under the two-fold tilt**, the Rademacher form of
`RMF.iIndepFun_blockSumPair_tiltedMeasure₂`.  Stated as a lemma rather than derived inline: the
inline form's inferred type carries `iIndepFun.comp`'s un-beta-reduced `g i ∘ f i`, and unifying
it against the shift lemma's `fun m => Z (m + k)` does not terminate in any heartbeat budget. -/
theorem iIndepFun_blockSumPairAdd_tiltedMeasure₂ (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (θ : ℝ) :
    iIndepFun (fun m ω => ∑ p ∈ primeBlockSub θ m,
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y s₁ s₂ μ) :=
  iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun (p : Nat.Primes) =>
      ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).prodMk
        ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)))
    ((iIndepFun_tiltedMeasure₂_rademacher hX y hs₁ hs₂).comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun (_ : Nat.Primes) => (measurable_localLogAdd _).prodMk (measurable_localLogAdd _))
    (pairwise_disjoint_primeBlockSub θ)

/-! ### The multi-block layer

One `Q` carrying every block, and `RMF.IsBoxComparison`: the two-point analogue of
`RMF.exists_isWindowComparison_primeBlockSub`; above it nothing knows about primes.

**No reservoir is needed.**  The one-point construction adds standard normals on `Nat.Primes ⊕ ℕ`
above the horizon because `IsGaussianWalk` demands a variance bounded below at every index, and
the block sums run to `0` past the top block.  `RMF.IsBoxComparison` quantifies only over `m < n`,
so the primes alone suffice, and the empty blocks contribute the constant `0`.

**The variance brackets arrive per block, as hypotheses**, for the reason given at the per-block
step: the bracket is existential in the height threshold, and
`RMF.exists_isWindowComparison_rademacher_of_cutoff` takes its bracket the same way. -/

/-- **The multi-block box comparison, with the block range free of the tilt cutoff.**

The tilt sits at `blockCutoff θ n` while the comparison runs only over blocks `m < r`.  Keeping
the two apart matters at a tilt scale `η > 1`: there the per-block scale exceeds `1` near the top,
and the barrier is stopped short of the tilt rather than the blocks weakened. -/
theorem exists_isBoxComparison_rademacher_of_range (hX : IsRademacherPrimeValues X μ)
    {θ σ : ℝ} {r n : ℕ} {s₁ s₂ : ℂ} {M : ℕ → ℝ} (hθ : (125 : ℝ) ≤ θ) (hrn : r ≤ n)
    (hre₁ : s₁.re = 1 / 2 + σ) (hre₂ : s₂.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ (r + 1)) ≤ 1)
    (hV₁ : ∀ m, m < r →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (hV₂ : ∀ m, m < r →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (hcov : ∀ m, m < r → |blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
        (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
        (primeBlockSub θ m)| ≤ 1 / 100)
    (henvc : ∀ m, m < r →
      M m + blockWindow m + 36 ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ × ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, m ≤ r → Q.map (N m) = gaussianPairLaw
        (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m))
        (blockMeanAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m))
        ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ((blockMatchedVarAdd₂ X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₂)) (primeBlockSub θ m) : ℝ≥0) : ℝ)
        (blockMatchedCovAdd X μ (blockCutoff θ n) s₁ s₂
          (fun p => ((p : ℕ) : ℂ) ^ (-s₁)) (fun p => ((p : ℕ) : ℂ) ^ (-s₂))
          (primeBlockSub θ m))) ∧
      ∀ k, k ≤ r → IsBoxComparison
        (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
          (blockCutoff θ n) s₁ s₂ μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
            localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
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
  -- one Gaussian family for the whole run
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hmom, hpair, hmarg₁, hmarg₂, hlawS⟩ :=
    exists_gaussian_pair_block_rademacher hX (blockCutoff θ n) hs₁ hs₂ hSsub hvS hwS
  have hPprob := isProbabilityMeasure_tiltedMeasure₂_rademacher hX (blockCutoff θ n) hs₁ hs₂
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω, hQ,
    fun m => Finset.measurable_sum _ fun p _ => hGm p,
    iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ),
    fun m hm => hlawS _ (hblockS m hm), ?_⟩
  have hZi := iIndepFun_blockSumPairAdd_tiltedMeasure₂ hX (blockCutoff θ n) hs₁ hs₂ θ
  -- **`hcmp` is stated and proved before the shift lemma sees it.**  Passed as a lambda with a
  -- hole, its expected type is read off `IsBoxComparison`'s unfolding, and elaborating it there
  -- costs forty seconds; stated up front it is immediate.
  have hcmp : ∀ m, m < r → ∀ c d : ℝ, |c| ≤ M m → |d| ≤ M m →
      (1 - blockEps θ m)
            * (Q ((fun ω => ∑ p ∈ primeBlockSub θ m, G p ω)
              ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
          ≤ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
                ⁻¹' (Set.Ioc c (c + blockWindow m) ×ˢ Set.Ioc d (d + blockWindow m)))).toReal
        ∧ ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ n) s₁ s₂ μ)
              ((fun ω => ∑ p ∈ primeBlockSub θ m,
                  (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
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
      sum_pair_eq (fun p ω => (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (primeBlockSub θ m)]
    exact box_comparison_blockAdd_of_family hX hθ hmn hre₁ hre₂ (hσ m hmr)
      (hV₁ m hm).1 (hV₁ m hm).2 (hV₂ m hm).1 (hV₂ m hm).2 (hcov m hm)
      (henvc m hm) hBS hSsub hvS hwS hGm hGi hmom hpair hmarg₁ hmarg₂ hlawsum c d hc hd
  intro k hkn
  -- `Z` and `N` are given, not inferred: left to unification the shift lemma unfolds
  -- `IsBoxComparison` and does not terminate in any heartbeat budget.
  exact isBoxComparison_shift_of_indep
    (Z := fun m ω => ∑ p ∈ primeBlockSub θ m,
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω)))
    (N := fun m ω => ∑ p ∈ primeBlockSub θ m, G p ω)
    (w := blockWindow) (M := M) (ε := blockEps θ) (E := 1 / 4) hZi
    (iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_primeBlockSub θ))
    hkn (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le (by linarith) r) (by norm_num) hcmp

end RMF
