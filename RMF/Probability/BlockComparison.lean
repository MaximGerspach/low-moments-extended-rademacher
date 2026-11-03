/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.NumberTheory.Bertrand
import RMF.Probability.HarperChain
import RMF.Probability.Grouping
import RMF.EulerProduct.TiltedMoments
import RMF.EulerProduct.Block
import RMF.NumberTheory.MertensBlock
import RMF.NumberTheory.PrimeTail

/-!
# The block comparison: from the third moment to Proposition 5

For the Steinhaus random multiplicative function under the tilt, this file proves the block form
of Harper's Lemma 3 (the tilted block increments are comparable, window by window, to matched
Gaussians) and assembles it into Harper's Proposition 5 (*Moments of random multiplicative
functions, I*, arXiv:1703.06654, §3.2):
`P̃(-a - Bj ≤ ∑_{m<j} log|I_m| ≤ a + j + h(j) ∀ j ≤ n) ≍ min{1, a/√n}`.

Notation: `x_m = RMF.blockScale θ m = e^{e^{m+θ}}`; block `m` is `RMF.primeBlockSub θ m`, the
primes `x_m < p ≤ x_{m+1}` (Harper's `j`-th block for `j = m + 1`); `ξ_p = localLog (w_p) (f(p))`.

* **The third moment**: `∑_{p ∈ B} (E~|ξ_p|³ + E|G_p|³) ≤ blockThirdConst · ∑_{p ∈ B} ‖w_p‖³`
  (`RMF.sum_third_moment_block_le`), the `T` of
  `RMF.isWindowComparison₁_of_gaussian_family_of_third_moment`, with
  `blockThirdConst = (11/5)³(1 + 4c₃) + 4(49/240)³ ≈ 78.7` and `c₃ = ∫|z|³ dN(0,1)`.  The matched
  Gaussian is not centred, so its third moment sees the tilted mean
  (`RMF.abs_integral_localLog_tiltedMeasure_le`) as well as the second moment.
* **Block Mertens and the variance**: `RMF.blockMatchedVar_concrete` (`1/8 ≤ 2V ≤ 9`) and its
  general-tilt form `RMF.blockMatchedVar_concrete_of_le`.
* **The multi-block comparison**: `RMF.exists_isWindowComparison_primeBlockSub_of_cutoff`, with its
  numerical hypotheses discharged in `RMF.exists_isWindowComparison_steinhaus_of_le` (and its
  `_of_range` and `_of_top` forms).
* **The drift**: `RMF.abs_sum_blockMean_sub_le`, and its form at a general tilt.
* **The walk and Proposition 5**: `RMF.exists_isGaussianWalk_steinhaus_of_le`,
  `RMF.exists_proposition5_steinhaus_of_le` and, with constants depending only on the tilt bound,
  `RMF.exists_const_proposition5_steinhaus_of_le`; their `_of_top` forms keep the constants of the
  untilted case by stopping the walk below the top blocks.
-/

set_option linter.style.longFile 5300

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The second moment, crudely

The matching needs `√(E~ξ²)`, and the sharp second moment
`RMF.abs_integral_localLog_sq_tiltedMeasure_sub_le` carries a `‖w‖²/2` main term plus errors.  For
the third moment only the *order* matters, so the crude bound `(11/5)²‖w‖²` is used — the same
constant as the a.e. bound, since `|ξ| ≤ (11/5)‖w‖` pointwise on the circle. -/

/-- **The tilted second moment, crudely**: `E~ξ_p² ≤ (11/5)²‖w‖²`.

By `RMF.abs_integral_localLog_sq_tiltedMeasure_sub_le`,
`E~ξ² ≤ ‖w‖²/2 + 20‖w‖³ + ‖w‖²‖p^{-s}‖²/2`, and at `‖w‖, ‖p^{-s}‖ ≤ 1/5` the right side is at most
`4.52‖w‖² ≤ (11/5)²‖w‖²`. -/
theorem integral_localLog_sq_tiltedMeasure_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5)
    (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) :
    (∫ ω, localLog w (X (p : ℕ) ω) ^ 2
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      ≤ (11 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  have hkey := abs_sub_le_iff.1 (abs_integral_localLog_sq_tiltedMeasure_sub_le hX y hs hp hw)
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have ha0 : (0 : ℝ) ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ := norm_nonneg _
  have h1 : ‖w‖ ^ 3 ≤ 1 / 5 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  have h2 : ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ 1 / 25 := by nlinarith
  have h3 : ‖w‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ ‖w‖ ^ 2 * (1 / 25) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  linarith [hkey.1, h1, h3]

/-- The local terms are square-integrable under the tilt, which is what Cauchy–Schwarz needs. -/
lemma memLp_two_localLog_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    MemLp (fun ω => localLog w (X (p : ℕ) ω)) 2
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) := by
  have hint := integrable_localLog_mul_self_tiltedMeasure hX y hs hp hw
  have hmeas : Measurable (fun ω => localLog w (X (p : ℕ) ω)) :=
    (measurable_localLog w).comp (hX.measurable (p : ℕ) p.2)
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  simpa only [pow_two] using hint

/-- **Cauchy–Schwarz for the local terms** — the hypothesis
`RMF.exists_gaussian_matching_moments` asks for, discharged. -/
lemma sq_integral_localLog_le_integral_mul_self (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2
      ≤ ∫ ω, localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) := by
  have := hX.isProbabilityMeasure_tiltedMeasure y hs
  exact sq_integral_le_integral_mul_self (memLp_two_localLog_tiltedMeasure hX y hs hp hw)

/-! ### The constant -/

/-- The absolute constant in the block third-moment bound,
`(11/5)³(1 + 4c₃) + 4(49/240)³` with `c₃ = ∫|z|³ dN(0,1) = 2√(2/π) ≈ 1.5958`.  Numerically
`≈ 78.7`: about `10.6` from the summands themselves and about `68` from the matched Gaussians,
whose third moment costs a factor `4` for not being centred. -/
noncomputable def blockThirdConst : ℝ :=
  (11 / 5 : ℝ) ^ 3 * (1 + 4 * absMomentConst 3) + 4 * (49 / 240 : ℝ) ^ 3

/-- The constant of the **two-point** block third-moment bound,
`2((11/5)³ + 4(c₃(11/5)³ + (57/5)³)) ≈ 12010`.  It is not `2·blockThirdConst ≈ 157`: under the
two-fold tilt the matched mean is `≤ (57/5)‖w‖` (`RMF.abs_integral_localLog_tiltedMeasure₂_le`)
against the one-fold `≤ (49/240)‖w‖`, and it enters cubed; the summand's third moment and the
matched variance are unchanged.  `RMF.blockNum₂_le_of_le` allows the resulting `Kb` up to
`e^{100}`, and this constant gives `Kb ≤ e^{15}`. -/
noncomputable def blockThirdConst₂ : ℝ :=
  2 * ((11 / 5 : ℝ) ^ 3 + 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (57 / 5 : ℝ) ^ 3))

/-! ### The two halves, per prime -/

/-- **The matched Gaussian's third moment**, in terms of `‖w‖` alone.

The Gaussian matched to `ξ_p` has mean `E~ξ_p`, of size at most `(49/240)‖w‖`, and variance at most
`E~ξ_p² ≤ (11/5)²‖w‖²`; `RMF.integral_abs_cube_of_hasLaw_matching` turns those into the third
moment. -/
theorem integral_abs_cube_matching_localLog_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω' → ℝ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5)
    (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      (matchingVar
        (∫ ω, localLog w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        (∫ ω, localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)))) :
    ∫ ω, |Y ω| ^ 3 ∂Q
      ≤ 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (49 / 240 : ℝ) ^ 3) * ‖w‖ ^ 3 := by
  set Pt := tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ with hPt
  set m₁ : ℝ := ∫ ω, localLog w (X (p : ℕ) ω) ∂Pt with hm₁
  set m₂ : ℝ := ∫ ω, localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω) ∂Pt with hm₂
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hcs : m₁ ^ 2 ≤ m₂ := sq_integral_localLog_le_integral_mul_self hX y hs hp hw
  -- the mean
  have hmean : |m₁| ≤ 49 / 240 * ‖w‖ := by
    have hb := abs_integral_localLog_tiltedMeasure_le hX y hs hp hw ha
    nlinarith [abs_nonneg m₁, norm_nonneg (((p : ℕ) : ℂ) ^ (-s))]
  have hmean₃ : |m₁| ^ 3 ≤ (49 / 240 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg m₁) hmean 3
    calc |m₁| ^ 3 ≤ (49 / 240 * ‖w‖) ^ 3 := this
      _ = (49 / 240 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  -- the second moment
  have hsq : m₂ ≤ (11 / 5 * ‖w‖) ^ 2 := by
    have h := integral_localLog_sq_tiltedMeasure_le hX y hs hp hw ha
    have hpow : (∫ ω, localLog w (X (p : ℕ) ω) ^ 2 ∂Pt) = m₂ := by
      rw [hm₂]; simp only [pow_two]
    rw [hpow] at h
    calc m₂ ≤ (11 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := h
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

/-- **The two halves together, per prime**: `E~|ξ_p|³ + E|G_p|³ ≤ blockThirdConst·‖w‖³`. -/
theorem third_moment_add_matching_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω' → ℝ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5)
    (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLog w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      (matchingVar
        (∫ ω, localLog w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        (∫ ω, localLog w (X (p : ℕ) ω) * localLog w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)))) :
    (∫ ω, |localLog w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      + ∫ ω, |Y ω| ^ 3 ∂Q ≤ blockThirdConst * ‖w‖ ^ 3 := by
  have hξ := integral_abs_localLog_cube_tiltedMeasure_le hX y hs hp hw
  have hG := integral_abs_cube_matching_localLog_le hX y hs hp hw ha hYm hlaw
  have hc := absMomentConst_nonneg 3
  unfold blockThirdConst
  nlinarith [hξ, hG, pow_nonneg (norm_nonneg w) 3]

/-! ### The block sum -/

/-- **The block third-moment sum**, the `T` of
`RMF.isWindowComparison₁_of_gaussian_family_of_third_moment`:
`∑_{p ∈ B} (E~|ξ_p|³ + E|G_p|³) ≤ blockThirdConst · ∑_{p ∈ B} ‖w_p‖³`.  Per prime and then summed:
no independence is used, only the two moments each `G_p` is matched to.  Of the constant `≈ 78.7`
the Gaussians carry about `68`, the summands about `10.6`. -/
theorem sum_third_moment_block_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {G : Nat.Primes → Ω' → ℝ} (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) (ha : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    (hGm : ∀ p, Measurable (G p))
    (hGlaw : ∀ p ∈ B, Q.map (G p) = gaussianReal
      (∫ ω, localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      (matchingVar
        (∫ ω, localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        (∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)))) :
    (∑ p ∈ B, ((∫ ω, |localLog (w p) (X (p : ℕ) ω)| ^ 3
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
        + ∫ ω, |G p ω| ^ 3 ∂Q))
      ≤ blockThirdConst * ∑ p ∈ B, ‖w p‖ ^ 3 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p hp =>
    third_moment_add_matching_le hX y hs (hB hp) (hw p hp) (ha p hp) (hGm p) (hGlaw p hp)

/-! ### Lemma 3 for the Steinhaus block

Everything above is per-prime.  What follows builds the Gaussian family once, matched to the block's
summands, and hands back the window comparison for the block increment
`∑_{p∈B} localLog (w_p) (f(p))` — which at `w_p = p^{-1/2-σ-it}` is the increment of
`log‖F(s)‖` over the block.

The two parameters of the comparison are named before the construction, so that the caller can
state the window hypothesis without knowing which auxiliary space the Gaussians live on. -/

/-- The tilted mean of the block increment — the mean of the Gaussian it is compared to. -/
noncomputable def blockMean (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ B, ∫ ω, localLog (w p) (X (p : ℕ) ω)
    ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)

/-- The variance of that Gaussian: the sum of the per-prime matched variances
`E~ξ_p² - (E~ξ_p)²`.  `RMF.abs_blockVar_sub_le` identifies it with `∑_{p∈B}‖w_p‖²/2` up to
`O(∑‖w_p‖³)`, and `RMF.sum_prime_block_rpow_bounds` then pins it two-sidedly. -/
noncomputable def blockMatchedVar (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (B : Finset Nat.Primes) : ℝ≥0 :=
  ∑ p ∈ B, matchingVar
    (∫ ω, localLog (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
    (∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
      ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))

/-- **The matched block variance, as a real number**:
`(blockMatchedVar : ℝ) = ∑_{p∈B} (E~ξ_p² - (E~ξ_p)²)`.  `matchingVar` truncates at zero, but under
Cauchy–Schwarz the truncation never fires.  Since the `ξ_p` are independent under the tilt
(`RMF.IsSteinhausPrimeValues.iIndepFun_localLog_tiltedMeasure`), this is the variance of the block
increment. -/
theorem coe_blockMatchedVar (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    ((blockMatchedVar X μ y s w B : ℝ≥0) : ℝ)
      = ∑ p ∈ B, ((∫ ω, localLog (w p) (X (p : ℕ) ω) ^ 2
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
          - (∫ ω, localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)) ^ 2) := by
  have hprob := hX.isProbabilityMeasure_tiltedMeasure y hs
  rw [blockMatchedVar, NNReal.coe_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [coe_matchingVar (sq_integral_localLog_le_integral_mul_self hX y hs (hB hq) (hw q hq))]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (pow_two _).symm)

/-- **The matched block variance is positive** when `‖w_p‖ ≤ 1/100`, `‖p^{-s}‖ ≤ 1/5` on the
block and some `w_p ≠ 0`.  By `RMF.abs_blockVar_sub_le`,
`|V - ∑‖w_p‖²/2| ≤ ∑(20‖w_p‖³ + (5/2)‖w_p‖²‖p^{-s}‖²)`; at `‖w_p‖ ≤ 1/5` the errors swamp the main
term, while `‖w_p‖ ≤ 1/100` leaves `V ≥ (1/5)∑‖w_p‖²`. -/
theorem blockMatchedVar_pos (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 100) (ha : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    (hne : ∃ p ∈ B, w p ≠ 0) :
    0 < blockMatchedVar X μ y s w B := by
  have hprob := hX.isProbabilityMeasure_tiltedMeasure y hs
  have hw5 : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5 := fun p hp => le_trans (hw p hp) (by norm_num)
  have hcoe := coe_blockMatchedVar hX y hs hB hw5
  set Pt := tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ with hPt
  -- the block variance estimate, and the errors beaten by the main term
  have hbv := abs_sub_le_iff.1 (abs_blockVar_sub_le hX y hs hB hw5 ha)
  have herr : ∑ p ∈ B, (20 * ‖w p‖ ^ 3
        + 5 / 2 * (‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2))
      ≤ ∑ p ∈ B, 3 / 10 * ‖w p‖ ^ 2 := by
    refine Finset.sum_le_sum fun q hq => ?_
    have h1 : ‖w q‖ ^ 3 ≤ 1 / 100 * ‖w q‖ ^ 2 := by
      nlinarith [norm_nonneg (w q), sq_nonneg ‖w q‖, hw q hq]
    have h2 : ‖((q : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ 1 / 25 := by
      nlinarith [norm_nonneg (((q : ℕ) : ℂ) ^ (-s)), ha q hq]
    have h3 : ‖w q‖ ^ 2 * ‖((q : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ ‖w q‖ ^ 2 * (1 / 25) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    linarith
  -- and the main term is positive
  have hpos : 0 < ∑ p ∈ B, ‖w p‖ ^ 2 := by
    obtain ⟨q, hqB, hq0⟩ := hne
    refine Finset.sum_pos' (fun r _ => sq_nonneg _) ⟨q, hqB, ?_⟩
    have : ‖w q‖ ≠ 0 := norm_ne_zero_iff.2 hq0
    positivity
  have hhalf : ∑ p ∈ B, ‖w p‖ ^ 2 / 2 = (1 / 2) * ∑ p ∈ B, ‖w p‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have h310 : ∑ p ∈ B, 3 / 10 * ‖w p‖ ^ 2 = (3 / 10) * ∑ p ∈ B, ‖w p‖ ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  rw [← NNReal.coe_pos, hcoe]
  rw [hhalf] at hbv
  rw [h310] at herr
  linarith [hbv.2, herr, hpos]

/-! ### Harper's block, in the indexing the comparison uses

Three indexings of a block of primes meet here and none of them agree on the nose.

* `RMF/EulerProduct/Block.lean` uses `primesIco y₀ y₁ : Finset ℕ`, half-open on the left;
* `RMF/NumberTheory/MertensBlock.lean` states the prime sums over
  `{p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ | p.Prime}`, half-open on the right — the indexing
  `PrimeNumberTheoremAnd`'s Mertens comes in;
* everything probabilistic is indexed by `Finset Nat.Primes`, because the independent family is.

The first two differ by a shift of one (`m < p ≤ n ↔ m+1 ≤ p < n+1` in `ℕ`), and the third is
`Finset.subtype`.  Both moves are lossless, and this section makes them once. -/

/-- The primes of `[y₀, y₁)`, promoted to `Finset Nat.Primes`. -/
noncomputable def primesIcoSub (y₀ y₁ : ℕ) : Finset Nat.Primes :=
  (primesIco y₀ y₁).subtype Nat.Prime

@[simp]
lemma mem_primesIcoSub {y₀ y₁ : ℕ} {p : Nat.Primes} :
    p ∈ primesIcoSub y₀ y₁ ↔ y₀ ≤ (p : ℕ) ∧ (p : ℕ) < y₁ := by
  constructor
  · intro h
    have h' := mem_primesIco.1 (Finset.mem_subtype.1 h)
    exact ⟨h'.2.1, h'.2.2⟩
  · intro h
    exact Finset.mem_subtype.2 (mem_primesIco.2 ⟨p.2, h.1, h.2⟩)

/-- Sums over a block read the same either way. -/
lemma sum_primesIcoSub {M : Type*} [AddCommMonoid M] (y₀ y₁ : ℕ) (F : ℕ → M) :
    ∑ p ∈ primesIcoSub y₀ y₁, F (p : ℕ) = ∑ p ∈ primesIco y₀ y₁, F p :=
  Finset.sum_subtype_of_mem F fun _ hp => prime_of_mem_primesIco hp

lemma primesIcoSub_subset_primesBelowSub {y₀ y₁ y : ℕ} (h : y₁ ≤ y) :
    primesIcoSub y₀ y₁ ⊆ primesBelowSub y := by
  intro p hp
  rw [mem_primesIcoSub] at hp
  rw [mem_primesBelowSub, Nat.mem_primesBelow]
  exact ⟨lt_of_lt_of_le hp.2 h, p.2⟩

/-- **Harper's block** `X^{1/e} < p ≤ X`, as a `Finset Nat.Primes`. -/
noncomputable def harperBlock (X : ℝ) : Finset Nat.Primes :=
  primesIcoSub (⌊X ^ (Real.exp 1)⁻¹⌋₊ + 1) (⌊X⌋₊ + 1)

lemma harperBlock_subset (X : ℝ) : harperBlock X ⊆ primesBelowSub (⌊X⌋₊ + 1) :=
  primesIcoSub_subset_primesBelowSub le_rfl

lemma lt_of_mem_harperBlock {X : ℝ} {p : Nat.Primes} (hp : p ∈ harperBlock X) :
    X ^ (Real.exp 1)⁻¹ < (p : ℝ) := by
  rw [harperBlock, mem_primesIcoSub] at hp
  refine lt_of_lt_of_le (Nat.lt_floor_add_one _) ?_
  exact_mod_cast hp.1

lemma le_of_mem_harperBlock {X : ℝ} (hX : 0 ≤ X) {p : Nat.Primes} (hp : p ∈ harperBlock X) :
    (p : ℝ) ≤ X := by
  rw [harperBlock, mem_primesIcoSub] at hp
  have : (p : ℕ) ≤ ⌊X⌋₊ := by omega
  exact le_trans (by exact_mod_cast this) (Nat.floor_le hX)

/-- **Membership in a block, in real terms.** -/
lemma mem_harperBlock {X : ℝ} (hX : 0 ≤ X) {p : Nat.Primes} :
    p ∈ harperBlock X ↔ X ^ (Real.exp 1)⁻¹ < (p : ℝ) ∧ (p : ℝ) ≤ X := by
  rw [harperBlock, mem_primesIcoSub]
  have h0 : (0 : ℝ) ≤ X ^ (Real.exp 1)⁻¹ := Real.rpow_nonneg hX _
  constructor
  · rintro ⟨h1, h2⟩
    have ha : ⌊X ^ (Real.exp 1)⁻¹⌋₊ < (p : ℕ) := by omega
    have hb : (p : ℕ) ≤ ⌊X⌋₊ := by omega
    exact ⟨(Nat.floor_lt h0).1 ha, (Nat.le_floor_iff hX).1 hb⟩
  · rintro ⟨h1, h2⟩
    have ha : ⌊X ^ (Real.exp 1)⁻¹⌋₊ < (p : ℕ) := (Nat.floor_lt h0).2 h1
    have hb : (p : ℕ) ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).2 h2
    exact ⟨by omega, by omega⟩

/-! ### The blocks, bottom up

`RMF.harperBlock` takes the *top* of a block and reconstructs the bottom as `X^{1/e}`.  Harper's
own scales run the other way: Proposition 5 sets `l_j := ⌊log log x⌋ - D - j`, so that

`log log x_j = {log log x} + D - 1 + j`,

an arithmetic progression of step `1` in `log log`, starting from an offset `θ` that depends on `x`
only through the *fractional part* of `log log x`.  So the family is bottom-up — `e^{e^{j+θ}}` — and
the offset cannot be dropped: fixing `θ = 0` would restrict to those `x` with `log log x ∈ ℤ`.

The bridge is the identity `(e^{e^{u+1}})^{1/e} = e^{e^u}`, which is just `e^{u+1}/e = e^u`.  It
means the top-down and bottom-up descriptions are the *same* block, so nothing above has to be
reproved. -/

/-- The `j`-th multiplicative scale at offset `θ`: `e^{e^{j+θ}}`.  Harper's `x_j` is this at
`θ = {log log x} + D - 1`. -/
noncomputable def blockScale (θ : ℝ) (j : ℕ) : ℝ := Real.exp (Real.exp ((j : ℝ) + θ))

lemma blockScale_pos (θ : ℝ) (j : ℕ) : 0 < blockScale θ j := Real.exp_pos _

lemma blockScale_mono (θ : ℝ) : Monotone (blockScale θ) := fun i j h => by
  refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
  linarith

@[simp]
lemma log_blockScale (θ : ℝ) (j : ℕ) : Real.log (blockScale θ j) = Real.exp ((j : ℝ) + θ) :=
  Real.log_exp _

/-- **The scales are exactly a factor `e` apart in the logarithm**:
`(blockScale θ (j+1))^{1/e} = blockScale θ j`, because `e^{u+1}/e = e^u`.

This is what makes `log log` of the two ends of a block differ by exactly `1`, hence the main term
of block Mertens exactly `1`. -/
lemma blockScale_rpow_inv_exp_one (θ : ℝ) (j : ℕ) :
    blockScale θ (j + 1) ^ (Real.exp 1)⁻¹ = blockScale θ j := by
  rw [blockScale, blockScale, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_neg, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- The same identity the other way: `(blockScale θ j)^e = blockScale θ (j+1)`. -/
lemma blockScale_rpow_exp_one (θ : ℝ) (j : ℕ) :
    blockScale θ j ^ Real.exp 1 = blockScale θ (j + 1) := by
  rw [blockScale, blockScale, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 2
  push_cast
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The `j`-th block, bottom up**: the primes with `e^{e^{j+θ}} < p ≤ e^{e^{j+1+θ}}`. -/
noncomputable def primeBlockSub (θ : ℝ) (j : ℕ) : Finset Nat.Primes :=
  harperBlock (blockScale θ (j + 1))

@[simp]
lemma mem_primeBlockSub {θ : ℝ} {j : ℕ} {p : Nat.Primes} :
    p ∈ primeBlockSub θ j ↔ blockScale θ j < (p : ℝ) ∧ (p : ℝ) ≤ blockScale θ (j + 1) := by
  rw [primeBlockSub, mem_harperBlock (blockScale_pos θ (j + 1)).le,
    blockScale_rpow_inv_exp_one]

/-- **The blocks are pairwise disjoint** — they are the unit intervals of `log log p`, shifted by
`θ`.  This is what the multi-block comparison will need in order to treat the block increments as
an independent family. -/
lemma disjoint_primeBlockSub {θ : ℝ} {i j : ℕ} (h : i < j) :
    Disjoint (primeBlockSub θ i) (primeBlockSub θ j) := by
  refine Finset.disjoint_left.2 fun p hp hp' => ?_
  rw [mem_primeBlockSub] at hp hp'
  have hle : blockScale θ (i + 1) ≤ blockScale θ j := (blockScale_mono θ) (by omega)
  linarith [hp.2, hp'.1]

/-- **The threshold on a block, in both forms**: `c^e ≤ x` gives `0 < x` and `c ≤ x^{1/e}`.
Stating it on `x` rather than on `x^{1/e}` removes a positivity hypothesis: for `x < 0` Lean reads
`x^{1/e}` as `|x|^{1/e}·cos(π/e)` (`Real.rpow_def_of_neg`), which is large and positive for `x`
very negative. -/
lemma pos_and_le_rpow_inv_exp_one {c x : ℝ} (hc : 0 < c) (h : c ^ Real.exp 1 ≤ x) :
    0 < x ∧ c ≤ x ^ (Real.exp 1)⁻¹ := by
  have hcpos : (0 : ℝ) < c ^ Real.exp 1 := Real.rpow_pos_of_pos hc _
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hcpos h
  refine ⟨hx0, ?_⟩
  have hmono := Real.rpow_le_rpow hcpos.le h (le_of_lt (by positivity : (0:ℝ) < (Real.exp 1)⁻¹))
  rwa [← Real.rpow_mul hc.le, mul_inv_cancel₀ (Real.exp_pos 1).ne', Real.rpow_one] at hmono

/-- **The side condition `‖u‖ ≤ K`** on Harper's block, for any `u` with `‖u‖² = p^{-1-2σ}` (the
observed weight and the tilt radius at `Re s = 1/2 + σ` both qualify), once `|σ| log X ≤ 1` and
`X ≥ (e²/K²)^e`.  Downstream `K = 1/100`, which the variance positivity needs
(`RMF.blockMatchedVar_pos`); the threshold is then `X ≥ (10⁴e²)^e ≈ 1.7·10¹³`, i.e. `j + θ ≥ 3` in
the bottom-up indexing. -/
lemma norm_le_of_mem_harperBlock {X σ K : ℝ} (hK : 0 < K)
    (hσ : |σ| * Real.log X ≤ 1) (hX : (Real.exp 2 / K ^ 2) ^ Real.exp 1 ≤ X)
    {p : Nat.Primes} (hp : p ∈ harperBlock X) {u : ℂ}
    (hu : ‖u‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ‖u‖ ≤ K := by
  obtain ⟨hX0, hthr⟩ := pos_and_le_rpow_inv_exp_one (by positivity) hX
  have hplow : X ^ (Real.exp 1)⁻¹ < ((p : ℕ) : ℝ) := lt_of_mem_harperBlock hp
  have hpthr : Real.exp 2 / K ^ 2 < ((p : ℕ) : ℝ) := lt_of_le_of_lt hthr hplow
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have h2 : 1 ≤ (p : ℕ) := p.2.one_lt.le
    exact_mod_cast h2
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hbnd := (rpow_neg_one_sub_two_mul_bounds hp1 (le_of_mem_harperBlock hX0.le hp) hσ).2
  have hsq : ‖u‖ ^ 2 ≤ Real.exp 2 * (1 / ((p : ℕ) : ℝ)) := by rw [hu]; exact hbnd
  have hdiv : Real.exp 2 * (1 / ((p : ℕ) : ℝ)) ≤ K ^ 2 := by
    rw [mul_one_div, div_le_iff₀ hp0]
    rw [div_lt_iff₀ (by positivity)] at hpthr
    nlinarith [hpthr]
  nlinarith [norm_nonneg u, hsq, hdiv, hK]

/-! ### The tilt hypothesis at a general scale

The lower bound needs the tilt at `σ = 4V/\log x` with `V` a large constant, so at
`|σ|·\log x ≈ 4V`, and the hypothesis has to be `|σ|·\log X ≤ η` with `η` a parameter.  The
arithmetic on either side of the probability layer is already stated at any `η`:
`RMF.rpow_neg_one_sub_two_mul_bounds_of_le`, and the per-block scaling `RMF.sigma_le_mul_exp_sub`
(a scale `K` at the top is `Ke^{m-n}` at block `m`).

The cost of a general `η` is `e^{2η}` in place of `e^2`, a constant.  The one place it is not free
is the block start, which rises from `j + θ ≥ 3` to `j + θ ≥ \log(14 + 2η)`, logarithmic in `η`:
`θ ≥ 4` covers `η ≤ 20` and `θ ≥ 5` covers `η ≤ 67`. -/

/-- **The weight bound on a Harper block, at a general tilt scale.**
`RMF.norm_le_of_mem_harperBlock` is the case `η = 1`.

The only change is that the threshold on the block reads `(e^{2η}/K^2)^e ≤ X` rather than
`(e^2/K^2)^e ≤ X`: the tilt can depress the weight by `e^{2η}` across the block, so the block has to
start `e^{2η}` further up for the same bound on `‖u‖`. -/
lemma norm_le_of_mem_harperBlock_of_le {X σ K η : ℝ} (hK : 0 < K)
    (hσ : |σ| * Real.log X ≤ η) (hX : (Real.exp (2 * η) / K ^ 2) ^ Real.exp 1 ≤ X)
    {p : Nat.Primes} (hp : p ∈ harperBlock X) {u : ℂ}
    (hu : ‖u‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ‖u‖ ≤ K := by
  obtain ⟨hX0, hthr⟩ := pos_and_le_rpow_inv_exp_one (by positivity) hX
  have hplow : X ^ (Real.exp 1)⁻¹ < ((p : ℕ) : ℝ) := lt_of_mem_harperBlock hp
  have hpthr : Real.exp (2 * η) / K ^ 2 < ((p : ℕ) : ℝ) := lt_of_le_of_lt hthr hplow
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have h2 : 1 ≤ (p : ℕ) := p.2.one_lt.le
    exact_mod_cast h2
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hbnd := (rpow_neg_one_sub_two_mul_bounds_of_le hp1
    (le_of_mem_harperBlock hX0.le hp) hσ).2
  have hsq : ‖u‖ ^ 2 ≤ Real.exp (2 * η) * (1 / ((p : ℕ) : ℝ)) := by rw [hu]; exact hbnd
  have hdiv : Real.exp (2 * η) * (1 / ((p : ℕ) : ℝ)) ≤ K ^ 2 := by
    rw [mul_one_div, div_le_iff₀ hp0]
    rw [div_lt_iff₀ (by positivity)] at hpthr
    nlinarith [hpthr]
  nlinarith [norm_nonneg u, hsq, hdiv, hK]

/-- **The block weight sum, two-sided, in the comparison's indexing**: for `X ≥ e^e`,
`|σ| log X ≤ 1` and `‖w_p‖² = p^{-1-2σ}` on Harper's block,
`e^{-2}(1 - 60/log X) ≤ ∑_{p∈B}‖w_p‖² ≤ e²(1 + 60/log X)`.  This is
`RMF.sum_prime_block_rpow_bounds` carried across the two indexing shifts; the sum is `2V` up to the
errors of `RMF.abs_blockVar_sub_le`. -/
theorem sum_norm_sq_harperBlock_bounds (X σ : ℝ) (w : Nat.Primes → ℂ)
    (hX : Real.exp (Real.exp 1) ≤ X) (hσ : |σ| * Real.log X ≤ 1)
    (hnorm : ∀ p ∈ harperBlock X, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
      Real.exp (-2) * (1 - 60 / Real.log X) ≤ ∑ p ∈ harperBlock X, ‖w p‖ ^ 2
      ∧ ∑ p ∈ harperBlock X, ‖w p‖ ^ 2 ≤ Real.exp 2 * (1 + 60 / Real.log X) := by
  have hrw : ∑ p ∈ harperBlock X, ‖w p‖ ^ 2
      = ∑ p ∈ {p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ | Nat.Prime p},
          (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [Finset.sum_congr rfl hnorm, harperBlock,
      sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-1 - 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  exact sum_prime_block_rpow_bounds X σ hX hσ

/-- **The block weight sum at a general tilt scale**, for `X ≥ e^e`, `σ ≥ 0`, `|σ| log X ≤ η` and
`‖w_p‖² = p^{-1-2σ}` on Harper's block: `e^{-2η}(1 - 60/log X) ≤ ∑_{p∈B}‖w_p‖² ≤ 1 + 60/log X`.
The lower bound keeps its `e^{-2η}` (the tilt thins the block); the upper bound loses `η`, since
`σ ≥ 0` gives `p^{-1-2σ} ≤ p^{-1}` termwise (`RMF.sum_prime_block_rpow_le_of_nonneg`). -/
theorem sum_norm_sq_harperBlock_bounds_of_le (X σ η : ℝ) (w : Nat.Primes → ℂ)
    (hX : Real.exp (Real.exp 1) ≤ X) (hσ0 : 0 ≤ σ) (hσ : |σ| * Real.log X ≤ η)
    (hnorm : ∀ p ∈ harperBlock X, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
      Real.exp (-(2 * η)) * (1 - 60 / Real.log X) ≤ ∑ p ∈ harperBlock X, ‖w p‖ ^ 2
      ∧ ∑ p ∈ harperBlock X, ‖w p‖ ^ 2 ≤ 1 + 60 / Real.log X := by
  have hrw : ∑ p ∈ harperBlock X, ‖w p‖ ^ 2
      = ∑ p ∈ {p ∈ Finset.Ioc ⌊X ^ (Real.exp 1)⁻¹⌋₊ ⌊X⌋₊ | Nat.Prime p},
          (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [Finset.sum_congr rfl hnorm, harperBlock,
      sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-1 - 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  exact ⟨(sum_prime_block_rpow_bounds_of_le X σ η hX hσ).1,
    sum_prime_block_rpow_le_of_nonneg X σ hX hσ0⟩

/-- **Harper's block is nonempty** once `x ≥ 2^e ≈ 6.6`: Bertrand's postulate puts a prime in
`(n, 2n]` for `n = ⌊x^{1/e}⌋₊`, and the block reaches `2n` because
`x = (x^{1/e})^e ≥ (x^{1/e})² ≥ 2x^{1/e}` whenever `x^{1/e} ≥ 2`.  Only `e ≥ 2` is used. -/
theorem harperBlock_nonempty {x : ℝ} (hx : (2 : ℝ) ^ Real.exp 1 ≤ x) :
    (harperBlock x).Nonempty := by
  obtain ⟨hx0, h2⟩ := pos_and_le_rpow_inv_exp_one (by norm_num) hx
  set t := x ^ (Real.exp 1)⁻¹ with ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  -- the two ends of the block differ by far more than a factor of two
  have hpow : t ^ (Real.exp 1) = x := by
    rw [ht, ← Real.rpow_mul hx0.le, inv_mul_cancel₀ (Real.exp_pos 1).ne', Real.rpow_one]
  have hsq : t ^ (2 : ℝ) = t * t := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hxt : 2 * t ≤ x :=
    calc 2 * t ≤ t * t := by nlinarith
      _ = t ^ (2 : ℝ) := hsq.symm
      _ ≤ t ^ (Real.exp 1) := Real.rpow_le_rpow_of_exponent_le ht1 he
      _ = x := hpow
  -- Bertrand
  have hfl : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
  obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊t⌋₊ (by omega)
  refine ⟨⟨q, hq⟩, ?_⟩
  rw [harperBlock, mem_primesIcoSub]
  have hup : 2 * ⌊t⌋₊ ≤ ⌊x⌋₊ := by
    refine Nat.le_floor ?_
    have hle := Nat.floor_le ht0.le
    push_cast
    linarith
  refine ⟨?_, ?_⟩
  · change ⌊t⌋₊ + 1 ≤ q
    omega
  · change q < ⌊x⌋₊ + 1
    omega

/-- The tilt radius at `Re s = 1/2 + σ` has the same squared norm as Harper's weights,
`‖p^{-s}‖² = p^{-1-2σ}` — so one side condition covers both. -/
lemma norm_sq_prime_cpow_neg (p : Nat.Primes) {s : ℂ} {σ : ℝ} (hres : s.re = 1 / 2 + σ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hres,
    ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0]
  congr 1
  push_cast
  ring

/-! ### How small the weights on a block really are

`RMF.norm_le_of_mem_harperBlock` gives `‖w_p‖ ≤ K` for any `K` whose threshold `(e²/K²)^e` the block
clears.  At `K = e/√(blockScale θ j)` the threshold is `(blockScale θ j)^e`, which is
`blockScale θ (j+1)` exactly, so that value of `K` is free, and it is the true size.

The crude `‖w_p‖ ≤ 1/100` suffices for the moment estimates and for a *positive* variance, but not
for a two-sided one: the second-moment errors (`RMF.abs_blockVar_sub_le`) are
`(40κ + 5κ²)·∑‖w_p‖²`, a `40%` distortion at `κ = 1/100`, which would push `1/(2V)` past the
`A < 9` of the Gaussian window bound (`RMF.rpow_le_exp_neg_sq_div_of_bounds`).  At `j + θ ≥ 3` the
true `κ` is at most `e·e^{-e³/2} ≈ 1.2·10^{-4}`, and the distortion is `0.5%`. -/

/-- The true size of the weights on the `j`-th block: `‖u‖ ≤ e/√(blockScale θ j)` for any `u` of
squared norm `p^{-1-2σ}`, with no hypothesis beyond `|σ|·log(top of block) ≤ 1`. -/
lemma norm_le_of_mem_primeBlockSub {θ σ : ℝ} {j : ℕ}
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ 1)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ j) {u : ℂ}
    (hu : ‖u‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ‖u‖ ≤ Real.exp 1 / √(blockScale θ j) := by
  have hb : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have hs : (0 : ℝ) < √(blockScale θ j) := Real.sqrt_pos.2 hb
  refine norm_le_of_mem_harperBlock (by positivity) hσ ?_ hp hu
  have hsq : (Real.exp 1 / √(blockScale θ j)) ^ 2 = Real.exp 2 / blockScale θ j := by
    rw [div_pow, Real.sq_sqrt hb.le, ← Real.exp_nat_mul]
    norm_num
  rw [hsq, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (Real.exp_pos 2).ne', mul_one,
    blockScale_rpow_exp_one]

/-- **The true weight size on a block, at a general tilt scale**: `‖u‖ ≤ e^η/√(blockScale θ j)`
for `‖u‖² = p^{-1-2σ}` and `|σ|·log(blockScale θ (j+1)) ≤ η`; `RMF.norm_le_of_mem_primeBlockSub`
is `η = 1`.  The threshold check is an equality, since `blockScale θ (j+1) = (blockScale θ j)^e`. -/
lemma norm_le_of_mem_primeBlockSub_of_le {θ σ η : ℝ} {j : ℕ}
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ j) {u : ℂ}
    (hu : ‖u‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ‖u‖ ≤ Real.exp η / √(blockScale θ j) := by
  have hb : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have hs : (0 : ℝ) < √(blockScale θ j) := Real.sqrt_pos.2 hb
  refine norm_le_of_mem_harperBlock_of_le (by positivity) hσ ?_ hp hu
  have hsq : (Real.exp η / √(blockScale θ j)) ^ 2 = Real.exp (2 * η) / blockScale θ j := by
    rw [div_pow, Real.sq_sqrt hb.le, ← Real.exp_nat_mul]
    norm_num
  rw [hsq, div_div_eq_mul_div, mul_comm, mul_div_assoc,
    div_self (Real.exp_pos (2 * η)).ne', mul_one, blockScale_rpow_exp_one]

/-- **The block variance, pinned two-sidedly** — `(1 - ε₀)·S ≤ 2V ≤ (1 + ε₀)·S`, where
`S = ∑_{p∈B}‖w_p‖²` and `ε₀ = 40κ + 5κ²` with `κ` the true weight size on the block.

This is `RMF.abs_blockVar_sub_le` with the errors measured against `κ` rather than against the crude
`1/5`, plus `RMF.coe_blockMatchedVar` to read the left-hand side off `blockMatchedVar`. -/
theorem blockMatchedVar_two_sided (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ} {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 5)
    (hw : ∀ p ∈ B, ‖w p‖ ≤ κ) (ha : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ κ) :
    (1 - (40 * κ + 5 * κ ^ 2)) * (∑ p ∈ B, ‖w p‖ ^ 2)
        ≤ 2 * ((blockMatchedVar X μ y s w B : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVar X μ y s w B : ℝ≥0) : ℝ)
        ≤ (1 + (40 * κ + 5 * κ ^ 2)) * (∑ p ∈ B, ‖w p‖ ^ 2) := by
  have hw5 : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5 := fun p hp => le_trans (hw p hp) hκ
  have ha5 : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := fun p hp => le_trans (ha p hp) hκ
  have hcoe := coe_blockMatchedVar hX y hs hB hw5
  have hbv := abs_sub_le_iff.1 (abs_blockVar_sub_le hX y hs hB hw5 ha5)
  -- the error sum, measured against κ
  have herr : ∑ p ∈ B, (20 * ‖w p‖ ^ 3
        + 5 / 2 * (‖w p‖ ^ 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2))
      ≤ (20 * κ + 5 / 2 * κ ^ 2) * ∑ p ∈ B, ‖w p‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have h1 : ‖w q‖ ^ 3 ≤ κ * ‖w q‖ ^ 2 := by
      nlinarith [norm_nonneg (w q), sq_nonneg ‖w q‖, hw q hq]
    have h2 : ‖((q : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ κ ^ 2 := by
      nlinarith [norm_nonneg (((q : ℕ) : ℂ) ^ (-s)), ha q hq]
    have h3 : ‖w q‖ ^ 2 * ‖((q : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ ‖w q‖ ^ 2 * κ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    nlinarith [h1, h3, sq_nonneg ‖w q‖]
  have hhalf : ∑ p ∈ B, ‖w p‖ ^ 2 / 2 = (1 / 2) * ∑ p ∈ B, ‖w p‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hhalf] at hbv
  rw [hcoe]
  constructor <;> linarith [hbv.1, hbv.2, herr]

/-- The true size of the weights on the `j`-th block, `κ = e/√(blockScale θ j)`. -/
noncomputable def blockWeightSize (θ : ℝ) (j : ℕ) : ℝ := Real.exp 1 / √(blockScale θ j)

lemma blockWeightSize_pos (θ : ℝ) (j : ℕ) : 0 < blockWeightSize θ j := by
  have := Real.sqrt_pos.2 (blockScale_pos θ j)
  unfold blockWeightSize
  positivity

/-- **`κ ≤ 1/1000` on every block with `j + θ ≥ 3`.**

`κ` is doubly exponentially small (at `j + θ = 3` already `e·e^{-e³/2} ≈ 1.2·10^{-4}`), so any fixed
bound holds with room.  `1/1000` is the one the variance needs: it makes the distortion
`40κ + 5κ²` at most `0.041`. -/
lemma blockWeightSize_le {θ : ℝ} {j : ℕ} (hjθ : (3 : ℝ) ≤ (j : ℝ) + θ) :
    blockWeightSize θ j ≤ 1 / 1000 := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hb : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have hpow : ∀ n : ℕ, Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    intro n; rw [← Real.exp_nat_mul]; ring_nf
  -- `1000000 e² ≤ e^{e³} ≤ blockScale θ j`
  have he3 : (19 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, hpow 3]
    calc (19 : ℝ) ≤ (2.7 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 3
  have he16 : (1000000 : ℝ) ≤ Real.exp 14 := by
    rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, hpow 14]
    calc (1000000 : ℝ) ≤ (2.7 : ℝ) ^ (14 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (14 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 14
  have hlog : Real.log (1000000 * Real.exp 2) ≤ Real.exp 3 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 2), Real.log_exp]
    have h1 : Real.log 1000000 ≤ 14 := (Real.log_le_iff_le_exp (by norm_num)).2 he16
    linarith
  have hkey : 1000000 * Real.exp 2 ≤ blockScale θ j := by
    rw [blockScale]
    refine le_trans ((Real.log_le_iff_le_exp (by positivity)).1 hlog) ?_
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 hjθ)
  -- hence `√(blockScale θ j) ≥ 400 e`
  have hsq : (1000 * Real.exp 1) ^ 2 ≤ blockScale θ j := by
    have hv : (1000 * Real.exp 1) ^ 2 = 1000000 * Real.exp 2 := by
      rw [mul_pow, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, hpow 2]; norm_num
    rw [hv]; exact hkey
  have hs : 1000 * Real.exp 1 ≤ √(blockScale θ j) := by
    calc 1000 * Real.exp 1 = √((1000 * Real.exp 1) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(blockScale θ j) := Real.sqrt_le_sqrt hsq
  unfold blockWeightSize
  rw [div_le_iff₀ (Real.sqrt_pos.2 hb)]
  linarith

/-- **`κ ≤ 10^{-6}` on every block with `j + θ ≥ 4`.**  `RMF.blockWeightSize_le`'s `1/1000` is sized
for the one-point distortion `40κ + 5κ²`; the two-point one is `1000κ + 25992κ²`
(`RMF.blockMatchedVar₂_bounds`), which at `κ = 1/1000` is `≈ 1` and says nothing.  The condition
is `log(10^{12}e²) ≤ e^{j+θ}`, i.e. `30 ≤ e^{j+θ}`, and `e⁴ ≈ 54.6`. -/
lemma blockWeightSize_le_millionth {θ : ℝ} {j : ℕ} (hjθ : (4 : ℝ) ≤ (j : ℝ) + θ) :
    blockWeightSize θ j ≤ 1 / 1000000 := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hb : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have hpow : ∀ n : ℕ, Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    intro n; rw [← Real.exp_nat_mul]; ring_nf
  have he14 : (1000000 : ℝ) ≤ Real.exp 14 := by
    rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, hpow 14]
    calc (1000000 : ℝ) ≤ (2.7 : ℝ) ^ (14 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (14 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 14
  have he4 : (30 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, hpow 4]
    calc (30 : ℝ) ≤ (2.7 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 4
  -- `\log(10^{12} e²) ≤ 30 ≤ e⁴ ≤ e^{j+θ}`
  have hlog : Real.log (1000000000000 * Real.exp 2) ≤ Real.exp ((j : ℝ) + θ) := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 2), Real.log_exp]
    have h28 : Real.log 1000000000000 ≤ 28 := by
      refine (Real.log_le_iff_le_exp (by norm_num)).2 ?_
      have hsplit : Real.exp 14 * Real.exp 14 = Real.exp 28 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [he14, hsplit, Real.exp_pos (14 : ℝ)]
    have hmono : Real.exp 4 ≤ Real.exp ((j : ℝ) + θ) := Real.exp_le_exp.2 hjθ
    linarith
  have hkey : 1000000000000 * Real.exp 2 ≤ blockScale θ j := by
    rw [blockScale]
    exact (Real.log_le_iff_le_exp (by positivity)).1 hlog
  have hsq : (1000000 * Real.exp 1) ^ 2 ≤ blockScale θ j := by
    have hv : (1000000 * Real.exp 1) ^ 2 = 1000000000000 * Real.exp 2 := by
      rw [mul_pow, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, hpow 2]; norm_num
    rw [hv]; exact hkey
  have hs : 1000000 * Real.exp 1 ≤ √(blockScale θ j) := by
    calc 1000000 * Real.exp 1 = √((1000000 * Real.exp 1) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(blockScale θ j) := Real.sqrt_le_sqrt hsq
  unfold blockWeightSize
  rw [div_le_iff₀ (Real.sqrt_pos.2 hb)]
  linarith

/-- `log x_j = e^{j+1+θ} ≥ 4` from `j ≥ 3` — used both to bound `|σ|` and to clear the envelope. -/
lemma four_le_log_blockScale {θ : ℝ} {j : ℕ} (hjθ : (3 : ℝ) ≤ (j : ℝ) + θ) :
    (4 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by
  rw [log_blockScale]
  have hle : (4 : ℝ) ≤ (j : ℝ) + 1 + θ := by linarith
  calc (4 : ℝ) ≤ (j : ℝ) + 1 + θ := hle
    _ ≤ Real.exp ((j : ℝ) + 1 + θ) := by linarith [Real.add_one_le_exp ((j : ℝ) + 1 + θ)]
    _ = Real.exp (((j + 1 : ℕ) : ℝ) + θ) := by push_cast; ring_nf

/-- On a block with `j + θ ≥ 3`, `|σ| ≤ 1/4`, hence `Re s = 1/2 + σ > 0`: the positivity of `Re s`
that every tilt statement needs is not a separate hypothesis. -/
lemma re_pos_of_block {θ σ : ℝ} {j : ℕ} {s : ℂ} (hjθ : (3 : ℝ) ≤ (j : ℝ) + θ)
    (hres : s.re = 1 / 2 + σ) (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ 1) :
    0 < s.re := by
  have habs : |σ| ≤ 1 / 4 := by
    nlinarith [abs_nonneg σ, hσ, four_le_log_blockScale hjθ]
  rw [hres]; linarith [neg_abs_le σ]

/-- **`Re s > 0` at any tilt scale**, from `14 + 2η ≤ e^{j+θ}` and `|σ|·log x_{j+1} ≤ η` (the
analogue of `RMF.re_pos_of_block`).  `log x_{j+1} = e^{j+1+θ}` grows exponentially in `j + θ`
while the tilt enters linearly, so this one hypothesis, shared with
`RMF.blockWeightSize_le_of_le`, gives `|σ| ≤ 1/(2e) < 2/5`; `θ ≥ log(14 + 2E₀)` supplies it for
every `η ≤ E₀` (`RMF.scale_cond_of_le`). -/
lemma re_pos_of_block_of_le {θ σ η : ℝ} {j : ℕ} {s : ℂ}
    (hres : s.re = 1 / 2 + σ) (hsc : 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ η) :
    0 < s.re := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hE0 : (0 : ℝ) < Real.exp ((j : ℝ) + θ) := Real.exp_pos _
  have hL : Real.log (blockScale θ (j + 1)) = Real.exp 1 * Real.exp ((j : ℝ) + θ) := by
    rw [log_blockScale, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hLge : (37.8 : ℝ) + 5.4 * η ≤ Real.log (blockScale θ (j + 1)) := by
    rw [hL]
    calc (37.8 : ℝ) + 5.4 * η = 2.7 * (14 + 2 * η) := by ring
      _ ≤ 2.7 * Real.exp ((j : ℝ) + θ) := by linarith
      _ ≤ Real.exp 1 * Real.exp ((j : ℝ) + θ) := mul_le_mul_of_nonneg_right he.le hE0.le
  have hL0 : (0 : ℝ) < Real.log (blockScale θ (j + 1)) := by rw [hL]; positivity
  have hη0 : (0 : ℝ) ≤ η := le_trans (mul_nonneg (abs_nonneg σ) hL0.le) hσ
  have hkey : |σ| * (37.8 + 5.4 * η) ≤ η :=
    le_trans (mul_le_mul_of_nonneg_left hLge (abs_nonneg σ)) hσ
  have habs : |σ| ≤ 2 / 5 := by nlinarith [abs_nonneg σ, hη0, hkey]
  rw [hres]; linarith [neg_abs_le σ]

/-- **The block weight size at any tilt scale**: `e^η/√(blockScale θ j) ≤ 1/1000` once
`14 + 2η ≤ e^{j+θ}` (the analogue of `RMF.blockWeightSize_le`).  Since
`blockScale θ j = exp(e^{j+θ})`, the sharp condition is `log(10⁶) + 2η ≤ e^{j+θ}`, with
`log(10⁶) ≈ 13.8155`; the hypothesis rounds it up and does not cap `η`. -/
lemma blockWeightSize_le_of_le {θ η : ℝ} {j : ℕ}
    (hsc : 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ)) :
    Real.exp η / √(blockScale θ j) ≤ 1 / 1000 := by
  have hb0 : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have he1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h14 : (1000000 : ℝ) ≤ Real.exp 14 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 14)
      (by norm_num) he1.le (by norm_num)
  have hprod : (1000 * Real.exp η) ^ 2 ≤ blockScale θ j := by
    have hsq : (1000 * Real.exp η) ^ 2 = 1000000 * Real.exp (2 * η) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [hsq, blockScale]
    calc (1000000 : ℝ) * Real.exp (2 * η)
        ≤ Real.exp 14 * Real.exp (2 * η) := mul_le_mul_of_nonneg_right h14 (Real.exp_pos _).le
      _ = Real.exp (14 + 2 * η) := by rw [← Real.exp_add]
      _ ≤ Real.exp (Real.exp ((j : ℝ) + θ)) := Real.exp_le_exp.2 hsc
  have hle : 1000 * Real.exp η ≤ √(blockScale θ j) :=
    (Real.le_sqrt (by positivity) hb0.le).2 hprod
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hb0) (by norm_num)]
  linarith

/-- **The scale condition at every block, from the offset**: `η ≤ E` and `14 + 2E ≤ e^θ` give
`14 + 2η ≤ e^{j+θ}` for every `j`.  This is the only condition `RMF.re_pos_of_block_of_le` and
`RMF.blockWeightSize_le_of_le` place on the tilt scale. -/
lemma scale_cond_of_le {θ η E : ℝ} {j : ℕ} (hηE : η ≤ E) (hθ : 14 + 2 * E ≤ Real.exp θ) :
    14 + 2 * η ≤ Real.exp ((j : ℝ) + θ) := by
  have hjθ : Real.exp θ ≤ Real.exp ((j : ℝ) + θ) :=
    Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) j])
  linarith

/-- **The block variance, two-sided, bottom up**:
`(1 - ε₀)·e^{-2}(1 - 60/log x_{j+1}) ≤ 2V ≤ (1 + ε₀)·e²(1 + 60/log x_{j+1})` with
`ε₀ = 40κ + 5κ²`, `κ = RMF.blockWeightSize θ j`.  `ε₀`, from `RMF.abs_blockVar_sub_le`, is doubly
exponentially small in `j`; the Mertens term `60/e^{j+1+θ}` is only singly so, and decides whether
`1/(2V)` clears the `A < 9` of `RMF.rpow_le_exp_neg_sq_div_of_bounds`. -/
theorem blockMatchedVar_bounds (hX : IsSteinhausPrimeValues X μ)
      (θ σ : ℝ) (j : ℕ) (s : ℂ) (w : Nat.Primes → ℂ)
      (hjθ : (3 : ℝ) ≤ (j : ℝ) + θ) (hres : s.re = 1 / 2 + σ)
      (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ 1)
      (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
      (1 - (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2))
            * (Real.exp (-2) * (1 - 60 / Real.log (blockScale θ (j + 1))))
          ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
              (primeBlockSub θ j) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
              (primeBlockSub θ j) : ℝ≥0) : ℝ)
          ≤ (1 + (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2))
            * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1)))) := by
  set κ := blockWeightSize θ j with hκdef
  have hκ0 : (0 : ℝ) < κ := blockWeightSize_pos θ j
  have hκ4 : κ ≤ 1 / 1000 := blockWeightSize_le hjθ
  have hκ5 : κ ≤ 1 / 5 := by linarith
  -- the weights and the tilt radius are both at most κ on the block
  have hw : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (hwn p hp)
  have ha : ∀ p ∈ primeBlockSub θ j, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ κ := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ hp (norm_sq_prime_cpow_neg p hres)
  -- `0 < Re s`, as in the block comparison
  have hsre : 0 < s.re := re_pos_of_block hjθ hres hσ
  -- the variance against the weight sum
  obtain ⟨hlo, hhi⟩ := blockMatchedVar_two_sided hX (⌊blockScale θ (j + 1)⌋₊ + 1) hsre
    (harperBlock_subset _) hκ0.le hκ5 hw ha
  -- the weight sum against block Mertens
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (j + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  obtain ⟨hSlo, hShi⟩ := sum_norm_sq_harperBlock_bounds (blockScale θ (j + 1)) σ w hbig hσ hwn
  have hfac0 : (0 : ℝ) ≤ 1 - (40 * κ + 5 * κ ^ 2) := by nlinarith
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left hSlo hfac0) hlo
  · refine le_trans hhi (mul_le_mul_of_nonneg_left hShi (by nlinarith))

/-- **The variance bracket, as arithmetic**: `κ ≤ 1/1000` bounds `ε₀ = 40κ + 5κ²` by `0.041` and
`L ≥ 7000` bounds `60/L` by `0.0086`, so `e^{-2η}/2 ≤ 2V ≤ 9`.  The lower end is kept at the scale
`η` rather than a numeral because the lower reduction tilts at `η = 4V` (its `V`, not this
variance), and that `V` is chosen in `RMF.exists_le_integral_rpow_normalisedSum` from other
constants. -/
lemma var_bracket_of_bounds {κ Lx V η : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 1000)
    (hL : (7000 : ℝ) ≤ Lx)
    (hlo : (1 - (40 * κ + 5 * κ ^ 2)) * (Real.exp (-(2 * η)) * (1 - 60 / Lx)) ≤ 2 * V)
    (hhi : 2 * V ≤ (1 + (40 * κ + 5 * κ ^ 2)) * (1 + 60 / Lx)) :
    Real.exp (-(2 * η)) / 2 ≤ 2 * V ∧ 2 * V ≤ 9 := by
  have hL0 : (0 : ℝ) < Lx := by linarith
  have hd0 : (0 : ℝ) ≤ 60 / Lx := by positivity
  have hd : (60 : ℝ) / Lx ≤ 0.0086 := by rw [div_le_iff₀ hL0]; linarith
  have hfac1 : (0.959 : ℝ) ≤ 1 - (40 * κ + 5 * κ ^ 2) := by nlinarith
  have hfac1u : 1 + (40 * κ + 5 * κ ^ 2) ≤ 1.041 := by nlinarith
  have hem0 : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
  refine ⟨?_, ?_⟩
  · have h1 : (0.9914 : ℝ) ≤ 1 - 60 / Lx := by linarith
    have hinner : (0.9914 : ℝ) * Real.exp (-(2 * η))
        ≤ Real.exp (-(2 * η)) * (1 - 60 / Lx) := by nlinarith [hem0, h1]
    have hlow2 : (0.959 : ℝ) * (0.9914 * Real.exp (-(2 * η)))
        ≤ (1 - (40 * κ + 5 * κ ^ 2)) * (Real.exp (-(2 * η)) * (1 - 60 / Lx)) :=
      mul_le_mul hfac1 hinner (by positivity) (by linarith)
    linarith
  · have h1u : (1 : ℝ) + 60 / Lx ≤ 1.0086 := by linarith
    have hmul : (1 + (40 * κ + 5 * κ ^ 2)) * (1 + 60 / Lx) ≤ 1.041 * 1.0086 :=
      mul_le_mul hfac1u h1u (by linarith) (by norm_num)
    linarith

/-- **The block variance, two-sided at a general tilt scale**, with the weight size `κ` a
parameter: the analogue of `RMF.blockMatchedVar_bounds`.  At a general scale the weight size is
`e^η/√(blockScale θ j)` rather than `e/√(blockScale θ j)`; keeping `κ` abstract separates the
distortion `ε₀ = 40κ + 5κ²` of `RMF.abs_blockVar_sub_le` from the tilt. -/
theorem blockMatchedVar_bounds_of_le (hX : IsSteinhausPrimeValues X μ)
    {θ σ η κ : ℝ} {j : ℕ} {s : ℂ} {w : Nat.Primes → ℂ}
    (hjθ : (3 : ℝ) ≤ (j : ℝ) + θ) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hsc : 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 1000)
    (hw : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ κ)
    (ha : ∀ p ∈ primeBlockSub θ j, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ κ)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    (1 - (40 * κ + 5 * κ ^ 2))
          * (Real.exp (-(2 * η)) * (1 - 60 / Real.log (blockScale θ (j + 1))))
        ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
            (primeBlockSub θ j) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
            (primeBlockSub θ j) : ℝ≥0) : ℝ)
        ≤ (1 + (40 * κ + 5 * κ ^ 2)) * (1 + 60 / Real.log (blockScale θ (j + 1))) := by
  have hsre : 0 < s.re := re_pos_of_block_of_le hres hsc hσ
  obtain ⟨hlo, hhi⟩ := blockMatchedVar_two_sided hX (⌊blockScale θ (j + 1)⌋₊ + 1) hsre
    (harperBlock_subset _) hκ0 (by linarith) hw ha
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (j + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  obtain ⟨hSlo, hShi⟩ :=
    sum_norm_sq_harperBlock_bounds_of_le (blockScale θ (j + 1)) σ η w hbig hσ0 hσ hwn
  have hfac0 : (0 : ℝ) ≤ 1 - (40 * κ + 5 * κ ^ 2) := by nlinarith
  exact ⟨le_trans (mul_le_mul_of_nonneg_left hSlo hfac0) hlo,
    le_trans hhi (mul_le_mul_of_nonneg_left hShi (by nlinarith))⟩

/-- **The block variance bracketed at a general tilt scale**: `e^{-2η}/2 ≤ 2V ≤ 9` on every block
with `j + θ ≥ 8`, for `σ ≥ 0`, `14 + 2η ≤ e^{j+θ}`, `|σ|·log x_{j+1} ≤ η` and
`‖w_p‖² = p^{-1-2σ}`; the analogue of `RMF.blockMatchedVar_concrete`.  The lower end is the tilt
thinning the block, the `A` that `RMF.exists_thr_direct` pays for in `θ`; the upper end does not
move, since `σ ≥ 0` costs the upper direction nothing. -/
theorem blockMatchedVar_concrete_of_le (hX : IsSteinhausPrimeValues X μ)
    (θ σ η : ℝ) (j : ℕ) (s : ℂ) (w : Nat.Primes → ℂ)
    (hjθ : (8 : ℝ) ≤ (j : ℝ) + θ) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hsc : 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    Real.exp (-(2 * η)) / 2 ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
        (primeBlockSub θ j) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
        (primeBlockSub θ j) : ℝ≥0) : ℝ) ≤ 9 := by
  have hj3 : (3 : ℝ) ≤ (j : ℝ) + θ := by linarith
  have hb0 : (0 : ℝ) < blockScale θ j := blockScale_pos θ j
  have hκ0 : (0 : ℝ) ≤ Real.exp η / √(blockScale θ j) := by
    have := Real.sqrt_pos.2 hb0
    positivity
  have hκ : Real.exp η / √(blockScale θ j) ≤ 1 / 1000 := blockWeightSize_le_of_le hsc
  have hw : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ Real.exp η / √(blockScale θ j) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (hwn p hp)
  have ha : ∀ p ∈ primeBlockSub θ j,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp η / √(blockScale θ j) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (norm_sq_prime_cpow_neg p hres)
  obtain ⟨hlo, hhi⟩ := blockMatchedVar_bounds_of_le hX hj3 hres hσ0 hsc hσ hκ0 hκ hw ha hwn
  -- the Mertens term at `j + θ ≥ 8`
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by
    rw [log_blockScale]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
      _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((j + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  exact var_bracket_of_bounds hκ0 hκ hL hlo hhi

/-- **The Gaussian window bound at a directly supplied threshold, at a general tilt scale**: mass
at least `h·x_{j+1}^{-τ}`, given `hthr : A(M + |m_B| + h)² + log(πB)/2 ≤ τ·log x_{j+1}`.  Any `A`
is admissible, so the tilt is not capped (Harper's envelope costs `A < 9`, hence `η < log 3`), and
`RMF.exists_thr_direct` supplies `hthr`.  The side conditions are the `_of_le` forms, at
`j + θ ≥ 5`. -/
theorem le_toReal_measure_Ioc_blockGaussian_of_thr (hX : IsSteinhausPrimeValues X μ)
    {θ σ η : ℝ} {j : ℕ} {s : ℂ} {w : Nat.Primes → ℂ} {A Bb h M τ : ℝ}
    (hjθ : (5 : ℝ) ≤ (j : ℝ) + θ) (hres : s.re = 1 / 2 + σ)
    (hsc : 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (hh : 0 ≤ h) (hA : 0 < A) (hB : 0 < Bb)
    (hV₁ : 1 / A ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
      (primeBlockSub θ j) : ℝ≥0) : ℝ))
    (hV₂ : 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
      (primeBlockSub θ j) : ℝ≥0) : ℝ) ≤ Bb)
    (hthr : A * (M + |blockMean X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w (primeBlockSub θ j)| + h) ^ 2
        + Real.log (Real.pi * Bb) / 2
      ≤ τ * Real.log (blockScale θ (j + 1))) :
    ∀ c, |c| ≤ M → h * blockScale θ (j + 1) ^ (-τ)
      ≤ (gaussianReal (blockMean X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w (primeBlockSub θ j))
          (blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w (primeBlockSub θ j))
          (Set.Ioc c (c + h))).toReal := by
  have hsre : 0 < s.re := re_pos_of_block_of_le hres hsc hσ
  have hκ' : Real.exp η / √(blockScale θ j) ≤ 1 / 1000 := blockWeightSize_le_of_le hsc
  -- the weights are small on the block, now at the general scale
  have hw100 : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ≤ 1 / 100 := fun p hp =>
    le_trans (norm_le_of_mem_primeBlockSub_of_le hσ hp (hwn p hp)) (by linarith)
  have ha5 : ∀ p ∈ primeBlockSub θ j, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := fun p hp =>
    le_trans (norm_le_of_mem_primeBlockSub_of_le hσ hp (norm_sq_prime_cpow_neg p hres))
      (by linarith)
  -- the block is nonempty, so the variance is nonzero
  have hne : (primeBlockSub θ j).Nonempty := by
    refine harperBlock_nonempty ?_
    have h2e : (2 : ℝ) ^ Real.exp 1 ≤ Real.exp 2 := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine Real.exp_le_exp.2 ?_
      nlinarith [Real.log_two_lt_d9, Real.exp_one_lt_d9,
        Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.exp_pos (1 : ℝ)]
    refine le_trans h2e ?_
    rw [blockScale]
    refine Real.exp_le_exp.2 ?_
    calc (2 : ℝ) ≤ (j : ℝ) + 1 + θ := by linarith
      _ ≤ Real.exp ((j : ℝ) + 1 + θ) := by linarith [Real.add_one_le_exp ((j : ℝ) + 1 + θ)]
      _ = Real.exp (((j + 1 : ℕ) : ℝ) + θ) := by push_cast; ring_nf
  have hne' : ∃ p ∈ primeBlockSub θ j, w p ≠ 0 := by
    obtain ⟨r, hr⟩ := hne
    refine ⟨r, hr, ?_⟩
    have hpos : (0 : ℝ) < ((r : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast r.2.pos) _
    have hnz : ‖w r‖ ^ 2 ≠ 0 := by rw [hwn r hr]; exact hpos.ne'
    intro h0
    rw [h0, norm_zero] at hnz
    norm_num at hnz
  have hv : blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w (primeBlockSub θ j) ≠ 0 :=
    (blockMatchedVar_pos hX _ hsre (harperBlock_subset _) hw100 ha5 hne').ne'
  have hx1 : (1 : ℝ) ≤ blockScale θ (j + 1) := by
    rw [blockScale]; exact Real.one_le_exp (Real.exp_pos _).le
  intro c hc
  exact le_toReal_measure_Ioc_gaussianReal_of_thr hv hh hA hB hV₁ hV₂ hx1 hc hthr

/-- **The block variance bracketed by numerals**: `1/8 ≤ 2V ≤ 9` on every block with `j + θ ≥ 8`,
`|σ|·log x_{j+1} ≤ 1` and `‖w_p‖² = p^{-1-2σ}`.  With `κ ≤ 1/1000` the distortion is at most
`0.041`, and the Mertens term is at most `60/7000`, so `2V ≥ 0.959·e^{-2}·0.9914 ≥ 0.1283` and
`2V ≤ 1.041·e²·1.0086 ≤ 7.76`.  So `A = 8`, `B = 9` are admissible in
`RMF.rpow_le_exp_neg_sq_div_of_bounds`. -/
theorem blockMatchedVar_concrete (hX : IsSteinhausPrimeValues X μ)
    (θ σ : ℝ) (j : ℕ) (s : ℂ) (w : Nat.Primes → ℂ)
    (hjθ : (8 : ℝ) ≤ (j : ℝ) + θ) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (j + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ j, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    1 / 8 ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
        (primeBlockSub θ j) : ℝ≥0) : ℝ)
      ∧ 2 * ((blockMatchedVar X μ (⌊blockScale θ (j + 1)⌋₊ + 1) s w
        (primeBlockSub θ j) : ℝ≥0) : ℝ) ≤ 9 := by
  have hj3 : (3 : ℝ) ≤ (j : ℝ) + θ := by linarith
  obtain ⟨hlo, hhi⟩ := blockMatchedVar_bounds hX θ σ j s w hj3 hres hσ hwn
  have hκ := blockWeightSize_le hj3
  have hκ0 := blockWeightSize_pos θ j
  -- the distortion from the second-moment errors
  have hfac1 : (0.959 : ℝ) ≤ 1 - (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2) := by
    nlinarith
  have hfac1' : 1 - (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2) ≤ 1 := by nlinarith
  have hfac1u : 1 + (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2) ≤ 1.041 := by
    nlinarith
  -- the Mertens term at `j ≥ 8`
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
  -- the exponentials
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
    have hB : (0.959 : ℝ) * (0.135 * 0.9914)
        ≤ (1 - (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2))
          * (Real.exp (-2) * (1 - 60 / Real.log (blockScale θ (j + 1)))) :=
      mul_le_mul hfac1 hA (by norm_num) (by linarith)
    nlinarith [hlo, hB]
  · have hA : Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1)))
        ≤ (7.39 : ℝ) * 1.0086 :=
      mul_le_mul he2 hfac2u (by linarith) (by norm_num)
    have hB : (1 + (40 * blockWeightSize θ j + 5 * blockWeightSize θ j ^ 2))
          * (Real.exp 2 * (1 + 60 / Real.log (blockScale θ (j + 1))))
        ≤ (1.041 : ℝ) * (7.39 * 1.0086) :=
      mul_le_mul hfac1u hA (by positivity) (by norm_num)
    nlinarith [hhi, hB]

/-- **The threshold of the Gaussian window bound, on every block with `j + θ ≥ 14`.**  At `A = 8`,
`B = 9` (`RMF.blockMatchedVar_concrete`) and envelope constant `Cₑ = 2`, the `hthr` of
`RMF.rpow_le_exp_neg_sq_div_of_bounds` reads
`0.8·√(log x_{j+1}) + 32 + ½log(9π) ≤ log x_{j+1}/1600`, which needs `√(log x_{j+1}) ≥ 1321`, i.e.
`j + 1 + θ ≥ 14.4`.  The envelope of `RMF.proposition5_lower` needs a larger offset. -/
lemma hthr_of_fourteen_le {θ : ℝ} {j : ℕ} (hjθ : (14 : ℝ) ≤ (j : ℝ) + θ) :
    (8 : ℝ) / 20 * 2 * √(Real.log (blockScale θ (j + 1))) + 8 * 2 ^ 2
        + Real.log (Real.pi * 9) / 2
      ≤ (9 - 8) / 1600 * Real.log (blockScale θ (j + 1)) := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  -- `log x_j ≥ e^15 ≥ 2.7^15 ≥ 2890000 = 1700²`
  have hL : (2890000 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by
    rw [log_blockScale]
    calc (2890000 : ℝ) ≤ (2.7 : ℝ) ^ (15 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (15 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 15
      _ = Real.exp ((15 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((j + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hL0 : (0 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by linarith
  have hsq : √(Real.log (blockScale θ (j + 1))) ^ 2 = Real.log (blockScale θ (j + 1)) :=
    Real.sq_sqrt hL0
  have ht : (1700 : ℝ) ≤ √(Real.log (blockScale θ (j + 1))) := by
    calc (1700 : ℝ) = √((1700 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(Real.log (blockScale θ (j + 1))) := by
          refine Real.sqrt_le_sqrt ?_
          rw [show ((1700 : ℝ)) ^ 2 = 2890000 by norm_num]
          exact hL
  -- `log (9π) ≤ 4`, crudely
  have hpi : Real.log (Real.pi * 9) ≤ 4 := by
    have h29 : Real.pi * 9 ≤ 36 := by nlinarith [Real.pi_le_four]
    have he4 : (36 : ℝ) ≤ Real.exp 4 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 4)
        (by norm_num) he.le (by norm_num)
    exact (Real.log_le_iff_le_exp (by positivity)).2 (le_trans h29 he4)
  nlinarith [ht, hsq, hpi]

/-- `log(9π) ≤ 4`, crudely — the normalisation term of the direct threshold. -/
lemma log_pi_nine_le : Real.log (Real.pi * 9) ≤ 4 := by
  have h29 : Real.pi * 9 ≤ 36 := by nlinarith [Real.pi_le_four]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he4 : (36 : ℝ) ≤ Real.exp 4 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 4)
      (by norm_num) he1.le (by norm_num)
  exact (Real.log_le_iff_le_exp (by positivity)).2 (le_trans h29 he4)

/-- **The two-point threshold**, the second coordinate's counterpart to `RMF.hthr_of_fourteen_le`:
slope `1/32` rather than `1/40` (the shear), `A = 9`, envelope constant `3`, and exponent `1/100`
rather than `9/1600`.  The surplus `1/100 - 9/1024 = 31/25600` is about a fifth of the one-point
`1/1600`, so the threshold is again `j + θ ≥ 14`, with less room (`3499` against `2952` at
`√(log x_{j+1}) ≥ 1700`). -/
lemma hthr₂_of_fourteen_le {θ : ℝ} {j : ℕ} (hjθ : (14 : ℝ) ≤ (j : ℝ) + θ) :
    2 * 9 * (1 / 32 : ℝ) * 3 * √(Real.log (blockScale θ (j + 1))) + 9 * 3 ^ 2
        + Real.log (Real.pi * 9) / 2
      ≤ (1 / 100 - 9 * (1 / 32 : ℝ) ^ 2) * Real.log (blockScale θ (j + 1)) := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hL : (2890000 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by
    rw [log_blockScale]
    calc (2890000 : ℝ) ≤ (2.7 : ℝ) ^ (15 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (15 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 15
      _ = Real.exp ((15 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((j + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hL0 : (0 : ℝ) ≤ Real.log (blockScale θ (j + 1)) := by linarith
  have hsq : √(Real.log (blockScale θ (j + 1))) ^ 2 = Real.log (blockScale θ (j + 1)) :=
    Real.sq_sqrt hL0
  have ht : (1700 : ℝ) ≤ √(Real.log (blockScale θ (j + 1))) := by
    calc (1700 : ℝ) = √((1700 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(Real.log (blockScale θ (j + 1))) := by
          refine Real.sqrt_le_sqrt ?_
          rw [show ((1700 : ℝ)) ^ 2 = 2890000 by norm_num]
          exact hL
  have hpi : Real.log (Real.pi * 9) ≤ 4 := log_pi_nine_le
  nlinarith [ht, hsq, hpi,
    mul_nonneg (by linarith : (0 : ℝ) ≤ √(Real.log (blockScale θ (j + 1))) - 1700)
      (by linarith : (0 : ℝ) ≤ √(Real.log (blockScale θ (j + 1))) + 48)]

/-- `(1+j)² ≤ 4e^{1+j}` — the step that makes the direct threshold uniform in the block index.

The barrier envelope grows *linearly* in `j` while `log x_j = e^{j+1+θ}` grows exponentially, so the
threshold binds at the bottom of the range and not at the top.  This is the inequality that says
so, and `4` is `2²` from `t ≤ e^t` at `t = (1+j)/2`. -/
lemma sq_succ_le_exp (j : ℕ) : (1 + (j : ℝ)) ^ 2 ≤ 4 * Real.exp (1 + (j : ℝ)) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have ht0 : (0 : ℝ) ≤ (1 + (j : ℝ)) / 2 := by linarith
  have ht : (1 + (j : ℝ)) / 2 ≤ Real.exp ((1 + (j : ℝ)) / 2) := by
    linarith [Real.add_one_le_exp ((1 + (j : ℝ)) / 2)]
  have hee : Real.exp ((1 + (j : ℝ)) / 2) ^ 2 = Real.exp (1 + (j : ℝ)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hp := pow_le_pow_left₀ ht0 ht 2
  rw [hee] at hp
  nlinarith

/-- **The direct threshold, with the envelope in product form `S·(1+j)`**: `(1+j)² ≤ 4e^{1+j}`,
`log(9π)/2 ≤ 2e^{1+j}` and `4 + 2 ≤ 5` once `AS² ≥ 2` reduce it to `5AS² ≤ τe^θ`. -/
lemma thr_direct_aux {A S τ θ : ℝ} {j : ℕ} (hA : 1 ≤ A) (hS : (7 : ℝ) ≤ S)
    (hθ : 5 * A * S ^ 2 ≤ τ * Real.exp θ) :
    A * (S * (1 + (j : ℝ))) ^ 2 + Real.log (Real.pi * 9) / 2
      ≤ τ * Real.log (blockScale θ (j + 1)) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hE0 : (0 : ℝ) < Real.exp (1 + (j : ℝ)) := Real.exp_pos _
  have hE1 : (1 : ℝ) ≤ Real.exp (1 + (j : ℝ)) := Real.one_le_exp (by linarith)
  have hS2 : (49 : ℝ) ≤ S ^ 2 := by nlinarith
  have hAS : (2 : ℝ) ≤ A * S ^ 2 := by nlinarith
  have hAS0 : (0 : ℝ) ≤ A * S ^ 2 := by linarith
  have hlogb : Real.log (blockScale θ (j + 1)) = Real.exp (1 + (j : ℝ)) * Real.exp θ := by
    rw [log_blockScale, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hlogb]
  have hstep : A * (S * (1 + (j : ℝ))) ^ 2 ≤ A * S ^ 2 * (4 * Real.exp (1 + (j : ℝ))) := by
    have hre : A * (S * (1 + (j : ℝ))) ^ 2 = A * S ^ 2 * (1 + (j : ℝ)) ^ 2 := by ring
    rw [hre]
    exact mul_le_mul_of_nonneg_left (sq_succ_le_exp j) hAS0
  have hlog2 : Real.log (Real.pi * 9) / 2 ≤ 2 * Real.exp (1 + (j : ℝ)) := by
    linarith [log_pi_nine_le]
  have hfive : A * S ^ 2 * (4 * Real.exp (1 + (j : ℝ))) + 2 * Real.exp (1 + (j : ℝ))
      ≤ 5 * A * S ^ 2 * Real.exp (1 + (j : ℝ)) := by
    nlinarith [hE0, hAS]
  have hlast : 5 * A * S ^ 2 * Real.exp (1 + (j : ℝ))
      ≤ τ * Real.exp θ * Real.exp (1 + (j : ℝ)) := mul_le_mul_of_nonneg_right hθ hE0.le
  nlinarith [hstep, hlog2, hfive, hlast]

/-- **The price of a large `A`**: `5A(a + B + e² + h)² ≤ τe^θ` gives the direct threshold
`A(a + Bj + e² + h)² + log(9π)/2 ≤ τ·log x_{j+1}` of `RMF.rpow_le_exp_neg_sq_div_of_thr` at every
`j`, with no cap on `A` (the proxy threshold `RMF.hthr_of_fourteen_le` needs `A < 9`, which caps
the tilt at `η < log 3`).  The envelope `a + Bj` is linear against `log x_{j+1} = e^{j+1+θ}`, so
the binding case is `j` small and a large `A` costs a larger `θ`, which `RMF.exists_thr_direct`
pays. -/
lemma thr_direct_of_offset {θ a Bs h A τ : ℝ} {j : ℕ}
    (hA : 1 ≤ A) (ha : 0 ≤ a) (hB : 0 < Bs) (hh : 0 ≤ h)
    (hθ : 5 * A * (a + Bs + Real.exp 2 + h) ^ 2 ≤ τ * Real.exp θ) :
    A * (a + Bs * j + Real.exp 2 + h) ^ 2 + Real.log (Real.pi * 9) / 2
      ≤ τ * Real.log (blockScale θ (j + 1)) := by
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]; nlinarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hS7 : (7 : ℝ) ≤ a + Bs + Real.exp 2 + h := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hprod : Bs * (j : ℝ) ≤ (a + Bs + Real.exp 2 + h) * (j : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hj0
  have hlin : a + Bs * j + Real.exp 2 + h ≤ (a + Bs + Real.exp 2 + h) * (1 + (j : ℝ)) := by
    have hre : (a + Bs + Real.exp 2 + h) * (1 + (j : ℝ))
        = (a + Bs + Real.exp 2 + h) + (a + Bs + Real.exp 2 + h) * (j : ℝ) := by ring
    rw [hre]
    linarith
  have hlin0 : (0 : ℝ) ≤ a + Bs * j + Real.exp 2 + h := by
    have := mul_nonneg hB.le hj0
    linarith
  have hsq : (a + Bs * j + Real.exp 2 + h) ^ 2
      ≤ ((a + Bs + Real.exp 2 + h) * (1 + (j : ℝ))) ^ 2 := pow_le_pow_left₀ hlin0 hlin 2
  have haux := thr_direct_aux (S := a + Bs + Real.exp 2 + h) (j := j) hA hS7 hθ
  have hmono : A * (a + Bs * j + Real.exp 2 + h) ^ 2
      ≤ A * ((a + Bs + Real.exp 2 + h) * (1 + (j : ℝ))) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hA0.le
  linarith

/-- **The direct threshold at any constants, with `θ` existential**: for `A ≥ 1`, `a, h ≥ 0` and
`B, τ > 0` there is `θ₀` such that the threshold of `RMF.thr_direct_of_offset` holds for all
`θ ≥ θ₀` and all `j`; `θ₀` depends only on `A, a, B, h, τ`. -/
theorem exists_thr_direct (A a Bs h τ : ℝ) (hA : 1 ≤ A) (ha : 0 ≤ a) (hB : 0 < Bs) (hh : 0 ≤ h)
    (hτ : 0 < τ) :
    ∃ θ₀ : ℝ, ∀ (θ : ℝ) (j : ℕ), θ₀ ≤ θ →
      A * (a + Bs * j + Real.exp 2 + h) ^ 2 + Real.log (Real.pi * 9) / 2
        ≤ τ * Real.log (blockScale θ (j + 1)) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hSpos : (0 : ℝ) < a + Bs + Real.exp 2 + h := by
    have := Real.exp_pos (2 : ℝ)
    linarith
  have hq : (0 : ℝ) < 5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ := by positivity
  refine ⟨Real.log (5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ), fun θ j hθ => ?_⟩
  refine thr_direct_of_offset hA ha hB hh ?_
  have hexp : 5 * A * (a + Bs + Real.exp 2 + h) ^ 2 / τ ≤ Real.exp θ := by
    rw [← Real.exp_log hq]
    exact Real.exp_le_exp.2 hθ
  rw [div_le_iff₀ hτ] at hexp
  rw [mul_comm τ (Real.exp θ)]
  exact hexp

/-! ### Towards the multi-block comparison

`RMF.isWindowComparison_of_indep` turns per-block comparisons into the joint statement Lemma 4
consumes, but it needs both increment families to be **jointly** independent, and all the
Gaussians to live on **one** space.  The pieces below supply that.

The `X` side is `RMF.iIndepFun_finsetSum_of_pairwiseDisjoint`: the local logarithms are independent
under the tilt and the blocks are disjoint.  The `Q` side needs the Gaussian family to be built
once, over all primes at once, which is what `RMF.primeMean` and `RMF.primeMoment₂` are for. -/

/-- The tilt cutoff serving every block up to the `n`-th: `y = ⌊x_n⌋₊ + 1`. -/
noncomputable def blockCutoff (θ : ℝ) (n : ℕ) : ℕ := ⌊blockScale θ (n + 1)⌋₊ + 1

/-- The prime set below a cutoff grows with the cutoff. -/
lemma primesBelowSub_mono {y y' : ℕ} (h : y ≤ y') : primesBelowSub y ⊆ primesBelowSub y' := by
  intro p hp
  rw [mem_primesBelowSub, Nat.mem_primesBelow] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩

/-- The cutoff grows with the horizon, so a block below one horizon is below any larger one. -/
lemma blockCutoff_mono (θ : ℝ) : Monotone (blockCutoff θ) := fun i j h => by
  rw [blockCutoff, blockCutoff]
  exact Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (by omega)))

/-- The blocks are pairwise disjoint, in the `Pairwise` form the grouping lemma wants. -/
lemma pairwise_disjoint_primeBlockSub (θ : ℝ) :
    Pairwise fun k l => Disjoint (primeBlockSub θ k) (primeBlockSub θ l) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact disjoint_primeBlockSub h
  · exact (disjoint_primeBlockSub h).symm

/-- Every block up to the `n`-th sits below the top of the `n`-th, so a single tilt at
`y = ⌊x_n⌋₊ + 1` serves them all. -/
lemma primeBlockSub_subset_primesBelowSub (θ : ℝ) {m n : ℕ} (h : m ≤ n) :
    primeBlockSub θ m ⊆ primesBelowSub (blockCutoff θ n) :=
  primesIcoSub_subset_primesBelowSub
    (Nat.succ_le_succ (Nat.floor_mono (blockScale_mono θ (by omega))))

/-- Hence a block below the horizon sits below any cutoff past it. -/
lemma primeBlockSub_subset_primesBelowSub_of_le {θ : ℝ} {n m y : ℕ} (hm : m ≤ n)
    (hy : blockCutoff θ n ≤ y) : primeBlockSub θ m ⊆ primesBelowSub y :=
  fun _ hp => primesBelowSub_mono hy (primeBlockSub_subset_primesBelowSub θ hm hp)

/-- **The block increments are jointly independent under the tilt.**

This is the `X` side of `RMF.isWindowComparison_of_indep`, and it is exactly what the grouping
lemma is for: the local logarithms are independent under `P~`
(`RMF.IsSteinhausPrimeValues.iIndepFun_localLog_tiltedMeasure`) and the blocks are disjoint. -/
theorem iIndepFun_blockSum_tiltedMeasure (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) (θ : ℝ) (w : Nat.Primes → ℂ) :
    iIndepFun (fun m ω => ∑ p ∈ primeBlockSub θ m, localLog (w p) (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun p => (measurable_localLog (w p)).comp (hX.measurable (p : ℕ) p.2))
    (hX.iIndepFun_localLog_tiltedMeasure y hs w) (pairwise_disjoint_primeBlockSub θ)

/-- The tilted mean at a single prime. -/
noncomputable def primeMean (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (p : Nat.Primes) : ℝ :=
  ∫ ω, localLog (w p) (X (p : ℕ) ω)
    ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ)

/-- The tilted second moment at a single prime, **raised to at least the square of the mean**:
`max (E~ξ_p²) ((E~ξ_p)²)`.  The `max` makes the hypothesis `m₁ p² ≤ m₂ p` of
`RMF.exists_gaussian_matching_moments` hold at every index (Cauchy–Schwarz is available only where
`‖w p‖ ≤ 1/5`), and changes nothing on a block (`RMF.primeMoment₂_eq_of_le`). -/
noncomputable def primeMoment₂ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (p : Nat.Primes) : ℝ :=
  max (∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
    (primeMean X μ y s w p ^ 2)

lemma sq_primeMean_le (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (p : Nat.Primes) :
    primeMean X μ y s w p ^ 2 ≤ primeMoment₂ X μ y s w p := le_max_right _ _

/-- On a block, the `max` is attained by the second moment — so nothing is distorted where it
matters. -/
lemma primeMoment₂_eq_of_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : Nat.Primes → ℂ} (hw : ‖w p‖ ≤ 1 / 5) :
    primeMoment₂ X μ y s w p
      = ∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ) :=
  max_eq_left (sq_integral_localLog_le_integral_mul_self hX y hs hp hw)

/-- `blockMatchedVar` is the sum of the per-prime matched variances built from `primeMoment₂` — the
`max` in `primeMoment₂` is inert on a block. -/
lemma blockMatchedVar_eq_sum (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    blockMatchedVar X μ y s w B
      = ∑ p ∈ B, matchingVar (primeMean X μ y s w p) (primeMoment₂ X μ y s w p) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [primeMoment₂_eq_of_le hX y hs (hB hp) (hw p hp)]
  rfl

/-! ### The cutoff does not matter

The multi-block comparison states its per-block hypotheses at the **global** cutoff
`blockCutoff θ n`, while the theorems that discharge them — `RMF.blockMatchedVar_concrete` and
`RMF.le_toReal_measure_Ioc_blockGaussian_of_thr` — are stated at the **per-block** cutoff
`blockCutoff θ j`.  For `j < n` those are different numbers, so without the bridge below nothing
plugs in.

The bridge is free, and `RMF.integral_comp_tiltedMeasure` is why: at a prime *below* the cutoff the
tilted law of `X p` is `steinhausLaw.tilted (2 • localLog (p^{-s}))`, in which `y` does not appear
at all.  Raising the cutoff adds tilting factors at other primes, and those are independent of
`X p`.  So no hypothesis on `w` is needed here — only that the block sits below both cutoffs. -/

/-- Any moment of a single `X p` is the same under either cutoff, provided `p` is below both. -/
lemma integral_comp_tiltedMeasure_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s : ℂ}
    (hs : 0 < s.re) {y y' : ℕ} {p : Nat.Primes} (hp : p ∈ primesBelowSub y)
    (hp' : p ∈ primesBelowSub y') {g : ℂ → ℝ} (hg : Measurable g) :
    (∫ ω, g (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y s μ))
      = ∫ ω, g (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) y' s μ) := by
  rw [integral_comp_tiltedMeasure hX y hs hp hg, integral_comp_tiltedMeasure hX y' hs hp' hg]

/-- Hence the block drift is cutoff-free. -/
lemma blockMean_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s : ℂ} (hs : 0 < s.re)
    {y y' : ℕ} {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hB' : B ⊆ primesBelowSub y') (w : Nat.Primes → ℂ) :
    blockMean X μ y s w B = blockMean X μ y' s w B :=
  Finset.sum_congr rfl fun p hp =>
    integral_comp_tiltedMeasure_congr_cutoff hX hs (hB hp) (hB' hp) (measurable_localLog (w p))

/-- And so is the matched block variance: both of `matchingVar`'s arguments are such moments. -/
lemma blockMatchedVar_congr_cutoff (hX : IsSteinhausPrimeValues X μ) {s : ℂ} (hs : 0 < s.re)
    {y y' : ℕ} {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y)
    (hB' : B ⊆ primesBelowSub y') (w : Nat.Primes → ℂ) :
    blockMatchedVar X μ y s w B = blockMatchedVar X μ y' s w B := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_comp_tiltedMeasure_congr_cutoff hX hs (hB hp) (hB' hp)
      (measurable_localLog (w p)),
    integral_comp_tiltedMeasure_congr_cutoff (g := fun z => localLog (w p) z * localLog (w p) z)
      hX hs (hB hp) (hB' hp) ((measurable_localLog (w p)).mul (measurable_localLog (w p)))]

/-! ### Beyond the horizon

`IsGaussianWalk`, and Proposition 5's `vmin ≤ v i ≤ vmax`, are statements about **every** index,
while the number theory controls only the blocks `m ≤ n`.  Past the top block the weights decay and
`∑_{p∈B_m} matchingVar` runs to `0`, so no `vmin > 0` can bound it: the walk cannot be the block
sums alone.

The fix is to give the walk a reservoir of its own.  The Gaussian family is indexed by
`Nat.Primes ⊕ ℕ`, the `ℕ` side carrying independent standard normals that are used *only* above the
horizon.  The blocks stay pairwise disjoint, so the grouping lemma still applies, and
`vmin ≤ 1 ≤ vmax` costs nothing.

This is legitimate exactly because everything Proposition 5 reads — `sliceEvent`, `barrierEvent`,
the drift sum — stops at `n`.  Nothing above the horizon is ever observed. -/

/-- The index set of block `m`: the primes of the block below the horizon, one fresh dummy above. -/
noncomputable def blockIndex (θ : ℝ) (n m : ℕ) : Finset (Nat.Primes ⊕ ℕ) :=
  if m ≤ n then (primeBlockSub θ m).map ⟨Sum.inl, Sum.inl_injective⟩ else {Sum.inr m}

@[simp]
lemma mem_blockIndex_inl {θ : ℝ} {n m : ℕ} {p : Nat.Primes} :
    Sum.inl p ∈ blockIndex θ n m ↔ m ≤ n ∧ p ∈ primeBlockSub θ m := by
  rw [blockIndex]
  by_cases hm : m ≤ n <;> simp [hm]

@[simp]
lemma mem_blockIndex_inr {θ : ℝ} {n m k : ℕ} :
    Sum.inr k ∈ blockIndex θ n m ↔ ¬ m ≤ n ∧ k = m := by
  rw [blockIndex]
  by_cases hm : m ≤ n <;> simp [hm]

/-- Still pairwise disjoint: the two sides of the sum cannot collide, and each side is disjoint on
its own — the primes by `RMF.pairwise_disjoint_primeBlockSub`, the dummies because index `m` uses
only the dummy `m`. -/
lemma pairwise_disjoint_blockIndex (θ : ℝ) (n : ℕ) :
    Pairwise fun k l => Disjoint (blockIndex θ n k) (blockIndex θ n l) := by
  intro k l hkl
  refine Finset.disjoint_left.2 ?_
  rintro (q | j) hik hil
  · rw [mem_blockIndex_inl] at hik hil
    exact Finset.disjoint_left.1 (pairwise_disjoint_primeBlockSub θ hkl) hik.2 hil.2
  · rw [mem_blockIndex_inr] at hik hil
    exact hkl (hik.2.symm.trans hil.2)

/-- The mean of the `m`-th block Gaussian: the tilted drift below the horizon, `0` above. -/
noncomputable def blockGaussMean (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ :=
  if m ≤ n then blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m) else 0

/-- The variance of the `m`-th block Gaussian: the matched block variance below the horizon, `1`
above.  The `1` is what makes `vmin ≤ v i ≤ vmax` satisfiable at every index. -/
noncomputable def blockGaussVar (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ≥0 :=
  if m ≤ n then blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) else 1

@[simp]
lemma blockGaussMean_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} {θ : ℝ} {n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} {m : ℕ} (hm : m ≤ n) :
    blockGaussMean X μ θ n s w m = blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m) :=
  if_pos hm

@[simp]
lemma blockGaussVar_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} {θ : ℝ} {n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} {m : ℕ} (hm : m ≤ n) :
    blockGaussVar X μ θ n s w m
      = blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) :=
  if_pos hm

/-- **The bridge, as the assembly needs it.**  Block `j` of an `n`-block run may be read at its own
cutoff, which is where the single-block development leaves it. -/
lemma blockMean_blockCutoff_eq (hX : IsSteinhausPrimeValues X μ) {s : ℂ} (hs : 0 < s.re)
    {θ : ℝ} {n j : ℕ} (hj : j ≤ n) (w : Nat.Primes → ℂ) :
    blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ j)
      = blockMean X μ (blockCutoff θ j) s w (primeBlockSub θ j) :=
  blockMean_congr_cutoff hX hs (primeBlockSub_subset_primesBelowSub θ hj)
    (primeBlockSub_subset_primesBelowSub θ le_rfl) w

/-- The same for the variance. -/
lemma blockMatchedVar_blockCutoff_eq (hX : IsSteinhausPrimeValues X μ) {s : ℂ} (hs : 0 < s.re)
    {θ : ℝ} {n j : ℕ} (hj : j ≤ n) (w : Nat.Primes → ℂ) :
    blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ j)
      = blockMatchedVar X μ (blockCutoff θ j) s w (primeBlockSub θ j) :=
  blockMatchedVar_congr_cutoff hX hs (primeBlockSub_subset_primesBelowSub θ hj)
    (primeBlockSub_subset_primesBelowSub θ le_rfl) w

/-- **The variance bounds at every index**, `1/16 ≤ v_m ≤ 9/2`, the bracket Probability Results 1
and 2 take.  Below the horizon this is `RMF.blockMatchedVar_concrete` moved to the global cutoff by
`RMF.blockMatchedVar_blockCutoff_eq`; above it the variance is the reservoir's `1`. -/
theorem blockGaussVar_bounds (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} (hθ : (8 : ℝ) ≤ θ) (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ 1)
    (hwn : ∀ j, j ≤ n → ∀ p ∈ primeBlockSub θ j,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ∀ m, 1 / 16 ≤ ((blockGaussVar X μ θ n s w m : ℝ≥0) : ℝ)
      ∧ ((blockGaussVar X μ θ n s w m : ℝ≥0) : ℝ) ≤ 9 / 2 := by
  intro m
  by_cases hm : m ≤ n
  · have hmθ : (8 : ℝ) ≤ (m : ℝ) + θ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [blockGaussVar, if_pos hm, blockMatchedVar_blockCutoff_eq hX hs hm w, blockCutoff]
    obtain ⟨hlo, hhi⟩ :=
      blockMatchedVar_concrete hX θ σ m s w hmθ hres (hσ m hm) (hwn m hm)
    constructor <;> linarith
  · rw [blockGaussVar, if_neg hm]
    norm_num

/-- **The variance bracket at a general tilt scale**: `e^{-2η}/4 ≤ v_m ≤ 9/2` at every index, the
analogue of `RMF.blockGaussVar_bounds`.  Only the lower end moves: the tilt thins the block, and
for `σ ≥ 0` every upper direction is free (`p^{-1-2σ} ≤ p^{-1}`).  The dummy indices above `n` keep
the value `1`, inside the bracket since `hσ` at `j = 0` forces `η ≥ 0`. -/
theorem blockGaussVar_bounds_of_le (hX : IsSteinhausPrimeValues X μ) {θ σ η : ℝ} {n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} (hθ : (8 : ℝ) ≤ θ) (hs : 0 < s.re) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hsc : ∀ j : ℕ, 14 + 2 * η ≤ Real.exp ((j : ℝ) + θ))
    (hσ : ∀ j, j ≤ n → |σ| * Real.log (blockScale θ (j + 1)) ≤ η)
    (hwn : ∀ j, j ≤ n → ∀ p ∈ primeBlockSub θ j,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ∀ m, Real.exp (-(2 * η)) / 4 ≤ ((blockGaussVar X μ θ n s w m : ℝ≥0) : ℝ)
      ∧ ((blockGaussVar X μ θ n s w m : ℝ≥0) : ℝ) ≤ 9 / 2 := by
  have hlog0 : (0 : ℝ) ≤ Real.log (blockScale θ (0 + 1)) := by
    rw [log_blockScale]; positivity
  have hη0 : (0 : ℝ) ≤ η :=
    le_trans (mul_nonneg (abs_nonneg σ) hlog0) (hσ 0 (Nat.zero_le n))
  have he1 : Real.exp (-(2 * η)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  intro m
  by_cases hm : m ≤ n
  · have hmθ : (8 : ℝ) ≤ (m : ℝ) + θ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [blockGaussVar, if_pos hm, blockMatchedVar_blockCutoff_eq hX hs hm w, blockCutoff]
    obtain ⟨hlo, hhi⟩ :=
      blockMatchedVar_concrete_of_le hX θ σ η m s w hmθ hres hσ0 (hsc m) (hσ m hm) (hwn m hm)
    constructor <;> linarith
  · rw [blockGaussVar, if_neg hm]
    refine ⟨?_, by norm_num⟩
    push_cast
    linarith

/-- **The block Gaussian's drift, with the tilt cutoff `y` a parameter**: `blockMean` at cutoff `y`
below the horizon, `0` above; `RMF.blockGaussMean` is the diagonal `y = RMF.blockCutoff θ n`.
Separating the two lets the walk stop below the top blocks while the tilt stays at the top: at
`η_m = Ke^{m-n}` (`RMF.sigma_le_mul_exp_sub`) only the top `⌈log K⌉` blocks are thinned. -/
noncomputable def blockGaussMeanAt (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ :=
  if m ≤ n then blockMean X μ y s w (primeBlockSub θ m) else 0

/-- The same for the variance. -/
noncomputable def blockGaussVarAt (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ≥0 :=
  if m ≤ n then blockMatchedVar X μ y s w (primeBlockSub θ m) else 1

@[simp]
lemma blockGaussMeanAt_blockCutoff (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) :
    blockGaussMeanAt X μ θ (blockCutoff θ n) n s w = blockGaussMean X μ θ n s w := rfl

@[simp]
lemma blockGaussVarAt_blockCutoff (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) :
    blockGaussVarAt X μ θ (blockCutoff θ n) n s w = blockGaussVar X μ θ n s w := rfl
/-- **Raising the cutoff does not move the block Gaussian.**  This is
`RMF.blockMean_congr_cutoff` and `RMF.blockMatchedVar_congr_cutoff` at every index: below the
horizon the tilted law of a prime does not see the cutoff, and above it both sides are the
reservoir's `N(0,1)`. -/
lemma blockGaussMeanAt_eq (hX : IsSteinhausPrimeValues X μ) {s : ℂ} (hs : 0 < s.re) {θ : ℝ}
    {n y : ℕ} (hy : blockCutoff θ n ≤ y) (w : Nat.Primes → ℂ) :
    blockGaussMeanAt X μ θ y n s w = blockGaussMean X μ θ n s w := by
  funext m
  rw [blockGaussMeanAt, blockGaussMean]
  by_cases hm : m ≤ n
  · rw [if_pos hm, if_pos hm]
    exact blockMean_congr_cutoff hX hs (primeBlockSub_subset_primesBelowSub_of_le hm hy)
      (primeBlockSub_subset_primesBelowSub θ hm) w
  · rw [if_neg hm, if_neg hm]

lemma blockGaussVarAt_eq (hX : IsSteinhausPrimeValues X μ) {s : ℂ} (hs : 0 < s.re) {θ : ℝ}
    {n y : ℕ} (hy : blockCutoff θ n ≤ y) (w : Nat.Primes → ℂ) :
    blockGaussVarAt X μ θ y n s w = blockGaussVar X μ θ n s w := by
  funext m
  rw [blockGaussVarAt, blockGaussVar]
  by_cases hm : m ≤ n
  · rw [if_pos hm, if_pos hm]
    exact blockMatchedVar_congr_cutoff hX hs (primeBlockSub_subset_primesBelowSub_of_le hm hy)
      (primeBlockSub_subset_primesBelowSub θ hm) w
  · rw [if_neg hm, if_neg hm]

/-- **The multi-block comparison**, Harper's Lemma 3 over the blocks `m < n`, in the shape
`RMF.measure_barrierEvent_le`, `RMF.proposition5_lower` and `RMF.proposition5_upper` consume, with
the tilt cutoff `y ≥ blockCutoff θ n` free.  One Gaussian family, indexed by `Nat.Primes ⊕ ℕ`, is
matched to `primeMean` and `primeMoment₂` at every prime and to `N(0,1)` at every dummy; the block
Gaussians are its block sums, at every index as `RMF.IsGaussianWalk` needs.  The per-block
hypotheses are discharged by `RMF.sum_third_moment_block_le` (`hTb`),
`RMF.le_toReal_measure_Ioc_blockGaussian_of_thr` (`hqlow`), `RMF.blockMatchedVar_concrete` (`hv`)
and `RMF.blockNum_le_of_le` (`hnum`).  The errors compound as in `RMF.isWindowComparison_of_indep`:
`∑_{m<n} ε m ≤ E ≤ 1/2` gives `2E`, for every shift `k ≤ n`. -/
theorem exists_isWindowComparison_primeBlockSub_of_cutoff (hX : IsSteinhausPrimeValues X μ)
    {s : ℂ} {θ : ℝ} {n y : ℕ} {w : Nat.Primes → ℂ} (hs : 0 < s.re)
    (hy : blockCutoff θ n ≤ y)
    (hw : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5)
    (ha : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    {W M T q ε : ℕ → ℝ} {E : ℝ}
    (hT : ∀ m, m < n → 0 < T m) (hq : ∀ m, m < n → 0 < q m)
    (hv : ∀ m, m < n →
      blockMatchedVar X μ (y) s w (primeBlockSub θ m) ≠ 0)
    (hTb : ∀ m, m < n →
      blockThirdConst * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ T m)
    (hqlow : ∀ m, m < n → ∀ c, |c| ≤ M m → q m ≤ (gaussianReal
      (blockMean X μ (y) s w (primeBlockSub θ m))
      (blockMatchedVar X μ (y) s w (primeBlockSub θ m))
      (Set.Ioc c (c + W m))).toReal)
    (hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        (blockMatchedVar X μ (y) s w (primeBlockSub θ m) : ℝ)))
      * T m ^ (1 / 4 : ℝ) ≤ ε m * q m)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m)
        = gaussianReal (blockGaussMeanAt X μ θ y n s w m) (blockGaussVarAt X μ θ y n s w m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (y) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLog (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => W (m + k)) (fun m => M (m + k)) (n - k) (2 * E)) := by
  classical
  have hprob := hX.isProbabilityMeasure_tiltedMeasure (y) hs
  have hξm : ∀ p : Nat.Primes, Measurable (fun ω => localLog (w p) (X (p : ℕ) ω)) := fun p =>
    (measurable_localLog (w p)).comp (hX.measurable (p : ℕ) p.2)
  have hξi := hX.iIndepFun_localLog_tiltedMeasure (y) hs w
  -- the Gaussian family: the primes, plus a reservoir of standard normals above the horizon
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hGlaw, hGm₁, hGm₂⟩ :=
    exists_gaussian_matching_moments
      (Sum.elim (primeMean X μ (y) s w) (fun _ : ℕ => (0 : ℝ)))
      (Sum.elim (primeMoment₂ X μ (y) s w) (fun _ : ℕ => (1 : ℝ)))
      (by
        rintro (q | j)
        · exact sq_primeMean_le X μ (y) s w q
        · norm_num)
  -- the prime half of that family, which is what the single-block development consumes
  have hPm : ∀ q : Nat.Primes, Measurable (G (Sum.inl q)) := fun q => hGm _
  have hPi : iIndepFun (fun q : Nat.Primes => G (Sum.inl q)) Q := hGi.precomp Sum.inl_injective
  have hPlaw : ∀ q : Nat.Primes, Q.map (G (Sum.inl q))
      = gaussianReal (primeMean X μ (y) s w q)
        (matchingVar (primeMean X μ (y) s w q)
          (primeMoment₂ X μ (y) s w q)) := fun q => hGlaw (Sum.inl q)
  have hPm₁ : ∀ q : Nat.Primes, ∫ ω, G (Sum.inl q) ω ∂Q
      = primeMean X μ (y) s w q := fun q => hGm₁ (Sum.inl q)
  have hPm₂ : ∀ q : Nat.Primes, ∫ ω, G (Sum.inl q) ω * G (Sum.inl q) ω ∂Q
      = primeMoment₂ X μ (y) s w q := fun q => hGm₂ (Sum.inl q)
  -- the variance sums agree with `blockMatchedVar` on each block below the horizon
  have hvar : ∀ m, m ≤ n →
      (∑ p ∈ primeBlockSub θ m, matchingVar (primeMean X μ (y) s w p)
          (primeMoment₂ X μ (y) s w p))
        = blockMatchedVar X μ (y) s w (primeBlockSub θ m) := fun m hm =>
    (blockMatchedVar_eq_sum hX _ hs (primeBlockSub_subset_primesBelowSub_of_le hm hy)
      (hw m hm)).symm
  -- below the horizon the block Gaussian is the block sum of the prime half
  have hNblock : ∀ m, m ≤ n → (fun ω => ∑ i ∈ blockIndex θ n m, G i ω)
      = fun ω => ∑ p ∈ primeBlockSub θ m, G (Sum.inl p) ω := by
    intro m hm
    funext ω
    rw [blockIndex, if_pos hm, Finset.sum_map]
    rfl
  have hNm : ∀ m, Measurable (fun ω => ∑ i ∈ blockIndex θ n m, G i ω) := fun m =>
    Finset.measurable_sum _ fun i _ => hGm i
  have hNi : iIndepFun (fun m ω => ∑ i ∈ blockIndex θ n m, G i ω) Q :=
    iIndepFun_finsetSum_of_pairwiseDisjoint hGm hGi (pairwise_disjoint_blockIndex θ n)
  have hNlaw : ∀ m, Q.map (fun ω => ∑ i ∈ blockIndex θ n m, G i ω)
      = gaussianReal (blockGaussMeanAt X μ θ y n s w m) (blockGaussVarAt X μ θ y n s w m) := by
    intro m
    rw [map_sum_gaussianReal hGm hGi hGlaw (blockIndex θ n m), blockGaussMeanAt,
      blockGaussVarAt]
    by_cases hm : m ≤ n
    · rw [if_pos hm, if_pos hm, blockIndex, if_pos hm, Finset.sum_map, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Sum.elim_inl]
      rw [hvar m hm]
      rfl
    · rw [if_neg hm, if_neg hm, blockIndex, if_neg hm, Finset.sum_singleton,
        Finset.sum_singleton]
      norm_num [matchingVar]
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ i ∈ blockIndex θ n m, G i ω, hQ, hNm, hNi, hNlaw, ?_⟩
  -- the per-block comparison, which is what the reindexing consumes
  have hblock : ∀ m, m < n → IsWindowComparison₁
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (y) s μ) Q
      (fun ω => ∑ p ∈ primeBlockSub θ m, localLog (w p) (X (p : ℕ) ω))
      (fun ω => ∑ i ∈ blockIndex θ n m, G i ω) (W m) (M m) (ε m) := by
    intro m hm
    have hmn : m ≤ n := le_of_lt hm
    rw [hNblock m hmn]
    have hB := primeBlockSub_subset_primesBelowSub_of_le hmn hy
    -- the matched law, with the `max` resolved on the block
    have hGlaw' : ∀ p ∈ primeBlockSub θ m, Q.map (G (Sum.inl p)) = gaussianReal
        (∫ ω, localLog (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (y) s μ))
        (matchingVar
          (∫ ω, localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (y) s μ))
          (∫ ω, localLog (w p) (X (p : ℕ) ω) * localLog (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => compMultExtension fun p => X p ω)
              (y) s μ))) := by
      intro p hp
      rw [hPlaw p, primeMoment₂_eq_of_le hX _ hs (hB hp) (hw m hmn p hp)]
      rfl
    -- the third-moment sum
    have hTsum := sum_third_moment_block_le hX (y) hs hB (hw m hmn) (ha m hmn)
      hPm hGlaw'
    refine isWindowComparison₁_of_gaussian_family_of_third_moment hξm hPm hξi hPi hPlaw
      (fun p hp => integrable_localLog_tiltedMeasure hX _ hs (hB hp) (hw m hmn p hp))
      (fun p hp => integrable_localLog_mul_self_tiltedMeasure hX _ hs (hB hp) (hw m hmn p hp))
      (fun p _ => integrable_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (fun p _ => integrable_mul_self_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (fun p _ => (hPm₁ p).symm)
      (fun p hp => by
        rw [hPm₂ p, primeMoment₂_eq_of_le hX _ hs (hB hp) (hw m hmn p hp)])
      (fun p hp => integrable_abs_cube_localLog_tiltedMeasure hX _ hs (hB hp) (hw m hmn p hp))
      (fun p _ => integrable_abs_cube_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (hT m hm) (hq m hm) (by rw [hvar m hmn]; exact hv m hm)
      (le_trans hTsum (hTb m hm))
      (by intro c hc; rw [hvar m hmn]; exact hqlow m hm c hc)
      (by rw [hvar m hmn]; exact hnum m hm)
  intro k hkn
  exact isWindowComparison_shift_of_indep
    (iIndepFun_blockSum_tiltedMeasure hX (y) hs θ w) hNi hkn hε0 hsum hE hblock

/-- **The multi-block comparison at the diagonal**, `y = RMF.blockCutoff θ n`:
`RMF.exists_isWindowComparison_primeBlockSub_of_cutoff` with the tilt cutoff fixed. -/
theorem exists_isWindowComparison_primeBlockSub (hX : IsSteinhausPrimeValues X μ)
    {s : ℂ} {θ : ℝ} {n : ℕ} {w : Nat.Primes → ℂ} (hs : 0 < s.re)
    (hw : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5)
    (ha : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    {W M T q ε : ℕ → ℝ} {E : ℝ}
    (hT : ∀ m, m < n → 0 < T m) (hq : ∀ m, m < n → 0 < q m)
    (hv : ∀ m, m < n →
      blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) ≠ 0)
    (hTb : ∀ m, m < n →
      blockThirdConst * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ T m)
    (hqlow : ∀ m, m < n → ∀ c, |c| ≤ M m → q m ≤ (gaussianReal
      (blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m))
      (blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m))
      (Set.Ioc c (c + W m))).toReal)
    (hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        (blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ)))
      * T m ^ (1 / 4 : ℝ) ≤ ε m * q m)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m)
        = gaussianReal (blockGaussMean X μ θ n s w m) (blockGaussVar X μ θ n s w m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLog (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => W (m + k)) (fun m => M (m + k)) (n - k) (2 * E)) :=
  exists_isWindowComparison_primeBlockSub_of_cutoff hX hs le_rfl hw ha hT hq hv hTb hqlow hnum
    hε0 hsum hE

/-! ### The drift

Under the tilt the field acquires a mean of about `+1` per block (the Girsanov shift, the `+ j` in
Harper's barrier).  Proposition 5 needs it quantitatively: `|∑_{m<j} θ_m - j| ≤ C` with `C`
independent of `n` and `j`.

At the one-point weight `w_p = p^{-s}` the field watched is the one the measure is tilted by, and
the main term `∑_{p∈B} Re(w_p · conj(p^{-s}))` of the tilted mean
(`RMF.abs_integral_sum_localLog_tiltedMeasure_sub_le`) is `∑_{p∈B} p^{-1-2σ}`, whose distance from
`1` is `RMF.abs_sum_prime_block_rpow_sub_one_le`.  The error term must be measured against the true
weight size, not the crude `‖p^{-s}‖ ≤ 1/5`: at `1/5` it is about `1/48` per block, which sums to
`O(n)`; against `κ² = e²/blockScale θ m` it is doubly exponentially small. -/

/-- `(z · conj z).re = ‖z‖²`. -/
lemma re_mul_conj_self (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

/-- **At the one-point weight, the tilted mean's main term is the block sum.**  With `w_p = p^{-s}`
and `Re s = 1/2 + σ`, `∑_{p∈B} Re(w_p · conj(p^{-s})) = ∑_{p∈B} p^{-1-2σ}`. -/
lemma sum_re_self_mul_conj_eq {s : ℂ} {σ : ℝ} (hres : s.re = 1 / 2 + σ)
    (B : Finset Nat.Primes) :
    (∑ p ∈ B, ((((p : ℕ) : ℂ) ^ (-s)) * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re)
      = ∑ p ∈ B, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [re_mul_conj_self, norm_sq_prime_cpow_neg p hres]

/-! ### One weight for block-dependent offsets

Every `w`-general lemma in this file takes a **single** `w : Nat.Primes → ℂ` for the whole family,
while Harper's offsets `t_m` vary with the block.  Substituting `fun p => p^{-(s + i t m)}` is
therefore not possible — there is no `m` in scope.

The fix is to let the prime choose its own block.  The blocks partition the primes above
`blockScale θ 0` (`RMF.pairwise_disjoint_primeBlockSub`), so `p` determines `m`, and a single
weight can carry all the offsets at once. -/

/-- The index of the block containing `p`.  Outside the blocks the value is junk, which is harmless:
every use is guarded by membership. -/
noncomputable def blockOffsetIndex (θ : ℝ) (p : Nat.Primes) : ℕ :=
  ⌈Real.log (Real.log ((p : ℕ) : ℝ)) - θ⌉₊ - 1

/-- On its own block the index is exact.  `p ∈ B_m` says `m + θ < log log p ≤ m + 1 + θ`, which is
`⌈log log p - θ⌉ = m + 1`. -/
lemma blockOffsetIndex_eq_of_mem {θ : ℝ} {m : ℕ} {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) : blockOffsetIndex θ p = m := by
  obtain ⟨h1, h2⟩ := mem_primeBlockSub.1 hp
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hlow : Real.exp ((m : ℝ) + θ) < Real.log ((p : ℕ) : ℝ) := by
    have h := Real.log_lt_log (blockScale_pos θ m) h1
    rwa [log_blockScale] at h
  have hhigh : Real.log ((p : ℕ) : ℝ) ≤ Real.exp (((m : ℝ) + 1) + θ) := by
    have h := Real.log_le_log hp0 h2
    rw [log_blockScale] at h
    push_cast at h
    linarith
  have hL0 : (0 : ℝ) < Real.log ((p : ℕ) : ℝ) := lt_trans (Real.exp_pos _) hlow
  have hlow2 : (m : ℝ) + θ < Real.log (Real.log ((p : ℕ) : ℝ)) := by
    have h := Real.log_lt_log (Real.exp_pos ((m : ℝ) + θ)) hlow
    rwa [Real.log_exp] at h
  have hhigh2 : Real.log (Real.log ((p : ℕ) : ℝ)) ≤ ((m : ℝ) + 1) + θ := by
    have h := Real.log_le_log hL0 hhigh
    rwa [Real.log_exp] at h
  have hceil : ⌈Real.log (Real.log ((p : ℕ) : ℝ)) - θ⌉₊ = m + 1 := by
    rw [Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel]
    refine ⟨by linarith, ?_⟩
    push_cast
    linarith
  rw [blockOffsetIndex, hceil]
  omega

/-- **The weight carrying block-dependent offsets.**  A single `Nat.Primes → ℂ`, so every
`w`-general lemma applies to it unchanged. -/
noncomputable def blockOffsetWeight (θ : ℝ) (t : ℕ → ℝ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  ((p : ℕ) : ℂ) ^ (-(s + (t (blockOffsetIndex θ p) : ℂ) * Complex.I))

lemma blockOffsetWeight_eq_of_mem {θ : ℝ} {t : ℕ → ℝ} {s : ℂ} {m : ℕ} {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    blockOffsetWeight θ t s p = ((p : ℕ) : ℂ) ^ (-(s + (t m : ℂ) * Complex.I)) := by
  rw [blockOffsetWeight, blockOffsetIndex_eq_of_mem hp]

/-- At zero offsets the weight **is** the one-point weight.  Harper's own lower-bound application
takes `t_j ≡ 0`. -/
lemma blockOffsetWeight_zero (θ : ℝ) (s : ℂ) :
    blockOffsetWeight θ (fun _ => 0) s = fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s) := by
  funext q
  rw [blockOffsetWeight]
  norm_num

/-- **The offsets are free.**  `‖w p‖² = p^{-1-2σ}` holds at *any* offsets, because multiplying by
`p^{-it}` is multiplying by a unimodular factor.  So the `hwn` hypothesis of every `w`-general
lemma discharges with no condition on `t` whatsoever. -/
lemma norm_sq_blockOffsetWeight {θ σ : ℝ} {t : ℕ → ℝ} {s : ℂ} (hres : s.re = 1 / 2 + σ)
    (p : Nat.Primes) :
    ‖blockOffsetWeight θ t s p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  rw [blockOffsetWeight]
  exact norm_sq_prime_cpow_neg p (by simp [hres])

/-- **The tilted block mean, in terms of `blockMean`**:
`|blockMean - ∑_{p∈B} Re(w_p·conj p^{-s})| ≤ ∑_{p∈B} ‖w_p p^{-s}‖²(1 - ‖w_p p^{-s}‖)⁻¹/2`.
`RMF.abs_integral_sum_localLog_tiltedMeasure_sub_le` is stated for the integral of the sum;
`blockMean` is the sum of the integrals. -/
theorem abs_blockMean_sub_sum_re_le (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |blockMean X μ y s w B - ∑ p ∈ B, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re|
      ≤ ∑ p ∈ B, ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖ ^ 2
          * (1 - ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖)⁻¹ / 2 := by
  have h := abs_integral_sum_localLog_tiltedMeasure_sub_le hX y hs hB hw
  rwa [integral_finsetSum B
    (fun p hp => integrable_localLog_tiltedMeasure hX y hs (hB hp) (hw p hp))] at h

/-- The block sum's deviation from `1`, in the `Nat.Primes` indexing. -/
theorem abs_sum_rpow_primeBlockSub_sub_one_le (θ σ η : ℝ) (m : ℕ)
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hη : 0 ≤ η) (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η) :
    |(∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) - 1|
      ≤ (Real.exp (2 * η) - 1)
        + Real.exp (2 * η) * (60 / Real.log (blockScale θ (m + 1))) := by
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  have hrw : (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = ∑ p ∈ {p ∈ Finset.Ioc ⌊blockScale θ (m + 1) ^ (Real.exp 1)⁻¹⌋₊
          ⌊blockScale θ (m + 1)⌋₊ | Nat.Prime p}, (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [primeBlockSub, harperBlock, sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-1 - 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  exact abs_sum_prime_block_rpow_sub_one_le _ σ η hη hbig hσ

/-- **The drift of one block**, at the one-point weight `w_p = p^{-s}`:
`|blockMean - 1| ≤ (e^{2η} - 1) + e^{2η}·60/log x_{m+1} + 2e^{4η}/x_m`.  The terms are the tilt
(geometric in `n - m` at `η = e^{m-n}`), block Mertens (geometric in `m`), and the second-order
error of the tilted mean, doubly exponentially small against the true weight size; against the
crude `‖p^{-s}‖ ≤ 1/5` it would be about `1/48` per block, summing to `O(n)`. -/
theorem abs_blockMean_sub_one_le (hX : IsSteinhausPrimeValues X μ) {s : ℂ} {θ σ η : ℝ} {m n : ℕ}
    (hmθ : (5 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n) (hres : s.re = 1 / 2 + σ)
    (hη0 : 0 ≤ η) (hsc : 14 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η) :
    |blockMean X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) - 1|
      ≤ (Real.exp (2 * η) - 1)
        + Real.exp (2 * η) * (60 / Real.log (blockScale θ (m + 1)))
        + 2 * Real.exp (4 * η) / blockScale θ m := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hsre : 0 < s.re := re_pos_of_block_of_le hres hsc hσ
  have hB := primeBlockSub_subset_primesBelowSub θ hmn
  have hb0 : (0 : ℝ) < blockScale θ m := blockScale_pos θ m
  have hκ0 : (0 : ℝ) < Real.exp η / √(blockScale θ m) := by
    have := Real.sqrt_pos.2 hb0
    positivity
  -- the true weight size on the block, now carrying the tilt scale
  have hκsq : (Real.exp η / √(blockScale θ m)) ^ 2 = Real.exp (2 * η) / blockScale θ m := by
    rw [div_pow, Real.sq_sqrt hb0.le, ← Real.exp_nat_mul]
    norm_num
  have hκ : Real.exp η / √(blockScale θ m) ≤ 1 / 1000 := blockWeightSize_le_of_le hsc
  -- the tilt radius on the block, in both the true and the crude form
  have hκ' : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp η / √(blockScale θ m) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (norm_sq_prime_cpow_neg p hres)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := fun p hp =>
    le_trans (hκ' p hp) (by linarith)
  -- the norm of the product is the block weight
  have hnorm : ∀ p : Nat.Primes,
      ‖(((p : ℕ) : ℂ) ^ (-s)) * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖
        = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    intro p
    rw [norm_mul, Complex.norm_conj, ← pow_two, norm_sq_prime_cpow_neg p hres]
  -- the tilted mean, and its main term
  have h1 := abs_blockMean_sub_sum_re_le hX (blockCutoff θ n) hsre hB hw5
  rw [sum_re_self_mul_conj_eq hres (primeBlockSub θ m)] at h1
  -- the block sum's deviation from 1
  have h2 := abs_sum_rpow_primeBlockSub_sub_one_le θ σ η m hm3 hη0 hσ
  set S : ℝ := ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) with hS
  set L : ℝ := Real.log (blockScale θ (m + 1)) with hL
  -- `L ≥ e⁴ ≥ 54.5`, so `1 + 60/L ≤ 2.11`
  have hLbig : (54.5 : ℝ) ≤ L := by
    rw [hL, log_blockScale]
    have he : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (54.5 : ℝ) ≤ (2.718 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 4
      _ = Real.exp ((4 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  have hd : (0 : ℝ) ≤ 60 / L := by positivity
  have hd2 : (60 : ℝ) / L ≤ 1.11 := by rw [div_le_iff₀ hL0]; linarith
  have hexp : (0 : ℝ) < Real.exp (2 * η) := Real.exp_pos _
  -- the tilted mean's error term, against the TRUE weight size
  have herr : ∑ p ∈ primeBlockSub θ m,
        ‖(((p : ℕ) : ℂ) ^ (-s)) * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖ ^ 2
          * (1 - ‖(((p : ℕ) : ℂ) ^ (-s)) * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖)⁻¹ / 2
      ≤ (25 / 48 * (Real.exp η / √(blockScale θ m)) ^ 2) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [hnorm p]
    have hu : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) = ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 :=
      (norm_sq_prime_cpow_neg p hres).symm
    have hu0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by rw [hu]; positivity
    have huk : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ (Real.exp η / √(blockScale θ m)) ^ 2 := by
      rw [hu]; exact pow_le_pow_left₀ (norm_nonneg _) (hκ' p hp) 2
    have hu25 : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ 1 / 25 := by
      rw [hu]
      nlinarith [norm_nonneg (((p : ℕ) : ℂ) ^ (-s)), hw5 p hp]
    have hinv : (1 - ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))⁻¹ ≤ 25 / 24 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    nlinarith [hu0, huk, hinv, hκ0]
  -- put the three together
  have hSle : S ≤ Real.exp (2 * η) * (1 + 60 / L) := by
    have := (abs_le.1 h2).2
    nlinarith [this, hexp, hd]
  have htri := abs_sub_le (blockMean X μ (blockCutoff θ n) s
    (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) S 1
  have hS384 : S ≤ 96 / 25 * Real.exp (2 * η) := by
    have h1' : Real.exp (2 * η) * (1 + 60 / L) ≤ Real.exp (2 * η) * 2.11 :=
      mul_le_mul_of_nonneg_left (by linarith) hexp.le
    linarith
  have hfac : (25 / 48 : ℝ) * (Real.exp η / √(blockScale θ m)) ^ 2 * S
      ≤ 2 * Real.exp (4 * η) / blockScale θ m := by
    have hexp4 : Real.exp (2 * η) * Real.exp (2 * η) = Real.exp (4 * η) := by
      rw [← Real.exp_add]; ring_nf
    rw [hκsq]
    have heq : (25 / 48 : ℝ) * (Real.exp (2 * η) / blockScale θ m) * S
        = 25 / 48 * Real.exp (2 * η) * S / blockScale θ m := by ring
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ hb0.le
    rw [← hexp4]
    nlinarith [mul_le_mul_of_nonneg_left hS384 hexp.le, hexp]
  linarith [htri, h1, h2, herr, hfac]

/-- From `‖u‖² = a^{-1-2σ}` to `‖u‖ = a^{-1/2-σ}`. -/
lemma norm_eq_rpow_of_sq_eq {u : ℂ} {a σ : ℝ} (ha : 0 < a)
    (hu : ‖u‖ ^ 2 = a ^ (-1 - 2 * σ)) :
    ‖u‖ = a ^ (-(1 / 2) - σ) := by
  have h := congrArg Real.sqrt hu
  rw [Real.sqrt_sq (norm_nonneg u), Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le] at h
  rw [h]
  congr 1
  ring

/-- The block sum at a non-negative shift, in the `Nat.Primes` indexing. -/
theorem sum_rpow_primeBlockSub_le_of_nonneg (θ σ : ℝ) (m : ℕ) (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : 0 ≤ σ) :
    (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      ≤ 1 + 60 / Real.log (blockScale θ (m + 1)) := by
  have hbig : Real.exp (Real.exp 1) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    refine Real.exp_le_exp.2 (Real.exp_le_exp.2 ?_)
    push_cast
    linarith [Real.exp_one_lt_d9]
  have hrw : (∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = ∑ p ∈ {p ∈ Finset.Ioc ⌊blockScale θ (m + 1) ^ (Real.exp 1)⁻¹⌋₊
          ⌊blockScale θ (m + 1)⌋₊ | Nat.Prime p}, (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [primeBlockSub, harperBlock, sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-1 - 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  exact sum_prime_block_rpow_le_of_nonneg _ σ hbig hσ

/-- **The drift's upper bound, uniform in the tilt scale**: for `m + θ ≥ 5`, `σ ≥ 0`,
`14 + 2η ≤ e^{m+θ}`, `|σ|·log x_{m+1} ≤ η` and `‖w_p‖² = p^{-1-2σ}`,
`|blockMean| ≤ 1 + 60/log x_{m+1} + 2e^{2η}/x_m`.  Since `σ ≥ 0`, `p^{-1-2σ} ≤ p^{-1}` termwise and
the main term loses its `η` (`RMF.sum_rpow_primeBlockSub_le_of_nonneg`); the tilt survives only in
the Taylor error. -/
theorem abs_blockMean_le_of_le (hX : IsSteinhausPrimeValues X μ) {s : ℂ} {θ σ η : ℝ} {m n : ℕ}
    {w : Nat.Primes → ℂ} (hmθ : (5 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hres : s.re = 1 / 2 + σ) (hσ0 : 0 ≤ σ) (hsc : 14 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    |blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m)|
      ≤ 1 + 60 / Real.log (blockScale θ (m + 1))
        + 2 * Real.exp (2 * η) / blockScale θ m := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hsre : 0 < s.re := re_pos_of_block_of_le hres hsc hσ
  have hB := primeBlockSub_subset_primesBelowSub θ hmn
  have hb0 : (0 : ℝ) < blockScale θ m := blockScale_pos θ m
  have hκ0 : (0 : ℝ) < Real.exp η / √(blockScale θ m) := by
    have := Real.sqrt_pos.2 hb0
    positivity
  have hκsq : (Real.exp η / √(blockScale θ m)) ^ 2 = Real.exp (2 * η) / blockScale θ m := by
    rw [div_pow, Real.sq_sqrt hb0.le, ← Real.exp_nat_mul]
    norm_num
  have hκ : Real.exp η / √(blockScale θ m) ≤ 1 / 1000 := blockWeightSize_le_of_le hsc
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ Real.exp η / √(blockScale θ m) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (hwn p hp)
  have haκ : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ Real.exp η / √(blockScale θ m) := fun p hp =>
    norm_le_of_mem_primeBlockSub_of_le hσ hp (norm_sq_prime_cpow_neg p hres)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun p hp =>
    le_trans (hwκ p hp) (by linarith)
  -- the product has the block weight as its norm, whatever the argument of `w p`
  have hnorm : ∀ p ∈ primeBlockSub θ m,
      ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖
        = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    intro p hp
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [norm_mul, Complex.norm_conj, norm_eq_rpow_of_sq_eq hp0 (hwn p hp),
      norm_eq_rpow_of_sq_eq hp0 (norm_sq_prime_cpow_neg p hres), ← Real.rpow_add hp0]
    congr 1
    ring
  have h1 := abs_blockMean_sub_sum_re_le hX (blockCutoff θ n) hsre hB hw5
  set S : ℝ := ∑ p ∈ primeBlockSub θ m, ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) with hS
  -- **the cosine, discarded**: `|Re z| ≤ ‖z‖`
  have hmain : |∑ p ∈ primeBlockSub θ m,
      (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re| ≤ S := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [hS]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [← hnorm p hp]
    exact Complex.abs_re_le_norm _
  -- the tilted mean's error term, against the true weight size
  have herr : ∑ p ∈ primeBlockSub θ m,
        ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖ ^ 2
          * (1 - ‖w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))‖)⁻¹ / 2
      ≤ (25 / 48 * (Real.exp η / √(blockScale θ m)) ^ 2) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [hnorm p hp]
    have hu : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = ‖w p‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
      rw [← hnorm p hp, norm_mul, Complex.norm_conj]
    have hu0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by rw [hu]; positivity
    have huk : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ (Real.exp η / √(blockScale θ m)) ^ 2 := by
      rw [hu, sq]
      exact mul_le_mul (hwκ p hp) (haκ p hp) (norm_nonneg _) hκ0.le
    have hu25 : ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) ≤ 1 / 25 := by nlinarith [huk, hκ, hκ0]
    have hinv : (1 - ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))⁻¹ ≤ 25 / 24 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    nlinarith [hu0, huk, hinv, hκ0]
  set L : ℝ := Real.log (blockScale θ (m + 1)) with hL
  have hLbig : (54.5 : ℝ) ≤ L := by
    rw [hL, log_blockScale]
    have he : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (54.5 : ℝ) ≤ (2.718 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 4
      _ = Real.exp ((4 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  have hd : (0 : ℝ) ≤ 60 / L := by positivity
  have hd2 : (60 : ℝ) / L ≤ 1.11 := by rw [div_le_iff₀ hL0]; linarith
  -- **the main term, with no `η` in it** — this is where `σ ≥ 0` is spent
  have hSle : S ≤ 1 + 60 / L := by
    rw [hS, hL]
    exact sum_rpow_primeBlockSub_le_of_nonneg θ σ m hm3 hσ0
  have hS384 : S ≤ 96 / 25 := by linarith
  have hfac : (25 / 48 : ℝ) * (Real.exp η / √(blockScale θ m)) ^ 2 * S
      ≤ 2 * Real.exp (2 * η) / blockScale θ m := by
    rw [hκsq]
    have hq0 : (0 : ℝ) ≤ 25 / 48 * (Real.exp (2 * η) / blockScale θ m) := by positivity
    have hstep : 25 / 48 * (Real.exp (2 * η) / blockScale θ m) * S
        ≤ 25 / 48 * (Real.exp (2 * η) / blockScale θ m) * (96 / 25) :=
      mul_le_mul_of_nonneg_left hS384 hq0
    have hre : 25 / 48 * (Real.exp (2 * η) / blockScale θ m) * (96 / 25)
        = 2 * Real.exp (2 * η) / blockScale θ m := by ring
    linarith
  have htri : |blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m)|
      ≤ |blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m)
            - ∑ p ∈ primeBlockSub θ m, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re|
          + |∑ p ∈ primeBlockSub θ m,
              (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re| := by
    simpa using abs_sub_le (blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m))
      (∑ p ∈ primeBlockSub θ m, (w p * (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-s))).re) 0
  linarith [htri, h1, hmain, herr, hfac, hSle]

/-! ### Summing the drift over the blocks

`|θ_m - 1|` has three parts (`RMF.abs_blockMean_sub_one_le`), and each is summable for a different
reason.  The two that matter are geometric, and they decay in *opposite* directions: the tilt term
decays as one moves **down** from the top block `n`, the Mertens term as one moves **up** from the
bottom.  Both sums are therefore `O(1)` uniformly in `n`, which is what makes `C` absolute. -/

/-- `∑_{m<j} e^{-m} ≤ 2`, uniformly in `j`. -/
lemma sum_exp_neg_nat_le (j : ℕ) : ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ)) ≤ 2 := by
  have hpos : (0 : ℝ) ≤ Real.exp (-1) := (Real.exp_pos _).le
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlt : Real.exp (-1) < 1 := by linarith
  have hrw : ∀ m : ℕ, Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
    intro m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun m _ => hrw m), Finset.range_eq_Ico]
  refine le_trans (geom_sum_Ico_le_of_lt_one hpos hlt) ?_
  rw [pow_zero, div_le_iff₀ (by linarith)]
  linarith

/-- **Harper's `|σ| ≤ 1/log x_n`, read at block `m`.**

The bound is at the **top** scale, and `log x_m / log x_n = e^{m-n}`, so at block `m` it delivers
`η_m = e^{m-n}` — exactly, not as a chosen convenience.  This is the whole reason the drift is
summable: the tilt distortion at block `m` is geometric in `n - m`. -/
lemma sigma_le_exp_sub (θ σ : ℝ) {m n : ℕ}
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1) :
    |σ| * Real.log (blockScale θ (m + 1)) ≤ Real.exp ((m : ℝ) - n) := by
  rw [log_blockScale] at hσ ⊢
  have hfac : Real.exp (((m + 1 : ℕ) : ℝ) + θ)
      = Real.exp (((n + 1 : ℕ) : ℝ) + θ) * Real.exp ((m : ℝ) - n) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hfac, ← mul_assoc]
  have h0 : (0 : ℝ) < Real.exp ((m : ℝ) - n) := Real.exp_pos _
  nlinarith [hσ, h0, abs_nonneg σ]

/-- **Harper's `|σ| ≤ K/\log x_n`, read at block `m`.**

`RMF.sigma_le_exp_sub` is the case `K = 1`.  The ratio `\log x_m / \log x_n = e^{m-n}` is what
carries the scale down, and it is exact — so a tilt of `K` at the top is a tilt of `Ke^{m-n}` at
block `m`, geometric in `n - m` whatever `K` is.  **This is why the drift stays summable at any
absolute scale.** -/
lemma sigma_le_mul_exp_sub (θ σ K : ℝ) {m n : ℕ}
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |σ| * Real.log (blockScale θ (m + 1)) ≤ K * Real.exp ((m : ℝ) - n) := by
  rw [log_blockScale] at hσ ⊢
  have hfac : Real.exp (((m + 1 : ℕ) : ℝ) + θ)
      = Real.exp (((n + 1 : ℕ) : ℝ) + θ) * Real.exp ((m : ℝ) - n) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hfac, ← mul_assoc]
  have h0 : (0 : ℝ) < Real.exp ((m : ℝ) - n) := Real.exp_pos _
  nlinarith [hσ, h0, abs_nonneg σ]

/-- `e^x - 1 ≤ x e^x`, the linearisation the tilt term needs.  Immediate from `1 - x ≤ e^{-x}`. -/
lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hx := Real.exp_pos x
  have hmul : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [h, hx, hmul]

/-- `∑_{m<j} e^{m-n} ≤ 2` for `j ≤ n+1` — the tilt term, summed.  Geometric **downwards** from the
top block. -/
lemma sum_exp_sub_le {n j : ℕ} (hj : j ≤ n + 1) :
    ∑ m ∈ Finset.range j, Real.exp ((m : ℝ) - n) ≤ 2 := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hne : Real.exp 1 ≠ 1 := by linarith
  have hrw : ∀ m : ℕ, Real.exp ((m : ℝ) - n) = Real.exp (-(n : ℝ)) * Real.exp 1 ^ m := by
    intro m
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun m _ => hrw m), ← Finset.mul_sum, geom_sum_eq hne]
  have hjn : Real.exp (-(n : ℝ)) * Real.exp 1 ^ j ≤ Real.exp 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
    linarith
  have hden : (0 : ℝ) < Real.exp 1 - 1 := by linarith
  have hnn : (0 : ℝ) < Real.exp (-(n : ℝ)) := Real.exp_pos _
  rw [mul_div_assoc'] at *
  rw [div_le_iff₀ hden]
  nlinarith [hjn, hnn, he2]

/-- `√(e^t) = e^{t/2}`. -/
lemma sqrt_exp (t : ℝ) : √(Real.exp t) = Real.exp (t / 2) := by
  rw [show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) by rw [← Real.exp_add]; ring_nf]
  exact Real.sqrt_mul_self (Real.exp_pos _).le

/-- `\min(x,1) ≤ √x` — the bound that lets a per-block estimate which is *linear* below the tilt
scale and *bounded* above it be summed without a case split. -/
lemma min_one_le_sqrt {x : ℝ} (hx : 0 ≤ x) : min x 1 ≤ √x := by
  rcases le_or_gt x 1 with h | h
  · rw [min_eq_left h]
    exact (Real.le_sqrt hx hx).2 (by nlinarith)
  · rw [min_eq_right h.le]
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- `∑_{m<j} e^{(m-n)/2} ≤ 3`, uniformly in `j ≤ n+1` — the half-rate analogue of
`RMF.sum_exp_sub_le`.  The half rate is what `\min(η_m,1) ≤ √{η_m}` costs. -/
lemma sum_exp_half_sub_le {n j : ℕ} (hj : j ≤ n + 1) :
    ∑ m ∈ Finset.range j, Real.exp (((m : ℝ) - n) / 2) ≤ 3 := by
  have he2 : (1.5 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have hne : Real.exp (1 / 2 : ℝ) ≠ 1 := by
    intro h; rw [h] at he2; linarith
  have hrw : ∀ m : ℕ, Real.exp (((m : ℝ) - n) / 2)
      = Real.exp (-(n : ℝ) / 2) * Real.exp (1 / 2 : ℝ) ^ m := by
    intro m
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun m _ => hrw m), ← Finset.mul_sum, geom_sum_eq hne]
  have hjn : Real.exp (-(n : ℝ) / 2) * Real.exp (1 / 2 : ℝ) ^ j ≤ Real.exp (1 / 2 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
    linarith
  have hden : (0 : ℝ) < Real.exp (1 / 2 : ℝ) - 1 := by linarith
  have hnn : (0 : ℝ) < Real.exp (-(n : ℝ) / 2) := Real.exp_pos _
  rw [mul_div_assoc'] at *
  rw [div_le_iff₀ hden]
  nlinarith [hjn, hnn, he2]

lemma blockWeightSize_sq (θ : ℝ) (m : ℕ) :
    blockWeightSize θ m ^ 2 = Real.exp 2 / blockScale θ m := by
  rw [blockWeightSize, div_pow, Real.sq_sqrt (blockScale_pos θ m).le, ← Real.exp_nat_mul]
  norm_num

/-- `∑_{m<j} κ_m² ≤ 2e²e^{-θ}`: the tilted mean's error term, summed.  `κ_m² = e²e^{-e^{m+θ}}` is
*doubly* exponentially small, so even the crude `e^{m+θ} ≥ m+θ` leaves a convergent geometric
series. -/
lemma sum_blockWeightSize_sq_le (θ : ℝ) (j : ℕ) :
    ∑ m ∈ Finset.range j, blockWeightSize θ m ^ 2 ≤ 2 * Real.exp 2 * Real.exp (-θ) := by
  have hc : (0 : ℝ) ≤ Real.exp 2 * Real.exp (-θ) := by positivity
  have hb : ∀ m : ℕ, blockWeightSize θ m ^ 2
      ≤ Real.exp 2 * Real.exp (-θ) * Real.exp (-(m : ℝ)) := by
    intro m
    rw [blockWeightSize_sq, blockScale, div_le_iff₀ (Real.exp_pos _)]
    have hmono : Real.exp ((m : ℝ) + θ) ≤ Real.exp (Real.exp ((m : ℝ) + θ)) :=
      Real.exp_le_exp.2 (by linarith [Real.add_one_le_exp ((m : ℝ) + θ)])
    have heq : Real.exp 2 * Real.exp (-θ) * Real.exp (-(m : ℝ)) * Real.exp ((m : ℝ) + θ)
        = Real.exp 2 := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add,
        show -θ + (-(m : ℝ) + ((m : ℝ) + θ)) = 0 by ring, Real.exp_zero, mul_one]
    calc Real.exp 2
        = Real.exp 2 * Real.exp (-θ) * Real.exp (-(m : ℝ)) * Real.exp ((m : ℝ) + θ) := heq.symm
      _ ≤ Real.exp 2 * Real.exp (-θ) * Real.exp (-(m : ℝ))
            * Real.exp (Real.exp ((m : ℝ) + θ)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  calc ∑ m ∈ Finset.range j, blockWeightSize θ m ^ 2
      ≤ ∑ m ∈ Finset.range j, Real.exp 2 * Real.exp (-θ) * Real.exp (-(m : ℝ)) :=
        Finset.sum_le_sum fun m _ => hb m
    _ = Real.exp 2 * Real.exp (-θ) * ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp 2 * Real.exp (-θ) * 2 := mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) hc
    _ = 2 * Real.exp 2 * Real.exp (-θ) := by ring

/-! ### The first power of the block weight, summed

Combining the drift ingredients needs the *errors* of the one- and two-point tilted means summed
over blocks, not just their main terms.  At Harper's weights all three moduli agree, so the
two-point error is `800∑_{p∈B_m}‖w_p‖³ ≤ 800κ_m S_m` with `κ_m = blockWeightSize θ m` and
`S_m = ∑‖w_p‖² ≤ e²(1+…)`, and the one-point error is smaller still; so what is wanted is
`∑_m κ_m`.

`RMF.sum_blockWeightSize_sq_le` does the square; the same argument does the first power:
`κ_m = e·e^{-e^{m+θ}/2}`, and the crude `e^{m+θ} ≥ m+θ` leaves a geometric series of ratio
`e^{-1/2}`. -/

/-- `κ_m ≤ e\,e^{-θ/2}e^{-m/2}` — the first-power analogue of the bound inside
`RMF.sum_blockWeightSize_sq_le`. -/
lemma blockWeightSize_le_exp_neg (θ : ℝ) (m : ℕ) :
    blockWeightSize θ m ≤ Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((m : ℝ) / 2)) := by
  have hsqrt : ∀ x : ℝ, Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    intro x
    rw [show Real.exp x = Real.exp (x / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
    exact Real.sqrt_sq (Real.exp_pos _).le
  rw [blockWeightSize, blockScale, hsqrt, div_le_iff₀ (Real.exp_pos _)]
  have hmono : ((m : ℝ) + θ) / 2 ≤ Real.exp ((m : ℝ) + θ) / 2 := by
    linarith [Real.add_one_le_exp ((m : ℝ) + θ)]
  calc Real.exp 1
      = Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((m : ℝ) / 2))
          * Real.exp (((m : ℝ) + θ) / 2) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        rw [show -(θ / 2) + (-((m : ℝ) / 2) + ((m : ℝ) + θ) / 2) = 0 by ring, Real.exp_zero,
          mul_one]
    _ ≤ Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((m : ℝ) / 2))
          * Real.exp (Real.exp ((m : ℝ) + θ) / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hmono) (by positivity)

/-- **The block weights are summable above a shift**, with a geometric tail in `r`. -/
lemma sum_blockWeightSize_shift_le (θ : ℝ) (r j : ℕ) :
    (∑ m ∈ Finset.range j, blockWeightSize θ (m + r))
      ≤ Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := by
  have he0 : (0 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := Real.exp_pos _
  have he1 : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hpow : ∀ m : ℕ, Real.exp (-(1 / 2 : ℝ)) ^ m = Real.exp (-((m : ℝ) / 2)) := by
    intro m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb : ∀ m ∈ Finset.range j, blockWeightSize θ (m + r)
      ≤ Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
        * Real.exp (-(1 / 2 : ℝ)) ^ m := by
    intro m _
    refine le_trans (blockWeightSize_le_exp_neg θ (m + r)) (le_of_eq ?_)
    rw [hpow m]
    have hcast : ((m + r : ℕ) : ℝ) = (m : ℝ) + (r : ℝ) := by push_cast; ring
    rw [hcast]
    simp only [← Real.exp_add]
    congr 1
    ring
  have hgeo : (∑ m ∈ Finset.range j, Real.exp (-(1 / 2 : ℝ)) ^ m)
      ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := by
    have hsummable : Summable (fun m : ℕ => Real.exp (-(1 / 2 : ℝ)) ^ m) :=
      summable_geometric_of_lt_one he0.le he1
    calc (∑ m ∈ Finset.range j, Real.exp (-(1 / 2 : ℝ)) ^ m)
        ≤ ∑' m : ℕ, Real.exp (-(1 / 2 : ℝ)) ^ m :=
          hsummable.sum_le_tsum _ (fun m _ => by positivity)
      _ = (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ := tsum_geometric_of_lt_one he0.le he1
  calc (∑ m ∈ Finset.range j, blockWeightSize θ (m + r))
      ≤ ∑ m ∈ Finset.range j, Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * Real.exp (-(1 / 2 : ℝ)) ^ m := Finset.sum_le_sum hb
    _ = Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * ∑ m ∈ Finset.range j, Real.exp (-(1 / 2 : ℝ)) ^ m := by rw [← Finset.mul_sum]
    _ ≤ Real.exp 1 * Real.exp (-(θ / 2)) * Real.exp (-((r : ℝ) / 2))
          * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)

/-- The Mertens error at block `m`, in geometric form: `60/log x_m = 60e^{-(1+θ)}e^{-m}`. -/
lemma sixty_div_log_blockScale (θ : ℝ) (m : ℕ) :
    (60 : ℝ) / Real.log (blockScale θ (m + 1))
      = 60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))) := by
  have hL : Real.log (blockScale θ (m + 1)) = Real.exp (1 + θ) * Real.exp ((m : ℝ)) := by
    rw [log_blockScale, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hL, div_eq_mul_inv, mul_inv, ← Real.exp_neg, ← Real.exp_neg]

/-- **The drift, summed** (what Proposition 5 asks for): for `θ ≥ 5`, `j ≤ n + 1` and
`|σ|·log x_{n+1} ≤ 1`, `|∑_{m<j} blockMean_m - j| ≤ 4e² + 120e²e^{-(1+θ)} + 4e²·e²e^{-θ}`, a bound
depending on `θ` only.  The tilt term decays geometrically downwards from the top block
(`RMF.sum_exp_sub_le`), the Mertens term upwards from the bottom (`RMF.sum_exp_neg_nat_le`), and the
tilted mean's error doubly exponentially (`RMF.sum_blockWeightSize_sq_le`). -/
theorem abs_sum_blockMean_sub_le (hX : IsSteinhausPrimeValues X μ) {s : ℂ} {θ σ : ℝ} {n j : ℕ}
    (hθ3 : (5 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1) :
    |(∑ m ∈ Finset.range j, blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) - (j : ℝ)|
      ≤ 4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ))
        + 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ)) := by
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have he2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have h16 : (14 : ℝ) + 2 * 1 ≤ Real.exp θ := by
    have he1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h5 : (16 : ℝ) ≤ Real.exp 5 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 5)
        (by norm_num) he1.le (by norm_num)
    have h5θ : Real.exp 5 ≤ Real.exp θ := Real.exp_le_exp.2 hθ3
    linarith
  have hblock : ∀ m ∈ Finset.range j,
      |blockMean X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
          (primeBlockSub θ m) - 1|
        ≤ 2 * Real.exp 2 * Real.exp ((m : ℝ) - n)
          + 60 * Real.exp 2 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))
          + 2 * Real.exp 2 * blockWeightSize θ m ^ 2 := by
    intro m hm
    have hmj : m < j := Finset.mem_range.1 hm
    have hmn : m ≤ n := by omega
    have hmθ : (5 : ℝ) ≤ (m : ℝ) + θ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hη0 : (0 : ℝ) ≤ Real.exp ((m : ℝ) - n) := (Real.exp_pos _).le
    have hη1 : Real.exp ((m : ℝ) - n) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    have hmain := abs_blockMean_sub_one_le hX hmθ hmn hres hη0
      (scale_cond_of_le hη1 h16) (sigma_le_exp_sub θ σ hσ)
    rw [sixty_div_log_blockScale] at hmain
    have hle2 : Real.exp (2 * Real.exp ((m : ℝ) - n)) ≤ Real.exp 2 :=
      Real.exp_le_exp.2 (by linarith)
    have hlin := exp_sub_one_le_mul_exp (2 * Real.exp ((m : ℝ) - n))
    have hk0 : (0 : ℝ) ≤ blockWeightSize θ m ^ 2 := sq_nonneg _
    have hd0 : (0 : ℝ) ≤ Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)) := by positivity
    -- the tilted mean's error, back in terms of the block weight size
    have hbsq : blockWeightSize θ m ^ 2 = Real.exp 2 / blockScale θ m := by
      rw [blockWeightSize, div_pow, Real.sq_sqrt (blockScale_pos θ m).le,
        ← Real.exp_nat_mul]
      norm_num
    have hthird : 2 * Real.exp (4 * Real.exp ((m : ℝ) - n)) / blockScale θ m
        ≤ 2 * Real.exp 2 * blockWeightSize θ m ^ 2 := by
      rw [hbsq]
      have h4 : Real.exp (4 * Real.exp ((m : ℝ) - n)) ≤ Real.exp 4 :=
        Real.exp_le_exp.2 (by linarith)
      have he4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      have heq : 2 * Real.exp 2 * (Real.exp 2 / blockScale θ m)
          = 2 * (Real.exp 2 * Real.exp 2) / blockScale θ m := by ring
      rw [heq, ← he4]
      exact div_le_div_of_nonneg_right (by linarith) (blockScale_pos θ m).le
    nlinarith [hmain, hle2, hlin, hη0, hk0, hd0, he2, hthird]
  have hsplit : (∑ m ∈ Finset.range j, blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) - (j : ℝ)
      = ∑ m ∈ Finset.range j, (blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hd0 : (0 : ℝ) < Real.exp (-(1 + θ)) := Real.exp_pos _
  have hA : ∑ m ∈ Finset.range j, 2 * Real.exp 2 * Real.exp ((m : ℝ) - n)
      ≤ 4 * Real.exp 2 := by
    rw [← Finset.mul_sum]
    calc 2 * Real.exp 2 * ∑ m ∈ Finset.range j, Real.exp ((m : ℝ) - n)
        ≤ 2 * Real.exp 2 * 2 :=
          mul_le_mul_of_nonneg_left (sum_exp_sub_le hj) (by positivity)
      _ = 4 * Real.exp 2 := by ring
  have hB : ∑ m ∈ Finset.range j,
        60 * Real.exp 2 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
    have hre : ∀ m : ℕ, 60 * Real.exp 2 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))
        = 60 * Real.exp 2 * Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)) := fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => hre m), ← Finset.mul_sum]
    calc 60 * Real.exp 2 * Real.exp (-(1 + θ)) * ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ))
        ≤ 60 * Real.exp 2 * Real.exp (-(1 + θ)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) (by positivity)
      _ = 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by ring
  have hC : ∑ m ∈ Finset.range j, 2 * Real.exp 2 * blockWeightSize θ m ^ 2
      ≤ 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ)) := by
    rw [← Finset.mul_sum]
    calc 2 * Real.exp 2 * ∑ m ∈ Finset.range j, blockWeightSize θ m ^ 2
        ≤ 2 * Real.exp 2 * (2 * Real.exp 2 * Real.exp (-θ)) :=
          mul_le_mul_of_nonneg_left (sum_blockWeightSize_sq_le θ j) (by positivity)
      _ = 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ)) := by ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [hA, hB, hC]

/-- **The summed drift at a general tilt scale**: for `θ ≥ 5`, `j ≤ n + 1`, `σ ≥ 0`, `0 ≤ K`,
`14 + 2K ≤ e^θ` and `|σ|·log x_{n+1} ≤ K`,
`|∑_{m<j} blockMean_m - j| ≤ 45√K + 120e²e^{-(1+θ)} + 4e^{4K}·e²e^{-θ}`, the analogue of
`RMF.abs_sum_blockMean_sub_le`.  The per-block deficit is at most `15·min(η_m, 1)` with
`η_m = Ke^{m-n}`: below the tilt scale the two-sided estimate linearises, above it
`RMF.abs_blockMean_le_of_le` bounds the block outright; `min(x,1) ≤ √x` sums it to `O(√K)`. -/
theorem abs_sum_blockMean_sub_le_of_le (hX : IsSteinhausPrimeValues X μ) {s : ℂ} {θ σ K : ℝ}
    {n j : ℕ} (hθ3 : (5 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hK0 : 0 ≤ K) (hsc : 14 + 2 * K ≤ Real.exp θ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ m ∈ Finset.range j, blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) - (j : ℝ)|
      ≤ 45 * √K + 120 * Real.exp 2 * Real.exp (-(1 + θ))
        + 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ)) := by
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have he2u : Real.exp 2 ≤ 7.4 := by
    have hrw : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hrw]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hblock : ∀ m ∈ Finset.range j,
      |blockMean X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
          (primeBlockSub θ m) - 1|
        ≤ 15 * min (K * Real.exp ((m : ℝ) - n)) 1
          + Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
          + 2 * Real.exp (4 * K) * blockWeightSize θ m ^ 2 := by
    intro m hm
    have hmj : m < j := Finset.mem_range.1 hm
    have hmn : m ≤ n := by omega
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmθ : (5 : ℝ) ≤ (m : ℝ) + θ := by linarith
    have hem0 : (0 : ℝ) < Real.exp ((m : ℝ) - n) := Real.exp_pos _
    have hem1 : Real.exp ((m : ℝ) - n) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    have hη0 : (0 : ℝ) ≤ K * Real.exp ((m : ℝ) - n) := by positivity
    have hηK : K * Real.exp ((m : ℝ) - n) ≤ K := by nlinarith
    have hd0 : (0 : ℝ) ≤ 60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))) := by positivity
    -- the scale condition at this block, from the one at the top
    have hscm : (14 : ℝ) + 2 * (K * Real.exp ((m : ℝ) - n)) ≤ Real.exp ((m : ℝ) + θ) := by
      have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) := Real.exp_le_exp.2 (by linarith)
      linarith
    have hbs0 : (0 : ℝ) < blockScale θ m := blockScale_pos θ m
    have hwn : ∀ p ∈ primeBlockSub θ m,
        ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
      fun p _ => norm_sq_prime_cpow_neg p hres
    rcases le_or_gt (K * Real.exp ((m : ℝ) - n)) 1 with hcase | hcase
    · -- the tilt is mild here: the two-sided block estimate, linearised
      have hmain := abs_blockMean_sub_one_le hX hmθ hmn hres hη0 hscm
        (sigma_le_mul_exp_sub θ σ K hσ)
      rw [sixty_div_log_blockScale] at hmain
      have hle2 : Real.exp (2 * (K * Real.exp ((m : ℝ) - n))) ≤ Real.exp 2 :=
        Real.exp_le_exp.2 (by linarith)
      have hlin := exp_sub_one_le_mul_exp (2 * (K * Real.exp ((m : ℝ) - n)))
      have hthird : 2 * Real.exp (4 * (K * Real.exp ((m : ℝ) - n))) / blockScale θ m
          ≤ 2 * Real.exp (4 * K) * blockWeightSize θ m ^ 2 := by
        rw [blockWeightSize_sq]
        have heq : 2 * Real.exp (4 * K) * (Real.exp 2 / blockScale θ m)
            = 2 * (Real.exp (4 * K) * Real.exp 2) / blockScale θ m := by ring
        rw [heq]
        refine div_le_div_of_nonneg_right ?_ hbs0.le
        have h4 : Real.exp (4 * (K * Real.exp ((m : ℝ) - n))) ≤ Real.exp (4 * K) :=
          Real.exp_le_exp.2 (by nlinarith)
        nlinarith [h4, he2, Real.exp_pos (4 * K)]
      rw [min_eq_left hcase]
      nlinarith [hmain, hle2, hlin, hη0, hd0, he2u, hthird]
    · -- the tilt has thinned the block: the σ-uniform drift bound is all that is needed
      have hup := abs_blockMean_le_of_le hX hmθ hmn hres hσ0 hscm
        (sigma_le_mul_exp_sub θ σ K hσ) hwn
      rw [sixty_div_log_blockScale] at hup
      have habs : |blockMean X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m) - 1|
          ≤ |blockMean X μ (blockCutoff θ n) s (fun p => ((p : ℕ) : ℂ) ^ (-s))
            (primeBlockSub θ m)| + 1 := by
        have h := abs_sub (a := blockMean X μ (blockCutoff θ n) s
          (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) (b := (1 : ℝ))
        simpa using h
      have hthird : 2 * Real.exp (2 * (K * Real.exp ((m : ℝ) - n))) / blockScale θ m
          ≤ 2 * Real.exp (4 * K) * blockWeightSize θ m ^ 2 := by
        rw [blockWeightSize_sq]
        have heq : 2 * Real.exp (4 * K) * (Real.exp 2 / blockScale θ m)
            = 2 * (Real.exp (4 * K) * Real.exp 2) / blockScale θ m := by ring
        rw [heq]
        refine div_le_div_of_nonneg_right ?_ hbs0.le
        have h4 : Real.exp (2 * (K * Real.exp ((m : ℝ) - n))) ≤ Real.exp (4 * K) :=
          Real.exp_le_exp.2 (by nlinarith)
        nlinarith [h4, he2, Real.exp_pos (4 * K)]
      rw [min_eq_right hcase.le]
      nlinarith [hup, habs, hd0, he2, hthird]
  have hsplit : (∑ m ∈ Finset.range j, blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m)) - (j : ℝ)
      = ∑ m ∈ Finset.range j, (blockMean X μ (blockCutoff θ n) s
        (fun p => ((p : ℕ) : ℂ) ^ (-s)) (primeBlockSub θ m) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hA : ∑ m ∈ Finset.range j, 15 * min (K * Real.exp ((m : ℝ) - n)) 1 ≤ 45 * √K := by
    have hterm : ∀ m ∈ Finset.range j,
        15 * min (K * Real.exp ((m : ℝ) - n)) 1
          ≤ 15 * √K * Real.exp (((m : ℝ) - n) / 2) := by
      intro m _
      have h := min_one_le_sqrt (show (0 : ℝ) ≤ K * Real.exp ((m : ℝ) - n) by positivity)
      rw [Real.sqrt_mul hK0, sqrt_exp] at h
      nlinarith [h]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    calc 15 * √K * ∑ m ∈ Finset.range j, Real.exp (((m : ℝ) - n) / 2)
        ≤ 15 * √K * 3 :=
          mul_le_mul_of_nonneg_left (sum_exp_half_sub_le hj) (by positivity)
      _ = 45 * √K := by ring
  have hB : ∑ m ∈ Finset.range j,
        Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by
    have hre : ∀ m : ℕ, Real.exp 2 * (60 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ))))
        = 60 * Real.exp 2 * Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)) := fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => hre m), ← Finset.mul_sum]
    calc 60 * Real.exp 2 * Real.exp (-(1 + θ)) * ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ))
        ≤ 60 * Real.exp 2 * Real.exp (-(1 + θ)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) (by positivity)
      _ = 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by ring
  have hC : ∑ m ∈ Finset.range j, 2 * Real.exp (4 * K) * blockWeightSize θ m ^ 2
      ≤ 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ)) := by
    rw [← Finset.mul_sum]
    calc 2 * Real.exp (4 * K) * ∑ m ∈ Finset.range j, blockWeightSize θ m ^ 2
        ≤ 2 * Real.exp (4 * K) * (2 * Real.exp 2 * Real.exp (-θ)) :=
          mul_le_mul_of_nonneg_left (sum_blockWeightSize_sq_le θ j) (by positivity)
      _ = 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ)) := by ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [hA, hB, hC]

/-! ### The third-moment sum on a block

The one hypothesis of the block comparison that is not arithmetic.  `‖w_p‖³ = p^{-3/2-3σ}` at
Harper's weights, and `RMF.sum_prime_Ioc_rpow_cube_le` bounds that sum over a range; all that is
left is the indexing transfer. -/

/-- Hence `‖u‖³ = a^{-3/2-3σ}` — the summand of the third-moment bound. -/
lemma norm_cube_eq_rpow {u : ℂ} {a σ : ℝ} (ha : 0 < a)
    (hu : ‖u‖ ^ 2 = a ^ (-1 - 2 * σ)) :
    ‖u‖ ^ 3 = a ^ (-(3 / 2) - 3 * σ) := by
  have h1 := norm_eq_rpow_of_sq_eq ha hu
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hu, h1, ← Real.rpow_add ha]
  congr 1
  ring

/-- **`hTb`, discharged.**  `∑_{p∈B_m} ‖w_p‖³ ≤ e³·8log4/(√(x_{m-1}) log x_{m-1})`, where
`x_{m-1} = blockScale θ m` is the *bottom* of the block — the sum is dominated by its smallest
primes.

This is what makes the numerical condition hold with room: the bound is
`≍ e^{-e^{m+θ}/2}`, doubly exponentially small, against an `εq` that is only singly so. -/
theorem sum_norm_cube_primeBlockSub_le {θ σ : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3
      ≤ Real.exp 3 * (8 * Real.log 4
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))) := by
  have hx2 : (2 : ℝ) ≤ blockScale θ m := by
    rw [blockScale]
    have h1 : (1 : ℝ) ≤ Real.exp ((m : ℝ) + θ) := Real.one_le_exp (by linarith)
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp (Real.exp ((m : ℝ) + θ)) := Real.exp_le_exp.2 h1
  have hxy : blockScale θ m ≤ blockScale θ (m + 1) := blockScale_mono θ (by omega)
  have hcube : ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 3 = ((p : ℕ) : ℝ) ^ (-(3 / 2) - 3 * σ) := fun q hq =>
    norm_cube_eq_rpow (by exact_mod_cast q.2.pos) (hwn q hq)
  have hrw : ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3
      = ∑ p ∈ {p ∈ Finset.Ioc ⌊blockScale θ m⌋₊ ⌊blockScale θ (m + 1)⌋₊ | Nat.Prime p},
          (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
    rw [Finset.sum_congr rfl hcube, primeBlockSub, harperBlock, blockScale_rpow_inv_exp_one,
      sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-(3 / 2) - 3 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  exact sum_prime_Ioc_rpow_cube_le hx2 hxy hσ

/-- **The third-moment sum on a block, at a general tilt scale.**

`RMF.sum_norm_cube_primeBlockSub_le` is the case `η = 1`.  The scale costs `e^{3η}` against a
denominator that is doubly exponential in the block index, so it is never the binding term. -/
theorem sum_norm_cube_primeBlockSub_le_of_le {θ σ η : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3
      ≤ Real.exp (3 * η) * (8 * Real.log 4
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))) := by
  have hx2 : (2 : ℝ) ≤ blockScale θ m := by
    rw [blockScale]
    have h1 : (1 : ℝ) ≤ Real.exp ((m : ℝ) + θ) := Real.one_le_exp (by linarith)
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp (Real.exp ((m : ℝ) + θ)) := Real.exp_le_exp.2 h1
  have hxy : blockScale θ m ≤ blockScale θ (m + 1) := blockScale_mono θ (by omega)
  have hcube : ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 3 = ((p : ℕ) : ℝ) ^ (-(3 / 2) - 3 * σ) := fun q hq =>
    norm_cube_eq_rpow (by exact_mod_cast q.2.pos) (hwn q hq)
  have hrw : ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3
      = ∑ p ∈ {p ∈ Finset.Ioc ⌊blockScale θ m⌋₊ ⌊blockScale θ (m + 1)⌋₊ | Nat.Prime p},
          (p : ℝ) ^ (-(3 / 2) - 3 * σ) := by
    rw [Finset.sum_congr rfl hcube, primeBlockSub, harperBlock, blockScale_rpow_inv_exp_one,
      sum_primesIcoSub _ _ fun q => (q : ℝ) ^ (-(3 / 2) - 3 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  exact sum_prime_Ioc_rpow_cube_le_of_le hx2 hxy hσ

/-! ### The margin

The numerical condition holds by an enormous factor, and it is worth isolating exactly *why*: the
swap error is doubly exponential in the block index while everything it must beat is at worst
polynomial.  Writing `E = e^{m+θ} = log x_m`, the gain is `exp((8-e)E/64) ≥ exp(5E/64)`, and
`E ≥ e¹⁴` already makes that `exp(93750)`.

`θ ≥ 0` is what makes this uniform in `m`: it gives `E ≥ e^m` as well as `E ≥ e¹⁴`, so the gain
grows doubly exponentially while the loss `(m+1)²` grows polynomially.  Without it `θ` could be very
negative for large `m`, pinning `E` at `e¹⁴`, and the inequality would fail. -/

private lemma exp_seven_ge : (1096 : ℝ) ≤ Real.exp 7 := by
  have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 7)
    (by norm_num) he.le (by norm_num)

private lemma exp_fourteen_ge : (1200000 : ℝ) ≤ Real.exp 14 := by
  have h7 := exp_seven_ge
  have hmul : Real.exp 7 * Real.exp 7 = Real.exp 14 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [h7, hmul]

private lemma exp_eleven_ge : (29000 : ℝ) ≤ Real.exp 11 := by
  have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 11)
    (by norm_num) he.le (by norm_num)

/-- **The margin.**  `457 e²⁵ (m+1)² ≤ exp(5E/64)` at `E = e^{m+θ}`.

The left side is everything the swap error carries in front of its exponential; the right side is
what separates the two exponents.  The proof is `457 ≤ e⁷`, `(m+1)² ≤ e^{2m}`, so the left side is
at most `e^{32+2m}`, against `5E/64 ≥ 46875 + (5/128)(1 + m/2)²` — a quadratic in `m` with no real
root. -/
lemma blockNum_margin {θ : ℝ} {m : ℕ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ) (hθ0 : (0 : ℝ) ≤ θ) :
    457 * Real.exp 25 * ((m : ℝ) + 1) ^ 2
      ≤ Real.exp (5 / 64 * Real.exp ((m : ℝ) + θ)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hEbig : (1200000 : ℝ) ≤ Real.exp ((m : ℝ) + θ) :=
    le_trans exp_fourteen_ge (Real.exp_le_exp.2 hmθ)
  have hEm : Real.exp (m : ℝ) ≤ Real.exp ((m : ℝ) + θ) :=
    Real.exp_le_exp.2 (by linarith)
  have hhalf : 1 + (m : ℝ) / 2 ≤ Real.exp ((m : ℝ) / 2) := by
    linarith [Real.add_one_le_exp ((m : ℝ) / 2)]
  have hsq : (1 + (m : ℝ) / 2) ^ 2 ≤ Real.exp (m : ℝ) := by
    have hmul : Real.exp ((m : ℝ) / 2) * Real.exp ((m : ℝ) / 2) = Real.exp (m : ℝ) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [hhalf, (Real.exp_pos ((m : ℝ) / 2)).le, hm0]
  -- the left side is at most `e^{32 + 2m}`
  have hm1 : (m : ℝ) + 1 ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
  have h2m : Real.exp (m : ℝ) ^ 2 = Real.exp (2 * (m : ℝ)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h32 : Real.exp 7 * Real.exp 25 = Real.exp 32 := by
    rw [← Real.exp_add]
    norm_num
  have hlhs : 457 * Real.exp 25 * ((m : ℝ) + 1) ^ 2 ≤ Real.exp (32 + 2 * (m : ℝ)) := by
    have hsq' : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (2 * (m : ℝ)) := by
      rw [← h2m]
      nlinarith [hm1, hm0]
    have h1 : (457 : ℝ) ≤ Real.exp 7 := le_trans (by norm_num) exp_seven_ge
    have hstep : 457 * Real.exp 25 ≤ Real.exp 7 * Real.exp 25 :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos 25).le
    calc 457 * Real.exp 25 * ((m : ℝ) + 1) ^ 2
        ≤ 457 * Real.exp 25 * Real.exp (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ ≤ Real.exp 7 * Real.exp 25 * Real.exp (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
      _ = Real.exp (32 + 2 * (m : ℝ)) := by rw [h32, ← Real.exp_add]
  refine le_trans hlhs (Real.exp_le_exp.2 ?_)
  nlinarith [hEbig, hEm, hsq, hm0, sq_nonneg ((m : ℝ) - 1000)]

/-! ### The numerical balance

`hnum` says the Lindeberg gain beats the smoothing loss, and `RMF.blockNum_le_of_le` discharges
it; the other hypotheses of `RMF.exists_isWindowComparison_primeBlockSub` are discharged by
`RMF.sum_third_moment_block_le` with `RMF.sum_norm_cube_primeBlockSub_le` (`hTb`),
`RMF.le_toReal_measure_Ioc_blockGaussian_of_thr` (`hqlow`) and `RMF.blockMatchedVar_concrete`
(`hv`).

With `E = e^{m+θ} = log x_m`, the swap error is `T^{1/4} ≍ exp(-E/8)` (`T ≍ x_m^{-1/2}`, `x_m` the
bottom of the block), and what it must beat is `ε_m q_m ≍ exp(-(1/100 + 9/1600)·eE) = exp(-eE/64)`
at Harper's `ε_m = x_{m+1}^{-1/100}` and the window mass `q_m` of `RMF.blockQ`.  Since `1/8 > e/64`
the gain wins by `exp(5E/64)`, which is `exp(93750)` at `m + θ = 14`.  `θ ≥ 0` is needed: it gives
`E ≥ e^m` as well as `E ≥ e¹⁴`, so the gain is doubly exponential in `m` while the window factor
`(m+1)^{-2}` is polynomial. -/

/-- **The numerical condition of Lemma 3, for any third-moment constant `0 ≤ Kb ≤ e^{100}`**: for
`m + θ ≥ 14`, `θ ≥ 0`, `V ≥ 1/16` and `0 ≤ T ≤ Kb/(√x_m log x_m)`,
`(450 + 4/√(2πV))·T^{1/4} ≤ x_{m+1}^{-1/100}·(m+1)^{-2}·x_{m+1}^{-9/1600}`.  With `E = log x_m`:
`T^{1/4} ≤ e²⁵e^{-E/8}`, the coefficient is at most `457`, the right side is
`(m+1)^{-2}e^{-eE/64}`, and `1/8 - e/64 ≥ 5/64`; `RMF.blockNum_margin` absorbs `457e²⁵(m+1)²`. -/
theorem blockNum_le_of_le {θ Kb : ℝ} {m : ℕ} {V T : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hθ0 : (0 : ℝ) ≤ θ) (hV : 1 / 16 ≤ V) (hT0 : 0 ≤ T)
    (hKb0 : 0 ≤ Kb) (hKb : Kb ≤ Real.exp 100)
    (hT : T ≤ Kb / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))) :
    (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
      ≤ blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * (1 / ((m : ℝ) + 1) ^ 2 * blockScale θ (m + 1) ^ (-(9 : ℝ) / 1600)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set E := Real.exp ((m : ℝ) + θ) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hE1 : (1 : ℝ) ≤ E := Real.one_le_exp (by linarith)
  -- the two scales, as exponentials
  have hXm : blockScale θ m = Real.exp E := by rw [blockScale]
  have hLm : Real.log (blockScale θ m) = E := log_blockScale θ m
  have hXm1 : blockScale θ (m + 1) = Real.exp (Real.exp 1 * E) := by
    have h : Real.exp 1 * E = Real.exp (((m + 1 : ℕ) : ℝ) + θ) := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [h, blockScale]
  have hsq : Real.sqrt (blockScale θ m) = Real.exp (E / 2) := by
    rw [hXm, ← Real.exp_half]
  -- `T ≤ Kb e^{-E/2}`, discarding the `log x_m` in the denominator
  have hT2 : T ≤ Kb * Real.exp (-(E / 2)) := by
    refine le_trans hT ?_
    rw [hsq, hLm, Real.exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (Real.exp_pos (E / 2))]
    nlinarith [mul_nonneg (mul_nonneg hKb0 (Real.exp_pos (E / 2)).le)
      (sub_nonneg.2 hE1)]
  -- `T^{1/4} ≤ e²⁵ e^{-E/8}`
  have hquarter : T ^ (1 / 4 : ℝ) ≤ Real.exp 25 * Real.exp (-(E / 8)) := by
    have h1 : T ^ (1 / 4 : ℝ) ≤ (Kb * Real.exp (-(E / 2))) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hT0 hT2 (by norm_num)
    have h2 : (Kb * Real.exp (-(E / 2))) ^ (1 / 4 : ℝ)
        = Kb ^ (1 / 4 : ℝ) * Real.exp (-(E / 8)) := by
      rw [Real.mul_rpow hKb0 (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      ring
    have h3 : Kb ^ (1 / 4 : ℝ) ≤ Real.exp 25 := by
      have h := Real.rpow_le_rpow hKb0 hKb (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [show Real.exp 100 ^ (1 / 4 : ℝ) = Real.exp 25 by
        rw [← Real.exp_mul]; congr 1; ring] at h
    calc T ^ (1 / 4 : ℝ) ≤ Kb ^ (1 / 4 : ℝ) * Real.exp (-(E / 8)) := by rw [← h2]; exact h1
      _ ≤ Real.exp 25 * Real.exp (-(E / 8)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  -- the coefficient, from `V ≥ 1/16` and `π > 3`
  have hcoef : 450 + 4 / Real.sqrt (2 * Real.pi * V) ≤ 457 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h2pv : (3 / 8 : ℝ) ≤ 2 * Real.pi * V := by nlinarith [hV, hpi]
    have hs : (4 / 7 : ℝ) ≤ Real.sqrt (2 * Real.pi * V) := by
      have h := Real.sqrt_le_sqrt (show ((4 / 7 : ℝ)) ^ 2 ≤ 2 * Real.pi * V by nlinarith)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 7)] at h
    have hs0 : (0 : ℝ) < Real.sqrt (2 * Real.pi * V) := by linarith
    have h7 : 4 / Real.sqrt (2 * Real.pi * V) ≤ 7 := by
      rw [div_le_iff₀ hs0]
      linarith
    linarith
  -- the right-hand side, as a single exponential
  have hprod : blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(9 : ℝ) / 1600)
      = Real.exp (-(Real.exp 1 * E / 64)) := by
    rw [← Real.rpow_add (blockScale_pos θ (m + 1)), hXm1, ← Real.exp_mul]
    congr 1
    ring
  rw [show blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * (1 / ((m : ℝ) + 1) ^ 2 * blockScale θ (m + 1) ^ (-(9 : ℝ) / 1600))
      = blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(9 : ℝ) / 1600) * (1 / ((m : ℝ) + 1) ^ 2) from by ring,
    hprod]
  -- the margin closes it
  have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hexpcmp : Real.exp (5 / 64 * E) ≤ Real.exp (E / 8 - Real.exp 1 * E / 64) :=
    Real.exp_le_exp.2 (by nlinarith [he3, hE0])
  have hkey : 457 * Real.exp 25 * ((m : ℝ) + 1) ^ 2 * Real.exp (-(E / 8))
      ≤ Real.exp (-(Real.exp 1 * E / 64)) := by
    have hmul : Real.exp (E / 8 - Real.exp 1 * E / 64) * Real.exp (-(E / 8))
        = Real.exp (-(Real.exp 1 * E / 64)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 457 * Real.exp 25 * ((m : ℝ) + 1) ^ 2 * Real.exp (-(E / 8))
        ≤ Real.exp (E / 8 - Real.exp 1 * E / 64) * Real.exp (-(E / 8)) :=
          mul_le_mul_of_nonneg_right (le_trans (blockNum_margin hmθ hθ0) hexpcmp)
            (Real.exp_pos _).le
      _ = Real.exp (-(Real.exp 1 * E / 64)) := hmul
  have hL : (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
      ≤ 457 * (Real.exp 25 * Real.exp (-(E / 8))) := by
    have hT4 : (0 : ℝ) ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT0 _
    calc (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
        ≤ 457 * T ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hcoef hT4
      _ ≤ 457 * (Real.exp 25 * Real.exp (-(E / 8))) :=
          mul_le_mul_of_nonneg_left hquarter (by norm_num)
  refine le_trans hL ?_
  rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  nlinarith [hkey]

/-- **The numerical condition of Lemma 3 at any tilt bound, with the block offset existential**:
for `E₀, G ≥ 0` there is `θ₀` such that for `θ ≥ θ₀`, `0 ≤ η ≤ E₀`, `V ≥ e^{-2η}/4`,
`0 ≤ Kb ≤ e^{4G}` and `0 ≤ T ≤ Kb/(√x_m log x_m)`, the numerical condition holds at the window
exponent `3/100`.  `RMF.blockNum_le_of_le` fixes `Kb ≤ e^{100}`, which at tilt scale `η` (where
`Kb ≈ 24192e^{3η}`) would cap `η` near `30`; here the price is paid in `θ₀`. -/
theorem exists_blockNum_le_of_scale (E₀ G : ℝ) (hE₀ : 0 ≤ E₀) (hG : 0 ≤ G) :
    ∃ θ₀ : ℝ, ∀ (θ η V T Kb : ℝ) (m : ℕ), θ₀ ≤ θ → 0 ≤ η → η ≤ E₀ →
      Real.exp (-(2 * η)) / 4 ≤ V → 0 ≤ T → 0 ≤ Kb → Kb ≤ Real.exp (4 * G) →
      T ≤ Kb / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)) →
        (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
          ≤ blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
            * (1 / ((m : ℝ) + 1) ^ 2 * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100)) := by
  have he1u : Real.exp 1 ≤ 2.7183 := by linarith [Real.exp_one_lt_d9]
  have hpos : (0 : ℝ) < 200 * (10 + E₀ + G) := by linarith
  refine ⟨Real.log (200 * (10 + E₀ + G)), ?_⟩
  intro θ η V T Kb m hθ hη0 hηE hV hT0 hKb0 hKb hT
  have hexpθ : 200 * (10 + E₀ + G) ≤ Real.exp θ := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hθ
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hθ0 : (0 : ℝ) ≤ θ := by
    by_contra hcon
    push Not at hcon
    have h1 : Real.exp θ < Real.exp 0 := Real.exp_lt_exp.2 hcon
    rw [Real.exp_zero] at h1
    linarith
  set Eb := Real.exp ((m : ℝ) + θ) with hEdef
  have hE0 : (0 : ℝ) < Eb := Real.exp_pos _
  -- `E_m ≥ e^θ(1+m)`
  have hEsplit : Eb = Real.exp (m : ℝ) * Real.exp θ := by rw [hEdef, ← Real.exp_add]
  have hm1 : (1 : ℝ) + (m : ℝ) ≤ Real.exp (m : ℝ) := by
    linarith [Real.add_one_le_exp ((m : ℝ))]
  have hEge : (1 + (m : ℝ)) * Real.exp θ ≤ Eb := by
    rw [hEsplit]
    exact mul_le_mul_of_nonneg_right hm1 (Real.exp_pos _).le
  have hE1 : (1 : ℝ) ≤ Eb := Real.one_le_exp (by linarith)
  -- the two scales, as exponentials
  have hXm : blockScale θ m = Real.exp Eb := by rw [blockScale]
  have hLm : Real.log (blockScale θ m) = Eb := log_blockScale θ m
  have hXm1 : blockScale θ (m + 1) = Real.exp (Real.exp 1 * Eb) := by
    have h : Real.exp 1 * Eb = Real.exp (((m + 1 : ℕ) : ℝ) + θ) := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [h, blockScale]
  have hsq : Real.sqrt (blockScale θ m) = Real.exp (Eb / 2) := by
    rw [hXm, ← Real.exp_half]
  clear_value Eb
  -- `T ≤ Kb e^{-E/2}`
  have hT2 : T ≤ Kb * Real.exp (-(Eb / 2)) := by
    refine le_trans hT ?_
    rw [hsq, hLm, Real.exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (Real.exp_pos (Eb / 2))]
    nlinarith [mul_nonneg (mul_nonneg hKb0 (Real.exp_pos (Eb / 2)).le)
      (sub_nonneg.2 hE1)]
  -- `T^{1/4} ≤ e^G e^{-E/8}`
  have hquarter : T ^ (1 / 4 : ℝ) ≤ Real.exp G * Real.exp (-(Eb / 8)) := by
    have h1 : T ^ (1 / 4 : ℝ) ≤ (Kb * Real.exp (-(Eb / 2))) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hT0 hT2 (by norm_num)
    have h2 : (Kb * Real.exp (-(Eb / 2))) ^ (1 / 4 : ℝ)
        = Kb ^ (1 / 4 : ℝ) * Real.exp (-(Eb / 8)) := by
      rw [Real.mul_rpow hKb0 (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      ring
    have h3 : Kb ^ (1 / 4 : ℝ) ≤ Real.exp G := by
      have h := Real.rpow_le_rpow hKb0 hKb (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [show Real.exp (4 * G) ^ (1 / 4 : ℝ) = Real.exp G by
        rw [← Real.exp_mul]; congr 1; ring] at h
    calc T ^ (1 / 4 : ℝ) ≤ Kb ^ (1 / 4 : ℝ) * Real.exp (-(Eb / 8)) := by rw [← h2]; exact h1
      _ ≤ Real.exp G * Real.exp (-(Eb / 8)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  -- the coefficient, from `V ≥ e^{-2η}/4`
  have hη1 : (1 : ℝ) ≤ Real.exp η := Real.one_le_exp hη0
  have hen : Real.exp (-η) * Real.exp η = 1 := by
    rw [← Real.exp_add, show -η + η = 0 by ring, Real.exp_zero]
  have hcoef : 450 + 4 / Real.sqrt (2 * Real.pi * V) ≤ 454 * Real.exp η := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hrw : Real.exp (-(2 * η)) = Real.exp (-η) * Real.exp (-η) := by
      rw [← Real.exp_add]; ring_nf
    have hen0 : (0 : ℝ) < Real.exp (-η) := Real.exp_pos _
    have hsq2 : ((6 / 5 : ℝ) * Real.exp (-η)) ^ 2 = 36 / 25 * Real.exp (-(2 * η)) := by
      rw [mul_pow, pow_two (Real.exp (-η)), ← hrw]
      norm_num
    have h2pv : ((6 / 5 : ℝ) * Real.exp (-η)) ^ 2 ≤ 2 * Real.pi * V := by
      rw [hsq2]
      nlinarith [hV, hpi, Real.exp_pos (-(2 * η))]
    have hs : (6 / 5 : ℝ) * Real.exp (-η) ≤ Real.sqrt (2 * Real.pi * V) := by
      have h := Real.sqrt_le_sqrt h2pv
      rwa [Real.sqrt_sq (by positivity)] at h
    have hs0 : (0 : ℝ) < Real.sqrt (2 * Real.pi * V) := by linarith [hs, hen0]
    have h4 : 4 / Real.sqrt (2 * Real.pi * V) ≤ 4 * Real.exp η := by
      rw [div_le_iff₀ hs0]
      nlinarith [hs, hen, Real.exp_pos η]
    linarith
  -- the right-hand side, as a single exponential
  have hprod : blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100)
      = Real.exp (-(Real.exp 1 * Eb / 25)) := by
    rw [← Real.rpow_add (blockScale_pos θ (m + 1)), hXm1, ← Real.exp_mul]
    congr 1
    ring
  rw [show blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * (1 / ((m : ℝ) + 1) ^ 2 * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100))
      = blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(3 : ℝ) / 100) * (1 / ((m : ℝ) + 1) ^ 2) from by ring,
    hprod]
  -- the margin: `454 e^{η+G} (m+1)² ≤ e^{cE}` with `c = 1/8 - e/25 ≥ 0.0162`
  have hc : (0.0162 : ℝ) ≤ 1 / 8 - Real.exp 1 / 25 := by linarith
  have hcE : (0.0162 : ℝ) * Eb ≤ Eb / 8 - Real.exp 1 * Eb / 25 := by
    have h := mul_le_mul_of_nonneg_right hc hE0.le
    linarith
  have hhalf : (454 : ℝ) * Real.exp η * Real.exp G ≤ Real.exp (0.0081 * Eb) := by
    have hlog : Real.log 454 ≤ 7 := by
      have h7 : (1090 : ℝ) ≤ Real.exp 7 := by
        have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 7)
          (by norm_num) he.le (by norm_num)
      have hle : (454 : ℝ) ≤ Real.exp 7 := by linarith
      exact (Real.log_le_iff_le_exp (by norm_num)).2 hle
    have hrw : (454 : ℝ) * Real.exp η * Real.exp G
        = Real.exp (Real.log 454 + η + G) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 454)]
    rw [hrw]
    refine Real.exp_le_exp.2 ?_
    have hE : 200 * (10 + E₀ + G) ≤ Eb := by
      have hmul : (0 : ℝ) ≤ (m : ℝ) * Real.exp θ := mul_nonneg hm0 (Real.exp_pos θ).le
      linarith [hEge, hexpθ, hmul]
    linarith
  have hsqm : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (0.0081 * Eb) := by
    have h1 : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (2 * (m : ℝ)) := by
      have h2 : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (m : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      rwa [show Real.exp (m : ℝ) ^ 2 = Real.exp (2 * (m : ℝ)) by
        rw [pow_two, ← Real.exp_add]; congr 1; ring] at h2
    refine le_trans h1 (Real.exp_le_exp.2 ?_)
    have h3 : (2000 : ℝ) ≤ Real.exp θ := by linarith
    have hbig : (2000 : ℝ) * (1 + (m : ℝ)) ≤ Eb := by
      have hmul : (1 + (m : ℝ)) * 2000 ≤ (1 + (m : ℝ)) * Real.exp θ :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      linarith [hEge, hmul]
    linarith
  have hmargin : (454 : ℝ) * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2
      ≤ Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) := by
    have hmul : Real.exp (0.0081 * Eb) * Real.exp (0.0081 * Eb)
        = Real.exp (0.0162 * Eb) := by rw [← Real.exp_add]; ring_nf
    calc (454 : ℝ) * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2
        ≤ Real.exp (0.0081 * Eb) * Real.exp (0.0081 * Eb) :=
          mul_le_mul hhalf hsqm (by positivity) (Real.exp_pos _).le
      _ = Real.exp (0.0162 * Eb) := hmul
      _ ≤ Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) := Real.exp_le_exp.2 hcE
  have hkey : 454 * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2 * Real.exp (-(Eb / 8))
      ≤ Real.exp (-(Real.exp 1 * Eb / 25)) := by
    have hmul : Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) * Real.exp (-(Eb / 8))
        = Real.exp (-(Real.exp 1 * Eb / 25)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 454 * Real.exp η * Real.exp G * ((m : ℝ) + 1) ^ 2 * Real.exp (-(Eb / 8))
        ≤ Real.exp (Eb / 8 - Real.exp 1 * Eb / 25) * Real.exp (-(Eb / 8)) :=
          mul_le_mul_of_nonneg_right hmargin (Real.exp_pos _).le
      _ = Real.exp (-(Real.exp 1 * Eb / 25)) := hmul
  have hL : (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
      ≤ 454 * Real.exp η * (Real.exp G * Real.exp (-(Eb / 8))) := by
    have hT4 : (0 : ℝ) ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT0 _
    calc (450 + 4 / Real.sqrt (2 * Real.pi * V)) * T ^ (1 / 4 : ℝ)
        ≤ 454 * Real.exp η * T ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hcoef hT4
      _ ≤ 454 * Real.exp η * (Real.exp G * Real.exp (-(Eb / 8))) :=
          mul_le_mul_of_nonneg_left hquarter (by positivity)
  refine le_trans hL ?_
  rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ 2)]
  linarith [hkey]

/-- `blockThirdConst₂ = 2((11/5)³ + 4(c₃(11/5)³ + (57/5)³)) ≤ 12050`, at `c₃ ≤ 2`.  The `2` is
`RMF.absMomentConst_three_le`, `(E Z⁴ + E Z²)/2 = (3+1)/2` by AM–GM; the true third absolute moment
is `2√(2/π) ≈ 1.596`. -/
lemma blockThirdConst₂_le : blockThirdConst₂ ≤ 12050 := by
  have h := absMomentConst_three_le
  have h0 := absMomentConst_nonneg 3
  rw [blockThirdConst₂]
  nlinarith [h, h0]

lemma blockThirdConst₂_pos : 0 < blockThirdConst₂ := by
  rw [blockThirdConst₂]
  nlinarith [absMomentConst_nonneg 3]

private lemma exp_fifteen_ge : (3100000 : ℝ) ≤ Real.exp 15 := by
  have h14 := exp_fourteen_ge
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hmul : Real.exp 14 * Real.exp 1 = Real.exp 15 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [h14, he, hmul, Real.exp_pos (14 : ℝ)]

lemma blockThirdConst_le : blockThirdConst ≤ 96 := by
  have h := absMomentConst_three_le
  have h0 := absMomentConst_nonneg 3
  rw [blockThirdConst]
  nlinarith [h, h0]

/-! ### The same balance, at two points

The two-point comparison (Harper's Lemma 7) needs the analogue of `hnum`, which differs in three
places: the swap constant is `3600` rather than `450` (`RMF.swap_error_at_quarter` at the two-point
Lindeberg charge); there are two collar terms, so the coefficient is
`3600 + 4/√(2πV₁) + 4/√(2πV₂) ≤ 3614`; and the box mass is a product of two window factors.

The first factor is the one-point `x_{m+1}^{-9/1600}`.  The second coordinate is the sheared one,
whose envelope has slope `(1+|ρ|)/40 ≤ 1/32` at `|ρ| ≤ 1/4`, and there
`RMF.rpow_le_exp_neg_sq_div_of_slope` buys `x_{m+1}^{-1/100}`, so `q_m ≍ h²/8·x_{m+1}^{-1/64}`.
Against the swap error's `x_m^{-1/8}` the loss is `(1/100 + 1/64)·e = 41e/1600` per `log x_m`, and
`41e ≤ 125` leaves `1/8 - 125/1600 = 3/64`. -/

/-- **The margin, at two points.**  `28912 e²⁵ (m+1)⁴ ≤ exp(3E/64)` at `E = e^{m+θ}`.

Same shape as `RMF.blockNum_margin`: `28912 = 8·3614` is the coefficient times the `8` in the box
mass, `(m+1)⁴` is the *square* of the one-point window, and `3/64` is what survives of the
one-point `5/64` after the second exponent is paid for. -/
lemma blockNum₂_margin {θ : ℝ} {m : ℕ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ) (hθ0 : (0 : ℝ) ≤ θ) :
    28912 * Real.exp 25 * ((m : ℝ) + 1) ^ 4
      ≤ Real.exp (3 / 64 * Real.exp ((m : ℝ) + θ)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hEbig : (1200000 : ℝ) ≤ Real.exp ((m : ℝ) + θ) :=
    le_trans exp_fourteen_ge (Real.exp_le_exp.2 hmθ)
  have hEm : Real.exp (m : ℝ) ≤ Real.exp ((m : ℝ) + θ) :=
    Real.exp_le_exp.2 (by linarith)
  have hhalf : 1 + (m : ℝ) / 2 ≤ Real.exp ((m : ℝ) / 2) := by
    linarith [Real.add_one_le_exp ((m : ℝ) / 2)]
  have hsq : (1 + (m : ℝ) / 2) ^ 2 ≤ Real.exp (m : ℝ) := by
    have hmul : Real.exp ((m : ℝ) / 2) * Real.exp ((m : ℝ) / 2) = Real.exp (m : ℝ) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [hhalf, (Real.exp_pos ((m : ℝ) / 2)).le, hm0]
  -- the left side is at most `e^{36 + 4m}`
  have hm1 : (m : ℝ) + 1 ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
  have h4m : Real.exp (m : ℝ) ^ (4 : ℕ) = Real.exp (4 * (m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h36 : Real.exp 11 * Real.exp 25 = Real.exp 36 := by
    rw [← Real.exp_add]
    norm_num
  have hlhs : 28912 * Real.exp 25 * ((m : ℝ) + 1) ^ 4 ≤ Real.exp (36 + 4 * (m : ℝ)) := by
    have hq : ((m : ℝ) + 1) ^ (4 : ℕ) ≤ Real.exp (4 * (m : ℝ)) := by
      rw [← h4m]
      exact pow_le_pow_left₀ (by linarith) hm1 4
    have h1 : (28912 : ℝ) ≤ Real.exp 11 := le_trans (by norm_num) exp_eleven_ge
    have hstep : 28912 * Real.exp 25 ≤ Real.exp 11 * Real.exp 25 :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos 25).le
    calc 28912 * Real.exp 25 * ((m : ℝ) + 1) ^ 4
        ≤ 28912 * Real.exp 25 * Real.exp (4 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ Real.exp 11 * Real.exp 25 * Real.exp (4 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
      _ = Real.exp (36 + 4 * (m : ℝ)) := by rw [h36, ← Real.exp_add]
  refine le_trans hlhs (Real.exp_le_exp.2 ?_)
  nlinarith [hEbig, hEm, hsq, hm0, sq_nonneg ((m : ℝ) - 1000)]

/-- **The two-point numerical condition, given any admissible third-moment constant.**

`RMF.blockNum_le_of_le` with `3600` for `450`, two collar terms for one, and the box mass
`h²/8 · x_{m+1}^{-1/64}` for the window mass `h · x_{m+1}^{-9/1600}`.  The proof is the same
computation: `T^{1/4} ≤ e²⁵e^{-E/8}`, the right side carries `e^{-41eE/1600}`, and `41e ≤ 125`
leaves `3/64` per `E` for `RMF.blockNum₂_margin` to absorb. -/
theorem blockNum₂_le_of_le {θ Kb : ℝ} {m : ℕ} {V₁ V₂ T : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hθ0 : (0 : ℝ) ≤ θ) (hV₁ : 1 / 16 ≤ V₁) (hV₂ : 1 / 16 ≤ V₂) (hT0 : 0 ≤ T)
    (hKb0 : 0 ≤ Kb) (hKb : Kb ≤ Real.exp 100)
    (hT : T ≤ Kb / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * T ^ (1 / 4 : ℝ)
      ≤ blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * ((1 / ((m : ℝ) + 1) ^ 2) ^ 2 / 8
          * blockScale θ (m + 1) ^ (-(1 : ℝ) / 64)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set E := Real.exp ((m : ℝ) + θ) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hE1 : (1 : ℝ) ≤ E := Real.one_le_exp (by linarith)
  -- the two scales, as exponentials
  have hXm : blockScale θ m = Real.exp E := by rw [blockScale]
  have hLm : Real.log (blockScale θ m) = E := log_blockScale θ m
  have hXm1 : blockScale θ (m + 1) = Real.exp (Real.exp 1 * E) := by
    have h : Real.exp 1 * E = Real.exp (((m + 1 : ℕ) : ℝ) + θ) := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [h, blockScale]
  have hsq : Real.sqrt (blockScale θ m) = Real.exp (E / 2) := by
    rw [hXm, ← Real.exp_half]
  -- `T ≤ Kb e^{-E/2}`, discarding the `log x_m` in the denominator
  have hT2 : T ≤ Kb * Real.exp (-(E / 2)) := by
    refine le_trans hT ?_
    rw [hsq, hLm, Real.exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (Real.exp_pos (E / 2))]
    nlinarith [mul_nonneg (mul_nonneg hKb0 (Real.exp_pos (E / 2)).le)
      (sub_nonneg.2 hE1)]
  -- `T^{1/4} ≤ e²⁵ e^{-E/8}`
  have hquarter : T ^ (1 / 4 : ℝ) ≤ Real.exp 25 * Real.exp (-(E / 8)) := by
    have h1 : T ^ (1 / 4 : ℝ) ≤ (Kb * Real.exp (-(E / 2))) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hT0 hT2 (by norm_num)
    have h2 : (Kb * Real.exp (-(E / 2))) ^ (1 / 4 : ℝ)
        = Kb ^ (1 / 4 : ℝ) * Real.exp (-(E / 8)) := by
      rw [Real.mul_rpow hKb0 (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      ring
    have h3 : Kb ^ (1 / 4 : ℝ) ≤ Real.exp 25 := by
      have h := Real.rpow_le_rpow hKb0 hKb (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [show Real.exp 100 ^ (1 / 4 : ℝ) = Real.exp 25 by
        rw [← Real.exp_mul]; congr 1; ring] at h
    calc T ^ (1 / 4 : ℝ) ≤ Kb ^ (1 / 4 : ℝ) * Real.exp (-(E / 8)) := by rw [← h2]; exact h1
      _ ≤ Real.exp 25 * Real.exp (-(E / 8)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  -- the coefficient, from `Vᵢ ≥ 1/16` and `π > 3`: each collar term is at most `7`
  have hcollar : ∀ V : ℝ, 1 / 16 ≤ V → 4 / Real.sqrt (2 * Real.pi * V) ≤ 7 := by
    intro V hV
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h2pv : (3 / 8 : ℝ) ≤ 2 * Real.pi * V := by nlinarith [hV, hpi]
    have hs : (4 / 7 : ℝ) ≤ Real.sqrt (2 * Real.pi * V) := by
      have h := Real.sqrt_le_sqrt (show ((4 / 7 : ℝ)) ^ 2 ≤ 2 * Real.pi * V by nlinarith)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 7)] at h
    have hs0 : (0 : ℝ) < Real.sqrt (2 * Real.pi * V) := by linarith
    rw [div_le_iff₀ hs0]
    linarith
  have hcoef : 3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂)
      ≤ 3614 := by
    linarith [hcollar V₁ hV₁, hcollar V₂ hV₂]
  -- the right-hand side, as a single exponential
  have hprod : blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(1 : ℝ) / 64)
      = Real.exp (-(41 / 1600 * (Real.exp 1 * E))) := by
    rw [← Real.rpow_add (blockScale_pos θ (m + 1)), hXm1, ← Real.exp_mul]
    congr 1
    ring
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hwin : ((1 : ℝ) / ((m : ℝ) + 1) ^ 2) ^ 2 / 8 = 1 / (8 * ((m : ℝ) + 1) ^ 4) := by
    field_simp
  rw [show blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * ((1 / ((m : ℝ) + 1) ^ 2) ^ 2 / 8
          * blockScale θ (m + 1) ^ (-(1 : ℝ) / 64))
      = blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * blockScale θ (m + 1) ^ (-(1 : ℝ) / 64)
        * ((1 / ((m : ℝ) + 1) ^ 2) ^ 2 / 8) from by ring, hprod, hwin]
  -- the margin closes it: `41e ≤ 125`, so `1/8 - 41e/1600 ≥ 3/64`
  have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hexpcmp : Real.exp (3 / 64 * E)
      ≤ Real.exp (E / 8 - 41 / 1600 * (Real.exp 1 * E)) :=
    Real.exp_le_exp.2 (by nlinarith [he3, hE0])
  have hkey : 28912 * Real.exp 25 * ((m : ℝ) + 1) ^ 4 * Real.exp (-(E / 8))
      ≤ Real.exp (-(41 / 1600 * (Real.exp 1 * E))) := by
    have hmul : Real.exp (E / 8 - 41 / 1600 * (Real.exp 1 * E)) * Real.exp (-(E / 8))
        = Real.exp (-(41 / 1600 * (Real.exp 1 * E))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 28912 * Real.exp 25 * ((m : ℝ) + 1) ^ 4 * Real.exp (-(E / 8))
        ≤ Real.exp (E / 8 - 41 / 1600 * (Real.exp 1 * E)) * Real.exp (-(E / 8)) :=
          mul_le_mul_of_nonneg_right (le_trans (blockNum₂_margin hmθ hθ0) hexpcmp)
            (Real.exp_pos _).le
      _ = Real.exp (-(41 / 1600 * (Real.exp 1 * E))) := hmul
  have hL : (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * T ^ (1 / 4 : ℝ)
      ≤ 3614 * (Real.exp 25 * Real.exp (-(E / 8))) := by
    have hT4 : (0 : ℝ) ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT0 _
    calc (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
          * T ^ (1 / 4 : ℝ)
        ≤ 3614 * T ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hcoef hT4
      _ ≤ 3614 * (Real.exp 25 * Real.exp (-(E / 8))) :=
          mul_le_mul_of_nonneg_left hquarter (by norm_num)
  refine le_trans hL ?_
  rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * ((m : ℝ) + 1) ^ 4)]
  nlinarith [hkey]

/-- **The two-point numerical condition, at Harper's windows and per-block errors**:
`RMF.blockNum₂_le_of_le` at `Kb = blockThirdConst₂·e³·8log4 ≤ 3.04·10⁶ ≤ e¹⁵`, far below the
`e¹⁰⁰` that lemma allows. -/
theorem blockNum₂_le {θ : ℝ} {m : ℕ} {V₁ V₂ T : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hθ0 : (0 : ℝ) ≤ θ) (hV₁ : 1 / 16 ≤ V₁) (hV₂ : 1 / 16 ≤ V₂) (hT0 : 0 ≤ T)
    (hT : T ≤ blockThirdConst₂ * (Real.exp 3 * (8 * Real.log 4
            / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))))) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * T ^ (1 / 4 : ℝ)
      ≤ blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)
        * ((1 / ((m : ℝ) + 1) ^ 2) ^ 2 / 8
          * blockScale θ (m + 1) ^ (-(1 : ℝ) / 64)) := by
  have hbt0 : (0 : ℝ) ≤ blockThirdConst₂ := blockThirdConst₂_pos.le
  have hexp3 : Real.exp 3 ≤ 21 := by
    have he : Real.exp 1 < 2.7182818286 := by linarith [Real.exp_one_lt_d9]
    have h3 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h3]
    calc Real.exp 1 ^ (3 : ℕ) ≤ (2.7182818286 : ℝ) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
      _ ≤ 21 := by norm_num
  have hexp30 : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have hlog4 : 8 * Real.log 4 ≤ 12 := by
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h4]
    linarith
  have hlog40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  refine blockNum₂_le_of_le (Kb := blockThirdConst₂ * (Real.exp 3 * (8 * Real.log 4)))
    hmθ hθ0 hV₁ hV₂ hT0 (by positivity) ?_ ?_
  · -- `≤ 12050 · 21 · 12 = 3036600 ≤ e¹⁵ ≤ e¹⁰⁰`
    have hA : Real.exp 3 * (8 * Real.log 4) ≤ 21 * 12 :=
      mul_le_mul hexp3 hlog4 hlog40 (by norm_num)
    have hA0 : (0 : ℝ) ≤ Real.exp 3 * (8 * Real.log 4) :=
      mul_nonneg hexp30.le hlog40
    have h1 : blockThirdConst₂ * (Real.exp 3 * (8 * Real.log 4)) ≤ 3036600 := by
      calc blockThirdConst₂ * (Real.exp 3 * (8 * Real.log 4))
          ≤ 12050 * (Real.exp 3 * (8 * Real.log 4)) :=
            mul_le_mul_of_nonneg_right blockThirdConst₂_le hA0
        _ ≤ 12050 * (21 * 12) := mul_le_mul_of_nonneg_left hA (by norm_num)
        _ = 3036600 := by norm_num
    have h2 : (3036600 : ℝ) ≤ Real.exp 15 := by linarith [exp_fifteen_ge]
    have h3 : Real.exp 15 ≤ Real.exp 100 := Real.exp_le_exp.2 (by norm_num)
    linarith
  · refine le_trans hT (le_of_eq ?_)
    ring

/-! ### Harper's window widths and per-block errors

The multi-block comparison takes `W`, `ε` and `E` as data.  Harper's choices are `W_m = 1/(m+1)²`,
whose partial sums are capped at `2` (which is what Lemma 4's `hwsum` wants), and
`ε_m = x_{m+1}^{-1/100}`, whose total must be at most `1/4` so that the compounded `2E` clears
Proposition 5's `ε ≤ 1/2`.

The `ε` sum is not delicate: `ε_m = \exp(-e^{m+1+θ}/100)` is *doubly* exponentially small, so at
`θ ≥ 16` the first term is already `e^{-240000}` and the crude comparison with `(1/2)^m` has room to
spare.  The `1/(m+1)²` sum, by contrast, is genuinely tight — `∑ 1/k² = π²/6 = 1.645`, and Lemma 4
asks for `2`. -/

private lemma exp_two_le : Real.exp 2 ≤ 7.39 := by
  have he : Real.exp 1 < 2.7182818286 := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [he, (Real.exp_pos 1).le, h2]

/-! ### The drift perturbation at general offsets

Harper observes `log|I_{l_j}(1/2+σ+it_j)|` with a block-dependent `t_j`, while the tilt sits at the
single point `1/2+σ`.  The observed weight is then `w_p = p^{-s-it_j}` rather than `p^{-s}`, and the
block drift picks up `∑_{p∈B_j}(cos(t_j log p) - 1)p^{-1-2σ}`.

Since `|cos u - 1| ≤ u²/2` and `log p ≤ log x_{j+1}` on the block, that is at most
`½ (t_j log x_{j+1})²` times the block mass.  Harper's range `|t_j| ≤ j^{-2/3}/log x_j` therefore
makes it `O(j^{-4/3})`, and **`∑ j^{-4/3}` converges** (to `ζ(4/3) ≈ 3.60`, kept as a `tsum`), so
the total drift moves by a constant, not by one growing with `n`.

`j^{-2/3}` is meaningless at `j = 0`, and Harper's blocks are numbered from `1`: Lean's block `m` is
his `j = m+1`, so everything below is stated at `(m+1)^{-4/3}`. -/

/-- The `p`-series at `p = 4/3 > 1`. -/
lemma summable_blockDrift : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3))) := by
  refine ((Real.summable_one_div_nat_add_rpow 1 ((4 : ℝ) / 3)).2 (by norm_num)).congr fun m => ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  rw [abs_of_nonneg hm, Real.rpow_neg hm, one_div]

/-- **The absolute constant the general-`t` drift costs.**  It depends on nothing — not on `x`, `a`,
`n`, `θ`, nor on the offsets `t_j` themselves. -/
noncomputable def blockDriftConst : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3))

lemma blockDriftConst_nonneg : 0 ≤ blockDriftConst :=
  tsum_nonneg fun _ => by positivity

/-- Every partial sum of the per-block perturbations is bounded by that one constant, uniformly in
`n`.  This is what keeps the drift `O(1)` rather than `O(n)` once the offsets are non-zero. -/
lemma sum_blockDrift_le (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3)) ≤ blockDriftConst :=
  summable_blockDrift.sum_le_tsum _ (fun _ _ => by positivity)

/-- `|cos u - 1| ≤ u²/2`.

Both halves are in Mathlib — `Real.cos_le_one` gives the sign, and
`Real.one_sub_sq_div_two_le_cos` the magnitude, unconditionally in `u`. -/
lemma abs_cos_sub_one_le (u : ℝ) : |Real.cos u - 1| ≤ u ^ 2 / 2 := by
  have h1 : Real.cos u ≤ 1 := Real.cos_le_one u
  have h2 : 1 - u ^ 2 / 2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The cosine drift on one block**: `|∑_{p∈B_m}(cos(t log p) - 1)w_p| ≤ ½(t·log x_{m+1})²·∑ w_p`
for `w_p ≥ 0`, since `|cos u - 1| ≤ u²/2` and `log p ≤ log x_{m+1}` on the block.  The bound is
quadratic in `t`, so Harper's `|t| ≤ j^{-2/3}/log x_j` gives `j^{-4/3}`, which is summable; at
`j^{-1/2}` it would give `∑ 1/j = log n`. -/
lemma abs_sum_cos_sub_one_block_le {θ t : ℝ} {m : ℕ} {w : Nat.Primes → ℝ}
    (hw : ∀ p ∈ primeBlockSub θ m, 0 ≤ w p) :
    |∑ p ∈ primeBlockSub θ m, (Real.cos (t * Real.log ((p : ℕ) : ℝ)) - 1) * w p|
      ≤ (t * Real.log (blockScale θ (m + 1))) ^ 2 / 2
          * ∑ p ∈ primeBlockSub θ m, w p := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
  have hqle : ((q : ℕ) : ℝ) ≤ blockScale θ (m + 1) := (mem_primeBlockSub.1 hq).2
  have hlog : Real.log ((q : ℕ) : ℝ) ≤ Real.log (blockScale θ (m + 1)) :=
    Real.log_le_log hq0 hqle
  have hlog0 : 0 ≤ Real.log ((q : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast q.2.one_lt.le)
  have habs : |t * Real.log ((q : ℕ) : ℝ)| ≤ |t * Real.log (blockScale θ (m + 1))| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hlog0, abs_of_nonneg (le_trans hlog0 hlog)]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg t)
  have hsq : (t * Real.log ((q : ℕ) : ℝ)) ^ 2
      ≤ (t * Real.log (blockScale θ (m + 1))) ^ 2 := by
    rw [← sq_abs (t * Real.log ((q : ℕ) : ℝ)),
      ← sq_abs (t * Real.log (blockScale θ (m + 1)))]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [abs_mul, abs_of_nonneg (hw q hq)]
  refine mul_le_mul_of_nonneg_right (le_trans (abs_cos_sub_one_le _) ?_) (hw q hq)
  linarith

/-- **The cosine drift at Harper's offsets**: for `14 ≤ m + θ`, `|σ|·log x_{m+1} ≤ 1` and
`|t|·log x_{m+1} ≤ (m+1)^{-2/3}`, the perturbation of one block mean is at most `4(m+1)^{-4/3}`.
The offset hypothesis is multiplicative to avoid a `log ≠ 0` side condition and `Real.zero_rpow`
forcing `t = 0` at `m = 0`; `t = 0` satisfies it.  The `4` needs `14 ≤ m + θ` (under `3 ≤ m + θ`
it would be `8`). -/
theorem abs_sum_cos_sub_one_primeBlockSub_le {θ σ t : ℝ} {m : ℕ}
    (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (ht : |t| * Real.log (blockScale θ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3))) :
    |∑ p ∈ primeBlockSub θ m,
        (Real.cos (t * Real.log ((p : ℕ) : ℝ)) - 1) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 4 * ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3)) := by
  set L := Real.log (blockScale θ (m + 1)) with hLdef
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  -- a crude lower bound on `L = log x_{m+1}`
  have hL : (1200000 : ℝ) ≤ L := by
    rw [hLdef, log_blockScale]
    refine le_trans exp_fourteen_ge (Real.exp_le_exp.2 ?_)
    push_cast
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  -- the block mass
  have hmass0 : ∀ q ∈ primeBlockSub θ m, (0 : ℝ) ≤ ((q : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun q _ => Real.rpow_nonneg (by positivity) _
  have hmass := abs_sum_rpow_primeBlockSub_sub_one_le θ σ 1 m hm3 (by norm_num) (by linarith)
  have hdiv : (60 : ℝ) / L ≤ 1 / 20000 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hmassle : (∑ q ∈ primeBlockSub θ m, ((q : ℕ) : ℝ) ^ (-1 - 2 * σ)) ≤ 7.4 := by
    have h1 := (abs_le.1 hmass).2
    have he2 : Real.exp (2 * (1 : ℝ)) ≤ 7.39 := by
      have : (2 : ℝ) * 1 = 2 := by ring
      rw [this]
      exact exp_two_le
    have hd0 : (0 : ℝ) ≤ 60 / L := by positivity
    have hprod : Real.exp (2 * (1 : ℝ)) * (60 / L) ≤ 7.39 * (1 / 20000) :=
      mul_le_mul he2 hdiv hd0 (by norm_num)
    linarith
  -- the squared offset
  have hpow : (((m : ℝ) + 1) ^ (-((2 : ℝ) / 3))) ^ 2 = ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3)) := by
    rw [← Real.rpow_natCast (((m : ℝ) + 1) ^ (-((2 : ℝ) / 3))) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have htL : |t * L| ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3)) := by
    rw [abs_mul, abs_of_pos hL0]
    exact ht
  have hsq : (t * L) ^ 2 ≤ ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3)) := by
    rw [← hpow, ← sq_abs (t * L)]
    exact pow_le_pow_left₀ (abs_nonneg _) htL 2
  have hsq0 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3)) := Real.rpow_nonneg (by positivity) _
  -- assemble
  refine le_trans (abs_sum_cos_sub_one_block_le hmass0) ?_
  have hmassnn : (0 : ℝ) ≤ ∑ q ∈ primeBlockSub θ m, ((q : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    Finset.sum_nonneg hmass0
  nlinarith [hsq, hsq0, hmassle, hmassnn, sq_nonneg (t * L)]

/-- `∑_{m<j} 1/(m+1)² ≤ 2`, the `range` form of `RMF.sum_inv_sq_Icc_le_two`. -/
lemma sum_inv_sq_range_le_two (j : ℕ) :
    ∑ m ∈ Finset.range j, (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 2 := by
  have h := sum_inv_sq_Icc_le_two j
  have hIcc : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by
    ext k
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range] at h
  simp only [Nat.add_sub_cancel] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_)) h
  push_cast
  ring

/-- Harper's per-block relative error, `ε_m = x_{m+1}^{-1/100}`. -/
noncomputable def blockEps (θ : ℝ) (m : ℕ) : ℝ :=
  blockScale θ (m + 1) ^ (-(1 : ℝ) / 100)

lemma blockEps_nonneg (θ : ℝ) (m : ℕ) : 0 ≤ blockEps θ m :=
  Real.rpow_nonneg (blockScale_pos θ (m + 1)).le _

lemma blockEps_eq (θ : ℝ) (m : ℕ) :
    blockEps θ m = Real.exp (-(1 / 100) * Real.exp ((m : ℝ) + 1 + θ)) := by
  rw [blockEps, blockScale, ← Real.exp_mul]
  congr 1
  push_cast
  ring

/-- `ε_m ≤ (1/8)(1/2)^m` once `θ ≥ 16`.  Crude by a factor of `e^{240000}`; the point is only that
the sum converges to something below `1/4`. -/
lemma blockEps_le {θ : ℝ} (hθ : (16 : ℝ) ≤ θ) (m : ℕ) :
    blockEps θ m ≤ 1 / 8 * (1 / 2) ^ m := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- `e^{m+1+θ} ≥ e¹⁴(1+m)`
  have hEm : Real.exp 14 * (1 + (m : ℝ)) ≤ Real.exp ((m : ℝ) + 1 + θ) := by
    have h1 : (1 : ℝ) + m ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
    calc Real.exp 14 * (1 + (m : ℝ)) ≤ Real.exp 14 * Real.exp (m : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos 14).le
      _ = Real.exp (14 + (m : ℝ)) := by rw [← Real.exp_add]
      _ ≤ Real.exp ((m : ℝ) + 1 + θ) := Real.exp_le_exp.2 (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hkey : Real.log 8 + (m : ℝ) ≤ 1 / 100 * Real.exp ((m : ℝ) + 1 + θ) := by
    nlinarith [hEm, exp_fourteen_ge, hm0, hlog2, hlog8]
  -- `e^{-m} ≤ (1/2)^m`, since `e^{-1} ≤ 1/2`
  have hhalf : Real.exp (-(m : ℝ)) ≤ ((1 : ℝ) / 2) ^ m := by
    have he : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ m
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [blockEps_eq]
  calc Real.exp (-(1 / 100) * Real.exp ((m : ℝ) + 1 + θ))
      ≤ Real.exp (-(Real.log 8 + (m : ℝ))) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / 8 * Real.exp (-(m : ℝ)) := by
        rw [show -(Real.log 8 + (m : ℝ)) = -Real.log 8 + -(m : ℝ) from by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
        norm_num
    _ ≤ 1 / 8 * ((1 : ℝ) / 2) ^ m := mul_le_mul_of_nonneg_left hhalf (by norm_num)

/-- `∑_{m<n} ε_m ≤ 1/4`, so the compounded error `2E` clears Proposition 5's `ε ≤ 1/2`. -/
lemma sum_blockEps_le {θ : ℝ} (hθ : (16 : ℝ) ≤ θ) (n : ℕ) :
    ∑ m ∈ Finset.range n, blockEps θ m ≤ 1 / 4 := by
  have hgeom : ∑ m ∈ Finset.range n, ((1 : ℝ) / 2) ^ m ≤ 2 := by
    rw [geom_sum_eq (by norm_num : ((1 : ℝ) / 2) ≠ 1)]
    have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num : ((1 : ℝ) / 2 - 1) < 0)]
    linarith
  calc ∑ m ∈ Finset.range n, blockEps θ m
      ≤ ∑ m ∈ Finset.range n, (1 / 8 : ℝ) * (1 / 2) ^ m :=
        Finset.sum_le_sum fun m _ => blockEps_le hθ m
    _ = 1 / 8 * ∑ m ∈ Finset.range n, ((1 : ℝ) / 2) ^ m := by rw [Finset.mul_sum]
    _ ≤ 1 / 8 * 2 := mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = 1 / 4 := by norm_num

/-! ### The per-block data, at Harper's choices

`RMF.exists_isWindowComparison_primeBlockSub` takes `W`, `M`, `T`, `q`, `ε` and `E` as data and
asks six numerical hypotheses about them.  Harper's choices are `W_m = 1/(m+1)²`,
`ε_m = x_{m+1}^{-1/100}` (both above), `T_m` the third-moment bound of
`RMF.sum_norm_cube_primeBlockSub_le`, and `q_m = W_m·x_{m+1}^{-9/1600}` the window mass.

Naming them makes `hTb` definitional and `hnum` into `RMF.blockNum_le_of_le`; only `hqlow`, which
needs the envelope and with it the real threshold on `θ`, carries any weight. -/

lemma blockThirdConst_pos : 0 < blockThirdConst := by
  rw [blockThirdConst]
  nlinarith [absMomentConst_nonneg 3]

/-- Harper's window width at block `m`. -/
noncomputable def blockWindow (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1) ^ 2

lemma blockWindow_pos (m : ℕ) : 0 < blockWindow m := by
  rw [blockWindow]
  positivity

/-- `blockThirdConst` times the third-moment bound of `RMF.sum_norm_cube_primeBlockSub_le` — that
is, the `T` of Lemma 3, so that `hTb` becomes definitional.  See
`RMF.blockThirdConst_mul_sum_le_of_le`. -/
noncomputable def blockT (θ : ℝ) (m : ℕ) : ℝ :=
  blockThirdConst * (Real.exp 3 * (8 * Real.log 4
    / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))))

/-- Harper's window mass `W_m·x_{m+1}^{-9/1600}`, named. -/
noncomputable def blockQ (θ : ℝ) (m : ℕ) : ℝ :=
  blockWindow m * blockScale θ (m + 1) ^ (-(9 : ℝ) / 1600)

lemma blockQ_pos (θ : ℝ) (m : ℕ) : 0 < blockQ θ m := by
  rw [blockQ]
  have h1 := blockWindow_pos m
  have h2 : (0 : ℝ) < blockScale θ (m + 1) ^ (-(9 : ℝ) / 1600) :=
    Real.rpow_pos_of_pos (blockScale_pos θ (m + 1)) _
  positivity

/-- **The two-point third-moment bound**: `RMF.blockT` with `RMF.blockThirdConst₂` in place of
`RMF.blockThirdConst`; see `RMF.blockThirdConst₂` for why it is not `2·blockT`. -/
noncomputable def blockT₂ (θ : ℝ) (m : ℕ) : ℝ :=
  blockThirdConst₂ * (Real.exp 3 * (8 * Real.log 4
    / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))))

/-- **The two-point box mass** `W_m²/8·x_{m+1}^{-1/64}`, the analogue of `RMF.blockQ`.  A product of
two window factors: the exponent is `-9/1600 - 1/100`, not `-9/800`, because the second coordinate
is the sheared one (envelope slope `1/32`, buying `x^{-1/100}`).  The `8` is `2·4`, the two window
shrinkages `RMF.le_measure_box_pair` pays to fit a closed box inside a half-open one. -/
noncomputable def blockQ₂ (θ : ℝ) (m : ℕ) : ℝ :=
  blockWindow m ^ 2 / 8 * blockScale θ (m + 1) ^ (-(1 : ℝ) / 64)

lemma blockQ₂_pos (θ : ℝ) (m : ℕ) : 0 < blockQ₂ θ m := by
  rw [blockQ₂]
  have h1 := blockWindow_pos m
  have h2 : (0 : ℝ) < blockScale θ (m + 1) ^ (-(1 : ℝ) / 64) :=
    Real.rpow_pos_of_pos (blockScale_pos θ (m + 1)) _
  positivity

lemma blockT_pos (θ : ℝ) (m : ℕ) : 0 < blockT θ m := by
  have hL : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  have hs : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rw [blockT]
  have h3 : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have hbt := blockThirdConst_pos
  positivity

lemma blockT₂_pos (θ : ℝ) (m : ℕ) : 0 < blockT₂ θ m := by
  have hL : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  have hs : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  rw [blockT₂]
  have h3 : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have hbt := blockThirdConst₂_pos
  positivity

/-- **The two-point `hnum`, at the named `T`, `q` and `ε`.**  `RMF.blockNum₂_le` verbatim; the only
work is unfolding the four names. -/
lemma blockNum₂_le' {θ : ℝ} {m : ℕ} {V₁ V₂ : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hθ0 : (0 : ℝ) ≤ θ) (hV₁ : 1 / 16 ≤ V₁) (hV₂ : 1 / 16 ≤ V₂) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * blockT₂ θ m ^ (1 / 4 : ℝ)
      ≤ blockEps θ m * blockQ₂ θ m := by
  rw [blockEps, blockQ₂, blockWindow]
  exact blockNum₂_le hmθ hθ0 hV₁ hV₂ (blockT₂_pos θ m).le (le_of_eq (by rw [blockT₂]))

/-- **The weight is small on its block, whatever its phase.**  Stated for any `u` with the right
modulus, so it serves the offset weight `RMF.blockOffsetWeight` as well as `p^{-s}`. -/
lemma norm_le_fifth_of_sq_eq {θ σ : ℝ} {m : ℕ} (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) {u : ℂ}
    (hu : ‖u‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) : ‖u‖ ≤ 1 / 5 := by
  have h : ‖u‖ ≤ blockWeightSize θ m := norm_le_of_mem_primeBlockSub hσ hp hu
  have hk := blockWeightSize_le hmθ
  linarith

/-- **`hw` and `ha` at the one-point weight.**  Both sides of the comparison use
`w_p = p^{-s}`, whose norm on a block is at most `κ_m ≤ 1/1000`. -/
lemma norm_prime_cpow_le_fifth {θ σ : ℝ} {m : ℕ} {s : ℂ} (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hres : s.re = 1 / 2 + σ) (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 :=
  norm_le_fifth_of_sq_eq hmθ hσ hp (norm_sq_prime_cpow_neg p hres)

/-- `‖p^{-s}‖ ≤ 1/5` on the block at a general tilt scale — `RMF.norm_prime_cpow_le_fifth` with
the scale carried, at the block start `RMF.blockWeightSize_le_of_le` needs. -/
lemma norm_prime_cpow_le_fifth_of_le {θ σ η : ℝ} {m : ℕ} {s : ℂ}
    (hres : s.re = 1 / 2 + σ) (hsc : 14 + 2 * η ≤ Real.exp ((m : ℝ) + θ))
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5 := by
  have h := norm_le_of_mem_primeBlockSub_of_le hσ hp (norm_sq_prime_cpow_neg p hres)
  have hκ := blockWeightSize_le_of_le hsc
  linarith

/-- **The third-moment hypothesis at a general tilt scale**, at the named `T`. -/
lemma blockThirdConst_mul_sum_le_of_le {θ σ η : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    blockThirdConst * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3
      ≤ Real.exp (3 * η - 3) * blockT θ m := by
  have he : Real.exp (3 * η - 3) * Real.exp 3 = Real.exp (3 * η) := by
    rw [← Real.exp_add]; ring_nf
  have hrw : Real.exp (3 * η - 3) * blockT θ m
      = blockThirdConst * (Real.exp (3 * η) * (8 * Real.log 4
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)))) := by
    rw [blockT, ← he]; ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left (sum_norm_cube_primeBlockSub_le_of_le hmθ hσ hwn)
    blockThirdConst_pos.le

/-- **The named window mass, at a directly-supplied threshold exponent.**

`RMF.blockQ` is this at `τ = 9/1600`, the exponent the envelope proxy forces.  The direct
threshold is free to spend more, and `RMF.exists_blockQThr_le_measure` spends `3/100` — inside the
`τ < 1/(8e) - 1/100` that the swap balance leaves. -/
noncomputable def blockQThr (θ τ : ℝ) (m : ℕ) : ℝ :=
  blockWindow m * blockScale θ (m + 1) ^ (-τ)

lemma blockQThr_pos (θ τ : ℝ) (m : ℕ) : 0 < blockQThr θ τ m :=
  mul_pos (blockWindow_pos m) (Real.rpow_pos_of_pos (blockScale_pos _ _) _)

/-- **`hqlow` at any tilt bound, with the block offset existential**: for `E₀, a ≥ 0`, `B > 0` there
is `θ₀` such that every block `m ≤ n` with `θ ≥ θ₀`, `σ ≥ 0`, `0 ≤ η ≤ E₀`, `|σ|·log x_{m+1} ≤ η`,
`‖w_p‖² = p^{-1-2σ}` and `0 ≤ M ≤ a + Bm` has window mass at least `RMF.blockQThr θ (3/100) m`.
Its inputs are `RMF.re_pos_of_block_of_le`, `RMF.blockWeightSize_le_of_le`,
`RMF.abs_blockMean_le_of_le` and `RMF.blockMatchedVar_concrete_of_le`; `RMF.exists_thr_direct` pays
for `A = 2e^{2η}` in `θ₀`, so no numeral depends on the tilt scale. -/
theorem exists_blockQThr_le_measure (E₀ a Bs : ℝ)
    (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∃ θ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (m n : ℕ) (s : ℂ) (w : Nat.Primes → ℂ) (M : ℝ),
      θ₀ ≤ θ → m ≤ n → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      (∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) →
      0 ≤ M → M ≤ a + Bs * m →
      ∀ c, |c| ≤ M → blockQThr θ (3 / 100) m ≤ (gaussianReal
          (blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m))
          (blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m))
          (Set.Ioc c (c + blockWindow m))).toReal := by
  have hA1 : (1 : ℝ) ≤ 2 * Real.exp (2 * E₀) := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * E₀)
    linarith
  obtain ⟨θ₁, hθ₁⟩ := exists_thr_direct (2 * Real.exp (2 * E₀)) a Bs 1 (3 / 100)
    hA1 ha hBs (by norm_num) (by norm_num)
  refine ⟨max (max θ₁ 9) (Real.log (14 + 2 * E₀)), ?_⟩
  intro Ω _ X μ hX θ σ η m n s w M hθ hmn hres hσ0 hη0 hηE hσ hwn hM0 hM
  have hAη : (1 : ℝ) ≤ 2 * Real.exp (2 * η) := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * η)
    linarith
  have hθ₁' : θ₁ ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hθ
  have hθ9 : (9 : ℝ) ≤ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hθ
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ := le_trans (le_max_right _ _) hθ
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm5 : (5 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hm8 : (8 : ℝ) ≤ (m : ℝ) + θ := by linarith
  -- the one hypothesis that replaces every cap on the tilt scale
  have hsc : (14 : ℝ) + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    have h1 : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 hθlog
    have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hsre : 0 < s.re := re_pos_of_block_of_le hres hsc hσ
  have hb0 : (0 : ℝ) < blockScale θ m := blockScale_pos θ m
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]; nlinarith
  -- the drift, at the per-block cutoff
  have habs := abs_blockMean_le_of_le hX hm5 hmn hres hσ0 hsc hσ hwn
  rw [blockMean_blockCutoff_eq hX hsre hmn w, blockCutoff] at habs
  have hL : (7000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [log_blockScale]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (7000 : ℝ) ≤ (2.7 : ℝ) ^ (9 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 9
      _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hmert : (60 : ℝ) / Real.log (blockScale θ (m + 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  -- `2e^{2η}` is under the block scale, which is where `θ ≥ \log(1+2η)` is spent
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbs : 2 * Real.exp (2 * η) ≤ blockScale θ m := by
    have hkey : Real.log 2 + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
      linarith [Real.log_two_lt_d9]
    have hrw : 2 * Real.exp (2 * η) = Real.exp (Real.log 2 + 2 * η) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hrw, blockScale]
    exact Real.exp_le_exp.2 hkey
  have hterm : 2 * Real.exp (2 * η) / blockScale θ m ≤ 1 := by
    rw [div_le_one hb0]; exact hbs
  have hdrift : |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
      ≤ Real.exp 2 := by linarith
  have hwin : blockWindow m ≤ 1 := by
    rw [blockWindow, div_le_one (by positivity)]
    nlinarith
  have hwin0 : (0 : ℝ) < blockWindow m := blockWindow_pos m
  -- the variance bracket, already at the per-block cutoff
  obtain ⟨hV₁, hV₂⟩ := blockMatchedVar_concrete_of_le hX θ σ η m s w hm8 hres hσ0 hsc hσ hwn
  have hV₁' : 1 / (2 * Real.exp (2 * η))
      ≤ 2 * ((blockMatchedVar X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w
        (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
    have hrw : Real.exp (-(2 * η)) / 2 = 1 / (2 * Real.exp (2 * η)) := by
      rw [Real.exp_neg]
      field_simp
    rw [← hrw]; exact hV₁
  -- the threshold, at `A = 2e^{2η}`, `B = 9`, `τ = 3/100`
  have hthr1 := hθ₁ θ m hθ₁'
  have hEη : 2 * Real.exp (2 * η) ≤ 2 * Real.exp (2 * E₀) := by
    have := Real.exp_le_exp.2 (by linarith : 2 * η ≤ 2 * E₀)
    linarith
  have hthr0 : 2 * Real.exp (2 * η) * (a + Bs * m + Real.exp 2 + 1) ^ 2
      + Real.log (Real.pi * 9) / 2
      ≤ 3 / 100 * Real.log (blockScale θ (m + 1)) := by
    have hsq : (0 : ℝ) ≤ (a + Bs * m + Real.exp 2 + 1) ^ 2 := sq_nonneg _
    nlinarith [hthr1, hEη, hsq]
  have henv : M + |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
      + blockWindow m ≤ a + Bs * m + Real.exp 2 + 1 := by linarith
  have henv0 : (0 : ℝ) ≤ M
      + |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
      + blockWindow m := by positivity
  have hthr : 2 * Real.exp (2 * η) * (M
        + |blockMean X μ (⌊blockScale θ (m + 1)⌋₊ + 1) s w (primeBlockSub θ m)|
        + blockWindow m) ^ 2 + Real.log (Real.pi * 9) / 2
      ≤ 3 / 100 * Real.log (blockScale θ (m + 1)) := by
    have hmono := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ henv0 henv 2)
      (by linarith : (0 : ℝ) ≤ 2 * Real.exp (2 * η))
    linarith
  have hmain := le_toReal_measure_Ioc_blockGaussian_of_thr hX hm5 hres hsc hσ hwn
    hwin0.le (by linarith : (0 : ℝ) < 2 * Real.exp (2 * η)) (by norm_num : (0 : ℝ) < 9)
    hV₁' hV₂ hthr
  intro c hc
  rw [blockQThr, blockMean_blockCutoff_eq hX hsre hmn w,
    blockMatchedVar_blockCutoff_eq hX hsre hmn w]
  simp only [blockCutoff]
  exact hmain c hc

/-! ### Two of the hypotheses are not really numerical

`hσ` is a `∀` over a family that is monotone in the index, so it is the single inequality at the
**top** scale.  And the envelope's middle bracket — the `e²`, the Mertens error `60/log x`, and the
weight size `κ_m` — is bounded by an absolute constant once `θ ≥ 125`, so it need not appear in any
statement.  Removing both leaves an envelope a reader can check by eye. -/

/-- `hσ` is a condition at the **top** scale only.  `log x_{m+1} = e^{m+1+θ}` is increasing in `m`,
so bounding `|σ|` against the largest block bounds it against all of them. -/
lemma hsigma_of_top {ϑ σ : ℝ} {n : ℕ} (h : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1) :
    ∀ m, m ≤ n → |σ| * Real.log (blockScale ϑ (m + 1)) ≤ 1 := by
  intro m hm
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)) h
  have hmn : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hm
  rw [log_blockScale, log_blockScale]
  refine Real.exp_le_exp.2 ?_
  push_cast
  linarith

/-- The same at a general tilt scale.  `RMF.hsigma_of_top` is the case `η = 1`; the scale rides
through unchanged, since the only fact used is that `\log x_{m+1}` is monotone in `m`. -/
lemma hsigma_of_top_of_le {ϑ σ η : ℝ} {n : ℕ}
    (h : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η) :
    ∀ m, m ≤ n → |σ| * Real.log (blockScale ϑ (m + 1)) ≤ η := by
  intro m hm
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)) h
  exact Real.log_le_log (blockScale_pos ϑ (m + 1)) (blockScale_mono ϑ (by omega))

/-! ### The join

`RMF.exists_isWindowComparison_primeBlockSub` produces Lemma 3 from six numerical facts about
`W, M, T, q, ε, E`, and each has a named discharger.  Together they give the comparison for the
Steinhaus random multiplicative function with two hypotheses left: the block offset and the
envelope.  The offset is taken past `125` (`RMF.sum_blockEps_le` needs only `θ ≥ 16`), which
`θ = {log log x} + D - 1` with `D ≥ 126` supplies, as Harper's `l_j = ⌊log log x⌋ - D - j` grants;
the envelope is linear, `0 ≤ M_m ≤ a + Bm`. -/

/-- **Lemma 3 for the Steinhaus RMF at a general tilt scale**: for `E₀, a ≥ 0`, `B > 0` there is
`θ₀` such that for `θ ≥ θ₀`, `σ ≥ 0`, `0 ≤ η ≤ E₀`, `|σ|·log x_{n+1} ≤ η` and an envelope
`0 ≤ M_m ≤ a + Bm`, the tilted block increments at `w_p = p^{-s}` compare, from every shift
`k ≤ n`, with an independent family of Gaussians of means `RMF.blockGaussMean` and variances
`RMF.blockGaussVar`, at the windows `RMF.blockWindow` and with error `1/2`.  The window mass is
`RMF.blockQThr θ (3/100)`, and the envelope is linear (the direct-threshold form) rather than
Harper's `(1/40)√(log x_m)`.  There is no cap on `E₀`: the only scale condition is
`14 + 2η ≤ e^{m+θ}`, which `θ ≥ log(14 + 2E₀)` buys. -/
theorem exists_isWindowComparison_steinhaus_of_le
    (E₀ a Bs : ℝ) (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∃ θ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (n : ℕ) (s : ℂ) (M : ℕ → ℝ),
      θ₀ ≤ θ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
        IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
        (∀ m, Q.map (N m)
          = gaussianReal (blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
              (blockGaussVar X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)) ∧
        (∀ k, k ≤ n → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
          (1 / 2)) := by
  obtain ⟨θq, hθq⟩ := exists_blockQThr_le_measure E₀ a Bs hE₀ ha hBs
  obtain ⟨θn, hθn⟩ := exists_blockNum_le_of_scale E₀ ((3 * E₀ + 8) / 4) hE₀ (by linarith)
  refine ⟨max (max θq θn) (max 125 (Real.log (14 + 2 * E₀))), ?_⟩
  intro Ω _ X μ hX θ σ η n s M hθ hres hσ0 hη0 hηE hσtop hM0 hM
  have hθq' : θq ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hθ
  have hθn' : θn ≤ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hθ
  have hθ125 : (125 : ℝ) ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hθ
  have hsc : ∀ m : ℕ, (14 : ℝ) + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
    intro m
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    have h1 : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 hθlog
    have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) :=
      Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    linarith
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  have hσm := hsigma_of_top_of_le hσtop
  have hmθ : ∀ m : ℕ, (14 : ℝ) ≤ (m : ℝ) + θ := by
    intro m
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hm5 : ∀ m : ℕ, (5 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hm8 : ∀ m : ℕ, (8 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hwn : ∀ m : ℕ, ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun m p _ => norm_sq_prime_cpow_neg p hres
  have hs : 0 < s.re := re_pos_of_block_of_le hres (hsc 0) (hσm 0 (Nat.zero_le n))
  have hV : ∀ m, m ≤ n →
      Real.exp (-(2 * η)) / 2
          ≤ 2 * ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
            ≤ 9 := by
    intro m hm
    rw [blockMatchedVar_blockCutoff_eq hX hs hm w, blockCutoff]
    exact blockMatchedVar_concrete_of_le hX θ σ η m s w (hm8 m) hres hσ0 (hsc m)
      (hσm m hm) (hwn m)
  -- the numerical condition, at `Kb = e^{3η}·blockThirdConst·8\log 4`
  have hlog40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hbt0 : (0 : ℝ) < blockThirdConst := blockThirdConst_pos
  have hKb0 : (0 : ℝ) ≤ Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4)) := by
    have := Real.exp_pos (3 * η)
    positivity
  have hKb : Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4))
      ≤ Real.exp (4 * ((3 * E₀ + 8) / 4)) := by
    have h1152 : blockThirdConst * (8 * Real.log 4) ≤ 1152 := by
      have hb := blockThirdConst_le
      have hl : 8 * Real.log 4 ≤ 12 := by
        have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        rw [h4]
        linarith
      nlinarith [hbt0, hlog40]
    have he8 : (1152 : ℝ) ≤ Real.exp 8 := by
      have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 8)
        (by norm_num) he.le (by norm_num)
    have hsplit : Real.exp (4 * ((3 * E₀ + 8) / 4)) = Real.exp (3 * E₀) * Real.exp 8 := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3η : Real.exp (3 * η) ≤ Real.exp (3 * E₀) := Real.exp_le_exp.2 (by linarith)
    rw [hsplit]
    have hc0 : (0 : ℝ) ≤ blockThirdConst * (8 * Real.log 4) := by positivity
    exact mul_le_mul h3η (le_trans h1152 he8) hc0 (Real.exp_pos _).le
  have hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)))
      * (Real.exp (3 * η - 3) * blockT θ m) ^ (1 / 4 : ℝ)
        ≤ blockEps θ m * blockQThr θ (3 / 100) m := by
    intro m hm
    have hVm := (hV m (le_of_lt hm)).1
    have hVge : Real.exp (-(2 * η)) / 4
        ≤ ((blockMatchedVar X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
      linarith
    have hT0 : (0 : ℝ) ≤ Real.exp (3 * η - 3) * blockT θ m := by
      have h1 : (0 : ℝ) < blockT θ m := blockT_pos θ m
      have h2 : (0 : ℝ) < Real.exp (3 * η - 3) := Real.exp_pos _
      positivity
    have he3 : Real.exp (3 * η - 3) * Real.exp 3 = Real.exp (3 * η) := by
      rw [← Real.exp_add]; ring_nf
    have hden : (0 : ℝ) < Real.sqrt (blockScale θ m) * Real.log (blockScale θ m) := by
      have h1 : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
      have h2 : (0 : ℝ) < Real.log (blockScale θ m) := by
        rw [log_blockScale]; exact Real.exp_pos _
      positivity
    have hTle : Real.exp (3 * η - 3) * blockT θ m
        ≤ Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4))
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)) :=
      le_of_eq (by rw [blockT, ← he3]; field_simp [hden.ne'])
    have h := hθn θ η _ _ _ m hθn' hη0 hηE hVge hT0 hKb0 hKb hTle
    rw [blockEps, blockQThr, blockWindow]
    refine le_trans h (le_of_eq ?_)
    norm_num
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_primeBlockSub (X := X) (μ := μ) (W := blockWindow) (M := M)
      (T := fun m => Real.exp (3 * η - 3) * blockT θ m) (q := blockQThr θ (3 / 100))
      (ε := blockEps θ) (E := 1 / 4) hX hs
      (fun m _ p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m (by omega)) hp)
      (fun m _ p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m (by omega)) hp)
      (fun m _ => by
        have h1 : (0 : ℝ) < blockT θ m := blockT_pos θ m
        have h2 : (0 : ℝ) < Real.exp (3 * η - 3) := Real.exp_pos _
        positivity)
      (fun m _ => blockQThr_pos θ (3 / 100) m)
      (fun m hm => by
        have h := (hV m (le_of_lt hm)).1
        have hpos : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
        intro hzero
        rw [hzero] at h
        norm_num at h
        linarith)
      (fun m hm => blockThirdConst_mul_sum_le_of_le (hm3 m) (hσm m (le_of_lt hm)) (hwn m))
      (fun m hm => hθq Ω X μ hX θ σ η m n s w (M m) hθq' (le_of_lt hm) hres hσ0 hη0 hηE
        (hσm m (le_of_lt hm)) (hwn m) (hM0 m) (hM m))
      hnum
      (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le (by linarith) n) (by norm_num)
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, fun k hk => ?_⟩
  have h := hcmp k hk
  rwa [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h

/-- **Lemma 3 for the Steinhaus RMF, with the barrier range `nR` below the tilt cutoff `nT`**: as
`RMF.exists_isWindowComparison_steinhaus_of_le`, with the tilt at `blockCutoff θ nT`, the
comparison over `m < nR`, and `|σ|·log x_{nR+1} ≤ η`.  At `η_m = Ke^{m-n}` only the top `⌈log K⌉`
blocks are thinned, so a caller may take `E₀ = 1` on the range and keep every constant free of
`K`.  The indices are independent because the tilted law of a prime does not see the cutoff
(`RMF.integral_comp_tiltedMeasure_congr_cutoff`). -/
theorem exists_isWindowComparison_steinhaus_of_range
    (E₀ a Bs : ℝ) (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∃ θ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (nT nR : ℕ) (s : ℂ) (M : ℕ → ℝ),
      θ₀ ≤ θ → nR ≤ nT → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (nR + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
        IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
        (∀ m, Q.map (N m)
          = gaussianReal (blockGaussMean X μ θ nR s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
              (blockGaussVar X μ θ nR s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)) ∧
        (∀ k, k ≤ nR → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ nT) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (nR - k)
          (1 / 2)) := by
  obtain ⟨θq, hθq⟩ := exists_blockQThr_le_measure E₀ a Bs hE₀ ha hBs
  obtain ⟨θn, hθn⟩ := exists_blockNum_le_of_scale E₀ ((3 * E₀ + 8) / 4) hE₀ (by linarith)
  refine ⟨max (max θq θn) (max 125 (Real.log (14 + 2 * E₀))), ?_⟩
  intro Ω _ X μ hX θ σ η nT nR s M hθ hnRT hres hσ0 hη0 hηE hσtop hM0 hM
  have hy : blockCutoff θ nR ≤ blockCutoff θ nT := blockCutoff_mono θ hnRT
  have hθq' : θq ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hθ
  have hθn' : θn ≤ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hθ
  have hθ125 : (125 : ℝ) ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hθ
  have hsc : ∀ m : ℕ, (14 : ℝ) + 2 * η ≤ Real.exp ((m : ℝ) + θ) := by
    intro m
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    have h1 : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 hθlog
    have hmt : Real.exp θ ≤ Real.exp ((m : ℝ) + θ) :=
      Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    linarith
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  have hσm := hsigma_of_top_of_le hσtop
  have hmθ : ∀ m : ℕ, (14 : ℝ) ≤ (m : ℝ) + θ := by
    intro m
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hm5 : ∀ m : ℕ, (5 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hm8 : ∀ m : ℕ, (8 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hwn : ∀ m : ℕ, ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun m p _ => norm_sq_prime_cpow_neg p hres
  have hs : 0 < s.re := re_pos_of_block_of_le hres (hsc 0) (hσm 0 (Nat.zero_le nR))
  have hV : ∀ m, m ≤ nR →
      Real.exp (-(2 * η)) / 2
          ≤ 2 * ((blockMatchedVar X μ (blockCutoff θ nT) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVar X μ (blockCutoff θ nT) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
            ≤ 9 := by
    intro m hm
    rw [blockMatchedVar_blockCutoff_eq hX hs (by omega : m ≤ nT) w, blockCutoff]
    exact blockMatchedVar_concrete_of_le hX θ σ η m s w (hm8 m) hres hσ0 (hsc m)
      (hσm m hm) (hwn m)
  -- the numerical condition, at `Kb = e^{3η}·blockThirdConst·8\log 4`
  have hlog40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hbt0 : (0 : ℝ) < blockThirdConst := blockThirdConst_pos
  have hKb0 : (0 : ℝ) ≤ Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4)) := by
    have := Real.exp_pos (3 * η)
    positivity
  have hKb : Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4))
      ≤ Real.exp (4 * ((3 * E₀ + 8) / 4)) := by
    have h1152 : blockThirdConst * (8 * Real.log 4) ≤ 1152 := by
      have hb := blockThirdConst_le
      have hl : 8 * Real.log 4 ≤ 12 := by
        have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        rw [h4]
        linarith
      nlinarith [hbt0, hlog40]
    have he8 : (1152 : ℝ) ≤ Real.exp 8 := by
      have he : (2.7182 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      simpa using le_exp_natCast_of_le_pow (c := 2.7182) (k := 8)
        (by norm_num) he.le (by norm_num)
    have hsplit : Real.exp (4 * ((3 * E₀ + 8) / 4)) = Real.exp (3 * E₀) * Real.exp 8 := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3η : Real.exp (3 * η) ≤ Real.exp (3 * E₀) := Real.exp_le_exp.2 (by linarith)
    rw [hsplit]
    have hc0 : (0 : ℝ) ≤ blockThirdConst * (8 * Real.log 4) := by positivity
    exact mul_le_mul h3η (le_trans h1152 he8) hc0 (Real.exp_pos _).le
  have hnum : ∀ m, m < nR → (450 + 4 / Real.sqrt (2 * Real.pi *
        ((blockMatchedVar X μ (blockCutoff θ nT) s w (primeBlockSub θ m) : ℝ≥0) : ℝ)))
      * (Real.exp (3 * η - 3) * blockT θ m) ^ (1 / 4 : ℝ)
        ≤ blockEps θ m * blockQThr θ (3 / 100) m := by
    intro m hm
    have hVm := (hV m (le_of_lt hm)).1
    have hVge : Real.exp (-(2 * η)) / 4
        ≤ ((blockMatchedVar X μ (blockCutoff θ nT) s w (primeBlockSub θ m) : ℝ≥0) : ℝ) := by
      linarith
    have hT0 : (0 : ℝ) ≤ Real.exp (3 * η - 3) * blockT θ m := by
      have h1 : (0 : ℝ) < blockT θ m := blockT_pos θ m
      have h2 : (0 : ℝ) < Real.exp (3 * η - 3) := Real.exp_pos _
      positivity
    have he3 : Real.exp (3 * η - 3) * Real.exp 3 = Real.exp (3 * η) := by
      rw [← Real.exp_add]; ring_nf
    have hden : (0 : ℝ) < Real.sqrt (blockScale θ m) * Real.log (blockScale θ m) := by
      have h1 : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
      have h2 : (0 : ℝ) < Real.log (blockScale θ m) := by
        rw [log_blockScale]; exact Real.exp_pos _
      positivity
    have hTle : Real.exp (3 * η - 3) * blockT θ m
        ≤ Real.exp (3 * η) * (blockThirdConst * (8 * Real.log 4))
          / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m)) :=
      le_of_eq (by rw [blockT, ← he3]; field_simp [hden.ne'])
    have h := hθn θ η _ _ _ m hθn' hη0 hηE hVge hT0 hKb0 hKb hTle
    rw [blockEps, blockQThr, blockWindow]
    refine le_trans h (le_of_eq ?_)
    norm_num
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_primeBlockSub_of_cutoff (X := X) (μ := μ) (n := nR)
      (W := blockWindow) (M := M)
      (T := fun m => Real.exp (3 * η - 3) * blockT θ m) (q := blockQThr θ (3 / 100))
      (ε := blockEps θ) (E := 1 / 4) hX hs hy
      (fun m _ p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m (by omega)) hp)
      (fun m _ p hp => norm_prime_cpow_le_fifth_of_le hres (hsc m) (hσm m (by omega)) hp)
      (fun m _ => by
        have h1 : (0 : ℝ) < blockT θ m := blockT_pos θ m
        have h2 : (0 : ℝ) < Real.exp (3 * η - 3) := Real.exp_pos _
        positivity)
      (fun m _ => blockQThr_pos θ (3 / 100) m)
      (fun m hm => by
        have h := (hV m (le_of_lt hm)).1
        have hpos : (0 : ℝ) < Real.exp (-(2 * η)) := Real.exp_pos _
        intro hzero
        rw [hzero] at h
        norm_num at h
        linarith)
      (fun m hm => blockThirdConst_mul_sum_le_of_le (hm3 m) (hσm m (le_of_lt hm)) (hwn m))
      (fun m hm => hθq Ω X μ hX θ σ η m nT s w (M m) hθq' (by omega) hres hσ0 hη0 hηE
        (hσm m (le_of_lt hm)) (hwn m) (hM0 m) (hM m))
      hnum
      (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le (by linarith) nR) (by norm_num)
  have hNlaw' : ∀ m, Q.map (N m)
      = gaussianReal (blockGaussMean X μ θ nR s w m) (blockGaussVar X μ θ nR s w m) := by
    intro m
    rw [hNlaw m, congrFun (blockGaussMeanAt_eq hX hs hy w) m,
      congrFun (blockGaussVarAt_eq hX hs hy w) m]
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw', fun k hk => ?_⟩
  have h := hcmp k hk
  rwa [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h

/-! ### From the comparison to a Gaussian walk

Proposition 5 wants a *centred* walk `G` together with the drift `θ m`, related by
`N m = G m + θ m`.  `RMF.isGaussianWalk_sub_const` does the centring; what has to be supplied here
is that the drift of the padded family agrees with `blockMean` below the horizon, so that
`RMF.abs_sum_blockMean_sub_le` — which is stated for `blockMean` — is the drift estimate
Proposition 5 asks for. -/

/-- Below the horizon the padded drift is the block drift, so their partial sums agree. -/
lemma sum_blockGaussMean_eq (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) {j : ℕ} (hj : j ≤ n + 1) :
    ∑ m ∈ Finset.range j, blockGaussMean X μ θ n s w m
      = ∑ m ∈ Finset.range j, blockMean X μ (blockCutoff θ n) s w (primeBlockSub θ m) :=
  Finset.sum_congr rfl fun m hm => by
    have : m < j := Finset.mem_range.1 hm
    exact blockGaussMean_of_le (by omega)

/-- The constant of the drift estimate, `4e² + 120e²e^{-(1+θ)} + 4e²·e²e^{-θ} + 4·blockDriftConst`.
It depends on `θ` only, not on `n` (`RMF.abs_sum_blockMean_sub_le`).  The last summand covers
Harper's block-dependent offsets, which move the drift by at most `4·blockDriftConst`
(`RMF.abs_sum_cos_sub_one_primeBlockSub_le`); `blockDriftConst` is an absolute `tsum`. -/
noncomputable def driftConst (θ : ℝ) : ℝ :=
  4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ))
    + 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ))
    + 4 * blockDriftConst

lemma driftConst_nonneg (θ : ℝ) : 0 ≤ driftConst θ := by
  rw [driftConst]
  have h1 : (0 : ℝ) ≤ 4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ))
      + 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ)) := by positivity
  linarith [blockDriftConst_nonneg]

/-- The drift constant decreases in the block offset: the two error terms are `e^{-θ}`. -/
lemma driftConst_antitone {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) : driftConst θ₂ ≤ driftConst θ₁ := by
  rw [driftConst, driftConst]
  have he : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have h1 : Real.exp (-(1 + θ₂)) ≤ Real.exp (-(1 + θ₁)) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-θ₂) ≤ Real.exp (-θ₁) := Real.exp_le_exp.2 (by linarith)
  have hA : 120 * Real.exp 2 * Real.exp (-(1 + θ₂))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ₁)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hB : 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ₂))
      ≤ 4 * Real.exp 2 * (Real.exp 2 * Real.exp (-θ₁)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 he.le) (by positivity)
  linarith

/-- **The barrier slope**, `result2Slope(1/16, 9/2) + 2 + driftConst θ`: Probability Result 2's
slope, plus the `2` by which Lemma 4 widens and the drift constant — what `RMF.proposition5_lower`
needs its slope to absorb (Harper's "provided `B` is fixed large enough").  It depends on `θ`,
which moves with `x` through `{log log x}`, but `driftConst` is antitone, so for `θ ≥ 125` it lies
in the fixed interval `[result2Slope + 2 + 4e² + 4·blockDriftConst, blockSlope 125]`. -/
noncomputable def blockSlope (θ : ℝ) : ℝ :=
  result2Slope (1 / 16) (9 / 2) + 2 + driftConst θ

/-- **The tilt is mild once the top `⌈\log K⌉` blocks are dropped.**  `RMF.sigma_le_mul_exp_sub`
says `η_m = Ke^{m-n}`; this is that at `m = n - r` with `r` large enough to bring it under `1`. -/
lemma sigma_le_one_of_drop {θ σ K : ℝ} {n r : ℕ} (hK : K ≤ Real.exp r) (hrn : r ≤ n)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |σ| * Real.log (blockScale θ (n - r + 1)) ≤ 1 := by
  refine le_trans (sigma_le_mul_exp_sub θ σ K hσ) ?_
  have hcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) := Nat.cast_sub hrn
  rw [hcast, show (n : ℝ) - (r : ℝ) - (n : ℝ) = -(r : ℝ) by ring, Real.exp_neg,
    inv_eq_one_div, mul_one_div, div_le_one (Real.exp_pos _)]
  exact hK

/-- **The drop of `RMF.exists_drop`**, `⌈\log\max(E₀,1)⌉`: the number of top blocks the barrier
gives up to obtain the tilt bound `η ≤ e^d`. -/
noncomputable def dropOf (E₀ : ℝ) : ℕ := ⌈Real.log (max E₀ 1)⌉₊

/-- **`RMF.dropOf` does cover the tilt**: `\max(E₀,1) ≤ e^{dropOf E₀}`. -/
lemma le_exp_dropOf (E₀ : ℝ) : max E₀ 1 ≤ Real.exp (dropOf E₀) := by
  rw [dropOf]
  have hmax1 : (1 : ℝ) ≤ max E₀ 1 := le_max_right _ _
  have h1 : Real.log (max E₀ 1) ≤ ((⌈Real.log (max E₀ 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 := Real.exp_le_exp.2 h1
  rwa [Real.exp_log (by linarith : (0 : ℝ) < max E₀ 1)] at h2

/-- **A drop that covers a given tilt bound.**  `\max(E₀,1) ≤ e^d` for `d = ⌈\log\max(E₀,1)⌉`,
which is what a caller supplies to the `_of_top` statements: they ask for `η ≤ e^d`, and this is
what turns a bound `η ≤ E₀` into one. -/
lemma exists_drop (E₀ : ℝ) : ∃ d : ℕ, max E₀ 1 ≤ Real.exp d :=
  ⟨dropOf E₀, le_exp_dropOf E₀⟩

/-- **Lemma 3 for the Steinhaus RMF at a general tilt, with constants independent of the tilt**:
the tilt hypothesis is at the top block, `|σ|·log x_{n+1} ≤ η` (what the lower reduction supplies
at `σ = 4V/log x`), while the walk runs to `n - d`, for any `d` with `η ≤ e^d` and `2d ≤ n`.  `θ₀`
is quantified before `d`, so it does not see the tilt; a caller with `η ≤ E₀` takes
`d = ⌈log max(E₀,1)⌉` (`RMF.exists_drop`).  On `m ≤ n - d` the per-block scale is at most `1`
(`RMF.sigma_le_one_of_drop`), so the variance bracket and every constant of the
Probability-Result tower are those of the `η ≤ 1` case. -/
theorem exists_isWindowComparison_steinhaus_of_top (a Bs : ℝ) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∃ θ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (d n : ℕ) (s : ℂ) (M : ℕ → ℝ),
      θ₀ ≤ θ → 2 * d ≤ n → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
      |σ| * Real.log (blockScale θ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
        IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
        (∀ m, Q.map (N m)
          = gaussianReal (blockGaussMean X μ θ (n - d) s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)
              (blockGaussVar X μ θ (n - d) s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m)) ∧
        (∀ k, k ≤ n - d → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k))
          (n - d - k) (1 / 2)) := by
  obtain ⟨θ₀, H⟩ := exists_isWindowComparison_steinhaus_of_range 1 a Bs zero_le_one ha hBs
  refine ⟨θ₀, ?_⟩
  intro Ω _ X μ hX θ σ η d n s M hθ hrn hres hσ0 hη0 hηE hσtop hM0 hM
  exact H Ω X μ hX θ σ 1 n (n - d) s M hθ (by omega) hres hσ0 zero_le_one le_rfl
    (sigma_le_one_of_drop le_rfl (by omega) (le_trans hσtop hηE)) hM0 hM

/-- **The drift estimate, in the shape Proposition 5 consumes.**  `RMF.abs_sum_blockMean_sub_le`
with the padded drift in place of the block drift. -/
theorem abs_sum_blockGaussMean_sub_le (hX : IsSteinhausPrimeValues X μ) {s : ℂ} {θ σ : ℝ}
    {n j : ℕ} (hθ3 : (5 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1) :
    |(∑ m ∈ Finset.range j,
        blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) - (j : ℝ)|
      ≤ driftConst θ := by
  rw [sum_blockGaussMean_eq X μ θ n s _ hj, driftConst]
  linarith [abs_sum_blockMean_sub_le hX hθ3 hj hres hσ, blockDriftConst_nonneg]

/-- **The drift constant at a general tilt scale**,
`45√K + 120e²e^{-(1+θ)} + 4e^{4K}·e²e^{-θ} + 4·blockDriftConst`, the analogue of `RMF.driftConst`.
The scale enters as `45√K`, not `e^{2K}`: `RMF.barrier_upper_exponent_le` spends this constant
additively in the exponent (see `RMF.abs_sum_blockMean_sub_le_of_le`).  The `e^{4K}` summand carries
`e^{-θ}`, and `θ` is chosen after `K`; the last summand pays for Harper's offsets. -/
noncomputable def driftConstOf (K θ : ℝ) : ℝ :=
  45 * Real.sqrt K + 120 * Real.exp 2 * Real.exp (-(1 + θ))
    + 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ))
    + 4 * blockDriftConst

lemma driftConstOf_nonneg (K θ : ℝ) : 0 ≤ driftConstOf K θ := by
  rw [driftConstOf]
  have h1 : (0 : ℝ) ≤ 45 * Real.sqrt K + 120 * Real.exp 2 * Real.exp (-(1 + θ))
      + 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ)) := by positivity
  linarith [blockDriftConst_nonneg]

/-- **The drift estimate at a general tilt scale**, in the shape Proposition 5 consumes: the
analogue of `RMF.abs_sum_blockGaussMean_sub_le`, with the constant `RMF.driftConstOf K θ`. -/
theorem abs_sum_blockGaussMean_sub_le_of_le (hX : IsSteinhausPrimeValues X μ) {s : ℂ}
    {θ σ K : ℝ} {n j : ℕ} (hθ3 : (5 : ℝ) ≤ θ) (hj : j ≤ n + 1) (hres : s.re = 1 / 2 + σ)
    (hσ0 : 0 ≤ σ) (hK0 : 0 ≤ K) (hsc : 14 + 2 * K ≤ Real.exp θ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |(∑ m ∈ Finset.range j,
        blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) - (j : ℝ)|
      ≤ driftConstOf K θ := by
  rw [sum_blockGaussMean_eq X μ θ n s _ hj, driftConstOf]
  linarith [abs_sum_blockMean_sub_le_of_le hX hθ3 hj hres hσ0 hK0 hsc hσ,
    blockDriftConst_nonneg]

/-- The observed field is measurable: a finite sum of `localLog`s of the prime values. -/
lemma measurable_blockLocalLog (hX : IsSteinhausPrimeValues X μ) (θ : ℝ) (w : Nat.Primes → ℂ)
    (m : ℕ) :
    Measurable (fun ω => ∑ p ∈ primeBlockSub θ m, localLog (w p) (X (p : ℕ) ω)) :=
  Finset.measurable_sum _ fun p _ =>
    (measurable_localLog (w p)).comp (hX.measurable (p : ℕ) p.2)

/-- **The Gaussian walk for the Steinhaus RMF at a general tilt scale**:
`RMF.exists_isWindowComparison_steinhaus_of_le` centred, `G_m = N_m - θ_m` a Gaussian walk with
variances in `[e^{-2η}/4, 9/2]` at every index (Probability Results 1 and 2 take the bracket as a
parameter), and `N_m = G_m + θ_m` Proposition 5's `hNG`.  Only the lower end of the bracket moves
with the tilt (`RMF.blockGaussVar_bounds_of_le`). -/
theorem exists_isGaussianWalk_steinhaus_of_le
    (E₀ a Bs : ℝ) (hE₀ : 0 ≤ E₀) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∃ θ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (n : ℕ) (s : ℂ) (M : ℕ → ℝ),
      θ₀ ≤ θ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale θ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ) (v : ℕ → ℝ≥0),
        IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
        (∀ m ω, N m ω
          = G m ω + blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) ∧
        (∀ i, Real.exp (-(2 * η)) / 4 ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 9 / 2) ∧
        (∀ k, k ≤ n → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
          (1 / 2)) := by
  obtain ⟨θw, hθw⟩ := exists_isWindowComparison_steinhaus_of_le E₀ a Bs hE₀ ha hBs
  refine ⟨max θw (max 125 (Real.log (14 + 2 * E₀))), ?_⟩
  intro Ω _ X μ hX θ σ η n s M hθ hres hσ0 hη0 hηE hσtop hM0 hM
  have hθw' : θw ≤ θ := le_trans (le_max_left _ _) hθ
  have hθ125 : (125 : ℝ) ≤ θ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hθ
  have hθlog : Real.log (14 + 2 * E₀) ≤ θ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hθ
  have hθE : (14 : ℝ) + 2 * E₀ ≤ Real.exp θ := by
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hθlog
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    hθw Ω X μ hX θ σ η n s M hθw' hres hσ0 hη0 hηE hσtop hM0 hM
  have hσm := hsigma_of_top_of_le hσtop
  have hs : 0 < s.re :=
    re_pos_of_block_of_le hres (scale_cond_of_le hηE hθE) (hσm 0 (Nat.zero_le n))
  have hwn : ∀ j : ℕ, j ≤ n → ∀ p ∈ primeBlockSub θ j,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun _ _ p _ => norm_sq_prime_cpow_neg p hres
  have hvb := blockGaussVar_bounds_of_le hX (by linarith : (8 : ℝ) ≤ θ) hs hres hσ0
    (fun j => scale_cond_of_le hηE hθE) hσm hwn
  exact ⟨Ω', mΩ', Q, fun m ω => N m ω
      - blockGaussMean X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m, N,
    blockGaussVar X μ θ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)), hQ,
    isGaussianWalk_sub_const hNm hNi hNlaw, hNm, fun m ω => by ring,
    fun i => (hvb i).1, fun i => (hvb i).2, hcmp⟩

/-- **The Gaussian walk at a general tilt, with the bracket `[1/16, 9/2]`**: the walk stops `d`
blocks below the top (`η ≤ e^d`, `2d ≤ n`), where `RMF.sigma_le_one_of_drop` puts the per-block
scale under `1`, while the tilt stays at the top.  Every constant of the Probability-Result tower
is a rational function of `√v_min` and `1/v_min` (e.g. `RMF.result1LowerConst ∝ min(1, √v_min)`),
so a bracket free of `E₀` makes `RMF.result2Slope`, the barrier slope and the block offset free of
it too. -/
theorem exists_isGaussianWalk_steinhaus_of_top (a Bs : ℝ) (ha : 0 ≤ a) (hBs : 0 < Bs) :
    ∃ θ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (θ σ η : ℝ) (d n : ℕ) (s : ℂ) (M : ℕ → ℝ),
      θ₀ ≤ θ → 2 * d ≤ n → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
      |σ| * Real.log (blockScale θ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M m) → (∀ m, M m ≤ a + Bs * m) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ)
          (v : ℕ → ℝ≥0),
        IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
        (∀ m ω, N m ω
          = G m ω + blockGaussMean X μ θ (n - d) s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) ∧
        (∀ i, (1 : ℝ) / 16 ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 9 / 2) ∧
        (∀ k, k ≤ n - d → IsWindowComparison
          (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
          (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
            localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
          (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k))
          (n - d - k) (1 / 2)) := by
  obtain ⟨θ₁, H⟩ := exists_isWindowComparison_steinhaus_of_top a Bs ha hBs
  refine ⟨max θ₁ 125, ?_⟩
  intro Ω _ X μ hX θ σ η d n s M hθ hrn hres hσ0 hη0 hηE hσtop hM0 hM
  have hθ₁ : θ₁ ≤ θ := le_trans (le_max_left _ _) hθ
  have hθ125 : (125 : ℝ) ≤ θ := le_trans (le_max_right _ _) hθ
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    H Ω X μ hX θ σ η d n s M hθ₁ hrn hres hσ0 hη0 hηE hσtop hM0 hM
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  -- on the shortened range the tilt scale is at most `1`, so the bracket is the absolute one
  have hσ1 : |σ| * Real.log (blockScale θ (n - d + 1)) ≤ 1 :=
    sigma_le_one_of_drop le_rfl (by omega) (le_trans hσtop hηE)
  have hσ := hsigma_of_top hσ1
  have hm3 : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + θ := by push_cast; linarith
  have hs : 0 < s.re := re_pos_of_block hm3 hres (hσ 0 (Nat.zero_le _))
  have hwn : ∀ j : ℕ, j ≤ n - d → ∀ p ∈ primeBlockSub θ j,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
    fun _ _ p _ => norm_sq_prime_cpow_neg p hres
  have hvb := blockGaussVar_bounds hX (by linarith : (8 : ℝ) ≤ θ) hs hres hσ hwn
  exact ⟨Ω', mΩ', Q, fun m ω => N m ω - blockGaussMean X μ θ (n - d) s w m, N,
    blockGaussVar X μ θ (n - d) s w, hQ,
    isGaussianWalk_sub_const hNm hNi hNlaw, hNm, fun m ω => by ring,
    fun i => (hvb i).1, fun i => (hvb i).2, hcmp⟩

/-! ### Proposition 5, for the Steinhaus random multiplicative function

Every hypothesis of `RMF.proposition5_lower` is supplied from the Steinhaus side: the walk and its
variance bracket from `RMF.exists_isGaussianWalk_steinhaus_of_le` (or `_of_top`), the drift from
`RMF.abs_sum_blockGaussMean_sub_le_of_le` (or `RMF.abs_sum_blockGaussMean_sub_le`), the window
widths from `RMF.sum_inv_sq_range_le_two`, the comparison at shift `0`, and measurability from
`RMF.measurable_blockLocalLog`.  The caller supplies the barrier data `M`, `M'`, `hf`, `a`, `n` and
the two size conditions on `n`. -/

/-- `RMF.driftConstOf` is monotone in the tilt scale: `45√K` and `e^{4K}` both are. -/
lemma driftConstOf_mono {K E θ : ℝ} (h : K ≤ E) :
    driftConstOf K θ ≤ driftConstOf E θ := by
  rw [driftConstOf, driftConstOf]
  have h1 : Real.sqrt K ≤ Real.sqrt E := Real.sqrt_le_sqrt h
  have h2 : Real.exp (4 * K) ≤ Real.exp (4 * E) := Real.exp_le_exp.2 (by linarith)
  have hpos : (0 : ℝ) ≤ Real.exp 2 * Real.exp (-θ) := by positivity
  have hB : 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ))
      ≤ 4 * Real.exp (4 * E) * (Real.exp 2 * Real.exp (-θ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos
  linarith

/-- And antitone in the block offset, exactly as `RMF.driftConst_antitone`: the two terms that
see `θ` see it as `e^{-θ}`. -/
lemma driftConstOf_antitone {K θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    driftConstOf K θ₂ ≤ driftConstOf K θ₁ := by
  rw [driftConstOf, driftConstOf]
  have h1 : Real.exp (-(1 + θ₂)) ≤ Real.exp (-(1 + θ₁)) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-θ₂) ≤ Real.exp (-θ₁) := Real.exp_le_exp.2 (by linarith)
  have hA : 120 * Real.exp 2 * Real.exp (-(1 + θ₂))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ₁)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hB : 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ₂))
      ≤ 4 * Real.exp (4 * K) * (Real.exp 2 * Real.exp (-θ₁)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos 2).le)
      (by positivity)
  linarith

/-- **The barrier slope at a general tilt scale**,
`result2Slope(e^{-2E}/4, 9/2) + 2 + driftConstOf E θ`, the analogue of `RMF.blockSlope`.  The tilt
enters twice: as `45√E` through `RMF.driftConstOf`, the drift the barrier absorbs, and through the
lower end `e^{-2E}/4` of the variance bracket in `result2Slope`.  Both are fixed once `E` is. -/
noncomputable def blockSlopeOf (E θ : ℝ) : ℝ :=
  result2Slope (Real.exp (-(2 * E)) / 4) (9 / 2) + 2 + driftConstOf E θ

lemma blockSlopeOf_pos (E θ : ℝ) : 0 < blockSlopeOf E θ := by
  rw [blockSlopeOf]
  linarith [le_result2Slope (Real.exp (-(2 * E)) / 4) (9 / 2 : ℝ), driftConstOf_nonneg E θ]

/-- And at least `20`, which is what the maximal-barrier chain asks of a slope.  Probability
Result 2's own slope already exceeds it, and both the `+2` and `RMF.driftConstOf` are
non-negative. -/
lemma twenty_le_blockSlopeOf (E θ : ℝ) : (20 : ℝ) ≤ blockSlopeOf E θ := by
  rw [blockSlopeOf]
  linarith [le_result2Slope (Real.exp (-(2 * E)) / 4) (9 / 2 : ℝ), driftConstOf_nonneg E θ]

/-- The slope is positive: `result2Slope ≥ 20` and `driftConst ≥ 0`. -/
lemma blockSlope_pos (ϑ : ℝ) : 0 < blockSlope ϑ := by
  rw [blockSlope]
  have h20 := le_result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ)
  have hd := driftConst_nonneg ϑ
  linarith

/-! ### Both halves, at a general tilt scale -/

/-- **Proposition 5 for the Steinhaus RMF at a general tilt scale, both bounds**: for
`0 ≤ η ≤ E₀`, `|σ|·log x_{n+1} ≤ η`, barrier data `M`, `M'` meeting the envelope conditions, `a`
past an explicit level, `n` past the two size conditions and `|h(j)| ≤ 10 log j`,
`α·min{1, a/√n} ≤ P̃(-a - Bj ≤ S_j ≤ a + j + h(j) ∀ j ≤ n) ≤ A·min{1, a/√n}` at the slope
`B = RMF.blockSlopeOf E₀ 125`, with `α` and `A` written out.  Both halves come from one call to
`RMF.exists_isGaussianWalk_steinhaus_of_le`, so that they concern the same event under one `ϑ₀`;
two separate existentials would give unrelated `ϑ₀`.  The halves carry different envelopes, the
lower one free of `a`, the upper one needed only above `a`. -/
theorem exists_proposition5_steinhaus_of_le
    (E₀ a₀ Bs : ℝ) (hE₀ : 0 ≤ E₀) (ha₀ : 0 ≤ a₀) (hBs : 0 < Bs) :
    ∃ ϑ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (ϑ σ η a : ℝ) (n : ℕ) (s : ℂ) (M M' hf : ℕ → ℝ),
      ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
      |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M' m) → (∀ m, M' m ≤ a₀ + Bs * m) →
      (∀ j, 0 ≤ M j) →
      (∀ j, 1 ≤ j → j ≤ n → blockSlopeOf E₀ 125 * j ≤ M j ∧
        blockSlopeOf E₀ 125 * j + j + hf j ≤ M j) →
      (∀ j : ℕ, a < (j : ℝ) → j ≤ n →
        (3 + blockSlopeOf E₀ 125) * a + blockSlopeOf E₀ 125 * j + j
          + 20 * Real.log j ≤ M j) →
      (∀ m, m < n → M m + M (m + 1) + blockWindow m ≤ M' m) →
      max (max (max 1 (result2Threshold (Real.exp (-(2 * E₀)) / 4) (9 / 2)
            + 2 + driftConstOf E₀ 125)) (4 + 2 * driftConstOf E₀ 125))
        (max 1 (result1Threshold (Real.exp (-(2 * E₀)) / 4) (9 / 2))) ≤ a →
      4 ≤ n → 4 * Real.log n ^ 20 ≤ (n : ℝ) →
      4 * Real.log n ^ 8 ≤ (n : ℝ) * (Real.exp (-(2 * E₀)) / 4) →
      (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
      result1LowerConst (Real.exp (-(2 * E₀)) / 4) (9 / 2) / 2 / 4 * min 1 (a / Real.sqrt n)
          ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
              (barrierEvent
                (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                  localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) n
                (fun j => -a - blockSlopeOf E₀ 125 * j)
                (fun j => a + j + hf j))).toReal
        ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
              (barrierEvent
                (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                  localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) n
                (fun j => -a - blockSlopeOf E₀ 125 * j)
                (fun j => a + j + hf j))).toReal
            ≤ 2 * result1Const (Real.exp (-(2 * E₀)) / 4) (9 / 2)
                * (Real.sqrt 2 * (15 + blockSlopeOf E₀ 125
                    + 2 * driftConstOf E₀ 125 + 10 * Real.log 2))
              * min 1 (a / Real.sqrt n) := by
  obtain ⟨ϑ₁, hwalk⟩ := exists_isGaussianWalk_steinhaus_of_le E₀ a₀ Bs hE₀ ha₀ hBs
  refine ⟨max ϑ₁ (max 125 (Real.log (14 + 2 * E₀))), ?_⟩
  intro Ω _ X μ hX ϑ σ η a n s M M' hf hϑ hres hσ0 hη0 hηE hσtop hM'0 hM' hM0 hMcap hMup
    hMM ha hn4 hbig hbig2 hhf
  have hϑ₁' : ϑ₁ ≤ ϑ := le_trans (le_max_left _ _) hϑ
  have hϑ125 : (125 : ℝ) ≤ ϑ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hϑ
  have hϑlog : Real.log (14 + 2 * E₀) ≤ ϑ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hϑ
  have hϑE : (14 : ℝ) + 2 * E₀ ≤ Real.exp ϑ := by
    have hpos : (0 : ℝ) < 14 + 2 * E₀ := by linarith
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hϑlog
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hGw, hNm, hNG, hvlo, hvhi, hcmp⟩ :=
    hwalk Ω X μ hX ϑ σ η n s M' hϑ₁' hres hσ0 hη0 hηE hσtop hM'0 hM'
  have hσm := hsigma_of_top_of_le hσtop
  have hs : 0 < s.re :=
    re_pos_of_block_of_le hres (scale_cond_of_le hηE hϑE) (hσm 0 (Nat.zero_le n))
  have hP : IsProbabilityMeasure
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ) :=
    hX.isProbabilityMeasure_tiltedMeasure (blockCutoff ϑ n) hs
  have hvlo' : ∀ i, Real.exp (-(2 * E₀)) / 4 ≤ (v i : ℝ) := by
    intro i
    have hE : Real.exp (-(2 * E₀)) ≤ Real.exp (-(2 * η)) := Real.exp_le_exp.2 (by linarith)
    linarith [hvlo i]
  have hC : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j,
      blockGaussMean X μ ϑ n s (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) - (j : ℝ)|
        ≤ driftConstOf E₀ 125 := by
    intro j hj
    refine le_trans (abs_sum_blockGaussMean_sub_le_of_le hX (by linarith : (5 : ℝ) ≤ ϑ)
      (by omega) hres hσ0 hη0 (by linarith) hσtop) ?_
    exact le_trans (driftConstOf_mono hηE) (driftConstOf_antitone hϑ125)
  have hcmp' : IsWindowComparison
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ) Q
      (fun m ω => ∑ p ∈ primeBlockSub ϑ (m + ⌊a⌋₊),
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
      (fun m => N (m + ⌊a⌋₊)) (fun m => blockWindow (m + ⌊a⌋₊))
      (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) (1 / 2) := by
    by_cases hk : ⌊a⌋₊ ≤ n
    · exact hcmp ⌊a⌋₊ hk
    · rw [show n - ⌊a⌋₊ = 0 from by omega]
      exact isWindowComparison_zero _ _ _ _ (by norm_num)
  constructor
  · refine proposition5_lower (B := blockSlopeOf E₀ 125)
      hGw (by positivity) hvlo' hvhi
      (driftConstOf_nonneg _ _) (by rw [blockSlopeOf]) _ hP _ N
      blockWindow M M' n (1 / 2) a hf
      (fun m => measurable_blockLocalLog hX ϑ (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) hNm hNG
      hC (fun m => blockWindow_pos m)
      (fun j _ => sum_inv_sq_range_le_two j) hM0 ?_ hMM (by norm_num) le_rfl
      (hcmp 0 (Nat.zero_le n)) (le_trans (le_max_left _ _) ha) (by omega) hbig hbig2 hhf
    intro j hj1 hjn
    have hb := hMcap j hj1 hjn
    rw [blockSlopeOf] at hb
    exact hb
  · exact proposition5_upper hGw (by positivity) hvlo' hvhi (driftConstOf_nonneg _ _)
      (blockSlopeOf_pos _ _)
      _ hP _ N blockWindow M M' n (1 / 2) a hf
      (fun m => measurable_blockLocalLog hX ϑ (fun p => ((p : ℕ) : ℂ) ^ (-s)) m) hNm hNG
      hC (fun m => blockWindow_pos m)
      (fun j _ => sum_inv_sq_range_le_two j) hM0 hMup hMM (by norm_num) le_rfl hcmp'
      (le_trans (le_max_right _ _) ha) hn4 hbig hbig2 hhf

/-! ### The envelope is a condition on `θ` alone

The envelope looks like a hypothesis about the barrier data, but it is not: every quantity in it is
either absolute or capped.  The slope `blockSlope θ` is bounded by `blockSlope 125` because
`driftConst` is antitone; the `a`-term enters only through `min a (m+1)`, which is at most `m+1`;
and the remaining terms are linear in `m` while the right side `(1/40)e^{(m+1+θ)/2}` is
exponential.  So the whole thing collapses to `θ ≥ θ₀` for one absolute `θ₀`.

The point of `RMF.blockOffsetThreshold` is that it can be *defined* in terms of `blockSlope 125`
without that number ever being evaluated — which is exactly Harper's "provided `B` is fixed large
enough".  The numerics are then nobody's business: they say where `θ₀` sits on the line, not whether
the argument works. -/

/-- The block offset at which the envelope closes, uniformly in `m` and in `a`. -/
noncomputable def blockOffsetThreshold : ℝ :=
  max 125 (2 * Real.log (80 * (4 * blockSlope 125 + 62)) - 1)

lemma le_blockOffsetThreshold : (125 : ℝ) ≤ blockOffsetThreshold := le_max_left _ _

/-- **The envelope, from the offset alone.**  No hypothesis on `M`, none on `a` beyond `1 ≤ a`, and
none on `m`.

Bounding `min a (m+1)` by `m+1` and `log(m+1)` by `m` makes the left side at most `(4B₀+62)(m+1)`,
while `e^{m/2} ≥ (m+1)/2` makes the right side at least `(1/80)e^{(1+θ)/2}(m+1)`; the `(m+1)`
cancels, leaving the definition of `θ₀`. -/
lemma envelope_of_le {ϑ a : ℝ} {m : ℕ} (hϑ : blockOffsetThreshold ≤ ϑ) (ha : 1 ≤ a) :
    2 * (3 + blockSlope 125) * min a ((m : ℝ) + 1) + blockSlope 125 * (2 * (m : ℝ) + 1)
        + (2 * (m : ℝ) + 1) + 40 * Real.log ((m : ℝ) + 1) + 14
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB0 : (0 : ℝ) < blockSlope 125 := blockSlope_pos 125
  -- `√(log x_{m+1})`, as an exponential
  have hsq : Real.sqrt (Real.log (blockScale ϑ (m + 1)))
      = Real.exp ((((m : ℝ) + 1) + ϑ) / 2) := by
    rw [log_blockScale, ← Real.exp_half]
    congr 2
    push_cast
    ring
  -- `e^{(1+ϑ)/2} ≥ 80(4B₀ + 62)`
  have hkey : 80 * (4 * blockSlope 125 + 62) ≤ Real.exp ((1 + ϑ) / 2) := by
    have hpos : (0 : ℝ) < 80 * (4 * blockSlope 125 + 62) := by linarith
    have hlog : Real.log (80 * (4 * blockSlope 125 + 62)) ≤ (1 + ϑ) / 2 := by
      have := le_trans (le_max_right (125 : ℝ) _) hϑ
      linarith
    calc 80 * (4 * blockSlope 125 + 62)
        = Real.exp (Real.log (80 * (4 * blockSlope 125 + 62))) := (Real.exp_log hpos).symm
      _ ≤ Real.exp ((1 + ϑ) / 2) := Real.exp_le_exp.2 hlog
  -- `e^{m/2} ≥ (m+1)/2`
  have hexpm : ((m : ℝ) + 1) / 2 ≤ Real.exp ((m : ℝ) / 2) := by
    linarith [Real.add_one_le_exp ((m : ℝ) / 2)]
  have hsplit : Real.exp ((((m : ℝ) + 1) + ϑ) / 2)
      = Real.exp ((1 + ϑ) / 2) * Real.exp ((m : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- the left side, bounded by `(4B₀ + 62)(m+1)`
  have hlogm : Real.log ((m : ℝ) + 1) ≤ (m : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by linarith)]
  have hmin : min a ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min a ((m : ℝ) + 1) := le_min (by linarith) (by linarith)
  have hlhs : 2 * (3 + blockSlope 125) * min a ((m : ℝ) + 1) + blockSlope 125 * (2 * (m : ℝ) + 1)
      + (2 * (m : ℝ) + 1) + 40 * Real.log ((m : ℝ) + 1) + 14
        ≤ (4 * blockSlope 125 + 62) * ((m : ℝ) + 1) := by
    nlinarith [hmin, hmin0, hlogm, hm0, hB0]
  -- and the right side, bounded below by the same shape
  have hrhs : (4 * blockSlope 125 + 62) * ((m : ℝ) + 1)
      ≤ 1 / 40 * Real.exp ((((m : ℝ) + 1) + ϑ) / 2) := by
    rw [hsplit]
    have hstep : 80 * (4 * blockSlope 125 + 62) * (((m : ℝ) + 1) / 2)
        ≤ Real.exp ((1 + ϑ) / 2) * Real.exp ((m : ℝ) / 2) := by
      refine mul_le_mul hkey hexpm (by linarith) (le_trans (by linarith) hkey)
    linarith
  rw [hsq]
  linarith

/-- **The two size conditions on `n` are a threshold.**  Both are instances of
`Real.isLittleO_pow_log_id_atTop`, so past one absolute `n₀` they hold together — along with the
`4 ≤ n` that Lemma 4 wants, which is folded in here so the caller supplies one hypothesis, not
three. -/
lemma exists_blockSizeThreshold :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      4 ≤ n ∧ 4 * Real.log n ^ 20 ≤ (n : ℝ) ∧ 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 16) := by
  have h20 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ 20‖ ≤ 1 / 4 * ‖id x‖ :=
    Real.isLittleO_pow_log_id_atTop.def (by norm_num)
  have h8 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ 8‖ ≤ 1 / 64 * ‖id x‖ :=
    Real.isLittleO_pow_log_id_atTop.def (by norm_num)
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hbase : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ n := Filter.eventually_atTop.2 ⟨4, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ :=
    Filter.eventually_atTop.1 ((hcast.eventually h20).and ((hcast.eventually h8).and hbase))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2, h4⟩ := hn₀ n hn
  have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (pow_nonneg hlog 20),
    abs_of_nonneg hx] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (pow_nonneg hlog 8),
    abs_of_nonneg hx] at h2
  exact ⟨h4, by linarith, by linarith⟩

/-- **Proposition 5 for the Steinhaus RMF at a general tilt, with the `η ≤ 1` constants**: for any
`d` with `η ≤ e^d` and `2d ≤ n`, the two-sided bound holds for the barrier up to `n - d`, with the
tilt at the top block `n`, the bracket `[1/16, 9/2]`, the drift `RMF.driftConst ϑ` and the slope
`RMF.blockSlope 125`, the constants of the `σ = 0` chain.  On `m ≤ n - d` the per-block scale is at
most `1` (`RMF.sigma_le_one_of_drop`), and only `d ≈ log E₀` blocks are given up; in
`RMF.exists_proposition5_steinhaus_of_le` the constants grow exponentially in `E₀`. -/
theorem exists_proposition5_steinhaus_of_top (a₀ Bs : ℝ) (ha₀ : 0 ≤ a₀) (hBs : 0 < Bs) :
    ∃ ϑ₀ : ℝ,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsSteinhausPrimeValues X μ →
      ∀ (ϑ σ η a : ℝ) (d n : ℕ) (s : ℂ) (M M' hf : ℕ → ℝ),
      ϑ₀ ≤ ϑ → 2 * d ≤ n → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
      |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
      (∀ m, 0 ≤ M' m) → (∀ m, M' m ≤ a₀ + Bs * m) →
      (∀ j, 0 ≤ M j) →
      (∀ j, 1 ≤ j → j ≤ n - d → blockSlope 125 * j ≤ M j ∧
        blockSlope 125 * j + j + hf j ≤ M j) →
      (∀ j : ℕ, a < (j : ℝ) → j ≤ n - d →
        (3 + blockSlope 125) * a + blockSlope 125 * j + j + 20 * Real.log j ≤ M j) →
      (∀ m, m < n - d → M m + M (m + 1) + blockWindow m ≤ M' m) →
      max (max (max 1 (result2Threshold (1 / 16) (9 / 2) + 2 + driftConst ϑ))
        (4 + 2 * driftConst ϑ)) (max 1 (result1Threshold (1 / 16) (9 / 2))) ≤ a →
      4 ≤ n - d → 4 * Real.log ((n - d : ℕ) : ℝ) ^ 20 ≤ ((n - d : ℕ) : ℝ) →
      4 * Real.log ((n - d : ℕ) : ℝ) ^ 8 ≤ ((n - d : ℕ) : ℝ) * (1 / 16) →
      (∀ j, 1 ≤ j → j ≤ n - d → |hf j| ≤ 10 * Real.log j) →
      result1LowerConst (1 / 16) (9 / 2) / 2 / 4 * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ))
          ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
              (barrierEvent
                (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                  localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) (n - d)
                (fun j => -a - blockSlope 125 * j)
                (fun j => a + j + hf j))).toReal
        ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ)
              (barrierEvent
                (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                  localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω)) (n - d)
                (fun j => -a - blockSlope 125 * j)
                (fun j => a + j + hf j))).toReal
            ≤ 2 * result1Const (1 / 16) (9 / 2)
                * (Real.sqrt 2 * (15 + blockSlope 125 + 2 * driftConst ϑ + 10 * Real.log 2))
              * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ)) := by
  obtain ⟨ϑ₁, H⟩ := exists_isGaussianWalk_steinhaus_of_top a₀ Bs ha₀ hBs
  refine ⟨max ϑ₁ 125, ?_⟩
  intro Ω _ X μ hΧ ϑ σ η a d n s M M' hf hϑ hrn hres hσ0 hη0 hηE hσtop hM'0 hM' hM0
    hMcap hMup hMM ha hn4 hbig hbig2 hhf
  have hϑ₁ : ϑ₁ ≤ ϑ := le_trans (le_max_left _ _) hϑ
  have hϑ125 : (125 : ℝ) ≤ ϑ := le_trans (le_max_right _ _) hϑ
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hGw, hNm, hNG, hvlo, hvhi, hcmp⟩ :=
    H Ω X μ hΧ ϑ σ η d n s M' hϑ₁ hrn hres hσ0 hη0 hηE hσtop hM'0 hM'
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-s) with hwdef
  -- the tilt is mild on the shortened range, so the `η = 1` estimates apply there
  have hσ1 : |σ| * Real.log (blockScale ϑ (n - d + 1)) ≤ 1 :=
    sigma_le_one_of_drop le_rfl (by omega) (le_trans hσtop hηE)
  have hσm := hsigma_of_top hσ1
  have hm3 : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + ϑ := by push_cast; linarith
  have hs : 0 < s.re := re_pos_of_block hm3 hres (hσm 0 (Nat.zero_le _))
  have hP : IsProbabilityMeasure
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ) :=
    hΧ.isProbabilityMeasure_tiltedMeasure (blockCutoff ϑ n) hs
  have hC : ∀ j, j ≤ n - d → |(∑ m ∈ Finset.range j,
      blockGaussMean X μ ϑ (n - d) s w m) - (j : ℝ)| ≤ driftConst ϑ := fun j hj =>
    abs_sum_blockGaussMean_sub_le hΧ (by linarith : (5 : ℝ) ≤ ϑ) (by omega) hres hσ1
  have hcmp' : IsWindowComparison
      (tiltedMeasure (fun ω => compMultExtension fun p => X p ω) (blockCutoff ϑ n) s μ) Q
      (fun m ω => ∑ p ∈ primeBlockSub ϑ (m + ⌊a⌋₊),
        localLog (((p : ℕ) : ℂ) ^ (-s)) (X (p : ℕ) ω))
      (fun m => N (m + ⌊a⌋₊)) (fun m => blockWindow (m + ⌊a⌋₊))
      (fun m => M' (m + ⌊a⌋₊)) (n - d - ⌊a⌋₊) (1 / 2) := by
    by_cases hk : ⌊a⌋₊ ≤ n - d
    · exact hcmp ⌊a⌋₊ hk
    · rw [show n - d - ⌊a⌋₊ = 0 from by omega]
      exact isWindowComparison_zero _ _ _ _ (by norm_num)
  constructor
  · exact proposition5_lower (B := blockSlope 125) hGw (by norm_num) hvlo hvhi
      (driftConst_nonneg ϑ) (by rw [blockSlope]; linarith [driftConst_antitone hϑ125])
      _ hP _ N blockWindow M M' (n - d) (1 / 2) a hf
      (fun m => measurable_blockLocalLog hΧ ϑ w m) hNm hNG
      hC (fun m => blockWindow_pos m)
      (fun j _ => sum_inv_sq_range_le_two j) hM0
      (fun j hj1 hjn => by
        have hb := hMcap j hj1 hjn
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have hsl : result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConst ϑ
            ≤ blockSlope 125 := by
          rw [blockSlope]; linarith [driftConst_antitone hϑ125]
        have hmul := mul_le_mul_of_nonneg_right hsl hj
        exact ⟨by linarith [hb.1], by linarith [hb.2]⟩)
      hMM (by norm_num) le_rfl
      (hcmp 0 (Nat.zero_le _)) (le_trans (le_max_left _ _) ha) (by omega) hbig hbig2 hhf
  · exact proposition5_upper hGw (by norm_num) hvlo hvhi (driftConst_nonneg ϑ)
      (blockSlope_pos 125)
      _ hP _ N blockWindow M M' (n - d) (1 / 2) a hf
      (fun m => measurable_blockLocalLog hΧ ϑ w m) hNm hNG
      hC (fun m => blockWindow_pos m)
      (fun j _ => sum_inv_sq_range_le_two j) hM0 hMup hMM (by norm_num) le_rfl hcmp'
      (le_trans (le_max_right _ _) ha) hn4 hbig hbig2 hhf

/-! ### Proposition 5 with absolute constants

`RMF.exists_proposition5_steinhaus_of_le` and `RMF.exists_proposition5_steinhaus_of_top` carry the
barrier data `M`, `M'` as parameters, because their two halves constrain them differently and a
caller may want the freedom.  For reading them that freedom is noise: the two envelope hypotheses
force `M` up to an additive constant, and `M m + M (m+1) + W_m ≤ M' m` then forces `M'`.  Choosing
both at their minima collapses the hypotheses on `M` and `M'` into a single inequality in `ϑ`, `a`
and `m`, and leaves constants independent of the space, the function and the barrier. -/

/-- The block-size threshold at any positive lower variance.  `RMF.exists_blockSizeThreshold` is
the case `v = 1/16`; a thinner block needs a longer walk, and `\log^8` against `n` gives it. -/
lemma exists_blockSizeThreshold_of_pos {v : ℝ} (hv : 0 < v) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      4 ≤ n ∧ 4 * Real.log n ^ 20 ≤ (n : ℝ) ∧ 4 * Real.log n ^ 8 ≤ (n : ℝ) * v := by
  have h20 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ 20‖ ≤ 1 / 4 * ‖id x‖ :=
    Real.isLittleO_pow_log_id_atTop.def (by norm_num)
  have h8 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x ^ 8‖ ≤ v / 4 * ‖id x‖ :=
    Real.isLittleO_pow_log_id_atTop.def (by positivity)
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hbase : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ n := Filter.eventually_atTop.2 ⟨4, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ :=
    Filter.eventually_atTop.1 ((hcast.eventually h20).and ((hcast.eventually h8).and hbase))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2, h4⟩ := hn₀ n hn
  have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (pow_nonneg hlog 20),
    abs_of_nonneg hx] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (pow_nonneg hlog 8),
    abs_of_nonneg hx] at h2
  exact ⟨h4, by linarith, by linarith⟩

/-- **Proposition 5 for the Steinhaus RMF at a general tilt scale, with constants depending only
on `E₀`**: there are `ϑ₀, n₀, a₀, α, A`, independent of the space, the function, `ϑ`, `a`, `n` and
`s`, with `α·min{1, a/√n} ≤ P̃(-a - Bj ≤ S_j ≤ a + j + h(j) ∀ j ≤ n) ≤ A·min{1, a/√n}` at
`B = RMF.blockSlopeOf E₀ 125`, for `ϑ ≥ ϑ₀`, `σ ≥ 0`, `0 ≤ η ≤ E₀`, `|σ|·log x_{n+1} ≤ η`,
`a ≥ a₀`, `n ≥ n₀` and `|h(j)| ≤ 10 log j`.  No envelope hypothesis remains: the window bound is
taken at the direct threshold, whose linear envelope the barrier data meet outright.  The slope is
quoted at `125`, not `ϑ₀`, because `ϑ₀` is produced from it. -/
theorem exists_const_proposition5_steinhaus_of_le (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ α A : ℝ), 0 < α ∧ 0 < A ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (ϑ σ η a : ℝ) (n : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
          a₀ ≤ a → n₀ ≤ n →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt n)
                ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) n
                      (fun j => -a - blockSlopeOf E₀ 125 * j)
                      (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) n
                      (fun j => -a - blockSlopeOf E₀ 125 * j)
                      (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt n) := by
  have hB0 : (0 : ℝ) < blockSlopeOf E₀ 125 := blockSlopeOf_pos E₀ 125
  have hv0 : (0 : ℝ) < Real.exp (-(2 * E₀)) / 4 := by positivity
  obtain ⟨n₀, hn₀⟩ := exists_blockSizeThreshold_of_pos hv0
  obtain ⟨ϑ₀, H⟩ := exists_proposition5_steinhaus_of_le E₀ (25 + 2 * blockSlopeOf E₀ 125)
    (48 + 4 * blockSlopeOf E₀ 125) hE₀ (by linarith) (by linarith)
  have hRC1 : (1 : ℝ) ≤ result1Const (Real.exp (-(2 * E₀)) / 4) (9 / 2) :=
    one_le_result1Const _ _
  have h2s : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hdc0 : (0 : ℝ) ≤ driftConstOf E₀ 125 := driftConstOf_nonneg E₀ 125
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨ϑ₀, n₀,
    max (max (max 1 (result2Threshold (Real.exp (-(2 * E₀)) / 4) (9 / 2)
        + 2 + driftConstOf E₀ 125)) (4 + 2 * driftConstOf E₀ 125))
      (max 1 (result1Threshold (Real.exp (-(2 * E₀)) / 4) (9 / 2))),
    result1LowerConst (Real.exp (-(2 * E₀)) / 4) (9 / 2) / 2 / 4,
    2 * result1Const (Real.exp (-(2 * E₀)) / 4) (9 / 2)
      * (Real.sqrt 2 * (15 + blockSlopeOf E₀ 125
          + 2 * driftConstOf E₀ 125 + 10 * Real.log 2)),
    ?_, ?_, ?_⟩
  · have hlc : (0 : ℝ) < result1LowerConst (Real.exp (-(2 * E₀)) / 4) (9 / 2) :=
      result1LowerConst_pos hv0 (by norm_num)
    linarith
  · have hp1 : (0 : ℝ) < 2 * result1Const (Real.exp (-(2 * E₀)) / 4) (9 / 2) := by linarith
    have hin : (0 : ℝ) < 15 + blockSlopeOf E₀ 125
        + 2 * driftConstOf E₀ 125 + 10 * Real.log 2 := by linarith
    exact mul_pos hp1 (by nlinarith [h2s, hin])
  intro Ω' _ Y ν hY ϑ σ η a n s hf hϑ hres hσ0 hη0 hηE hσtop ha hn hhf
  obtain ⟨hn4, hbig, hbig2⟩ := hn₀ n hn
  set B := blockSlopeOf E₀ 125 with hBdef
  set M : ℕ → ℝ := fun j =>
    (3 + B) * min a (j : ℝ) + B * (j : ℝ) + (j : ℝ) + 20 * Real.log (j : ℝ) with hMdef
  set M' : ℕ → ℝ := fun m => M m + M (m + 1) + blockWindow m with hM'def
  have ha1 : (1 : ℝ) ≤ a :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlogn : ∀ j : ℕ, (0 : ℝ) ≤ Real.log (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hj)
  have hlogle : ∀ j : ℕ, Real.log (j : ℝ) ≤ (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      linarith [Real.log_le_sub_one_of_pos hj0]
  have hM0 : ∀ j, 0 ≤ M j := by
    intro j
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    nlinarith [hlogn j, Nat.cast_nonneg (α := ℝ) j, hB0, ha0, hmin]
  -- the linear envelope, which replaces Harper's `√\log` one
  have hMlin : ∀ j : ℕ, M j ≤ (24 + 2 * B) * (j : ℝ) := by
    intro j
    have hmin : min a (j : ℝ) ≤ (j : ℝ) := min_le_right _ _
    have hmul : (3 + B) * min a (j : ℝ) ≤ (3 + B) * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hmin (by linarith)
    simp only [hMdef]
    linarith [hlogle j]
  have hM'0 : ∀ m, 0 ≤ M' m := by
    intro m
    simp only [hM'def]
    linarith [hM0 m, hM0 (m + 1), (blockWindow_pos m).le]
  have hM'lin : ∀ m : ℕ, M' m
      ≤ 25 + 2 * blockSlopeOf E₀ 125 + (48 + 4 * blockSlopeOf E₀ 125) * (m : ℝ) := by
    intro m
    have hW : blockWindow m ≤ 1 := by
      rw [blockWindow, div_le_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have h1 := hMlin m
    have h2 := hMlin (m + 1)
    rw [hcast] at h2
    simp only [hM'def, hBdef] at *
    linarith
  have hMcap : ∀ j, 1 ≤ j → j ≤ n → B * j ≤ M j ∧ B * j + j + hf j ≤ M j := by
    intro j hj1 hjn
    have habs := abs_le.1 (hhf j hj1 hjn)
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    exact ⟨by nlinarith [hlogn j, ha0, hB0, hmin],
      by nlinarith [habs.2, hlogn j, ha0, hB0, hmin]⟩
  have hMup : ∀ j : ℕ, a < (j : ℝ) → j ≤ n →
      (3 + B) * a + B * j + j + 20 * Real.log j ≤ M j := by
    intro j hj _
    have hmin : min a (j : ℝ) = a := min_eq_left hj.le
    simp only [hMdef, hmin]
    exact le_rfl
  have hMM : ∀ m, m < n → M m + M (m + 1) + blockWindow m ≤ M' m := by
    intro m _
    simp only [hM'def]
    exact le_rfl
  exact H Ω' Y ν hY ϑ σ η a n s M M' hf hϑ hres hσ0 hη0 hηE hσtop hM'0 hM'lin hM0
    hMcap hMup hMM ha hn4 hbig hbig2 hhf

/-- **The level `a₀` of `RMF.exists_const_proposition5_steinhaus_of_top`**, written out.  Four
terms: `1`, the threshold of Probability Result 2 shifted by the drift of a `ϑ = 125` block
comparison, twice that drift, and the threshold of Probability Result 1. -/
noncomputable def prop5TopLevel : ℝ :=
  max (max (max 1 (result2Threshold (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConst 125))
    (4 + 2 * driftConst 125)) (max 1 (result1Threshold (1 / 16 : ℝ) (9 / 2 : ℝ)))

/-- **The lower constant `α` of `RMF.exists_const_proposition5_steinhaus_of_top`**, written out:
`result1LowerConst (1/16) (9/2)/8`, the two factors being the union bound against Probability
Result 2's upper half and the four-fold loss in the window comparison.  Since
`result1LowerConst = barrierConstLow/4`, this is `barrierConstLow (1/16) (9/2)/32`. -/
noncomputable def prop5TopLower : ℝ := result1LowerConst (1 / 16 : ℝ) (9 / 2 : ℝ) / 2 / 4

/-- **The upper constant `A` of `RMF.exists_const_proposition5_steinhaus_of_top`**, written out.
Not used by the lower chain; named for symmetry with `RMF.prop5TopLower`. -/
noncomputable def prop5TopUpper : ℝ :=
  2 * result1Const (1 / 16 : ℝ) (9 / 2 : ℝ)
    * (Real.sqrt 2 * (15 + blockSlope 125 + 2 * driftConst 125 + 10 * Real.log 2))

/-- **`RMF.exists_const_proposition5_steinhaus_of_top` with its level named.**  The same
statement, with the level out of the existential and displayed as `RMF.prop5TopLevel`: that is
what lets a caller bound it, since a `Classical.choose`n witness has no size. -/
theorem exists_const_proposition5_steinhaus_of_level :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ), 0 < prop5TopLower ∧ 0 < prop5TopUpper ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (ϑ σ η a : ℝ) (d n : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
          prop5TopLevel ≤ a → 2 * d ≤ n → n₀ ≤ n - d →
          (∀ j, 1 ≤ j → j ≤ n - d → |hf j| ≤ 10 * Real.log j) →
            prop5TopLower * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ))
                ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (n - d)
                      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (n - d)
                      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
                  ≤ prop5TopUpper * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ)) := by
  have hB0 : (0 : ℝ) < blockSlope 125 := blockSlope_pos 125
  obtain ⟨n₀, hn₀⟩ := exists_blockSizeThreshold
  obtain ⟨ϑ₀, H⟩ := exists_proposition5_steinhaus_of_top
    (25 + 2 * blockSlope 125) (48 + 4 * blockSlope 125) (by linarith) (by linarith)
  have hRC1 : (1 : ℝ) ≤ result1Const (1 / 16 : ℝ) (9 / 2 : ℝ) := one_le_result1Const _ _
  have h2s : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hdc0 : (0 : ℝ) ≤ driftConst 125 := driftConst_nonneg 125
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [prop5TopLevel, prop5TopLower, prop5TopUpper]
  refine ⟨max ϑ₀ 125, n₀, ?_, ?_, ?_⟩
  · have hlc : (0 : ℝ) < result1LowerConst (1 / 16 : ℝ) (9 / 2 : ℝ) :=
      result1LowerConst_pos (by norm_num) (by norm_num)
    linarith
  · have hp1 : (0 : ℝ) < 2 * result1Const (1 / 16 : ℝ) (9 / 2 : ℝ) := by linarith
    have hin : (0 : ℝ) < 15 + blockSlope 125 + 2 * driftConst 125 + 10 * Real.log 2 := by
      linarith
    exact mul_pos hp1 (by nlinarith [h2s, hin])
  intro Ω' _ Y ν hY ϑ σ η a d n s hf hϑ hres hσ0 hη0 hηE hσtop ha hdn hn hhf
  have hϑ₀ : ϑ₀ ≤ ϑ := le_trans (le_max_left _ _) hϑ
  have hϑ125 : (125 : ℝ) ≤ ϑ := le_trans (le_max_right _ _) hϑ
  have hd := driftConst_antitone hϑ125
  obtain ⟨hn4, hbig, hbig2⟩ := hn₀ (n - d) hn
  set B := blockSlope 125 with hBdef
  set M : ℕ → ℝ := fun j =>
    (3 + B) * min a (j : ℝ) + B * (j : ℝ) + (j : ℝ) + 20 * Real.log (j : ℝ) with hMdef
  set M' : ℕ → ℝ := fun m => M m + M (m + 1) + blockWindow m with hM'def
  have ha1 : (1 : ℝ) ≤ a :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlogn : ∀ j : ℕ, (0 : ℝ) ≤ Real.log (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hj)
  have hlogle : ∀ j : ℕ, Real.log (j : ℝ) ≤ (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      linarith [Real.log_le_sub_one_of_pos hj0]
  have hM0 : ∀ j, 0 ≤ M j := by
    intro j
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    nlinarith [hlogn j, Nat.cast_nonneg (α := ℝ) j, hB0, ha0, hmin]
  have hMlin : ∀ j : ℕ, M j ≤ (24 + 2 * B) * (j : ℝ) := by
    intro j
    have hmin : min a (j : ℝ) ≤ (j : ℝ) := min_le_right _ _
    have hmul : (3 + B) * min a (j : ℝ) ≤ (3 + B) * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hmin (by linarith)
    simp only [hMdef]
    linarith [hlogle j]
  have hM'0 : ∀ m, 0 ≤ M' m := by
    intro m
    simp only [hM'def]
    linarith [hM0 m, hM0 (m + 1), (blockWindow_pos m).le]
  have hM'lin : ∀ m : ℕ, M' m
      ≤ 25 + 2 * blockSlope 125 + (48 + 4 * blockSlope 125) * (m : ℝ) := by
    intro m
    have hW : blockWindow m ≤ 1 := by
      rw [blockWindow, div_le_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have h1 := hMlin m
    have h2 := hMlin (m + 1)
    rw [hcast] at h2
    simp only [hM'def, hBdef] at *
    linarith
  have hMcap : ∀ j, 1 ≤ j → j ≤ n - d → B * j ≤ M j ∧ B * j + j + hf j ≤ M j := by
    intro j hj1 hjn
    have habs := abs_le.1 (hhf j hj1 hjn)
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    exact ⟨by nlinarith [hlogn j, ha0, hB0, hmin],
      by nlinarith [habs.2, hlogn j, ha0, hB0, hmin]⟩
  have hMup : ∀ j : ℕ, a < (j : ℝ) → j ≤ n - d →
      (3 + B) * a + B * j + j + 20 * Real.log j ≤ M j := by
    intro j hj _
    have hmin : min a (j : ℝ) = a := min_eq_left hj.le
    simp only [hMdef, hmin]
    exact le_rfl
  have hMM : ∀ m, m < n - d → M m + M (m + 1) + blockWindow m ≤ M' m := by
    intro m _
    simp only [hM'def]
    exact le_rfl
  -- the level threshold is quoted at `125`, which is stronger since `driftConst` is antitone
  have hX : result2Threshold (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConst 125 ≤ a :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) ha
  have hY4 : 4 + 2 * driftConst 125 ≤ a :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have hZ : max 1 (result1Threshold (1 / 16 : ℝ) (9 / 2 : ℝ)) ≤ a :=
    le_trans (le_max_right _ _) ha
  have haa : max (max (max 1 (result2Threshold (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConst ϑ))
      (4 + 2 * driftConst ϑ)) (max 1 (result1Threshold (1 / 16 : ℝ) (9 / 2 : ℝ))) ≤ a :=
    max_le (max_le (max_le ha1 (by linarith)) (by linarith)) hZ
  obtain ⟨hlow, hup⟩ := H Ω' Y ν hY ϑ σ η a d n s M M' hf hϑ₀ hdn hres hσ0 hη0 hηE hσtop
    hM'0 hM'lin hM0 hMcap hMup hMM haa hn4 hbig hbig2 hhf
  refine ⟨hlow, le_trans hup ?_⟩
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ)) :=
    le_min zero_le_one (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ hmin0
  have hstep : 15 + B + 2 * driftConst ϑ + 10 * Real.log 2
      ≤ 15 + B + 2 * driftConst 125 + 10 * Real.log 2 := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep (by linarith)) (by linarith)

/-- **Proposition 5 with constants independent of the tilt scale**: there are `ϑ₀, n₀, a₀, α, A`,
independent of the space, the function, `ϑ`, `η`, `d`, `a`, `n` and `s`, with
`α·min{1, a/√(n-d)} ≤ P̃(-a - Bj ≤ S_j ≤ a + j + h(j) ∀ j ≤ n-d) ≤ A·min{1, a/√(n-d)}` at
`B = RMF.blockSlope 125`, whenever `ϑ ≥ ϑ₀`, `σ ≥ 0`, `0 ≤ η ≤ e^d`, `|σ|·log x_{n+1} ≤ η`,
`a ≥ a₀`, `2d ≤ n`, `n - d ≥ n₀` and `|h(j)| ≤ 10 log j`.  Only `d` sees the tilt; a caller with
`η ≤ E₀` takes `d = ⌈log max(E₀,1)⌉` (`RMF.exists_drop`). -/
theorem exists_const_proposition5_steinhaus_of_top :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ α A : ℝ), 0 < α ∧ 0 < A ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (ϑ σ η a : ℝ) (d n : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → s.re = 1 / 2 + σ → 0 ≤ σ → 0 ≤ η → η ≤ Real.exp d →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ η →
          a₀ ≤ a → 2 * d ≤ n → n₀ ≤ n - d →
          (∀ j, 1 ≤ j → j ≤ n - d → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ))
                ≤ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (n - d)
                      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff ϑ n) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLog (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) (n - d)
                      (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt ((n - d : ℕ) : ℝ)) := by
  obtain ⟨ϑ₀, n₀, hα, hA, H⟩ := exists_const_proposition5_steinhaus_of_level
  exact ⟨ϑ₀, n₀, prop5TopLevel, prop5TopLower, prop5TopUpper, hα, hA, H⟩

end RMF
