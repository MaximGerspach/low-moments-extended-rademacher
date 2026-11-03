/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherBlockVariance

/-!
# The Rademacher window comparison, and Harper's Proposition 6

The Rademacher counterpart of the Steinhaus window comparison of `Probability/BlockComparison.lean`,
and the barrier estimate built on it.  Everything above the window comparison is model-agnostic —
`RMF.IsWindowComparison` relates two arbitrary measures and two arbitrary families of real
random variables — so this is the last place the model appears.

**The Lindeberg step itself is generic.**
`RMF.isWindowComparison₁_of_gaussian_family_of_third_moment` takes measurability, independence,
laws, integrability, moment matching and a third-moment bound, all as hypotheses about arbitrary
families.  So the Rademacher comparison is not new mathematics: it is the Steinhaus skeleton with
`localLogAdd` for `localLog`, the squarefree extension for the completely multiplicative one, and
this file's per-prime inputs for the Steinhaus ones.  Four things differ from the Steinhaus
originals, and all four are constants:

* the mean is `|m₁| ≤ (12/5)‖w‖` where Steinhaus has `(49/240)‖w‖` — the Rademacher local mean is
  genuinely of order `‖w‖ ² ` rather than `‖w‖ ³`, and the tilt adds a term of order `‖a‖‖w‖`;
* the second moment is `m₂ ≤ (12/5) ² ‖w‖ ² ` against `(11/5) ² ‖w‖ ² `;
* the third absolute moment is the same `(11/5) ³ ‖w‖ ³`, pointwise on the circle;
* hence `RMF.blockThirdConstAdd` in place of `RMF.blockThirdConst`.

None of the four is visible past the comparison.  On top of it the file proves the Rademacher
analogue of Harper's Lemma 3 (Harper, arXiv:1703.06654) for the block,
`RMF.exists_isWindowComparison_rademacher_of_cutoff`, the Gaussian walk, the drift at Harper's
offsets, and his Proposition 6 with absolute constants
(`RMF.exists_const_proposition5_rademacher_of_offset_of_cutoff`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The two moments, sized -/

lemma memLp_two_localLogAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5) :
    MemLp (fun ω => localLogAdd w (X (p : ℕ) ω)) 2
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  have hmeas : Measurable (fun ω => localLogAdd w (X (p : ℕ) ω)) :=
    (measurable_localLogAdd w).comp (hX.measurable (p : ℕ) p.2)
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    (integrable_localLogAdd_sq_tiltedMeasure hX y hs hp hw)

/-- Cauchy–Schwarz at one prime: the square of the mean is at most the second moment. -/
lemma sq_integral_localLogAdd_le_integral_mul_self (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) ^ 2
      ≤ ∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  have := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  exact sq_integral_le_integral_mul_self (memLp_two_localLogAdd_tiltedMeasure hX y hs hp hw)

/-- The mean at one prime, in the shape the Gaussian bound consumes: `|m₁| ≤ (12/5)‖w‖`.

`RMF.abs_integral_localLogAdd_tiltedMeasure_le` gives `4‖a‖‖w‖ + 8‖w‖ ² `; at `‖a‖, ‖w‖ ≤ 1/5`
that is `(4/5 + 8/5)‖w‖`. -/
lemma abs_integral_localLogAdd_tiltedMeasure_le' (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) :
    |(∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))|
      ≤ 12 / 5 * ‖w‖ := by
  have h := abs_integral_localLogAdd_tiltedMeasure_le hX y hs hp hw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  nlinarith [mul_nonneg (norm_nonneg (((p : ℕ) : ℂ) ^ (-s))) hw0]

/-- The second moment at one prime: `m₂ ≤ (12/5) ² ‖w‖ ² `.

From `RMF.abs_integral_localLogAdd_sq_tiltedMeasure_sub_le`, `m₂ ≤ (Re w) ² + 22‖w‖ ³`, and at
`‖w‖ ≤ 1/5` that is at most `(1 + 22/5)‖w‖ ² = 5.4‖w‖ ² ≤ 5.76‖w‖ ² `. -/
lemma integral_localLogAdd_sq_tiltedMeasure_le (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    (∫ ω, localLogAdd w (X (p : ℕ) ω) ^ 2
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      ≤ (12 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  have h := abs_integral_localLogAdd_sq_tiltedMeasure_sub_le hX y hs hp hw
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  rw [abs_le] at h hre
  nlinarith [h.2, hre.1, hre.2, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 5 - ‖w‖) (sq_nonneg ‖w‖)]

/-! ### The third absolute moment, both halves -/

/-- The Rademacher counterpart of `RMF.blockThirdConst`.  Larger, because the Rademacher local
mean is of order `‖w‖ ² ` and the Steinhaus one is not; invisible past the seam. -/
noncomputable def blockThirdConstAdd : ℝ :=
  (11 / 5 : ℝ) ^ 3 + 4 * (absMomentConst 3 * (12 / 5 : ℝ) ^ 3 + (12 / 5 : ℝ) ^ 3)

/-- **The Gaussian half.**  A Gaussian matched to the two moments has third absolute moment
`O(‖w‖ ³)`, by the size bounds above. -/
theorem integral_abs_cube_matching_localLogAdd_le {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} {Y : Ω' → ℝ} (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5)
    (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      (matchingVar
        (∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        (∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)))) :
    ∫ ω, |Y ω| ^ 3 ∂Q
      ≤ 4 * (absMomentConst 3 * (12 / 5 : ℝ) ^ 3 + (12 / 5 : ℝ) ^ 3) * ‖w‖ ^ 3 := by
  set Pt := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ with hPt
  set m₁ : ℝ := ∫ ω, localLogAdd w (X (p : ℕ) ω) ∂Pt with hm₁
  set m₂ : ℝ := ∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω) ∂Pt with hm₂
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hcs : m₁ ^ 2 ≤ m₂ := sq_integral_localLogAdd_le_integral_mul_self hX y hs hp hw
  have hmean : |m₁| ≤ 12 / 5 * ‖w‖ := abs_integral_localLogAdd_tiltedMeasure_le' hX y hs hp hw ha
  have hmean₃ : |m₁| ^ 3 ≤ (12 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    calc |m₁| ^ 3 ≤ (12 / 5 * ‖w‖) ^ 3 := pow_le_pow_left₀ (abs_nonneg m₁) hmean 3
      _ = (12 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  have hsq : m₂ ≤ (12 / 5 * ‖w‖) ^ 2 := by
    have h := integral_localLogAdd_sq_tiltedMeasure_le hX y hs hp hw
    have hpow : (∫ ω, localLogAdd w (X (p : ℕ) ω) ^ 2 ∂Pt) = m₂ := by
      rw [hm₂]; simp only [pow_two]
    rw [hpow] at h
    calc m₂ ≤ (12 / 5 : ℝ) ^ 2 * ‖w‖ ^ 2 := h
      _ = (12 / 5 * ‖w‖) ^ 2 := by ring
  have hroot : √m₂ ≤ 12 / 5 * ‖w‖ := by
    refine le_trans (Real.sqrt_le_sqrt hsq) ?_
    rw [Real.sqrt_sq (by positivity)]
  have hroot₃ : √m₂ ^ 3 ≤ (12 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by
    calc √m₂ ^ 3 ≤ (12 / 5 * ‖w‖) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 3
      _ = (12 / 5 : ℝ) ^ 3 * ‖w‖ ^ 3 := by ring
  refine le_trans (integral_abs_cube_of_hasLaw_matching hYm hcs hlaw) ?_
  have hc := absMomentConst_nonneg 3
  nlinarith [hroot₃, hmean₃]

/-- **The two halves together, per prime.** -/
theorem third_moment_add_matching_leAdd {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : Ω' → ℝ} (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ} (hw : ‖w‖ ≤ 1 / 5)
    (ha : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5) (hYm : Measurable Y)
    (hlaw : Q.map Y = gaussianReal
      (∫ ω, localLogAdd w (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      (matchingVar
        (∫ ω, localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        (∫ ω, localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)))) :
    (∫ ω, |localLogAdd w (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      + ∫ ω, |Y ω| ^ 3 ∂Q ≤ blockThirdConstAdd * ‖w‖ ^ 3 := by
  have hξ := integral_abs_localLogAdd_cube_tiltedMeasure_le hX y hs hp hw
  have hG := integral_abs_cube_matching_localLogAdd_le hX y hs hp hw ha hYm hlaw
  unfold blockThirdConstAdd
  nlinarith [hξ, hG]

/-! ### The prime moments, and the block variance as their sum -/

/-- The tilted mean at one prime, named so that the Gaussian family can be built from it. -/
noncomputable def primeMeanAdd (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (p : Nat.Primes) : ℝ :=
  ∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
    ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)

/-- The tilted second moment, floored at the square of the mean so that the matched variance is
honest without a hypothesis. -/
noncomputable def primeMoment₂Add (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (p : Nat.Primes) : ℝ :=
  max (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
    (primeMeanAdd X μ y s w p ^ 2)

lemma sq_primeMeanAdd_le (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (p : Nat.Primes) :
    primeMeanAdd X μ y s w p ^ 2 ≤ primeMoment₂Add X μ y s w p := le_max_right _ _

/-- On the block the floor is inactive, by Cauchy–Schwarz. -/
lemma primeMoment₂Add_eq_of_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ‖w p‖ ≤ 1 / 5) :
    primeMoment₂Add X μ y s w p
      = ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  max_eq_left (sq_integral_localLogAdd_le_integral_mul_self hX y hs hp hw)

lemma blockMatchedVarAdd_eq_sum (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    blockMatchedVarAdd X μ y s w B
      = ∑ p ∈ B, matchingVar (primeMeanAdd X μ y s w p) (primeMoment₂Add X μ y s w p) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [primeMoment₂Add_eq_of_le hX y hs (hB hp) (hw p hp)]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    pow_two (localLogAdd (w p) (X (p : ℕ) ω)))

/-- **The block third-moment sum**, the term the Lindeberg swap charges. -/
theorem sum_third_moment_blockAdd_le {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {G : Nat.Primes → Ω' → ℝ} (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) (ha : ∀ p ∈ B, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    (hGm : ∀ p, Measurable (G p))
    (hGlaw : ∀ p ∈ B, Q.map (G p) = gaussianReal
      (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
      (matchingVar
        (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)))) :
    (∑ p ∈ B, ((∫ ω, |localLogAdd (w p) (X (p : ℕ) ω)| ^ 3
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
        + ∫ ω, |G p ω| ^ 3 ∂Q))
      ≤ blockThirdConstAdd * ∑ p ∈ B, ‖w p‖ ^ 3 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p hp =>
    third_moment_add_matching_leAdd hX y hs (hB hp) (hw p hp) (ha p hp) (hGm p) (hGlaw p hp)

/-- **The block increments are independent under the tilt** — the last input the reindexing
needs. -/
theorem iIndepFun_blockSumAdd_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) (θ : ℝ) (w : Nat.Primes → ℂ) :
    iIndepFun (fun m ω => ∑ p ∈ primeBlockSub θ m, localLogAdd (w p) (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) :=
  iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun p => (measurable_localLogAdd (w p)).comp (hX.measurable (p : ℕ) p.2))
    (iIndepFun_localLogAdd_tiltedMeasure_rademacher hX y hs w) (pairwise_disjoint_primeBlockSub θ)

/-! ### The block Gaussian's two parameters -/

/-- The mean of the `m`-th block Gaussian: the tilted drift below the horizon, `0` above. -/
noncomputable def blockGaussMeanAddAt (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ :=
  if m ≤ n then blockMeanAdd X μ y s w (primeBlockSub θ m) else 0

/-- The variance: the matched block variance below the horizon, `1` above.  The `1` is what makes
the variance bracket satisfiable at every index. -/
noncomputable def blockGaussVarAddAt (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) (m : ℕ) : ℝ≥0 :=
  if m ≤ n then blockMatchedVarAdd X μ y s w (primeBlockSub θ m) else 1

@[simp]
lemma blockGaussMeanAddAt_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} {θ : ℝ} {y n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} {m : ℕ} (hm : m ≤ n) :
    blockGaussMeanAddAt X μ θ y n s w m = blockMeanAdd X μ y s w (primeBlockSub θ m) :=
  if_pos hm

@[simp]
lemma blockGaussVarAddAt_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω} {θ : ℝ} {y n : ℕ} {s : ℂ}
    {w : Nat.Primes → ℂ} {m : ℕ} (hm : m ≤ n) :
    blockGaussVarAddAt X μ θ y n s w m = blockMatchedVarAdd X μ y s w (primeBlockSub θ m) :=
  if_pos hm

/-- The square of a local term is integrable under `P~`, in the `ξ * ξ` shape the Lindeberg
step asks for. -/
theorem integrable_localLogAdd_mul_self_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) {p : Nat.Primes} (hp : p ∈ primesBelowSub y) {w : ℂ}
    (hw : ‖w‖ ≤ 1 / 5) :
    Integrable (fun ω => localLogAdd w (X (p : ℕ) ω) * localLogAdd w (X (p : ℕ) ω))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ) := by
  have h := integrable_localLogAdd_sq_tiltedMeasure hX y hs hp hw
  simpa only [pow_two] using h

/-! ### The matched variance as a real number

`RMF.matchingVar` truncates at zero.  On the block the truncation is inactive — Cauchy–Schwarz
gives `m₁ ² ≤ m₂` at every prime — so the coercion is exact and
`RMF.abs_blockVarAdd_sub_le` transfers unchanged. -/

/-- The `ℝ≥0` truncation is inactive on the block. -/
lemma coe_blockMatchedVarAdd (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re)
    {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    ((blockMatchedVarAdd X μ y s w B : ℝ≥0) : ℝ)
      = ∑ p ∈ B, ((∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ^ 2
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ))
          - (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ)) ^ 2) := by
  rw [blockMatchedVarAdd, NNReal.coe_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hcs := sq_integral_localLogAdd_le_integral_mul_self hX y hs (hB hp) (hw p hp)
  have hpow : (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) ^ 2
      ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ))
      = ∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun q => X q ω) y s μ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      pow_two (localLogAdd (w p) (X (p : ℕ) ω)))
  rw [hpow]
  exact coe_matchingVar hcs

/-- **The matched block variance is `∑ (Re w p) ² ` up to a third-order error.**

This is `RMF.abs_blockVarAdd_sub_le` with the `ℝ≥0` coercion resolved — the form the numeric
wrappers consume, and the point at which
`RMF.exists_sum_re_cpow_neg_sq_primeBlockSub_bounds` becomes a bound on the variance the
Gaussian comparison actually uses. -/
theorem abs_coe_blockMatchedVarAdd_sub_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {B : Finset Nat.Primes} (hB : B ⊆ primesBelowSub y) {w : Nat.Primes → ℂ}
    (hw : ∀ p ∈ B, ‖w p‖ ≤ 1 / 5) :
    |((blockMatchedVarAdd X μ y s w B : ℝ≥0) : ℝ) - ∑ p ∈ B, (w p).re ^ 2|
      ≤ ∑ p ∈ B, (42 * ‖w p‖ ^ 3
          + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2) := by
  rw [coe_blockMatchedVarAdd hX y hs hB hw]
  exact abs_blockVarAdd_sub_le hX y hs hB hw

/-! ### The variance bracket, concretely -/

/-- **The block's third-moment sum is below `1/1000` once `9 ≤ m + θ`.**

`RMF.sum_norm_cube_primeBlockSub_le` bounds it by `e³·8\log 4 / (√X·\log X)` with
`X = blockScale θ m`, and at `9 ≤ m + θ` both factors of the denominator exceed `1000` —
`√X` by `RMF.blockWeightSize_le_of_le` at `η = 0`, and `\log X = e^{m+θ} ≥ e⁹` directly. -/
lemma sum_norm_cube_primeBlockSub_le_of_nine {θ σ : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (9 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ 1 / 1000 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he9 : (1000 : ℝ) ≤ Real.exp 9 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 9) (by norm_num) he1.le (by norm_num)
  have hexp : (1000 : ℝ) ≤ Real.exp ((m : ℝ) + θ) := he9.trans (Real.exp_le_exp.2 hmθ)
  -- `√X ≥ 1000`
  have hroot0 : (0 : ℝ) < √(blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
  have hroot : (1000 : ℝ) ≤ √(blockScale θ m) := by
    have h := blockWeightSize_le_of_le (θ := θ) (η := 0) (j := m) (by simpa using by linarith)
    rw [Real.exp_zero] at h
    rw [div_le_div_iff₀ hroot0 (by norm_num)] at h
    linarith
  -- `\log X = e^{m+θ} ≥ 1000`
  have hlog : (1000 : ℝ) ≤ Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact hexp
  have hden : (1000000 : ℝ) ≤ √(blockScale θ m) * Real.log (blockScale θ m) := by
    nlinarith
  have hl40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hnum : Real.exp 3 * (8 * Real.log 4) ≤ 1000 := by
    have h3 : Real.exp 3 ≤ 21 := by
      simpa using exp_natCast_le_of_pow_le (c := 2.7182818286) (k := 3)
        (by linarith [Real.exp_one_lt_d9]) (by norm_num)
    have hl4 : Real.log 4 ≤ 1.4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    nlinarith [Real.exp_pos (3 : ℝ)]
  have hd0 : (0 : ℝ) < √(blockScale θ m) * Real.log (blockScale θ m) :=
    mul_pos hroot0 (by linarith)
  refine (sum_norm_cube_primeBlockSub_le (by linarith : (3 : ℝ) ≤ (m : ℝ) + θ) hσ hwn).trans ?_
  rw [← mul_div_assoc, div_le_iff₀ hd0]
  linarith

/-- **The Rademacher block variance, bracketed.**  Past an absolute threshold `Tsh ≤ τ e^{m+θ}` —
the height condition — the matched block variance satisfies `1/8 ≤ 2·var ≤ 9`, the shape
Probability Results 1 and 2 ask for.  `RMF.exists_sum_re_cpow_neg_sq_primeBlockSub_bounds` puts
`∑ (Re w p)²` in `[1/4, 3/4]`, and `RMF.abs_coe_blockMatchedVarAdd_sub_le` with
`RMF.sum_norm_cube_primeBlockSub_le_of_nine` keeps the matched variance within `52/1000` of it, so
it lies in `[0.198, 0.802]`. -/
theorem exists_blockMatchedVarAdd_concrete_top :
    ∃ Tsh > 0,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (θ σ η : ℝ) (m y : ℕ) (s u : ℂ) (w : Nat.Primes → ℂ),
      0 < s.re → s.re = 1 / 2 + σ → u.re = 1 / 2 + σ →
      (9 : ℝ) ≤ (m : ℝ) + θ → 0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * u.im → (2 * u.im) ^ 2 ≤ Real.exp ((m : ℝ) + θ) →
      Tsh ≤ 2 * u.im * Real.exp ((m : ℝ) + θ) →
      (∀ p ∈ primeBlockSub θ m, w p = ((p : ℕ) : ℂ) ^ (-u)) →
      primeBlockSub θ m ⊆ primesBelowSub y →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9 := by
  obtain ⟨Tsh, hTsh0, hbr⟩ := exists_sum_re_cpow_neg_sq_primeBlockSub_bounds
  refine ⟨Tsh, hTsh0, ?_⟩
  intro Ω _ X μ hX θ σ η m y s u w hs hres hu hmθ hθ hη hη' hσ hτ hτ2 hTsh hwv hB
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hσ1 : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := by linarith
  -- the weights, and the tilt radius, have the same modulus on the block
  have hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p hp => by
    rw [hwv p hp]
    exact norm_sq_prime_cpow_neg p hu
  have han : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p _ =>
    norm_sq_prime_cpow_neg p hres
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun p hp => by
    rw [hwv p hp]
    exact norm_prime_cpow_le_fifth hm3 hu hσ1 hp
  -- the error is at most `52/1000`
  have hcube := sum_norm_cube_primeBlockSub_le_of_nine hmθ hσ1 hwn
  have hterm : ∀ p ∈ primeBlockSub θ m,
      42 * ‖w p‖ ^ 3 + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2
        ≤ 52 * ‖w p‖ ^ 3 := fun p hp => by
    have heq : ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ‖w p‖ ^ 2 := by rw [han p hp, hwn p hp]
    have h5 := hw5 p hp
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    rw [heq]
    nlinarith [mul_nonneg (mul_nonneg h0 h0) h0, pow_nonneg h0 3]
  have herr : (∑ p ∈ primeBlockSub θ m,
      (42 * ‖w p‖ ^ 3 + 48 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 * ‖w p‖ ^ 2)) ≤ 52 / 1000 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    linarith
  -- the main term, in the block's own variables
  have hsum : (∑ p ∈ primeBlockSub θ m, (w p).re ^ 2)
      = ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2 :=
    Finset.sum_congr rfl fun p hp => by rw [hwv p hp]
  obtain ⟨hlo, hhi⟩ := hbr θ σ η m u hu hmθ hθ hη hη' hσ hτ hτ2 hTsh
  have hgap := abs_coe_blockMatchedVarAdd_sub_le hX y hs hB hw5
  rw [abs_le] at hgap
  rw [hsum] at hgap
  constructor <;> linarith [hgap.1, hgap.2]

/-! ### The third-moment bound and the numerator condition -/

lemma blockThirdConstAdd_pos : 0 < blockThirdConstAdd := by
  unfold blockThirdConstAdd
  have := absMomentConst_nonneg 3
  positivity

/-- `blockThirdConstAdd ≤ 200`, from `RMF.absMomentConst_three_le`.  The Steinhaus constant is
`≤ 96`; the Rademacher one is larger because the local mean is of order `‖w‖ ² `. -/
lemma blockThirdConstAdd_le : blockThirdConstAdd ≤ 200 := by
  have h := absMomentConst_three_le
  have h0 := absMomentConst_nonneg 3
  rw [blockThirdConstAdd]
  nlinarith [h, h0]

/-- `RMF.blockThirdConstAdd` times the third-moment bound of
`RMF.sum_norm_cube_primeBlockSub_le` — the `T` of Lemma 3, so that `hTb` becomes definitional. -/
noncomputable def blockTAdd (θ : ℝ) (m : ℕ) : ℝ :=
  blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4
    / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))))

lemma blockTAdd_pos {θ : ℝ} {m : ℕ} (hθ : (0 : ℝ) < Real.log (blockScale θ m)) :
    0 < blockTAdd θ m := by
  have hs : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
  have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  unfold blockTAdd
  have := blockThirdConstAdd_pos
  positivity

/-- **`hTb`, at the named `T`.** -/
lemma blockThirdConstAdd_mul_sum_le {θ σ : ℝ} {m : ℕ} {w : Nat.Primes → ℂ}
    (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    blockThirdConstAdd * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ blockTAdd θ m := by
  rw [blockTAdd]
  exact mul_le_mul_of_nonneg_left (sum_norm_cube_primeBlockSub_le hmθ hσ hwn)
    blockThirdConstAdd_pos.le

/-- **`hnum`, at the named `T`, `q` and `ε`.**  `RMF.blockNum_le_of_le` is generic in the
constant and asks only `Kb ≤ e^100`; here `Kb ≤ 200 · 21 · 12 = 50400 ≤ e^14`. -/
lemma blockNumAdd_le {θ : ℝ} {m : ℕ} {V : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hθ0 : (0 : ℝ) ≤ θ) (hV : 1 / 16 ≤ V) :
    (450 + 4 / Real.sqrt (2 * Real.pi * V)) * blockTAdd θ m ^ (1 / 4 : ℝ)
      ≤ blockEps θ m * blockQ θ m := by
  have hexp3 : Real.exp 3 ≤ 21 := by
    simpa using exp_natCast_le_of_pow_le (c := 2.7182818286) (k := 3)
      (by linarith [Real.exp_one_lt_d9]) (by norm_num)
  have hexp30 : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have hlog4 : 8 * Real.log 4 ≤ 12 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h4]
    linarith [Real.log_two_lt_d9]
  have hlog40 : (0 : ℝ) ≤ 8 * Real.log 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  rw [blockEps, blockQ, blockWindow]
  refine blockNum_le_of_le (Kb := blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4)))
    hmθ hθ0 hV (blockTAdd_pos hlogpos).le
    (mul_nonneg blockThirdConstAdd_pos.le (mul_nonneg hexp30.le hlog40)) ?_ ?_
  · -- `≤ 200 · 21 · 12 = 50400 ≤ e¹⁴ ≤ e¹⁰⁰`
    have hA : Real.exp 3 * (8 * Real.log 4) ≤ 21 * 12 :=
      mul_le_mul hexp3 hlog4 hlog40 (by norm_num)
    have hA0 : (0 : ℝ) ≤ Real.exp 3 * (8 * Real.log 4) := mul_nonneg hexp30.le hlog40
    have h1 : blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4)) ≤ 50400 := by
      calc blockThirdConstAdd * (Real.exp 3 * (8 * Real.log 4))
          ≤ 200 * (Real.exp 3 * (8 * Real.log 4)) :=
            mul_le_mul_of_nonneg_right blockThirdConstAdd_le hA0
        _ ≤ 200 * (21 * 12) := mul_le_mul_of_nonneg_left hA (by norm_num)
        _ = 50400 := by norm_num
    have he1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : (1000000 : ℝ) ≤ Real.exp 14 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.718) (k := 14)
        (by norm_num) he1.le (by norm_num)
    have h3 : Real.exp 14 ≤ Real.exp 100 := Real.exp_le_exp.2 (by norm_num)
    linarith
  · rw [blockTAdd]
    apply le_of_eq
    ring

/-! ### The two-point third-moment constant

`RMF.blockThirdConstAdd` and `RMF.blockTAdd` at two points.  The constant is doubled, because
`hTb` sums four moments per prime where the one-point `hTb` sums two, and the mean's `(12/5)`
becomes `(18/5)` — `RMF.third_moment_pair_add_matching_leAdd` is what pins the three numbers.

It is `≈ 530` where `RMF.blockThirdConst₂` is `≈ 12010`, and that gap is the whole reason nothing
new has to be proved about it: `RMF.blockNum₂_le` is generic in the third-moment bound, so
`RMF.blockThirdConstAdd₂_le_blockThirdConst₂` — pure numerics, `(18/5)³ ≤ (57/5)³` — is all that
is checked, and the two-point `hnum` follows from the Steinhaus one. -/

/-- The Rademacher counterpart of `RMF.blockThirdConst₂`.  **Smaller**, not larger: the Steinhaus
two-fold mean grows from `(49/240)‖w‖` to `(57/5)‖w‖`, where the Rademacher one grows only from
`(12/5)‖w‖` to `(18/5)‖w‖`, because it was already of order `‖w‖` at one point. -/
noncomputable def blockThirdConstAdd₂ : ℝ :=
  2 * ((11 / 5 : ℝ) ^ 3 + 4 * (absMomentConst 3 * (11 / 5 : ℝ) ^ 3 + (18 / 5 : ℝ) ^ 3))

lemma blockThirdConstAdd₂_pos : 0 < blockThirdConstAdd₂ := by
  unfold blockThirdConstAdd₂
  have := absMomentConst_nonneg 3
  positivity

/-- **The Rademacher two-point constant is below the Steinhaus one**, and by a factor `≈ 23`.  The
`absMomentConst` terms are identical, so this is `(18/5) ³ ≤ (57/5) ³ ` and nothing else — no
bound on `c₃` is needed. -/
lemma blockThirdConstAdd₂_le_blockThirdConst₂ : blockThirdConstAdd₂ ≤ blockThirdConst₂ := by
  rw [blockThirdConstAdd₂, blockThirdConst₂]
  norm_num

/-- `RMF.blockThirdConstAdd₂` times the third-moment bound of
`RMF.sum_norm_cube_primeBlockSub_le` — the `T` of the two-point Lemma 3, so that `hTb` becomes
definitional. -/
noncomputable def blockTAdd₂ (θ : ℝ) (m : ℕ) : ℝ :=
  blockThirdConstAdd₂ * (Real.exp 3 * (8 * Real.log 4
    / (Real.sqrt (blockScale θ m) * Real.log (blockScale θ m))))

lemma blockTAdd₂_pos {θ : ℝ} {m : ℕ} (hθ : (0 : ℝ) < Real.log (blockScale θ m)) :
    0 < blockTAdd₂ θ m := by
  have hs : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
  have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  unfold blockTAdd₂
  have := blockThirdConstAdd₂_pos
  positivity

/-- **The two-point `hnum`, at the named `T`, `q` and `ε`.**  `RMF.blockNum₂_le'` with
`RMF.blockTAdd₂` for `RMF.blockT₂`; the constant is smaller, so the same estimate covers it. -/
lemma blockNumAdd₂_le {θ : ℝ} {m : ℕ} {V₁ V₂ : ℝ} (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ)
    (hθ0 : (0 : ℝ) ≤ θ) (hV₁ : 1 / 16 ≤ V₁) (hV₂ : 1 / 16 ≤ V₂) :
    (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
        * blockTAdd₂ θ m ^ (1 / 4 : ℝ)
      ≤ blockEps θ m * blockQ₂ θ m := by
  have hlogpos : (0 : ℝ) < Real.log (blockScale θ m) := by
    rw [log_blockScale]
    exact Real.exp_pos _
  have hs : (0 : ℝ) < Real.sqrt (blockScale θ m) := Real.sqrt_pos.2 (blockScale_pos θ m)
  have hl4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [blockEps, blockQ₂, blockWindow]
  refine blockNum₂_le hmθ hθ0 hV₁ hV₂ (blockTAdd₂_pos hlogpos).le ?_
  rw [blockTAdd₂]
  exact mul_le_mul_of_nonneg_right blockThirdConstAdd₂_le_blockThirdConst₂ (by positivity)

/-! ### The drift -/

/-- **The Rademacher block drift.**  `|blockMeanAdd| ≤ 3 e^{2η}(1 + 60/log x_{m+1})`.  The main
term has two pieces where the Steinhaus one has the single `Re(w_p · conj p^{-s})`:
`2(Re p^{-s})(Re w_p)`, at most `2p^{-1-2σ}`, and `Re(w_p²)/2`, at most `p^{-1-2σ}/2`.  So the
drift is at most `5/2` times the block sum (`RMF.abs_sum_rpow_primeBlockSub_sub_one_le`), and the
third-order error of `RMF.abs_blockMeanAdd_sub_sum_le` adds at most `0.037`. -/
theorem abs_blockMeanAdd_le (hX : IsRademacherPrimeValues X μ) {s : ℂ} {θ σ η : ℝ} {m n y : ℕ}
    {w : Nat.Primes → ℂ} (hmθ : (3 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hy : blockCutoff θ n ≤ y)
    (hres : s.re = 1 / 2 + σ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :
    |blockMeanAdd X μ y s w (primeBlockSub θ m)|
      ≤ 3 * (Real.exp (2 * η) * (1 + 60 / Real.log (blockScale θ (m + 1)))) := by
  have hσ1 : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := le_trans hσ hη1
  have hsre : 0 < s.re := re_pos_of_block hmθ hres hσ1
  have hB := primeBlockSub_subset_primesBelowSub_of_le hmn hy
  have hκ0 : (0 : ℝ) < blockWeightSize θ m := blockWeightSize_pos θ m
  have hκ : blockWeightSize θ m ≤ 1 / 1000 := blockWeightSize_le hmθ
  have han : ∀ p ∈ primeBlockSub θ m,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := fun p _ =>
    norm_sq_prime_cpow_neg p hres
  have haw : ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ = ‖w p‖ := fun p hp => by
    have h : ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ‖w p‖ ^ 2 := by rw [han p hp, hwn p hp]
    have h1 := Real.sqrt_sq (norm_nonneg (((p : ℕ) : ℂ) ^ (-s)))
    have h2 := Real.sqrt_sq (norm_nonneg (w p))
    rw [← h1, ← h2, h]
  have hwκ : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ blockWeightSize θ m := fun p hp =>
    norm_le_of_mem_primeBlockSub hσ1 hp (hwn p hp)
  have hw5 : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun p hp =>
    le_trans (hwκ p hp) (by linarith)
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
  -- the main term, termwise
  have hmain : |∑ p ∈ primeBlockSub θ m,
      (2 * (((p : ℕ) : ℂ) ^ (-s)).re * (w p).re - ((w p) ^ 2).re / 2)| ≤ 5 / 2 * S := by
    rw [hSdef, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hare : |(((p : ℕ) : ℂ) ^ (-s)).re| ≤ ‖w p‖ := by
      rw [← haw p hp]
      exact Complex.abs_re_le_norm _
    have hwre : |(w p).re| ≤ ‖w p‖ := Complex.abs_re_le_norm _
    have hsq : |((w p) ^ 2).re| ≤ ‖w p‖ ^ 2 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_pow]
    have h1 : |2 * (((p : ℕ) : ℂ) ^ (-s)).re * (w p).re| ≤ 2 * ‖w p‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg (((p : ℕ) : ℂ) ^ (-s)).re, abs_nonneg (w p).re]
    have h2 : |((w p) ^ 2).re / 2| ≤ ‖w p‖ ^ 2 / 2 := by
      rw [abs_div, abs_two]
      linarith
    rw [← hwn p hp]
    exact (abs_sub _ _).trans (by linarith)
  -- the third-order error, termwise
  have herr : (∑ p ∈ primeBlockSub θ m,
      (36 * ‖w p‖ ^ 3 + 2 * ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 3 * ‖w p‖)) ≤ 37 / 1000 * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hk := hwκ p hp
    have hk1 : ‖w p‖ ≤ 1 / 1000 := le_trans hk hκ
    rw [haw p hp, ← hwn p hp]
    nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, mul_nonneg h0 h0]
  have hgap := abs_blockMeanAdd_sub_sum_le hX y hsre hB hw5
  rw [abs_le] at hgap hmain ⊢
  have hpos : (0 : ℝ) < Real.exp (2 * η) * (1 + 60 / L) := by
    have : (0 : ℝ) < 60 / L := by positivity
    have := Real.exp_pos (2 * η)
    nlinarith
  constructor <;> nlinarith [hgap.1, hgap.2, hmain.1, hmain.2, hSle, hS0, herr]

/-! ### The window mass -/

/-- **`hqlow` for the Rademacher block.**  The Gaussian gives the window at least `RMF.blockQ θ m`
of its mass once the drift sits inside the envelope: the generic
`RMF.le_toReal_measure_Ioc_gaussianReal_of_bounds` at `A = 8`, `B = 9`, `Cₑ = 2`, under the
variance bracket `1/8 ≤ 2·var ≤ 9`.  The bracket also gives `variance ≠ 0`, which the Steinhaus
counterpart gets from `RMF.blockMatchedVar_pos`. -/
theorem blockQAdd_le_measure (hX : IsRademacherPrimeValues X μ) {θ σ η : ℝ} {m n y : ℕ}
    {s : ℂ} {w : Nat.Primes → ℂ} {M : ℝ}
    (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (hwn : ∀ p ∈ primeBlockSub θ m, ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (hV₁ : 1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ y s w
      (primeBlockSub θ m) : ℝ≥0) : ℝ))
    (hV₂ : 2 * ((blockMatchedVarAdd X μ y s w
      (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (henv : M + 3 * (Real.exp (2 * η) * (1 + 60 / Real.log (blockScale θ (m + 1))))
        + blockWindow m
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))) + 2) :
    ∀ c, |c| ≤ M → blockQ θ m ≤ (gaussianReal
        (blockMeanAdd X μ y s w (primeBlockSub θ m))
        (blockMatchedVarAdd X μ y s w (primeBlockSub θ m))
        (Set.Ioc c (c + blockWindow m))).toReal := by
  -- the variance is nonzero, straight from the bracket
  have hv : blockMatchedVarAdd X μ y s w (primeBlockSub θ m) ≠ 0 := by
    intro hzero
    rw [hzero] at hV₁
    norm_num at hV₁
  -- the drift sits inside the envelope
  have hdrift := abs_blockMeanAdd_le hX (by linarith : (3 : ℝ) ≤ (m : ℝ) + θ) hmn hy hres
    hη0 hη1 hσ hwn
  have henv' : M + |blockMeanAdd X μ y s w (primeBlockSub θ m)|
      + blockWindow m ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))) + 2 := by
    linarith
  have hx1 : (1 : ℝ) ≤ blockScale θ (m + 1) := by
    rw [blockScale]
    exact Real.one_le_exp (Real.exp_pos _).le
  intro c hc
  rw [blockQ]
  exact le_toReal_measure_Ioc_gaussianReal_of_bounds hv (blockWindow_pos m).le
    (by norm_num : (0 : ℝ) < 8) (by norm_num : (0 : ℝ) < 9) hV₁ hV₂ hx1 hc henv'
    (hthr_of_fourteen_le hmθ)

/-! ### The seam

The multi-block window comparison for the Rademacher model, with the tilt cutoff free.  This is
`RMF.exists_isWindowComparison_primeBlockSub_of_cutoff` with the Rademacher inputs; the Gaussian
family, the reindexing and the Lindeberg step are all the generic machinery. -/

/-- **The Rademacher analogue of Harper's Lemma 3, per block, with the tilt cutoff free.**  The
Gaussian family is built once, matched to the block's summands, and the window comparison is
returned for the block increment `∑_{p ∈ B} localLogAdd (w p) (f p)` — at `w p = p^{-1/2-σ-it}`
the increment of `log‖F(s)‖` over the block — for every shift `k ≤ n`.  Above the horizon the
family is a reservoir of standard normals, which makes the variance bracket satisfiable. -/
theorem exists_isWindowComparison_primeBlockSubAdd_of_cutoff (hX : IsRademacherPrimeValues X μ)
    {s : ℂ} {θ : ℝ} {n y : ℕ} {w : Nat.Primes → ℂ} (hs : 0 < s.re)
    (hy : blockCutoff θ n ≤ y)
    (hw : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5)
    (ha : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    {W M T q ε : ℕ → ℝ} {E : ℝ}
    (hT : ∀ m, m < n → 0 < T m) (hq : ∀ m, m < n → 0 < q m)
    (hv : ∀ m, m < n → blockMatchedVarAdd X μ (y) s w (primeBlockSub θ m) ≠ 0)
    (hTb : ∀ m, m < n →
      blockThirdConstAdd * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ T m)
    (hqlow : ∀ m, m < n → ∀ c, |c| ≤ M m → q m ≤ (gaussianReal
      (blockMeanAdd X μ (y) s w (primeBlockSub θ m))
      (blockMatchedVarAdd X μ (y) s w (primeBlockSub θ m))
      (Set.Ioc c (c + W m))).toReal)
    (hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        (blockMatchedVarAdd X μ (y) s w (primeBlockSub θ m) : ℝ)))
      * T m ^ (1 / 4 : ℝ) ≤ ε m * q m)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m) = gaussianReal (blockGaussMeanAddAt X μ θ y n s w m)
        (blockGaussVarAddAt X μ θ y n s w m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLogAdd (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => W (m + k)) (fun m => M (m + k)) (n - k) (2 * E)) := by
  classical
  have hprob := isProbabilityMeasure_tiltedMeasure_rademacher hX (y) hs
  have hξm : ∀ p : Nat.Primes, Measurable (fun ω => localLogAdd (w p) (X (p : ℕ) ω)) := fun p =>
    (measurable_localLogAdd (w p)).comp (hX.measurable (p : ℕ) p.2)
  have hξi := iIndepFun_localLogAdd_tiltedMeasure_rademacher hX (y) hs w
  -- the Gaussian family: the primes, plus a reservoir of standard normals above the horizon
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hGlaw, hGm₁, hGm₂⟩ :=
    exists_gaussian_matching_moments
      (Sum.elim (primeMeanAdd X μ (y) s w) (fun _ : ℕ => (0 : ℝ)))
      (Sum.elim (primeMoment₂Add X μ (y) s w) (fun _ : ℕ => (1 : ℝ)))
      (by
        rintro (q | j)
        · exact sq_primeMeanAdd_le X μ (y) s w q
        · norm_num)
  have hPm : ∀ q : Nat.Primes, Measurable (G (Sum.inl q)) := fun q => hGm _
  have hPi : iIndepFun (fun q : Nat.Primes => G (Sum.inl q)) Q := hGi.precomp Sum.inl_injective
  have hPlaw : ∀ q : Nat.Primes, Q.map (G (Sum.inl q))
      = gaussianReal (primeMeanAdd X μ (y) s w q)
        (matchingVar (primeMeanAdd X μ (y) s w q)
          (primeMoment₂Add X μ (y) s w q)) := fun q => hGlaw (Sum.inl q)
  have hPm₁ : ∀ q : Nat.Primes, ∫ ω, G (Sum.inl q) ω ∂Q
      = primeMeanAdd X μ (y) s w q := fun q => hGm₁ (Sum.inl q)
  have hPm₂ : ∀ q : Nat.Primes, ∫ ω, G (Sum.inl q) ω * G (Sum.inl q) ω ∂Q
      = primeMoment₂Add X μ (y) s w q := fun q => hGm₂ (Sum.inl q)
  have hvar : ∀ m, m ≤ n →
      (∑ p ∈ primeBlockSub θ m, matchingVar (primeMeanAdd X μ (y) s w p)
          (primeMoment₂Add X μ (y) s w p))
        = blockMatchedVarAdd X μ (y) s w (primeBlockSub θ m) := fun m hm =>
    (blockMatchedVarAdd_eq_sum hX _ hs (primeBlockSub_subset_primesBelowSub_of_le hm hy)
      (hw m hm)).symm
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
      = gaussianReal (blockGaussMeanAddAt X μ θ y n s w m)
        (blockGaussVarAddAt X μ θ y n s w m) := by
    intro m
    rw [map_sum_gaussianReal hGm hGi hGlaw (blockIndex θ n m), blockGaussMeanAddAt,
      blockGaussVarAddAt]
    by_cases hm : m ≤ n
    · rw [if_pos hm, if_pos hm, blockIndex, if_pos hm, Finset.sum_map, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Sum.elim_inl]
      rw [hvar m hm]
      rfl
    · rw [if_neg hm, if_neg hm, blockIndex, if_neg hm, Finset.sum_singleton,
        Finset.sum_singleton]
      norm_num [matchingVar]
  refine ⟨Ω', mΩ', Q, fun m ω => ∑ i ∈ blockIndex θ n m, G i ω, hQ, hNm, hNi, hNlaw, ?_⟩
  have hblock : ∀ m, m < n → IsWindowComparison₁
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) Q
      (fun ω => ∑ p ∈ primeBlockSub θ m, localLogAdd (w p) (X (p : ℕ) ω))
      (fun ω => ∑ i ∈ blockIndex θ n m, G i ω) (W m) (M m) (ε m) := by
    intro m hm
    have hmn : m ≤ n := le_of_lt hm
    rw [hNblock m hmn]
    have hB := primeBlockSub_subset_primesBelowSub_of_le hmn hy
    have hGlaw' : ∀ p ∈ primeBlockSub θ m, Q.map (G (Sum.inl p)) = gaussianReal
        (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ))
        (matchingVar
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ))
          (∫ ω, localLogAdd (w p) (X (p : ℕ) ω) * localLogAdd (w p) (X (p : ℕ) ω)
            ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω)
              (y) s μ))) := by
      intro p hp
      rw [hPlaw p, primeMoment₂Add_eq_of_le hX _ hs (hB hp) (hw m hmn p hp)]
      rfl
    have hTsum := sum_third_moment_blockAdd_le hX (y) hs hB (hw m hmn) (ha m hmn)
      hPm hGlaw'
    refine isWindowComparison₁_of_gaussian_family_of_third_moment hξm hPm hξi hPi hPlaw
      (fun p hp => integrable_localLogAdd_tiltedMeasure hX _ hs (hB hp) (hw m hmn p hp))
      (fun p hp =>
        integrable_localLogAdd_mul_self_tiltedMeasure hX _ hs (hB hp) (hw m hmn p hp))
      (fun p _ => integrable_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (fun p _ => integrable_mul_self_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (fun p _ => (hPm₁ p).symm)
      (fun p hp => by
        rw [hPm₂ p, primeMoment₂Add_eq_of_le hX _ hs (hB hp) (hw m hmn p hp)])
      (fun p hp =>
        integrable_abs_cube_localLogAdd_tiltedMeasure hX _ hs (hB hp) (hw m hmn p hp))
      (fun p _ => integrable_abs_cube_of_hasLaw_gaussianReal (hPm p) (hPlaw p))
      (hT m hm) (hq m hm) (by rw [hvar m hmn]; exact hv m hm)
      (le_trans hTsum (hTb m hm))
      (by intro c hc; rw [hvar m hmn]; exact hqlow m hm c hc)
      (by rw [hvar m hmn]; exact hnum m hm)
  intro k hkn
  exact isWindowComparison_shift_of_indep
    (iIndepFun_blockSumAdd_tiltedMeasure hX (y) hs θ w) hNi hkn hε0 hsum hE hblock

/-- **The multi-block comparison at the diagonal**, `y = RMF.blockCutoff θ n` — the form the
consumers use. -/
theorem exists_isWindowComparison_primeBlockSubAdd (hX : IsRademacherPrimeValues X μ)
    {s : ℂ} {θ : ℝ} {n : ℕ} {w : Nat.Primes → ℂ} (hs : 0 < s.re)
    (hw : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5)
    (ha : ∀ m, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 5)
    {W M T q ε : ℕ → ℝ} {E : ℝ}
    (hT : ∀ m, m < n → 0 < T m) (hq : ∀ m, m < n → 0 < q m)
    (hv : ∀ m, m < n →
      blockMatchedVarAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m) ≠ 0)
    (hTb : ∀ m, m < n →
      blockThirdConstAdd * ∑ p ∈ primeBlockSub θ m, ‖w p‖ ^ 3 ≤ T m)
    (hqlow : ∀ m, m < n → ∀ c, |c| ≤ M m → q m ≤ (gaussianReal
      (blockMeanAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m))
      (blockMatchedVarAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m))
      (Set.Ioc c (c + W m))).toReal)
    (hnum : ∀ m, m < n → (450 + 4 / Real.sqrt (2 * Real.pi *
        (blockMatchedVarAdd X μ (blockCutoff θ n) s w (primeBlockSub θ m) : ℝ)))
      * T m ^ (1 / 4 : ℝ) ≤ ε m * q m)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m) = gaussianReal
        (blockGaussMeanAddAt X μ θ (blockCutoff θ n) n s w m)
        (blockGaussVarAddAt X μ θ (blockCutoff θ n) n s w m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (blockCutoff θ n) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLogAdd (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => W (m + k)) (fun m => M (m + k)) (n - k) (2 * E)) :=
  exists_isWindowComparison_primeBlockSubAdd_of_cutoff hX hs le_rfl hw ha hT hq hv hTb hqlow
    hnum hε0 hsum hE

/-! ### Lemma 3 for the Rademacher block

Everything the seam asks for is above, so this is assembly.  The variance bracket arrives as a
hypothesis, supplied under the height condition by the concrete bracket of the previous
sections. -/

/-- **Lemma 3 for the Rademacher RMF**, at Harper's window `1/(m+1)²` with relative error `1/2`.
The observed field is `∑_{p ∈ B_m} log‖1 + f(p)p^{-u}‖`, compared against the block Gaussians of
`RMF.blockGaussMeanAddAt` and `RMF.blockGaussVarAddAt`, for every shift `k ≤ n`.  The envelope
constant is `21` where the Steinhaus statement has `7`: the Rademacher drift is at most
`3 e^{2η}(1 + 60/log x_{m+1})`, its main term having two pieces rather than one. -/
theorem exists_isWindowComparison_rademacher_of_cutoff
    (hX : IsRademacherPrimeValues X μ)
    {θ σ : ℝ} {n y : ℕ} {s : ℂ} {w : Nat.Primes → ℂ} {M : ℕ → ℝ}
    (hθ : (125 : ℝ) ≤ θ) (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1)
    (hwn : ∀ m : ℕ, ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ (y) s w
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ (y) s w
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (henvc : ∀ m, m < n →
      M m + blockWindow m + 21 ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (N : ℕ → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ m, Measurable (N m)) ∧ iIndepFun N Q ∧
      (∀ m, Q.map (N m) = gaussianReal
        (blockGaussMeanAddAt X μ θ (y) n s w m)
        (blockGaussVarAddAt X μ θ (y) n s w m)) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLogAdd (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
        (1 / 2)) := by
  have hσ : ∀ m, m ≤ n → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := hsigma_of_top hσtop
  have hmθ : ∀ m : ℕ, (14 : ℝ) ≤ (m : ℝ) + θ := fun m => by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hm3 : ∀ m : ℕ, (3 : ℝ) ≤ (m : ℝ) + θ := fun m => by linarith [hmθ m]
  have hw5 : ∀ m : ℕ, m ≤ n → ∀ p ∈ primeBlockSub θ m, ‖w p‖ ≤ 1 / 5 := fun m hm p hp =>
    le_trans (le_trans (norm_le_of_mem_primeBlockSub (hσ m hm) hp (hwn m p hp))
      (blockWeightSize_le (hm3 m))) (by norm_num)
  have hs : 0 < s.re := re_pos_of_block (hm3 0) hres (hσ 0 (Nat.zero_le n))
  -- `3 e²(1 + 60/L) ≤ 23`, so the envelope constant `21` clears the drift
  have he2 : Real.exp 2 ≤ 7.4 := by
    simpa using exp_natCast_le_of_pow_le (c := 2.7182818286) (k := 2)
      (by linarith [Real.exp_one_lt_d9]) (by norm_num)
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h10 : (6000 : ℝ) ≤ Real.exp 10 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 10) (by norm_num) he1.le (by norm_num)
  have henv : ∀ m, m < n →
      M m + 3 * (Real.exp (2 * 1) * (1 + 60 / Real.log (blockScale θ (m + 1))))
          + blockWindow m
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1))) + 2 := fun m hm => by
    have hL : (6000 : ℝ) ≤ Real.log (blockScale θ (m + 1)) := by
      rw [log_blockScale]
      refine h10.trans (Real.exp_le_exp.2 ?_)
      push_cast
      linarith [hmθ m]
    have hL0 : (0 : ℝ) < Real.log (blockScale θ (m + 1)) := by linarith
    have hfrac : 60 / Real.log (blockScale θ (m + 1)) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]
      linarith
    have hfrac0 : (0 : ℝ) ≤ 60 / Real.log (blockScale θ (m + 1)) := by positivity
    have hc := henvc m hm
    have hexp : Real.exp (2 * 1) = Real.exp 2 := by norm_num
    rw [hexp]
    nlinarith [Real.exp_pos (2 : ℝ)]
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_primeBlockSubAdd_of_cutoff (X := X) (μ := μ)
      (W := blockWindow) (M := M) (T := blockTAdd θ) (q := blockQ θ)
      (ε := blockEps θ) (E := 1 / 4) hX hs hy
      (fun m hm p hp => hw5 m hm p hp)
      (fun m _ p hp => norm_prime_cpow_le_fifth (hm3 m) hres (hσ m (by omega)) hp)
      (fun m _ => blockTAdd_pos (by rw [log_blockScale]; exact Real.exp_pos _))
      (fun m _ => blockQ_pos θ m)
      (fun m hm => by
        have h := (hV m (le_of_lt hm)).1
        intro hzero
        rw [hzero] at h
        norm_num at h)
      (fun m hm => blockThirdConstAdd_mul_sum_le (hm3 m) (hσ m (le_of_lt hm)) (hwn m))
      (fun m hm => blockQAdd_le_measure hX (hmθ m) (le_of_lt hm) hy hres (by norm_num) le_rfl
        (hσ m (le_of_lt hm)) (hwn m) (hV m (le_of_lt hm)).1 (hV m (le_of_lt hm)).2
        (henv m hm))
      (fun m hm => blockNumAdd_le (hmθ m) (by linarith) (by linarith [(hV m (le_of_lt hm)).1]))
      (fun m _ => blockEps_nonneg θ m) (sum_blockEps_le (by linarith) n) (by norm_num)
  refine ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, fun k hk => ?_⟩
  have h := hcmp k hk
  rwa [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h

/-! ### The Gaussian walk -/

/-- **The variance bounds, at every index.**  Below the horizon this is the bracket; above it the
variance is the reservoir's `1`, which sits inside `[1/16, 9/2]` for free.

The `∀ i` is the point: `IsGaussianWalk`'s `vmin`/`vmax` quantify over every index, and without
the reservoir no positive `vmin` could bound the tail. -/
lemma blockGaussVarAddAt_bounds {θ : ℝ} {n y : ℕ} {s : ℂ} {w : Nat.Primes → ℂ}
    (hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ y s w (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9) :
    ∀ i, (1 : ℝ) / 16 ≤ ((blockGaussVarAddAt X μ θ y n s w i : ℝ≥0) : ℝ)
      ∧ ((blockGaussVarAddAt X μ θ y n s w i : ℝ≥0) : ℝ) ≤ 9 / 2 := by
  intro i
  by_cases hi : i ≤ n
  · rw [blockGaussVarAddAt_of_le hi]
    obtain ⟨h1, h2⟩ := hV i hi
    constructor <;> linarith
  · rw [blockGaussVarAddAt, if_neg hi]
    norm_num

/-- **The Gaussian walk for the Rademacher RMF, with the tilt cutoff free.**
`RMF.exists_isWindowComparison_rademacher_of_cutoff` centred, with the variance bracket carried to
every index; `RMF.exists_isGaussianWalk_rademacher_of_offset_of_cutoff` is an instance of it.  A
consumer running the walk only to `n - d` still wants the tilted measure at the full cutoff, which
needs the two indices apart. -/
theorem exists_isGaussianWalk_rademacher_of_cutoff
    (hX : IsRademacherPrimeValues X μ)
    {θ σ : ℝ} {n y : ℕ} {s : ℂ} {w : Nat.Primes → ℂ} {M : ℕ → ℝ}
    (hθ : (125 : ℝ) ≤ θ) (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1)
    (hwn : ∀ m : ℕ, ∀ p ∈ primeBlockSub θ m,
      ‖w p‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
    (hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ (y) s w
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ (y) s w
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (henvc : ∀ m, m < n →
      M m + blockWindow m + 21 ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ) (v : ℕ → ℝ≥0),
      IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
      (∀ m ω, N m ω
        = G m ω + blockGaussMeanAddAt X μ θ (y) n s w m) ∧
      (∀ i, (1 : ℝ) / 16 ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 9 / 2) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k), localLogAdd (w p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
        (1 / 2)) := by
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmp⟩ :=
    exists_isWindowComparison_rademacher_of_cutoff hX hθ hy hres hσtop hwn hV henvc
  have hvb := blockGaussVarAddAt_bounds (θ := θ) (n := n) (y := y) (s := s) (w := w) hV
  exact ⟨Ω', mΩ', Q, fun m ω => N m ω - blockGaussMeanAddAt X μ θ y n s w m, N,
    blockGaussVarAddAt X μ θ y n s w, hQ,
    isGaussianWalk_sub_const hNm hNi hNlaw, hNm, fun m ω => by ring,
    fun i => (hvb i).1, fun i => (hvb i).2, hcmp⟩

/-! ### The offset forms

Harper's Proposition 6 (arXiv:1703.06654) carries a sequence `(t_j)` with
`|t_j - t| ≤ 1/(j^{2/3}e^{D+j})` and watches the field at `1/2 + σ + i t_m` on block `m` — a
different height per block.  `RMF.blockOffsetWeight` packages that as a single weight, and
`RMF.norm_sq_blockOffsetWeight` says its modulus is `p^{-1/2-σ}` on every block.

Because the statements above take `hwn` — the modulus — rather than a single exponent, the walk
at offsets is an *instantiation* and not a second theorem.  What genuinely sees the height is the
variance bracket, and that is per block: on block `m` the weight **is** `p^{-(s + i t_m)}`. -/

/-- The variance bracket at the offset weight.  On block `m` the height is `Im s + t m`, which is
Harper's `t_m`, and the condition is his `D ≥ log(1/|t|)`-style requirement read at that block. -/
theorem exists_blockMatchedVarAdd_concrete_of_offset_top :
    ∃ Tsh > 0,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
        IsRademacherPrimeValues X μ →
      ∀ (θ σ η : ℝ) (t : ℕ → ℝ) (m y : ℕ) (s : ℂ),
      0 < s.re → s.re = 1 / 2 + σ →
      (9 : ℝ) ≤ (m : ℝ) + θ → 0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * (s.im + t m) → (2 * (s.im + t m)) ^ 2 ≤ Real.exp ((m : ℝ) + θ) →
      Tsh ≤ 2 * (s.im + t m) * Real.exp ((m : ℝ) + θ) →
      primeBlockSub θ m ⊆ primesBelowSub y →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ y s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ y s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9 := by
  obtain ⟨Tsh, hTsh0, H⟩ := exists_blockMatchedVarAdd_concrete_top
  refine ⟨Tsh, hTsh0, ?_⟩
  intro Ω _ X μ hX θ σ η t m y s hs hres hmθ hθ hη hη' hσ hτ hτ2 hTsh hB
  have hre : (s + (t m : ℂ) * Complex.I).re = 1 / 2 + σ := by
    simp [hres]
  have him : (s + (t m : ℂ) * Complex.I).im = s.im + t m := by
    simp
  refine H _ X μ hX θ σ η m y s (s + (t m : ℂ) * Complex.I) (blockOffsetWeight θ t s)
    hs hres hre hmθ hθ
    hη hη' hσ (by rw [him]; exact hτ) (by rw [him]; exact hτ2) (by rw [him]; exact hTsh)
    (fun p hp => blockOffsetWeight_eq_of_mem hp) hB

/-- **The Gaussian walk at Harper's offsets, with the tilt cutoff free.**
`RMF.exists_isGaussianWalk_rademacher_of_cutoff` at `w = RMF.blockOffsetWeight θ t s`.  **This is
the form the Proposition 6 layer consumes**, since both halves obtain the offset walk. -/
theorem exists_isGaussianWalk_rademacher_of_offset_of_cutoff
    (hX : IsRademacherPrimeValues X μ)
    {θ σ : ℝ} {t : ℕ → ℝ} {n y : ℕ} {s : ℂ} {M : ℕ → ℝ}
    (hθ : (125 : ℝ) ≤ θ) (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1)
    (hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ (y) s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ (y) s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) : ℝ≥0) : ℝ) ≤ 9)
    (henvc : ∀ m, m < n →
      M m + blockWindow m + 21 ≤ 1 / 40 * Real.sqrt (Real.log (blockScale θ (m + 1)))) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (G N : ℕ → Ω' → ℝ) (v : ℕ → ℝ≥0),
      IsProbabilityMeasure Q ∧ IsGaussianWalk G v Q ∧ (∀ m, Measurable (N m)) ∧
      (∀ m ω, N m ω = G m ω
        + blockGaussMeanAddAt X μ θ (y) n s (blockOffsetWeight θ t s) m) ∧
      (∀ i, (1 : ℝ) / 16 ≤ (v i : ℝ)) ∧ (∀ i, (v i : ℝ) ≤ 9 / 2) ∧
      (∀ k, k ≤ n → IsWindowComparison
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) Q
        (fun m ω => ∑ p ∈ primeBlockSub θ (m + k),
          localLogAdd (blockOffsetWeight θ t s p) (X (p : ℕ) ω))
        (fun m => N (m + k)) (fun m => blockWindow (m + k)) (fun m => M (m + k)) (n - k)
        (1 / 2)) :=
  exists_isGaussianWalk_rademacher_of_cutoff hX hθ hy hres hσtop
    (fun _ p _ => norm_sq_blockOffsetWeight hres p) hV henvc

/-! ### Harper's trigonometric split, over a block

Harper writes `c(t, t_j - t, p) = 2cos(t log p)cos(t_j log p) - (1/2)cos(2 t_j log p)` and
splits the product with `2 cos A cos B = cos(A+B) + cos(A-B)`, leaving three sums to estimate:
`cos((t - t_j) log p)`, which is `1 + O(1/j^{4/3})` because the offsets are tiny, and two
oscillatory ones killed by the prime number theorem.

`RMF.rademacherDrift_prime_eq` is that split pointwise.  Summed over a block at the offset weight
it says the Rademacher main term is

* the **Steinhaus main term**, verbatim, so everything the Steinhaus drift proof does with it
  transfers unchanged; plus
* two oscillatory sums, at frequencies `2 Im s + t_m` and `2(Im s + t_m)`, both of which
  `RMF.exists_abs_sum_cos_primeBlockSub_le'` bounds. -/

/-- **The Rademacher block main term = the Steinhaus one + two oscillatory sums.**  Harper's
trigonometric split, summed over `RMF.primeBlockSub`. -/
lemma sum_rademacherDrift_primeBlockSub_eq {θ σ : ℝ} (t : ℕ → ℝ) (m : ℕ) {s : ℂ}
    (hres : s.re = 1 / 2 + σ) :
    (∑ p ∈ primeBlockSub θ m,
        (2 * (((p : ℕ) : ℂ) ^ (-s)).re * (blockOffsetWeight θ t s p).re
          - (blockOffsetWeight θ t s p ^ 2).re / 2))
      = (∑ p ∈ primeBlockSub θ m,
            Real.cos (t m * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        + (∑ p ∈ primeBlockSub θ m,
            Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - (∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) / 2 := by
  rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  set u : ℂ := s + (t m : ℂ) * Complex.I with hu_def
  have hure : u.re = 1 / 2 + σ := by simp [hu_def, hres]
  have huim : u.im = s.im + t m := by simp [hu_def]
  have hw : blockOffsetWeight θ t s p = ((p : ℕ) : ℂ) ^ (-u) := blockOffsetWeight_eq_of_mem hp
  rw [hw, rademacherDrift_prime_eq p.2 hres hure, huim]
  -- `Im s - (Im s + t m) = -(t m)`, and cosine is even
  rw [show (s.im - (s.im + t m)) * Real.log ((p : ℕ) : ℝ)
        = -(t m * Real.log ((p : ℕ) : ℝ)) by ring,
    Real.cos_neg, show s.im + (s.im + t m) = 2 * s.im + t m by ring]
  ring

/-! ### The per-block drift

Harper computes `∑_{p ∈ B_j} c(t, t_j-t, p)/p^{1+2σ} = 1 + O(1/e^{n-j} + 1/j^{4/3})` — the block
mean drifts by `+1`, exactly as in the Steinhaus case.  This is that estimate, per block.

**The two oscillatory sums are left in the bound rather than taken as hypotheses.**
`RMF.exists_abs_sum_cos_primeBlockSub_le'` needs `0 < τ`, so a hypothesis in that shape could not
be discharged at zero height.  This is also what Harper does: he estimates the two sums separately
by the prime number theorem, and their bound is where the two models' block drifts differ. -/

/-- **The per-block drift for the Rademacher RMF.**  `|E~N_m - 1|` bounded by four `t`-free terms
plus the two oscillatory sums.  The first three summands are those of the Steinhaus per-block
drift, the fourth is the cubic error of the two-atom law, and the last two are what Harper's `c`
contributes beyond the Steinhaus main term (`RMF.sum_rademacherDrift_primeBlockSub_eq`). -/
theorem abs_blockMeanAdd_sub_one_le_of_offset (hX : IsRademacherPrimeValues X μ) {s : ℂ}
    {θ σ η : ℝ} {t : ℕ → ℝ} {m n y : ℕ}
    (hmθ : (14 : ℝ) ≤ (m : ℝ) + θ) (hmn : m ≤ n)
    (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ : |σ| * Real.log (blockScale θ (m + 1)) ≤ η)
    (ht : |t m| * Real.log (blockScale θ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3))) :
    |blockMeanAdd X μ (y) s (blockOffsetWeight θ t s) (primeBlockSub θ m) - 1|
      ≤ (Real.exp (2 * η) - 1)
        + Real.exp (2 * η) * (60 / Real.log (blockScale θ (m + 1)))
        + 4 * ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3))
        + 76 * blockWeightSize θ m * Real.exp (2 * η)
        + |∑ p ∈ primeBlockSub θ m,
            Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2 := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + θ := by linarith
  have hσ1 : |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 := le_trans hσ hη1
  have hsre : 0 < s.re := re_pos_of_block hm3 hres hσ1
  have hB := primeBlockSub_subset_primesBelowSub_of_le hmn hy
  have hκ0 : (0 : ℝ) < blockWeightSize θ m := blockWeightSize_pos θ m
  have hκ : blockWeightSize θ m ≤ 1 / 1000 := blockWeightSize_le hm3
  have hκw : ∀ q ∈ primeBlockSub θ m,
      ‖blockOffsetWeight θ t s q‖ ≤ blockWeightSize θ m :=
    fun q hq => norm_le_of_mem_primeBlockSub hσ1 hq (norm_sq_blockOffsetWeight hres q)
  have hw5 : ∀ q ∈ primeBlockSub θ m, ‖blockOffsetWeight θ t s q‖ ≤ 1 / 5 := fun q hq =>
    le_trans (hκw q hq) (by linarith)
  -- the two norms agree, so the cubic error is `≤ 38 κ p^{-1-2σ}` per prime
  have hnormeq : ∀ q : Nat.Primes,
      ‖blockOffsetWeight θ t s q‖ = ‖((q : ℕ) : ℂ) ^ (-s)‖ := by
    intro q
    have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
    rw [norm_eq_rpow_of_sq_eq hq0 (norm_sq_blockOffsetWeight hres q),
      norm_eq_rpow_of_sq_eq hq0 (norm_sq_prime_cpow_neg q hres)]
  set S : ℝ := ∑ q ∈ primeBlockSub θ m, ((q : ℕ) : ℝ) ^ (-1 - 2 * σ) with hSdef
  have herr : (∑ q ∈ primeBlockSub θ m,
        (36 * ‖blockOffsetWeight θ t s q‖ ^ 3
          + 2 * ‖((q : ℕ) : ℂ) ^ (-s)‖ ^ 3 * ‖blockOffsetWeight θ t s q‖))
      ≤ 38 * blockWeightSize θ m * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hsq : ‖blockOffsetWeight θ t s q‖ ^ 2 = ((q : ℕ) : ℝ) ^ (-1 - 2 * σ) :=
      norm_sq_blockOffsetWeight hres q
    have h0 : (0 : ℝ) ≤ ‖blockOffsetWeight θ t s q‖ := norm_nonneg _
    have hle := hκw q hq
    have hw2 : (0 : ℝ) ≤ ‖blockOffsetWeight θ t s q‖ ^ 2 := sq_nonneg _
    have hwle1 : ‖blockOffsetWeight θ t s q‖ ≤ 1 := le_trans hle (by linarith)
    -- `w³ = w·w² ≤ κ w²`, and `w⁴ ≤ κ w²·w ≤ κ w²`
    have h3 : ‖blockOffsetWeight θ t s q‖ ^ 3
        ≤ blockWeightSize θ m * ‖blockOffsetWeight θ t s q‖ ^ 2 := by
      rw [show ‖blockOffsetWeight θ t s q‖ ^ 3
          = ‖blockOffsetWeight θ t s q‖ * ‖blockOffsetWeight θ t s q‖ ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hle hw2
    have h4 : ‖blockOffsetWeight θ t s q‖ ^ 3 * ‖blockOffsetWeight θ t s q‖
        ≤ blockWeightSize θ m * ‖blockOffsetWeight θ t s q‖ ^ 2 := by
      have a1 : ‖blockOffsetWeight θ t s q‖ ^ 3 * ‖blockOffsetWeight θ t s q‖
          ≤ blockWeightSize θ m * ‖blockOffsetWeight θ t s q‖ ^ 2
            * ‖blockOffsetWeight θ t s q‖ := mul_le_mul_of_nonneg_right h3 h0
      have a2 : blockWeightSize θ m * ‖blockOffsetWeight θ t s q‖ ^ 2
            * ‖blockOffsetWeight θ t s q‖
          ≤ blockWeightSize θ m * ‖blockOffsetWeight θ t s q‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hwle1 (by positivity)
      linarith
    rw [← hnormeq q, ← hsq]
    linarith [h3, h4]
  -- the main term, split by Harper's trigonometric identity
  have h1 := abs_blockMeanAdd_sub_sum_le hX (y) hsre hB hw5
  rw [sum_rademacherDrift_primeBlockSub_eq t m hres] at h1
  -- the near-`1` piece: the block sum plus the `4/3` correction
  have hsplit : (∑ q ∈ primeBlockSub θ m,
      Real.cos (t m * Real.log ((q : ℕ) : ℝ)) * ((q : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = S + ∑ q ∈ primeBlockSub θ m,
          (Real.cos (t m * Real.log ((q : ℕ) : ℝ)) - 1) * ((q : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
    rw [hSdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsplit] at h1
  have hcos : |∑ q ∈ primeBlockSub θ m,
      (Real.cos (t m * Real.log ((q : ℕ) : ℝ)) - 1) * ((q : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 4 * ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3)) :=
    abs_sum_cos_sub_one_primeBlockSub_le hmθ hσ1 ht
  have h2 := abs_sum_rpow_primeBlockSub_sub_one_le θ σ η m hm3 hη0 hσ
  rw [← hSdef] at h2
  -- `S ≤ 2 e^{2η}`, since `60/L ≤ 1` on a block this high
  set L : ℝ := Real.log (blockScale θ (m + 1)) with hLdef
  have hLbig : (60 : ℝ) ≤ L := by
    rw [hLdef, log_blockScale]
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (60 : ℝ) ≤ (2.7 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 5
      _ = Real.exp ((5 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (((m + 1 : ℕ) : ℝ) + θ) := Real.exp_le_exp.2 (by push_cast; linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  have hd : (0 : ℝ) ≤ 60 / L := by positivity
  have hd1 : (60 : ℝ) / L ≤ 1 := by rw [div_le_one hL0]; linarith
  have hexp : (1 : ℝ) ≤ Real.exp (2 * η) := Real.one_le_exp (by linarith)
  have hS2 : S ≤ 2 * Real.exp (2 * η) := by nlinarith [(abs_le.1 h2).2, hexp, hd1, hd]
  have hcub : 38 * blockWeightSize θ m * S ≤ 76 * blockWeightSize θ m * Real.exp (2 * η) := by
    nlinarith [hS2, hκ0]
  set A : ℝ := ∑ p ∈ primeBlockSub θ m,
    Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) with hAdef
  set C : ℝ := ∑ p ∈ primeBlockSub θ m,
    Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) with hCdef
  rw [abs_le] at h1 h2 hcos
  rw [abs_le]
  constructor <;>
    linarith [h1.1, h1.2, h2.1, h2.2, hcos.1, hcos.2, herr, hcub,
      neg_abs_le A, le_abs_self A, neg_abs_le C, le_abs_self C]

/-! ### The summed drift

`|∑_{m<j} E~N_m - j| ≤ C`, with `C` independent of `n`, `j` and `σ` — what Proposition 6 consumes.
The first three pieces are those of the Steinhaus summed drift: the tilt collapses geometrically
from the top, Mertens from the bottom, and the offsets' contribution converges because
`∑ (m+1)^{-4/3}` does.

The Rademacher branch adds two.  The cubic error of the two-atom law sums because
`κ_m = e/√(blockScale θ m)` decays doubly exponentially.  The oscillatory pair is a hypothesis
`≤ K_d e^{-m}`, the shape `RMF.exists_abs_sum_cos_primeBlockSub_le'` produces under Harper's
`x_1 ≥ e^{C/|t|}` read as `Tsh ≤ τ e^θ`, with `K_d = (3/2)K/Tsh`.

That hypothesis has no instances at zero height, correctly: at `Im s = t_m = 0` Harper's `c` is
`2·1·1 - (1/2)·1 = 3/2`, so the drift there is `3/2` per block, not `1`. -/

/-- **The summed drift at Harper's offsets.**  The first three summands of the bound are those of
the Steinhaus summed drift.  The bound depends only on `θ` and `K_d`, not on `n`, `j` or `σ`. -/
theorem abs_sum_blockMeanAdd_sub_le_of_offset (hX : IsRademacherPrimeValues X μ) {s : ℂ}
    {θ σ Kd : ℝ} {t : ℕ → ℝ} {n j y : ℕ}
    (hθ14 : (14 : ℝ) ≤ θ) (hj : j ≤ n + 1)
    (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1)
    (ht : ∀ m, m < j →
      |t m| * Real.log (blockScale θ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3)))
    (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < j →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ))) :
    |(∑ m ∈ Finset.range j, blockMeanAdd X μ (y) s
        (blockOffsetWeight θ t s) (primeBlockSub θ m)) - (j : ℝ)|
      ≤ 4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ))
        + 4 * blockDriftConst
        + 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ / 2))
            * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
        + 2 * Kd := by
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have he2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have hblock : ∀ m ∈ Finset.range j,
      |blockMeanAdd X μ (y) s (blockOffsetWeight θ t s)
          (primeBlockSub θ m) - 1|
        ≤ 2 * Real.exp 2 * Real.exp ((m : ℝ) - n)
          + 60 * Real.exp 2 * (Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)))
          + 4 * ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3))
          + 76 * Real.exp 2 * blockWeightSize θ m
          + Kd * Real.exp (-(m : ℝ)) := by
    intro m hm
    have hmj : m < j := Finset.mem_range.1 hm
    have hmn : m ≤ n := by omega
    have hmθ : (14 : ℝ) ≤ (m : ℝ) + θ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hη0 : (0 : ℝ) ≤ Real.exp ((m : ℝ) - n) := (Real.exp_pos _).le
    have hη1 : Real.exp ((m : ℝ) - n) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    have hmain := abs_blockMeanAdd_sub_one_le_of_offset hX hmθ hmn hy hres hη0 hη1
      (sigma_le_exp_sub θ σ hσ) (ht m hmj)
    rw [sixty_div_log_blockScale] at hmain
    have hle2 : Real.exp (2 * Real.exp ((m : ℝ) - n)) ≤ Real.exp 2 :=
      Real.exp_le_exp.2 (by linarith)
    have hlin := exp_sub_one_le_mul_exp (2 * Real.exp ((m : ℝ) - n))
    have hκ0 : (0 : ℝ) ≤ blockWeightSize θ m := (blockWeightSize_pos θ m).le
    have hd0 : (0 : ℝ) ≤ Real.exp (-(1 + θ)) * Real.exp (-(m : ℝ)) := by positivity
    have hosc' := hosc m hmj
    nlinarith [hmain, hle2, hlin, hη0, hκ0, hd0, he2, hosc']
  have hsplit : (∑ m ∈ Finset.range j, blockMeanAdd X μ (y) s
        (blockOffsetWeight θ t s) (primeBlockSub θ m)) - (j : ℝ)
      = ∑ m ∈ Finset.range j, (blockMeanAdd X μ (y) s
        (blockOffsetWeight θ t s) (primeBlockSub θ m) - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
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
  have hC : ∑ m ∈ Finset.range j, 4 * ((m : ℝ) + 1) ^ (-((4 : ℝ) / 3))
      ≤ 4 * blockDriftConst := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_blockDrift_le j) (by norm_num)
  -- the two-atom law's cubic error, summable because `κ_m` decays doubly exponentially
  have hD : ∑ m ∈ Finset.range j, 76 * Real.exp 2 * blockWeightSize θ m
      ≤ 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ / 2))
          * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hshift := sum_blockWeightSize_shift_le θ 0 j
    simpa using hshift
  -- the oscillatory pair, geometric by hypothesis
  have hE : ∑ m ∈ Finset.range j, Kd * Real.exp (-(m : ℝ)) ≤ 2 * Kd := by
    rw [← Finset.mul_sum]
    calc Kd * ∑ m ∈ Finset.range j, Real.exp (-(m : ℝ))
        ≤ Kd * 2 := mul_le_mul_of_nonneg_left (sum_exp_neg_nat_le j) hKd
      _ = 2 * Kd := by ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  linarith [hA, hB, hC, hD, hE]

/-! ### The drift in the shape Proposition 6 consumes

`RMF.blockGaussMeanAddAt` is the comparison Gaussian's mean: the block mean below the horizon and
`0` above it.  Below the horizon it *is* the block mean, so the summed drift transfers verbatim;
the wrapper exists because Proposition 6 quantifies over `blockGaussMeanAddAt` and wants one
absolute constant, not a five-term bound. -/

/-- **The constant in the Rademacher drift estimate**:
`4e² + 120e²e^{-(1+θ)} + 4·blockDriftConst + 76e³e^{-θ/2}/(1 - e^{-1/2}) + 2K_d`.  The Steinhaus
counterpart is `RMF.driftConstOf`, whose summands are the first three; the fourth is the two-atom
law's cubic error and the last pays for the oscillatory pair.  It depends on `θ` and `K_d` only. -/
noncomputable def driftConstAdd (Kd θ : ℝ) : ℝ :=
  4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ))
    + 4 * blockDriftConst
    + 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
    + 2 * Kd

lemma one_sub_exp_neg_half_pos : (0 : ℝ) < 1 - Real.exp (-(1 / 2 : ℝ)) := by
  have : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  linarith

lemma driftConstAdd_nonneg {Kd θ : ℝ} (hKd : 0 ≤ Kd) : 0 ≤ driftConstAdd Kd θ := by
  have hinv : (0 : ℝ) ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ :=
    (inv_pos.2 one_sub_exp_neg_half_pos).le
  have h1 : (0 : ℝ) ≤ 4 * Real.exp 2 + 120 * Real.exp 2 * Real.exp (-(1 + θ)) := by positivity
  have h2 : (0 : ℝ) ≤ 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ / 2))
      * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) := by positivity
  rw [driftConstAdd]
  linarith [blockDriftConst_nonneg, hKd]

/-- Below the horizon the comparison Gaussian's mean **is** the block mean, so the summed drift
transfers verbatim.  The Steinhaus counterpart is `RMF.sum_blockGaussMean_eq`. -/
lemma sum_blockGaussMeanAddAt_eq (X : ℕ → Ω → ℂ) (μ : Measure Ω) (θ : ℝ) (y n : ℕ) (s : ℂ)
    (w : Nat.Primes → ℂ) {j : ℕ} (hj : j ≤ n + 1) :
    ∑ m ∈ Finset.range j, blockGaussMeanAddAt X μ θ y n s w m
      = ∑ m ∈ Finset.range j, blockMeanAdd X μ y s w (primeBlockSub θ m) :=
  Finset.sum_congr rfl fun m hm => by
    have : m < j := Finset.mem_range.1 hm
    exact blockGaussMeanAddAt_of_le (by omega)

/-- **The drift estimate in the shape Proposition 6 consumes.**  `hosc` is supplied by
`RMF.abs_sum_cos_pair_le_of_threshold`, with `K_d = (3/2)K/Tsh` under Harper's `x₁ ≥ e^{C/|t|}`.
It has no instances at zero height, correctly: there Harper's `c` is `3/2`, so the drift is `3/2`
per block and not `1`. -/
theorem abs_sum_blockGaussMeanAddAt_sub_le_of_offset (hX : IsRademacherPrimeValues X μ) {s : ℂ}
    {θ σ Kd : ℝ} {t : ℕ → ℝ} {n j y : ℕ}
    (hθ14 : (14 : ℝ) ≤ θ) (hj : j ≤ n + 1)
    (hy : blockCutoff θ n ≤ y) (hres : s.re = 1 / 2 + σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ 1)
    (ht : ∀ m, m < j →
      |t m| * Real.log (blockScale θ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3)))
    (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < j →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub θ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ))) :
    |(∑ m ∈ Finset.range j,
        blockGaussMeanAddAt X μ θ (y) n s (blockOffsetWeight θ t s) m) - (j : ℝ)|
      ≤ driftConstAdd Kd θ := by
  rw [sum_blockGaussMeanAddAt_eq X μ θ (y) n s _ hj, driftConstAdd]
  exact abs_sum_blockMeanAdd_sub_le_of_offset hX hθ14 hj hy hres hσ ht hKd hosc

/-! ### The block cosine bound, in the spelling the drift bound uses

`RMF.exists_abs_sum_cos_primeBlockSub_le'` is stated with `cos(τ log p)/p^{1+2σ}`; the drift bound
carries `cos(τ log p)·p^{-1-2σ}`.  The same number, and the restatement below is what discharges
`hosc`, so that its satisfiability is exhibited rather than asserted. -/

/-- `RMF.exists_abs_sum_cos_primeBlockSub_le'`, with the weight written as an `rpow` with a
negative exponent. -/
theorem exists_abs_sum_cos_primeBlockSub_rpow_le :
    ∃ K > 0, ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → 0 ≤ θ → τ ^ 2 ≤ Real.exp ((m : ℝ) + θ) →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ K / (τ * Real.exp ((m : ℝ) + θ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_sum_cos_primeBlockSub_le'
  refine ⟨K, hK0, fun τ σ θ m hτ hθ hτ2 hσ => ?_⟩
  have hrw : ∀ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [Finset.sum_congr rfl hrw]
  exact hK τ σ θ m hτ hθ hτ2 hσ

/-- **`hosc` is satisfiable, and this is what supplies it.**  At both of Harper's frequencies
`2 Im s + t_m` and `2(Im s + t_m)`, the bound `K/(τe^{m+θ}) = (K/(τe^θ))e^{-m}` of
`RMF.exists_abs_sum_cos_primeBlockSub_rpow_le` with a uniform threshold `Tsh ≤ τe^θ` — Harper's
`x₁ ≥ e^{C/|t|}` — makes the pair geometric with `K_d = (3/2)K/Tsh`.  Both conditions are per
block, on whichever frequency is in play. -/
theorem abs_sum_cos_pair_le_of_threshold {K Tsh τ₁ τ₂ σ θ : ℝ} {m : ℕ}
    (hK0 : 0 < K) (hTsh : 0 < Tsh)
    (hA : |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ₁ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ K / (τ₁ * Real.exp ((m : ℝ) + θ)))
    (hC : |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ₂ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ K / (τ₂ * Real.exp ((m : ℝ) + θ)))
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hT₁ : Tsh ≤ τ₁ * Real.exp θ) (hT₂ : Tsh ≤ τ₂ * Real.exp θ) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ₁ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      + |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ₂ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
      ≤ (3 / 2 * (K / Tsh)) * Real.exp (-(m : ℝ)) := by
  have hem : (0 : ℝ) < Real.exp ((m : ℝ)) := Real.exp_pos _
  have heθ : (0 : ℝ) < Real.exp θ := Real.exp_pos _
  -- `K/(τ e^{m+θ}) = (K/(τ e^θ)) e^{-m} ≤ (K/Tsh) e^{-m}`
  have hkey : ∀ τ : ℝ, 0 < τ → Tsh ≤ τ * Real.exp θ →
      K / (τ * Real.exp ((m : ℝ) + θ)) ≤ (K / Tsh) * Real.exp (-(m : ℝ)) := by
    intro τ hτ hT
    have hτe : (0 : ℝ) < τ * Real.exp θ := by positivity
    have hsplit : τ * Real.exp ((m : ℝ) + θ) = (τ * Real.exp θ) * Real.exp ((m : ℝ)) := by
      rw [Real.exp_add]; ring
    have hrhs : (K / Tsh) * Real.exp (-(m : ℝ)) = K / (Tsh * Real.exp ((m : ℝ))) := by
      rw [Real.exp_neg]
      field_simp
    rw [hsplit, hrhs]
    exact div_le_div_of_nonneg_left hK0.le (by positivity)
      (mul_le_mul_of_nonneg_right hT hem.le)
  have h1 := le_trans hA (hkey τ₁ hτ₁ hT₁)
  have h2 := le_trans hC (hkey τ₂ hτ₂ hT₂)
  have hexp : (0 : ℝ) < Real.exp (-(m : ℝ)) := Real.exp_pos _
  linarith

/-! ### Proposition 6, the lower half

Harper's Proposition 6 is the Rademacher analogue of Proposition 5: with `B` a large absolute
natural number and the barriers `-a - Bj` and `a + j + h(j)`, the tilted probability of staying
inside them for all `j ≤ n` is `≍ min\{1, a/√n\}`.  His own proof says the only non-trivial change
from Proposition 5 is verifying the extra condition `x₁ ≥ max\{e^{C/|t|}, e^{C log²|t|}\}` — which
is where `K_d` comes from.

`RMF.proposition5_lower` in `HarperChain.lean` is the model-agnostic core: it relates an abstract
probability measure to a Gaussian walk through `RMF.IsWindowComparison`, and knows nothing about
which random multiplicative function is underneath.  So the Rademacher half is that core fed with
the Rademacher walk and the Rademacher drift. -/

/-- `driftConstAdd` is antitone in `θ`, like `RMF.driftConst`.  Both `θ`-dependent summands decay
in `θ`, so a slope quoted at `θ = 125` dominates every admissible `θ` — which is what lets one
barrier slope serve the whole range even though `θ = \{log log x\} + D - 1` moves with `x`. -/
lemma driftConstAdd_antitone {Kd θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    driftConstAdd Kd θ₂ ≤ driftConstAdd Kd θ₁ := by
  have hinv : (0 : ℝ) ≤ (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ :=
    (inv_pos.2 one_sub_exp_neg_half_pos).le
  have h1 : Real.exp (-(1 + θ₂)) ≤ Real.exp (-(1 + θ₁)) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-(θ₂ / 2)) ≤ Real.exp (-(θ₁ / 2)) := Real.exp_le_exp.2 (by linarith)
  have he2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  rw [driftConstAdd, driftConstAdd]
  have hA : 120 * Real.exp 2 * Real.exp (-(1 + θ₂))
      ≤ 120 * Real.exp 2 * Real.exp (-(1 + θ₁)) := by nlinarith
  have hB : 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ₂ / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹)
      ≤ 76 * Real.exp 2 * (Real.exp 1 * Real.exp (-(θ₁ / 2))
        * (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 he1.le) hinv)
      (by positivity)
  linarith

/-- **Harper's `B`, for the Rademacher branch**:
`result2Slope (1/16) (9/2) + 2 + driftConstAdd Kd θ`.  The Steinhaus counterpart is
`RMF.blockSlope`; only the drift constant differs, and `K_d` is fixed by the block cosine bound's
constant and Harper's height threshold, so it does not move with `x`. -/
noncomputable def blockSlopeAdd (Kd θ : ℝ) : ℝ :=
  result2Slope (1 / 16) (9 / 2) + 2 + driftConstAdd Kd θ

lemma blockSlopeAdd_pos {Kd θ : ℝ} (hKd : 0 ≤ Kd) : 0 < blockSlopeAdd Kd θ := by
  have h := driftConstAdd_nonneg (Kd := Kd) (θ := θ) hKd
  have hs : 0 < result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ) := by
    linarith [le_result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ)]
  rw [blockSlopeAdd]
  linarith

/-- **Harper's `B` for the Rademacher branch is at least `20`**: `RMF.blockSlopeAdd` is
`result2Slope (1/16) (9/2) + 2 + driftConstAdd Kd θ`, `RMF.le_result2Slope` gives
`20 ≤ result2Slope`, and the drift constant is non-negative.  It discharges the barrier's
`20 ≤ c` on the Rademacher side, where the slope is an existential `B` passed unchanged through
every layer. -/
lemma twenty_le_blockSlopeAdd {Kd θ : ℝ} (hKd : 0 ≤ Kd) : (20 : ℝ) ≤ blockSlopeAdd Kd θ := by
  have h := driftConstAdd_nonneg (Kd := Kd) (θ := θ) hKd
  have hs := le_result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ)
  rw [blockSlopeAdd]
  linarith

/-- The block increment is measurable at any weight.  `RMF.measurable_blockLocalLogAdd` fixes the
weight at `p^{-s}`; Proposition 6 needs it at `RMF.blockOffsetWeight`. -/
lemma measurable_blockLocalLogAdd_weight (hX : IsRademacherPrimeValues X μ) (θ : ℝ)
    (w : Nat.Primes → ℂ) (m : ℕ) :
    Measurable (fun ω => ∑ p ∈ primeBlockSub θ m, localLogAdd (w p) (X (p : ℕ) ω)) :=
  Finset.measurable_sum _ fun p _ =>
    (measurable_localLogAdd (w p)).comp (hX.measurable (p : ℕ) p.2)

/-- **Proposition 6, lower bound, at Harper's offsets, with the tilt cutoff free.**  Every index is
the **range** except the tilted measure's `y`, the **cutoff**, so a consumer can run the barrier to
`n - d` while keeping the measure at the full cutoff.

`hV` (the variance bracket at the offset weight) and `hosc` (the oscillatory pair, discharged by
`RMF.abs_sum_cos_pair_le_of_threshold`) hold under Harper's height conditions; both are carried so
that the packaging chooses the threshold `Tsh` once. -/
theorem proposition5_lower_rademacher_of_offset_of_cutoff
    (hX : IsRademacherPrimeValues X μ)
    {ϑ σ a Kd : ℝ} {t : ℕ → ℝ} {n y : ℕ} {s : ℂ} {M M' hf : ℕ → ℝ}
    (hϑ : (125 : ℝ) ≤ ϑ) (hy : blockCutoff ϑ n ≤ y)
    (hres : s.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1)
    (ht : ∀ m, m < n →
      |t m| * Real.log (blockScale ϑ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3)))
    (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < n →
      |∑ p ∈ primeBlockSub ϑ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub ϑ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ)))
    (hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ) ≤ 9)
    (henvc : ∀ m, m < n →
      M' m + blockWindow m + 21
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))))
    (hM0 : ∀ j, 0 ≤ M j)
    (hMcap : ∀ j, 1 ≤ j → j ≤ n →
      blockSlopeAdd Kd 125 * j ≤ M j ∧
        blockSlopeAdd Kd 125 * j + j + hf j ≤ M j)
    (hMM : ∀ m, m < n → M m + M (m + 1) + blockWindow m ≤ M' m)
    (ha : max (max 1 (result2Threshold (1 / 16) (9 / 2) + 2 + driftConstAdd Kd ϑ))
      (4 + 2 * driftConstAdd Kd ϑ) ≤ a)
    (hn : 1 ≤ n) (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ))
    (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 16))
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    result1LowerConst (1 / 16) (9 / 2) / 2 / 4 * min 1 (a / Real.sqrt n)
      ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ)
          (barrierEvent
            (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
              localLogAdd (blockOffsetWeight ϑ t s p) (X (p : ℕ) ω)) n
            (fun j => -a - blockSlopeAdd Kd 125 * j)
            (fun j => a + j + hf j))).toReal := by
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hGw, hNm, hNG, hvlo, hvhi, hcmp⟩ :=
    exists_isGaussianWalk_rademacher_of_offset_of_cutoff hX hϑ hy hres hσtop hV henvc
  have hσ := hsigma_of_top hσtop
  have h14 : (14 : ℝ) ≤ ϑ := by linarith
  have hm3' : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + ϑ := by
    push_cast
    linarith
  have hs : 0 < s.re := re_pos_of_block hm3' hres (hσ 0 (Nat.zero_le n))
  have hP : IsProbabilityMeasure
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) :=
    isProbabilityMeasure_tiltedMeasure_rademacher hX (y) hs
  have hslope : result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConstAdd Kd ϑ
      ≤ blockSlopeAdd Kd 125 := by
    rw [blockSlopeAdd]
    linarith [driftConstAdd_antitone (Kd := Kd) hϑ]
  have hMcap' : ∀ j, 1 ≤ j → j ≤ n →
      (result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConstAdd Kd ϑ) * j ≤ M j ∧
        (result2Slope (1 / 16 : ℝ) (9 / 2 : ℝ) + 2 + driftConstAdd Kd ϑ) * j + j + hf j
          ≤ M j := by
    intro j hj1 hjn
    have hb := hMcap j hj1 hjn
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hmul := mul_le_mul_of_nonneg_right hslope hj
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  refine proposition5_lower (B := blockSlopeAdd Kd 125) hGw (by norm_num) hvlo hvhi
    (driftConstAdd_nonneg hKd) hslope _ hP _ N
    blockWindow M M' n (1 / 2) a hf
    (fun m => measurable_blockLocalLogAdd_weight hX ϑ (blockOffsetWeight ϑ t s) m) hNm hNG
    (fun j hj => abs_sum_blockGaussMeanAddAt_sub_le_of_offset hX h14 (by omega) hy hres
      (hσ n le_rfl) (fun m hm => ht m (by omega)) hKd (fun m hm => hosc m (by omega)))
    (fun m => blockWindow_pos m)
    (fun j _ => sum_inv_sq_range_le_two j) hM0 hMcap' hMM (by norm_num) le_rfl
    (hcmp 0 (Nat.zero_le n)) ha hn hbig hbig2 hhf

/-! ### Proposition 6, the upper half

The `≤` side of Harper's Proposition 6.  The two halves carry **different envelopes**, and that is
not an artefact of the formalisation: the lower bound shrinks the event to Harper's capped barrier
and needs `M_j ≥ Bj` free of `a`, while the upper bound restarts at `⌊a⌋` and needs its envelope
only above `a`, where it may mention `a`. -/

/-- **Proposition 6, upper bound, at Harper's offsets, with the tilt cutoff free.**
The mirror of `RMF.proposition5_lower_rademacher_of_offset_of_cutoff`, and the same separation:
`y` is the cutoff, every other index is the range.

`hV` and `hosc` are carried exactly as in the lower half, with the same dischargers, so that the
packaging step chooses the threshold `Tsh` once for both. -/
theorem proposition5_upper_rademacher_of_offset_of_cutoff
    (hX : IsRademacherPrimeValues X μ)
    {ϑ σ a Kd : ℝ} {t : ℕ → ℝ} {n y : ℕ} {s : ℂ} {M M' hf : ℕ → ℝ}
    (hϑ : (125 : ℝ) ≤ ϑ) (hy : blockCutoff ϑ n ≤ y)
    (hres : s.re = 1 / 2 + σ)
    (hσtop : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1)
    (ht : ∀ m, m < n →
      |t m| * Real.log (blockScale ϑ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3)))
    (hKd : 0 ≤ Kd)
    (hosc : ∀ m, m < n →
      |∑ p ∈ primeBlockSub ϑ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub ϑ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ)))
    (hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd X μ (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd X μ (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ) ≤ 9)
    (henvc : ∀ m, m < n →
      M' m + blockWindow m + 21
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))))
    (hM0 : ∀ j, 0 ≤ M j)
    (hMup : ∀ j : ℕ, a < (j : ℝ) → j ≤ n →
      (3 + blockSlopeAdd Kd 125) * a
        + blockSlopeAdd Kd 125 * j + j
        + 20 * Real.log j ≤ M j)
    (hMM : ∀ m, m < n → M m + M (m + 1) + blockWindow m ≤ M' m)
    (ha : max 1 (result1Threshold (1 / 16) (9 / 2)) ≤ a) (hn4 : 4 ≤ n)
    (hbig : 4 * Real.log n ^ 20 ≤ (n : ℝ))
    (hbig2 : 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 16))
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ)
        (barrierEvent
          (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
            localLogAdd (blockOffsetWeight ϑ t s p) (X (p : ℕ) ω)) n
          (fun j => -a - blockSlopeAdd Kd 125 * j)
          (fun j => a + j + hf j))).toReal
      ≤ 2 * result1Const (1 / 16) (9 / 2)
          * (Real.sqrt 2 * (15 + blockSlopeAdd Kd 125
              + 2 * driftConstAdd Kd ϑ + 10 * Real.log 2))
        * min 1 (a / Real.sqrt n) := by
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hGw, hNm, hNG, hvlo, hvhi, hcmp⟩ :=
    exists_isGaussianWalk_rademacher_of_offset_of_cutoff hX hϑ hy hres hσtop hV henvc
  have hσ := hsigma_of_top hσtop
  have h14 : (14 : ℝ) ≤ ϑ := by linarith
  have hm3' : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + ϑ := by
    push_cast
    linarith
  have hs : 0 < s.re := re_pos_of_block hm3' hres (hσ 0 (Nat.zero_le n))
  have hP : IsProbabilityMeasure
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) :=
    isProbabilityMeasure_tiltedMeasure_rademacher hX (y) hs
  -- the upper bound restarts at `⌊a⌋`; above the horizon the comparison is vacuous
  have hcmp' : IsWindowComparison
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) (y) s μ) Q
      (fun m ω => ∑ p ∈ primeBlockSub ϑ (m + ⌊a⌋₊),
        localLogAdd (blockOffsetWeight ϑ t s p) (X (p : ℕ) ω))
      (fun m => N (m + ⌊a⌋₊)) (fun m => blockWindow (m + ⌊a⌋₊))
      (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) (1 / 2) := by
    by_cases hk : ⌊a⌋₊ ≤ n
    · exact hcmp ⌊a⌋₊ hk
    · rw [show n - ⌊a⌋₊ = 0 from by omega]
      exact isWindowComparison_zero _ _ _ _ (by norm_num)
  exact proposition5_upper hGw (by norm_num) hvlo hvhi (driftConstAdd_nonneg hKd)
    (blockSlopeAdd_pos hKd)
    _ hP _ N blockWindow M M' n (1 / 2) a hf
    (fun m => measurable_blockLocalLogAdd_weight hX ϑ (blockOffsetWeight ϑ t s) m) hNm hNG
    (fun j hj => abs_sum_blockGaussMeanAddAt_sub_le_of_offset hX h14 (by omega) hy hres
      (hσ n le_rfl) (fun m hm => ht m (by omega)) hKd (fun m hm => hosc m (by omega)))
    (fun m => blockWindow_pos m)
    (fun j _ => sum_inv_sq_range_le_two j) hM0 hMup hMM (by norm_num) le_rfl hcmp' ha hn4
    hbig hbig2 hhf

/-! ### The envelope, from the offset alone

`RMF.envelope_of_le` does this for the Steinhaus branch.  Two numbers change.  The slack is `14`
there because the Steinhaus walk asks `M' m + blockWindow m + 7`; the Rademacher walk asks `+ 21`,
so the slack is `28`.  And the slope is `RMF.blockSlopeAdd` rather than `RMF.blockSlope`.  The
argument is otherwise identical: the left side is at most `(4B₀ + 76)(m+1)`, the right side at
least `(1/80)e^{(1+ϑ)/2}(m+1)`, the `(m+1)` cancels, and the rest is the definition of `ϑ₀`. -/

/-- The offset threshold for the Rademacher branch, mirroring `RMF.blockOffsetThreshold`. -/
noncomputable def blockOffsetThresholdAdd (Kd : ℝ) : ℝ :=
  max 125 (2 * Real.log (80 * (4 * blockSlopeAdd Kd 125 + 76)) - 1)

lemma le_blockOffsetThresholdAdd (Kd : ℝ) : (125 : ℝ) ≤ blockOffsetThresholdAdd Kd :=
  le_max_left _ _

/-- **The envelope, from the offset alone** — the Rademacher analogue of `RMF.envelope_of_le`.
No hypothesis on `M`, none on `a` beyond `1 ≤ a`, and none on `m`. -/
lemma envelope_of_le_add {Kd ϑ a : ℝ} {m : ℕ} (hKd : 0 ≤ Kd)
    (hϑ : blockOffsetThresholdAdd Kd ≤ ϑ) (ha : 1 ≤ a) :
    2 * (3 + blockSlopeAdd Kd 125) * min a ((m : ℝ) + 1)
        + blockSlopeAdd Kd 125 * (2 * (m : ℝ) + 1)
        + (2 * (m : ℝ) + 1) + 40 * Real.log ((m : ℝ) + 1) + 28
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB0 : (0 : ℝ) < blockSlopeAdd Kd 125 := blockSlopeAdd_pos hKd
  have hsq : Real.sqrt (Real.log (blockScale ϑ (m + 1)))
      = Real.exp ((((m : ℝ) + 1) + ϑ) / 2) := by
    rw [log_blockScale, ← Real.exp_half]
    congr 2
    push_cast
    ring
  -- `e^{(1+ϑ)/2} ≥ 80(4B₀ + 76)`
  have hkey : 80 * (4 * blockSlopeAdd Kd 125 + 76) ≤ Real.exp ((1 + ϑ) / 2) := by
    have hpos : (0 : ℝ) < 80 * (4 * blockSlopeAdd Kd 125 + 76) := by linarith
    have hlog : Real.log (80 * (4 * blockSlopeAdd Kd 125 + 76)) ≤ (1 + ϑ) / 2 := by
      have := le_trans (le_max_right (125 : ℝ) _) hϑ
      linarith
    calc 80 * (4 * blockSlopeAdd Kd 125 + 76)
        = Real.exp (Real.log (80 * (4 * blockSlopeAdd Kd 125 + 76))) := (Real.exp_log hpos).symm
      _ ≤ Real.exp ((1 + ϑ) / 2) := Real.exp_le_exp.2 hlog
  have hexpm : ((m : ℝ) + 1) / 2 ≤ Real.exp ((m : ℝ) / 2) := by
    linarith [Real.add_one_le_exp ((m : ℝ) / 2)]
  have hsplit : Real.exp ((((m : ℝ) + 1) + ϑ) / 2)
      = Real.exp ((1 + ϑ) / 2) * Real.exp ((m : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlogm : Real.log ((m : ℝ) + 1) ≤ (m : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by linarith)]
  have hmin : min a ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min a ((m : ℝ) + 1) := le_min (by linarith) (by linarith)
  have hlhs : 2 * (3 + blockSlopeAdd Kd 125) * min a ((m : ℝ) + 1)
      + blockSlopeAdd Kd 125 * (2 * (m : ℝ) + 1)
      + (2 * (m : ℝ) + 1) + 40 * Real.log ((m : ℝ) + 1) + 28
        ≤ (4 * blockSlopeAdd Kd 125 + 76) * ((m : ℝ) + 1) := by
    nlinarith [hmin, hmin0, hlogm, hm0, hB0]
  have hrhs : (4 * blockSlopeAdd Kd 125 + 76) * ((m : ℝ) + 1)
      ≤ 1 / 40 * Real.exp ((((m : ℝ) + 1) + ϑ) / 2) := by
    rw [hsplit]
    have hstep : 80 * (4 * blockSlopeAdd Kd 125 + 76) * (((m : ℝ) + 1) / 2)
        ≤ Real.exp ((1 + ϑ) / 2) * Real.exp ((m : ℝ) / 2) :=
      mul_le_mul hkey hexpm (by linarith) (le_trans (by linarith) hkey)
    linarith
  rw [hsq]
  linarith

/-! ### Proposition 6, packaged

Harper's Proposition 6, with every constant absolute: there is a large natural number `B` such
that `P_Rad(-a - Bj ≤ ∑ log|I| ≤ a + j + h(j) ∀ j ≤ n) ≍ min{1, a/√n}`.

Everything is chosen **before** the probability space is quantified, which makes `B` absolute:
`Tsh` from the variance bracket, `K` from `RMF.exists_abs_sum_cos_primeBlockSub_rpow_le`, then
`K_d = (3/2)(K/Tsh)` and `B = blockSlopeAdd K_d 125`.  Two deviations from Harper's constants:

* the tilt bound is `|σ|·log x_{n+1} ≤ 1/10`, where Harper has `|σ| ≤ 1/e^{D+n}`, i.e. `≤ 1`; the
  variance bracket needs `η ≤ 1/10`, and the factor ten costs `D → D + log 10`;
* the height conditions are stated at both frequencies `2·Im s + t_m` and `2(Im s + t_m)`, and at
  `e^ϑ` rather than `e^{m+ϑ}` — the stronger, `m`-free form, Harper's
  `D ≥ max{log(1/|t|), 2 log log(1+|t|)} + (B+1)` made explicit. -/

set_option maxHeartbeats 400000 in
-- this proof applies BOTH Proposition 6 halves, and with the tilt cutoff free
-- neither application has the cutoff to pin its implicit indices early
/-- **Proposition 6 with absolute constants, at Harper's offsets, with the tilt cutoff free.**
`y` is the tilt cutoff and every other index is the range, so a consumer may run the barrier to
`n` while tilting at any `y ≥ RMF.blockCutoff ϑ n`, and the drop `n ↦ n - d` is one
instantiation.  `RMF.primeBlockSub_subset_primesBelowSub_of_le` supplies the inclusion
`primeBlockSub ϑ m ⊆ primesBelowSub y` that `RMF.exists_blockMatchedVarAdd_concrete_of_offset_top`
takes. -/
theorem exists_const_proposition5_rademacher_of_offset_of_cutoff :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ α A B Tsh : ℝ),
      0 < α ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (ϑ σ a : ℝ) (n y : ℕ) (s : ℂ) (t hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → blockCutoff ϑ n ≤ y → s.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 / 10 →
          (∀ m, m < n →
            |t m| * Real.log (blockScale ϑ (m + 1)) ≤ ((m : ℝ) + 1) ^ (-((2 : ℝ) / 3))) →
          (∀ m, m ≤ n →
            0 < 2 * s.im + t m ∧ (2 * s.im + t m) ^ 2 ≤ Real.exp ϑ
              ∧ Tsh ≤ (2 * s.im + t m) * Real.exp ϑ
              ∧ 0 < 2 * (s.im + t m) ∧ (2 * (s.im + t m)) ^ 2 ≤ Real.exp ϑ
              ∧ Tsh ≤ 2 * (s.im + t m) * Real.exp ϑ) →
          a₀ ≤ a → n₀ ≤ n →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt n)
                ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (blockOffsetWeight ϑ t s p) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (blockOffsetWeight ϑ t s p) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt n) := by
  obtain ⟨n₀, hn₀⟩ := exists_blockSizeThreshold
  obtain ⟨Tsh, hTsh0, HV⟩ := exists_blockMatchedVarAdd_concrete_of_offset_top
  obtain ⟨K, hK0, HK⟩ := exists_abs_sum_cos_primeBlockSub_rpow_le
  set Kd : ℝ := 3 / 2 * (K / Tsh) with hKddef
  have hKd : (0 : ℝ) ≤ Kd := by
    rw [hKddef]
    positivity
  have hB0 : (0 : ℝ) < blockSlopeAdd Kd 125 := blockSlopeAdd_pos hKd
  have hB20 : (20 : ℝ) ≤ blockSlopeAdd Kd 125 := twenty_le_blockSlopeAdd hKd
  have hdc0 : (0 : ℝ) ≤ driftConstAdd Kd 125 := driftConstAdd_nonneg hKd
  have hRC1 : (1 : ℝ) ≤ result1Const (1 / 16) (9 / 2) := one_le_result1Const _ _
  have h2s : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨blockOffsetThresholdAdd Kd, n₀,
    max (max 1 (result2Threshold (1 / 16) (9 / 2) + 2 + driftConstAdd Kd 125))
      (max (4 + 2 * driftConstAdd Kd 125) (max 1 (result1Threshold (1 / 16) (9 / 2)))),
    result1LowerConst (1 / 16) (9 / 2) / 2 / 4,
    2 * result1Const (1 / 16) (9 / 2)
      * (Real.sqrt 2 * (15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd 125 + 10 * Real.log 2)),
    blockSlopeAdd Kd 125, Tsh, ?_, ?_, hB20, hTsh0, ?_⟩
  · have hlc : (0 : ℝ) < result1LowerConst (1 / 16) (9 / 2) :=
      result1LowerConst_pos (by norm_num) (by norm_num)
    linarith
  · have hp1 : (0 : ℝ) < 2 * result1Const (1 / 16) (9 / 2) := by linarith
    have hin : (0 : ℝ)
        < 15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd 125 + 10 * Real.log 2 := by
      linarith
    exact mul_pos hp1 (by nlinarith [h2s, hin])
  intro Ω' _ Y ν hY ϑ σ a n y s t hf hϑ hy hres hσtop ht hfreq ha hn hhf
  have h125 : (125 : ℝ) ≤ ϑ := le_trans (le_blockOffsetThresholdAdd Kd) hϑ
  have hϑ0 : (0 : ℝ) ≤ ϑ := by linarith
  obtain ⟨hn4, hbig, hbig2⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := by omega
  have hσtop1 : |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 := by linarith
  have hσm : ∀ m : ℕ, m ≤ n → |σ| * Real.log (blockScale ϑ (m + 1)) ≤ 1 / 10 := by
    intro m hmn
    have h := sigma_le_mul_exp_sub ϑ σ (1 / 10) hσtop (m := m) (n := n)
    have hle : Real.exp ((m : ℝ) - n) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    nlinarith [h, hle, Real.exp_pos ((m : ℝ) - n)]
  have hm3' : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + ϑ := by
    push_cast
    linarith
  have hs : 0 < s.re := re_pos_of_block hm3' hres (hsigma_of_top hσtop1 0 (Nat.zero_le n))
  -- the variance bracket, at every block
  have hV : ∀ m, m ≤ n →
      1 / 8 ≤ 2 * ((blockMatchedVarAdd Y ν (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ)
        ∧ 2 * ((blockMatchedVarAdd Y ν (y) s (blockOffsetWeight ϑ t s)
          (primeBlockSub ϑ m) : ℝ≥0) : ℝ) ≤ 9 := by
    intro m hmn
    obtain ⟨-, -, -, hτ0, hτsq, hT⟩ := hfreq m hmn
    have hm9 : (9 : ℝ) ≤ (m : ℝ) + ϑ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hexp : Real.exp ϑ ≤ Real.exp ((m : ℝ) + ϑ) := by
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    refine HV Ω' Y ν hY ϑ σ (1 / 10) t m (y) s hs hres hm9 hϑ0
      (by norm_num) le_rfl (hσm m hmn) hτ0 (le_trans hτsq hexp) ?_
      (primeBlockSub_subset_primesBelowSub_of_le hmn hy)
    exact le_trans hT (mul_le_mul_of_nonneg_left hexp (by linarith))
  -- the oscillatory pair, geometric under the height threshold
  have hosc : ∀ m, m < n →
      |∑ p ∈ primeBlockSub ϑ m,
          Real.cos ((2 * s.im + t m) * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        + |∑ p ∈ primeBlockSub ϑ m,
            Real.cos (2 * (s.im + t m) * Real.log ((p : ℕ) : ℝ))
              * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| / 2
        ≤ Kd * Real.exp (-(m : ℝ)) := by
    intro m hmn
    obtain ⟨hτ10, hτ1sq, hT1, hτ20, hτ2sq, hT2⟩ := hfreq m hmn.le
    have hσ1 : |σ| * Real.log (blockScale ϑ (m + 1)) ≤ 1 := by
      linarith [hσm m hmn.le]
    have hexp : Real.exp ϑ ≤ Real.exp ((m : ℝ) + ϑ) := by
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hA := HK (2 * s.im + t m) σ ϑ m hτ10 hϑ0 (le_trans hτ1sq hexp) hσ1
    have hC := HK (2 * (s.im + t m)) σ ϑ m hτ20 hϑ0 (le_trans hτ2sq hexp) hσ1
    exact abs_sum_cos_pair_le_of_threshold hK0 hTsh0 hA hC hτ10 hτ20 hT1 hT2
  -- the envelope
  set M : ℕ → ℝ := fun j =>
    (3 + blockSlopeAdd Kd 125) * min a (j : ℝ) + blockSlopeAdd Kd 125 * (j : ℝ) + (j : ℝ)
      + 20 * Real.log (j : ℝ) with hMdef
  set M' : ℕ → ℝ := fun m => M m + M (m + 1) + blockWindow m with hM'def
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hlogn : ∀ j : ℕ, (0 : ℝ) ≤ Real.log (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hj)
  have henvc : ∀ m, m < n →
      M' m + blockWindow m + 21
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
    intro m _
    have hW0 : (0 : ℝ) < blockWindow m := blockWindow_pos m
    have hW : blockWindow m ≤ 1 := by
      rw [blockWindow, div_le_one (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · exact Real.log_le_log (by exact_mod_cast hm0) (by linarith)
    have hminmono : min a (m : ℝ) ≤ min a ((m : ℝ) + 1) := min_le_min le_rfl (by linarith)
    have hmm : (3 + blockSlopeAdd Kd 125) * min a (m : ℝ)
        ≤ (3 + blockSlopeAdd Kd 125) * min a ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hminmono (by linarith)
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hbud := envelope_of_le_add (Kd := Kd) (ϑ := ϑ) (a := a) (m := m) hKd hϑ ha1
    simp only [hM'def, hMdef, hcast]
    nlinarith [hbud, hlogm, hW, hW0, hmm]
  have hM0 : ∀ j, 0 ≤ M j := by
    intro j
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    nlinarith [hlogn j, Nat.cast_nonneg (α := ℝ) j, hB0, ha0, hmin]
  have hMcap : ∀ j, 1 ≤ j → j ≤ n →
      blockSlopeAdd Kd 125 * j ≤ M j ∧
        blockSlopeAdd Kd 125 * j + j + hf j ≤ M j := by
    intro j hj1 hjn
    have habs := abs_le.1 (hhf j hj1 hjn)
    have hmin : (0 : ℝ) ≤ min a (j : ℝ) := le_min ha0 (Nat.cast_nonneg j)
    simp only [hMdef]
    exact ⟨by nlinarith [hlogn j, ha0, hB0, hmin],
      by nlinarith [habs.2, hlogn j, ha0, hB0, hmin]⟩
  have hMup : ∀ j : ℕ, a < (j : ℝ) → j ≤ n →
      (3 + blockSlopeAdd Kd 125) * a + blockSlopeAdd Kd 125 * j + j
        + 20 * Real.log j ≤ M j := by
    intro j hj _
    have hmin : min a (j : ℝ) = a := min_eq_left hj.le
    simp only [hMdef, hmin]
    exact le_rfl
  have hMM : ∀ m, m < n → M m + M (m + 1) + blockWindow m ≤ M' m := by
    intro m _
    simp only [hM'def]
    exact le_rfl
  have hdc : driftConstAdd Kd ϑ ≤ driftConstAdd Kd 125 := driftConstAdd_antitone h125
  have halow : max (max 1 (result2Threshold (1 / 16) (9 / 2) + 2 + driftConstAdd Kd ϑ))
      (4 + 2 * driftConstAdd Kd ϑ) ≤ a := by
    refine max_le (max_le ?_ ?_) ?_
    · exact ha1
    · refine le_trans ?_ ha
      refine le_trans ?_ (le_max_left _ _)
      refine le_trans ?_ (le_max_right _ _)
      linarith
    · refine le_trans ?_ ha
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_max_left _ _)
      linarith
  have haup : max 1 (result1Threshold (1 / 16) (9 / 2)) ≤ a :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ha
  refine ⟨proposition5_lower_rademacher_of_offset_of_cutoff hY h125 hy hres hσtop1 ht hKd
      hosc hV henvc
      hM0 hMcap hMM halow hn1 hbig hbig2 hhf, ?_⟩
  refine le_trans (proposition5_upper_rademacher_of_offset_of_cutoff hY h125 hy hres hσtop1
    ht hKd hosc hV henvc hM0 hMup hMM haup hn4 hbig hbig2 hhf) ?_
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) := le_min zero_le_one (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ hmin0
  have hstep : 15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd ϑ + 10 * Real.log 2
      ≤ 15 + blockSlopeAdd Kd 125 + 2 * driftConstAdd Kd 125 + 10 * Real.log 2 := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep (by linarith))
    (by linarith)

/-! ### Proposition 6 at zero offsets

The `t ≡ 0` slice of the offset form.  There the two frequencies `2·Im s + t_m` and
`2(Im s + t_m)` **collapse to the same `2·Im s`**, so the six per-block height conditions become
one `m`-free triple — which is exactly Harper's condition on `|t|` alone. -/

/-- **Proposition 6 with absolute constants, at zero offsets, with the tilt cutoff free.**
The `t ≡ 0` slice of `RMF.exists_const_proposition5_rademacher_of_offset_of_cutoff`, and the form
`RMF.exists_const_freeStart_barrier_le_rademacher_of_cutoff` consumes.  The height conditions
survive, unlike on the Steinhaus side: the Rademacher block variance and the block drift both see
the height, so `2·Im s` must be positive and bounded below. -/
theorem exists_const_proposition5_rademacher_of_cutoff :
    ∃ (ϑ₀ : ℝ) (n₀ : ℕ) (a₀ α A B Tsh : ℝ),
      0 < α ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (ϑ σ a : ℝ) (n y : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          ϑ₀ ≤ ϑ → blockCutoff ϑ n ≤ y → s.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale ϑ (n + 1)) ≤ 1 / 10 →
          0 < 2 * s.im → (2 * s.im) ^ 2 ≤ Real.exp ϑ → Tsh ≤ 2 * s.im * Real.exp ϑ →
          a₀ ≤ a → n₀ ≤ n →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            α * min 1 (a / Real.sqrt n)
                ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
              ∧ ((tiltedMeasure (fun ω => squarefreeExtension fun p => Y p ω)
                      (y) s ν)
                    (barrierEvent
                      (fun m ω => ∑ p ∈ primeBlockSub ϑ m,
                        localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y (p : ℕ) ω)) n
                      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
                  ≤ A * min 1 (a / Real.sqrt n) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, hα, hA, hB, hTsh, H⟩ :=
    exists_const_proposition5_rademacher_of_offset_of_cutoff
  refine ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, hα, hA, hB, hTsh, ?_⟩
  intro Ω' _ Y ν hY ϑ σ a n y s hf hϑ hy hres hσtop hτ0 hτsq hT ha hn hhf
  have h := H Ω' Y ν hY ϑ σ a n y s (fun _ => 0) hf hϑ hy hres hσtop
    (fun m _ => by
      simpa using Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) _)
    (fun m _ => by
      exact ⟨by simpa using hτ0, by simpa using hτsq, by simpa using hT,
        by simpa using hτ0, by simpa using hτsq, by simpa using hT⟩)
    ha hn hhf
  simpa only [blockOffsetWeight_zero] using h

end RMF
