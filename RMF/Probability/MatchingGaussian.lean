/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.GaussianEstimates
import Mathlib.Probability.HasLawExists

/-!
# The matching Gaussian family

A Lindeberg swap replaces each summand by a Gaussian with the *same first and second moments*.
`RMF.abs_integral_telescope_le` asks for exactly that, as `hm₁ : ∫ X i = ∫ Y i` and
`hm₂ : ∫ X i * X i = ∫ Y i * Y i`, so the comparison family has to be built to order.

## Raw moments, not variances

The tilted increments are **not centred** — their mean is Harper's `+ 1` of drift per block — so
the family cannot be a centred Gaussian family with matched variances.  Given targets `m₁ i` and
`m₂ i` for the raw first and second moments, the right Gaussian is

`N(m₁ i, m₂ i - m₁ i ^ 2)`,

and the variance is non-negative precisely because `m₁ i ^ 2 ≤ m₂ i`, which is Cauchy–Schwarz for
the family being matched.  That hypothesis is therefore not a restriction: it holds automatically
whenever `m₁`, `m₂` really are the first two moments of something.

## Where the space comes from

`ProbabilityTheory.exists_hasLaw_indepFun` builds an independent family with prescribed marginals
on the product space, so nothing has to be constructed by hand.  The family it produces is
independent, which the telescope needs, and its members have the prescribed Gaussian laws, from
which the two moment identities follow by transport.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace RMF

/-- The variance that matches a prescribed pair of raw moments. -/
noncomputable def matchingVar (m₁ m₂ : ℝ) : ℝ≥0 := (m₂ - m₁ ^ 2).toNNReal

lemma coe_matchingVar {m₁ m₂ : ℝ} (h : m₁ ^ 2 ≤ m₂) :
    (matchingVar m₁ m₂ : ℝ) = m₂ - m₁ ^ 2 :=
  Real.coe_toNNReal _ (by linarith)

/-- **The mean of a real Gaussian, transported to the underlying space.** -/
lemma integral_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hY : Measurable Y) (hlaw : Q.map Y = gaussianReal m v) :
    ∫ ω, Y ω ∂Q = m := by
  have h1 : (∫ y, y ∂(Q.map Y)) = ∫ ω, Y ω ∂Q :=
    integral_map hY.aemeasurable (by fun_prop)
  rw [← h1, hlaw, integral_id_gaussianReal]

/-- **The second moment of a real Gaussian, transported.**  `E[Y²] = v + m²`. -/
lemma integral_sq_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {Y : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hY : Measurable Y) (hlaw : Q.map Y = gaussianReal m v) :
    ∫ ω, Y ω * Y ω ∂Q = (v : ℝ) + m ^ 2 := by
  have hmem : MemLp Y 2 Q := by
    have hiff := memLp_map_measure_iff (μ := Q) (f := Y) (g := fun x : ℝ => x) (p := 2)
      (by fun_prop) hY.aemeasurable
    have hgauss : MemLp (fun x : ℝ => x) 2 (Q.map Y) := by
      rw [hlaw]; exact memLp_id_gaussianReal 2
    exact hiff.mp hgauss
  have hvar : Var[Y; Q] = (v : ℝ) := by
    have hmap : Var[fun x : ℝ => x; Q.map Y] = Var[(fun x : ℝ => x) ∘ Y; Q] :=
      variance_map (by fun_prop) hY.aemeasurable
    rw [hlaw, variance_fun_id_gaussianReal] at hmap
    exact hmap.symm
  have hmean : ∫ ω, Y ω ∂Q = m := integral_of_hasLaw_gaussianReal hY hlaw
  have hsub := variance_eq_sub hmem
  rw [hvar, hmean] at hsub
  have hpow : (∫ ω, (Y ^ 2) ω ∂Q) = ∫ ω, Y ω * Y ω ∂Q := by
    simp only [Pi.pow_apply, pow_two]
  rw [hpow] at hsub
  linarith

/-- **The matching Gaussian family.**  Given target raw moments `m₁`, `m₂` with `m₁ i ^ 2 ≤ m₂ i`,
there is a probability space carrying an **independent** family of real Gaussians whose first and
second raw moments are exactly `m₁` and `m₂`, as `RMF.abs_integral_telescope_le` asks of its
comparison family.  The hypothesis is Cauchy–Schwarz for the family being matched
(`RMF.sq_integral_le_integral_mul_self`), so it is free at the point of use. -/
theorem exists_gaussian_matching_moments {ι : Type u} (m₁ m₂ : ι → ℝ)
    (h : ∀ i, m₁ i ^ 2 ≤ m₂ i) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (Q : Measure Ω') (Y : ι → Ω' → ℝ),
      IsProbabilityMeasure Q ∧ (∀ i, Measurable (Y i)) ∧ iIndepFun Y Q ∧
        (∀ i, Q.map (Y i) = gaussianReal (m₁ i) (matchingVar (m₁ i) (m₂ i))) ∧
        (∀ i, ∫ ω, Y i ω ∂Q = m₁ i) ∧
        (∀ i, ∫ ω, Y i ω * Y i ω ∂Q = m₂ i) := by
  obtain ⟨Ω', mΩ', Q, Y, hYm, hYlaw, hYind, hQ⟩ :=
    exists_hasLaw_indepFun (fun _ : ι => ℝ)
      (fun i => gaussianReal (m₁ i) (matchingVar (m₁ i) (m₂ i)))
  refine ⟨Ω', mΩ', Q, Y, hQ, hYm, hYind, fun i => (hYlaw i).map_eq, fun i => ?_, fun i => ?_⟩
  · exact integral_of_hasLaw_gaussianReal (hYm i) (hYlaw i).map_eq
  · rw [integral_sq_of_hasLaw_gaussianReal (hYm i) (hYlaw i).map_eq, coe_matchingVar (h i)]
    ring

/-! ### Discharging the two hypotheses the matching needs

`exists_gaussian_matching_moments` asks `m₁ i ² ≤ m₂ i`, and the numerical condition downstream
needs a bound on the *third* absolute moment of a Gaussian that is **not centred**.  Both are
supplied here, so that neither is left to the caller. -/

/-- **Cauchy–Schwarz, in the form the matching wants**: `(E X)² ≤ E X²`.  This is why the variance
of the matching Gaussian is non-negative, so the hypothesis of
`RMF.exists_gaussian_matching_moments` is free wherever the moments really are moments. -/
lemma sq_integral_le_integral_mul_self {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, X ω ∂P) ^ 2 ≤ ∫ ω, X ω * X ω ∂P := by
  have hnn := variance_nonneg X P
  have hsub := variance_eq_sub hX
  have hpow : (∫ ω, (X ^ 2) ω ∂P) = ∫ ω, X ω * X ω ∂P := by
    simp only [Pi.pow_apply, pow_two]
  rw [hpow] at hsub
  linarith

/-- `(a + b)³ ≤ 4(a³ + b³)` for `a, b ≥ 0` — convexity of the cube, in the crude form the third
moment of a shifted Gaussian needs. -/
lemma add_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb]

/-- **The third absolute moment of a Gaussian that is not centred.**  Shifting by `m` costs a
factor `4` and an additive `|m|³`; the centred moment is `RMF.integral_abs_pow_gaussianReal`.

Harper's block increments have mean `≈ 1` per block, so the Gaussians matched to them are *not*
centred and this is the bound the numerical condition actually consumes. -/
lemma integral_abs_cube_gaussianReal_le (m : ℝ) (v : ℝ≥0) :
    ∫ x, |x| ^ 3 ∂(gaussianReal m v) ≤ 4 * (absMomentConst 3 * √(v : ℝ) ^ 3 + |m| ^ 3) := by
  have hshift : gaussianReal m v = (gaussianReal 0 v).map (· + m) := by
    rw [gaussianReal_map_add_const, zero_add]
  have hint₃ : Integrable (fun z : ℝ => |z| ^ 3) (gaussianReal 0 v) :=
    integrable_abs_pow_gaussianReal v 3
  have hmap : ∫ x, |x| ^ 3 ∂(gaussianReal m v) = ∫ z, |z + m| ^ 3 ∂(gaussianReal 0 v) := by
    rw [hshift, integral_map (by fun_prop) (by fun_prop)]
  have hmaj : Integrable (fun z : ℝ => 4 * (|z| ^ 3 + |m| ^ 3)) (gaussianReal 0 v) :=
    (hint₃.add (integrable_const _)).const_mul 4
  have hpt : ∀ z : ℝ, |z + m| ^ 3 ≤ 4 * (|z| ^ 3 + |m| ^ 3) := by
    intro z
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le z m) 3) ?_
    exact add_cube_le (abs_nonneg z) (abs_nonneg m)
  have hint : Integrable (fun z : ℝ => |z + m| ^ 3) (gaussianReal 0 v) := by
    refine hmaj.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt z
  rw [hmap]
  calc ∫ z, |z + m| ^ 3 ∂(gaussianReal 0 v)
      ≤ ∫ z, 4 * (|z| ^ 3 + |m| ^ 3) ∂(gaussianReal 0 v) :=
        integral_mono hint hmaj hpt
    _ = 4 * ((∫ z, |z| ^ 3 ∂(gaussianReal 0 v)) + |m| ^ 3) := by
        rw [integral_const_mul, integral_add hint₃ (integrable_const _)]
        simp
    _ = 4 * (absMomentConst 3 * √(v : ℝ) ^ 3 + |m| ^ 3) := by
        rw [integral_abs_pow_gaussianReal]

/-! ### Everything the comparison needs from the Gaussian side

`RMF.isWindowComparison₁_of_gaussian_family` asks for integrability of `G i`, of `G i · G i` and of
`|G i|³`, and for a bound on the third absolute moment.  All four depend only on the *law*, so they
are proved once from `hlaw` and applied pointwise — the caller never has to touch the auxiliary
space the family lives on. -/

/-- A random variable with a Gaussian law is integrable. -/
lemma integrable_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hY : Measurable Y) (hlaw : Q.map Y = gaussianReal m v) :
    Integrable Y Q := by
  have h : Integrable id (Q.map Y) := by
    rw [hlaw]; exact memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  exact h.comp_aemeasurable hY.aemeasurable

/-- Its square is integrable. -/
lemma integrable_mul_self_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hY : Measurable Y) (hlaw : Q.map Y = gaussianReal m v) :
    Integrable (fun ω => Y ω * Y ω) Q := by
  have h : Integrable (fun x : ℝ => x * x) (Q.map Y) := by
    rw [hlaw]
    have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal m v) := memLp_id_gaussianReal 2
    have h2 := hmem.integrable_mul hmem
    have hfun : ((fun x : ℝ => x) * fun x : ℝ => x) = fun x : ℝ => x * x := by
      funext x; simp
    rwa [hfun] at h2
  exact h.comp_aemeasurable hY.aemeasurable

/-- Its third absolute moment is finite. -/
lemma integrable_abs_cube_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → ℝ} {m : ℝ} {v : ℝ≥0} (hY : Measurable Y) (hlaw : Q.map Y = gaussianReal m v) :
    Integrable (fun ω => |Y ω| ^ 3) Q := by
  have h : Integrable (fun x : ℝ => |x| ^ 3) (Q.map Y) := by
    rw [hlaw]
    have hshift : gaussianReal m v = (gaussianReal 0 v).map (· + m) := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [hshift, integrable_map_measure (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def]
    have hint₃ : Integrable (fun z : ℝ => |z| ^ 3) (gaussianReal 0 v) :=
      integrable_abs_pow_gaussianReal v 3
    have hmaj : Integrable (fun z : ℝ => 4 * (|z| ^ 3 + |m| ^ 3)) (gaussianReal 0 v) :=
      (hint₃.add (integrable_const _)).const_mul 4
    refine hmaj.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le z m) 3) ?_
    exact add_cube_le (abs_nonneg z) (abs_nonneg m)
  exact h.comp_aemeasurable hY.aemeasurable

/-- **The third moment of the matched Gaussian, from the two moments it matches.**

The Gaussian matched to `(m₁, m₂)` has variance `m₂ - m₁² ≤ m₂`, so its third absolute moment is
controlled by `m₂` and `m₁` alone.  This is what turns a bound on the *summands'* moments into the
`T` of `RMF.isWindowComparison₁_of_gaussian_family_of_third_moment`. -/
lemma integral_abs_cube_gaussianReal_matching_le {m₁ m₂ : ℝ} (h : m₁ ^ 2 ≤ m₂) :
    ∫ x, |x| ^ 3 ∂(gaussianReal m₁ (matchingVar m₁ m₂))
      ≤ 4 * (absMomentConst 3 * √m₂ ^ 3 + |m₁| ^ 3) := by
  refine le_trans (integral_abs_cube_gaussianReal_le m₁ (matchingVar m₁ m₂)) ?_
  have hle : √((matchingVar m₁ m₂ : ℝ≥0) : ℝ) ≤ √m₂ := by
    rw [coe_matchingVar h]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg m₁])
  have hcube : √((matchingVar m₁ m₂ : ℝ≥0) : ℝ) ^ 3 ≤ √m₂ ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 3
  have h0 := absMomentConst_nonneg 3
  nlinarith

/-- The same bound, transported to a random variable carrying the matched law. -/
lemma integral_abs_cube_of_hasLaw_matching {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → ℝ} {m₁ m₂ : ℝ} (hY : Measurable Y) (h : m₁ ^ 2 ≤ m₂)
    (hlaw : Q.map Y = gaussianReal m₁ (matchingVar m₁ m₂)) :
    ∫ ω, |Y ω| ^ 3 ∂Q ≤ 4 * (absMomentConst 3 * √m₂ ^ 3 + |m₁| ^ 3) := by
  have hmap : ∫ x, |x| ^ 3 ∂(Q.map Y) = ∫ ω, |Y ω| ^ 3 ∂Q :=
    integral_map hY.aemeasurable (by fun_prop)
  rw [← hmap, hlaw]
  exact integral_abs_cube_gaussianReal_matching_le h

/-! ### The sum of the family

A block increment is a *sum* over the primes of the block, so the comparison at the end is between
the block sum and a single Gaussian.  Mathlib has the two-variable convolution
(`gaussianReal_add_gaussianReal_of_indepFun`) but not the `Finset` version; this is the
induction. -/

/-- **An independent Gaussian family sums to a Gaussian**, with the means and variances added. -/
theorem map_sum_gaussianReal {ι : Type*} {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {G : ι → Ω' → ℝ} {m : ι → ℝ} {v : ι → ℝ≥0}
    (hGm : ∀ i, Measurable (G i)) (hGi : iIndepFun G Q)
    (hlaw : ∀ i, Q.map (G i) = gaussianReal (m i) (v i)) (s : Finset ι) :
    Q.map (fun ω => ∑ i ∈ s, G i ω) = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [gaussianReal_zero_var, Measure.map_const, measure_univ, one_smul]
  | insert a t ha ih =>
    have hindep : IndepFun (G a) (fun ω => ∑ i ∈ t, G i ω) Q := by
      have h := (hGi.indepFun_finsetSum_of_notMem hGm ha).symm
      have hfun : (∑ j ∈ t, G j) = fun ω => ∑ i ∈ t, G i ω := by
        funext ω; simp [Finset.sum_apply]
      rwa [hfun] at h
    have hsum : (fun ω => ∑ i ∈ insert a t, G i ω)
        = G a + fun ω => ∑ i ∈ t, G i ω := by
      funext ω
      simp [Finset.sum_insert ha]
    rw [hsum, Finset.sum_insert ha, Finset.sum_insert ha,
      gaussianReal_add_gaussianReal_of_indepFun hindep (hlaw a) ih]

end RMF
