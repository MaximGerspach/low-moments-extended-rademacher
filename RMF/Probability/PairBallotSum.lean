/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.PairBallot
import RMF.Probability.HarperChainSlack
import RMF.Probability.BlockComparison
import RMF.NumberTheory.MertensBlock
import RMF.Probability.BlockComparisonPair
import RMF.EulerProduct.JointLaplace
import RMF.Probability.PairBoxCorrelated
import RMF.Analysis.Lindeberg
import RMF.Probability.BlockComparisonPairSharp
import RMF.NumberTheory.StrongBlockCosineExplicit
import RMF.NumberTheory.PNTThresholdExplicit
import RMF.Probability.RestrictedSecondMoment.Drift
import RMF.Probability.BallotLower

/-!
# The Gaussian pair ballot with summed variances

The decoupled pair ballot, with each survival bounded through the sum of its own variances, as in
the sharp one-dimensional survival `RMF.IsGaussianWalk.measureReal_survival_le_sqrt`, rather than
through one lower variance `v₋` over all blocks.

* `RMF.IsGaussianWalk.measureReal_forall_le_le_sqrt_sum`: the flat-ceiling ballot
  `P(walk ≤ y on [0,n]) ≤ (y + c)√(2/(π∑_{i<n} v_i))`, the constant-barrier case of
  `RMF.IsGaussianWalk.measureReal_survival_le_sqrt`.
* `RMF.IsGaussianWalk.setIntegral_abs_survival_le_sum`: the ballot weighted by one increment,
  `E[|G_m|; survive] ≤ ((y + c)√v₊ + v₊)√(2/(π(∑_{i<n} v_i - v₊)))`: the walk without increment
  `m` has `n - 1` steps whose variances sum to at least `∑_{i<n} v_i - v₊`.
* `RMF.measureReal_prod_pairBallot_le_sum`: the decoupled pair ballot with
  `β' = √(2/(π(∑_{i<n} v₁ᵢ - v₊)))` and `β = √(2/(π∑_{i<n} v₂ᵢ))`.
* `RMF.measureReal_barrierEventPair_le_of_boxComparison_sum`: the pair barrier from a box
  comparison, with walk 1's variances and the residual variances summed over the blocks.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace RMF

section OneDim

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {Q : Measure Ω}
  [IsProbabilityMeasure Q]

/-- **The flat-ceiling ballot with summed variances**:
`Q(walk_j ≤ y, j ≤ n) ≤ (y + c)√(2/(π∑_{i<n} v_i))` for `y ≥ 0`, `n ≥ 1`, nonzero variances at
most `v₊` and `c ≥ √(πv₊/2)`: `RMF.IsGaussianWalk.measureReal_survival_le_sqrt` at the constant
barrier. -/
theorem IsGaussianWalk.measureReal_forall_le_le_sqrt_sum (h : IsGaussianWalk G v Q)
    (hv0 : ∀ i, v i ≠ 0) {vmax : ℝ} (hv : ∀ i, (v i : ℝ) ≤ vmax) {c : ℝ} (hc0 : 0 < c)
    (hc : √(π * vmax / 2) ≤ c) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 ≤ y) :
    Q.real {ω | ∀ j ≤ n, walk G j ω ≤ y}
      ≤ (y + c) * √(2 / (π * ∑ i ∈ Finset.range n, (v i : ℝ))) :=
  h.measureReal_survival_le_sqrt (g := fun _ => y) hy hn (fun _ _ => le_rfl) hv0 hc0
    fun i => le_trans (Real.sqrt_le_sqrt (by have := hv i; nlinarith [Real.pi_pos])) hc

/-- `n ≥ 2` once variances, each at most `v₊`, sum to more than `v₊` over `[0, n)`. -/
lemma two_le_of_lt_sum {vmax : ℝ} (hv : ∀ i, (v i : ℝ) ≤ vmax) {n : ℕ}
    (hsum : vmax < ∑ i ∈ Finset.range n, (v i : ℝ)) : 2 ≤ n := by
  by_contra hlt
  push Not at hlt
  have hle : ∑ i ∈ Finset.range n, (v i : ℝ) ≤ vmax := by
    interval_cases n
    · simpa using le_trans (NNReal.coe_nonneg (v 0)) (hv 0)
    · simpa using hv 0
  linarith

end OneDim

section Skip

/-- **The walk without increment `m` keeps all variances but one**: over its first `n - 1` steps
they sum to at least `∑_{i<n} w_i - v₊`, when every `w_i ≤ v₊`. -/
lemma sum_range_sub_le_sum_skipIdx {w : ℕ → ℝ} {vmax : ℝ} (hw : ∀ i, w i ≤ vmax) (m : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, w i - vmax ≤ ∑ i ∈ Finset.range (n - 1), w (skipIdx m i) := by
  classical
  set T : Finset ℕ := (Finset.range (n - 1)).image (skipIdx m) with hT
  have hTsub : T ⊆ Finset.range n := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    have h1 := skipIdx_le_succ m i
    rw [Finset.mem_range] at hi ⊢
    omega
  have hcard : (Finset.range n \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hTsub, hT,
      Finset.card_image_of_injective _ (skipIdx_injective m), Finset.card_range,
      Finset.card_range]
    omega
  have himg : ∑ j ∈ T, w j = ∑ i ∈ Finset.range (n - 1), w (skipIdx m i) :=
    Finset.sum_image fun a _ b _ hab => skipIdx_injective m hab
  have hsplit := Finset.sum_sdiff hTsub (f := w)
  have hrest : ∑ j ∈ Finset.range n \ T, w j ≤ vmax := by
    have h1 := Finset.sum_le_card_nsmul (Finset.range n \ T) w vmax fun j _ => hw j
    rwa [hcard, one_nsmul] at h1
  linarith

end Skip

section WeightedBallot

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {Q : Measure Ω}
  [IsProbabilityMeasure Q]

set_option maxHeartbeats 1000000 in
-- independence, Tonelli and the one-dimensional ballot in one proof
/-- **The ballot bound weighted by one increment, with summed variances**: for nonzero
variances at most `v₊`, `c ≥ √(πv₊/2)` and `∑_{i<n} v_i > v₊`,
`E[|G_m|; walk_j ≤ y, j ≤ n] ≤ ((y + c)√v₊ + v₊)√(2/(π(∑_{i<n} v_i - v₊)))`.  On the survival
event the walk without increment `m` stays below `y + |G_m|`, and it meets the summed-variance
ballot, its `n - 1` variances summing to at least `∑_{i<n} v_i - v₊`
(`RMF.sum_range_sub_le_sum_skipIdx`). -/
theorem IsGaussianWalk.setIntegral_abs_survival_le_sum (h : IsGaussianWalk G v Q)
    (hv0 : ∀ i, v i ≠ 0) {vmax : ℝ} (hv : ∀ i, (v i : ℝ) ≤ vmax) {c : ℝ} (hc0 : 0 < c)
    (hc : √(π * vmax / 2) ≤ c) {n m : ℕ} (hsum : vmax < ∑ i ∈ Finset.range n, (v i : ℝ))
    {y : ℝ} (hy : 0 ≤ y) :
    ∫ ω in {ω | ∀ j ≤ n, walk G j ω ≤ y}, |G m ω| ∂Q
      ≤ ((y + c) * √vmax + vmax)
        * √(2 / (π * (∑ i ∈ Finset.range n, (v i : ℝ) - vmax))) := by
  classical
  have hn := two_le_of_lt_sum hv hsum
  set n' : ℕ := n - 1 with hn'def
  have hn'1 : 1 ≤ n' := by omega
  set β : ℝ := √(2 / (π * (∑ i ∈ Finset.range n, (v i : ℝ) - vmax))) with hβdef
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hvmax0 : 0 ≤ vmax := le_trans (NNReal.coe_nonneg _) (hv 0)
  -- the walk without increment `m` has a ballot constant at most `β`
  have hskip : ∑ i ∈ Finset.range n, (v i : ℝ) - vmax
      ≤ ∑ i ∈ Finset.range n', (v (skipIdx m i) : ℝ) :=
    sum_range_sub_le_sum_skipIdx hv m (by omega)
  have hβskip : √(2 / (π * ∑ i ∈ Finset.range n', (v (skipIdx m i) : ℝ))) ≤ β :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num)
      (mul_pos Real.pi_pos (by linarith)) (mul_le_mul_of_nonneg_left hskip Real.pi_pos.le))
  -- the index set of the other increments, and independence
  set T : Finset ℕ := (Finset.range n').image (skipIdx m) with hTdef
  have hST : Disjoint ({m} : Finset ℕ) T := by
    rw [Finset.disjoint_singleton_left, hTdef, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact skipIdx_ne m i hi
  have hind := h.indep.indepFun_finset {m} T hST h.measurable
  set Y : Ω → (T → ℝ) := fun ω i => G i ω with hYdef
  have hXY : IndepFun (G m) Y Q :=
    hind.comp (φ := fun f : ({m} : Finset ℕ) → ℝ => f ⟨m, Finset.mem_singleton_self m⟩)
      (ψ := id) (measurable_pi_apply _) measurable_id
  have hX : Measurable (G m) := h.measurable m
  have hY : Measurable Y := measurable_pi_lambda _ fun i => h.measurable i
  -- the walk of the other increments, read off `Y`
  set part : (T → ℝ) → ℕ → ℝ := fun z j => ∑ i ∈ Finset.range j,
    (if hi : skipIdx m i ∈ T then z ⟨skipIdx m i, hi⟩ else 0) with hpartdef
  have hpart : ∀ ω, ∀ j ≤ n', part (Y ω) j = walk (fun i => G (skipIdx m i)) j ω := by
    intro ω j hj
    rw [walk_apply, hpartdef]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hmem : skipIdx m i ∈ T := Finset.mem_image.2
      ⟨i, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hj), rfl⟩
    rw [dif_pos hmem]
  have hpartm : ∀ j, Measurable fun z : T → ℝ => part z j := by
    intro j
    refine Finset.measurable_sum _ fun i _ => ?_
    split_ifs with hi
    · exact measurable_pi_apply _
    · exact measurable_const
  set A : Set (ℝ × (T → ℝ)) := {p | ∀ j ≤ n', part p.2 j ≤ y + |p.1|} with hAdef
  have hA : MeasurableSet A := by
    have hrw : A = ⋂ j ∈ Set.Iic n', {p : ℝ × (T → ℝ) | part p.2 j ≤ y + |p.1|} := by
      ext p
      simp [hAdef]
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le ((hpartm j).comp measurable_snd)
        (measurable_const.add measurable_fst.abs)
  -- the survival event sits inside the preimage of `A`
  set S : Set Ω := {ω | ∀ j ≤ n, walk G j ω ≤ y} with hSdef
  have hSm : MeasurableSet S := h.measurableSet_survivalSet (fun _ => y) n
  have hsub : S ⊆ (fun ω => (G m ω, Y ω)) ⁻¹' A := by
    intro ω hω j hj
    change part (Y ω) j ≤ y + |G m ω|
    rw [hpart ω j hj]
    exact walk_skipIdx_le hω (by omega)
  -- integrability of `|G m|`
  have hint : Integrable (fun ω => |G m ω|) Q := by
    have h1 : Integrable (fun x : ℝ => |x|) (Q.map (G m)) := by
      rw [h.map_eq m]
      exact ((memLp_id_gaussianReal 1).integrable le_rfl).abs
    exact h1.comp_measurable hX
  -- the Gaussian side: `∫|x|(y + |x| + c) ≤ (y + c)√v + v`
  have hvm0 : (0 : ℝ) < (v m : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv0 m))
  have hγ1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 (v m)) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hγ2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (v m)) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hγ : Integrable (fun x : ℝ => |x| * ((y + |x| + c) * β)) (gaussianReal 0 (v m)) := by
    have heq : (fun x : ℝ => |x| * ((y + |x| + c) * β))
        = fun x => ((y + c) * β) * |x| + β * x ^ 2 := by
      funext x
      rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
      ring
    rw [heq]
    exact (hγ1.const_mul _).add (hγ2.const_mul _)
  have hgauss : ∫ x, |x| * ((y + |x| + c) * β) ∂(gaussianReal 0 (v m))
      ≤ ((y + c) * √vmax + vmax) * β := by
    have heq : (fun x : ℝ => |x| * ((y + |x| + c) * β))
        = fun x => ((y + c) * β) * |x| + β * x ^ 2 := by
      funext x
      rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
      ring
    rw [heq, integral_add (hγ1.const_mul _) (hγ2.const_mul _), integral_const_mul,
      integral_const_mul, integral_sq_gaussianReal_eq]
    have habs := integral_abs_gaussianReal_le hvm0
    have hsq : √(v m : ℝ) ≤ √vmax := Real.sqrt_le_sqrt (hv m)
    have hyc : 0 ≤ (y + c) * β := by positivity
    have h1 : (y + c) * β * ∫ x, |x| ∂(gaussianReal 0 (v m)) ≤ (y + c) * β * √vmax :=
      mul_le_mul_of_nonneg_left (le_trans habs hsq) hyc
    have h2 : β * (v m : ℝ) ≤ β * vmax := mul_le_mul_of_nonneg_left (hv m) hβ0
    nlinarith
  have hB0 : 0 ≤ ((y + c) * √vmax + vmax) * β := by positivity
  -- the lintegral chain
  set F : ℝ × (T → ℝ) → ℝ≥0∞ := A.indicator (fun p => ENNReal.ofReal |p.1|) with hFdef
  have hFm : Measurable F := (measurable_fst.abs.ennreal_ofReal).indicator hA
  rw [← ENNReal.ofReal_le_ofReal_iff hB0,
    ofReal_integral_eq_lintegral_ofReal hint.integrableOn (ae_of_all _ fun ω => abs_nonneg _)]
  calc ∫⁻ ω in S, ENNReal.ofReal |G m ω| ∂Q
      ≤ ∫⁻ ω, F (G m ω, Y ω) ∂Q := by
        rw [← lintegral_indicator hSm]
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ S
        · rw [Set.indicator_of_mem hω, hFdef,
            Set.indicator_of_mem (show (G m ω, Y ω) ∈ A from hsub hω)]
        · rw [Set.indicator_of_notMem hω]
          exact zero_le
    _ = ∫⁻ p, F p ∂(Q.map fun ω => (G m ω, Y ω)) := (lintegral_map hFm (hX.prodMk hY)).symm
    _ = ∫⁻ p, F p ∂((Q.map (G m)).prod (Q.map Y)) := by
        rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = ∫⁻ x, ∫⁻ z, F (x, z) ∂(Q.map Y) ∂(Q.map (G m)) := lintegral_prod F hFm.aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (|x| * ((y + |x| + c) * β)) ∂(Q.map (G m)) := by
        refine lintegral_mono fun x => ?_
        have hsl : MeasurableSet {z : T → ℝ | (x, z) ∈ A} := measurable_prodMk_left hA
        have hinner : ∫⁻ z, F (x, z) ∂(Q.map Y)
            = ENNReal.ofReal |x| * (Q.map Y) {z | (x, z) ∈ A} := by
          have hfun : (fun z => F (x, z))
              = {z : T → ℝ | (x, z) ∈ A}.indicator (fun _ => ENNReal.ofReal |x|) := by
            funext z
            by_cases hz : (x, z) ∈ A
            · rw [hFdef, Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ _ from hz)]
            · rw [hFdef, Set.indicator_of_notMem hz,
                Set.indicator_of_notMem (show z ∉ {z : T → ℝ | (x, z) ∈ A} from hz)]
          rw [hfun, lintegral_indicator_const hsl]
        rw [hinner]
        have hslice : (Q.map Y) {z | (x, z) ∈ A}
            = Q {ω | ∀ j ≤ n', walk (fun i => G (skipIdx m i)) j ω ≤ y + |x|} := by
          rw [Measure.map_apply hY hsl]
          congr 1
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, hAdef]
          exact forall_congr' fun j => imp_congr_right fun hj => by rw [hpart ω j hj]
        rw [hslice]
        have hbal := (h.skip m).measureReal_forall_le_le_sqrt_sum
          (fun i => hv0 (skipIdx m i)) (fun i => hv (skipIdx m i)) hc0 hc hn'1
          (by positivity : (0 : ℝ) ≤ y + |x|)
        have hbal' : Q.real {ω | ∀ j ≤ n', walk (fun i => G (skipIdx m i)) j ω ≤ y + |x|}
            ≤ (y + |x| + c) * β :=
          le_trans hbal (mul_le_mul_of_nonneg_left hβskip (by positivity))
        rw [Measure.real] at hbal'
        have hne : Q {ω | ∀ j ≤ n', walk (fun i => G (skipIdx m i)) j ω ≤ y + |x|} ≠ ⊤ :=
          measure_ne_top _ _
        calc ENNReal.ofReal |x| * Q {ω | ∀ j ≤ n', walk (fun i => G (skipIdx m i)) j ω ≤ y + |x|}
            ≤ ENNReal.ofReal |x| * ENNReal.ofReal ((y + |x| + c) * β) := by
              gcongr
              rw [← ENNReal.ofReal_toReal hne]
              exact ENNReal.ofReal_le_ofReal hbal'
          _ = ENNReal.ofReal (|x| * ((y + |x| + c) * β)) :=
              (ENNReal.ofReal_mul (abs_nonneg x)).symm
    _ = ENNReal.ofReal (∫ x, |x| * ((y + |x| + c) * β) ∂(Q.map (G m))) := by
        rw [h.map_eq m]
        exact (ofReal_integral_eq_lintegral_ofReal hγ
          (ae_of_all _ fun x => by positivity)).symm
    _ ≤ ENNReal.ofReal (((y + c) * √vmax + vmax) * β) := by
        rw [h.map_eq m]
        exact ENNReal.ofReal_le_ofReal hgauss

end WeightedBallot

section PairProduct

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
  {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {G₁ : ℕ → Ω₁ → ℝ} {G₂ : ℕ → Ω₂ → ℝ} {v₁ v₂ : ℕ → ℝ≥0}

set_option maxHeartbeats 1000000 in
-- the slice, the two ballots and the weighted ballot in one proof
/-- **The Gaussian pair ballot, decoupled, with summed variances.**  Two Gaussian walks on the
two factors of a product space, the second perturbed by the shear `H_j = ∑_{i<j} ρ_i G₁ᵢ`, with
nonzero variances at most `v₊`, `c ≥ √(πv₊/2)` and `∑_{i<n} v₁ᵢ > v₊`:
`P(G₁-walk ≤ y₁, G₂-walk + H ≤ y₂ on [0,n]) ≤ β'β((y₁ + c)(y₂ + c) + ∑|ρ_i|((y₁ + c)√v₊ + v₊))`,
`β' = √(2/(π(∑_{i<n} v₁ᵢ - v₊)))`, `β = √(2/(π∑_{i<n} v₂ᵢ))`.  Fibre by fibre in the first
factor the second walk sees a ceiling raised by `∑|ρ_i||G₁ᵢ|`, paid for by the summed-variance
ballots `RMF.IsGaussianWalk.measureReal_forall_le_le_sqrt_sum` and
`RMF.IsGaussianWalk.setIntegral_abs_survival_le_sum`. -/
theorem measureReal_prod_pairBallot_le_sum (h₁ : IsGaussianWalk G₁ v₁ Q₁)
    (h₂ : IsGaussianWalk G₂ v₂ Q₂) (hv₁0 : ∀ i, v₁ i ≠ 0) (hv₂0 : ∀ i, v₂ i ≠ 0) {vmax : ℝ}
    (hv₁ : ∀ i, (v₁ i : ℝ) ≤ vmax) (hv₂ : ∀ i, (v₂ i : ℝ) ≤ vmax) {c : ℝ} (hc0 : 0 < c)
    (hc : √(π * vmax / 2) ≤ c) {n : ℕ} (hsum : vmax < ∑ i ∈ Finset.range n, (v₁ i : ℝ))
    (ρ : ℕ → ℝ) {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    (Q₁.prod Q₂).real {ω | ∀ j ≤ n, walk G₁ j ω.1 ≤ y₁ ∧
        walk G₂ j ω.2 + ∑ i ∈ Finset.range j, ρ i * G₁ i ω.1 ≤ y₂}
      ≤ √(2 / (π * (∑ i ∈ Finset.range n, (v₁ i : ℝ) - vmax)))
          * √(2 / (π * ∑ i ∈ Finset.range n, (v₂ i : ℝ)))
        * ((y₁ + c) * (y₂ + c)
          + (∑ i ∈ Finset.range n, |ρ i|) * ((y₁ + c) * √vmax + vmax)) := by
  classical
  have hvmax0 : 0 ≤ vmax := le_trans (NNReal.coe_nonneg _) (hv₁ 0)
  have hn1 : 1 ≤ n := by have := two_le_of_lt_sum hv₁ hsum; omega
  set β' : ℝ := √(2 / (π * (∑ i ∈ Finset.range n, (v₁ i : ℝ) - vmax))) with hβ'def
  set β : ℝ := √(2 / (π * ∑ i ∈ Finset.range n, (v₂ i : ℝ))) with hβdef
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβ'0 : 0 ≤ β' := Real.sqrt_nonneg _
  -- the first walk's own ballot constant is at most `β'`
  have hβ₁β' : √(2 / (π * ∑ i ∈ Finset.range n, (v₁ i : ℝ))) ≤ β' :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num)
      (mul_pos Real.pi_pos (by linarith)) (mul_le_mul_of_nonneg_left (by linarith)
        Real.pi_pos.le))
  -- the first walk's survival set and the shear weight
  set S₁ : Set Ω₁ := {ω₁ | ∀ j ≤ n, walk G₁ j ω₁ ≤ y₁} with hS₁def
  have hS₁m : MeasurableSet S₁ := h₁.measurableSet_survivalSet (fun _ => y₁) n
  set R : Ω₁ → ℝ := fun ω₁ => ∑ i ∈ Finset.range n, |ρ i| * |G₁ i ω₁| with hRdef
  have hR0 : ∀ ω₁, 0 ≤ R ω₁ := fun ω₁ => Finset.sum_nonneg fun i _ => by positivity
  have hRm : Measurable R :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (h₁.measurable i).abs
  -- the event inside the sliced event
  set E : Set (Ω₁ × Ω₂) := {ω | ∀ j ≤ n, walk G₁ j ω.1 ≤ y₁ ∧
      walk G₂ j ω.2 + ∑ i ∈ Finset.range j, ρ i * G₁ i ω.1 ≤ y₂} with hEdef
  set E' : Set (Ω₁ × Ω₂) := {ω | ω.1 ∈ S₁ ∧ ∀ j ≤ n, walk G₂ j ω.2 ≤ y₂ + R ω.1} with hE'def
  have hshear : ∀ ω₁ : Ω₁, ∀ j ≤ n, -(∑ i ∈ Finset.range j, ρ i * G₁ i ω₁) ≤ R ω₁ := by
    intro ω₁ j hj
    calc -(∑ i ∈ Finset.range j, ρ i * G₁ i ω₁)
        ≤ |∑ i ∈ Finset.range j, ρ i * G₁ i ω₁| := neg_le_abs _
      _ ≤ ∑ i ∈ Finset.range j, |ρ i * G₁ i ω₁| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range j, |ρ i| * |G₁ i ω₁| := by simp_rw [abs_mul]
      _ ≤ R ω₁ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
          fun i _ _ => by positivity
  have hsub : E ⊆ E' := by
    intro ω hω
    refine ⟨fun j hj => (hω j hj).1, fun j hj => ?_⟩
    have h2 := (hω j hj).2
    have h3 := hshear ω.1 j hj
    linarith
  have hE'm : MeasurableSet E' := by
    have hrw : E' = (Prod.fst ⁻¹' S₁) ∩ ⋂ j ∈ Set.Iic n,
        {ω : Ω₁ × Ω₂ | walk G₂ j ω.2 ≤ y₂ + R ω.1} := by
      ext ω
      simp [hE'def]
    rw [hrw]
    exact (measurable_fst hS₁m).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le ((h₂.measurable_walk j).comp measurable_snd)
        (measurable_const.add (hRm.comp measurable_fst)))
  -- the slices of `E'`
  have hslice : ∀ ω₁ : Ω₁, Q₂ (Prod.mk ω₁ ⁻¹' E')
      ≤ S₁.indicator (fun ω₁ => ENNReal.ofReal ((y₂ + R ω₁ + c) * β)) ω₁ := by
    intro ω₁
    by_cases hω₁ : ω₁ ∈ S₁
    · rw [Set.indicator_of_mem hω₁]
      have hset : Prod.mk ω₁ ⁻¹' E' = {ω₂ | ∀ j ≤ n, walk G₂ j ω₂ ≤ y₂ + R ω₁} := by
        ext ω₂
        simp [hE'def, hω₁]
      rw [hset]
      have hbal := h₂.measureReal_forall_le_le_sqrt_sum hv₂0 hv₂ hc0 hc hn1
        (by linarith [hR0 ω₁] : (0 : ℝ) ≤ y₂ + R ω₁)
      rw [Measure.real] at hbal
      rw [← ENNReal.ofReal_toReal (measure_ne_top Q₂ _)]
      exact ENNReal.ofReal_le_ofReal hbal
    · rw [Set.indicator_of_notMem hω₁]
      have hset : Prod.mk ω₁ ⁻¹' E' = ∅ := by
        ext ω₂
        simp [hE'def, hω₁]
      rw [hset, measure_empty]
  -- the first factor
  have hint₁ : ∀ i, IntegrableOn (fun ω₁ => |G₁ i ω₁|) S₁ Q₁ := by
    intro i
    have h1 : Integrable (fun x : ℝ => |x|) (Q₁.map (G₁ i)) := by
      rw [h₁.map_eq i]
      exact ((memLp_id_gaussianReal 1).integrable le_rfl).abs
    exact (h1.comp_measurable (h₁.measurable i)).integrableOn
  have hintR : IntegrableOn R S₁ Q₁ := by
    have : IntegrableOn (fun ω₁ => ∑ i ∈ Finset.range n, |ρ i| * |G₁ i ω₁|) S₁ Q₁ :=
      integrable_finsetSum _ fun i _ => (hint₁ i).const_mul _
    exact this
  have hintg : IntegrableOn (fun ω₁ => (y₂ + R ω₁ + c) * β) S₁ Q₁ :=
    ((integrableOn_const (by simp)).add hintR |>.add (integrableOn_const (by simp))).mul_const β
  have hS₁bal := h₁.measureReal_forall_le_le_sqrt_sum hv₁0 hv₁ hc0 hc hn1 hy₁
  have hweight : ∀ i, ∫ ω₁ in S₁, |G₁ i ω₁| ∂Q₁ ≤ ((y₁ + c) * √vmax + vmax) * β' :=
    fun i => h₁.setIntegral_abs_survival_le_sum hv₁0 hv₁ hc0 hc hsum hy₁
  have hRint : ∫ ω₁ in S₁, R ω₁ ∂Q₁
      ≤ (∑ i ∈ Finset.range n, |ρ i|) * (((y₁ + c) * √vmax + vmax) * β') := by
    rw [hRdef, integral_finsetSum _ fun i _ => (hint₁ i).const_mul _, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hweight i) (abs_nonneg _)
  have hmain : ∫ ω₁ in S₁, (y₂ + R ω₁ + c) * β ∂Q₁
      ≤ β' * β * ((y₁ + c) * (y₂ + c)
          + (∑ i ∈ Finset.range n, |ρ i|) * ((y₁ + c) * √vmax + vmax)) := by
    have hsplit : ∫ ω₁ in S₁, (y₂ + R ω₁ + c) * β ∂Q₁
        = ((y₂ + c) * Q₁.real S₁ + ∫ ω₁ in S₁, R ω₁ ∂Q₁) * β := by
      rw [integral_mul_const]
      congr 1
      have heq : (fun ω₁ => y₂ + R ω₁ + c) = fun ω₁ => (y₂ + c) + R ω₁ := by
        funext ω₁; ring
      rw [heq, integral_add (integrable_const (y₂ + c)) hintR, setIntegral_const,
        smul_eq_mul, mul_comm]
    rw [hsplit]
    have hQS : Q₁.real S₁ ≤ (y₁ + c) * β' := le_trans hS₁bal
      (mul_le_mul_of_nonneg_left hβ₁β' (by linarith))
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, |ρ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hA : (y₂ + c) * Q₁.real S₁ ≤ (y₂ + c) * ((y₁ + c) * β') :=
      mul_le_mul_of_nonneg_left hQS (by linarith)
    have hB : ((y₂ + c) * Q₁.real S₁ + ∫ ω₁ in S₁, R ω₁ ∂Q₁)
        ≤ (y₂ + c) * ((y₁ + c) * β')
          + (∑ i ∈ Finset.range n, |ρ i|) * (((y₁ + c) * √vmax + vmax) * β') := by linarith
    have hC := mul_le_mul_of_nonneg_right hB hβ0
    nlinarith [hC]
  have hbound0 : 0 ≤ β' * β * ((y₁ + c) * (y₂ + c)
      + (∑ i ∈ Finset.range n, |ρ i|) * ((y₁ + c) * √vmax + vmax)) := by
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, |ρ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  -- assemble in `ℝ≥0∞`
  have hmeasE : (Q₁.prod Q₂) E ≤ ENNReal.ofReal (β' * β * ((y₁ + c) * (y₂ + c)
      + (∑ i ∈ Finset.range n, |ρ i|) * ((y₁ + c) * √vmax + vmax))) := by
    calc (Q₁.prod Q₂) E ≤ (Q₁.prod Q₂) E' := measure_mono hsub
      _ = ∫⁻ ω₁, Q₂ (Prod.mk ω₁ ⁻¹' E') ∂Q₁ := Measure.prod_apply hE'm
      _ ≤ ∫⁻ ω₁, S₁.indicator (fun ω₁ => ENNReal.ofReal ((y₂ + R ω₁ + c) * β)) ω₁ ∂Q₁ :=
          lintegral_mono hslice
      _ = ∫⁻ ω₁ in S₁, ENNReal.ofReal ((y₂ + R ω₁ + c) * β) ∂Q₁ := lintegral_indicator hS₁m _
      _ = ENNReal.ofReal (∫ ω₁ in S₁, (y₂ + R ω₁ + c) * β ∂Q₁) :=
          (ofReal_integral_eq_lintegral_ofReal hintg
            (ae_of_all _ fun ω₁ => by have := hR0 ω₁; positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hmain
  rw [Measure.real]
  calc ((Q₁.prod Q₂) E).toReal ≤ (ENNReal.ofReal (β' * β * ((y₁ + c) * (y₂ + c)
        + (∑ i ∈ Finset.range n, |ρ i|) * ((y₁ + c) * √vmax + vmax)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasE
    _ = _ := ENNReal.toReal_ofReal hbound0

end PairProduct

section FarAbstract

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

set_option maxHeartbeats 2000000 in
-- the realisation, the transfer, Lemma 4 and the pair ballot in one proof
/-- **The pair barrier from a box comparison, with summed variances.**  For walk 1's variances
`V₁ m` and the residual variances `RMF.pairResidVar (V₁ m) (V₂ m) (cv m)` positive and at most
`v₊` on the compared blocks `m < r`, and `∑_{m<r} V₁ m > v₊`: the two-point barrier has probability
at most `(1 + ε)β'β((Y₁ + c)(Y₂ + c) + K((Y₁ + c)√v₊ + v₊))`, `β' = √(2/(π(∑_{m<r} V₁ m - v₊)))`,
`β = √(2/(π∑_{m<r} pairResidVar (V₁ m) (V₂ m) (cv m)))`, `K = ∑|ρ_m|` the regression slopes.
The realisation is padded past `r` with the variance `v₊`, which enters no sum over `m < r`. -/
theorem measureReal_barrierEventPair_le_of_boxComparison_sum {P : Measure Ω}
    [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Z : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' → ℝ × ℝ} {w M M' : ℕ → ℝ} {r : ℕ} {ε ρ : ℝ}
    (hZ : ∀ m, Measurable (Z m)) (hN : ∀ m, Measurable (N m)) (hNi : iIndepFun N Q)
    {m₁ m₂ V₁ V₂ cv : ℕ → ℝ}
    (hlaw : ∀ m, m < r → Q.map (N m) = gaussianPairLaw (m₁ m) (m₂ m) (V₁ m) (V₂ m) (cv m))
    {vmax : ℝ} (hvpos₁ : ∀ m, m < r → 0 < V₁ m) (hvhi₁ : ∀ m, m < r → V₁ m ≤ vmax)
    (hvpos₂ : ∀ m, m < r → 0 < pairResidVar (V₁ m) (V₂ m) (cv m))
    (hvhi₂ : ∀ m, m < r → pairResidVar (V₁ m) (V₂ m) (cv m) ≤ vmax)
    (hsum : vmax < ∑ m ∈ Finset.range r, V₁ m)
    {c : ℝ} (hc0 : 0 < c) (hc : √(π * vmax / 2) ≤ c) (hr : 2 ≤ r)
    (hw : ∀ m, 0 < w m) (hwsum : ∀ j, j ≤ r → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hM0 : ∀ j, 0 ≤ M j)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ}
    (hM₁ : ∀ j, 1 ≤ j → j ≤ r → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hM₂ : ∀ j, 1 ≤ j → j ≤ r → -M j ≤ u₂ j ∧ v₂ j ≤ M j) (hε : 0 ≤ ε)
    (hMM : ∀ m, m < r → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsBoxComparison P Q Z N w M' r ε)
    {Y₁ Y₂ : ℝ} (hY₁0 : 0 ≤ Y₁) (hY₂0 : 0 ≤ Y₂)
    (hY₁ : ∀ j, 1 ≤ j → j ≤ r → v₁ j + ρ - ∑ m ∈ Finset.range j, m₁ m ≤ Y₁)
    (hY₂ : ∀ j, 1 ≤ j → j ≤ r → v₂ j + ρ - ∑ m ∈ Finset.range j, m₂ m ≤ Y₂) :
    (P (barrierEventPair Z r u₁ v₁ u₂ v₂)).toReal
      ≤ (1 + ε) * (√(2 / (π * (∑ m ∈ Finset.range r, V₁ m - vmax)))
          * √(2 / (π * ∑ m ∈ Finset.range r, pairResidVar (V₁ m) (V₂ m) (cv m)))
        * ((Y₁ + c) * (Y₂ + c) + (∑ m ∈ Finset.range r, |pairSlope (V₁ m) (cv m)|)
            * ((Y₁ + c) * √vmax + vmax))) := by
  classical
  -- the parameter sequences, padded past `r` with the variance `v₊`
  set m₁' : ℕ → ℝ := fun m => if m < r then m₁ m else 0 with hm₁'
  set m₂' : ℕ → ℝ := fun m => if m < r then m₂ m else 0 with hm₂'
  set V₁' : ℕ → ℝ := fun m => if m < r then V₁ m else vmax with hV₁'
  set V₂' : ℕ → ℝ := fun m => if m < r then V₂ m else vmax with hV₂'
  set cv' : ℕ → ℝ := fun m => if m < r then cv m else 0 with hcv'
  have hvmax : 0 < vmax := lt_of_lt_of_le (hvpos₁ 0 (by omega)) (hvhi₁ 0 (by omega))
  obtain ⟨Ω₁, Ω₂, mΩ₁, mΩ₂, Q₁, Q₂, G₁, Zr, G₂, W, N', hQ₁, hQ₂, hG₁, hG₂, hN'm, hN'i, hshear,
    hZG, hWG, hN'law⟩ := exists_gaussianWalk_pair_regression m₁' m₂' V₁' V₂' cv'
  haveI := hQ₁
  haveI := hQ₂
  -- the comparison, moved onto the realisation
  have hcmp' : IsBoxComparison P (Q₁.prod Q₂) Z N' w M' r ε := by
    refine hcmp.congr_law hN hN'm hNi hN'i fun m hm => ?_
    rw [hlaw m hm, hN'law m]
    simp only [hm₁', hm₂', hV₁', hV₂', hcv', hm, if_true]
  -- Lemma 4 with slack `ρ`
  have h4 := measure_barrierEventPair_le_slack hZ hN'm hw hwsum hM0 hM₁ hM₂ hε hMM hcmp'
  -- the padded variances are positive and at most `v₊` everywhere
  have hV₁'pos : ∀ i, 0 < V₁' i := fun i => by
    by_cases hi : i < r
    · simp only [hV₁', hi, if_true]; exact hvpos₁ i hi
    · simp only [hV₁', hi, if_false]; exact hvmax
  have hV₁'le : ∀ i, V₁' i ≤ vmax := fun i => by
    by_cases hi : i < r
    · simp only [hV₁', hi, if_true]; exact hvhi₁ i hi
    · simp only [hV₁', hi, if_false]; exact le_rfl
  have hres : ∀ i, ¬ i < r → pairResidVar (V₁' i) (V₂' i) (cv' i) = vmax := fun i hi => by
    simp only [hV₁', hV₂', hcv', hi, if_false, pairResidVar]
    ring
  have hR'pos : ∀ i, 0 < pairResidVar (V₁' i) (V₂' i) (cv' i) := fun i => by
    by_cases hi : i < r
    · simp only [hV₁', hV₂', hcv', hi, if_true]; exact hvpos₂ i hi
    · rw [hres i hi]; exact hvmax
  have hR'le : ∀ i, pairResidVar (V₁' i) (V₂' i) (cv' i) ≤ vmax := fun i => by
    by_cases hi : i < r
    · simp only [hV₁', hV₂', hcv', hi, if_true]; exact hvhi₂ i hi
    · rw [hres i hi]
  have hv₁0 : ∀ i, (V₁' i).toNNReal ≠ 0 := fun i => (Real.toNNReal_pos.2 (hV₁'pos i)).ne'
  have hv₂0 : ∀ i, (pairResidVar (V₁' i) (V₂' i) (cv' i)).toNNReal ≠ 0 := fun i =>
    (Real.toNNReal_pos.2 (hR'pos i)).ne'
  have hv₁ : ∀ i, (((V₁' i).toNNReal : ℝ≥0) : ℝ) ≤ vmax := fun i => by
    rw [Real.coe_toNNReal _ (hV₁'pos i).le]
    exact hV₁'le i
  have hv₂ : ∀ i, (((pairResidVar (V₁' i) (V₂' i) (cv' i)).toNNReal : ℝ≥0) : ℝ) ≤ vmax :=
    fun i => by
      rw [Real.coe_toNNReal _ (hR'pos i).le]
      exact hR'le i
  -- the sums over the compared blocks see no padding
  have hsum₁ : ∑ i ∈ Finset.range r, (((V₁' i).toNNReal : ℝ≥0) : ℝ)
      = ∑ m ∈ Finset.range r, V₁ m :=
    Finset.sum_congr rfl fun i hi => by
      rw [Real.coe_toNNReal _ (hV₁'pos i).le]
      simp only [hV₁', Finset.mem_range.1 hi, if_true]
  have hsum₂ : ∑ i ∈ Finset.range r,
        (((pairResidVar (V₁' i) (V₂' i) (cv' i)).toNNReal : ℝ≥0) : ℝ)
      = ∑ m ∈ Finset.range r, pairResidVar (V₁ m) (V₂ m) (cv m) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Real.coe_toNNReal _ (hR'pos i).le]
      simp only [hV₁', hV₂', hcv', Finset.mem_range.1 hi, if_true]
  -- the widened Gaussian barrier inside the decoupled event
  set ρs : ℕ → ℝ := fun i => pairSlope (V₁' i) (cv' i) with hρs
  have hsub : barrierEventPair N' r (fun j => u₁ j - ρ) (fun j => v₁ j + ρ)
        (fun j => u₂ j - ρ) (fun j => v₂ j + ρ)
      ⊆ {ω | ∀ j ≤ r, walk G₁ j ω.1 ≤ Y₁ ∧
          walk G₂ j ω.2 + ∑ i ∈ Finset.range j, ρs i * G₁ i ω.1 ≤ Y₂} := by
    rintro ω ⟨h₁, h₂⟩ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simp only [walk_zero, Pi.zero_apply, Finset.range_zero, Finset.sum_empty, add_zero]
      exact ⟨hY₁0, hY₂0⟩
    have hdr₁ : ∑ i ∈ Finset.range j, m₁' i = ∑ i ∈ Finset.range j, m₁ i :=
      Finset.sum_congr rfl fun i hi => by
        simp only [hm₁', show i < r by have := Finset.mem_range.1 hi; omega, if_true]
    have hdr₂ : ∑ i ∈ Finset.range j, m₂' i = ∑ i ∈ Finset.range j, m₂ i :=
      Finset.sum_congr rfl fun i hi => by
        simp only [hm₂', show i < r by have := Finset.mem_range.1 hi; omega, if_true]
    have hw₁ : walk (fun m ω => (N' m ω).1) j ω = walk G₁ j ω.1 + ∑ i ∈ Finset.range j, m₁' i := by
      rw [walk_apply, walk_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hshear i ω, hZG i ω.1]
    have hw₂ : walk (fun m ω => (N' m ω).2) j ω
        = walk G₂ j ω.2 + ∑ i ∈ Finset.range j, ρs i * G₁ i ω.1
          + ∑ i ∈ Finset.range j, m₂' i := by
      rw [walk_apply, walk_apply, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hshear i ω, hZG i ω.1, hWG i ω.2]
      simp only [hρs]
      ring
    have h₁j := (h₁ j hj1 hj).2
    have h₂j := (h₂ j hj1 hj).2
    simp only at h₁j h₂j
    rw [hw₁, hdr₁] at h₁j
    rw [hw₂, hdr₂] at h₂j
    have hy₁ := hY₁ j hj1 hj
    have hy₂ := hY₂ j hj1 hj
    exact ⟨by linarith, by linarith⟩
  have hball := measureReal_prod_pairBallot_le_sum hG₁ hG₂ hv₁0 hv₂0 hv₁ hv₂ hc0 hc
    (by rw [hsum₁]; exact hsum) ρs hY₁0 hY₂0
  have hρsum : ∑ i ∈ Finset.range r, |ρs i|
      = ∑ m ∈ Finset.range r, |pairSlope (V₁ m) (cv m)| :=
    Finset.sum_congr rfl fun i hi => by
      simp only [hρs, hV₁', hcv', Finset.mem_range.1 hi, if_true]
  rw [hρsum, hsum₁, hsum₂] at hball
  have hmono : ((Q₁.prod Q₂) (barrierEventPair N' r (fun j => u₁ j - ρ) (fun j => v₁ j + ρ)
        (fun j => u₂ j - ρ) (fun j => v₂ j + ρ))).toReal
      ≤ (Q₁.prod Q₂).real {ω | ∀ j ≤ r, walk G₁ j ω.1 ≤ Y₁ ∧
          walk G₂ j ω.2 + ∑ i ∈ Finset.range j, ρs i * G₁ i ω.1 ≤ Y₂} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  calc (P (barrierEventPair Z r u₁ v₁ u₂ v₂)).toReal
      ≤ (1 + ε) * ((Q₁.prod Q₂) (barrierEventPair N' r (fun j => u₁ j - ρ)
          (fun j => v₁ j + ρ) (fun j => u₂ j - ρ) (fun j => v₂ j + ρ))).toReal := h4
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_trans hmono hball) (by linarith)

end FarAbstract

end RMF
