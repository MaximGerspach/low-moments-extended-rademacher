/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.FreeStartAveraged
import RMF.Probability.HarperChainSlack
import RMF.Probability.BarrierLosses
import RMF.Probability.ProbabilityLemma1
import RMF.Probability.BlockComparisonSharp
import RMF.Probability.BlockComparisonPairSharp
import RMF.Probability.BlockComparison
import RMF.NumberTheory.MertensBlock
import RMF.Probability.BlockComparisonPair
import RMF.EulerProduct.JointLaplace
import RMF.Probability.Grouping
import RMF.Analysis.IteratedLog
import RMF.EulerProduct.TiltedMoments
import RMF.Probability.ChaosInterpolation
import RMF.Probability.MaximalBarrierExplicit
import RMF.Probability.RestrictedSecondMoment.Drift
import RMF.EulerProduct.TwoPoint
import Mathlib.Probability.Moments.SubGaussian
import RMF.Probability.BallotLower

/-!
# The floor loss, relative to the ballot

A union bound over the breach times pays for the floor by an absolute loss
`∑_k e^{-(Bk)²/(2kv₊)}`, the floor taken at depth `0` below the start.  Against a ballot of size
`c/√n` that is fatal once `n` is large.

Two things make the loss small **and** of the ballot's order.  A path that breaks the floor at time
`k` must still survive the ceiling from there to `n`, which costs the upper ballot
`√(2/(π(n-k)v₋))·(z - y + c)` (`RMF.IsGaussianWalk.measureReal_survival_le_sqrt`, applied to the
shifted walk); and the floor sits at depth `D` below the start, which costs `e^{-D}` by Chernoff.
For `k ≤ n/2` the first gives the `1/√n`; for `k > n/2` the Chernoff factor `e^{-(B - 2v₊)k}` is
itself `O(1/√n)`.  The result is `RMF.floorLossDepth`, of order `e^{-D}(z + 1)/√n`.

## Main results

* `RMF.IsGaussianWalk.measure_breach_survive_le`: one breach time, the ballot kept.
* `RMF.IsGaussianWalk.measure_inter_floorBreach_le_depth`: the whole floor loss.
* `RMF.IsGaussianWalk.le_measure_barrierEvent_flat_depth`: the flat-ceiling bound with it.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace RMF

section GaussianTail

/-- **The weight that dominates the lower tail.**  On `y < -u`, `1 ≤ e^{-u-y}` and
`w - y ≤ w + e^{y} + e^{-y}`; off it the indicator vanishes.  For `u ≥ 0`, `w ≥ 0`. -/
lemma indicator_Iio_sub_le_exp_weight {u w : ℝ} (hw : 0 ≤ w) (y : ℝ) :
    Set.indicator (Set.Iio (-u)) (fun y => w - y) y
      ≤ Real.exp (-u) * (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)) := by
  have hR : 0 ≤ Real.exp (-u) * (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)) := by
    positivity
  by_cases hy : y ∈ Set.Iio (-u)
  · rw [Set.indicator_of_mem hy]
    have hy' : y < -u := hy
    have h1 : 1 ≤ Real.exp (-u - y) := Real.one_le_exp (by linarith)
    have habs : -y ≤ Real.exp y + Real.exp (-y) := by
      have := Real.add_one_le_exp (-y)
      have := Real.exp_pos y
      linarith
    have e1 : Real.exp (-1 * y) = Real.exp (-y) := by ring_nf
    have e2 : Real.exp (-2 * y) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]
      ring_nf
    have e3 : Real.exp (-y) * Real.exp y = 1 := by
      rw [← Real.exp_add]
      simp
    have heq : Real.exp (-u) * (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y))
        = Real.exp (-u - y) * (w + Real.exp y + Real.exp (-y)) := by
      rw [show -u - y = -u + -y by ring, Real.exp_add, e1, e2]
      linear_combination (-Real.exp (-u)) * e3
    rw [heq]
    have hpos : 0 ≤ w + Real.exp y + Real.exp (-y) := by positivity
    calc w - y ≤ w + Real.exp y + Real.exp (-y) := by linarith
      _ ≤ Real.exp (-u - y) * (w + Real.exp y + Real.exp (-y)) := le_mul_of_one_le_left hpos h1
  · rw [Set.indicator_of_notMem hy]
    exact hR

/-- The dominating weight is integrable under any centred Gaussian. -/
lemma integrable_exp_weight_gaussianReal (W : ℝ≥0) (u w : ℝ) :
    Integrable (fun y => Real.exp (-u) * (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)))
      (gaussianReal 0 W) := by
  refine Integrable.const_mul ?_ _
  refine Integrable.add (Integrable.add ?_ (integrable_const _)) ?_
  · exact (integrable_exp_mul_gaussianReal (μ := 0) (v := W) (-1)).const_mul w
  · exact integrable_exp_mul_gaussianReal (μ := 0) (v := W) (-2)

/-- **The dominating weight integrates to at most `e^{-u}(w + 2)e^{2W}`**: its three exponentials
are the Gaussian moment generating function at `-1`, `0` and `-2`. -/
lemma integral_exp_weight_gaussianReal_le (W : ℝ≥0) (u : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ∫ y, Real.exp (-u) * (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)) ∂(gaussianReal 0 W)
      ≤ Real.exp (-u) * (w + 2) * Real.exp (2 * (W : ℝ)) := by
  have hm1 : ∫ y, Real.exp (-1 * y) ∂(gaussianReal 0 W) = Real.exp ((W : ℝ) / 2) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := W)) (-1)
    rw [mgf] at h
    simp only [id] at h
    rw [h]
    congr 1
    ring
  have hm2 : ∫ y, Real.exp (-2 * y) ∂(gaussianReal 0 W) = Real.exp (2 * (W : ℝ)) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := W)) (-2)
    rw [mgf] at h
    simp only [id] at h
    rw [h]
    congr 1
    ring
  have hi1 := (integrable_exp_mul_gaussianReal (μ := 0) (v := W) (-1)).const_mul w
  have hi2 := integrable_exp_mul_gaussianReal (μ := 0) (v := W) (-2)
  have hint : ∫ y, Real.exp (-u) * (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y))
        ∂(gaussianReal 0 W)
      = Real.exp (-u) * (w * Real.exp ((W : ℝ) / 2) + 1 + Real.exp (2 * (W : ℝ))) := by
    have hs1 : ∫ y, (w * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)) ∂(gaussianReal 0 W)
        = (∫ y, (w * Real.exp (-1 * y) + 1) ∂(gaussianReal 0 W))
          + ∫ y, Real.exp (-2 * y) ∂(gaussianReal 0 W) :=
      integral_add (hi1.add (integrable_const _)) hi2
    have hs2 : ∫ y, (w * Real.exp (-1 * y) + 1) ∂(gaussianReal 0 W)
        = (∫ y, w * Real.exp (-1 * y) ∂(gaussianReal 0 W))
          + ∫ _y, (1 : ℝ) ∂(gaussianReal 0 W) :=
      integral_add hi1 (integrable_const _)
    rw [integral_const_mul, hs1, hs2, integral_const_mul, hm1, hm2]
    simp
  rw [hint]
  have hW0 : (0 : ℝ) ≤ (W : ℝ) := W.coe_nonneg
  have hA : Real.exp ((W : ℝ) / 2) ≤ Real.exp (2 * (W : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have hB : (1 : ℝ) ≤ Real.exp (2 * (W : ℝ)) := Real.one_le_exp (by linarith)
  have hE : 0 < Real.exp (-u) := Real.exp_pos _
  have hin : w * Real.exp ((W : ℝ) / 2) + 1 + Real.exp (2 * (W : ℝ))
      ≤ (w + 2) * Real.exp (2 * (W : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hA hw
    nlinarith
  calc Real.exp (-u) * (w * Real.exp ((W : ℝ) / 2) + 1 + Real.exp (2 * (W : ℝ)))
      ≤ Real.exp (-u) * ((w + 2) * Real.exp (2 * (W : ℝ))) :=
        mul_le_mul_of_nonneg_left hin hE.le
    _ = Real.exp (-u) * (w + 2) * Real.exp (2 * (W : ℝ)) := by ring

end GaussianTail

/-! ### One breach time -/

section BreachTime

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}

/-- The walk's variance up to time `k` is at most `k v₊`. -/
lemma sum_range_var_le {vmax : ℝ} (hvmax : ∀ i, (v i : ℝ) ≤ vmax) (k : ℕ) :
    ((∑ m ∈ Finset.range k, v m : ℝ≥0) : ℝ) ≤ (k : ℝ) * vmax := by
  push_cast
  calc ∑ m ∈ Finset.range k, (v m : ℝ) ≤ ∑ _m ∈ Finset.range k, vmax :=
        Finset.sum_le_sum fun m _ => hvmax m
    _ = (k : ℝ) * vmax := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `exp(t·S_k)` is integrable: `S_k` is centred Gaussian. -/
lemma IsGaussianWalk.integrable_exp_mul_walk (h : IsGaussianWalk G v Q) (k : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * walk G k ω)) Q := by
  have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := ∑ m ∈ Finset.range k, v m) t
  rw [← h.map_walk k] at h1
  exact (integrable_map_measure (by fun_prop) (h.measurable_walk k).aemeasurable).1 h1

/-- **Chernoff for the walk.**  `P(S_k < -u) ≤ e^{-u}e^{2kv₊}` — the exponent `2` rather than the
sharp `1/2`, to match `RMF.integral_exp_weight_gaussianReal_le`. -/
lemma IsGaussianWalk.measure_walk_lt_le (h : IsGaussianWalk G v Q) {vmax : ℝ}
    (hvmax : ∀ i, (v i : ℝ) ≤ vmax) (k : ℕ) (u : ℝ) :
    Q {ω | walk G k ω < -u}
      ≤ ENNReal.ofReal (Real.exp (-u) * Real.exp (2 * ((k : ℝ) * vmax))) := by
  set W : ℝ≥0 := ∑ m ∈ Finset.range k, v m with hWdef
  have hch := measure_le_le_exp_mul_mgf (μ := Q) (X := walk G k) (t := -1) (-u) (by norm_num)
    (h.integrable_exp_mul_walk k (-1))
  rw [mgf_gaussianReal (h.map_walk k)] at hch
  have hsub : {ω | walk G k ω < -u} ⊆ {ω | walk G k ω ≤ -u} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact hω.le
  have hW : (W : ℝ) ≤ (k : ℝ) * vmax := sum_range_var_le hvmax k
  have hW0 : (0 : ℝ) ≤ (W : ℝ) := W.coe_nonneg
  have hexp : Real.exp (-(-1) * (-u)) * Real.exp (0 * (-1) + (W : ℝ) * (-1) ^ 2 / 2)
      ≤ Real.exp (-u) * Real.exp (2 * ((k : ℝ) * vmax)) := by
    have e1 : Real.exp (-(-1) * (-u)) = Real.exp (-u) := by ring_nf
    rw [e1]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    nlinarith
  calc Q {ω | walk G k ω < -u} ≤ Q {ω | walk G k ω ≤ -u} := measure_mono hsub
    _ = ENNReal.ofReal (Q.real {ω | walk G k ω ≤ -u}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-u) * Real.exp (2 * ((k : ℝ) * vmax))) :=
        ENNReal.ofReal_le_ofReal (le_trans hch hexp)

set_option maxHeartbeats 400000 in
-- the fibre decomposition, the shifted ballot and the Gaussian integral in one proof
/-- **One breach time, the ballot kept.**  For `1 ≤ k`, `2k ≤ n`, `z ≥ 0` and `u ≥ 0`, the paths
below `-u` at time `k` that stay below `z` on `[k, n]` have mass at most
`√(4/(πnv₋))·e^{-u}(z + √(πv₊/2) + 2)e^{2kv₊}`.  Given `S_k = y`, the shifted walk must stay below
`z - y` for `n - k ≥ n/2` steps (`RMF.IsGaussianWalk.measureReal_survival_le_sqrt`), and the
weight `z + c - y` integrates against the law of `S_k` by
`RMF.integral_exp_weight_gaussianReal_le`. -/
theorem IsGaussianWalk.measure_breach_survive_le (h : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {k n : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    {z u : ℝ} (hz : 0 ≤ z) (hu : 0 ≤ u) :
    Q {ω | walk G k ω < -u ∧ ∀ j, k ≤ j → j ≤ n → walk G j ω ≤ z}
      ≤ ENNReal.ofReal (√(4 / (π * ((n : ℝ) * vmin)))
        * (Real.exp (-u) * (z + √(π * vmax / 2) + 2) * Real.exp (2 * ((k : ℝ) * vmax)))) := by
  classical
  set c : ℝ := √(π * vmax / 2) with hcdef
  set K : ℝ := √(4 / (π * ((n : ℝ) * vmin))) with hKdef
  have hvmin := hv.pos
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hv.lo 0) (hv.hi 0))
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set Φ : Ω → ℝ := walk G k with hΦdef
  set Ψ : Ω → (ℕ → ℝ) := fun ω => blockSums k n fun i => G i ω with hΨdef
  have hΦ : Measurable Φ := h.measurable_walk k
  have hΨ : Measurable Ψ :=
    (measurable_blockSums k n).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hind : IndepFun Φ Ψ Q := by
    have h0 := (h.indepFun_prefixSums_blockSums k n).comp (measurable_pi_apply k) measurable_id
    have hrw : ((fun f : ℕ → ℝ => f k) ∘ fun ω => prefixSums k fun i => G i ω) = Φ := by
      funext ω
      simp only [Function.comp, hΦdef]
      exact prefixSums_comp G le_rfl ω
    rw [hrw] at h0
    exact h0
  set S : Set (ℝ × (ℕ → ℝ)) := {p | p.1 < -u ∧ ∀ j, k ≤ j → j ≤ n → p.1 + p.2 j ≤ z}
    with hSdef
  have hS : MeasurableSet S := by
    have hrw : S = (Prod.fst ⁻¹' Set.Iio (-u))
        ∩ ⋂ j ∈ Set.Icc k n, {p : ℝ × (ℕ → ℝ) | p.1 + p.2 j ≤ z} := by
      ext p
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio,
        Set.mem_iInter, Set.mem_Icc]
      exact and_congr_right fun _ => ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
    rw [hrw]
    refine (measurable_fst measurableSet_Iio).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_)
    exact measurableSet_le (measurable_fst.add ((measurable_pi_apply j).comp measurable_snd))
      measurable_const
  have hset : {ω | walk G k ω < -u ∧ ∀ j, k ≤ j → j ≤ n → walk G j ω ≤ z}
      = (fun ω => (Φ ω, Ψ ω)) ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hSdef, hΦdef, hΨdef]
    refine and_congr_right fun _ => forall_congr' fun j => forall_congr' fun hkj =>
      forall_congr' fun hjn => ?_
    rw [blockSums_comp G hkj hjn ω]
    constructor <;> intro hh <;> linarith
  rw [hset, measure_preimage_prod_eq_lintegral hΦ hΨ hind hS, h.map_walk k]
  set W : ℝ≥0 := ∑ m ∈ Finset.range k, v m with hWdef
  -- the fibre bound
  have hfib : ∀ y, (Q.map Ψ) (Prod.mk y ⁻¹' S)
      ≤ ENNReal.ofReal (K * (Real.exp (-u)
          * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)))) := by
    intro y
    by_cases hy : y < -u
    · have hslice : MeasurableSet (Prod.mk y ⁻¹' S) := measurable_prodMk_left hS
      rw [Measure.map_apply hΨ hslice]
      have hpre : Ψ ⁻¹' (Prod.mk y ⁻¹' S)
          = survivalSet (fun m => G (m + k)) (fun _ => z - y) (n - k) := by
        ext ω
        simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, survivalSet, hΨdef]
        constructor
        · rintro ⟨-, hh⟩ j hj
          have h1 := hh (k + j) (by omega) (by omega)
          rw [blockSums_comp G (by omega) (by omega) ω] at h1
          rw [walk_shift]
          linarith
        · intro hh
          refine ⟨hy, fun j hkj hjn => ?_⟩
          have h1 := hh (j - k) (by omega)
          rw [walk_shift, show k + (j - k) = j by omega] at h1
          rw [blockSums_comp G hkj hjn ω]
          linarith
      rw [hpre]
      have hvne : ∀ j, v (j + k) ≠ 0 := by
        intro j h0
        have h1 := hv.lo (j + k)
        rw [h0] at h1
        simp only [NNReal.coe_zero] at h1
        linarith
      have hcj : ∀ j, √(π * (v (j + k) : ℝ) / 2) ≤ c := by
        intro j
        refine Real.sqrt_le_sqrt ?_
        have h1 := hv.hi (j + k)
        have hπ := Real.pi_pos
        have : π * (v (j + k) : ℝ) ≤ π * vmax := mul_le_mul_of_nonneg_left h1 hπ.le
        linarith
      have hsurv := (h.shift k).measureReal_survival_le_sqrt (g := fun _ => z - y) (Y := z - y)
        (by linarith) (n := n - k) (by omega) (fun _ _ => le_rfl) hvne hc0 hcj
      -- the variance of the shifted walk is at least `(n/2)v₋`
      have hsum : ((n : ℝ) / 2) * vmin
          ≤ ∑ i ∈ Finset.range (n - k), ((v (i + k) : ℝ≥0) : ℝ) := by
        have hle : ∑ _i ∈ Finset.range (n - k), vmin
            ≤ ∑ i ∈ Finset.range (n - k), ((v (i + k) : ℝ≥0) : ℝ) :=
          Finset.sum_le_sum fun i _ => hv.lo (i + k)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
        have hnk : (n : ℝ) / 2 ≤ ((n - k : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          have : (2 * k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
          linarith
        nlinarith
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        linarith
      have hSpos : 0 < ∑ i ∈ Finset.range (n - k), ((v (i + k) : ℝ≥0) : ℝ) :=
        lt_of_lt_of_le (by positivity) hsum
      have hroot : √(2 / (π * ∑ i ∈ Finset.range (n - k), ((v (i + k) : ℝ≥0) : ℝ))) ≤ K := by
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hπ := Real.pi_pos
        nlinarith
      have hw0 : 0 ≤ z + c := by linarith
      have hpt := indicator_Iio_sub_le_exp_weight (u := u) hw0 y
      rw [Set.indicator_of_mem (show y ∈ Set.Iio (-u) from hy)] at hpt
      calc Q (survivalSet (fun m => G (m + k)) (fun _ => z - y) (n - k))
          = ENNReal.ofReal (Q.real (survivalSet (fun m => G (m + k)) (fun _ => z - y) (n - k))) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (K * (Real.exp (-u)
              * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)))) := by
            refine ENNReal.ofReal_le_ofReal (le_trans hsurv ?_)
            have hzy : 0 ≤ z - y + c := by linarith
            calc (z - y + c) * √(2 / (π * ∑ i ∈ Finset.range (n - k),
                  ((v (i + k) : ℝ≥0) : ℝ)))
                ≤ (z - y + c) * K := mul_le_mul_of_nonneg_left hroot hzy
              _ = K * (z + c - y) := by ring
              _ ≤ K * (Real.exp (-u)
                  * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y))) :=
                  mul_le_mul_of_nonneg_left hpt hK0
    · have hempty : Prod.mk y ⁻¹' S = ∅ := by
        ext f
        simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hh => hy hh.1
      rw [hempty, measure_empty]
      exact bot_le
  have hint : Integrable (fun y => K * (Real.exp (-u)
      * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)))) (gaussianReal 0 W) :=
    (integrable_exp_weight_gaussianReal W u (z + c)).const_mul K
  have hnn : 0 ≤ᵐ[gaussianReal 0 W] fun y => K * (Real.exp (-u)
      * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y))) :=
    Filter.Eventually.of_forall fun y => by
      have : 0 ≤ z + c := by linarith
      positivity
  have hW : (W : ℝ) ≤ (k : ℝ) * vmax := sum_range_var_le hv.hi k
  have hI := integral_exp_weight_gaussianReal_le W u (w := z + c) (by linarith)
  calc ∫⁻ y, (Q.map Ψ) (Prod.mk y ⁻¹' S) ∂(gaussianReal 0 W)
      ≤ ∫⁻ y, ENNReal.ofReal (K * (Real.exp (-u)
          * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y)))) ∂(gaussianReal 0 W) :=
        lintegral_mono hfib
    _ = ENNReal.ofReal (∫ y, K * (Real.exp (-u)
          * ((z + c) * Real.exp (-1 * y) + 1 + Real.exp (-2 * y))) ∂(gaussianReal 0 W)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ ≤ ENNReal.ofReal (K * (Real.exp (-u) * (z + c + 2) * Real.exp (2 * ((k : ℝ) * vmax)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        refine mul_le_mul_of_nonneg_left (le_trans hI ?_) hK0
        have hzc : 0 ≤ z + c + 2 := by linarith
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
          (mul_nonneg (Real.exp_pos _).le hzc)

end BreachTime

/-! ### The floor loss at depth `D` -/

/-- **The floor loss at depth `D`**, relative to the ballot:
`e^{-D}(z⁺ + √(πv₊/2) + 2)·max(√(4/(πv₋)), √(2/(e(B - 2v₊))))/(√n(e^{(B-2v₊)/2} - 1))`, for a floor
below `-D - Bi` and a flat ceiling `z` (`RMF.IsGaussianWalk.measure_inter_floorBreach_le_depth`). -/
noncomputable def floorLossDepth (D B vmin vmax : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  Real.exp (-D) * (max z 0 + √(π * vmax / 2) + 2)
    * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
    / (√(n : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1))

lemma floorLossDepth_nonneg {D B vmin vmax : ℝ} (hB : 2 * vmax < B) (n : ℕ) (z : ℝ) :
    0 ≤ floorLossDepth D B vmin vmax n z := by
  have hz : 0 ≤ max z 0 := le_max_right _ _
  have hden : 0 ≤ √(n : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1) := by
    have : 1 ≤ Real.exp ((B - 2 * vmax) / 2) := Real.one_le_exp (by linarith)
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  unfold floorLossDepth
  refine div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))
    (le_trans (Real.sqrt_nonneg _) (le_max_left _ _))) hden

/-- `√n·e^{-αn/4} ≤ √(2/(eα))`: `ye^{-y} ≤ e^{-1}` at `y = αn/2`. -/
lemma exp_neg_mul_div_four_le {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(α * (n : ℝ) / 4)) ≤ √(2 / (Real.exp 1 * α)) / √(n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  rw [le_div_iff₀ hsq]
  have hy' : α * (n : ℝ) / 2 * Real.exp 1 ≤ Real.exp (α * (n : ℝ) / 2) := by
    have h1 := Real.add_one_le_exp (α * (n : ℝ) / 2 - 1)
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos 1)] at h1
    linarith
  have key : Real.exp (-(α * (n : ℝ) / 2)) * (n : ℝ) ≤ 2 / (Real.exp 1 * α) := by
    rw [le_div_iff₀ (by positivity)]
    have hE := (Real.exp_pos (-(α * (n : ℝ) / 2))).le
    calc Real.exp (-(α * (n : ℝ) / 2)) * (n : ℝ) * (Real.exp 1 * α)
        = 2 * (Real.exp (-(α * (n : ℝ) / 2)) * (α * (n : ℝ) / 2 * Real.exp 1)) := by ring
      _ ≤ 2 * (Real.exp (-(α * (n : ℝ) / 2)) * Real.exp (α * (n : ℝ) / 2)) := by
          have := mul_le_mul_of_nonneg_left hy' hE
          linarith
      _ = 2 := by rw [← Real.exp_add]; simp
  have hsplit : Real.exp (-(α * (n : ℝ) / 4)) * √(n : ℝ)
      = √(Real.exp (-(α * (n : ℝ) / 2)) * (n : ℝ)) := by
    have he : Real.exp (-(α * (n : ℝ) / 2)) = Real.exp (-(α * (n : ℝ) / 4)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
  rw [hsplit]
  exact Real.sqrt_le_sqrt key

section FloorLossDepth

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}

set_option maxHeartbeats 400000 in
-- the cover by breach times, the two regimes and the geometric sum in one proof
/-- **The floor loss at depth `D`.**  For a floor below `-D - Bi` with `B > 2v₊`, the paths that
stay below `z` on `[0, n]` and break the floor somewhere have mass at most
`RMF.floorLossDepth D B v₋ v₊ n z`.  By breach time `k`: the ballot kept for `2k ≤ n`
(`RMF.IsGaussianWalk.measure_breach_survive_le`), Chernoff alone for `2k > n`
(`RMF.IsGaussianWalk.measure_walk_lt_le`, with `e^{-(B-2v₊)n/4} = O(1/√n)`); both terms are at most
`e^{-D}(z + c + 2)(M/√n)e^{-(B-2v₊)k/2}`, and the geometric sum does the rest. -/
theorem IsGaussianWalk.measure_inter_floorBreach_le_depth (h : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n : ℕ} (hn : 1 ≤ n) (z : ℝ)
    {lo : ℕ → ℝ} {D B : ℝ} (hD : 0 ≤ D) (hB : 2 * vmax < B)
    (hlo : ∀ i : ℕ, 1 ≤ i → lo i ≤ -D - B * (i : ℝ)) :
    Q ({ω | ∀ j ≤ n, walk G j ω ≤ z} ∩ floorBreach G n lo)
      ≤ ENNReal.ofReal (floorLossDepth D B vmin vmax n z) := by
  classical
  rcases lt_or_ge z 0 with hz | hz
  · -- no path stays below a negative ceiling: `S_0 = 0`
    have hempty : {ω | ∀ j ≤ n, walk G j ω ≤ z} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
      exact ⟨0, Nat.zero_le n, by rw [walk_zero]; simpa using hz⟩
    rw [hempty, Set.empty_inter, measure_empty]
    exact bot_le
  set α : ℝ := B - 2 * vmax with hαdef
  have hα : 0 < α := by linarith
  set c : ℝ := √(π * vmax / 2) with hcdef
  set M : ℝ := max √(4 / (π * vmin)) √(2 / (Real.exp 1 * α)) with hMdef
  have hvmin := hv.pos
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hMn : 0 ≤ M / √(n : ℝ) := div_nonneg hM0 hsqn.le
  have hzc : (1 : ℝ) ≤ z + c + 2 := by linarith
  set r : ℝ := Real.exp (-(α / 2)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  set T : ℕ → ℝ := fun k => Real.exp (-D) * (z + c + 2) * (M / √(n : ℝ)) * r ^ k with hTdef
  have hTnn : ∀ k, 0 ≤ T k := fun k => by
    simp only [hTdef]
    have : 0 ≤ z + c + 2 := by linarith
    positivity
  -- the cover by breach times
  set E : ℕ → Set Ω := fun k => {ω | walk G k ω < -(D + B * (k : ℝ))
    ∧ ∀ j, k ≤ j → j ≤ n → walk G j ω ≤ z} with hEdef
  have hcover : {ω | ∀ j ≤ n, walk G j ω ≤ z} ∩ floorBreach G n lo
      ⊆ ⋃ k ∈ Finset.Icc 1 n, E k := by
    rintro ω ⟨hA, j, hj1, hjn, hlt⟩
    refine Set.mem_biUnion (Finset.mem_Icc.2 ⟨hj1, hjn⟩) ⟨?_, fun i _ hin => hA i hin⟩
    have := hlo j hj1
    linarith
  have hEk : ∀ k ∈ Finset.Icc 1 n, Q (E k) ≤ ENNReal.ofReal (T k) := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hk
    have hk0 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hBnn : 0 ≤ B := by
      have := hv.hi 0
      have := (v 0).coe_nonneg
      linarith
    have hu : 0 ≤ D + B * (k : ℝ) := by positivity
    have hpow : r ^ k = Real.exp (-(α * (k : ℝ) / 2)) := by
      rw [hrdef, ← Real.exp_nat_mul]
      ring_nf
    have hdecay : Real.exp (-(D + B * (k : ℝ))) * Real.exp (2 * ((k : ℝ) * vmax))
        = Real.exp (-D) * (Real.exp (-(α * (k : ℝ) / 2)) * Real.exp (-(α * (k : ℝ) / 2))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hαdef]
      congr 1
      ring
    have hP : 0 ≤ Real.exp (-D) * (Real.exp (-(α * (k : ℝ) / 2)) * (M / √(n : ℝ))) := by
      positivity
    have hlast : Real.exp (-D) * (Real.exp (-(α * (k : ℝ) / 2)) * (M / √(n : ℝ))) ≤ T k := by
      simp only [hTdef]
      rw [hpow]
      nlinarith [mul_le_mul_of_nonneg_left hzc hP]
    rcases le_or_gt (2 * k) n with h2k | h2k
    · -- the ballot regime: `√(4/(πnv₋)) ≤ M/√n`, and `e^{-αk} ≤ e^{-αk/2}`
      have hb := h.measure_breach_survive_le hv hk1 h2k (u := D + B * (k : ℝ)) hz hu
      refine le_trans hb (ENNReal.ofReal_le_ofReal ?_)
      have hK : √(4 / (π * ((n : ℝ) * vmin))) ≤ M / √(n : ℝ) := by
        have heq : √(4 / (π * ((n : ℝ) * vmin))) = √(4 / (π * vmin)) / √(n : ℝ) := by
          rw [show 4 / (π * ((n : ℝ) * vmin)) = 4 / (π * vmin) / (n : ℝ) by
            field_simp]
          exact Real.sqrt_div' _ hn0.le
        rw [heq]
        exact div_le_div_of_nonneg_right (le_max_left _ _) hsqn.le
      have he1 : Real.exp (-(α * (k : ℝ) / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ α * (k : ℝ) := by positivity
        linarith)
      have hE0 : 0 ≤ Real.exp (-(α * (k : ℝ) / 2)) := (Real.exp_pos _).le
      have hK0 : 0 ≤ √(4 / (π * ((n : ℝ) * vmin))) := Real.sqrt_nonneg _
      have hz0 : 0 ≤ z + √(π * vmax / 2) + 2 := by linarith
      calc √(4 / (π * ((n : ℝ) * vmin))) * (Real.exp (-(D + B * (k : ℝ)))
            * (z + √(π * vmax / 2) + 2) * Real.exp (2 * ((k : ℝ) * vmax)))
          = √(4 / (π * ((n : ℝ) * vmin))) * (z + √(π * vmax / 2) + 2)
            * (Real.exp (-(D + B * (k : ℝ))) * Real.exp (2 * ((k : ℝ) * vmax))) := by ring
        _ = √(4 / (π * ((n : ℝ) * vmin))) * (z + √(π * vmax / 2) + 2)
            * (Real.exp (-D) * (Real.exp (-(α * (k : ℝ) / 2))
              * Real.exp (-(α * (k : ℝ) / 2)))) := by rw [hdecay]
        _ ≤ (M / √(n : ℝ)) * (z + √(π * vmax / 2) + 2)
            * (Real.exp (-D) * (Real.exp (-(α * (k : ℝ) / 2)) * 1)) := by
            gcongr
        _ = Real.exp (-D) * (z + c + 2) * (M / √(n : ℝ)) * Real.exp (-(α * (k : ℝ) / 2)) := by
            rw [hcdef]
            ring
        _ = T k := by
            simp only [hTdef]
            rw [hpow]
    · -- the Chernoff regime, `2k > n`: `e^{-αk/2} ≤ e^{-αn/4} ≤ M/√n`
      have hsub : E k ⊆ {ω | walk G k ω < -(D + B * (k : ℝ))} := fun ω hω => hω.1
      refine le_trans (measure_mono hsub)
        (le_trans (h.measure_walk_lt_le hv.hi k _) (ENNReal.ofReal_le_ofReal ?_))
      have h4 : Real.exp (-(α * (k : ℝ) / 2)) ≤ Real.exp (-(α * (n : ℝ) / 4)) :=
        Real.exp_le_exp.2 (by
          have : (n : ℝ) < 2 * (k : ℝ) := by exact_mod_cast h2k
          nlinarith)
      have h5 := exp_neg_mul_div_four_le hα hn
      have hM' : √(2 / (Real.exp 1 * α)) / √(n : ℝ) ≤ M / √(n : ℝ) :=
        div_le_div_of_nonneg_right (le_max_right _ _) hsqn.le
      have h45 : Real.exp (-(α * (k : ℝ) / 2)) ≤ M / √(n : ℝ) :=
        le_trans h4 (le_trans h5 hM')
      rw [hdecay]
      refine le_trans ?_ hlast
      have hE0 : 0 ≤ Real.exp (-(α * (k : ℝ) / 2)) := (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h45 hE0) (Real.exp_pos _).le
  -- the geometric sum
  have hgeom : ∑ k ∈ Finset.Icc 1 n, T k ≤ floorLossDepth D B vmin vmax n z := by
    have hsum : ∑ k ∈ Finset.Icc 1 n, T k
        = Real.exp (-D) * (z + c + 2) * (M / √(n : ℝ)) * ∑ k ∈ Finset.Ico 1 (n + 1), r ^ k := by
      rw [Finset.Ico_add_one_right_eq_Icc, Finset.mul_sum]
    have hg := geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) hr0 hr1
    have hr : r ^ 1 / (1 - r) = 1 / (Real.exp (α / 2) - 1) := by
      have hE : Real.exp (α / 2) * r = 1 := by
        rw [hrdef, ← Real.exp_add]
        simp
      have h1 : 0 < 1 - r := by linarith
      have h2 : 0 < Real.exp (α / 2) - 1 := by
        have : 1 < Real.exp (α / 2) := Real.one_lt_exp_iff.2 (by linarith)
        linarith
      rw [pow_one, div_eq_div_iff h1.ne' h2.ne']
      nlinarith
    rw [hr] at hg
    have hpre : 0 ≤ Real.exp (-D) * (z + c + 2) * (M / √(n : ℝ)) := by
      have : 0 ≤ z + c + 2 := by linarith
      positivity
    rw [hsum]
    refine le_trans (mul_le_mul_of_nonneg_left hg hpre) (le_of_eq ?_)
    rw [floorLossDepth, max_eq_left hz, ← hαdef, ← hcdef, ← hMdef]
    field_simp
  calc Q ({ω | ∀ j ≤ n, walk G j ω ≤ z} ∩ floorBreach G n lo)
      ≤ Q (⋃ k ∈ Finset.Icc 1 n, E k) := measure_mono hcover
    _ ≤ ∑ k ∈ Finset.Icc 1 n, Q (E k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ENNReal.ofReal (T k) := Finset.sum_le_sum hEk
    _ = ENNReal.ofReal (∑ k ∈ Finset.Icc 1 n, T k) :=
        (ENNReal.ofReal_sum_of_nonneg fun k _ => hTnn k).symm
    _ ≤ ENNReal.ofReal (floorLossDepth D B vmin vmax n z) := ENNReal.ofReal_le_ofReal hgeom

/-- **A flat ceiling and a floor at depth `D`, from below.**  For a floor `lo i ≤ -D - Bi` with
`B > 2v₊` and a flat ceiling `z`, the barrier event has probability at least the ballot
`ballotLinear v₋ v₊ n z` less the floor loss `RMF.floorLossDepth` of
`RMF.IsGaussianWalk.measure_inter_floorBreach_le_depth`: of the ballot's order `1/√n`, and small
by `e^{-D}`. -/
theorem IsGaussianWalk.le_measure_barrierEvent_flat_depth (h : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n : ℕ} (hn : 1 ≤ n) (z : ℝ)
    {lo : ℕ → ℝ} {D B : ℝ} (hD : 0 ≤ D) (hB : 2 * vmax < B)
    (hlo : ∀ i : ℕ, 1 ≤ i → lo i ≤ -D - B * (i : ℝ)) :
    ballotLinear vmin vmax n z - floorLossDepth D B vmin vmax n z
      ≤ (Q (barrierEvent G n lo (fun _ => z))).toReal := by
  set A : Set Ω := {ω | ∀ j ≤ n, walk G j ω ≤ z} with hAdef
  have hdec := measure_le_barrierEvent_add_breaches (μ := Q) G n lo (fun _ => z) A
  have hceil : Q (A ∩ ceilBreach G n (fun _ => z)) = 0 := by
    have hempty : A ∩ ceilBreach G n (fun _ => z) = ∅ := by
      ext ω
      simp only [hAdef, ceilBreach, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and, not_exists]
      intro hA j hj1 hjn hlt
      exact absurd (hA j hjn) (not_le.2 hlt)
    rw [hempty, measure_empty]
  have hfloor : Q (A ∩ floorBreach G n lo)
      ≤ ENNReal.ofReal (floorLossDepth D B vmin vmax n z) :=
    h.measure_inter_floorBreach_le_depth hv hn z hD hB hlo
  have hA : ballotLinear vmin vmax n z ≤ (Q A).toReal := by
    have h1 := h.explicit_le_barrierProb_posPart hv z hn
    rw [barrierProb] at h1
    exact le_trans (ballotLinear_le_ballotLower hv.pos hn z) h1
  have hfin1 : Q (barrierEvent G n lo fun _ => z) ≠ ⊤ := measure_ne_top _ _
  have hL0 := floorLossDepth_nonneg (D := D) (vmin := vmin) hB n z
  have hle : (Q A).toReal ≤ (Q (barrierEvent G n lo fun _ => z)).toReal
      + floorLossDepth D B vmin vmax n z := by
    have h2 : Q A ≤ Q (barrierEvent G n lo fun _ => z)
        + ENNReal.ofReal (floorLossDepth D B vmin vmax n z) := by
      calc Q A ≤ Q (barrierEvent G n lo fun _ => z) + Q (A ∩ ceilBreach G n fun _ => z)
            + Q (A ∩ floorBreach G n lo) := hdec
        _ ≤ Q (barrierEvent G n lo fun _ => z) + 0
            + ENNReal.ofReal (floorLossDepth D B vmin vmax n z) := by
            rw [hceil]
            gcongr
        _ = _ := by rw [add_zero]
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, ENNReal.ofReal_ne_top⟩) h2
    rwa [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hL0] at h3
  linarith

end FloorLossDepth

end RMF
