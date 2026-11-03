/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherRestrictedSecondMoment.Ranges
import RMF.Probability.RestrictedSecondMoment.Assembly

/-!
# The assembly of Key Proposition 5's ranges, for the Rademacher function

The Rademacher counterpart of `RMF/Probability/RestrictedSecondMoment/Assembly.lean`: the ranges
at Harper's data, the display's hypotheses discharged one by one, the ranges' shapes reconciled,
and `RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges_rademacher`, the second
moment of the restricted chaos from the four range bounds.  The arithmetic about Harper's data (the
split index, the block count, the envelope, the `Λ` bookkeeping) is imported from the Steinhaus
file.  What changes is what changes in `Ranges.lean`:

* the statements carry Harper's height restriction `t ∈ [1/3, 1/2]` (§5.3), because the Rademacher
  pair statistics see the sum frequency as well as the difference;
* the oscillation hypotheses at the two doubled heights travel with them, and `Kd` sits outside
  the existential;
* the envelope condition carries `36` where the Steinhaus one carries `13`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The height integral in the form the ranges produce

The ranges deliver set integrals over `L t ∩ L u`; the height integral wants a barrier probability
times a free moment.  `RMF.IsRademacherRMF.setIntegral_normSq_mul_normSq_eq` is an *equality*, not
an estimate, so nothing is lost in the translation. -/

/-- **The height integral in the form the ranges produce**, for the Rademacher function.  As
`RMF.integral_sq_setIntegral_indicator_normSq_le_of_cases_rademacher` except that the two pointwise
hypotheses are stated as set integrals over `L t ∩ L u`.  The twin of
`RMF.integral_sq_setIntegral_indicator_normSq_le_of_setIntegral`. -/
theorem integral_sq_setIntegral_indicator_normSq_le_of_setIntegral_rademacher {Ω' : Type*}
    [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'}
    (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc)
    (hD : 0 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcrude : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C * min Lc (1 / |t - u|))
    (hout : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ D / (|t - u| * Real.log (2 / |t - u|) ^ 2)) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hre : ∀ t : ℝ, (0 : ℝ) < (shiftLine σ t).re := by
    intro t
    rw [re_shiftLine]
    linarith
  have hbridge : ∀ t u : ℝ,
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        = ∫ ω in L t ∩ L u,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν := fun t u =>
    (hf.setIntegral_normSq_mul_normSq_eq y (hre t) (hre u) ((hLmeas t).inter (hLmeas u))).symm
  refine integral_sq_setIntegral_indicator_normSq_le_of_cases_rademacher hY y hσ L hLmeas hSmeas
    hTm hTsub hC hLc hD hε0 hε1 (fun t ht u hu htu hτ => ?_) (fun t ht u hu htu hτ => ?_)
  · rw [hbridge t u]
    exact hcrude t ht u hu htu hτ
  · rw [hbridge t u]
    exact hout t ht u hu htu hτ

/-! ### The cutoff, and the two barrier identities

The chain reads the barrier over `b` blocks — Harper's `L(t)`, which stops `⌊\log V⌋+3` short of
the top — while the tilt sits at the full product to `x`.  Raising the cutoff from `b` to `N`
changes nothing, and the reason is a factorisation: above `x_{n+1}` the weight is independent of
the barrier, so it cancels between numerator and denominator of the tilt.

Everything structural is law-free — `RMF.indepFun_barrierLowProd_highBlocks`,
`RMF.barrierEventPair_zero`, `RMF.sum_pair_eq` — and the Rademacher block process supplies the
independence.  What is twinned is the identification of the weight with the augmented blocks'
exponential, which is `RMF.exp_sum_localTiltAdd₂_ae_eq` and
`RMF.sum_blockPairAugAdd_range_eq_sum_localTiltAdd₂`. -/

/-- **The intersection of the two barriers is the pair barrier**, in `RMF.blockPairAdd` form.  The
twin of `RMF.barrierEvent_inter_eq_blockPair`, and `rfl` for the same reason. -/
lemma barrierEvent_inter_eq_blockPairAdd {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {θ : ℝ} {N : ℕ}
    {s₁ s₂ : ℂ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} :
    barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω)) N u₁ v₁
        ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)) N u₂ v₂
      = barrierEventPair (blockPairAdd θ s₁ s₂ Y) N u₁ v₁ u₂ v₂ := rfl

/-- **The shifted sum-pair barrier is the shifted pair barrier**, for the Rademacher function.
The twin of `RMF.barrierEventPair_sumPair_shift_eq`; `RMF.sum_pair_eq` is law-free. -/
lemma barrierEventPair_sumPairAdd_shift_eq {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (θ : ℝ) (s₁ s₂ : ℂ)
    (r n : ℕ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    barrierEventPair (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
        (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) n u₁ v₁ u₂ v₂
      = barrierEventPair (fun m => blockPairAdd θ s₁ s₂ Y (m + r)) n u₁ v₁ u₂ v₂ := by
  have hpair : ∀ (m : ℕ) (ω : Ω'), (∑ p ∈ primeBlockSub θ (m + r),
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)))
      = blockPairAdd θ s₁ s₂ Y (m + r) ω :=
    fun m ω => congrFun (sum_pair_eq (fun p ω =>
      (localLogAdd (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLogAdd (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) (primeBlockSub θ (m + r))) ω
  rw [barrierEventPair, barrierEventPair]
  congr 1
  · congr 1
    funext m ω
    rw [hpair m ω]
  · congr 1
    funext m ω
    rw [hpair m ω]

/-- **The tilt's cutoff does not matter for a barrier below it**, for the Rademacher function.
The twin of `RMF.tiltedMeasure₂_barrierEventPair_congr_cutoff`.

The weight above `x_{n+1}` is independent of the barrier, so it factors out of both the restricted
and the free integral and cancels; `RMF.indepFun_barrierLowProd_highBlocks` supplies the
factorisation and is law-free. -/
theorem tiltedMeasure₂_barrierEventPairAdd_congr_cutoff {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (θ : ℝ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {n N : ℕ} (hnN : n ≤ N) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N) s₁ s₂ ν
        (barrierEventPair (blockPairAdd θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal
      = (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ n) s₁ s₂ ν
          (barrierEventPair (blockPairAdd θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal := by
  classical
  haveI := hY.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  set A : Set Ω := barrierEventPair (blockPairAdd θ s₁ s₂ Y) n u₁ v₁ u₂ v₂ with hAdef
  have hAm : MeasurableSet A :=
    measurableSet_barrierEventPair (measurable_blockPairAdd hY θ s₁ s₂) n u₁ v₁ u₂ v₂
  set W : ℕ → Ω → ℝ := fun y ω =>
    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y s₁ ω‖ ^ 2
      * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y s₂ ω‖ ^ 2 with hWdef
  have haux : ∀ j : ℕ, (fun ω => Real.exp (∑ m ∈ Finset.range (j + 2),
        (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2)))
      =ᵐ[ν] W (blockCutoff θ j) := by
    intro j
    filter_upwards [exp_sum_localTiltAdd₂_ae_eq hY (blockCutoff θ j) hs₁ hs₂] with ω hω
    rw [show j + 2 = j + 1 + 1 from rfl,
      sum_blockPairAugAdd_range_eq_sum_localTiltAdd₂ θ (j + 1) s₁ s₂ ω]
    exact hω
  have hsplit : ∀ ω : Ω, (∑ m ∈ Finset.range (N + 2),
        (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))
      = (∑ m ∈ Finset.range (n + 2),
          (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2))
        + ∑ m ∈ Finset.Ico (n + 2) (N + 2),
            (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1
              + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2) :=
    fun ω => (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  set Lo : Ω → ℝ := fun ω => Real.exp (∑ m ∈ Finset.range (n + 2),
    (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2)) with hLodef
  set Hi : Ω → ℝ := fun ω => Real.exp (∑ m ∈ Finset.Ico (n + 2) (N + 2),
    (2 * (blockPairAugAdd θ s₁ s₂ Y m ω).1 + 2 * (blockPairAugAdd θ s₁ s₂ Y m ω).2)) with hHidef
  have hWN : W (blockCutoff θ N) =ᵐ[ν] fun ω => Lo ω * Hi ω := by
    filter_upwards [(haux N).symm] with ω hω
    rw [hω, hLodef, hHidef]
    simp only
    rw [← Real.exp_add, ← hsplit ω]
  have hWn : W (blockCutoff θ n) =ᵐ[ν] Lo := (haux n).symm
  have hZm := measurable_blockPairAugAdd hY θ s₁ s₂
  have hLom : Measurable Lo := Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
    (((hZm m).fst).const_mul 2).add (((hZm m).snd).const_mul 2))
  have hHim : Measurable Hi := Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
    (((hZm m).fst).const_mul 2).add (((hZm m).snd).const_mul 2))
  have hAind : Measurable (Set.indicator A Lo) := hLom.indicator hAm
  have hindA := indepFun_barrierLowProd_highBlocks (iIndepFun_blockPairAugAdd hY θ s₁ s₂)
    (measurable_blockPairAugAdd hY θ s₁ s₂) (nb := n) (c := n + 2) (by omega) (N + 2)
    u₁ v₁ u₂ v₂
  have hind0 := indepFun_barrierLowProd_highBlocks (iIndepFun_blockPairAugAdd hY θ s₁ s₂)
    (measurable_blockPairAugAdd hY θ s₁ s₂) (nb := 0) (c := n + 2) (by omega) (N + 2)
    u₁ v₁ u₂ v₂
  rw [barrierEventPair_zero] at hind0
  simp only [Set.indicator_univ] at hind0
  have hnum : (∫ ω, Set.indicator A Lo ω * Hi ω ∂ν)
      = (∫ ω, Set.indicator A Lo ω ∂ν) * ∫ ω, Hi ω ∂ν :=
    hindA.integral_mul_eq_mul_integral hAind.aestronglyMeasurable hHim.aestronglyMeasurable
  have hden : (∫ ω, Lo ω * Hi ω ∂ν) = (∫ ω, Lo ω ∂ν) * ∫ ω, Hi ω ∂ν :=
    hind0.integral_mul_eq_mul_integral hLom.aestronglyMeasurable hHim.aestronglyMeasurable
  have hIN : (∫ ω, W (blockCutoff θ N) ω ∂ν) = (∫ ω, Lo ω ∂ν) * ∫ ω, Hi ω ∂ν := by
    rw [integral_congr_ae hWN, hden]
  have hIn : (∫ ω, W (blockCutoff θ n) ω ∂ν) = ∫ ω, Lo ω ∂ν := integral_congr_ae hWn
  have hAN : (∫ ω in A, W (blockCutoff θ N) ω ∂ν)
      = (∫ ω in A, W (blockCutoff θ n) ω ∂ν) * ∫ ω, Hi ω ∂ν := by
    rw [integral_indicator hAm |>.symm, integral_indicator hAm |>.symm]
    have hind : (fun ω => Set.indicator A (W (blockCutoff θ N)) ω)
        =ᵐ[ν] fun ω => Set.indicator A Lo ω * Hi ω := by
      filter_upwards [hWN] with ω hω
      by_cases hmem : ω ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
    have hind2 : (fun ω => Set.indicator A (W (blockCutoff θ n)) ω)
        =ᵐ[ν] fun ω => Set.indicator A Lo ω := by
      filter_upwards [hWn] with ω hω
      by_cases hmem : ω ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    rw [integral_congr_ae hind, hnum, integral_congr_ae hind2]
  have hposN : (0 : ℝ) < ∫ ω, W (blockCutoff θ N) ω ∂ν :=
    hf.integral_normSq_mul_normSq_pos _ hs₁ hs₂
  have hposn : (0 : ℝ) < ∫ ω, W (blockCutoff θ n) ω ∂ν :=
    hf.integral_normSq_mul_normSq_pos _ hs₁ hs₂
  have hHi0 : (0 : ℝ) < ∫ ω, Hi ω ∂ν := by
    rw [hIn] at hposn
    rw [hIN] at hposN
    nlinarith
  have hNeq := hf.setIntegral_normSq_mul_normSq_eq (blockCutoff θ N) hs₁ hs₂ hAm
  have hneq := hf.setIntegral_normSq_mul_normSq_eq (blockCutoff θ n) hs₁ hs₂ hAm
  have hfin : (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
        (blockCutoff θ N) s₁ s₂ ν A).toReal * (∫ ω, W (blockCutoff θ N) ω ∂ν)
      = (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
          (blockCutoff θ n) s₁ s₂ ν A).toReal * (∫ ω, W (blockCutoff θ N) ω ∂ν) := by
    rw [← hNeq, hAN, hneq, hIN, hIn]
    ring
  exact mul_right_cancel₀ hposN.ne' hfin

/-- **The barrier bound the chain consumes**, for the Rademacher function: `b` and `N` decoupled,
the barrier over `b` blocks and the tilt at the full product.  The twin of
`RMF.tiltedMeasure₂_barrier_le_of_cutoff`. -/
theorem tiltedMeasure₂_barrierAdd_le_of_cutoff {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) (θ : ℝ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {n N : ℕ} (hnN : n ≤ N) (u₁ v₁ u₂ v₂ : ℕ → ℝ) {C : ℝ}
    (h : (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ n) s₁ s₂ ν
        (barrierEventPair (blockPairAdd θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal ≤ C) :
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N) s₁ s₂ ν
        (barrierEventPair (blockPairAdd θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal ≤ C := by
  rwa [tiltedMeasure₂_barrierEventPairAdd_congr_cutoff hY θ hs₁ hs₂ hnN u₁ v₁ u₂ v₂]

/-! ### `hP0` — the bottom of the Euler product

The chain pays `E[P₀(s₁)P₀(s₂)]` for the primes below `x₀`, and it must be an absolute constant:
`\log x₀ = e^{θ}` and `θ` is capped by `ϑ = B + 2`.

**The Steinhaus deterministic constant `RMF.bottomSupConst` serves unchanged**, because the
Rademacher product is smaller factor by factor: `(1+u)(1-u) = 1-u² ≤ 1`, so
`1+u ≤ (1-u)^{-1}`.  That is the same "a fortiori" move as for the low factor
(`RMF.prod_one_add_rpow_le`), and it means `RMF.prod_one_sub_norm_inv_le` and
`RMF.one_le_prod_one_sub_rpow_half_inv` are reused rather than re-proved.  (The Steinhaus chain
itself uses the moment bound `RMF.bottomConst`.) -/

/-- `1 + u ≤ (1-u)^{-1}` for `0 ≤ u < 1`, since `(1+u)(1-u) = 1-u² ≤ 1`. -/
private lemma one_add_le_one_sub_inv {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    1 + u ≤ (1 - u)⁻¹ := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hkey : (1 + u) * (1 - u) ≤ 1 := by nlinarith
  have hw : (0 : ℝ) ≤ (1 - u)⁻¹ := inv_nonneg.2 h1u.le
  calc 1 + u = (1 + u) * (1 - u) * (1 - u)⁻¹ := by field_simp
    _ ≤ 1 * (1 - u)⁻¹ := mul_le_mul_of_nonneg_right hkey hw
    _ = (1 - u)⁻¹ := one_mul _

/-- **The Rademacher bound is dominated by the Steinhaus one, factor by factor.** -/
lemma prod_one_add_norm_le_prod_one_sub_norm_inv {S : Finset ℕ} {s : ℂ}
    (h : ∀ p ∈ S, ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1) :
    ∏ p ∈ S, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖)
      ≤ ∏ p ∈ S, (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ :=
  Finset.prod_le_prod (fun p _ => by positivity)
    fun p hp => one_add_le_one_sub_inv (norm_nonneg _) (h p hp)

/-- **The two-point weight of the whole product is integrable**, deterministically. -/
lemma IsRademacherRMF.integrable_normSq_pair {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} [IsFiniteMeasure μ]
    (hf : IsRademacherRMF f μ) (y : ℕ) (s₁ s₂ : ℂ) :
    Integrable (fun ω => ‖randomEulerProduct f y s₁ ω‖ ^ 2
      * ‖randomEulerProduct f y s₂ ω‖ ^ 2) μ := by
  have hpos : ∀ s : ℂ,
      (0 : ℝ) ≤ ∏ p ∈ Nat.primesBelow y, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖) :=
    fun s => Finset.prod_nonneg fun p _ => by positivity
  refine Integrable.mono' (integrable_const
    ((∏ p ∈ Nat.primesBelow y, (1 + ‖((p : ℕ) : ℂ) ^ (-s₁)‖)) ^ 2
      * (∏ p ∈ Nat.primesBelow y, (1 + ‖((p : ℕ) : ℂ) ^ (-s₂)‖)) ^ 2)) ?_ ?_
  · exact (((hf.aemeasurable_randomEulerProduct y s₁).norm.pow_const 2).mul
      ((hf.aemeasurable_randomEulerProduct y s₂).norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [hf.ae_norm_randomEulerProduct_le y s₁,
      hf.ae_norm_randomEulerProduct_le y s₂] with ω h₁ h₂
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
      (pow_le_pow_left₀ (norm_nonneg _) h₂ 2) (by positivity) (pow_nonneg (hpos s₁) 2)

/-- **`hP0`, supplied, for the Rademacher function.**  `E[P₀(s₁)P₀(s₂)] ≤ RMF.bottomSupConst ϑ` for
every `θ ≤ ϑ` and every pair of heights on the line `1/2 + σ`, `σ ≥ 0`: the deterministic
Steinhaus constant, since the Rademacher product is smaller factor by factor. -/
theorem integral_normSq_pair_bottom_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} (hf : IsRademacherRMF f μ)
    {θ ϑ σ : ℝ} (hθϑ : θ ≤ ϑ) {s₁ s₂ : ℂ} (hre₁ : s₁.re = 1 / 2 + σ)
    (hre₂ : s₂.re = 1 / 2 + σ) (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂μ) ≤ bottomSupConst ϑ := by
  haveI := hf.isProbabilityMeasure
  have hs₁ : 0 < s₁.re := by rw [hre₁]; linarith
  have hs₂ : 0 < s₂.re := by rw [hre₂]; linarith
  set Q : ℝ := ∏ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1),
    (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := one_le_prod_one_sub_rpow_half_inv _
  -- the Rademacher bound, then the domination, then the Steinhaus one
  have hdom : ∀ s : ℂ, 0 < s.re →
      (∏ p ∈ Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1), (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖))
        ≤ ∏ p ∈ Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1), (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ :=
    fun s hs => prod_one_add_norm_le_prod_one_sub_norm_inv
      fun p hp => norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hs
  have hbdd : ∀ᵐ ω ∂μ, ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
      * ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ≤ bottomSupConst ϑ := by
    filter_upwards [hf.ae_norm_randomEulerProduct_le (⌊blockScale θ 0⌋₊ + 1) s₁,
      hf.ae_norm_randomEulerProduct_le (⌊blockScale θ 0⌋₊ + 1) s₂] with ω h₁ h₂
    have hc₁ := le_trans (le_trans h₁ (hdom s₁ hs₁)) (prod_one_sub_norm_inv_le hθϑ hre₁ hσ)
    have hc₂ := le_trans (le_trans h₂ (hdom s₂ hs₂)) (prod_one_sub_norm_inv_le hθϑ hre₂ hσ)
    rw [← hQdef] at hc₁ hc₂
    have hsq₁ : ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2 ≤ Q ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hc₁ 2
    have hsq₂ : ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ≤ Q ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hc₂ 2
    have hfin : Q ^ 2 * Q ^ 2 = bottomSupConst ϑ := by
      rw [bottomSupConst, ← hQdef]
      ring
    calc ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2
        ≤ Q ^ 2 * Q ^ 2 :=
          mul_le_mul hsq₁ hsq₂ (by positivity) (by positivity)
      _ = bottomSupConst ϑ := hfin
  calc (∫ ω, ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ ∫ _ω, bottomSupConst ϑ ∂μ :=
        integral_mono_ae (hf.integrable_normSq_pair _ s₁ s₂) (integrable_const _) hbdd
    _ = bottomSupConst ϑ := by simp

/-! ### The split index's two moments

The middle range splits the Euler product at `x_{k+1}`, and the two factors are bounded separately:
`E[P_t] ≪ 1/τ` below the split and `E[Q] ≪ (τ/σ)²` above it.

Both are law-free in structure — `RMF.log_blockScale_splitIndex_le` and `RMF.half_lt_floor` do the
arithmetic — so only the moment inputs change: the low one calls
`RMF.exists_integral_norm_randomEulerProductIco_sq_le_rademacher` and the high one
`RMF.exists_integral_normSq_high_shift_le_rademacher`.

**`E[Q]` is where Key Proposition 5's `1/V` comes from**, and it comes from `σ`, not the grid: the
right cutoff is `M = ⌊e^{1/σ}⌉`, the scale at which the tilt's own hypothesis `1 ≤ 2σ\log M`
becomes an equality, so `\log M ≤ 1/σ` and `\log N₁ ≥ 1/τ` and the quotient is `τ/σ`. -/

/-- **`E[Q] ≪ (τ/σ)²` above the split index**, for the Rademacher function.  The twin of
`RMF.exists_integral_normSq_high_splitIndex_le`, in the regime where the split index is set by `τ`
rather than by the top of the barrier range.  Harper's height range `t, u ∈ [1/3, 1/2]` is added
and discharged inside: the sum frequency lies in `[2/3, 1]`, so `1/|t+u| ≤ 3/2 ≤ \log N₁`. -/
theorem exists_integral_normSq_high_splitIndex_le_rademacher :
    ∃ KQ > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (θ σ t u : ℝ) (m N : ℕ), 2 ≤ θ → 0 < σ → σ ≤ 1 / 2 →
        0 < |t - u| → |t - u| ≤ 1 →
        1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
        ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ m →
        Real.exp ((splitIndex θ m (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
        1 / σ ≤ Real.log (blockScale θ (N + 1)) →
        (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ + 1)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ + 1)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ KQ * (|t - u| / σ) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_high_shift_le_rademacher (Ω := Ω)
  refine ⟨K, hK, fun X μ hX θ σ t u m N hθ hσ0 hσhalf hτ0 hτ1 htl htu hul huu hfloor hNM hMN => ?_⟩
  obtain ⟨h400, hNM', hMN', hlogN₁, hM, hquot, hquot0⟩ :=
    splitIndex_high_bounds hθ hσ0 hσhalf hτ0 hτ1 hfloor hNM hMN
  set j : ℕ := splitIndex θ m (t - u) with hjdef
  -- Harper's height range makes the sum frequency free
  have hsumnn : (0 : ℝ) ≤ t + u := by linarith
  have hsum23 : (2 : ℝ) / 3 ≤ |t + u| := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have hsm : 0 < |t + u| := by linarith
  have hsm1 : |t + u| ≤ 1 := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have h32log : (3 : ℝ) / 2 ≤ Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have hle : Real.log 8 ≤ Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [h8] at hle
    linarith [Real.log_two_gt_d9]
  have hlogsum : 1 / |t + u| ≤ Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := by
    have hrecip : 1 / |t + u| ≤ 3 / 2 := by
      rw [div_le_iff₀ hsm]
      linarith
    linarith
  refine le_trans (hbound X μ hX σ t u _ _ _ hσ0.le hτ0 hτ1 hsm hsm1 h400 hNM' hMN'
    hlogN₁ hlogsum hM) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hquot0 hquot 2) hK.le

/-- **`E[P_t] \ll 1/\tau` below the split index, at `j+2`**, for the Rademacher function.  The
twin of `RMF.exists_integral_normSq_low_splitIndex_add_two_le`: two more blocks cost `e^2` in the
constant, because `\log x_{j+2} = e^2\log x_j`. -/
theorem exists_integral_normSq_low_splitIndex_add_two_le_rademacher :
    ∃ CP > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (θ σ τ : ℝ) (m : ℕ) (s : ℂ), 0 ≤ θ → 0 ≤ σ → s.re = 1 / 2 + σ →
        1 ≤ splitIndex θ m τ →
        (∫ ω, ‖randomEulerProductIco f (⌊blockScale θ 0⌋₊ + 1)
              (⌊blockScale θ (splitIndex θ m τ + 2)⌋₊ + 1) s ω‖ ^ 2 ∂μ) ≤ CP * (1 / |τ|) := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_randomEulerProductIco_sq_le_rademacher (Ω := Ω)
  refine ⟨C * Real.exp 2, by positivity, fun f μ hf θ σ τ m s hθ hσ hre h1 => ?_⟩
  have hmono : blockScale θ 0 ≤ blockScale θ (splitIndex θ m τ + 2) :=
    blockScale_mono θ (Nat.zero_le _)
  have hy₀ : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ (splitIndex θ m τ + 2)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor hmono)
  -- `\log x_{j+2} = e²\log x_j ≤ e²/τ`
  have hstep : Real.log (blockScale θ (splitIndex θ m τ + 2))
      = Real.exp 2 * Real.log (blockScale θ (splitIndex θ m τ)) := by
    rw [log_blockScale, log_blockScale, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hle : Real.log (blockScale θ (splitIndex θ m τ + 2)) ≤ Real.exp 2 * (1 / |τ|) := by
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (log_blockScale_splitIndex_le hθ h1) (Real.exp_pos 2).le
  refine le_trans (hbound f μ hf _ (blockScale θ (splitIndex θ m τ + 2)) s σ
    (two_le_blockScale hθ _) hy₀ hσ hre) ?_
  calc C * Real.log (blockScale θ (splitIndex θ m τ + 2))
      ≤ C * (Real.exp 2 * (1 / |τ|)) := mul_le_mul_of_nonneg_left hle hC.le
    _ = C * Real.exp 2 * (1 / |τ|) := by ring

/-- **The crude range's first regime**, for the Rademacher function.  The twin of
`RMF.setIntegral_normSq_pair_crude_split_le`: the four factors multiplied out, at the same
constant.  `\sigma^{-1} = \log x/(4V) = L/4`, so this is `\ll e^{2a}L^2/(\tau\log^4(2/\tau))`, and
the crude range's `\log(2/\tau) \ge \Lambda/3` is where the `\Lambda^{-4}` comes from. -/
theorem setIntegral_normSq_pair_crude_split_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {X KQ CP K0 σ τ : ℝ}
    (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hK0 : 0 ≤ K0) (hτ0 : 0 < τ) (hσ0 : 0 < σ)
    (hlog : Real.log (2 / τ) ≠ 0)
    (h52 : Real.exp (v₂ (k + 1)) ^ 2 ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
          ≤ KQ * (τ / σ) ^ 2)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν)
          ≤ CP * (1 / τ))
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ X ^ 2 * KQ * CP * K0 / σ ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 4)) := by
  have hchain := setIntegral_normSq_pair_crude_le_rademacher hY θ hs₁ hs₂ hkb hbN
    (KQ := KQ * (τ / σ) ^ 2) (CP := CP * (1 / τ)) (K0 := K0) (u₁ := u₁) (v₁ := v₁)
    (u₂ := u₂) (v₂ := v₂) (by positivity) (by positivity) hQ hPt hP0
  refine le_trans hchain ?_
  -- the four factors multiply out to the stated shape
  have h1 : (0 : ℝ) ≤ KQ * (τ / σ) ^ 2 * (CP * (1 / τ)) := by positivity
  have hstep : Real.exp (v₂ (k + 1)) ^ 2 * (KQ * (τ / σ) ^ 2 * (CP * (1 / τ))) * K0
      ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2
          * (KQ * (τ / σ) ^ 2 * (CP * (1 / τ))) * K0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h52 h1) hK0
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **The crude range's second regime**, for the Rademacher function.  The twin of
`RMF.setIntegral_normSq_pair_crude_top_le`: `k+1 = b`, the top block, where the quotient is a
single block and neither moment needs a hypothesis on `1/\tau`. -/
theorem setIntegral_normSq_pair_crude_top_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b : ℕ} (hb1 : 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {X KQ CP K0 L : ℝ}
    (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hK0 : 0 ≤ K0) (hL : 0 ≤ L)
    (h52 : Real.exp (v₂ b) ^ 2 ≤ X ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ b⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ b⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ KQ)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) ≤ CP * L)
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPairAdd θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ X ^ 2 * KQ * CP * K0 * L := by
  have hchain := setIntegral_normSq_pair_crude_le_rademacher hY θ hs₁ hs₂ (k := b - 1)
    (by omega) hbN (KQ := KQ) (CP := CP * L) (K0 := K0) (u₁ := u₁) (v₁ := v₁)
    (u₂ := u₂) (v₂ := v₂) hKQ (by positivity)
    (by rw [show b - 1 + 1 = b from by omega]; exact hQ)
    (by rw [show b - 1 + 1 = b from by omega]; exact hPt) hP0
  rw [show b - 1 + 1 = b from by omega] at hchain
  refine le_trans hchain ?_
  have h1 : (0 : ℝ) ≤ KQ * (CP * L) := by positivity
  have hstep : Real.exp (v₂ b) ^ 2 * (KQ * (CP * L)) * K0 ≤ X ^ 2 * (KQ * (CP * L)) * K0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h52 h1) hK0
  refine le_trans hstep (le_of_eq ?_)
  ring

/-- **The height integral at Harper's tube**, for the Rademacher function.  The twin of
`RMF.integral_sq_setIntegral_indicator_normSq_harper_le`. -/
theorem integral_sq_setIntegral_indicator_normSq_harper_le_rademacher {Ω' : Type*}
    [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) {E Lc W Λ ε : ℝ}
    (hE : 0 ≤ E) (hLc : 1 ≤ Lc) (hΛ : 1 ≤ Λ) (hW : 0 < W) (hWΛ : W ^ 2 ≤ Λ)
    (hlogL : 1 + Real.log (2 * Lc) ≤ 3 * Λ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcrude : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E * Lc ^ 2 / Λ ^ 4 * min Lc (1 / |t - u|))
    (hout : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E * Lc ^ 2 / W ^ 2 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (6 + 2 / Real.log 2) * (E * Lc ^ 2 / W ^ 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hC : (0 : ℝ) ≤ E * Lc ^ 2 / Λ ^ 4 := by positivity
  have hD : (0 : ℝ) ≤ E * Lc ^ 2 / W ^ 2 := by positivity
  -- `|T| ≤ 1`, since `T ⊆ [-1/2,1/2]`
  have hTfin : volume T ≤ 1 := by
    refine le_trans (measure_mono hTsub) ?_
    rw [Real.volume_Icc]
    norm_num
  have hT1 : (volume T).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (by norm_num) hTfin
    simpa using h
  have hbracket : (0 : ℝ) ≤ 2 * (E * Lc ^ 2 / Λ ^ 4) * (1 + Real.log (2 * Lc))
      + 2 * (E * Lc ^ 2 / W ^ 2) / Real.log 2 := by
    have hlog : (0 : ℝ) ≤ Real.log (2 * Lc) := Real.log_nonneg (by linarith)
    have h1 : (0 : ℝ) ≤ 2 * (E * Lc ^ 2 / Λ ^ 4) * (1 + Real.log (2 * Lc)) := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (E * Lc ^ 2 / W ^ 2) / Real.log 2 := by positivity
    linarith
  refine le_trans (integral_sq_setIntegral_indicator_normSq_le_of_setIntegral_rademacher hY y hσ L
    hLmeas
    hSmeas hTm hTsub hC hLc hD hε0 hε1 hcrude ?_) ?_
  · intro t ht u hu htu hτ
    refine le_trans (hout t ht u hu htu hτ) (le_of_eq ?_)
    rw [div_div]
  · refine le_trans (mul_le_mul_of_nonneg_right hT1 hbracket) ?_
    rw [one_mul]
    exact harper_outer_total_le hE hΛ hW hWΛ hlogL

/-- **The middle range at Harper's tube and split**, for the Rademacher function.  The twin of
`RMF.setIntegral_normSq_pair_middle_harper_le`; `RMF.barrierEventPair_subset_shift` is law-free and
supplies `hAR`. -/
theorem setIntegral_normSq_pair_middle_harper_le_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν)
    {θ σ a t u Bs : ℝ} {N b r n : ℕ} (hbN : b ≤ N) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hτ0 : 0 < |t - u|) (hτ1 : |t - u| ≤ 1)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|))
    (hmb : Real.log (2 / |t - u|) ≤ 2 * (b : ℝ))
    (hsr : splitIndex θ b (t - u) + 2 ≤ r)
    (hrb : r ≤ b) (hnbr : n ≤ b - r)
    {Cst KQ CP K0 L W : ℝ} (hCst : 0 ≤ Cst) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hW : W ≠ 0)
    (hbarD : (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
            (blockCutoff θ N) (shiftLine σ t) (shiftLine σ u) ν
            (barrierEventPair
              (fun mm => blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y (mm + r)) n
              (fun m => -shiftedHeight a Bs harperHf r - Bs * m)
              (fun m => shiftedHeight a Bs harperHf r + m + 10 * Real.log m)
              (fun m => -shiftedHeight a Bs harperHf r - Bs * m)
              (fun m => shiftedHeight a Bs harperHf r + m + 10 * Real.log m))).toReal
        ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (splitIndex θ b (t - u) + 2)⌋₊ + 1)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (splitIndex θ b (t - u) + 2)⌋₊ + 1)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ KQ * (|t - u| * L) ^ 2)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (splitIndex θ b (t - u) + 2)⌋₊ + 1)
              (shiftLine σ t) ω‖ ^ 2 ∂ν) ≤ CP * (1 / |t - u|))
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
        (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
        (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cst * KQ * CP * K0 * L ^ 2 / W ^ 2
          * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [re_shiftLine]; linarith
  have hlog0 : Real.log (2 / |t - u|) ≠ 0 := (log_two_div_pos hτ0 hτ1).ne'
  -- the barrier sits inside the shifted one, at the widened height
  have hAR := Set.Subset.trans
    (barrierEventPair_subset_shiftOf
      (Z := blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) (b := b) (r := r) (c := Bs)
      (by omega) hrb (a := a) (hf := harperHf) (fun j _ _ => abs_harperHf_le j))
    (barrierEventPair_subset_of_le hnbr)
  -- `hbarD` is already at the chain's cutoff, in the shifted family
  have hbar : (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω)
        (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) (shiftLine σ u) ν
        (barrierEventPair
          (fun m => blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y (m + r)) n
          (fun m => -shiftedHeight a Bs harperHf r - Bs * m)
          (fun m => shiftedHeight a Bs harperHf r + m + 10 * Real.log m)
          (fun m => -shiftedHeight a Bs harperHf r - Bs * m)
          (fun m => shiftedHeight a Bs harperHf r + m + 10 * Real.log m))).toReal
      ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2 := hbarD
  refine setIntegral_normSq_pair_middle_envelope_le_rademacher hY θ hs₁ hs₂
    (k := splitIndex θ b (t - u) + 1) ?_ hbN ?_ ?_ hAR hCst hKQ hCP hτ0 hlog0 hW ?_ ?_ ?_ ?_
    hP0
  · omega
  · omega
  · omega
  · exact exp_envelope_splitIndex_add_two_sq_le hθ hτ0 hsmall hmb a
  · exact hbar
  · exact hQ
  · exact hPt

/-- **The far range with its cutoffs chosen**, for the Rademacher function.  The twin of
`RMF.exists_setIntegral_normSq_pair_far_le`: `N_1 = ⌊e^Θ⌉` with `Θ` bounding `1/τ` (so
`\log^4(2Θ)` and `Θ²` are constants), `M = ⌊e^{1/σ}⌉` and `N_2 = ⌊x⌋`.  Harper's height range is
added and the sum-frequency conditions are discharged inside, as in
`RMF.exists_integral_normSq_high_splitIndex_le_rademacher`. -/
theorem exists_setIntegral_normSq_pair_far_le_rademacher :
    ∃ K > 0, ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
      ∀ (θ σ τ0 t u Cst W : ℝ) (N : ℕ) (A : Set Ω),
      0 < σ → σ ≤ 1 / 2 → 0 < |t - u| → |t - u| ≤ 1 →
      1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
      1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
      1 / σ ≤ Real.log (blockScale θ (N + 1)) → 0 ≤ Cst →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2 →
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (blockCutoff θ N) (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                  (blockCutoff θ N) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
            * ((1 / σ) ^ 2 / W ^ 2) * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨K, hK, hfarsrc⟩ := setIntegral_normSq_pair_far_envelope_le_rademacher (Ω' := Ω)
  refine ⟨K, hK, ?_⟩
  intro Y ν hY θ σ τ0 t u Cst W N A hσ0 hσhalf hτ0 hτ1 htl htu hul huu hτ0le hτ0σ hσN hCst hbar
  obtain ⟨h400, hNM, hMN₂, hlg, hM, hΘup, hlogM_hi, hlogM0, hΘ9⟩ :=
    far_truncation_bounds hσ0 hσhalf hτ0 hτ1 hτ0le hτ0σ hσN
  set τ : ℝ := |t - u| with hτdef
  set Θ : ℝ := 2 * τ0 + 7 with hΘdef
  -- the cutoff `N₂ + 1` is the tilt's
  have hcut : ⌊blockScale θ (N + 1)⌋₊ + 1 = blockCutoff θ N := rfl
  -- Harper's height range makes the sum frequency free
  have hsumnn : (0 : ℝ) ≤ t + u := by linarith
  have hsm : 0 < |t + u| := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have hsm1 : |t + u| ≤ 1 := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have hsm23 : (2 : ℝ) / 3 ≤ |t + u| := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have hlogsum : 1 / |t + u| ≤ Real.log 400 := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have hle : Real.log 8 ≤ Real.log 400 := Real.log_le_log (by norm_num) (by norm_num)
    have hrecip : 1 / |t + u| ≤ 3 / 2 := by
      rw [div_le_iff₀ hsm]
      linarith
    rw [h8] at hle
    linarith [Real.log_two_gt_d9]
  have hfar := hfarsrc Y ν hY σ t u (⌊Real.exp Θ⌋₊) (⌊Real.exp (1 / σ)⌋₊)
    (⌊blockScale θ (N + 1)⌋₊) Θ W Cst A hσ0.le hτ0 hτ1 hsm hsm1 h400 hNM hMN₂ hlg hlogsum
    hM hCst hΘup (by rw [hcut]; exact hbar)
  rw [hcut] at hfar
  refine le_trans hfar ?_
  have hbase : (0 : ℝ) ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4 := by
    have hlog0 : (0 : ℝ) ≤ Real.log (2 * Θ) := Real.log_nonneg (by linarith)
    positivity
  have hsq : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ^ 2 ≤ (1 / σ) ^ 2 :=
    pow_le_pow_left₀ hlogM0 hlogM_hi 2
  have hW0 : (0 : ℝ) ≤ 1 / W ^ 2 := by positivity
  have hlast : (0 : ℝ) ≤ 1 / (τ * Real.log (2 / τ) ^ 2) := by positivity
  have hdiv : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ^ 2 / W ^ 2 ≤ (1 / σ) ^ 2 / W ^ 2 := by
    gcongr
  calc Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4
        * (Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ^ 2 / W ^ 2)
        * (1 / (τ * Real.log (2 / τ) ^ 2))
      ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4 * ((1 / σ) ^ 2 / W ^ 2)
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hbase) hlast
    _ = Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4 * ((1 / σ) ^ 2 / W ^ 2)
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by rw [hΘdef]

/-! ### Supporting pieces for Harper's data

At Harper's data the Rademacher chain differs from the Steinhaus one in three places: the tilt
bound is `|σ|\log x_{N-d+1} ≤ η` with `η ≤ 1/10`, not `≤ 1`, so the drop has to cover `4V/η`; the
envelope condition carries `36` where the Steinhaus one carries `13`, the constant of
`RMF.exists_isBoxComparison_rademacher_of_range`; and the two `hosc` at the doubled heights are
hypotheses, supplied at Harper's heights by `RMF.exists_abs_sum_cos_primeBlockSub_harper_le`.  The
lemmas for the first two are below. -/

/-- **A drop that covers a given tilt bound, at an arbitrary target.**  The generalisation of
`RMF.sigma_le_one_of_drop` from `1` to `η`: dropping `r` blocks divides the tilt by `e^r`, so
`K ≤ ηe^r` is exactly what is needed. -/
lemma sigma_le_of_drop {θ σ K η : ℝ} {n r : ℕ} (hK : K ≤ η * Real.exp (r : ℝ)) (hrn : r ≤ n)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ K) :
    |σ| * Real.log (blockScale θ (n - r + 1)) ≤ η := by
  refine le_trans (sigma_le_mul_exp_sub θ σ K hσ) ?_
  have hcast : ((n - r : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) := Nat.cast_sub hrn
  rw [hcast, show (n : ℝ) - (r : ℝ) - (n : ℝ) = -(r : ℝ) by ring, Real.exp_neg,
    inv_eq_one_div, mul_one_div, div_le_iff₀ (Real.exp_pos _)]
  exact hK

/-! ### The envelope at a general slope

The chain runs at a slope `Bs ≥ RMF.blockSlope 125`, and its envelope condition at `36` comes from
`RMF.boxEnvelope_pair_gen_le_thirtysix`, at any slope `B ≥ 20` and offset
`RMF.blockOffsetThresholdOf B`.  `RMF.envelope_of_le_gen` carries `28` where `RMF.envelope_of_le`
carries `14`, which is why no extra offset is needed there. -/

/-- **The offset threshold at a general slope**: `\max(125, 2\log(80(4B+76)) - 1)`.  At the
Rademacher slope it is `RMF.blockOffsetThresholdAdd`, and `RMF.blockOffsetThreshold` is the
Steinhaus sibling, with `62` for `76` at `RMF.blockSlope 125`.  The shape is what the one
non-trivial step of `RMF.envelope_of_le_gen` needs. -/
noncomputable def blockOffsetThresholdOf (B : ℝ) : ℝ :=
  max 125 (2 * Real.log (80 * (4 * B + 76)) - 1)

lemma le_blockOffsetThresholdOf (B : ℝ) : (125 : ℝ) ≤ blockOffsetThresholdOf B := le_max_left _ _

/-- **The envelope, from the offset alone, at a general slope.**  `RMF.envelope_of_le_add` is this
at `RMF.blockSlopeAdd Kd 125`; the argument uses only that the slope is positive.

The `28` is the Rademacher walk's slack (`RMF.envelope_of_le` has `14`), and it is what lets the
`36`-envelope below be had with no extra offset. -/
lemma envelope_of_le_gen {B ϑ a : ℝ} {m : ℕ} (hB : 0 < B)
    (hϑ : blockOffsetThresholdOf B ≤ ϑ) (ha : 1 ≤ a) :
    2 * (3 + B) * min a ((m : ℝ) + 1) + B * (2 * (m : ℝ) + 1)
        + (2 * (m : ℝ) + 1) + 40 * Real.log ((m : ℝ) + 1) + 28
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsq : Real.sqrt (Real.log (blockScale ϑ (m + 1)))
      = Real.exp ((((m : ℝ) + 1) + ϑ) / 2) := by
    rw [log_blockScale, ← Real.exp_half]
    congr 2
    push_cast
    ring
  have hkey : 80 * (4 * B + 76) ≤ Real.exp ((1 + ϑ) / 2) := by
    have hpos : (0 : ℝ) < 80 * (4 * B + 76) := by linarith
    have hlog : Real.log (80 * (4 * B + 76)) ≤ (1 + ϑ) / 2 := by
      have := le_trans (le_max_right (125 : ℝ) _) hϑ
      linarith
    calc 80 * (4 * B + 76)
        = Real.exp (Real.log (80 * (4 * B + 76))) := (Real.exp_log hpos).symm
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
  have hlhs : 2 * (3 + B) * min a ((m : ℝ) + 1) + B * (2 * (m : ℝ) + 1)
      + (2 * (m : ℝ) + 1) + 40 * Real.log ((m : ℝ) + 1) + 28
        ≤ (4 * B + 76) * ((m : ℝ) + 1) := by
    nlinarith [hmin, hmin0, hlogm, hm0, hB]
  have hrhs : (4 * B + 76) * ((m : ℝ) + 1)
      ≤ 1 / 40 * Real.exp ((((m : ℝ) + 1) + ϑ) / 2) := by
    rw [hsplit]
    have hstep : 80 * (4 * B + 76) * (((m : ℝ) + 1) / 2)
        ≤ Real.exp ((1 + ϑ) / 2) * Real.exp ((m : ℝ) / 2) :=
      mul_le_mul hkey hexpm (by linarith) (le_trans (by linarith) hkey)
    linarith
  rw [hsq]
  linarith

/-- **The envelope condition at `36`, at a general slope**, in the form the chain consumes. -/
lemma boxEnvelope_pair_gen_le_thirtysix {B ϑ : ℝ} (hB : (20 : ℝ) ≤ B)
    (hϑ : blockOffsetThresholdOf B ≤ ϑ) (m : ℕ) :
    boxEnvelope B m + boxEnvelope B (m + 1) + blockWindow m + blockWindow m + 36
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hW : blockWindow m ≤ 1 := by
    rw [blockWindow, div_le_one (by positivity)]
    nlinarith
  have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Real.log_le_log (by exact_mod_cast hm) (by linarith)
  have henv := envelope_of_le_gen (B := B) (ϑ := ϑ) (a := (m : ℝ) + 1) (m := m)
    (by linarith) hϑ (by linarith)
  rw [min_self] at henv
  simp only [boxEnvelope]
  push_cast
  linarith

/-- **The display at Harper's data, for the Rademacher function.**  The twin of
`RMF.exists_measure_barrier_inter_harper_data_le`.  The tilt bound `|σ|\log x_{N-d+1} ≤ η` comes
from `RMF.sigma_le_of_drop`, using `|σ|\log x_{N+1} ≤ 4V` and `4V ≤ ηe^d`; the envelope at `36`
comes from `RMF.boxEnvelope_pair_gen_le_thirtysix`; the two `hosc` at the doubled heights are left
to the caller (`RMF.exists_abs_sum_cos_primeBlockSub_harper_le` on Harper's heights).  The drop `d`
is a parameter rather than `RMF.harperD V`, because `η ≤ 1/10` makes it cover `4V/η`. -/
theorem exists_measure_barrier_inter_harper_data_le_rademacher (κ Kd Bs : ℝ) (hκ : 0 ≤ κ)
    (hKd : 0 ≤ Kd) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ (n₀ : ℕ) (θ₀ : ℝ),
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (θ σ η a Λ q m V : ℝ) (N d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          θ₀ ≤ θ → harperR |t - u| + d + 4 ≤ N →
          n₀ ≤ N - d - harperR |t - u| →
          0 ≤ η → η ≤ 1 / 10 → 4 * V ≤ η * Real.exp (d : ℝ) →
          |σ| * Real.log (blockScale θ (N + 1)) ≤ 4 * V →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          0 < |t - u| → |t - u| ≤ 1 →
          (∀ mm, mm < N - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < N - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * u * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (1 : ℝ) ≤ a →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((N - d - harperR |t - u| : ℕ) : ℝ) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - Bs * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ :=
    exists_measure_barrier_inter_display_le_rademacher κ Kd Bs hκ hKd hBs
  obtain ⟨n₀, hn₀⟩ := exists_blockSizeThreshold_of_pos (v := (1 : ℝ) / 18) (by norm_num)
  refine ⟨Cst, hCst, n₀,
    max (blockOffsetThresholdOf Bs) (Real.log (Tsh / 2)), ?_⟩
  intro Ω' _ Y ν hY θ σ η a Λ q m V N d t u hf hθ hrdN hn₀N hη0 hη1 hdrop hσ
    htl htu hul huu hτ0 hτ1 hosc₁ hosc₂ ha hhf hΛ hq0 hq1 hm0 hmΛ hmq ham hn4
  set r : ℕ := harperR |t - u| with hrdef
  have hϑ : blockOffsetThresholdOf Bs ≤ θ := le_trans (le_max_left _ _) hθ
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have h125 : (125 : ℝ) ≤ θ := by linarith [le_blockOffsetThresholdOf Bs]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  -- the shift threshold, from `θ ≥ \log(Tsh/2)`
  have hTsh4 : Tsh ≤ 2 * Real.exp θ := by
    have hlog : Real.log (Tsh / 2) ≤ θ := le_trans (le_max_right _ _) hθ
    have h4 : Tsh / 2 ≤ Real.exp θ := by
      have := Real.exp_le_exp.2 hlog
      rwa [Real.exp_log (by positivity)] at this
    linarith
  obtain ⟨-, hbig, hbig2⟩ := hn₀ (N - d - r) (by rw [hrdef]; omega)
  refine hbound Ω' Y ν hY θ σ η a Λ q m N r d t u hf h125
    (one_le_harperR hτ0 hτ1) (by omega) hη0 hη1 ?_ htl htu hul huu hτ0 hτ1 ?_
    hosc₁ hosc₂ ?_ ha hbig hbig2 hhf hΛ hq0 hq1 hm0 hmΛ hmq ham (harperR_le hτ0 hτ1) hn4
  · exact sigma_le_of_drop hdrop (by omega) hσ
  · exact le_trans hTsh4 (two_mul_exp_le_mul_exp_harperR hτ0)
  · exact fun mm _ =>
      boxEnvelope_pair_gen_le_thirtysix (twenty_le_of_blockSlope_le hBs) (by linarith) mm

/-- **The barrier bound the chain consumes, at Harper's data, for the Rademacher function.**  The
twin of `RMF.exists_measure_barrier_top_harper_le`: the barrier runs over `b` blocks, Harper's
`L(t)`, and the tilt is at `blockCutoff θ N`, the full product to `x`.  The display at `(θ, b)`,
`RMF.barrierEvent_inter_eq_blockPairAdd` for the pair form, and
`RMF.tiltedMeasure₂_barrierAdd_le_of_cutoff` to raise the cutoff from `b` to `N`. -/
theorem exists_measure_barrier_top_harper_le_rademacher (κ Kd Bs : ℝ) (hκ : 0 ≤ κ) (hKd : 0 ≤ Kd)
    (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ (n₀ : ℕ) (θ₀ : ℝ),
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (θ σ η a Λ q m V : ℝ) (N b d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          θ₀ ≤ θ → 0 ≤ σ → b ≤ N →
          harperR |t - u| + d + 4 ≤ b →
          n₀ ≤ b - d - harperR |t - u| →
          0 ≤ η → η ≤ 1 / 10 → 4 * V ≤ η * Real.exp (d : ℝ) →
          |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          0 < |t - u| → |t - u| ≤ 1 →
          (∀ mm, mm < b - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < b - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * u * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          1 ≤ a → (∀ j, 1 ≤ j → j ≤ b → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((b - d - harperR |t - u| : ℕ) : ℝ) →
            (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν
                (barrierEventPair (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - Bs * j) (fun j => a + j + hf j)
                  (fun j => -a - Bs * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, hCst, n₀, θ₀, hbound⟩ :=
    exists_measure_barrier_inter_harper_data_le_rademacher κ Kd Bs hκ hKd hBs
  refine ⟨Cst, hCst, n₀, θ₀, ?_⟩
  intro Ω' _ Y ν hY θ σ η a Λ q m V N b d t u hf hθ hσ hbN hrdb hn₀b hη0 hη1 hdrop hσtop
    htl htu hul huu hτ0 hτ1 hosc₁ hosc₂ ha hhf hΛ hq0 hq1 hm0 hmΛ hmq ham hn4
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [re_shiftLine]; linarith
  have hdisp := hbound Ω' Y ν hY θ σ η a Λ q m V b d t u hf hθ hrdb hn₀b hη0 hη1 hdrop hσtop
    htl htu hul huu hτ0 hτ1 hosc₁ hosc₂ ha hhf hΛ hq0 hq1 hm0 hmΛ hmq ham hn4
  rw [barrierEvent_inter_eq_blockPairAdd] at hdisp
  exact tiltedMeasure₂_barrierAdd_le_of_cutoff hY θ hs₁ hs₂ hbN
    (fun j => -a - Bs * j) (fun j => a + j + hf j)
    (fun j => -a - Bs * j) (fun j => a + j + hf j) hdisp

/-- **`hbar` at Harper's data, for the Rademacher function.**  The twin of
`RMF.exists_measure_barrierEventPair_shift_display_le`: Proposition 7 at the shifted family,
`RMF.exists_proposition7_upper_rademacher`, converted by the law-free `Λ` arithmetic
`RMF.min_one_div_sqrt_sq_le`.  It carries `η`, Harper's height range, the two `hosc` at the
doubled heights and the envelope condition at `36`. -/
theorem exists_measure_barrierEventPair_shift_display_le_rademacher (κ Kd Bs : ℝ) (hκ : 0 ≤ κ)
    (hKd : 0 ≤ Kd) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
        ∀ (θ σ η τ a Λ q m : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf hg : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          0 ≤ η → η ≤ 1 / 10 → |σ| * Real.log (blockScale θ (r + n + 1)) ≤ η →
          1 / 3 ≤ s₁.im → s₁.im ≤ 1 / 2 → 1 / 3 ≤ s₂.im → s₂.im ≤ 1 / 2 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < r + n →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * s₁.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < r + n →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * s₂.im * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < n →
            boxEnvelope (Bs) mm + boxEnvelope (Bs) (mm + 1)
                + blockWindow mm + blockWindow mm + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftedHeight a Bs hf r → 4 ≤ n →
          4 * Real.log (n : ℝ) ^ 20 ≤ (n : ℝ) →
          4 * Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hg j| ≤ 10 * Real.log j) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / τ) →
          0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / τ) + 1 → Λ ≤ 4 * (n : ℝ) →
            ((tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair (fun mm => blockPairAdd θ s₁ s₂ X (mm + r)) n
                (fun j => -shiftedHeight a Bs hf r - Bs * j)
                (fun j => shiftedHeight a Bs hf r + j + hg j)
                (fun j => -shiftedHeight a Bs hf r - Bs * j)
                (fun j => shiftedHeight a Bs hf r + j + hg j))).toReal
              ≤ Cst * Real.log (2 / τ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hprop7⟩ := exists_proposition7_upper_rademacher Kd Bs hKd hBs
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB : (0 : ℝ) ≤ Bs := le_trans (blockSlope_pos 125).le hBs
  set K : ℝ := 42 + 2 * Bs + (31 + Bs) / Real.log 2 + 2 * κ
    with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    positivity
  refine ⟨Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2), Tsh, by positivity, hTsh, ?_⟩
  intro Ω' _ X μ hX θ σ η τ a Λ q m N r n s₁ s₂ hf hg hθ hr1 hrn hre₁ hre₂ hη0 hη1 hσtop
    him₁l him₁u him₂l him₂u hτ0 hτ1 hτeq hTshle hosc₁ hosc₂ henvc ha hn4 hbig hbig2 hhg hhf
    hΛ hq0 hq1 hm0 hmΛ hmq ham ha0 hr hn3
  have hn1 : 1 ≤ n := by omega
  have himne : s₁.im ≠ s₂.im := by
    intro h
    rw [h, sub_self, abs_zero] at hτeq
    linarith [hτeq ▸ hτ0]
  have hTsh' : Tsh ≤ |s₁.im - s₂.im| * Real.exp ((r : ℝ) + θ) := by rw [hτeq]; exact hTshle
  have hlev : shiftedHeight a Bs hf r ≤ 2 * m + K * Real.log (2 / τ) := by
    have h := shiftedHeight_le_of_le (a := a) (c := Bs) (hf := hf)
      (zero_le_of_blockSlope_le hBs) hτ0 hτ1 hr (hhf r hr1 (by omega))
    have hKL : K * Real.log (2 / τ)
        = (42 + 2 * Bs + (31 + Bs) / Real.log 2)
            * Real.log (2 / τ) + 2 * (κ * Real.log (2 / τ)) := by
      rw [hKdef]
      ring
    linarith [h, ham, hKL]
  have harith := min_one_div_sqrt_sq_le (Λ := Λ) (a := shiftedHeight a Bs hf r) (τ := τ) (K := K)
    (q := q) (m := m) (n := n) hΛ hq0 hq1 hτ0 hτ1 hK0 hn1 hm0 hmΛ hmq
    (le_trans ha0 (le_shiftedHeight (zero_le_of_blockSlope_le hBs) ha0 r hf)) hlev (by norm_num) hn3
  have hprop := hprop7 Ω' X μ hX θ σ η (shiftedHeight a Bs hf r) N r n s₁ s₂ hg hθ hrn hre₁ hre₂
    hη0 hη1 hσtop him₁l him₁u him₂l him₂u himne hTsh' hosc₁ hosc₂ henvc ha hn4 hbig hbig2 hhg
  rw [barrierEventPair_sumPairAdd_shift_eq] at hprop
  refine le_trans hprop ?_
  calc Cst * min 1 (shiftedHeight a Bs hf r / Real.sqrt n) ^ 2
      ≤ Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2 * Real.log (2 / τ) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := mul_le_mul_of_nonneg_left harith hCst.le
    _ = Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2) * Real.log (2 / τ) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by ring

/-- **The far range, end to end at Harper's data, for the Rademacher function.**  The twin of
`RMF.exists_setIntegral_normSq_pair_far_harper_le`: the `hout` shape of
`RMF.integral_sq_setIntegral_indicator_normSq_le_of_setIntegral_rademacher`, with the barrier
probability supplied at Harper's data and the free moment at the far range's own cutoffs;
`RMF.IsRademacherRMF.setIntegral_normSq_mul_normSq_eq` is an equality, so nothing is lost. -/
theorem exists_setIntegral_normSq_pair_far_harper_le_rademacher (κ Kd Bs : ℝ) (hκ : 0 ≤ κ)
    (hKd : 0 ≤ Kd) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ (n₀ : ℕ) (θ₀ : ℝ),
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ K > 0,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (θ σ η a Λ q m V τ0 : ℝ) (N b d : ℕ) (t u : ℝ),
          θ₀ ≤ θ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
          harperR |t - u| + d + 4 ≤ b →
          n₀ ≤ b - d - harperR |t - u| →
          0 ≤ η → η ≤ 1 / 10 → 4 * V ≤ η * Real.exp (d : ℝ) →
          |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          0 < |t - u| → |t - u| ≤ 1 →
          (∀ mm, mm < b - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < b - d →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * u * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          1 ≤ a → 1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((b - d - harperR |t - u| : ℕ) : ℝ) →
          1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
          1 / σ ≤ Real.log (blockScale θ (N + 1)) →
              (∫ ω in barrierEventPair
                  (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
                  (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
                  ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (blockCutoff θ N) (shiftLine σ t) ω‖ ^ 2
                    * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                        (blockCutoff θ N) (shiftLine σ u) ω‖ ^ 2 ∂ν)
                ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
                    * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
                    * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨Cst, hCst, n₀, θ₀, hbar⟩ :=
    exists_measure_barrier_top_harper_le_rademacher κ Kd Bs hκ hKd hBs
  refine ⟨Cst, hCst, n₀, θ₀, ?_⟩
  intro Ω' _
  obtain ⟨K, hK, hfarsrc⟩ := exists_setIntegral_normSq_pair_far_le_rademacher (Ω := Ω')
  refine ⟨K, hK, ?_⟩
  intro Y ν hY θ σ η a Λ q m V τ0 N b d t u hθ hσ0 hσhalf hbN hrdb hn₀b hη0 hη1 hdrop hσtop
    htl htu hul huu hτ0 hτ1 hosc₁ hosc₂ ha hΛ hq0 hq1 hm0 hmΛ hmq ham hn4 hτ0le hτ0σ hσN
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [re_shiftLine]; linarith
  have hAm : MeasurableSet
      (barrierEventPair (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
        (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
        (fun j => -a - Bs * j) (fun j => a + j + harperHf j)) :=
    measurableSet_barrierEventPair
      (measurable_blockPairAdd hY θ (shiftLine σ t) (shiftLine σ u)) b _ _ _ _
  have hbarA := hbar Ω' Y ν hY θ σ η a Λ q m V N b d t u harperHf hθ hσ0.le hbN hrdb hn₀b
    hη0 hη1 hdrop hσtop htl htu hul huu hτ0 hτ1 hosc₁ hosc₂ ha
    (fun j _ _ => abs_harperHf_le j) hΛ hq0 hq1 hm0 hmΛ hmq ham hn4
  have hfar := hfarsrc Y ν hY θ σ τ0 t u Cst (1 + (1 - q) * Real.sqrt Λ) N _ hσ0 hσhalf
    hτ0 hτ1 htl htu hul huu hτ0le hτ0σ hσN hCst.le hbarA
  rw [hf.setIntegral_normSq_mul_normSq_eq (blockCutoff θ N) hs₁ hs₂ hAm]
  exact hfar

/-! ### The middle range, end to end at Harper's data

Three of the barrier's inputs differ from the Steinhaus assembly: the tilt bound is `≤ η` with
`η ≤ 1/10` rather than `≤ 1`, the block envelope is at `36` rather than `13`, and the two `hosc` at
the doubled heights are carried.  Harper's height range is carried too; `hQ` needs it and
discharges the sum frequency inside. -/

/-- **The middle range, end to end at Harper's data, for the Rademacher function.**  The twin of
`RMF.exists_setIntegral_normSq_pair_middle_harper_le`.  `KQ` and `CP` come after `Ω'`, as in
their sources, but before `Y`, `t`, `u` and the rest of the data, so one constant serves every pair
`(t, u)` in `T`.  The estimate runs over `n ≤ b - r` blocks while the barrier stays at `b`
(`RMF.barrierEventPair_subset_of_le`): the tilt bound `≤ 1` at Harper's barrier top becomes
`≤ 1/10` three blocks down. -/
theorem exists_setIntegral_normSq_pair_middle_harper_le_rademacher (κ Kd Bs : ℝ) (hκ : 0 ≤ κ)
    (hKd : 0 ≤ Kd) (hBs : blockSlope 125 ≤ Bs) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (θ σ η a Λ q m ϑ t u : ℝ) (N b r n : ℕ),
          (125 : ℝ) ≤ θ → θ ≤ ϑ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
          splitIndex θ b (t - u) + 2 ≤ r → r ≤ b →
          n ≤ b - r →
          1 ≤ splitIndex θ b (t - u) → ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b →
          0 < |t - u| → |t - u| ≤ 1 →
          1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
          Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) →
          Real.log (2 / |t - u|) ≤ 2 * (b : ℝ) →
          0 ≤ η → η ≤ 1 / 10 →
          |σ| * Real.log (blockScale θ (r + n + 1)) ≤ η →
          Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < r + n →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * t * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < r + n →
            |∑ p ∈ primeBlockSub θ mm,
                Real.cos (2 * u * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
              ≤ 2 / 3 * (Kd * Real.exp (-(mm : ℝ)))) →
          (∀ mm, mm < n →
            boxEnvelope (Bs) mm + boxEnvelope (Bs) (mm + 1)
                + blockWindow mm + blockWindow mm + 36
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftedHeight a Bs harperHf r → 4 ≤ n →
          4 * Real.log (n : ℝ) ^ 20 ≤ (n : ℝ) →
          4 * Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) * (1 / 18) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / |t - u|) + 1 → Λ ≤ 4 * (n : ℝ) →
          Real.exp ((splitIndex θ b (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
          1 / σ ≤ Real.log (blockScale θ (N + 1)) →
              (∫ ω in barrierEventPair (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
                  (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
                  ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                      (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
                    * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                        (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
                ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cst * KQ * CP * bottomSupConst ϑ
                    * (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2
                    * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbarsrc⟩ :=
    exists_measure_barrierEventPair_shift_display_le_rademacher κ Kd Bs hκ hKd hBs
  refine ⟨Cst, Tsh, hCst, hTsh, ?_⟩
  intro Ω' _
  obtain ⟨KQ, hKQ, hQsrc⟩ := exists_integral_normSq_high_splitIndex_le_rademacher (Ω := Ω')
  obtain ⟨CP, hCP, hPsrc⟩ :=
    exists_integral_normSq_low_splitIndex_add_two_le_rademacher (Ω := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY θ σ η a Λ q m ϑ t u N b r n hθ hθϑ hσ0 hσhalf hbN hsr hrb hnbr hsplit1
    hfloor hτ0 hτ1 htl htu hul huu hsmall hmb hη0 hη1 hσtop hTshle hosc₁ hosc₂ henvc hares
    hn4 hbig hbig2 hΛ hq0 hq1 hm0 hmΛ hmq ham ha0 hr hn3 hNM hMN
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hre₁ : (shiftLine σ t).re = 1 / 2 + σ := re_shiftLine σ t
  have hre₂ : (shiftLine σ u).re = 1 / 2 + σ := re_shiftLine σ u
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hW : (1 : ℝ) + (1 - q) * Real.sqrt Λ ≠ 0 := by
    have hs : (1 : ℝ) ≤ Real.sqrt Λ := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hΛ
    nlinarith
  -- `hbarD`
  have hbarD := hbarsrc Ω' Y ν hY θ σ η |t - u| a Λ q m N r n (shiftLine σ t)
    (shiftLine σ u) harperHf (fun mm => 10 * Real.log mm) hθ (by omega) (by omega) hre₁ hre₂
    hη0 hη1 hσtop
    (by rw [im_shiftLine]; exact htl) (by rw [im_shiftLine]; exact htu)
    (by rw [im_shiftLine]; exact hul) (by rw [im_shiftLine]; exact huu) hτ0 hτ1
    (by rw [im_shiftLine, im_shiftLine]) hTshle
    (fun mm hmm => by rw [im_shiftLine]; exact hosc₁ mm hmm)
    (fun mm hmm => by rw [im_shiftLine]; exact hosc₂ mm hmm)
    henvc hares hn4 hbig hbig2
    (fun j _ _ => le_of_eq (abs_of_nonneg (by
      have h0 := Real.log_natCast_nonneg j
      positivity)))
    (fun j _ _ => abs_harperHf_le j) hΛ hq0 hq1 hm0 hmΛ hmq ham ha0 hr hn3
  -- `hQ` and `hPt`
  have hQ := hQsrc Y ν hY θ σ t u b N (by linarith) hσ0 hσhalf hτ0 hτ1 htl htu hul huu hfloor
    hNM hMN
  have hPt := hPsrc (fun ω => squarefreeExtension fun p => Y p ω) ν hf θ σ (t - u) b
    (shiftLine σ t) hθ0 hσ0.le hre₁ hsplit1
  -- `hP0`
  have hP0 := integral_normSq_pair_bottom_le_rademacher hf hθϑ hre₁ hre₂ hσ0.le
  refine setIntegral_normSq_pair_middle_harper_le_rademacher hY hbN hθ0 hσ0.le hτ0 hτ1 hsmall
    hmb hsr hrb hnbr hCst.le hKQ.le hCP.le hW hbarD ?_ ?_ hP0
  · refine le_trans hQ (le_of_eq ?_)
    rw [div_eq_mul_inv, mul_comm |t - u| (1 / σ)]
    field_simp
  · exact hPt

/-! ### The crude range, end to end at Harper's data

Two instantiations of `RMF.setIntegral_normSq_pair_crude_le_rademacher`, as in the Steinhaus file.
Below `(\log x)^{-1/3}` the `1/Λ^4` in (5.2) suffices and the indicators are thrown away, so no
barrier probability enters and `η` does not appear.  Harper's height range is carried, because the
two-point moment sees the sum frequency `t+u`; `1/|t+u| ≤ \log N_1` is discharged inside. -/

/-- **The crude range's first regime, end to end, for the Rademacher function.**  The twin of
`RMF.exists_setIntegral_normSq_pair_crude_split_harper_le`: `\tau \ge 1/L`, split at
`RMF.splitIndex θ b (t-u) + 2`.  Harper's height range is the only added hypothesis;
`RMF.exists_integral_normSq_high_splitIndex_le_rademacher` uses it for the sum frequency. -/
theorem exists_setIntegral_normSq_pair_crude_split_harper_le_rademacher (Bs : ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
      ∀ (θ σ a ϑ t u : ℝ) (N b : ℕ),
      (125 : ℝ) ≤ θ → θ ≤ ϑ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
      splitIndex θ b (t - u) + 2 ≤ b → 1 ≤ splitIndex θ b (t - u) →
      ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b →
      0 < |t - u| → |t - u| ≤ 1 →
      1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
      Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) →
      Real.log (2 / |t - u|) ≤ 2 * (b : ℝ) →
      Real.exp ((splitIndex θ b (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
      1 / σ ≤ Real.log (blockScale θ (N + 1)) →
      (∫ ω in barrierEventPair (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * KQ * CP * bottomSupConst ϑ / σ ^ 2
            * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 4)) := by
  obtain ⟨KQ, hKQ, hQsrc⟩ := exists_integral_normSq_high_splitIndex_le_rademacher (Ω := Ω')
  obtain ⟨CP, hCP, hPsrc⟩ :=
    exists_integral_normSq_low_splitIndex_add_two_le_rademacher (Ω := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY θ σ a ϑ t u N b hθ hθϑ hσ0 hσhalf hbN hsp hsplit1 hfloor hτ0 hτ1 htl htu hul huu
    hsmall hmb hNM hMN
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hre₁ : (shiftLine σ t).re = 1 / 2 + σ := re_shiftLine σ t
  have hre₂ : (shiftLine σ u).re = 1 / 2 + σ := re_shiftLine σ u
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [hre₂]; linarith
  have hQ := hQsrc Y ν hY θ σ t u b N (by linarith) hσ0 hσhalf hτ0 hτ1 htl htu hul huu hfloor
    hNM hMN
  have hPt := hPsrc (fun ω => squarefreeExtension fun p => Y p ω) ν hf θ σ (t - u) b
    (shiftLine σ t) hθ0 hσ0.le hre₁ hsplit1
  have hP0 := integral_normSq_pair_bottom_le_rademacher hf hθϑ hre₁ hre₂ hσ0.le
  have h52 := exp_envelope_splitIndex_add_two_sq_le (θ := θ) (m := b) (t := t - u) hθ0 hτ0
    hsmall hmb a
  exact setIntegral_normSq_pair_crude_split_le_rademacher hY θ hs₁ hs₂
    (k := splitIndex θ b (t - u) + 1) (by omega) hbN hKQ.le hCP.le
    (one_le_bottomSupConst ϑ |>.trans' zero_le_one) hτ0 hσ0
    (log_two_div_pos hτ0 hτ1).ne' h52 hQ hPt hP0

/-- **The crude range's second regime, end to end, for the Rademacher function.**  The twin of
`RMF.exists_setIntegral_normSq_pair_crude_top_harper_le`: `τ < 1/L`, split at the barrier's own
top `k+1 = b`, where `Q` is the `⌊\log V⌋+3` blocks between `x_b` and `x` and neither moment sees
`1/τ`.  The sum frequency is seen, and Harper's height range answers it:
`1/|t+u| ≤ 3/2 ≤ \log N_1` since `N_1 = ⌊x_b⌋ ≥ 400`. -/
theorem exists_setIntegral_normSq_pair_crude_top_harper_le_rademacher (Bs : ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
      ∀ (θ σ a ϑ t u : ℝ) (N b M : ℕ),
      (0 : ℝ) ≤ θ → θ ≤ ϑ → 0 ≤ σ → 1 ≤ b → b ≤ N →
      (400 : ℝ) ≤ ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) →
      ⌊blockScale θ b⌋₊ ≤ M → M ≤ ⌊blockScale θ (N + 1)⌋₊ →
      1 ≤ 2 * σ * Real.log (M : ℝ) →
      1 / 3 ≤ t → t ≤ 1 / 2 → 1 / 3 ≤ u → u ≤ 1 / 2 →
      (∫ ω in barrierEventPair (blockPairAdd θ (shiftLine σ t) (shiftLine σ u) Y) b
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j)
          (fun j => -a - Bs * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Real.exp (a + (b : ℝ) + harperHf b) ^ 2
            * (KQ * (Real.log (M : ℝ)
                / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ)) ^ 4)
            * CP * bottomSupConst ϑ * Real.log (blockScale θ b) := by
  obtain ⟨KQ, hKQ, hQsrc⟩ := exists_integral_normSq_pairIco_split_shift_le_rademacher (Ω := Ω')
  obtain ⟨CP, hCP, hPsrc⟩ := exists_integral_norm_randomEulerProductIco_sq_le_rademacher (Ω := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY θ σ a ϑ t u N b M hθ hθϑ hσ0 hb1 hbN h400 hbM hMN hMtilt htl htu hul huu
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hre₁ : (shiftLine σ t).re = 1 / 2 + σ := re_shiftLine σ t
  have hre₂ : (shiftLine σ u).re = 1 / 2 + σ := re_shiftLine σ u
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [hre₂]; linarith
  -- Harper's height range makes the sum frequency free, exactly as it does above the split index
  have hsumnn : (0 : ℝ) ≤ t + u := by linarith
  have hsum23 : (2 : ℝ) / 3 ≤ |t + u| := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have hsm : 0 < |t + u| := by linarith
  have hsm1 : |t + u| ≤ 1 := by
    rw [abs_of_nonneg hsumnn]
    linarith
  have h32log : (3 : ℝ) / 2 ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have hle : Real.log 8 ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [h8] at hle
    linarith [Real.log_two_gt_d9]
  have hlogsum : 1 / |t + u| ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
    have hrecip : 1 / |t + u| ≤ 3 / 2 := by
      rw [div_le_iff₀ hsm]
      linarith
    linarith
  have hQ := hQsrc Y ν hY σ t u (⌊blockScale θ b⌋₊) M (⌊blockScale θ (N + 1)⌋₊) hσ0 hsm hsm1
    h400 hbM hMN hlogsum hMtilt
  have hy₀ : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ b⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le b)))
  have hPt := hPsrc (fun ω => squarefreeExtension fun p => Y p ω) ν hf (⌊blockScale θ 0⌋₊ + 1)
    (blockScale θ b) (shiftLine σ t) σ (two_le_blockScale hθ b) hy₀ hσ0 hre₁
  have hP0 := integral_normSq_pair_bottom_le_rademacher hf hθϑ hre₁ hre₂ hσ0
  refine setIntegral_normSq_pair_crude_top_le_rademacher hY θ hs₁ hs₂ hb1 hbN
    (KQ := KQ * (Real.log (M : ℝ)
      / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ)) ^ 4) (CP := CP) (K0 := bottomSupConst ϑ)
    (L := Real.log (blockScale θ b)) (by positivity) hCP.le
    (le_trans zero_le_one (one_le_bottomSupConst ϑ)) ?_ le_rfl hQ hPt hP0
  · have hlogb : (0 : ℝ) ≤ Real.log (blockScale θ b) := by
      rw [log_blockScale]
      positivity
    positivity

/-! ### Key Proposition 5 from the four ranges, for the Rademacher function

This step is law-free apart from the Euler product it names: every hypothesis is an abstract bound
on the four ranges, and the proof is the Steinhaus twin's two case splits, three reconciliations
(`RMF.crude_split_le_min`, `RMF.crude_top_le_min`, `RMF.le_div_of_middle_far`, shared) and `max`
over four constants.  It discharges the two range hypotheses of
`RMF.integral_sq_setIntegral_indicator_normSq_harper_le_rademacher`.  Harper's height range and `η`
do not appear: the suppliers `RMF.exists_setIntegral_normSq_pair_crude_split_harper_le_rademacher`,
`RMF.exists_setIntegral_normSq_pair_crude_top_harper_le_rademacher`,
`RMF.exists_setIntegral_normSq_pair_middle_harper_le_rademacher` and
`RMF.exists_setIntegral_normSq_pair_far_harper_le_rademacher` consume them.  The crude boundary
`κ` is a parameter, not `L_c`, since the first regime reaches only `1/τ = e^{b+θ-2}`
(`RMF.exp_splitIndex_add_two_le_of_le`).  `ε` is Harper's `(\log x)^{-1/3}` and `ε'` his
`e^{-(2θ+2)}/2`; `hcrudelog`, `Λ/3 ≤ \log(2/τ)` on the crude range, gives the `Λ^{-4}`. -/
theorem integral_sq_setIntegral_indicator_normSq_harper_of_ranges_rademacher {Ω' : Type*}
    [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν)
    (y : ℕ) {σ : ℝ} (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    {C₁ C₂ E₁ E₂ S Lb nb Lc W Λ ε ε' κ K : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hS0 : 0 ≤ S)
    (hLb0 : 0 ≤ Lb) (hnb0 : 0 < nb) (hσ0 : 0 < σ) (hLceq : Lc = 1 / σ) (hLc : 1 ≤ Lc)
    (hΛ : 1 ≤ Λ) (hW : 0 < W) (hWΛ : W ^ 2 ≤ Λ) (hlogL : 1 + Real.log (2 * Lc) ≤ 3 * Λ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hσLb : σ * Lb ≤ S) (hΛb : Λ ≤ 2 * nb)
    (hK1 : 1 ≤ K) (hκLc : κ ≤ Lc) (hLcκ : Lc ≤ K * κ)
    (hcrudelog : ∀ τ : ℝ, 0 < τ → τ ≤ ε → Λ / 3 ≤ Real.log (2 / τ))
    (hcr1 : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε → 1 / |t - u| ≤ κ →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C₁ * Lc ^ 2 * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 4)))
    (hcr2 : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε → κ ≤ 1 / |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C₂ * Lb ^ 3 / nb ^ 4)
    (hmid : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| → |t - u| ≤ ε' →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E₁ * Lc ^ 2 / W ^ 2 * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)))
    (hfar : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| → ε' < |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E₂ * Lc ^ 2 / W ^ 2 * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2))) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (6 + 2 / Real.log 2)
          * (max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / W ^ 2) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ4 : (0 : ℝ) < Λ ^ 4 := by positivity
  have hW2 : (0 : ℝ) < W ^ 2 := pow_pos hW 2
  have hmax1 : (0 : ℝ) ≤ max (81 * C₁) (16 * K * S ^ 3 * C₂) :=
    le_trans (by positivity) (le_max_left _ _)
  have hE : (0 : ℝ) ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
    le_trans hmax1 (le_max_left _ _)
  -- `|t-u| ≤ 1`, since `T ⊆ [-1/2,1/2]`
  have hTle : ∀ t ∈ T, ∀ u ∈ T, |t - u| ≤ 1 := by
    intro t ht u hu
    have h1 := hTsub ht
    have h2 := hTsub hu
    simp only [Set.mem_Icc] at h1 h2
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine integral_sq_setIntegral_indicator_normSq_harper_le_rademacher hY y hσ0.le L
    hLmeas hSmeas hTm hTsub hE hLc hΛ hW hWΛ hlogL hε0 hε1 ?_ ?_
  · -- the crude range, split at `1/τ = L_c`
    intro t ht u hu htu hτ
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hmin0 : (0 : ℝ) ≤ min Lc (1 / |t - u|) := le_min (by linarith) (by positivity)
    have hLc0 : (0 : ℝ) ≤ Lc := by linarith
    rcases le_or_gt (1 / |t - u|) κ with h | h
    · have hLe : 1 / |t - u| ≤ Lc := le_trans h hκLc
      have h1 := crude_split_le_min (C := C₁ * Lc ^ 2) (by positivity) hτ0 hΛ0
        (hcrudelog _ hτ0 hτ) hLe (hcr1 t ht u hu htu hτ h)
      have hle : 81 * C₁ ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hstep : 81 * (C₁ * Lc ^ 2) / Λ ^ 4
          ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / Λ ^ 4 := by
        rw [div_le_div_iff₀ hΛ4 hΛ4]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg Lc)) hΛ4.le]
      exact le_trans h1 (mul_le_mul_of_nonneg_right hstep hmin0)
    · have hKm : Lc ≤ K * (1 / |t - u|) := by
        refine le_trans hLcκ ?_
        exact mul_le_mul_of_nonneg_left h.le (by linarith)
      have h2 := crude_top_le_min (C := C₂) (K := K) hC₂ hS0 hσ0 hΛ0 hnb0 hLb0
        hK1 hσLb hΛb hLceq hKm (hcr2 t ht u hu htu hτ h.le)
      have hle : 16 * K * S ^ 3 * C₂
          ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hstep : 16 * K * S ^ 3 * C₂ * Lc ^ 2 / Λ ^ 4
          ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / Λ ^ 4 := by
        rw [div_le_div_iff₀ hΛ4 hΛ4]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg Lc)) hΛ4.le]
      exact le_trans h2 (mul_le_mul_of_nonneg_right hstep hmin0)
  · -- the outer range, split at `τ = ε'`
    intro t ht u hu htu hτ
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := hTle t ht u hu
    have hden : (0 : ℝ) < |t - u| * Real.log (2 / |t - u|) ^ 2 := by
      have hlp := log_two_div_pos hτ0 hτ1
      positivity
    have h := le_div_of_middle_far (E₁ := E₁) (E₂ := E₂) (Lc := Lc) (W := W) (ε' := ε')
      hE₁ hE₂ hτ0 (fun hle => hmid t ht u hu htu hτ hle) (fun hlt => hfar t ht u hu htu hτ hlt)
    have hle : max E₁ E₂ ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
      le_max_right _ _
    have hpos : (0 : ℝ) < W ^ 2 * (|t - u| * Real.log (2 / |t - u|) ^ 2) := mul_pos hW2 hden
    have hstep : max E₁ E₂ * Lc ^ 2 / W ^ 2 / (|t - u| * Real.log (2 / |t - u|) ^ 2)
        ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / W ^ 2
            / (|t - u| * Real.log (2 / |t - u|) ^ 2) := by
      rw [div_div, div_div, div_le_div_iff₀ hpos hpos]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg Lc)) hpos.le]
    exact le_trans h hstep

end RMF
