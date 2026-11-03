/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.PSeries
import RMF.Probability.Barrier

/-!
# The expected overshoot at first passage, and the barrier estimate

`RMF.IsGaussianWalk.barrierProb_le` is conditional on a uniform bound `D₀` for the expected
overshoot at the first passage of the barrier.  This file discharges that hypothesis
(`RMF.IsGaussianWalk.lintegral_overshoot_le_mgf`), which completes the upper bound of (A1)
(Harper, arXiv:1703.06654, Appendix A.1) for increments that are not identically distributed:

`P(max_{j ≤ n} S j ≤ c) ≤ A (1 + c) / √n`,

with `A` depending only on bounds `v₋ ≤ v j ≤ v₊` for the increment variances
(`RMF.IsGaussianWalk.barrierProb_le_of_comparable_mgf`).

## The reduction

On the event that the first passage happens at time `k`, the walk stood at `S (k-1) ≤ c` a
moment earlier, so with `a := c - S (k-1) ≥ 0` the overshoot is exactly `(G (k-1) - a)⁺`.  Both
the event and `a` depend only on the increments before `k - 1`, so independence gives

`E[overshoot] = ∑_j E[𝟙{τ > j} · g (c - S j)]`,   `g a := E[(G - a)⁺]`,

and slicing the distance below the barrier into unit bands reduces the problem to two estimates,
which are then summed against each other.

## The two estimates

*Decay of `g`*: `g i ≤ (e\sqrt{v₊}/2)e^{-2i/\sqrt{v₊}}`, from the moment generating function
(`RMF.integral_posPart_sub_le_mgf` at `t = 2/\sqrt{v₊}`), so the sum over the bands is geometric.

*Occupation of a band*: the expected time the walk spends within `[i, i+1)` of the barrier
before crossing it is `≪ (i+1)²`
(`RMF.IsGaussianWalk.tsum_measure_survivedGap_le_occConstOf`).  The visits are split into
excursions of length `⌈(i+1)²/v₋⌉`, over which the accumulated variance is at least `(i+1)²`;
each excursion therefore fails to cross the barrier with probability at most `1 - ρ`, where
`ρ = 1/8` (`RMF.le_measure_Ioi_one_gaussianReal_eighth`; the true `P(N(0,1) > 1)` is `0.1587`).
Only the *lower* bound on the variances enters here.

## The constant

The two estimates give `RMF.overshootConstMgf`.  At `(v₋, v₊) = (1/16, 9/2)` it is `2.4·10³`, and
it is the constant `RMF.barrierConst` carries.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### Splitting off one increment

At a first passage at time `j + 1`, the walk stood at `walk G j ≤ c` a moment earlier, so the
overshoot is `(G j - a)⁺` with `a := c - walk G j ≥ 0`.  Both the survival event and `a` are
functions of the increments before `j`, so `G j` is independent of them.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma mem_firstPassage_succ {c : ℝ} {j : ℕ} {ω : Ω} :
    ω ∈ firstPassage G c (j + 1) ↔ (∀ l ≤ j, walk G l ω ≤ c) ∧ c < walk G (j + 1) ω := by
  simp only [firstPassage, Set.mem_setOf_eq, Nat.lt_succ_iff]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **One increment split off.**  The overshoot at a passage at time `j + 1` is the positive
part of the `j`-th increment beyond the distance the walk then had to the barrier. -/
lemma passageZ_succ_eq (G : ℕ → Ω → ℝ) (c : ℝ) (j : ℕ) (ω : Ω) :
    passageZ G c (j + 1) ω
      = {ω | ∀ l ≤ j, walk G l ω ≤ c}.indicator
          (fun ω => max (G j ω - (c - walk G j ω)) 0) ω := by
  have hw : walk G (j + 1) ω - c = G j ω - (c - walk G j ω) := by
    rw [walk_succ]
    simp only [Pi.add_apply]
    ring
  by_cases hW : ω ∈ {ω | ∀ l ≤ j, walk G l ω ≤ c}
  · rw [Set.indicator_of_mem hW]
    by_cases hF : ω ∈ firstPassage G c (j + 1)
    · rw [passageZ, Set.indicator_of_mem hF, hw,
        max_eq_left (by linarith [(mem_firstPassage_succ.mp hF).2, hw])]
    · have hle : walk G (j + 1) ω ≤ c := by
        by_contra hcon
        exact hF (mem_firstPassage_succ.mpr ⟨hW, not_le.mp hcon⟩)
      rw [passageZ, Set.indicator_of_notMem hF, max_eq_right (by linarith)]
  · rw [Set.indicator_of_notMem hW, passageZ,
      Set.indicator_of_notMem fun hcon => hW (mem_firstPassage_succ.mp hcon).1]

omit [IsProbabilityMeasure μ] in
/-- The prefix of partial sums up to time `j` is independent of the `j`-th increment. -/
lemma IsGaussianWalk.indepFun_prefixSums_incr (h : IsGaussianWalk G v μ) (j : ℕ) :
    IndepFun (fun ω => prefixSums j fun i => G i ω) (G j) μ := by
  have hcomp := (h.indepFun_prefixSums_blockSums j (j + 1)).comp
    (measurable_id : Measurable (id : (ℕ → ℝ) → (ℕ → ℝ))) (measurable_pi_apply (j + 1))
  simp only [Function.comp_def, id] at hcomp
  have h2 : (fun ω => (blockSums j (j + 1) fun i => G i ω) (j + 1)) = G j := by
    funext ω
    rw [blockSums_comp G (Nat.le_succ j) le_rfl ω, walk_succ]
    simp
  rwa [h2] at hcomp

omit [IsProbabilityMeasure μ] in
/-- If `Y` and `R` are independent then over any event cut out by `Y` the average of a function
of `R` factors as the measure of the event times the average of the function. -/
lemma lintegral_preimage_comp_of_indepFun {β : Type*} [MeasurableSpace β] {Y : Ω → β}
    {R : Ω → ℝ} {S : Set β} {f : ℝ → ℝ≥0∞} (hY : Measurable Y) (hR : Measurable R)
    (hS : MeasurableSet S) (hf : Measurable f) (hind : IndepFun Y R μ) :
    ∫⁻ ω in Y ⁻¹' S, f (R ω) ∂μ = μ (Y ⁻¹' S) * ∫⁻ ω, f (R ω) ∂μ := by
  have hFY : (Y ⁻¹' S).indicator (1 : Ω → ℝ≥0∞)
      = fun ω => (S.indicator (1 : β → ℝ≥0∞)) (Y ω) := by
    ext ω
    by_cases hω : Y ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ Y ⁻¹' S from hω), Set.indicator_of_mem hω,
        Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem (show ω ∉ Y ⁻¹' S from hω), Set.indicator_of_notMem hω]
  have hindep : IndepFun ((Y ⁻¹' S).indicator (1 : Ω → ℝ≥0∞)) (fun ω => f (R ω)) μ := by
    rw [hFY]
    exact hind.comp (measurable_one.indicator hS) hf
  have hmeas1 : Measurable ((Y ⁻¹' S).indicator (1 : Ω → ℝ≥0∞)) :=
    measurable_one.indicator (hY hS)
  have hpt : ∀ ω, ((Y ⁻¹' S).indicator (1 : Ω → ℝ≥0∞) * fun ω => f (R ω)) ω
      = (Y ⁻¹' S).indicator (fun ω => f (R ω)) ω := by
    intro ω
    by_cases hω : ω ∈ Y ⁻¹' S
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  calc ∫⁻ ω in Y ⁻¹' S, f (R ω) ∂μ
      = ∫⁻ ω, (Y ⁻¹' S).indicator (fun ω => f (R ω)) ω ∂μ :=
        (lintegral_indicator (hY hS) _).symm
    _ = ∫⁻ ω, ((Y ⁻¹' S).indicator (1 : Ω → ℝ≥0∞) * fun ω => f (R ω)) ω ∂μ :=
        lintegral_congr fun ω => (hpt ω).symm
    _ = (∫⁻ ω, (Y ⁻¹' S).indicator (1 : Ω → ℝ≥0∞) ω ∂μ) * ∫⁻ ω, f (R ω) ∂μ :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hmeas1 (hf.comp hR) hindep
    _ = μ (Y ⁻¹' S) * ∫⁻ ω, f (R ω) ∂μ := by
        rw [lintegral_indicator_one (hY hS)]

/-! ### Partitioning by the distance to the barrier

Write `S j` for `walk G j`.  Partitioning the survival event `{S l ≤ c for all l ≤ j}` according
to the integer part of the gap `c - S j ≥ 0` gives, for each `j`,

`E[(G j - (c - S j))⁺; S l ≤ c for l ≤ j]
    ≤ ∑_i P(S l ≤ c for l ≤ j, c - S j ∈ [i, i+1)) · E[(G j - i)⁺]`,

since `c - S j ≥ i` on the `i`-th piece.  The point of the partition is that the right-hand
factor no longer involves the past: it is a function of `G j` alone, so it factors out against
the event by `RMF.lintegral_preimage_comp_of_indepFun`.
-/

/-- The walk has stayed below the barrier through time `j`, and stands at distance in
`[i, i + 1)` below it. -/
def survivedGap (G : ℕ → Ω → ℝ) (c : ℝ) (i j : ℕ) : Set Ω :=
  {ω | (∀ l ≤ j, walk G l ω ≤ c) ∧ (i : ℝ) ≤ c - walk G j ω ∧ c - walk G j ω < i + 1}

/-- The same condition, read off the prefix of partial sums. -/
private def survivedGapSet (c : ℝ) (i j : ℕ) : Set (ℕ → ℝ) :=
  {f | (∀ l ≤ j, f l ≤ c) ∧ (i : ℝ) ≤ c - f j ∧ c - f j < i + 1}

private lemma measurableSet_survivedGapSet (c : ℝ) (i j : ℕ) :
    MeasurableSet (survivedGapSet c i j) := by
  have hrw : survivedGapSet c i j = (⋂ l ∈ Set.Iic j, {f : ℕ → ℝ | f l ≤ c})
      ∩ {f : ℕ → ℝ | (i : ℝ) ≤ c - f j} ∩ {f : ℕ → ℝ | c - f j < i + 1} := by
    ext f
    simp [survivedGapSet, and_assoc]
  rw [hrw]
  refine ((MeasurableSet.biInter (Set.to_countable _) fun l _ =>
    measurableSet_le (measurable_pi_apply l) measurable_const).inter ?_).inter ?_
  · exact measurableSet_le measurable_const (measurable_const.sub (measurable_pi_apply j))
  · exact measurableSet_lt (measurable_const.sub (measurable_pi_apply j)) measurable_const

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
private lemma survivedGap_eq_preimage (G : ℕ → Ω → ℝ) (c : ℝ) (i j : ℕ) :
    survivedGap G c i j
      = (fun ω => prefixSums j fun t => G t ω) ⁻¹' survivedGapSet c i j := by
  ext ω
  simp only [survivedGap, survivedGapSet, Set.mem_preimage, Set.mem_setOf_eq,
    prefixSums_comp G le_rfl ω]
  refine and_congr_left fun _ => forall_congr' fun l => forall_congr' fun hl => ?_
  rw [prefixSums_comp G hl ω]

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurableSet_survivedGap (h : IsGaussianWalk G v μ) (c : ℝ) (i j : ℕ) :
    MeasurableSet (survivedGap G c i j) := by
  rw [survivedGap_eq_preimage]
  exact (measurable_prefixSums j).comp
    (measurable_pi_lambda _ fun t => h.measurable t) (measurableSet_survivedGapSet c i j)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma iUnion_survivedGap (G : ℕ → Ω → ℝ) (c : ℝ) (j : ℕ) :
    ⋃ i : ℕ, survivedGap G c i j = {ω | ∀ l ≤ j, walk G l ω ≤ c} := by
  ext ω
  simp only [Set.mem_iUnion, survivedGap, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hs, -, -⟩
    exact hs
  · intro hs
    have hnn : 0 ≤ c - walk G j ω := by linarith [hs j le_rfl]
    refine ⟨⌊c - walk G j ω⌋₊, hs, ?_, ?_⟩
    · exact Nat.floor_le hnn
    · exact Nat.lt_floor_add_one _

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma pairwise_disjoint_survivedGap (G : ℕ → Ω → ℝ) (c : ℝ) (j : ℕ) :
    Pairwise (Function.onFun Disjoint (fun i => survivedGap G c i j)) := by
  intro i i' hii
  refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
  have hi : (i : ℝ) ≤ c - walk G j ω := h1.2.1
  have hi' : (i' : ℝ) ≤ c - walk G j ω := h2.2.1
  have hu : c - walk G j ω < i + 1 := h1.2.2
  have hu' : c - walk G j ω < i' + 1 := h2.2.2
  have : i = i' := by
    have h1' : (i : ℝ) < i' + 1 := lt_of_le_of_lt hi hu'
    have h2' : (i' : ℝ) < i + 1 := lt_of_le_of_lt hi' hu
    have e1 : i < i' + 1 := by exact_mod_cast h1'
    have e2 : i' < i + 1 := by exact_mod_cast h2'
    omega
  exact hii this

omit [IsProbabilityMeasure μ] in
/-- The overshoot contributed by a passage at time `j + 1` is at most

`∑_i P(survived to j, gap in [i, i+1)) · b i`,   `b i ≥ E[(G j - i)⁺]`. -/
theorem IsGaussianWalk.lintegral_passageZ_le (h : IsGaussianWalk G v μ) (c : ℝ) (j : ℕ)
    {b : ℕ → ℝ}
    (hb : ∀ i : ℕ, ∫ x, max (x - i) 0 ∂(gaussianReal 0 (v j)) ≤ b i) :
    ∫⁻ ω, ENNReal.ofReal (passageZ G c (j + 1) ω) ∂μ
      ≤ ∑' i : ℕ, μ (survivedGap G c i j) * ENNReal.ofReal (b i) := by
  have hGmeas := h.measurable j
  have hind := h.indepFun_prefixSums_incr j
  -- the average of `(G j - i)⁺`
  have hone : ∀ i : ℕ, ∫⁻ ω, ENNReal.ofReal (max (G j ω - i) 0) ∂μ
      ≤ ENNReal.ofReal (b i) := by
    intro i
    have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (max (x - i) 0) := by fun_prop
    rw [← lintegral_map hmeas hGmeas, h.map_eq j,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_posPart_sub_gaussianReal _ _)
        (Filter.Eventually.of_forall fun x => le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal (hb i)
  calc ∫⁻ ω, ENNReal.ofReal (passageZ G c (j + 1) ω) ∂μ
      = ∫⁻ ω in {ω | ∀ l ≤ j, walk G l ω ≤ c},
          ENNReal.ofReal (max (G j ω - (c - walk G j ω)) 0) ∂μ := by
        rw [← lintegral_indicator (h.measurableSet_forall_le c j)]
        refine lintegral_congr fun ω => ?_
        rw [passageZ_succ_eq G c j ω]
        by_cases hω : ω ∈ {ω | ∀ l ≤ j, walk G l ω ≤ c}
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
    _ = ∑' i : ℕ, ∫⁻ ω in survivedGap G c i j,
          ENNReal.ofReal (max (G j ω - (c - walk G j ω)) 0) ∂μ := by
        rw [← iUnion_survivedGap G c j,
          lintegral_iUnion (fun i => h.measurableSet_survivedGap c i j)
            (pairwise_disjoint_survivedGap G c j)]
    _ ≤ ∑' i : ℕ, ∫⁻ ω in survivedGap G c i j,
          ENNReal.ofReal (max (G j ω - i) 0) ∂μ := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        refine setLIntegral_mono' (h.measurableSet_survivedGap c i j) fun ω hω => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hgap : (i : ℝ) ≤ c - walk G j ω := hω.2.1
        rcases le_total (G j ω - (c - walk G j ω)) 0 with hle | hle
        · rw [max_eq_right hle]
          exact le_max_right _ _
        · rw [max_eq_left hle]
          exact le_trans (by linarith) (le_max_left _ _)
    _ = ∑' i : ℕ, μ (survivedGap G c i j) * ∫⁻ ω, ENNReal.ofReal (max (G j ω - i) 0) ∂μ := by
        refine tsum_congr fun i => ?_
        rw [survivedGap_eq_preimage]
        exact lintegral_preimage_comp_of_indepFun (R := G j)
          (f := fun x => ENNReal.ofReal (max (x - (i : ℝ)) 0))
          ((measurable_prefixSums j).comp (measurable_pi_lambda _ fun t => h.measurable t))
          hGmeas (measurableSet_survivedGapSet c i j) (by fun_prop) hind
    _ ≤ ∑' i : ℕ, μ (survivedGap G c i j) * ENNReal.ofReal (b i) :=
        ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (hone i)

/-- The σ-algebra of events decided by the walk up to time `s`. -/
@[reducible]
noncomputable def prefixAlgebra (G : ℕ → Ω → ℝ) (s : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => prefixSums s fun t => G t ω) inferInstance

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Events decided by the walk up to time `j` are decided by it up to any later time `s`. -/
lemma measurableSet_prefixAlgebra_survivedGap (G : ℕ → Ω → ℝ) (c : ℝ) (i : ℕ) {j s : ℕ}
    (hjs : j ≤ s) : MeasurableSet[prefixAlgebra G s] (survivedGap G c i j) := by
  refine ⟨survivedGapSet c i j, measurableSet_survivedGapSet c i j, ?_⟩
  ext ω
  simp only [survivedGap, survivedGapSet, Set.mem_preimage, Set.mem_setOf_eq,
    prefixSums_comp G hjs ω]
  refine and_congr_left fun _ => forall_congr' fun l => forall_congr' fun hl => ?_
  rw [prefixSums_comp G (hl.trans hjs) ω]

/-! ### Surviving one block from within the band

Write `S j` for `walk G j`.  If at time `s` the walk is still below the barrier and within
`i + 1` of it, then it clears the barrier during `(s, s + T]` as soon as the block sum exceeds
`i + 1`, which has probability at least `ρ` once the block's variance is at least `(i+1)²` and
`ρ ≤ P(N(0,1) > 1)`.  Hence for any event `B` decided by the increments before `s` and forcing
the walk into the band at `s`,

`P(B and the walk survives to s + T) ≤ (1 - ρ) P(B)`.

This is the one step that the excursion count iterates; note that it compares `B` with itself,
not with a supremum over walks, so no fixed-point argument is involved.
-/

/-- **One block from within the band**, at any crossing probability `ρ`. -/
theorem IsGaussianWalk.measure_inter_survived_le_of (h : IsGaussianWalk G v μ) {c : ℝ}
    {i s T : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ ≤ gaussianReal 0 1 (Set.Ioi 1))
    (hV1 : ((i : ℝ) + 1) ^ 2 ≤ ((∑ m ∈ Finset.Ico s (s + T), v m : ℝ≥0) : ℝ))
    {B : Set Ω} (hB : MeasurableSet[prefixAlgebra G s] B)
    (hsub : B ⊆ survivedGap G c i s) :
    μ (B ∩ {ω | ∀ l ≤ s + T, walk G l ω ≤ c})
      ≤ ENNReal.ofReal (1 - ρ) * μ B := by
  obtain ⟨S, hS, rfl⟩ := hB
  set y : ℝ := (i : ℝ) + 1 with hy
  set V := (∑ m ∈ Finset.Ico s (s + T), v m) with hVdef
  have hypos : (0 : ℝ) < y := by positivity
  -- the block clears the gap with probability at least `ρ`
  have hcross : ENNReal.ofReal ρ
      ≤ μ {ω | y < walk G (s + T) ω - walk G s ω} := by
    have hlaw : μ.map (fun ω => walk G (s + T) ω - walk G s ω) = gaussianReal 0 V :=
      h.map_walk_sub (Nat.le_add_right s T)
    have hmeasR : Measurable (fun ω => walk G (s + T) ω - walk G s ω) :=
      (h.measurable_walk (s + T)).sub (h.measurable_walk s)
    have hset : {ω | y < walk G (s + T) ω - walk G s ω}
        = (fun ω => walk G (s + T) ω - walk G s ω) ⁻¹' Set.Ioi y := rfl
    rw [hset, ← Measure.map_apply hmeasR measurableSet_Ioi, hlaw]
    exact le_measure_Ioi_gaussianReal_of hρ hypos hV1
  -- so it fails to clear it with probability at most `1 - ρ`
  have hfail : μ {ω | walk G (s + T) ω - walk G s ω ≤ y}
      ≤ ENNReal.ofReal (1 - ρ) := by
    have hcompl : {ω | walk G (s + T) ω - walk G s ω ≤ y}
        = {ω | y < walk G (s + T) ω - walk G s ω}ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hmeasgt : MeasurableSet {ω | y < walk G (s + T) ω - walk G s ω} :=
      measurableSet_lt measurable_const
        ((h.measurable_walk (s + T)).sub (h.measurable_walk s) :
          Measurable (fun ω => walk G (s + T) ω - walk G s ω))
    rw [hcompl, prob_compl_eq_one_sub hmeasgt]
    have hρ1 : ENNReal.ofReal (1 - ρ) = 1 - ENNReal.ofReal ρ := by
      rw [ENNReal.ofReal_sub _ hρ0, ENNReal.ofReal_one]
    rw [hρ1]
    exact tsub_le_tsub_left hcross 1
  -- surviving to `s + T` from the band forces the block not to clear the gap
  have hincl : (fun ω => prefixSums s fun t => G t ω) ⁻¹' S
        ∩ {ω | ∀ l ≤ s + T, walk G l ω ≤ c}
      ⊆ (fun ω => prefixSums s fun t => G t ω) ⁻¹' S
        ∩ {ω | walk G (s + T) ω - walk G s ω ≤ y} := by
    rintro ω ⟨hB, hsurv⟩
    refine ⟨hB, ?_⟩
    have hgap : c - walk G s ω < y := (hsub hB).2.2
    have hle : walk G (s + T) ω ≤ c := hsurv (s + T) le_rfl
    simp only [Set.mem_setOf_eq]
    linarith
  -- and the two events are independent
  have hblock : {ω | walk G (s + T) ω - walk G s ω ≤ y}
      = (fun ω => blockSums s (s + T) fun t => G t ω) ⁻¹' {f : ℕ → ℝ | f (s + T) ≤ y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq,
      blockSums_comp G (Nat.le_add_right s T) le_rfl ω]
  calc μ ((fun ω => prefixSums s fun t => G t ω) ⁻¹' S
        ∩ {ω | ∀ l ≤ s + T, walk G l ω ≤ c})
      ≤ μ ((fun ω => prefixSums s fun t => G t ω) ⁻¹' S
          ∩ {ω | walk G (s + T) ω - walk G s ω ≤ y}) := measure_mono hincl
    _ = μ ((fun ω => prefixSums s fun t => G t ω) ⁻¹' S)
          * μ {ω | walk G (s + T) ω - walk G s ω ≤ y} := by
        rw [hblock]
        exact (h.indepFun_prefixSums_blockSums s (s + T)).measure_inter_preimage_eq_mul _ _ hS
          (measurableSet_le (measurable_pi_apply (s + T)) measurable_const)
    _ ≤ μ ((fun ω => prefixSums s fun t => G t ω) ⁻¹' S)
          * ENNReal.ofReal (1 - ρ) := mul_le_mul' le_rfl hfail
    _ = ENNReal.ofReal (1 - ρ)
          * μ ((fun ω => prefixSums s fun t => G t ω) ⁻¹' S) := mul_comm _ _

/-! ### The excursion times

The occupation of the band is bounded by counting *excursions*: the visits to the band split
into groups of length `T`, and each group costs a factor `1 - ρ` by
`RMF.IsGaussianWalk.measure_inter_survived_le_of`.

The excursion times are functions `Ω → ℕ` defined by `Nat.find`; the fibres
`{ω | visitTime r ω = s}` are characterised as events built from `survivedGap` at times `≤ s`,
hence preimages under `prefixSums s`, which is what the one-step estimate needs.  A walk need not
visit the band again, so a horizon `N` is fixed and `N + 1` means "no further visit"; the bound
`T / ρ` does not depend on `N`, and the untruncated statement is the supremum over `N`.
-/

open scoped Classical in
/-- The first time in `[t, N]` at which the walk is still below the barrier and within `i + 1`
of it, or `N + 1` if there is no such time. -/
noncomputable def nextVisit (G : ℕ → Ω → ℝ) (c : ℝ) (i N t : ℕ) (ω : Ω) : ℕ :=
  Nat.find (p := fun j => j = N + 1 ∨ (t ≤ j ∧ j ≤ N ∧ ω ∈ survivedGap G c i j))
    ⟨N + 1, Or.inl rfl⟩

/-- The `r`-th visit to the band, successive visits being separated by at least `T`. -/
noncomputable def visitTime (G : ℕ → Ω → ℝ) (c : ℝ) (i N T : ℕ) : ℕ → Ω → ℕ
  | 0 => nextVisit G c i N 0
  | r + 1 => fun ω => nextVisit G c i N (visitTime G c i N T r ω + T) ω

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Below the sentinel, `nextVisit` really is a visit, and it is at least `t`. -/
lemma nextVisit_spec {G : ℕ → Ω → ℝ} {c : ℝ} {i N t : ℕ} {ω : Ω}
    (h : nextVisit G c i N t ω ≤ N) :
    t ≤ nextVisit G c i N t ω ∧ ω ∈ survivedGap G c i (nextVisit G c i N t ω) := by
  classical
  simp only [nextVisit] at h ⊢
  rcases Nat.find_spec (p := fun j => j = N + 1 ∨ (t ≤ j ∧ j ≤ N ∧ ω ∈ survivedGap G c i j))
    ⟨N + 1, Or.inl rfl⟩ with hsent | ⟨ht, -, hmem⟩
  · exact absurd hsent (by omega)
  · exact ⟨ht, hmem⟩

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- `nextVisit` is the *first* such time. -/
lemma nextVisit_le_of_mem {G : ℕ → Ω → ℝ} {c : ℝ} {i N t : ℕ} {ω : Ω} {j : ℕ}
    (htj : t ≤ j) (hjN : j ≤ N) (hmem : ω ∈ survivedGap G c i j) :
    nextVisit G c i N t ω ≤ j := by
  classical
  exact Nat.find_min' _ (Or.inr ⟨htj, hjN, hmem⟩)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Successive visits are separated by at least `T`, unless the sentinel has been reached. -/
lemma visitTime_succ_ge (G : ℕ → Ω → ℝ) (c : ℝ) (i N T : ℕ) (r : ℕ) (ω : Ω)
    (h : visitTime G c i N T (r + 1) ω ≤ N) :
    visitTime G c i N T r ω + T ≤ visitTime G c i N T (r + 1) ω :=
  (nextVisit_spec h).1

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Below the sentinel, the `r`-th visit really is a visit. -/
lemma mem_survivedGap_visitTime {G : ℕ → Ω → ℝ} {c : ℝ} {i N T r : ℕ} {ω : Ω}
    (h : visitTime G c i N T r ω ≤ N) :
    ω ∈ survivedGap G c i (visitTime G c i N T r ω) := by
  cases r with
  | zero => exact (nextVisit_spec h).2
  | succ r => exact (nextVisit_spec h).2

/-! ### Fibres of the excursion times

The bridge promised above: the fibres of `visitTime`, which the covering argument treats as
numbers, are the events built from `survivedGap`, which is what makes them measurable with
respect to the walk up to that time.

Both statements carry an ambient level `s` with the target time `s' ≤ s`, so that the induction
never has to compare `prefixAlgebra G s'` with `prefixAlgebra G s`.
-/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Below the horizon, `nextVisit t ω = s` says exactly that `s` is a visit at a time `≥ t`,
and that there is no earlier one. -/
lemma nextVisit_eq_iff_of_le {G : ℕ → Ω → ℝ} {c : ℝ} {i N t s : ℕ} (hs : s ≤ N) (ω : Ω) :
    nextVisit G c i N t ω = s ↔
      t ≤ s ∧ ω ∈ survivedGap G c i s ∧ ∀ j, t ≤ j → j < s → ω ∉ survivedGap G c i j := by
  classical
  rw [nextVisit, Nat.find_eq_iff]
  constructor
  · rintro ⟨hps, hmin⟩
    rcases hps with hsent | ⟨ht, -, hmem⟩
    · exact absurd hsent (by omega)
    · exact ⟨ht, hmem, fun j htj hjs hmemj => hmin j hjs (Or.inr ⟨htj, by omega, hmemj⟩)⟩
  · rintro ⟨ht, hmem, hno⟩
    refine ⟨Or.inr ⟨ht, hs, hmem⟩, fun j hjs hpj => ?_⟩
    rcases hpj with hsent | ⟨htj, -, hmemj⟩
    · exact absurd hsent (by omega)
    · exact hno j htj hjs hmemj

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma measurableSet_prefixAlgebra_nextVisit (G : ℕ → Ω → ℝ) (c : ℝ) (i N t : ℕ) {s s' : ℕ}
    (hs's : s' ≤ s) (hs' : s' ≤ N) :
    MeasurableSet[prefixAlgebra G s] {ω | nextVisit G c i N t ω = s'} := by
  by_cases hts : t ≤ s'
  · have hrw : {ω | nextVisit G c i N t ω = s'}
        = survivedGap G c i s' ∩ ⋂ j ∈ Set.Ico t s', (survivedGap G c i j)ᶜ := by
      ext ω
      rw [Set.mem_setOf_eq, nextVisit_eq_iff_of_le hs' ω]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_Ico, Set.mem_compl_iff]
      constructor
      · rintro ⟨-, hmem, hno⟩
        exact ⟨hmem, fun j hj => hno j hj.1 hj.2⟩
      · rintro ⟨hmem, hno⟩
        exact ⟨hts, hmem, fun j h1 h2 => hno j ⟨h1, h2⟩⟩
    rw [hrw]
    refine (measurableSet_prefixAlgebra_survivedGap G c i hs's).inter ?_
    refine MeasurableSet.biInter (Set.to_countable _) fun j hj => ?_
    exact (measurableSet_prefixAlgebra_survivedGap G c i
      (le_of_lt (lt_of_lt_of_le hj.2 hs's))).compl
  · have hrw : {ω | nextVisit G c i N t ω = s'} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hcon
      exact hts ((nextVisit_eq_iff_of_le hs' ω).mp hcon).1
    rw [hrw]
    exact @MeasurableSet.empty Ω (prefixAlgebra G s)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The `r + 1`-st visit is reached from the `r`-th, and the two are `T` apart. -/
lemma visitTime_succ_eq_iff {G : ℕ → Ω → ℝ} {c : ℝ} {i N T r s' : ℕ} (hs' : s' ≤ N) (ω : Ω) :
    visitTime G c i N T (r + 1) ω = s'
      ↔ ∃ s'' ≤ s', visitTime G c i N T r ω = s'' ∧ nextVisit G c i N (s'' + T) ω = s' := by
  constructor
  · intro hv
    refine ⟨visitTime G c i N T r ω, ?_, rfl, hv⟩
    have := (nextVisit_eq_iff_of_le hs' ω).mp hv
    omega
  · rintro ⟨s'', -, hr, hnext⟩
    change nextVisit G c i N (visitTime G c i N T r ω + T) ω = s'
    rw [hr]
    exact hnext

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The bridge.**  Each fibre of `visitTime` is decided by the walk up to that time. -/
lemma measurableSet_prefixAlgebra_visitTime (G : ℕ → Ω → ℝ) (c : ℝ) (i N T : ℕ) (r : ℕ)
    {s s' : ℕ} (hs's : s' ≤ s) (hs' : s' ≤ N) :
    MeasurableSet[prefixAlgebra G s] {ω | visitTime G c i N T r ω = s'} := by
  induction r generalizing s' with
  | zero => exact measurableSet_prefixAlgebra_nextVisit G c i N 0 hs's hs'
  | succ r ih =>
      have hrw : {ω | visitTime G c i N T (r + 1) ω = s'}
          = ⋃ s'' ∈ Set.Iic s', ({ω | visitTime G c i N T r ω = s''}
              ∩ {ω | nextVisit G c i N (s'' + T) ω = s'}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, Set.mem_inter_iff,
          exists_prop]
        rw [visitTime_succ_eq_iff hs' ω]
      rw [hrw]
      refine MeasurableSet.biUnion (Set.to_countable _) fun s'' hs'' => ?_
      exact (ih (le_trans hs'' hs's) (le_trans hs'' hs')).inter
        (measurableSet_prefixAlgebra_nextVisit G c i N _ hs's hs')

/-! ### Geometric decay of the excursion count

Each excursion costs a factor `1 - ρ`: splitting `{θ_{r+1} ≤ N}` over the disjoint fibres of
`θ_r` puts us, on each piece, in the situation of
`RMF.IsGaussianWalk.measure_inter_survived_le_of`.
-/

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurableSet_of_prefixAlgebra (h : IsGaussianWalk G v μ) {s : ℕ}
    {B : Set Ω} (hB : MeasurableSet[prefixAlgebra G s] B) : MeasurableSet B := by
  obtain ⟨S, hS, rfl⟩ := hB
  exact ((measurable_prefixSums s).comp (measurable_pi_lambda _ fun t => h.measurable t)) hS

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Below the horizon, the `r`-th visit takes one of finitely many values. -/
lemma visitTime_le_eq_biUnion (G : ℕ → Ω → ℝ) (c : ℝ) (i N T r : ℕ) :
    {ω | visitTime G c i N T r ω ≤ N}
      = ⋃ s ∈ Finset.range (N + 1), {ω | visitTime G c i N T r ω = s} := by
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, exists_prop]
  constructor
  · exact fun hv => ⟨_, by omega, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    omega

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurableSet_visitTime_le (h : IsGaussianWalk G v μ) (c : ℝ)
    (i N T r : ℕ) : MeasurableSet {ω | visitTime G c i N T r ω ≤ N} := by
  rw [visitTime_le_eq_biUnion]
  exact MeasurableSet.biUnion (Set.to_countable _) fun s hs =>
    h.measurableSet_of_prefixAlgebra (measurableSet_prefixAlgebra_visitTime G c i N T r
      (le_refl s) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Being in the band at time `j` entails having stayed below the barrier up to any earlier
time. -/
lemma survivedGap_forall_le {G : ℕ → Ω → ℝ} {c : ℝ} {i j : ℕ} {ω : Ω}
    (hmem : ω ∈ survivedGap G c i j) {j' : ℕ} (hj : j' ≤ j) : ∀ l ≤ j', walk G l ω ≤ c :=
  fun l hl => hmem.1 l (hl.trans hj)

/-- **One excursion costs a factor `1 - ρ`**, at any crossing probability `ρ`. -/
theorem IsGaussianWalk.measure_visitTime_succ_le_of (h : IsGaussianWalk G v μ) {c : ℝ}
    {i N T : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ ≤ gaussianReal 0 1 (Set.Ioi 1))
    (hV1 : ∀ s, ((i : ℝ) + 1) ^ 2 ≤ ((∑ m ∈ Finset.Ico s (s + T), v m : ℝ≥0) : ℝ))
    (r : ℕ) :
    μ {ω | visitTime G c i N T (r + 1) ω ≤ N}
      ≤ ENNReal.ofReal (1 - ρ)
          * μ {ω | visitTime G c i N T r ω ≤ N} := by
  classical
  have hfibre : ∀ s ≤ N, MeasurableSet {ω | visitTime G c i N T r ω = s} := fun s hs =>
    h.measurableSet_of_prefixAlgebra
      (measurableSet_prefixAlgebra_visitTime G c i N T r (le_refl s) hs)
  have hmeasSucc := h.measurableSet_visitTime_le c i N T (r + 1)
  -- split over the value of the `r`-th visit
  have hunion : {ω | visitTime G c i N T (r + 1) ω ≤ N}
      = ⋃ s ∈ Finset.range (N + 1), ({ω | visitTime G c i N T r ω = s}
          ∩ {ω | visitTime G c i N T (r + 1) ω ≤ N}) := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq,
      exists_prop]
    constructor
    · intro hv
      refine ⟨visitTime G c i N T r ω, ?_, rfl, hv⟩
      have hsep := visitTime_succ_ge G c i N T r ω hv
      omega
    · rintro ⟨s, -, -, hv⟩
      exact hv
  have hdisj : ((Finset.range (N + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun s => {ω | visitTime G c i N T r ω = s}
        ∩ {ω | visitTime G c i N T (r + 1) ω ≤ N} := by
    intro s _ s' _ hss
    refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
    exact hss (h1.1.symm.trans h2.1)
  rw [hunion, measure_biUnion_finset hdisj fun s hs =>
    (hfibre s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))).inter hmeasSucc]
  -- each piece shrinks by `1 - ρ`
  have hstep : ∀ s ∈ Finset.range (N + 1),
      μ ({ω | visitTime G c i N T r ω = s} ∩ {ω | visitTime G c i N T (r + 1) ω ≤ N})
        ≤ ENNReal.ofReal (1 - ρ) * μ {ω | visitTime G c i N T r ω = s} := by
    intro s hs
    have hsN : s ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hsub : {ω | visitTime G c i N T r ω = s} ⊆ survivedGap G c i s := by
      intro ω hω
      have : visitTime G c i N T r ω ≤ N := by rw [hω]; exact hsN
      have hmem := mem_survivedGap_visitTime this
      rwa [hω] at hmem
    have hincl : {ω | visitTime G c i N T r ω = s}
          ∩ {ω | visitTime G c i N T (r + 1) ω ≤ N}
        ⊆ {ω | visitTime G c i N T r ω = s} ∩ {ω | ∀ l ≤ s + T, walk G l ω ≤ c} := by
      rintro ω ⟨h1, h2⟩
      simp only [Set.mem_setOf_eq] at h1 h2
      refine ⟨h1, ?_⟩
      have hnext : visitTime G c i N T (r + 1) ω = nextVisit G c i N (s + T) ω := by
        rw [← h1]
        rfl
      rw [hnext] at h2
      obtain ⟨hge, hmem⟩ := nextVisit_spec h2
      exact survivedGap_forall_le hmem hge
    refine le_trans (measure_mono hincl) ?_
    exact h.measure_inter_survived_le_of hρ0 hρ (hV1 s)
      (measurableSet_prefixAlgebra_visitTime G c i N T r (le_refl s) hsN) hsub
  calc ∑ s ∈ Finset.range (N + 1),
        μ ({ω | visitTime G c i N T r ω = s} ∩ {ω | visitTime G c i N T (r + 1) ω ≤ N})
      ≤ ∑ s ∈ Finset.range (N + 1),
          ENNReal.ofReal (1 - ρ) * μ {ω | visitTime G c i N T r ω = s} :=
        Finset.sum_le_sum hstep
    _ = ENNReal.ofReal (1 - ρ) * ∑ s ∈ Finset.range (N + 1),
          μ {ω | visitTime G c i N T r ω = s} := by rw [Finset.mul_sum]
    _ = ENNReal.ofReal (1 - ρ) * μ {ω | visitTime G c i N T r ω ≤ N} := by
        congr 1
        rw [visitTime_le_eq_biUnion, measure_biUnion_finset ?_ fun s hs =>
          hfibre s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))]
        intro s _ s' _ hss
        exact Set.disjoint_left.mpr fun ω h1 h2 => hss (h1.symm.trans h2)

/-- **Geometric decay**, at any crossing probability `ρ`. -/
theorem IsGaussianWalk.measure_visitTime_le_of (h : IsGaussianWalk G v μ) {c : ℝ}
    {i N T : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ ≤ gaussianReal 0 1 (Set.Ioi 1))
    (hV1 : ∀ s, ((i : ℝ) + 1) ^ 2 ≤ ((∑ m ∈ Finset.Ico s (s + T), v m : ℝ≥0) : ℝ))
    (r : ℕ) :
    μ {ω | visitTime G c i N T r ω ≤ N}
      ≤ ENNReal.ofReal (1 - ρ) ^ r := by
  induction r with
  | zero => simpa using prob_le_one
  | succ r ih =>
      calc μ {ω | visitTime G c i N T (r + 1) ω ≤ N}
          ≤ ENNReal.ofReal (1 - ρ)
              * μ {ω | visitTime G c i N T r ω ≤ N} :=
            h.measure_visitTime_succ_le_of hρ0 hρ hV1 r
        _ ≤ ENNReal.ofReal (1 - ρ)
              * ENNReal.ofReal (1 - ρ) ^ r := by gcongr
        _ = ENNReal.ofReal (1 - ρ) ^ (r + 1) := by ring

/-! ### The covering

Every visit to the band lies within `T` of one of the excursion times: take the last excursion
starting at or before it.  This is where the times are used as *numbers* rather than as events,
which is what the function encoding was chosen for.
-/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The excursion times advance by at least one each step, so the `r`-th is at least `r`. -/
lemma le_visitTime (G : ℕ → Ω → ℝ) (c : ℝ) (i N T : ℕ) (hT : 1 ≤ T) (r : ℕ) (ω : Ω)
    (h : visitTime G c i N T r ω ≤ N) : r ≤ visitTime G c i N T r ω := by
  induction r with
  | zero => exact Nat.zero_le _
  | succ r ih =>
      have hsep := visitTime_succ_ge G c i N T r ω h
      have hr : visitTime G c i N T r ω ≤ N := by omega
      have := ih hr
      omega

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The covering.**  Every visit to the band is within `T` of an excursion time. -/
lemma exists_visitTime_covering (G : ℕ → Ω → ℝ) (c : ℝ) {i N T : ℕ} (hT : 1 ≤ T) {j : ℕ}
    (hjN : j ≤ N) {ω : Ω} (hmem : ω ∈ survivedGap G c i j) :
    ∃ r ≤ N, visitTime G c i N T r ω ≤ j ∧ j < visitTime G c i N T r ω + T := by
  classical
  have hP0 : visitTime G c i N T 0 ω ≤ j := nextVisit_le_of_mem (Nat.zero_le j) hjN hmem
  have hPbound : ∀ r, visitTime G c i N T r ω ≤ j → r ≤ N := by
    intro r hr
    have h1 : visitTime G c i N T r ω ≤ N := le_trans hr hjN
    exact le_trans (le_visitTime G c i N T hT r ω h1) (le_trans hr hjN)
  set r := Nat.findGreatest (fun r => visitTime G c i N T r ω ≤ j) N with hrdef
  have hPr : visitTime G c i N T r ω ≤ j :=
    Nat.findGreatest_spec (P := fun r => visitTime G c i N T r ω ≤ j) (Nat.zero_le N) hP0
  have hnot : ¬ visitTime G c i N T (r + 1) ω ≤ j := by
    intro hcon
    have hle : r + 1 ≤ N := hPbound _ hcon
    exact absurd hcon (Nat.findGreatest_is_greatest
      (P := fun r => visitTime G c i N T r ω ≤ j) (by omega) hle)
  refine ⟨r, hPbound r hPr, hPr, ?_⟩
  by_contra hcon
  push Not at hcon
  refine hnot ?_
  have hnext : visitTime G c i N T (r + 1) ω
      = nextVisit G c i N (visitTime G c i N T r ω + T) ω := rfl
  rw [hnext]
  exact nextVisit_le_of_mem hcon hjN hmem

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- Summing the measures of a finite family of events is integrating how many of them occur. -/
lemma sum_measure_eq_lintegral_card {E : ℕ → Set Ω} (hE : ∀ j, MeasurableSet (E j))
    (s : Finset ℕ) :
    ∑ j ∈ s, μ (E j) = ∫⁻ ω, (((s.filter fun j => ω ∈ E j).card : ℕ) : ℝ≥0∞) ∂μ := by
  calc ∑ j ∈ s, μ (E j)
      = ∑ j ∈ s, ∫⁻ ω, (E j).indicator 1 ω ∂μ :=
        Finset.sum_congr rfl fun j _ => (lintegral_indicator_one (hE j)).symm
    _ = ∫⁻ ω, ∑ j ∈ s, (E j).indicator 1 ω ∂μ :=
        (lintegral_finsetSum _ fun j _ => measurable_one.indicator (hE j)).symm
    _ = ∫⁻ ω, (((s.filter fun j => ω ∈ E j).card : ℕ) : ℝ≥0∞) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : ω ∈ E j
        · rw [if_pos hj, Set.indicator_of_mem hj, Pi.one_apply]
        · rw [if_neg hj, Set.indicator_of_notMem hj]

open scoped Classical in
omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Pointwise, each excursion accounts for at most `T` visits. -/
lemma card_filter_survivedGap_le (G : ℕ → Ω → ℝ) (c : ℝ) {i N T : ℕ} (hT : 1 ≤ T) (ω : Ω) :
    ((Finset.range (N + 1)).filter fun j => ω ∈ survivedGap G c i j).card
      ≤ T * ((Finset.range (N + 1)).filter fun r => visitTime G c i N T r ω ≤ N).card := by
  classical
  have hsub : ((Finset.range (N + 1)).filter fun j => ω ∈ survivedGap G c i j)
      ⊆ ((Finset.range (N + 1)).filter fun r => visitTime G c i N T r ω ≤ N).biUnion
          fun r => Finset.Ico (visitTime G c i N T r ω) (visitTime G c i N T r ω + T) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨r, hrN, h1, h2⟩ := exists_visitTime_covering G c hT (by omega : j ≤ N) hj.2
    refine Finset.mem_biUnion.mpr ⟨r, ?_, Finset.mem_Ico.mpr ⟨h1, h2⟩⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_trans h1 (by omega)⟩
  calc ((Finset.range (N + 1)).filter fun j => ω ∈ survivedGap G c i j).card
      ≤ (((Finset.range (N + 1)).filter fun r => visitTime G c i N T r ω ≤ N).biUnion
          fun r => Finset.Ico (visitTime G c i N T r ω)
            (visitTime G c i N T r ω + T)).card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ (Finset.range (N + 1)).filter fun r => visitTime G c i N T r ω ≤ N,
          (Finset.Ico (visitTime G c i N T r ω) (visitTime G c i N T r ω + T)).card :=
        Finset.card_biUnion_le
    _ = T * ((Finset.range (N + 1)).filter fun r => visitTime G c i N T r ω ≤ N).card := by
        simp [Nat.card_Ico, Finset.sum_const, mul_comm]

open scoped Classical in
omit [IsProbabilityMeasure μ] in
/-- **The occupation of the band, up to the horizon**, is at most `T` times the expected number
of excursions. -/
theorem IsGaussianWalk.sum_measure_survivedGap_le (h : IsGaussianWalk G v μ) (c : ℝ)
    {i N T : ℕ} (hT : 1 ≤ T) :
    ∑ j ∈ Finset.range (N + 1), μ (survivedGap G c i j)
      ≤ (T : ℝ≥0∞) * ∑ r ∈ Finset.range (N + 1), μ {ω | visitTime G c i N T r ω ≤ N} := by
  have hEmeas : ∀ j, MeasurableSet (survivedGap G c i j) := fun j =>
    h.measurableSet_survivedGap c i j
  have hVmeas : ∀ r, MeasurableSet {ω | visitTime G c i N T r ω ≤ N} :=
    fun r => h.measurableSet_visitTime_le c i N T r
  rw [sum_measure_eq_lintegral_card hEmeas, sum_measure_eq_lintegral_card hVmeas,
    ← lintegral_const_mul' _ _ (by simp : (T : ℝ≥0∞) ≠ ⊤)]
  refine lintegral_mono fun ω => ?_
  have hcard := card_filter_survivedGap_le G c hT ω (i := i) (N := N) (T := T)
  have hcast : ((((Finset.range (N + 1)).filter fun j => ω ∈ survivedGap G c i j).card : ℕ)
        : ℝ≥0∞)
      ≤ (((T * ((Finset.range (N + 1)).filter
          fun r => ω ∈ {ω | visitTime G c i N T r ω ≤ N}).card : ℕ)) : ℝ≥0∞) :=
    Nat.cast_le.mpr hcard
  simpa using hcast

/-! ### The occupation estimate

Combining: at most `T` visits per excursion, and geometrically many excursions.  The bound does
not involve the horizon `N`, so it survives the passage to the full sum.
-/

/-- **The occupation estimate, at any crossing probability `ρ`.**  The expected time the walk
spends in the band `[i, i+1)` below the barrier, before crossing it, is at most `T / ρ`, for any
`ρ > 0` below the probability `P(N(0,1) > 1)`. -/
theorem IsGaussianWalk.tsum_measure_survivedGap_le_of (h : IsGaussianWalk G v μ) (c : ℝ)
    {i T : ℕ} (hT : 1 ≤ T) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ENNReal.ofReal ρ ≤ gaussianReal 0 1 (Set.Ioi 1))
    (hV1 : ∀ s, ((i : ℝ) + 1) ^ 2 ≤ ((∑ m ∈ Finset.Ico s (s + T), v m : ℝ≥0) : ℝ)) :
    ∑' j, μ (survivedGap G c i j)
      ≤ (T : ℝ≥0∞) * (ENNReal.ofReal ρ)⁻¹ := by
  have hρ1 : ρ ≤ 1 := ENNReal.ofReal_le_one.1 (le_trans hρ prob_le_one)
  -- for each horizon, the truncated sum is bounded
  have hbdd : ∀ N : ℕ, ∑ j ∈ Finset.range (N + 1), μ (survivedGap G c i j)
      ≤ (T : ℝ≥0∞) * (ENNReal.ofReal ρ)⁻¹ := by
    intro N
    have hgeo : ∑ r ∈ Finset.range (N + 1), ENNReal.ofReal (1 - ρ) ^ r
        ≤ (ENNReal.ofReal ρ)⁻¹ := by
      calc ∑ r ∈ Finset.range (N + 1), ENNReal.ofReal (1 - ρ) ^ r
          ≤ ∑' r : ℕ, ENNReal.ofReal (1 - ρ) ^ r := ENNReal.sum_le_tsum _
        _ = (1 - ENNReal.ofReal (1 - ρ))⁻¹ := ENNReal.tsum_geometric _
        _ = (ENNReal.ofReal ρ)⁻¹ := by
            congr 1
            rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
              ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - ρ)]
            norm_num
    calc ∑ j ∈ Finset.range (N + 1), μ (survivedGap G c i j)
        ≤ (T : ℝ≥0∞) * ∑ r ∈ Finset.range (N + 1), μ {ω | visitTime G c i N T r ω ≤ N} :=
          h.sum_measure_survivedGap_le c hT
      _ ≤ (T : ℝ≥0∞) * ∑ r ∈ Finset.range (N + 1), ENNReal.ofReal (1 - ρ) ^ r := by
          gcongr with r _
          exact h.measure_visitTime_le_of hρ0.le hρ hV1 r
      _ ≤ (T : ℝ≥0∞) * (ENNReal.ofReal ρ)⁻¹ := by gcongr
  -- and the full sum is the supremum of the truncations
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  exact le_trans (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ n))) (hbdd n)

/-! ### Choosing the block length

For variances at least `vmin`, a block of `⌈(i+1)² / vmin⌉` steps has variance at least `(i+1)²`,
which is what the crossing bound needs.  The resulting occupation bound is `≪ (i+1)²`, with the
implied constant depending only on `vmin` and the crossing probability.
-/

/-- The block length used at band `i`. -/
noncomputable def blockLen (vmin : ℝ) (i : ℕ) : ℕ := ⌈((i : ℝ) + 1) ^ 2 / vmin⌉₊

lemma one_le_blockLen {vmin : ℝ} (hvmin : 0 < vmin) (i : ℕ) : 1 ≤ blockLen vmin i := by
  rw [blockLen, Nat.one_le_ceil_iff]
  positivity

lemma blockLen_bounds {vmin : ℝ} (hvmin : 0 < vmin) (i : ℕ) :
    ((i : ℝ) + 1) ^ 2 / vmin ≤ (blockLen vmin i : ℝ) ∧
      (blockLen vmin i : ℝ) ≤ ((i : ℝ) + 1) ^ 2 / vmin + 1 :=
  ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le⟩

lemma blockVar_lower {w : ℕ → ℝ≥0} {vmin : ℝ} (hvmin : 0 < vmin)
    (hlo : ∀ m, vmin ≤ (w m : ℝ)) (i s : ℕ) :
    ((i : ℝ) + 1) ^ 2
      ≤ ((∑ m ∈ Finset.Ico s (s + blockLen vmin i), w m : ℝ≥0) : ℝ) := by
  have hcard : ((Finset.Ico s (s + blockLen vmin i)).card : ℝ) = (blockLen vmin i : ℝ) := by
    rw [Nat.card_Ico]
    congr 1
    omega
  have hsum : (blockLen vmin i : ℝ) * vmin
      ≤ ((∑ m ∈ Finset.Ico s (s + blockLen vmin i), w m : ℝ≥0) : ℝ) := by
    push_cast
    calc (blockLen vmin i : ℝ) * vmin
        = ∑ _m ∈ Finset.Ico s (s + blockLen vmin i), vmin := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ m ∈ Finset.Ico s (s + blockLen vmin i), (w m : ℝ) :=
          Finset.sum_le_sum fun m _ => hlo m
  have hlow := (blockLen_bounds hvmin i).1
  have : ((i : ℝ) + 1) ^ 2 ≤ (blockLen vmin i : ℝ) * vmin := by
    rw [div_le_iff₀ hvmin] at hlow
    linarith
  linarith

/-! ### The band bound from the moment generating function -/

/-- **The band bound from the moment generating function**, at `t = 2/\sqrt{v₊}`:
`(e\sqrt{v₊}/2)·e^{-2i/\sqrt{v₊}}`. -/
noncomputable def bandBoundMgf (vmax : ℝ) (i : ℕ) : ℝ :=
  rexp 1 * √vmax / 2 * rexp (-(2 / √vmax)) ^ i

/-- The band bound holds for every increment variance below `vmax`. -/
lemma integral_posPart_sub_le_bandBoundMgf {V : ℝ≥0} {vmax : ℝ} (hvmax : 0 < vmax)
    (hV : (V : ℝ) ≤ vmax) (i : ℕ) :
    ∫ x, max (x - (i : ℝ)) 0 ∂(gaussianReal 0 V) ≤ bandBoundMgf vmax i := by
  have hs : 0 < √vmax := Real.sqrt_pos.2 hvmax
  have ht : 0 < 2 / √vmax := div_pos two_pos hs
  refine le_trans (integral_posPart_sub_le_mgf V i ht) ?_
  have hvt : (V : ℝ) * (2 / √vmax) ^ 2 / 2 ≤ 2 := by
    have h4 : vmax * (2 / √vmax) ^ 2 = 4 := by
      rw [div_pow, Real.sq_sqrt hvmax.le]
      field_simp
      norm_num
    have hV0 : (0 : ℝ) ≤ V := V.coe_nonneg
    nlinarith [sq_nonneg (2 / √vmax)]
  calc rexp ((V : ℝ) * (2 / √vmax) ^ 2 / 2 - 2 / √vmax * i) / (rexp 1 * (2 / √vmax))
      ≤ rexp (2 - 2 / √vmax * i) / (rexp 1 * (2 / √vmax)) := by
        gcongr
    _ = bandBoundMgf vmax i := by
        rw [bandBoundMgf, ← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add,
          show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        field_simp

/-! ### Summing over the passage times

The overshoot is the sum of the per-passage contributions, and each of those is controlled by
the occupation of the bands.  Interchanging the two sums gives

`E[overshoot] ≤ ∑_i (∑_j P(survived to j, gap in [i, i+1))) · b i`.
-/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- A walk starting at `0` cannot be above a nonnegative barrier at time `0`. -/
lemma passageZ_zero_eq_zero (G : ℕ → Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) (ω : Ω) :
    passageZ G c 0 ω = 0 := by
  have hnot : ω ∉ firstPassage G c 0 := by
    rintro ⟨-, hlt⟩
    rw [walk_zero] at hlt
    simp only [Pi.zero_apply] at hlt
    linarith
  simp [passageZ, Set.indicator_of_notMem hnot]

omit [IsProbabilityMeasure μ] in
/-- **The overshoot, band by band, at any band bound `b`.** -/
theorem IsGaussianWalk.lintegral_overshoot_le_tsum_of (h : IsGaussianWalk G v μ) {c : ℝ}
    (hc : 0 ≤ c) {b : ℕ → ℝ}
    (hb : ∀ j i : ℕ, ∫ x, max (x - i) 0 ∂(gaussianReal 0 (v j)) ≤ b i) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ
      ≤ ∑' i : ℕ, (∑' j : ℕ, μ (survivedGap G c i j))
          * ENNReal.ofReal (b i) := by
  have hsplit : ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ
      = ∑ k ∈ Finset.range (m + 1), ∫⁻ ω, ENNReal.ofReal (passageZ G c k ω) ∂μ := by
    have hpt : (fun ω => ENNReal.ofReal (overshoot G c m ω))
        = fun ω => ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal (passageZ G c k ω) := by
      funext ω
      simp only [overshoot]
      exact ENNReal.ofReal_sum_of_nonneg (fun k _ => passageZ_nonneg G c k ω)
    rw [hpt, lintegral_finsetSum _ fun k _ => (h.measurable_passageZ c k).ennreal_ofReal]
  have hzero : ∫⁻ ω, ENNReal.ofReal (passageZ G c 0 ω) ∂μ = 0 := by
    simp [passageZ_zero_eq_zero G hc]
  rw [hsplit, Finset.sum_range_succ', hzero, add_zero]
  calc ∑ j ∈ Finset.range m, ∫⁻ ω, ENNReal.ofReal (passageZ G c (j + 1) ω) ∂μ
      ≤ ∑ j ∈ Finset.range m,
          ∑' i : ℕ, μ (survivedGap G c i j) * ENNReal.ofReal (b i) :=
        Finset.sum_le_sum fun j _ =>
          h.lintegral_passageZ_le c j fun i => hb j i
    _ ≤ ∑' j : ℕ, ∑' i : ℕ, μ (survivedGap G c i j) * ENNReal.ofReal (b i) :=
        ENNReal.sum_le_tsum _
    _ = ∑' i : ℕ, ∑' j : ℕ, μ (survivedGap G c i j) * ENNReal.ofReal (b i) :=
        ENNReal.tsum_comm
    _ = ∑' i : ℕ, (∑' j : ℕ, μ (survivedGap G c i j)) * ENNReal.ofReal (b i) := by
        exact tsum_congr fun i => ENNReal.tsum_mul_right

/-! ### The occupation constant at any crossing probability -/

/-- The occupation constant at a crossing probability `ρ`: `(1/v₋ + 1)/ρ`. -/
noncomputable def occConstOf (ρ vmin : ℝ) : ℝ := (1 / vmin + 1) / ρ

/-- **The occupation estimate at any crossing probability `ρ`**:
`∑_j P(survived to j, gap in [i, i+1)) ≤ occConstOf ρ v₋ · (i + 1)²`. -/
theorem IsGaussianWalk.tsum_measure_survivedGap_le_occConstOf (h : IsGaussianWalk G v μ) (c : ℝ)
    {vmin : ℝ} (hvmin : 0 < vmin) (hlo : ∀ m, vmin ≤ (v m : ℝ)) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ENNReal.ofReal ρ ≤ gaussianReal 0 1 (Set.Ioi 1)) (i : ℕ) :
    ∑' j, μ (survivedGap G c i j) ≤ ENNReal.ofReal (occConstOf ρ vmin * ((i : ℝ) + 1) ^ 2) := by
  refine le_trans (h.tsum_measure_survivedGap_le_of c (one_le_blockLen hvmin i) hρ0 hρ
    (fun s => blockVar_lower hvmin hlo i s)) ?_
  have hT : (blockLen vmin i : ℝ) ≤ (1 / vmin + 1) * ((i : ℝ) + 1) ^ 2 := by
    have hup := (blockLen_bounds hvmin i).2
    have hone : (1 : ℝ) ≤ ((i : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) i]
    have he : (1 / vmin + 1) * ((i : ℝ) + 1) ^ 2
        = ((i : ℝ) + 1) ^ 2 / vmin + ((i : ℝ) + 1) ^ 2 := by ring
    rw [he]
    linarith
  have hreal : (blockLen vmin i : ℝ) / ρ ≤ occConstOf ρ vmin * ((i : ℝ) + 1) ^ 2 := by
    rw [occConstOf, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hρ0]
    exact hT
  calc (blockLen vmin i : ℝ≥0∞) * (ENNReal.ofReal ρ)⁻¹
      = ENNReal.ofReal ((blockLen vmin i : ℝ) / ρ) := by
        rw [ENNReal.ofReal_div_of_pos hρ0, ENNReal.ofReal_natCast, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (occConstOf ρ vmin * ((i : ℝ) + 1) ^ 2) := ENNReal.ofReal_le_ofReal hreal

/-! ### The expected overshoot from the moment generating function

The crossing probability is taken to be `1/8` (`RMF.le_measure_Ioi_one_gaussianReal_eighth`), and
the band bound comes from the moment generating function, `(e\sqrt{v₊}/2)·e^{-2i/\sqrt{v₊}}`, so
the sum over the bands is geometric.  At `v₋ = 1/16`, `v₊ = 9/2` the constant is `2.4·10³`. -/

/-- `∑_{i ≥ 0} (i+1)² rⁱ = (1+r)/(1-r)³` for `0 ≤ r < 1`. -/
lemma hasSum_succ_sq_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ i) ((1 + r) / (1 - r) ^ 3) := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr
  have h := (h2.mul_left 2).sub h1
  have hne : (1 - r) ≠ 0 := by linarith
  have hfun : (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ i)
      = fun i : ℕ => 2 * ((((i + 2).choose 2 : ℕ) : ℝ) * r ^ i)
          - (((i + 1).choose 1 : ℕ) : ℝ) * r ^ i := by
    funext i
    rw [Nat.cast_choose_two, Nat.choose_one_right]
    push_cast
    ring
  have hval : (1 + r) / (1 - r) ^ 3
      = 2 * (1 / (1 - r) ^ (2 + 1)) - 1 / (1 - r) ^ (1 + 1) := by
    field_simp
    ring
  rw [hfun, hval]
  exact h

/-- **The overshoot constant from the moment generating function**: the occupation
`8(1/v₋ + 1)(i+1)²` at crossing probability `1/8`, against the band bound `(e\sqrt{v₊}/2) rⁱ`,
`r = e^{-2/\sqrt{v₊}}`, summed: `8(1/v₋ + 1)(e\sqrt{v₊}/2)(1+r)/(1-r)³`. -/
noncomputable def overshootConstMgf (vmin vmax : ℝ) : ℝ :=
  8 * (1 / vmin + 1) * (rexp 1 * √vmax / 2)
    * ((1 + rexp (-(2 / √vmax))) / (1 - rexp (-(2 / √vmax))) ^ 3)

lemma overshootConstMgf_nonneg {vmin vmax : ℝ} (hvmin : 0 < vmin) :
    0 ≤ overshootConstMgf vmin vmax := by
  have hr1 : rexp (-(2 / √vmax)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg zero_le_two (Real.sqrt_nonneg _)))
  have h1 : 0 ≤ 1 - rexp (-(2 / √vmax)) := by linarith
  rw [overshootConstMgf]
  have : 0 < 1 / vmin + 1 := by positivity
  positivity

/-- **The expected overshoot at first passage**, bounded by `RMF.overshootConstMgf`. -/
theorem IsGaussianWalk.lintegral_overshoot_le_mgf (h : IsGaussianWalk G v μ) {c : ℝ}
    (hc : 0 ≤ c) {vmin vmax : ℝ} (hvmin : 0 < vmin) (hlo : ∀ m, vmin ≤ (v m : ℝ))
    (hhi : ∀ m, (v m : ℝ) ≤ vmax) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ
      ≤ ENNReal.ofReal (overshootConstMgf vmin vmax) := by
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hlo 0) (hhi 0))
  have hs : 0 < √vmax := Real.sqrt_pos.2 hvmax
  set r := rexp (-(2 / √vmax)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos two_pos hs))
  have hsum := hasSum_succ_sq_mul_pow hr0 hr1
  set C := 8 * (1 / vmin + 1) * (rexp 1 * √vmax / 2) with hCdef
  have hC : 0 ≤ C := by
    have : 0 < 1 / vmin + 1 := by positivity
    positivity
  have hterm : ∀ i : ℕ, occConstOf (1 / 8) vmin * ((i : ℝ) + 1) ^ 2 * bandBoundMgf vmax i
      = C * (((i : ℝ) + 1) ^ 2 * r ^ i) := by
    intro i
    rw [occConstOf, bandBoundMgf, hCdef, hrdef]
    ring
  have hocc0 : ∀ i : ℕ, 0 ≤ occConstOf (1 / 8) vmin * ((i : ℝ) + 1) ^ 2 := fun i => by
    rw [occConstOf]
    have : 0 < 1 / vmin + 1 := by positivity
    positivity
  refine le_trans (h.lintegral_overshoot_le_tsum_of hc
    (fun j i => integral_posPart_sub_le_bandBoundMgf hvmax (hhi j) i) m) ?_
  calc ∑' i : ℕ, (∑' j : ℕ, μ (survivedGap G c i j)) * ENNReal.ofReal (bandBoundMgf vmax i)
      ≤ ∑' i : ℕ, ENNReal.ofReal (occConstOf (1 / 8) vmin * ((i : ℝ) + 1) ^ 2)
          * ENNReal.ofReal (bandBoundMgf vmax i) :=
        ENNReal.tsum_le_tsum fun i => by
          gcongr
          exact h.tsum_measure_survivedGap_le_occConstOf c hvmin hlo (by norm_num)
            le_measure_Ioi_one_gaussianReal_eighth i
    _ = ∑' i : ℕ, ENNReal.ofReal (C * (((i : ℝ) + 1) ^ 2 * r ^ i)) :=
        tsum_congr fun i => by
          rw [← ENNReal.ofReal_mul (hocc0 i), hterm]
    _ = ENNReal.ofReal (∑' i : ℕ, C * (((i : ℝ) + 1) ^ 2 * r ^ i)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (hsum.summable.mul_left C)).symm
    _ = ENNReal.ofReal (overshootConstMgf vmin vmax) := by
        rw [tsum_mul_left, hsum.tsum_eq, overshootConstMgf, hCdef, hrdef]

/-! ### The barrier estimate: (A1) of Harper, upper bound -/

/-- **The barrier estimate with the overshoot constant `RMF.overshootConstMgf`.** -/
theorem IsGaussianWalk.barrierProb_le_of_comparable_mgf (h : IsGaussianWalk G v μ) {c : ℝ}
    (hc : 0 ≤ c) {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n : ℕ} (hn : 1 ≤ n) :
    barrierProb μ G c n
      ≤ (√3 + 5 * ((c + 1) / √(2 * π * vmin)
          + overshootConstMgf vmin vmax / √(π * vmin))) / √n :=
  h.barrierProb_le hc hv.pos hv.lo (overshootConstMgf_nonneg hv.pos)
    (fun m => h.lintegral_overshoot_le_mgf hc hv.pos hv.lo hv.hi m) hn

universe u

/-! ### (A1) of Harper, both bounds

The upper bound above, and the reflection lower bound of `RMF.IsGaussianWalk.le_measure_forall_le`
read as a bound on `barrierProb`, are the two halves of the statement Harper uses.  Note that his
maximum runs over `1 ≤ j ≤ n` while `barrierProb` includes `j = 0`; since `S 0 = 0` and `c ≥ 1`,
the two events agree.
-/

/-- The barrier event grows with the barrier. -/
lemma barrierProb_mono (G : ℕ → Ω → ℝ) {c c' : ℝ} (hcc : c ≤ c') (n : ℕ) :
    barrierProb μ G c n ≤ barrierProb μ G c' n :=
  ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono fun _ hω j hj => (hω j hj).trans hcc)

/-- The reflection lower bound, as a bound on `barrierProb`. -/
theorem IsGaussianWalk.le_barrierProb (h : IsGaussianWalk G v μ) {n : ℕ}
    (hV : (∑ m ∈ Finset.range n, v m) ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    2 * c * rexp (-c ^ 2 / (2 * (∑ m ∈ Finset.range n, v m : ℝ≥0)))
        / √(2 * π * (∑ m ∈ Finset.range n, v m : ℝ≥0))
      ≤ barrierProb μ G c n :=
  (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 (h.le_measure_forall_le hV hc)

end RMF
