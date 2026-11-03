/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperChain
import RMF.Probability.MatchingGaussianPair

/-!
# Lemma 4 at two heights — the slicing grid in two dimensions

Harper's Proposition 7 needs the barrier probability at **two** heights at once, `1/2 + σ` and
`1/2 + σ + it`, and he proves it *"exactly as in the deduction of Lemma 4"*.  This file is that
deduction, for pair-valued increments.

**What carries over unchanged is the grid.**  `RMF.gridPoint` and `RMF.gridIndex`, the covering
`RMF.mem_sliceEvent_gridPoint`, the disjointness `RMF.sliceEvent_gridPoint_disjoint`, the envelope
bound `RMF.abs_gridPoint_le_of_mem_barrierEvent`, and the containment
`RMF.sliceEvent_subset_barrierEvent_widen` are statements about *one* coordinate, and are applied
here coordinate by coordinate, with no two-dimensional analogue.

**Lemma 4's own two theorems do not carry over.**  `RMF.measure_barrierEvent_le` and
`RMF.le_measure_barrierEvent` are typed at real increments and interval cells, so the upper bound
is restated below for pair-valued increments and box cells; the lower bound, at slack `ρ`, is
`RMF.le_measure_barrierEventPair_slack`.  All of them run on one skeleton,
`RMF.mul_measure_le_of_cellwise`: a countable disjoint cover, a cellwise comparison, disjoint
images inside the target.

**Lemma 7's envelope is a fourth root.**  It is `|u_j|, |v_j| ≤ (1/40)(log x_j)^{1/4} + 2`, where
Lemma 3 has a square root.  The statements here take abstract `M` and `M'`, but at Proposition 7's
instantiation `hMM` compares a linear `M j ≈ a + j + h(j)` with `exp((j + θ)/4)/80` rather than
`exp((j + θ)/2)/80`, so it holds at a different threshold in `θ` from Proposition 5's.

## The two barriers may differ, and in the application they do not

The statements below carry separate barriers `u₁, v₁` and `u₂, v₂`, because nothing in the argument
needs them equal.  In Harper's application they are equal: by
`RMF.abs_integral_localLog_tilted_pair_sub_le` the two-fold tilted mean of `localLog w` is
`Re(w ā₁) + Re(w ā₂)`, so coordinate one (at `w = a₁`) has mean `|a₁|² + Re(a₁ā₂)` and coordinate
two (at `w = a₂`) has mean `|a₂|² + Re(a₂ā₁)`.  Since `a₁ = p^{-1/2-σ}` and `a₂ = p^{-1/2-σ-it}`
have the same modulus, **the two drifts are equal**, both `(1 + cos(t log p))·p^{-1-2σ}`, which is
what makes Harper's single pair `(u_j, v_j)` correct.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ### The two-point cell

A cell is a box: each coordinate in its own window, both of width `w m`.  The bridge lemma
`RMF.sliceEventOf_boxCell` says the box slice is the intersection of the two window slices, and
it is what lets every one-dimensional grid lemma be applied here one coordinate at a time. -/

/-- The box cell at index `m`: coordinate one in the window with left endpoint `c m`, coordinate
two in the window with left endpoint `d m`. -/
def boxCell (w c d : ℕ → ℝ) (m : ℕ) : Set (ℝ × ℝ) :=
  Set.Ioc (c m) (c m + w m) ×ˢ Set.Ioc (d m) (d m + w m)

lemma measurableSet_boxCell (w c d : ℕ → ℝ) (m : ℕ) : MeasurableSet (boxCell w c d m) :=
  measurableSet_Ioc.prod measurableSet_Ioc

omit [MeasurableSpace Ω] in
/-- **The box slice is the intersection of the two window slices.** -/
lemma sliceEventOf_boxCell (Z : ℕ → Ω → ℝ × ℝ) (w c d : ℕ → ℝ) (n : ℕ) :
    sliceEventOf Z n (boxCell w c d)
      = sliceEvent (fun m ω => (Z m ω).1) w n c ∩ sliceEvent (fun m ω => (Z m ω).2) w n d := by
  ext ω
  simp only [sliceEventOf, sliceEvent, boxCell, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
  exact ⟨fun h => ⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2⟩,
    fun h m hm => ⟨h.1 m hm, h.2 m hm⟩⟩

/-- **The two-point barrier**: both walks stay in their tubes, for `1 ≤ j ≤ n`. -/
def barrierEventPair (Z : ℕ → Ω → ℝ × ℝ) (n : ℕ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) : Set Ω :=
  barrierEvent (fun m ω => (Z m ω).1) n u₁ v₁ ∩ barrierEvent (fun m ω => (Z m ω).2) n u₂ v₂

private lemma measurable_fst_of {Z : ℕ → Ω → ℝ × ℝ} (hZ : ∀ m, Measurable (Z m)) (m : ℕ) :
    Measurable (fun ω => (Z m ω).1) := measurable_fst.comp (hZ m)

private lemma measurable_snd_of {Z : ℕ → Ω → ℝ × ℝ} (hZ : ∀ m, Measurable (Z m)) (m : ℕ) :
    Measurable (fun ω => (Z m ω).2) := measurable_snd.comp (hZ m)

lemma measurableSet_barrierEventPair {Z : ℕ → Ω → ℝ × ℝ} (hZ : ∀ m, Measurable (Z m)) (n : ℕ)
    (u₁ v₁ u₂ v₂ : ℕ → ℝ) : MeasurableSet (barrierEventPair Z n u₁ v₁ u₂ v₂) :=
  (measurableSet_barrierEvent (measurable_fst_of hZ) n u₁ v₁).inter
    (measurableSet_barrierEvent (measurable_snd_of hZ) n u₂ v₂)

lemma measurableSet_sliceEventOf_boxCell {Z : ℕ → Ω → ℝ × ℝ} (hZ : ∀ m, Measurable (Z m))
    (w c d : ℕ → ℝ) (n : ℕ) : MeasurableSet (sliceEventOf Z n (boxCell w c d)) := by
  rw [sliceEventOf_boxCell]
  exact (measurableSet_sliceEvent (measurable_fst_of hZ) w n c).inter
    (measurableSet_sliceEvent (measurable_snd_of hZ) w n d)

/-! ### Lemma 7's conclusion, as a hypothesis shape

Exactly as `RMF.IsWindowComparison` carries Lemma 3 into Lemma 4 without committing to how it is
proved, `RMF.IsBoxComparison` carries Lemma 7 into what follows.  It is supplied by
`RMF.le_measure_sliceEventOf_of_indep` at `β = ℝ × ℝ`, whose per-block input is
`RMF.le_measure_box_of_swap`. -/

/-- **Lemma 7's conclusion**, as a relation between two laws: for all tuples `c, d` with
`|c m|, |d m| ≤ M m` for `m < n`, `(1-ε)·Q(N ∈ S) ≤ P(Z ∈ S) ≤ (1+ε)·Q(N ∈ S)`, where `Z ∈ S`
means `Z m ∈ (c m, c m + w m] × (d m, d m + w m]` for every `m < n` (`RMF.boxCell`). -/
def IsBoxComparison (P : Measure Ω) (Q : Measure Ω') (Z : ℕ → Ω → ℝ × ℝ) (N : ℕ → Ω' → ℝ × ℝ)
    (w M : ℕ → ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ c d : ℕ → ℝ, (∀ m, m < n → |c m| ≤ M m) → (∀ m, m < n → |d m| ≤ M m) →
    (1 - ε) * (Q (sliceEventOf N n (boxCell w c d))).toReal
        ≤ (P (sliceEventOf Z n (boxCell w c d))).toReal ∧
      (P (sliceEventOf Z n (boxCell w c d))).toReal
        ≤ (1 + ε) * (Q (sliceEventOf N n (boxCell w c d))).toReal

/-! ### The comparison sees the Gaussian side only through its marginals

`RMF.IsBoxComparison` mentions `Q` and `N` **only** inside
`Q (sliceEventOf N n (boxCell w c d))`, and `RMF.measure_sliceEventOf_eq_prod` factorises that
into `∏_m Q (N m ⁻¹' I m)` as soon as the family is independent.  So an independent family is
pinned by its one-dimensional laws: two of them, on different spaces, give every cell tuple the
same mass, and the comparison transfers.

**This is what lets Proposition 7's Gaussian side be rebuilt on another space.**
`RMF.exists_isBoxComparison_steinhaus_of_range` delivers an *abstract* `Q` carrying `iIndepFun`,
while `RMF.proposition7_upper_of_threshold` wants the family in regression form on a product
space — the two do not compose as they stand.  Both have the same `RMF.gaussianPairLaw`
marginals, so this lemma is the bridge, and it is short for a structural reason worth naming:
nothing in `IsBoxComparison` looks at the joint law beyond the cylinder it is stated on. -/

/-- **The box comparison transfers along equal marginal laws.**  Two independent Gaussian families
with the same one-dimensional laws are interchangeable in `RMF.IsBoxComparison`, whatever spaces
they live on.  The laws are asked for only below `n`, which is all the cylinder sees; the Steinhaus
instantiation builds its Gaussian family from one finite set of primes, so its block laws stop
where that set does. -/
theorem IsBoxComparison.congr_law {Ω'' : Type*} [MeasurableSpace Ω'']
    {P : Measure Ω} {Q : Measure Ω'} {Q' : Measure Ω''} {Z : ℕ → Ω → ℝ × ℝ}
    {N : ℕ → Ω' → ℝ × ℝ} {N' : ℕ → Ω'' → ℝ × ℝ} {w M : ℕ → ℝ} {n : ℕ} {ε : ℝ}
    (hN : ∀ m, Measurable (N m)) (hN' : ∀ m, Measurable (N' m))
    (hNi : iIndepFun N Q) (hN'i : iIndepFun N' Q')
    (hlaw : ∀ m, m < n → Q.map (N m) = Q'.map (N' m))
    (h : IsBoxComparison P Q Z N w M n ε) :
    IsBoxComparison P Q' Z N' w M n ε := by
  intro c d hc hd
  have hmeas : ∀ m, MeasurableSet (boxCell w c d m) := measurableSet_boxCell w c d
  have hcell : Q' (sliceEventOf N' n (boxCell w c d))
      = Q (sliceEventOf N n (boxCell w c d)) := by
    rw [measure_sliceEventOf_eq_prod hN'i n hmeas, measure_sliceEventOf_eq_prod hNi n hmeas]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [← Measure.map_apply (hN' m) (hmeas m), ← Measure.map_apply (hN m) (hmeas m),
      hlaw m (Finset.mem_range.1 hm)]
  rw [hcell]
  exact h c d hc hd

/-- **The empty box comparison.**  Over no blocks both slice events are the whole space.  This is
the case `n ≤ ⌊a⌋` of the comparison hypothesis of `RMF.proposition7_upper_of_threshold`, where
the suffix it restarts on is empty. -/
lemma isBoxComparison_zero {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (Z : ℕ → Ω → ℝ × ℝ) (N : ℕ → Ω' → ℝ × ℝ) (w M : ℕ → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) : IsBoxComparison P Q Z N w M 0 ε := by
  intro c d _ _
  have hZ : sliceEventOf Z 0 (boxCell w c d) = Set.univ := by
    ext ω
    simp [sliceEventOf]
  have hN : sliceEventOf N 0 (boxCell w c d) = Set.univ := by
    ext ω
    simp [sliceEventOf]
  rw [hZ, hN, measure_univ, measure_univ]
  simp only [ENNReal.toReal_one, mul_one]
  constructor <;> linarith

/-! ### The grid, indexed by pairs

A cell is named by a pair of one-dimensional grid tuples.  `(Fin n → ℤ) × (Fin n → ℤ)` is still
countable, which is all `RMF.mul_measure_le_of_cellwise` asks of the index. -/

/-- The cell named by a pair of grid tuples. -/
noncomputable def gridBox (w : ℕ → ℝ) (n : ℕ) (k : (Fin n → ℤ) × (Fin n → ℤ)) : ℕ → Set (ℝ × ℝ) :=
  boxCell w (gridPoint w n k.1) (gridPoint w n k.2)

omit [MeasurableSpace Ω] in
/-- Every path lies in the cell its own pair of grid indices names. -/
lemma mem_sliceEventOf_gridBox {Z : ℕ → Ω → ℝ × ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : ∀ m, 0 < w m)
    (ω : Ω) :
    ω ∈ sliceEventOf Z n (gridBox w n
      (gridIndex (fun m ω => (Z m ω).1) w n ω, gridIndex (fun m ω => (Z m ω).2) w n ω)) := by
  rw [gridBox, sliceEventOf_boxCell]
  exact ⟨mem_sliceEvent_gridPoint hw ω, mem_sliceEvent_gridPoint hw ω⟩

omit [MeasurableSpace Ω] in
/-- Distinct pairs of grid tuples name disjoint cells: they differ in some coordinate, and there
the one-dimensional slices are already disjoint. -/
lemma sliceEventOf_gridBox_disjoint {Z : ℕ → Ω → ℝ × ℝ} {w : ℕ → ℝ} {n : ℕ} (hw : ∀ m, 0 < w m)
    {k k' : (Fin n → ℤ) × (Fin n → ℤ)} (hne : k ≠ k') :
    Disjoint (sliceEventOf Z n (gridBox w n k)) (sliceEventOf Z n (gridBox w n k')) := by
  rw [gridBox, gridBox, sliceEventOf_boxCell, sliceEventOf_boxCell]
  by_cases h1 : k.1 = k'.1
  · have h2 : k.2 ≠ k'.2 := fun h => hne (Prod.ext_iff.mpr ⟨h1, h⟩)
    exact (sliceEvent_gridPoint_disjoint (X := fun m ω => (Z m ω).2) hw h2).mono
      Set.inter_subset_right Set.inter_subset_right
  · exact (sliceEvent_gridPoint_disjoint (X := fun m ω => (Z m ω).1) hw h1).mono
      Set.inter_subset_left Set.inter_subset_left

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The containment the upper bound sums over**, one coordinate at a time. -/
lemma sliceEventOf_subset_barrierEventPair_widen {Z : ℕ → Ω → ℝ × ℝ} {Y : ℕ → Ω' → ℝ × ℝ}
    {w c d : ℕ → ℝ} {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {ω : Ω}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hx : ω ∈ sliceEventOf Z n (boxCell w c d)) (hb : ω ∈ barrierEventPair Z n u₁ v₁ u₂ v₂) :
    sliceEventOf Y n (boxCell w c d)
      ⊆ barrierEventPair Y n (fun j => u₁ j - 2) (fun j => v₁ j + 2)
          (fun j => u₂ j - 2) (fun j => v₂ j + 2) := by
  rw [sliceEventOf_boxCell] at hx
  rw [sliceEventOf_boxCell, barrierEventPair]
  exact Set.inter_subset_inter (sliceEvent_subset_barrierEvent_widen hwsum hx.1 hb.1)
    (sliceEvent_subset_barrierEvent_widen hwsum hx.2 hb.2)

/-! ### Wrappers at the grid cell

The lemmas above are stated at a general `boxCell`; the theorem below only ever meets the cell
named by a pair of grid tuples.  Restating them there keeps every unfolding of `gridBox` in one
place. -/

lemma measurableSet_sliceEventOf_gridBox {Z : ℕ → Ω → ℝ × ℝ} (hZ : ∀ m, Measurable (Z m))
    (w : ℕ → ℝ) (n : ℕ) (k : (Fin n → ℤ) × (Fin n → ℤ)) :
    MeasurableSet (sliceEventOf Z n (gridBox w n k)) :=
  measurableSet_sliceEventOf_boxCell hZ w _ _ n

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
lemma sliceEventOf_gridBox_subset_widen {Z : ℕ → Ω → ℝ × ℝ} {Y : ℕ → Ω' → ℝ × ℝ}
    {w : ℕ → ℝ} {n : ℕ} {k : (Fin n → ℤ) × (Fin n → ℤ)} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {ω : Ω}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hx : ω ∈ sliceEventOf Z n (gridBox w n k)) (hb : ω ∈ barrierEventPair Z n u₁ v₁ u₂ v₂) :
    sliceEventOf Y n (gridBox w n k)
      ⊆ barrierEventPair Y n (fun j => u₁ j - 2) (fun j => v₁ j + 2)
          (fun j => u₂ j - 2) (fun j => v₂ j + 2) :=
  sliceEventOf_subset_barrierEventPair_widen hwsum hx hb

/-! ### Lemma 4 at two heights

The upper half of what Harper's *"exactly as in the deduction of Lemma 4"* points at.  It is the
one-dimensional proof with the grid lemmas applied once per coordinate and the cells boxes rather
than intervals; the summation itself is `RMF.mul_measure_le_of_cellwise`, shared with
`RMF.measure_barrierEvent_le` and `RMF.le_measure_barrierEvent`.

`hM0` is load-bearing for the same reason as in one dimension.  `IsBoxComparison` quantifies over
grid tuples confined by `M'`, so a negative `M' m` makes its premise unsatisfiable and the whole
hypothesis vacuous — an inequality between two arbitrary measures would follow.  With `hM0` the
grid point of a barrier path always lands inside `M'`, by
`RMF.abs_gridPoint_le_of_mem_barrierEvent` applied to each coordinate in turn. -/

/-- **Lemma 4 at two heights, upper bound.**  The two-point barrier probability under `P` is at
most the bivariate Gaussian one for both tubes widened by `2`.

The widening is `2` and not `4`: the two coordinates are sliced on the *same* grid width `w`, so
each walk moves by at most `∑_{m<j} w m ≤ 2` within its own cell, independently of the other. -/
theorem measure_barrierEventPair_le {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Z : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' → ℝ × ℝ}
    {w M M' u₁ v₁ u₂ v₂ : ℕ → ℝ} {n : ℕ} {ε : ℝ}
    (hZ : ∀ m, Measurable (Z m)) (hN : ∀ m, Measurable (N m)) (hw : ∀ m, 0 < w m)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM₁ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hM₂ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₂ j ∧ v₂ j ≤ M j) (hε : 0 ≤ ε)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsBoxComparison P Q Z N w M' n ε) :
    (P (barrierEventPair Z n u₁ v₁ u₂ v₂)).toReal
      ≤ (1 + ε) * (Q (barrierEventPair N n (fun j => u₁ j - 2) (fun j => v₁ j + 2)
          (fun j => u₂ j - 2) (fun j => v₂ j + 2))).toReal := by
  classical
  set A := barrierEventPair Z n u₁ v₁ u₂ v₂ with hAdef
  set Bw := barrierEventPair N n (fun j => u₁ j - 2) (fun j => v₁ j + 2)
    (fun j => u₂ j - 2) (fun j => v₂ j + 2) with hBwdef
  set F : ((Fin n → ℤ) × (Fin n → ℤ)) → Set Ω :=
    fun k => A ∩ sliceEventOf Z n (gridBox w n k) with hFdef
  set G : ((Fin n → ℤ) × (Fin n → ℤ)) → Set Ω' :=
    fun k => if (F k).Nonempty then sliceEventOf N n (gridBox w n k) else ∅ with hGdef
  have hFmeas : ∀ k, MeasurableSet (F k) := fun k =>
    (measurableSet_barrierEventPair hZ n u₁ v₁ u₂ v₂).inter
      (measurableSet_sliceEventOf_gridBox hZ w n k)
  have hGmeas : ∀ k, MeasurableSet (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · simpa only [hGdef, if_pos h] using measurableSet_sliceEventOf_gridBox hN w n k
    · simpa only [hGdef, if_neg h] using MeasurableSet.empty
  have hFdisj : Pairwise (Function.onFun Disjoint F) := fun k k' hne =>
    (sliceEventOf_gridBox_disjoint hw hne).mono Set.inter_subset_right Set.inter_subset_right
  have hGdisj : Pairwise (Function.onFun Disjoint G) := by
    intro k k' hne
    simp only [hGdef, Function.onFun]
    split_ifs
    · exact sliceEventOf_gridBox_disjoint hw hne
    all_goals simp
  have hAunion : A = ⋃ k, F k := by
    ext ω
    refine ⟨fun hω => Set.mem_iUnion.mpr ⟨(gridIndex (fun m ω => (Z m ω).1) w n ω,
      gridIndex (fun m ω => (Z m ω).2) w n ω), hω, mem_sliceEventOf_gridBox hw ω⟩, fun h => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact hk.1
  have hconv : ∀ (t : Set Ω) (r : Set Ω'), (P t).toReal ≤ (1 + ε) * (Q r).toReal →
      P t ≤ ENNReal.ofReal (1 + ε) * Q r := by
    intro t r h
    rw [← ENNReal.ofReal_toReal (measure_ne_top P t), ← ENNReal.ofReal_toReal (measure_ne_top Q r),
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal h
  have hGpos : ∀ k, (F k).Nonempty → G k = sliceEventOf N n (gridBox w n k) := by
    intro k h
    simp only [hGdef]
    rw [if_pos h]
  have hslice : ∀ k, P (F k) ≤ ENNReal.ofReal (1 + ε) * Q (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωA, hωs⟩ := h
      have hkeq : k = (gridIndex (fun m ω => (Z m ω).1) w n ω,
          gridIndex (fun m ω => (Z m ω).2) w n ω) := by
        by_contra hne
        exact Set.disjoint_left.mp (sliceEventOf_gridBox_disjoint (Z := Z) hw hne) hωs
          (mem_sliceEventOf_gridBox hw ω)
      have hk₁ : k.1 = gridIndex (fun m ω => (Z m ω).1) w n ω := by rw [hkeq]
      have hk₂ : k.2 = gridIndex (fun m ω => (Z m ω).2) w n ω := by rw [hkeq]
      have henv₁ : ∀ m, m < n → |gridPoint w n k.1 m| ≤ M' m := by
        intro m hm
        rw [hk₁]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hM₁ hMM hωA.1 hm
      have henv₂ : ∀ m, m < n → |gridPoint w n k.2 m| ≤ M' m := by
        intro m hm
        rw [hk₂]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hM₂ hMM hωA.2 hm
      have hup : (P (sliceEventOf Z n (gridBox w n k))).toReal
          ≤ (1 + ε) * (Q (sliceEventOf N n (gridBox w n k))).toReal :=
        (hcmp (gridPoint w n k.1) (gridPoint w n k.2) henv₁ henv₂).2
      rw [hGpos k ⟨ω, hωA, hωs⟩]
      exact le_trans (measure_mono Set.inter_subset_right) (hconv _ _ hup)
    · have : F k = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [this]
  have hGsub : (⋃ k, G k) ⊆ Bw := by
    refine Set.iUnion_subset fun k => ?_
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωA, hωs⟩ := h
      rw [hGpos k ⟨ω, hωA, hωs⟩]
      exact sliceEventOf_gridBox_subset_widen hwsum hωs hωA
    · simp only [hGdef, if_neg h]
      exact Set.empty_subset _
  have key : P A ≤ ENNReal.ofReal (1 + ε) * Q Bw := by
    have h := mul_measure_le_of_cellwise (μ := P) (ν := Q) (S := A) (T := Bw) (a := 1)
      (b := ENNReal.ofReal (1 + ε)) hFmeas hGmeas hFdisj hGdisj hAunion.subset hGsub
      fun k => by rw [one_mul]; exact hslice k
    rwa [one_mul] at h
  have hle := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top Q Bw)) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hle

/-! ### The Gaussian side, and why the square is not free

Proposition 7's answer is the **square** `min{1, a/√n}²`.  Probability Results 1 and 2 are about
*one* Gaussian walk, and two walks give a product only when independent.  The comparison Gaussian
here is not: Lemma 7 matches the covariance `∑_p cos(t log p)/2p^{1+2σ}`, which is not zero, and
it cannot be dropped — the swap would then carry `|Cov|/δ²`, which diverges at the Lindeberg
optimum `δ ≍ x_j^{-1/(8e)}`.

What works is the regression form, in which `RMF.gaussianPairLaw` is written:
`walk₂ j = ∑_{m<j} r_m Z_m + walk_W j` with `W` independent of `Z`.  On the first walk's barrier
`|Z_m| ≤ M_m + M_{m+1}` (`RMF.abs_increment_le_of_mem_barrierEvent`), so the shear is a bounded
additive perturbation, with budget `K = ∑_m |r_m|(M_m + M_{m+1}) = O(e^{-θ/4}/√C)` under Harper's
`x_1 ≥ e^{C/|t|²}`; `RMF.min_one_div_sqrt_add_le` and `RMF.half_min_one_div_sqrt_le` absorb it
into `a`.  The two theorems below are that argument; the one-point probabilities are left to the
caller. -/

omit [MeasurableSpace Ω] in
/-- Two families that agree pointwise have the same barrier event. -/
lemma barrierEvent_congr {X Y : ℕ → Ω → ℝ} (h : ∀ m ω, X m ω = Y m ω) (n : ℕ) (u v : ℕ → ℝ) :
    barrierEvent X n u v = barrierEvent Y n u v := by
  have hXY : X = Y := funext fun m => funext fun ω => h m ω
  rw [hXY]

omit [MeasurableSpace Ω] in
/-- **The shear is bounded on the first walk's barrier.**  Its increments are pinned by the
envelope, so the perturbation of the second walk never exceeds the budget `K` — at any `j ≤ n`,
uniformly. -/
lemma abs_sum_shear_le {Z : ℕ → Ω → ℝ} {r M u v : ℕ → ℝ} {n : ℕ} {K : ℝ} {ω : Ω}
    (hM0 : ∀ j, 0 ≤ M j) (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j)
    (hK : ∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) ≤ K)
    (hb : ω ∈ barrierEvent Z n u v) {j : ℕ} (hjn : j ≤ n) :
    |∑ m ∈ Finset.range j, r m * Z m ω| ≤ K := by
  have hterm : ∀ m ∈ Finset.range j, |r m * Z m ω| ≤ |r m| * (M m + M (m + 1)) := by
    intro m hm
    have hmn : m < n := lt_of_lt_of_le (Finset.mem_range.mp hm) hjn
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_increment_le_of_mem_barrierEvent hM0 hM hb hmn) (abs_nonneg _)
  calc |∑ m ∈ Finset.range j, r m * Z m ω|
      ≤ ∑ m ∈ Finset.range j, |r m * Z m ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range j, |r m| * (M m + M (m + 1)) := Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn)
          fun m _ _ => mul_nonneg (abs_nonneg _) (by linarith [hM0 m, hM0 (m + 1)])
    _ ≤ K := hK

omit [MeasurableSpace Ω] in
private lemma walk_snd_shear {Z W : ℕ → Ω → ℝ} {N : ℕ → Ω → ℝ × ℝ} {r : ℕ → ℝ}
    (hN : ∀ m ω, N m ω = (Z m ω, r m * Z m ω + W m ω)) (j : ℕ) (ω : Ω) :
    walk (fun m ω => (N m ω).2) j ω = (∑ m ∈ Finset.range j, r m * Z m ω) + walk W j ω := by
  rw [walk_apply, walk_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [hN m ω]

omit [MeasurableSpace Ω] in
/-- **The shear decoupling, upper containment.**  The two-point barrier for the sheared pair sits
inside the first walk's barrier intersected with the second walk's barrier *widened by the shear
budget* — and that second walk is independent of the first. -/
theorem barrierEventPair_shear_subset {Z W : ℕ → Ω → ℝ} {N : ℕ → Ω → ℝ × ℝ} {r M : ℕ → ℝ}
    {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {K : ℝ}
    (hN : ∀ m ω, N m ω = (Z m ω, r m * Z m ω + W m ω))
    (hM0 : ∀ j, 0 ≤ M j) (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hK : ∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) ≤ K) :
    barrierEventPair N n u₁ v₁ u₂ v₂
      ⊆ barrierEvent Z n u₁ v₁ ∩ barrierEvent W n (fun j => u₂ j - K) (fun j => v₂ j + K) := by
  have hfst : barrierEvent (fun m ω => (N m ω).1) n u₁ v₁ = barrierEvent Z n u₁ v₁ :=
    barrierEvent_congr (fun m ω => by rw [hN m ω]) n u₁ v₁
  intro ω hω
  have h₁ : ω ∈ barrierEvent Z n u₁ v₁ := hfst ▸ hω.1
  refine ⟨h₁, fun j hj1 hjn => ?_⟩
  have h₂ := hω.2 j hj1 hjn
  rw [Set.mem_Icc, walk_snd_shear hN] at h₂
  have hsh := abs_le.mp (abs_sum_shear_le hM0 hM hK h₁ hjn)
  rw [Set.mem_Icc]
  constructor <;> simp only <;> linarith [h₂.1, h₂.2, hsh.1, hsh.2]

/-! ### The product, where the square appears

`W` independent of `Z` is realised the way `RMF.iIndepFun_sumElim_prod` realises everything else
here: the two walks live on the two factors of a product space, and then the factorisation is
`MeasureTheory.Measure.prod_prod` — no independence API is needed at all, because the intersection
of the two barrier events *is* a rectangle. -/

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
lemma walk_comp_fst (Z : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω × Ω') :
    walk (fun (m : ℕ) (ω : Ω × Ω') => Z m ω.1) j ω = walk Z j ω.1 := by
  rw [walk_apply, walk_apply]

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
lemma walk_comp_snd (W : ℕ → Ω' → ℝ) (j : ℕ) (ω : Ω × Ω') :
    walk (fun (m : ℕ) (ω : Ω × Ω') => W m ω.2) j ω = walk W j ω.2 := by
  rw [walk_apply, walk_apply]

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- The two barrier events on a product space intersect in a rectangle. -/
lemma barrierEvent_inter_eq_prod (Z : ℕ → Ω → ℝ) (W : ℕ → Ω' → ℝ) (n : ℕ)
    (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    barrierEvent (fun (m : ℕ) (ω : Ω × Ω') => Z m ω.1) n u₁ v₁
        ∩ barrierEvent (fun (m : ℕ) (ω : Ω × Ω') => W m ω.2) n u₂ v₂
      = barrierEvent Z n u₁ v₁ ×ˢ barrierEvent W n u₂ v₂ := by
  ext ω
  simp only [barrierEvent, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod,
    walk_comp_fst, walk_comp_snd]

/-- **The two-point Gaussian barrier probability is a product**, on a product space. -/
lemma measure_barrierEvent_inter_prod {Q₁ : Measure Ω} {Q₂ : Measure Ω'} [SFinite Q₂]
    (Z : ℕ → Ω → ℝ) (W : ℕ → Ω' → ℝ) (n : ℕ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    (Q₁.prod Q₂) (barrierEvent (fun (m : ℕ) (ω : Ω × Ω') => Z m ω.1) n u₁ v₁
        ∩ barrierEvent (fun (m : ℕ) (ω : Ω × Ω') => W m ω.2) n u₂ v₂)
      = Q₁ (barrierEvent Z n u₁ v₁) * Q₂ (barrierEvent W n u₂ v₂) := by
  rw [barrierEvent_inter_eq_prod, Measure.prod_prod]

/-! ### Proposition 7's Gaussian side

The upper half.  The right-hand side is a **product of two one-point barrier probabilities**, and
that is the whole content: bound both by the one-point estimate and the answer is
`≪ min{1, a/√n}²`, the square Harper's Proposition 7 asserts.  The barrier of the second factor is
widened by the shear budget `K`. -/

/-- **Proposition 7's Gaussian side, upper bound.** -/
theorem measure_barrierEventPair_shear_le {Q₁ : Measure Ω} {Q₂ : Measure Ω'} [SFinite Q₂]
    {Z : ℕ → Ω → ℝ} {W : ℕ → Ω' → ℝ} {N : ℕ → Ω × Ω' → ℝ × ℝ} {r M : ℕ → ℝ}
    {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {K : ℝ}
    (hN : ∀ m ω, N m ω = (Z m ω.1, r m * Z m ω.1 + W m ω.2))
    (hM0 : ∀ j, 0 ≤ M j) (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hK : ∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) ≤ K) :
    (Q₁.prod Q₂) (barrierEventPair N n u₁ v₁ u₂ v₂)
      ≤ Q₁ (barrierEvent Z n u₁ v₁)
          * Q₂ (barrierEvent W n (fun j => u₂ j - K) (fun j => v₂ j + K)) := by
  refine le_trans (measure_mono
    (barrierEventPair_shear_subset (Z := fun (m : ℕ) (ω : Ω × Ω') => Z m ω.1)
      (W := fun (m : ℕ) (ω : Ω × Ω') => W m ω.2) hN hM0 hM hK)) ?_
  rw [measure_barrierEvent_inter_prod]

/-- **The square, upper half.** -/
theorem toReal_measure_barrierEventPair_shear_le {Q₁ : Measure Ω} {Q₂ : Measure Ω'}
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    {Z : ℕ → Ω → ℝ} {W : ℕ → Ω' → ℝ} {N : ℕ → Ω × Ω' → ℝ × ℝ} {r M : ℕ → ℝ}
    {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {K : ℝ}
    (hN : ∀ m ω, N m ω = (Z m ω.1, r m * Z m ω.1 + W m ω.2))
    (hM0 : ∀ j, 0 ≤ M j) (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hK : ∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) ≤ K) :
    ((Q₁.prod Q₂) (barrierEventPair N n u₁ v₁ u₂ v₂)).toReal
      ≤ (Q₁ (barrierEvent Z n u₁ v₁)).toReal
          * (Q₂ (barrierEvent W n (fun j => u₂ j - K) (fun j => v₂ j + K))).toReal := by
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (measure_barrierEventPair_shear_le hN hM0 hM hK)

/-! ### Proposition 7, modulo the one-point estimates

The chain, in one statement: the two-point comparison at the top, the two-point Lemma 4, the shear
decoupling, the product — and then two **one-dimensional** Gaussian barrier probabilities.  The
square is visible in the right-hand side: it is a product of two factors of the same shape.

**One envelope hypothesis serves both uses, and it is Harper's own.**  `hM₁` asks `M` to dominate
the barrier *widened by 2* — which is what the upper bound needs, since Lemma 4 widens before the
shear sees the increments — and the unwidened form follows from it by `linarith`.  That is not an
extra demand: Lemma 7's envelope is `(1/40)(\log x_j)^{1/4} + 2`, and **the `+ 2` is precisely
this widening**.

`hM₂` is needed only by Lemma 4.  The shear reads the increments of the *first* walk alone, so the
second barrier's envelope never enters it. -/

/-- **Proposition 7's upper bound, modulo the one-point estimates.** -/
theorem measure_barrierEventPair_of_shear_le {Ω'' : Type*} [MeasurableSpace Ω'']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q₁ : Measure Ω'} [IsProbabilityMeasure Q₁]
    {Q₂ : Measure Ω''} [IsProbabilityMeasure Q₂]
    {L : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' × Ω'' → ℝ × ℝ} {Z : ℕ → Ω' → ℝ} {W : ℕ → Ω'' → ℝ}
    {w M M' r : ℕ → ℝ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {n : ℕ} {ε K : ℝ}
    (hL : ∀ m, Measurable (L m)) (hN : ∀ m, Measurable (N m))
    (hshear : ∀ m ω, N m ω = (Z m ω.1, r m * Z m ω.1 + W m ω.2))
    (hw : ∀ m, 0 < w m) (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM₁ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j - 2 ∧ v₁ j + 2 ≤ M j)
    (hM₂ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₂ j ∧ v₂ j ≤ M j)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hK : ∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) ≤ K) (hε0 : 0 ≤ ε)
    (hcmp : IsBoxComparison P (Q₁.prod Q₂) L N w M' n ε) :
    (P (barrierEventPair L n u₁ v₁ u₂ v₂)).toReal
      ≤ (1 + ε) * ((Q₁ (barrierEvent Z n (fun j => u₁ j - 2) (fun j => v₁ j + 2))).toReal
          * (Q₂ (barrierEvent W n (fun j => u₂ j - 2 - K) (fun j => v₂ j + 2 + K))).toReal) := by
  have hplain : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j := fun j h1 h2 =>
    ⟨by linarith [(hM₁ j h1 h2).1], by linarith [(hM₁ j h1 h2).2]⟩
  have hlem4 := measure_barrierEventPair_le hL hN hw hwsum hM0 hplain hM₂ hε0 hMM hcmp
  have hshr := toReal_measure_barrierEventPair_shear_le (Q₁ := Q₁) (Q₂ := Q₂)
    (u₁ := fun j => u₁ j - 2)
    (v₁ := fun j => v₁ j + 2) (u₂ := fun j => u₂ j - 2) (v₂ := fun j => v₂ j + 2)
    hshear hM0 hM₁ hK
  exact le_trans hlem4 (mul_le_mul_of_nonneg_left hshr (by linarith))

/-! ### The two-point product, packaged for Lemma 4

`RMF.isBoxComparison_of_indep` compounds per-block box comparisons into `RMF.IsBoxComparison`, the
interface the Steinhaus instantiation has to meet, so that everything above is independent of how
the comparison is proved — as `RMF.IsWindowComparison` keeps Lemma 4 independent of Lemma 3. -/

/-- **Per-block box comparisons compound into `RMF.IsBoxComparison`**, the joint statement the
two-point Lemma 4 consumes, with the relative errors adding up to `2E`. -/
theorem isBoxComparison_of_indep {P : Measure Ω} {Q : Measure Ω'}
    {Z : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' → ℝ × ℝ} {w M : ℕ → ℝ} {n : ℕ} {ε : ℕ → ℝ} {E : ℝ}
    (hZi : iIndepFun Z P) (hNi : iIndepFun N Q)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2)
    (hcmp : ∀ m, m < n → ∀ c d : ℝ, |c| ≤ M m → |d| ≤ M m →
      (1 - ε m) * (Q (N m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ (P (Z m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal ∧
        (P (Z m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ (1 + ε m) * (Q (N m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal) :
    IsBoxComparison P Q Z N w M n (2 * E) := by
  intro c d hc hd
  exact le_measure_sliceEventOf_of_indep hZi hNi (fun m => measurableSet_boxCell w c d m)
    hε0 hsum hE fun m hm => hcmp m hm (c m) (d m) (hc m hm) (hd m hm)

/-! ### The box mass from below

The input `q` of `RMF.le_measure_box_of_swap`, and the one that has to beat the swap error.
`RMF.le_measure_box_shifted` does the work; two things stand between it and the shape wanted here.

**Half-open against closed.**  `RMF.IsBoxComparison` is stated at `Ioc` boxes, and
`RMF.le_measure_box_shifted` delivers a closed box.  Shrinking `Ioc c (c+h)` to
`Icc (c + h/4) (c + 3h/4)` costs a factor `2` in each width and nothing else.

**The second window carries the shear.**  `RMF.le_measure_box_shifted` asks `2|ρ|h₁ + s h' ≤ h₂`;
at `h₁ = h₂ = h/2`, `h' = h/(4s)` works as soon as `|ρ| ≤ 1/4`, which the correlation, being
`O(e^{-j})`, satisfies.  The corner hypotheses are passed through, with two constants: `C₂` bounds
the sheared corner divided by `s`, and forcing `C₁ = C₂` would multiply the first coordinate's
exponent by `(1/s)² ≈ 16`, after which the box mass would not beat the swap error. -/

/-- **The box mass from below**, for the regression pair, at a half-open box. -/
theorem le_measure_box_pair {Ω'' : Type*} [MeasurableSpace Ω'']
    {Q₁ : Measure Ω'} [IsProbabilityMeasure Q₁] {Q₂ : Measure Ω''} [IsProbabilityMeasure Q₂]
    {Z : Ω' → ℝ} {W : Ω'' → ℝ} {V₁ V₂ : ℝ≥0} (hV₁ : V₁ ≠ 0) (hV₂ : V₂ ≠ 0)
    (hZm : Measurable Z) (hWm : Measurable W)
    (hZlaw : Q₁.map Z = gaussianReal 0 V₁) (hWlaw : Q₂.map W = gaussianReal 0 V₂)
    {m₁ m₂ r s : ℝ} {N : Ω' × Ω'' → ℝ × ℝ}
    (hN : ∀ ω, N ω = (m₁ + Z ω.1, m₂ + (r * Z ω.1 + s * W ω.2)))
    (hs : 0 < s) (hr : |r| ≤ 1 / 4) {h C₁ C₂ c₁ c₂ : ℝ} (hh : 0 < h)
    (hC₁ : |c₁ + h / 4 - m₁| + h / 2 ≤ C₁)
    (hC₂ : |c₂ + h / 4 - m₂ + |r| * (h / 2) - r * (c₁ + h / 4 - m₁)| / s
      + h / (4 * s) ≤ C₂) :
    h / 2 * Real.exp (-C₁ ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁)
        * (h / (4 * s) * Real.exp (-C₂ ^ 2 / (2 * V₂)) / Real.sqrt (2 * Real.pi * V₂))
      ≤ ((Q₁.prod Q₂) (N ⁻¹' (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h)))).toReal := by
  -- the two coordinates, read on the product space
  have hZ'law : (Q₁.prod Q₂).map (fun ω : Ω' × Ω'' => Z ω.1) = gaussianReal 0 V₁ := by
    have hcomp : (fun ω : Ω' × Ω'' => Z ω.1) = Z ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map hZm measurable_fst, map_fst_prod_eq, hZlaw]
  have hW'law : (Q₁.prod Q₂).map (fun ω : Ω' × Ω'' => W ω.2) = gaussianReal 0 V₂ := by
    have hcomp : (fun ω : Ω' × Ω'' => W ω.2) = W ∘ Prod.snd := rfl
    rw [hcomp, ← Measure.map_map hWm measurable_snd, map_snd_prod_eq, hWlaw]
  have hind : IndepFun (fun ω : Ω' × Ω'' => Z ω.1) (fun ω : Ω' × Ω'' => W ω.2)
      (Q₁.prod Q₂) := indepFun_comp_fst_snd Z W
  -- the box mass from below, at the shrunken closed box
  have habs₁ := abs_nonneg (c₁ + h / 4 - m₁)
  have habs₂ := abs_nonneg (c₂ + h / 4 - m₂ + |r| * (h / 2) - r * (c₁ + h / 4 - m₁))
  have hle₁ := neg_abs_le (c₁ + h / 4 - m₁)
  have hle₁' := le_abs_self (c₁ + h / 4 - m₁)
  have hdiv : ∀ x : ℝ, -(|x| / s) ≤ x / s ∧ x / s ≤ |x| / s := by
    intro x
    exact ⟨by rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_abs_le x) hs.le,
      div_le_div_of_nonneg_right (le_abs_self x) hs.le⟩
  obtain ⟨hd₁, hd₂⟩ := hdiv (c₂ + h / 4 - m₂ + |r| * (h / 2) - r * (c₁ + h / 4 - m₁))
  have hq0 : (0 : ℝ) ≤ h / (4 * s) := div_nonneg hh.le (by linarith)
  have hbox := le_measure_box_shifted (μ := Q₁.prod Q₂)
    (Z := fun ω : Ω' × Ω'' => Z ω.1) (W := fun ω : Ω' × Ω'' => W ω.2)
    hV₁ hV₂ hZ'law hW'law (by fun_prop) (by fun_prop) hind
    (m₁ := m₁) (m₂ := m₂) (ρ := r) (s := s) (u₁ := c₁ + h / 4) (h₁ := h / 2)
    (v₁ := c₂ + h / 4) (h₂ := h / 2) (h' := h / (4 * s)) (c₁ := C₁) (c₂ := C₂) hs
    (by
      have hs0 : s ≠ 0 := hs.ne'
      have hsh : s * (h / (4 * s)) = h / 4 := by field_simp
      nlinarith [hr, hh, hsh])
    (by linarith) (by linarith)
    (by linarith [hd₁, hq0]) (by linarith [hd₂, hq0])
  -- the closed box sits inside the half-open one
  have hsub : {ω : Ω' × Ω'' | m₁ + Z ω.1 ∈ Set.Icc (c₁ + h / 4) (c₁ + h / 4 + h / 2)
        ∧ m₂ + (r * Z ω.1 + s * W ω.2) ∈ Set.Icc (c₂ + h / 4) (c₂ + h / 4 + h / 2)}
      ⊆ N ⁻¹' (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h)) := by
    rintro ω ⟨h1, h2⟩
    rw [Set.mem_Icc] at h1 h2
    simp only [Set.mem_preimage, hN ω, Set.mem_prod, Set.mem_Ioc]
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩
  -- transport to `ℝ`
  have hnn₁ : (0 : ℝ)
      ≤ h / 2 * Real.exp (-C₁ ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁) :=
    div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.sqrt_nonneg _)
  have hnn₂ : (0 : ℝ)
      ≤ h / (4 * s) * Real.exp (-C₂ ^ 2 / (2 * V₂)) / Real.sqrt (2 * Real.pi * V₂) :=
    div_nonneg (mul_nonneg hq0 (Real.exp_pos _).le) (Real.sqrt_nonneg _)
  have hfin := le_trans hbox (measure_mono hsub)
  have := ENNReal.toReal_mono (measure_ne_top (Q₁.prod Q₂) _) hfin
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn₁, ENNReal.toReal_ofReal hnn₂] at this

/-! ### The box mass, in law form

`RMF.le_measure_box_pair` bounds the box for a pair given in regression form on a product space;
the block Gaussian is a sum, and what names it is its *law*.

Here the transport is immediate, and for a reason worth stating: `RMF.gaussianPairLaw` **is** the
pushforward of `N(0,V₁) ⊗ N(0,1)` under the regression map, so the law-form statement is the
realisation-form one read at that canonical realisation, with `Z = W = id`.  No new estimate is
needed — only the observation that the definition is already a realisation. -/

/-- **The box mass from below, in law form.** -/
lemma le_toReal_measure_box_gaussianPairLaw {m₁ m₂ V₁ V₂ c : ℝ} (hV₁ : V₁.toNNReal ≠ 0)
    (hs : 0 < Real.sqrt (pairResidVar V₁ V₂ c)) (hr : |pairSlope V₁ c| ≤ 1 / 4)
    {h C₁ C₂ c₁ c₂ : ℝ} (hh : 0 < h)
    (hC₁ : |c₁ + h / 4 - m₁| + h / 2 ≤ C₁)
    (hC₂ : |c₂ + h / 4 - m₂ + |pairSlope V₁ c| * (h / 2)
          - pairSlope V₁ c * (c₁ + h / 4 - m₁)| / Real.sqrt (pairResidVar V₁ V₂ c)
        + h / (4 * Real.sqrt (pairResidVar V₁ V₂ c)) ≤ C₂) :
    h / 2 * Real.exp (-C₁ ^ 2 / (2 * (V₁.toNNReal : ℝ)))
          / Real.sqrt (2 * Real.pi * (V₁.toNNReal : ℝ))
        * (h / (4 * Real.sqrt (pairResidVar V₁ V₂ c)) * Real.exp (-C₂ ^ 2 / 2)
            / Real.sqrt (2 * Real.pi))
      ≤ (gaussianPairLaw m₁ m₂ V₁ V₂ c
          (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h))).toReal := by
  have hlaw : (gaussianPairLaw m₁ m₂ V₁ V₂ c)
        (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h))
      = ((gaussianReal 0 V₁.toNNReal).prod (gaussianReal 0 1))
          ((fun z : ℝ × ℝ => (m₁ + z.1, m₂ + pairSlope V₁ c * z.1
              + Real.sqrt (pairResidVar V₁ V₂ c) * z.2))
            ⁻¹' (Set.Ioc c₁ (c₁ + h) ×ˢ Set.Ioc c₂ (c₂ + h))) := by
    rw [gaussianPairLaw, Measure.map_apply (measurable_gaussianPairMap m₁ m₂ V₁ V₂ c)
      (measurableSet_Ioc.prod measurableSet_Ioc)]
  rw [hlaw]
  have hbox := le_measure_box_pair (Q₁ := gaussianReal 0 V₁.toNNReal)
    (Q₂ := gaussianReal 0 1) (Z := id) (W := id) (V₁ := V₁.toNNReal) (V₂ := 1)
    (m₁ := m₁) (m₂ := m₂) (r := pairSlope V₁ c) (s := Real.sqrt (pairResidVar V₁ V₂ c))
    (N := fun z : ℝ × ℝ => (m₁ + z.1, m₂ + pairSlope V₁ c * z.1
      + Real.sqrt (pairResidVar V₁ V₂ c) * z.2))
    (h := h) (C₁ := C₁) (C₂ := C₂) (c₁ := c₁) (c₂ := c₂)
    hV₁ one_ne_zero measurable_id measurable_id Measure.map_id Measure.map_id
    (fun ω => Prod.ext rfl (by simp only [id_eq]; ring)) hs hr hh hC₁ hC₂
  simpa using hbox

/-! ### The box mass, normalised

The two-point analogue of `RMF.le_measure_Icc_gaussianReal_normalised_of_bounds`, and the estimate
behind `RMF.blockQ₂`: `RMF.rpow_le_exp_neg_sq_div_of_slope` twice, **at two different slopes**.

The first coordinate is the one-point situation verbatim: envelope slope `1/40`, variance bracket
`1/8 ≤ 2V₁ ≤ 9`, and `Aκ² = 8/1600 < 9/1600`, so it buys `x^{-9/1600}`.  The second corner is the
*sheared* one, of slope `(1+|ρ|)/40 ≤ 1/32` at `|ρ| ≤ 1/4`; against `A = 9` that is
`Aκ² = 9/1024`, so it buys `x^{-1/100}`.  Hence the exponent `1/64 = 9/1600 + 1/100`, not `9/800`.

**Where the `1/s` goes.**  The second factor of `RMF.le_toReal_measure_box_gaussianPairLaw` is
`(h/4s)·e^{-C₂²/2}/√(2π)`; with `K = sC₂` it is `(h/4)·e^{-K²/(2s²)}/√(2πs²)`, a Gaussian window at
variance `s² = pairResidVar` with no `1/s` left, so each coordinate pays only its own variance. -/

/-- **The two-point box mass, normalised.**  A box of side `h` inside Harper's envelope carries
mass at least `(h²/8)·x^{-1/64}`. -/
theorem le_toReal_measure_box_gaussianPairLaw_envelope {m₁ m₂ V₁ V₂ cv : ℝ}
    (hV₁l : 1 / 8 ≤ 2 * V₁) (hV₁u : 2 * V₁ ≤ 9)
    (hRl : 1 / 9 ≤ 2 * pairResidVar V₁ V₂ cv) (hRu : 2 * pairResidVar V₁ V₂ cv ≤ 9)
    (hr : |pairSlope V₁ cv| ≤ 1 / 4)
    {h x c d : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hx : 1 ≤ x)
    (henv₁ : |c| + |m₁| + h ≤ 1 / 40 * Real.sqrt (Real.log x) + 2)
    (henv₂ : |d| + |m₂| + h ≤ 1 / 40 * Real.sqrt (Real.log x) + 2)
    (hthr₁ : (8 : ℝ) / 20 * 2 * Real.sqrt (Real.log x) + 8 * 2 ^ 2
        + Real.log (Real.pi * 9) / 2 ≤ (9 - 8) / 1600 * Real.log x)
    (hthr₂ : 2 * 9 * (1 / 32 : ℝ) * 3 * Real.sqrt (Real.log x) + 9 * 3 ^ 2
        + Real.log (Real.pi * 9) / 2
      ≤ (1 / 100 - 9 * (1 / 32 : ℝ) ^ 2) * Real.log x) :
    h ^ 2 / 8 * x ^ (-(1 : ℝ) / 64)
      ≤ (gaussianPairLaw m₁ m₂ V₁ V₂ cv
          (Set.Ioc c (c + h) ×ˢ Set.Ioc d (d + h))).toReal := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hV₁pos : (0 : ℝ) < V₁ := by linarith
  have hR0 : (0 : ℝ) < pairResidVar V₁ V₂ cv := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (pairResidVar V₁ V₂ cv) := Real.sqrt_pos.2 hR0
  have hRs : Real.sqrt (pairResidVar V₁ V₂ cv) ^ 2 = pairResidVar V₁ V₂ cv :=
    Real.sq_sqrt hR0.le
  set s := Real.sqrt (pairResidVar V₁ V₂ cv) with hsdef
  set ρ := pairSlope V₁ cv with hρdef
  set t := Real.sqrt (Real.log x) with htdef
  have ht0 : (0 : ℝ) ≤ t := Real.sqrt_nonneg _
  have hr0 : (0 : ℝ) ≤ |ρ| := abs_nonneg _
  set D := 1 / 40 * t + 2 with hDdef
  have hD0 : (0 : ℝ) < D := by rw [hDdef]; linarith
  set K := (1 + |ρ|) * D + |ρ| / 2 + h / 4 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have : (0 : ℝ) ≤ (1 + |ρ|) * D := mul_nonneg (by linarith) hD0.le
    rw [hKdef]
    linarith
  -- the first corner
  have habs₁ : |c + h / 4 - m₁| ≤ |c| + h / 4 + |m₁| := by
    rw [abs_le]
    constructor <;>
      linarith [neg_abs_le c, le_abs_self c, neg_abs_le m₁, le_abs_self m₁, hh.le]
  -- the second, sheared, corner
  have hin : |ρ * (c + h / 4 - m₁)| ≤ |ρ| * (|c| + h / 4 + |m₁|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left habs₁ hr0
  have hstep : |d + h / 4 - m₂ + |ρ| * (h / 2) - ρ * (c + h / 4 - m₁)|
      ≤ |d| + h / 4 + |m₂| + |ρ| * (h / 2) + |ρ| * (|c| + h / 4 + |m₁|) := by
    rw [abs_le]
    constructor <;>
      linarith [neg_abs_le d, le_abs_self d, neg_abs_le m₂, le_abs_self m₂,
        neg_abs_le (ρ * (c + h / 4 - m₁)), le_abs_self (ρ * (c + h / 4 - m₁)), hin, hr0,
        hh.le, mul_nonneg hr0 hh.le]
  have hp₁ : |ρ| * (|c| + h / 4 + |m₁|) ≤ |ρ| * D :=
    mul_le_mul_of_nonneg_left (by rw [hDdef]; linarith) hr0
  have hp₂ : |ρ| * (h / 2) ≤ |ρ| * (1 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hr0
  have hnum : |d + h / 4 - m₂ + |ρ| * (h / 2) - ρ * (c + h / 4 - m₁)| + h / 4 ≤ K := by
    rw [hKdef]
    have hd₂ : |d| + h / 4 + |m₂| ≤ D := by rw [hDdef]; linarith
    linarith [hstep, hp₁, hp₂]
  -- the box mass from below, at the two corners
  have hbox := le_toReal_measure_box_gaussianPairLaw (m₁ := m₁) (m₂ := m₂)
    (V₁ := V₁) (V₂ := V₂) (c := cv) (h := h) (C₁ := D) (C₂ := K / s) (c₁ := c) (c₂ := d)
    (by simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hV₁pos) hs0 hr hh
    (by rw [hDdef]; linarith [habs₁])
    (by
      have hrw : |d + h / 4 - m₂ + |ρ| * (h / 2) - ρ * (c + h / 4 - m₁)| / s + h / (4 * s)
          = (|d + h / 4 - m₂ + |ρ| * (h / 2) - ρ * (c + h / 4 - m₁)| + h / 4) / s := by
        field_simp
      rw [hrw]
      exact div_le_div_of_nonneg_right hnum hs0.le)
  rw [Real.coe_toNNReal V₁ hV₁pos.le] at hbox
  refine le_trans ?_ hbox
  -- the first factor
  have hf₁ : x ^ (-(9 : ℝ) / 1600)
      ≤ Real.exp (-D ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁) := by
    have hthr₁' : 2 * 8 * (1 / 40 : ℝ) * 2 * Real.sqrt (Real.log x) + 8 * 2 ^ 2
        + Real.log (Real.pi * 9) / 2 ≤ (9 / 1600 - 8 * (1 / 40 : ℝ) ^ 2) * Real.log x := by
      rw [show (9 : ℝ) / 1600 - 8 * (1 / 40 : ℝ) ^ 2 = (9 - 8) / 1600 from by norm_num]
      linarith [hthr₁]
    have h := rpow_le_exp_neg_sq_div_of_slope (V := V₁) (c := D) (C := 2) (x := x)
      (A := 8) (B := 9) (κ := 1 / 40) (E := 9 / 1600) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hx hD0.le (by rw [hDdef, htdef]) hthr₁'
    rw [show (-(9 : ℝ) / 1600) = -((9 : ℝ) / 1600) from by ring]
    exact h
  -- the second factor, at variance `s²`: the `1/s` cancels
  have hf₂ : s * x ^ (-(1 : ℝ) / 100)
      ≤ Real.exp (-(K / s) ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
    have hKenv : K ≤ 1 / 32 * Real.sqrt (Real.log x) + 3 := by
      rw [hKdef, hDdef, htdef]
      nlinarith [hr, hr0, ht0, hh1, hh.le]
    have h := rpow_le_exp_neg_sq_div_of_slope (V := pairResidVar V₁ V₂ cv) (c := K) (C := 3)
      (x := x) (A := 9) (B := 9) (κ := 1 / 32) (E := 1 / 100) (by norm_num) (by norm_num)
      (by linarith) (by linarith) hx hK0 hKenv hthr₂
    have he₂ : -K ^ 2 / (2 * pairResidVar V₁ V₂ cv) = -(K / s) ^ 2 / 2 := by
      rw [← hRs]
      field_simp
    have hd₂ : Real.sqrt (2 * Real.pi * pairResidVar V₁ V₂ cv) = Real.sqrt (2 * Real.pi) * s := by
      rw [hsdef, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [he₂, hd₂] at h
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt (2 * Real.pi) * s)] at h
    rw [show (-(1 : ℝ) / 100) = -((1 : ℝ) / 100) from by ring,
      le_div_iff₀ (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * Real.pi))]
    calc s * x ^ (-((1 : ℝ) / 100)) * Real.sqrt (2 * Real.pi)
        = x ^ (-((1 : ℝ) / 100)) * (Real.sqrt (2 * Real.pi) * s) := by ring
      _ ≤ Real.exp (-(K / s) ^ 2 / 2) := h
  -- assemble
  have hsum : x ^ (-(9 : ℝ) / 1600) * x ^ (-(1 : ℝ) / 100) = x ^ (-(1 : ℝ) / 64) := by
    rw [← Real.rpow_add hx0]
    congr 1
    norm_num
  have hq0 : (0 : ℝ) ≤ h / (4 * s) := div_nonneg hh.le (by linarith)
  have hnn₁ : (0 : ℝ) ≤ h / 2 * x ^ (-(9 : ℝ) / 1600) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)
  have hnn₂ : (0 : ℝ) ≤ h / (4 * s) * (s * x ^ (-(1 : ℝ) / 100)) :=
    mul_nonneg hq0 (mul_nonneg hs0.le (Real.rpow_nonneg hx0.le _))
  have hA₁ : h / 2 * x ^ (-(9 : ℝ) / 1600)
      ≤ h / 2 * (Real.exp (-D ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁)) :=
    mul_le_mul_of_nonneg_left hf₁ (by linarith)
  have hA₂ : h / (4 * s) * (s * x ^ (-(1 : ℝ) / 100))
      ≤ h / (4 * s) * (Real.exp (-(K / s) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_left hf₂ hq0
  calc h ^ 2 / 8 * x ^ (-(1 : ℝ) / 64)
      = h / 2 * x ^ (-(9 : ℝ) / 1600) * (h / (4 * s) * (s * x ^ (-(1 : ℝ) / 100))) := by
        rw [← hsum]
        field_simp
        ring
    _ ≤ h / 2 * (Real.exp (-D ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁))
        * (h / (4 * s) * (Real.exp (-(K / s) ^ 2 / 2) / Real.sqrt (2 * Real.pi))) :=
        mul_le_mul hA₁ hA₂ hnn₂ (le_trans hnn₁ hA₁)
    _ = h / 2 * Real.exp (-D ^ 2 / (2 * V₁)) / Real.sqrt (2 * Real.pi * V₁)
        * (h / (4 * s) * Real.exp (-(K / s) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) := by
        ring

/-! ### The comparison at one block, with `δ` eliminated

The two-point analogue of `RMF.isWindowComparison₁_of_gaussian_family_of_third_moment`, and the
same theorem line for line.  The balance is `δ = T^{1/4}` — the same `δ`, by
`RMF.swap_error_at_quarter`, which is stated for a general constant.  At it
the swap error is `3600·T^{1/4}` and the collar is `4T^{1/4}(1/√(2πV₁) + 1/√(2πV₂))`.  The
one-point version has `450` and one collar term; that is the whole difference between them.

Everything the block Gaussian is asked for is asked of its **law**.  That is what lets the block
Gaussian be a sum of per-prime pairs — which is what the Lindeberg telescope leaves — rather than
something in regression form. -/

/-- **The two-point comparison at one block, with `δ` eliminated.** -/
theorem le_measure_box_of_gaussian_pair_of_third_moment {ι : Type*} {t : Finset ι}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ξ : ι → Ω → ℝ × ℝ} {G : ι → Ω' → ℝ × ℝ}
    (hξm : ∀ i, Measurable (ξ i)) (hGm : ∀ i, Measurable (G i))
    (hξi : iIndepFun ξ P) (hGi : iIndepFun G Q)
    {T w M ε q M₁ M₂ V₁ V₂ Cov : ℝ} (hT : 0 < T)
    (hmξ : ∀ i ∈ t, ∀ j, Integrable (fun ω => quadMonomial j (ξ i ω)) P)
    (hmG : ∀ i ∈ t, ∀ j, Integrable (fun ω => quadMonomial j (G i ω)) Q)
    (hmom : ∀ i ∈ t, ∀ j, (∫ ω, quadMonomial j (ξ i ω) ∂P)
      = ∫ ω, quadMonomial j (G i ω) ∂Q)
    (hLξ : ∀ i ∈ t, Integrable (fun ω => windowLindebergBound (T ^ (1 / 4 : ℝ)) (ξ i ω)) P)
    (hLG : ∀ i ∈ t, Integrable (fun ω => windowLindebergBound (T ^ (1 / 4 : ℝ)) (G i ω)) Q)
    (hξ₁ : ∀ i ∈ t, Integrable (fun ω => |(ξ i ω).1| ^ 3) P)
    (hξ₂ : ∀ i ∈ t, Integrable (fun ω => |(ξ i ω).2| ^ 3) P)
    (hG₁ : ∀ i ∈ t, Integrable (fun ω => |(G i ω).1| ^ 3) Q)
    (hG₂ : ∀ i ∈ t, Integrable (fun ω => |(G i ω).2| ^ 3) Q)
    (hTb : ∑ i ∈ t, ((∫ ω, |(ξ i ω).1| ^ 3 ∂P) + (∫ ω, |(ξ i ω).2| ^ 3 ∂P)
        + (∫ ω, |(G i ω).1| ^ 3 ∂Q) + ∫ ω, |(G i ω).2| ^ 3 ∂Q) ≤ T)
    (hlaw : Q.map (fun ω => ((∑ i ∈ t, (G i ω).1), ∑ i ∈ t, (G i ω).2))
      = gaussianPairLaw M₁ M₂ V₁ V₂ Cov)
    (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) (hCS : Cov ^ 2 ≤ V₁ * V₂)
    (hn₁ : V₁.toNNReal ≠ 0) (hn₂ : V₂.toNNReal ≠ 0) (hq : 0 < q)
    (hqlow : ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      q ≤ (Q ((fun ω => ((∑ i ∈ t, (G i ω).1), ∑ i ∈ t, (G i ω).2))
        ⁻¹' (Set.Ioc c (c + w) ×ˢ Set.Ioc d (d + w)))).toReal)
    (hnum : (3600 + 4 / Real.sqrt (2 * Real.pi * V₁) + 4 / Real.sqrt (2 * Real.pi * V₂))
      * T ^ (1 / 4 : ℝ) ≤ ε * q) :
    ∀ c d : ℝ, |c| ≤ M → |d| ≤ M →
      (1 - ε) * (Q ((fun ω => ((∑ i ∈ t, (G i ω).1), ∑ i ∈ t, (G i ω).2))
            ⁻¹' (Set.Ioc c (c + w) ×ˢ Set.Ioc d (d + w)))).toReal
          ≤ (P ((fun ω => ((∑ i ∈ t, (ξ i ω).1), ∑ i ∈ t, (ξ i ω).2))
            ⁻¹' (Set.Ioc c (c + w) ×ˢ Set.Ioc d (d + w)))).toReal
        ∧ (P ((fun ω => ((∑ i ∈ t, (ξ i ω).1), ∑ i ∈ t, (ξ i ω).2))
            ⁻¹' (Set.Ioc c (c + w) ×ˢ Set.Ioc d (d + w)))).toReal
          ≤ (1 + ε) * (Q ((fun ω => ((∑ i ∈ t, (G i ω).1), ∑ i ∈ t, (G i ω).2))
            ⁻¹' (Set.Ioc c (c + w) ×ˢ Set.Ioc d (d + w)))).toReal := by
  intro c d hc hd
  have hδ : (0 : ℝ) < T ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hT _
  have hXm : Measurable (fun ω => ((∑ i ∈ t, (ξ i ω).1), ∑ i ∈ t, (ξ i ω).2)) :=
    (Finset.measurable_sum t fun i _ => (hξm i).fst).prodMk
      (Finset.measurable_sum t fun i _ => (hξm i).snd)
  have hNm : Measurable (fun ω => ((∑ i ∈ t, (G i ω).1), ∑ i ∈ t, (G i ω).2)) :=
    (Finset.measurable_sum t fun i _ => (hGm i).fst).prodMk
      (Finset.measurable_sum t fun i _ => (hGm i).snd)
  -- the swap, both halves of the sandwich
  obtain ⟨hswU, hswL⟩ := abs_integral_smoothIndicator_pair_sum_sub_le hδ c (c + w) d (d + w)
    hξm hGm hξi hGi hmξ hmG hmom hLξ hLG
  -- the Lindeberg charge, at the balanced `δ`
  have hD : ∑ i ∈ t, ((∫ ω, windowLindebergBound (T ^ (1 / 4 : ℝ)) (ξ i ω) ∂P)
        + ∫ ω, windowLindebergBound (T ^ (1 / 4 : ℝ)) (G i ω) ∂Q)
      ≤ 3600 * T ^ (1 / 4 : ℝ) := by
    refine le_trans (sum_integral_windowLindebergBound_le hδ hLξ hLG hξ₁ hξ₂ hG₁ hG₂ hTb) ?_
    exact le_of_eq (swap_error_at_quarter 3600 hT)
  -- the collar, read off the law
  have hcollar : (Q ((fun ω => ((∑ i ∈ t, (G i ω).1), ∑ i ∈ t, (G i ω).2))
        ⁻¹' (smoothCollar (T ^ (1 / 4 : ℝ)) c (c + w) ×ˢ (Set.univ : Set ℝ)
          ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar (T ^ (1 / 4 : ℝ)) d (d + w)))).toReal
      ≤ 4 * T ^ (1 / 4 : ℝ) / Real.sqrt (2 * Real.pi * V₁)
        + 4 * T ^ (1 / 4 : ℝ) / Real.sqrt (2 * Real.pi * V₂) := by
    have hms : MeasurableSet (smoothCollar (T ^ (1 / 4 : ℝ)) c (c + w) ×ˢ (Set.univ : Set ℝ)
        ∪ (Set.univ : Set ℝ) ×ˢ smoothCollar (T ^ (1 / 4 : ℝ)) d (d + w)) :=
      ((measurableSet_Icc.union measurableSet_Icc).prod MeasurableSet.univ).union
        (MeasurableSet.univ.prod (measurableSet_Icc.union measurableSet_Icc))
    rw [← Measure.map_apply hNm hms, hlaw]
    exact toReal_measure_collar_gaussianPairLaw_le hV₁ hV₂ hCS hn₁ hn₂ c (c + w) d (d + w) hδ.le
  refine le_measure_box_of_swap hXm hNm hδ (le_trans hswU hD) (le_trans hswL hD) hcollar hq
    (hqlow c d hc hd) ?_
  have hs₁ : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi * V₁) := Real.sqrt_nonneg _
  have hs₂ : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi * V₂) := Real.sqrt_nonneg _
  refine le_trans (le_of_eq ?_) hnum
  ring

/-! ### Restarting the two-point barrier

The upper bound cannot use the envelope on all of `[1,n]`, for the reason `RMF.proposition5_upper`
records: `hM₁` would force `M j ≥ a + j + h(j) + 2`, and `M j ≍ (1/80)(log x_j)^{1/4}` is a
constant at `j = 1`, so `a = O(1)` — unsatisfiable for the `a → ∞` of Harper's application.  His
fix, discarding the first `⌊a⌋` steps, transfers without change: the restart is a statement about
one walk at a time, and the two walks restart at the same index.

The comparison does not transfer for free: `RMF.IsBoxComparison` on `[1,n]` controls only grid
points inside `M m`, so the first `k` coordinates cannot be marginalised away.  It is rebuilt from
the per-block data by `RMF.isBoxComparison_shift_of_indep`, the two-point analogue of
`RMF.isWindowComparison_shift_of_indep`. -/

omit [MeasurableSpace Ω] in
/-- **The two-point barrier, restarted at `k`** — one application of
`RMF.barrierEvent_subset_suffix` per coordinate. -/
lemma barrierEventPair_subset_suffix {Z : ℕ → Ω → ℝ × ℝ} {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} :
    barrierEventPair Z n u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => Z (m + k)) (n - k)
          (fun i => u₁ (k + i) - v₁ k) (fun i => v₁ (k + i) - u₁ k)
          (fun i => u₂ (k + i) - v₂ k) (fun i => v₂ (k + i) - u₂ k) :=
  Set.inter_subset_inter (barrierEvent_subset_suffix hk1 hkn)
    (barrierEvent_subset_suffix hk1 hkn)

/-- **The box comparison, restarted at `k`.**  Not derivable from the unshifted one; rebuilt from
the same per-block data, exactly as in one dimension.  The `ε`-budget survives because the
discarded prefix contributes a non-negative amount. -/
theorem isBoxComparison_shift_of_indep {P : Measure Ω} {Q : Measure Ω'}
    {Z : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' → ℝ × ℝ} {w M : ℕ → ℝ} {n k : ℕ} {ε : ℕ → ℝ} {E : ℝ}
    (hZi : iIndepFun Z P) (hNi : iIndepFun N Q) (hkn : k ≤ n)
    (hε0 : ∀ m, m < n → 0 ≤ ε m) (hsum : ∑ m ∈ Finset.range n, ε m ≤ E) (hE : E ≤ 1 / 2)
    (hcmp : ∀ m, m < n → ∀ c d : ℝ, |c| ≤ M m → |d| ≤ M m →
      (1 - ε m) * (Q (N m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ (P (Z m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal ∧
        (P (Z m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal
          ≤ (1 + ε m) * (Q (N m ⁻¹' (Set.Ioc c (c + w m) ×ˢ Set.Ioc d (d + w m)))).toReal) :
    IsBoxComparison P Q (fun m => Z (m + k)) (fun m => N (m + k))
      (fun m => w (m + k)) (fun m => M (m + k)) (n - k) (2 * E) := by
  refine isBoxComparison_of_indep (ε := fun m => ε (m + k))
    (hZi.precomp fun x y h => by omega) (hNi.precomp fun x y h => by omega)
    (fun m hm => hε0 _ (by omega)) ?_ hE (fun m hm => hcmp _ (by omega))
  have hsplit := sum_range_add_shift (f := ε) k (n - k)
  rw [show k + (n - k) = n from by omega] at hsplit
  have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.range k, ε m :=
    Finset.sum_nonneg fun m hm => hε0 m (by have := Finset.mem_range.1 hm; omega)
  linarith

/-! ### Proposition 7, upper bound

**This is the half the restricted second moment (Harper's Key Proposition 5) consumes**: it bounds
a second moment from above, so it needs `P⁽²⁾ ≪ min{1, a/√n}²`.  Harper states Proposition 7 as
`≍`; the lower half is not needed.

Its **Gaussian step is short** — `RMF.measure_barrierEvent_drift_le_of_threshold` drops the lower
barrier and calls Probability Result 1, since there is no comparison in a statement about the
Gaussian walk alone.  Its **Lemma 4 step is long**: the envelope has to dominate the stated
barrier, which contains `a`, so the restart at `k = ⌊a⌋` is unavoidable and the comparison is
supplied along the suffix.

`hMup` carries `+ 2` beyond `RMF.proposition5_upper`'s form, because Lemma 4 widens before the
shear reads the increments.  The shear budget `K` enters only through the constant
`15 + B + K + 10 log 2`; the shape `min{1, a/√n}²` does not depend on it. -/

set_option maxHeartbeats 1000000 in
-- the suffix bookkeeping runs the same envelope inequality at both coordinates, as in
-- `RMF.proposition5_upper`, which raises the limit for the same reason
/-- **Proposition 7, upper bound.**  The two-point barrier probability is at most a constant times
`min\{1, a/√n\}²`. -/
theorem proposition7_upper_of_threshold {Ω'' : Type*} [MeasurableSpace Ω'']
    {Q₁ : Measure Ω'} [IsProbabilityMeasure Q₁] {Q₂ : Measure Ω''} [IsProbabilityMeasure Q₂]
    {G₁ : ℕ → Ω' → ℝ} {vv₁ : ℕ → ℝ≥0} (hG₁ : IsGaussianWalk G₁ vv₁ Q₁)
    {G₂ : ℕ → Ω'' → ℝ} {vv₂ : ℕ → ℝ≥0} (hG₂ : IsGaussianWalk G₂ vv₂ Q₂)
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo₁ : ∀ i, vmin ≤ (vv₁ i : ℝ)) (hvhi₁ : ∀ i, (vv₁ i : ℝ) ≤ vmax)
    (hvlo₂ : ∀ i, vmin ≤ (vv₂ i : ℝ)) (hvhi₂ : ∀ i, (vv₂ i : ℝ) ≤ vmax)
    {C K B : ℝ} (hC : 0 ≤ C) (hK0 : 0 ≤ K) (hB : 0 < B) {R : ℝ} (hR : 1000 ≤ R) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ × ℝ)
        (N : ℕ → Ω' × Ω'' → ℝ × ℝ) (Z : ℕ → Ω' → ℝ) (W : ℕ → Ω'' → ℝ)
        (θ₁ θ₂ w M M' r : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        (∀ m, Measurable (L m)) → (∀ m, Measurable (N m)) →
        (∀ m ω, N m ω = (Z m ω.1, r m * Z m ω.1 + W m ω.2)) →
        (∀ m ω, Z m ω = G₁ m ω + θ₁ m) → (∀ m ω, W m ω = G₂ m ω + θ₂ m) →
        (∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ₁ m) - j| ≤ C) →
        (∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ₂ m) - j| ≤ C) →
        (∀ m, 0 < w m) → (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) → (∀ j, 0 ≤ M j) →
        (∀ j : ℕ, a < (j : ℝ) → j ≤ n →
          (3 + B) * a + B * j + j + 20 * Real.log j + 2 ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        (∑ m ∈ Finset.range n, |r m| * (M m + M (m + 1)) ≤ K) →
        0 ≤ ε → ε ≤ 1 / 2 →
        IsBoxComparison P (Q₁.prod Q₂) (fun m => L (m + ⌊a⌋₊)) (fun m => N (m + ⌊a⌋₊))
          (fun m => w (m + ⌊a⌋₊)) (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) ε →
        max 1 R ≤ a → 4 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (P (barrierEventPair L n (fun j => -a - B * j) (fun j => a + j + hf j)
                (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
            ≤ 3 * (result1Const vmin vmax * (1 + 2 * C)
                * (15 + B + K + 10 * Real.log 2)) ^ 2 * min 1 (a / Real.sqrt n) ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hRC : (1 : ℝ) ≤ result1Const vmin vmax := one_le_result1Const vmin vmax
  intro P hP L N Z W θ₁ θ₂ w M M' r n ε a hf hL hN hshear hZG hWG hθ₁ hθ₂ hw hwsum hM0 hMup
    hMM hK hε0 hε hcmp ha hn4 hbig hbig2 hhf
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have haT : R ≤ a := le_trans (le_max_right _ _) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hn1 : 1 ≤ n := by omega
  have hn4' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) := le_min zero_le_one (by positivity)
  set Kc := 15 + B + K + 10 * Real.log 2 with hKcd
  have hKc1 : (1 : ℝ) ≤ Kc := by rw [hKcd]; linarith [hB.le, hK0, hlog2.le]
  set Ac := result1Const vmin vmax * (1 + 2 * C) * Kc with hAcd
  have hRC0 : (1 : ℝ) ≤ result1Const vmin vmax * (1 + 2 * C) := by nlinarith [hRC, hC]
  have hAc1 : (1 : ℝ) ≤ Ac := by rw [hAcd]; nlinarith [hRC0, hKc1]
  have hAcm : (0 : ℝ) ≤ Ac ^ 2 * min 1 (a / Real.sqrt n) ^ 2 := by positivity
  clear_value Kc Ac
  have hprob : (P (barrierEventPair L n (fun j => -a - B * j) (fun j => a + j + hf j)
      (fun j => -a - B * j) (fun j => a + j + hf j))).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by norm_num) prob_le_one
  rcases le_or_gt (Real.sqrt n) a with htriv | hsmall
  · have hone : min 1 (a / Real.sqrt n) = 1 :=
      min_eq_left (by rw [le_div_iff₀ hsn]; linarith)
    rw [hone]
    nlinarith [hprob, hAc1]
  · set k := ⌊a⌋₊ with hkdef
    have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast ha1)
    have hka : ((k : ℕ) : ℝ) ≤ a := Nat.floor_le ha0
    have hak : a < ((k : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
    have hkn2 : 2 * k ≤ n := by
      have hr : 2 * ((k : ℕ) : ℝ) ≤ (n : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), Real.sqrt_nonneg (n : ℝ)]
      exact_mod_cast hr
    have hkn : k ≤ n := by omega
    have hnk1 : 1 ≤ n - k := by omega
    have hklog : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
    have hlogk_le : Real.log k ≤ a := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) by exact_mod_cast hk1)
      linarith
    have hkR0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hBk : (0 : ℝ) ≤ (1 + B) * (k : ℝ) := mul_nonneg (by linarith) hkR0
    clear_value k
    -- the suffix data
    have hLs : ∀ m, Measurable (L (m + k)) := fun m => hL _
    have hNs : ∀ m, Measurable (N (m + k)) := fun m => hN _
    have hws : ∀ m, 0 < w (m + k) := fun m => hw _
    have hwsums := sum_shift_le (fun m => (hw m).le) hkn hwsum
    have hM0s : ∀ j, 0 ≤ M (k + j) := fun j => hM0 _
    have hMMs : ∀ m, m < n - k → M (k + m) + M (k + (m + 1)) + w (m + k) ≤ M' (m + k) := by
      intro m hm
      have h := hMM (k + m) (by omega)
      rw [show m + k = k + m from Nat.add_comm m k]
      exact h
    have hKs : ∑ m ∈ Finset.range (n - k), |r (m + k)| * (M (k + m) + M (k + (m + 1))) ≤ K := by
      have heq : ∀ m : ℕ, |r (m + k)| * (M (k + m) + M (k + (m + 1)))
          = (fun i => |r i| * (M i + M (i + 1))) (m + k) := by
        intro m
        simp only
        rw [show k + m = m + k from Nat.add_comm k m,
          show k + (m + 1) = m + k + 1 from by omega]
      rw [Finset.sum_congr rfl fun m _ => heq m]
      have hsplit := sum_range_add_shift (f := fun i => |r i| * (M i + M (i + 1))) k (n - k)
      rw [show k + (n - k) = n from by omega] at hsplit
      have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.range k, |r m| * (M m + M (m + 1)) :=
        Finset.sum_nonneg fun m _ => mul_nonneg (abs_nonneg _) (by linarith [hM0 m, hM0 (m + 1)])
      linarith
    -- the envelope at the suffix indices, at the barrier widened by `2`
    have hMs1 : ∀ i, 1 ≤ i → i ≤ n - k →
        -M (k + i) ≤ ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2 ∧
          ((a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ))) + 2 ≤ M (k + i) := by
      intro i hi1 hin
      have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      have hki : a < ((k + i : ℕ) : ℝ) := by push_cast; linarith
      have hkin : k + i ≤ n := by omega
      have henv := hMup (k + i) hki hkin
      have hlogki : Real.log k ≤ Real.log ((k + i : ℕ) : ℝ) := by
        refine Real.log_le_log (by exact_mod_cast hk1) ?_
        push_cast
        linarith
      have hlogki0 : (0 : ℝ) ≤ Real.log ((k + i : ℕ) : ℝ) := le_trans hklog hlogki
      have habs1 := abs_le.1 (hhf k hk1 hkn)
      have habs2 := abs_le.1 (hhf (k + i) (by omega) hkin)
      have hBa : (0 : ℝ) ≤ B * a := mul_nonneg hB.le ha0
      have hBi : (0 : ℝ) ≤ B * (i : ℝ) := mul_nonneg hB.le (Nat.cast_nonneg i)
      push_cast at henv habs2 hlogki hlogki0 ⊢
      rw [show (3 + B) * a = 3 * a + B * a from by ring,
        show B * ((k : ℝ) + (i : ℝ)) = B * (k : ℝ) + B * (i : ℝ) from by ring] at henv
      exact ⟨by linarith [habs1.2, hlogki], by linarith [habs2.2]⟩
    have hMs2 : ∀ i, 1 ≤ i → i ≤ n - k →
        -M (k + i) ≤ (-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k) ∧
          (a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ)) ≤ M (k + i) := by
      intro i hi1 hin
      obtain ⟨h1, h2⟩ := hMs1 i hi1 hin
      exact ⟨by linarith, by linarith⟩
    -- the chain, on the suffix
    have hchain := measure_barrierEventPair_of_shear_le (Q₁ := Q₁) (Q₂ := Q₂)
      (L := fun m => L (m + k)) (N := fun m => N (m + k)) (Z := fun m => Z (m + k))
      (W := fun m => W (m + k)) (w := fun m => w (m + k)) (M := fun j => M (k + j))
      (M' := fun m => M' (m + k)) (r := fun m => r (m + k)) (n := n - k) (K := K)
      (u₁ := fun i => (-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k))
      (v₁ := fun i => (a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ)))
      (u₂ := fun i => (-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k))
      (v₂ := fun i => (a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ)))
      hLs hNs (fun m ω => hshear (m + k) ω) hws hwsums hM0s hMs1 hMs2 hMMs hKs hε0 hcmp
    have hP1 := ENNReal.toReal_mono (measure_ne_top P _)
      (measure_mono (barrierEventPair_subset_suffix (Z := L) (n := n) (k := k)
        (u₁ := fun j => -a - B * (j : ℝ)) (v₁ := fun j => a + (j : ℝ) + hf j)
        (u₂ := fun j => -a - B * (j : ℝ)) (v₂ := fun j => a + (j : ℝ) + hf j) hk1 hkn))
    -- the size conditions along the suffix
    have hnkR : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by
      have h : n ≤ 2 * (n - k) := by omega
      exact_mod_cast h
    have hlogn0 : (0 : ℝ) ≤ Real.log ((n - k : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hnk1)
    have hlognk : Real.log ((n - k : ℕ) : ℝ) ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hnk1) (by exact_mod_cast Nat.sub_le n k)
    have hbig' : 2 * Real.log ((n - k : ℕ) : ℝ) ^ 20 ≤ ((n - k : ℕ) : ℝ) := by
      have hp : Real.log ((n - k : ℕ) : ℝ) ^ 20 ≤ Real.log n ^ 20 := by gcongr
      linarith
    have hbig2' : 2 * Real.log ((n - k : ℕ) : ℝ) ^ 8 ≤ ((n - k : ℕ) : ℝ) * vmin := by
      have hp : Real.log ((n - k : ℕ) : ℝ) ^ 8 ≤ Real.log n ^ 8 := by gcongr
      have hh : (n : ℝ) / 2 * vmin ≤ ((n - k : ℕ) : ℝ) * vmin :=
        mul_le_mul_of_nonneg_right (by linarith) hvmin.le
      linarith
    have hhf' : ∀ j : ℕ, 1 ≤ j → j ≤ n - k →
        |10 * Real.log (j : ℝ)| ≤ 10 * Real.log (j : ℝ) := by
      intro j hj1 _
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 10 * Real.log (j : ℝ))]
    -- the inflated constant, and the two Gaussian factors
    set A1 := 2 * a + (1 + B) * (k : ℝ) + 10 * Real.log k + 10 * Real.log 2 + 2 with hA1d
    clear_value A1
    have hA10 : (0 : ℝ) ≤ A1 := by rw [hA1d]; linarith [hlog2.le]
    have hA1a : max 1 R ≤ A1 := by
      rw [hA1d]
      exact max_le (by linarith [hlog2.le]) (by linarith [hlog2.le])
    have hA1K : max 1 R ≤ A1 + K := le_trans hA1a (by linarith)
    have hvA : ∀ i : ℕ, 1 ≤ i → i ≤ n - k →
        ((a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ))) + 2
          ≤ A1 + 0 + (i : ℝ) + 10 * Real.log (i : ℝ) := by
      intro i hi1 hin
      have habs2 := abs_le.1 (hhf (k + i) (by omega) (by omega))
      have hlog := log_natCast_add_le hk1 hi1
      rw [hA1d]
      push_cast at habs2 hlog ⊢
      linarith [habs2.2, hlog]
    have hvB : ∀ i : ℕ, 1 ≤ i → i ≤ n - k →
        ((a + ((k + i : ℕ) : ℝ) + hf (k + i)) - (-a - B * (k : ℝ))) + 2 + K
          ≤ (A1 + K) + 0 + (i : ℝ) + 10 * Real.log (i : ℝ) := by
      intro i hi1 hin
      linarith [hvA i hi1 hin]
    have hF1 := measure_barrierEvent_drift_le_of_threshold (hG₁.shift k) hvmin (fun i => hvlo₁ (i +
        k))
      (fun i => hvhi₁ (i + k))
      (u := fun i => ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2)
      (by linarith : (0 : ℝ) ≤ 2 * C) le_rfl
      (fun m ω => hZG (m + k) ω) (drift_shift_le hkn hθ₁) hvA hR hA1a hnk1 hbig' hbig2' hhf'
    have hF2 := measure_barrierEvent_drift_le_of_threshold (hG₂.shift k) hvmin (fun i => hvlo₂ (i +
        k))
      (fun i => hvhi₂ (i + k))
      (u := fun i => ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2 - K)
      (by linarith : (0 : ℝ) ≤ 2 * C) le_rfl
      (fun m ω => hWG (m + k) ω) (drift_shift_le hkn hθ₂) hvB hR hA1K hnk1 hbig' hbig2' hhf'
    -- both inflated constants are `≤ Kc · a`, and the suffix rescaling costs `√2`
    have hKa : A1 + K ≤ Kc * a := by
      have h1 : (1 + B) * (k : ℝ) ≤ a + B * a := by
        have h := mul_le_mul_of_nonneg_left hka (by linarith : (0 : ℝ) ≤ 1 + B)
        linarith [h]
      have h2 : 10 * Real.log 2 ≤ 10 * Real.log 2 * a :=
        le_mul_of_one_le_right (by linarith [hlog2.le]) ha1
      have h3 : K ≤ K * a := le_mul_of_one_le_right hK0 ha1
      rw [hA1d, hKcd]
      linarith [h1, h2, h3, hlogk_le, ha1]
    have hres : ∀ A : ℝ, A ≤ Kc * a →
        min 1 (A / Real.sqrt ((n - k : ℕ) : ℝ))
          ≤ Real.sqrt 2 * Kc * min 1 (a / Real.sqrt n) := by
      intro A hAK
      refine le_trans (min_le_min le_rfl ?_) (min_one_div_sqrt_suffix_le hKc1 ha0 hn1 hnk1 ?_)
      · exact div_le_div_of_nonneg_right hAK (Real.sqrt_nonneg _)
      · exact_mod_cast hnkR
    have hr1 := hres A1 (by linarith)
    have hr2 := hres (A1 + K) hKa
    have hSK0 : (0 : ℝ) ≤ Ac * Real.sqrt 2 * min 1 (a / Real.sqrt n) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg 2)) hmin0
    have hRCnn : (0 : ℝ) ≤ result1Const vmin vmax * (1 + 0 + 2 * C) := by
      nlinarith only [hRC, hC]
    have hB1 : (Q₁ (barrierEvent (fun m => Z (m + k)) (n - k)
          (fun i => ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2)
          (fun i => ((a + ((k + i : ℕ) : ℝ) + hf (k + i))
            - (-a - B * (k : ℝ))) + 2))).toReal
        ≤ Ac * Real.sqrt 2 * min 1 (a / Real.sqrt n) :=
      le_trans hF1 (le_trans (mul_le_mul_of_nonneg_left hr1 hRCnn)
        (le_of_eq (by rw [hAcd]; ring)))
    have hB2 : (Q₂ (barrierEvent (fun m => W (m + k)) (n - k)
          (fun i => ((-a - B * ((k + i : ℕ) : ℝ)) - (a + (k : ℝ) + hf k)) - 2 - K)
          (fun i => ((a + ((k + i : ℕ) : ℝ) + hf (k + i))
            - (-a - B * (k : ℝ))) + 2 + K))).toReal
        ≤ Ac * Real.sqrt 2 * min 1 (a / Real.sqrt n) :=
      le_trans hF2 (le_trans (mul_le_mul_of_nonneg_left hr2 hRCnn)
        (le_of_eq (by rw [hAcd]; ring)))
    have hsq2 : (Ac * Real.sqrt 2 * min 1 (a / Real.sqrt n))
        * (Ac * Real.sqrt 2 * min 1 (a / Real.sqrt n))
        = (Real.sqrt 2 * Real.sqrt 2) * (Ac ^ 2 * min 1 (a / Real.sqrt n) ^ 2) := by ring
    rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq2
    have hgen : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        x * y ≤ 2 * (Ac ^ 2 * min 1 (a / Real.sqrt n) ^ 2) →
        (1 + ε) * (x * y) ≤ 3 * Ac ^ 2 * min 1 (a / Real.sqrt n) ^ 2 := by
      intro x y hx hy hxy
      nlinarith only [hxy, hε, hε0, hAcm, mul_nonneg hx hy]
    refine le_trans hP1 (le_trans hchain (hgen _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg ?_))
    rw [← hsq2]
    exact mul_le_mul hB1 hB2 ENNReal.toReal_nonneg hSK0

/-! ### Proposition 7's Gaussian side, built from the laws alone

`RMF.proposition7_upper_of_threshold` asks for the comparison family in **regression form** on a
product space: `N m ω = (Z m ω.1, r m · Z m ω.1 + W m ω.2)` with `Z = G₁ + θ₁`, `W = G₂ + θ₂` and
`G₁, G₂` independent Gaussian walks on the two factors, while
`RMF.exists_isBoxComparison_steinhaus_of_range` delivers an *abstract* space with the per-block
`RMF.gaussianPairLaw`s.  They compose through the laws: `RMF.exists_gaussian_pair_regression`
realises any family of `gaussianPairLaw`s in regression form, and `RMF.IsBoxComparison.congr_law`
moves the comparison onto it.

**One thing is not read off.**  Matching against `gaussianPairLaw m₁ m₂ V₁ V₂ c` gives `θ₁ = m₁`
and `r = ρ = c/V₁`, but `θ₂ = m₂ - ρ m₁`: the shear carries the first coordinate's drift into the
second.  So the second drift hypothesis is about `∑(m₂ - ρm₁)`, and needs `∑|ρ_m|` controlled as
well as `∑m₂`; in the application `ρ_m` is the block covariance over the block variance
(`RMF.abs_blockMatchedCov_sub_le`).  No variance hypothesis is needed: `Real.sqrt` clips a negative
`RMF.pairResidVar`, and the walk carries `(√x)² = x⁺`. -/

/-- `(√x)² = x⁺`, which is the sheared walk's variance whether or not `pairResidVar` is
non-negative. -/
lemma sq_sqrt_eq_coe_toNNReal (x : ℝ) :
    Real.sqrt x ^ 2 = ((x.toNNReal : ℝ≥0) : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [Real.sq_sqrt hx, Real.coe_toNNReal x hx]
  · rw [Real.sqrt_eq_zero'.2 hx.le, Real.toNNReal_of_nonpos hx.le]
    norm_num

/-- **Proposition 7's Gaussian side, realised from a family of laws.**  Every piece of data the
proposition asks for on the Gaussian side, produced from the five parameter sequences alone. -/
theorem exists_gaussianWalk_pair_regression (m₁ m₂ V₁ V₂ cv : ℕ → ℝ) :
    ∃ (Ω₁ Ω₂ : Type) (_ : MeasurableSpace Ω₁) (_ : MeasurableSpace Ω₂)
      (Q₁ : Measure Ω₁) (Q₂ : Measure Ω₂) (G₁ Z : ℕ → Ω₁ → ℝ) (G₂ W : ℕ → Ω₂ → ℝ)
      (N : ℕ → Ω₁ × Ω₂ → ℝ × ℝ),
      IsProbabilityMeasure Q₁ ∧ IsProbabilityMeasure Q₂ ∧
        IsGaussianWalk G₁ (fun i => (V₁ i).toNNReal) Q₁ ∧
        IsGaussianWalk G₂ (fun i => (pairResidVar (V₁ i) (V₂ i) (cv i)).toNNReal) Q₂ ∧
        (∀ i, Measurable (N i)) ∧ iIndepFun N (Q₁.prod Q₂) ∧
        (∀ i ω, N i ω = (Z i ω.1, pairSlope (V₁ i) (cv i) * Z i ω.1 + W i ω.2)) ∧
        (∀ i ω, Z i ω = G₁ i ω + m₁ i) ∧
        (∀ i ω, W i ω = G₂ i ω + (m₂ i - pairSlope (V₁ i) (cv i) * m₁ i)) ∧
        ∀ i, (Q₁.prod Q₂).map (N i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (cv i) := by
  obtain ⟨Ω₁, Ω₂, mΩ₁, mΩ₂, Q₁, Q₂, Zr, Wr, hQ₁, hQ₂, hZm, hWm, hZi, hWi, hZlaw, hWlaw,
    hNi, hNlaw⟩ := exists_gaussian_pair_regression m₁ m₂ V₁ V₂ cv
  refine ⟨Ω₁, Ω₂, mΩ₁, mΩ₂, Q₁, Q₂, Zr, fun i ω => m₁ i + Zr i ω,
    (fun i ω => Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * Wr i ω),
    (fun i ω => m₂ i - pairSlope (V₁ i) (cv i) * m₁ i
      + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * Wr i ω),
    (fun i ω => (m₁ i + Zr i ω.1, m₂ i + pairSlope (V₁ i) (cv i) * Zr i ω.1
      + Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * Wr i ω.2)),
    hQ₁, hQ₂, ⟨hZm, hZi, hZlaw⟩, ?_, ?_, hNi, ?_, fun i ω => by ring, fun i ω => by ring,
    hNlaw⟩
  · -- the sheared walk: a constant multiple of a standard Gaussian walk
    refine ⟨fun i => (hWm i).const_mul _,
      hWi.comp (fun i => fun x : ℝ => Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * x)
        (fun i => measurable_id.const_mul _), fun i => ?_⟩
    have hcomp : (fun ω => Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * Wr i ω)
        = (fun x : ℝ => Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * x) ∘ Wr i := rfl
    have hmul : Measurable
        (fun x : ℝ => Real.sqrt (pairResidVar (V₁ i) (V₂ i) (cv i)) * x) := by fun_prop
    rw [hcomp, ← Measure.map_map hmul (hWm i), hWlaw i, gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]
      refine NNReal.coe_injective ?_
      simpa using sq_sqrt_eq_coe_toNNReal (pairResidVar (V₁ i) (V₂ i) (cv i))
  · intro i
    have h₁ := hZm i
    have h₂ := hWm i
    fun_prop
  · intro i ω
    simp only [Prod.mk.injEq, true_and]
    ring

/-! ### Proposition 7, against the laws

`RMF.proposition7_upper_of_threshold` is stated on the realisation; this is the same theorem
stated on the **laws**, which is what `RMF.exists_isBoxComparison_steinhaus_of_range` produces.
Its Gaussian input is an independent family with prescribed `RMF.gaussianPairLaw` marginals — no
product space, no regression form, no Gaussian walks — and its drift and shear hypotheses are
phrased in the five parameter sequences.

Two of those hypotheses are not what the realisation-side statement asks for:

* the **second drift** is about `∑(m₂ - ρm₁)`, not `∑m₂` — see the section above;
* the **shear budget** weights `|ρ_m|` by `M_m + M_{m+1}`, so `M` must be chosen **free of `a`**.
  `hMup` is required only for `a < j`, where `(3+B)a < (3+B)j`, so `M j = (4+2B)j + 20 log j + 2`
  meets it; `M j = (3+B)a + Bj + j + …` also meets it but makes `K` grow like `a`. -/

/-- **The envelope Proposition 7's pair form wants**: `(4 + 2B)·j + 20 log j + 2`, with no `a`.
`hMup` is required only for `a < j`, where `(3+B)a < (3+B)j`, so the `a` can be traded for a `j`;
an `a` here would make the shear budget `∑ |r_m|(M_m + M_{m+1})` grow with `a`. -/
noncomputable def boxEnvelope (B : ℝ) (j : ℕ) : ℝ :=
  (4 + 2 * B) * j + 20 * Real.log j + 2

/-- **The envelope meets all three constraints at once**: non-negative, dominating Proposition 7's
`hMup` above `a`, and linear in the block index so that the shear budget converges.  Stating the
three together is the point — the second and third pull in opposite directions, and the whole
content of the `a`-free choice is that they can be met simultaneously. -/
lemma boxEnvelope_spec {B : ℝ} (hB : 0 < B) (a : ℝ) :
    (∀ j, 0 ≤ boxEnvelope B j)
      ∧ (∀ j : ℕ, a < (j : ℝ) →
          (3 + B) * a + B * j + j + 20 * Real.log j + 2 ≤ boxEnvelope B j)
      ∧ ∀ m : ℕ, boxEnvelope B m + boxEnvelope B (m + 1)
          ≤ (52 + 4 * B) * ((m : ℝ) + 1) := by
  have hlog : ∀ j : ℕ, Real.log j ≤ (j : ℝ) := by
    intro j
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (j : ℝ) by linarith)]
  have hlog0 : ∀ j : ℕ, 0 ≤ Real.log j := by
    intro j
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  refine ⟨fun j => ?_, fun j hj => ?_, fun m => ?_⟩
  · rw [boxEnvelope]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [hlog0 j, hB]
  · rw [boxEnvelope]
    nlinarith [hj, hB]
  · rw [boxEnvelope, boxEnvelope]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [hlog m, hlog (m + 1), hcast ▸ hlog (m + 1), hm0, hB]

/-- **Proposition 7, upper bound, from the laws.**  The two-point barrier probability is at most a
constant times `\min\{1, a/√n\}²`, with the Gaussian side given as an independent family of
prescribed bivariate laws rather than as a realisation. -/
theorem proposition7_upper_of_law_of_threshold {Q : Measure Ω'} {N₀ : ℕ → Ω' → ℝ × ℝ}
    {m₁ m₂ V₁ V₂ cv : ℕ → ℝ}
    (hN₀m : ∀ i, Measurable (N₀ i)) (hN₀i : iIndepFun N₀ Q)
    {nlaw : ℕ}
    (hN₀law : ∀ i, i < nlaw →
      Q.map (N₀ i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (cv i))
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo₁ : ∀ i, vmin ≤ V₁ i) (hvhi₁ : ∀ i, V₁ i ≤ vmax)
    (hvlo₂ : ∀ i, vmin ≤ pairResidVar (V₁ i) (V₂ i) (cv i))
    (hvhi₂ : ∀ i, pairResidVar (V₁ i) (V₂ i) (cv i) ≤ vmax)
    {C K B : ℝ} (hC : 0 ≤ C) (hK0 : 0 ≤ K) (hB : 0 < B) {R : ℝ} (hR : 1000 ≤ R) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ × ℝ)
        (w M M' : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        n ≤ nlaw →
        (∀ m, Measurable (L m)) →
        (∀ j, j ≤ n → |(∑ i ∈ Finset.range j, m₁ i) - j| ≤ C) →
        (∀ j, j ≤ n →
          |(∑ i ∈ Finset.range j, (m₂ i - pairSlope (V₁ i) (cv i) * m₁ i)) - j| ≤ C) →
        (∀ m, 0 < w m) → (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) → (∀ j, 0 ≤ M j) →
        (∀ j : ℕ, a < (j : ℝ) → j ≤ n →
          (3 + B) * a + B * j + j + 20 * Real.log j + 2 ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        (∑ m ∈ Finset.range n, |pairSlope (V₁ m) (cv m)| * (M m + M (m + 1)) ≤ K) →
        0 ≤ ε → ε ≤ 1 / 2 →
        IsBoxComparison P Q (fun m => L (m + ⌊a⌋₊)) (fun m => N₀ (m + ⌊a⌋₊))
          (fun m => w (m + ⌊a⌋₊)) (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) ε →
        max 1 R ≤ a → 4 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (P (barrierEventPair L n (fun j => -a - B * j) (fun j => a + j + hf j)
                (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
            ≤ 3 * (result1Const vmin vmax * (1 + 2 * C)
                * (15 + B + K + 10 * Real.log 2)) ^ 2 * min 1 (a / Real.sqrt n) ^ 2 := by
  obtain ⟨Ω₁, Ω₂, mΩ₁, mΩ₂, Q₁, Q₂, G₁, Z, G₂, W, N, hQ₁, hQ₂, hG₁, hG₂, hNm, hNi, hshear,
    hZG, hWG, hNlaw⟩ := exists_gaussianWalk_pair_regression m₁ m₂ V₁ V₂ cv
  intro P hP L w M M' n ε a hf hnlaw hL hd₁ hd₂ hw hwsum hM0 hMup hMM hK hε0 hε hcmp ha hn4
    hbig hbig2 hhf
  have hcoe : ∀ x : ℝ, vmin ≤ x → (((x.toNNReal : ℝ≥0)) : ℝ) = x :=
    fun x hx => Real.coe_toNNReal x (le_trans hvmin.le hx)
  have hlo₁ : ∀ i, vmin ≤ (((V₁ i).toNNReal : ℝ≥0) : ℝ) := by
    intro i; rw [hcoe _ (hvlo₁ i)]; exact hvlo₁ i
  have hhi₁ : ∀ i, (((V₁ i).toNNReal : ℝ≥0) : ℝ) ≤ vmax := by
    intro i; rw [hcoe _ (hvlo₁ i)]; exact hvhi₁ i
  have hlo₂ : ∀ i, vmin ≤ (((pairResidVar (V₁ i) (V₂ i) (cv i)).toNNReal : ℝ≥0) : ℝ) := by
    intro i; rw [hcoe _ (hvlo₂ i)]; exact hvlo₂ i
  have hhi₂ : ∀ i, (((pairResidVar (V₁ i) (V₂ i) (cv i)).toNNReal : ℝ≥0) : ℝ) ≤ vmax := by
    intro i; rw [hcoe _ (hvlo₂ i)]; exact hvhi₂ i
  -- the comparison, moved onto the realisation
  have hcmp' : IsBoxComparison P (Q₁.prod Q₂) (fun m => L (m + ⌊a⌋₊)) (fun m => N (m + ⌊a⌋₊))
      (fun m => w (m + ⌊a⌋₊)) (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) ε :=
    hcmp.congr_law (fun m => hN₀m _) (fun m => hNm _)
      (hN₀i.precomp fun _ _ hab => by omega) (hNi.precomp fun _ _ hab => by omega)
      (fun m hm => by rw [hN₀law _ (by omega), hNlaw])
  haveI := hQ₁
  haveI := hQ₂
  exact proposition7_upper_of_threshold hG₁ hG₂ hvmin hlo₁ hhi₁ hlo₂ hhi₂ hC hK0 hB hR
    P hP L N Z W m₁ (fun i => m₂ i - pairSlope (V₁ i) (cv i) * m₁ i) w M M'
    (fun i => pairSlope (V₁ i) (cv i)) n ε a hf hL hNm hshear hZG hWG hd₁ hd₂ hw hwsum hM0
    hMup hMM hK hε0 hε hcmp' ha hn4 hbig hbig2 hhf

/-- **Proposition 7, upper bound, from the law**, at Result 1's lower threshold
`RMF.result1Threshold`. -/
theorem proposition7_upper_of_law {Q : Measure Ω'} {N₀ : ℕ → Ω' → ℝ × ℝ}
    {m₁ m₂ V₁ V₂ cv : ℕ → ℝ}
    (hN₀m : ∀ i, Measurable (N₀ i)) (hN₀i : iIndepFun N₀ Q)
    {nlaw : ℕ}
    (hN₀law : ∀ i, i < nlaw →
      Q.map (N₀ i) = gaussianPairLaw (m₁ i) (m₂ i) (V₁ i) (V₂ i) (cv i))
    {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hvlo₁ : ∀ i, vmin ≤ V₁ i) (hvhi₁ : ∀ i, V₁ i ≤ vmax)
    (hvlo₂ : ∀ i, vmin ≤ pairResidVar (V₁ i) (V₂ i) (cv i))
    (hvhi₂ : ∀ i, pairResidVar (V₁ i) (V₂ i) (cv i) ≤ vmax)
    {C K B : ℝ} (hC : 0 ≤ C) (hK0 : 0 ≤ K) (hB : 0 < B) :
      ∀ (P : Measure Ω) (_ : IsProbabilityMeasure P) (L : ℕ → Ω → ℝ × ℝ)
        (w M M' : ℕ → ℝ) (n : ℕ) (ε a : ℝ) (hf : ℕ → ℝ),
        n ≤ nlaw →
        (∀ m, Measurable (L m)) →
        (∀ j, j ≤ n → |(∑ i ∈ Finset.range j, m₁ i) - j| ≤ C) →
        (∀ j, j ≤ n →
          |(∑ i ∈ Finset.range j, (m₂ i - pairSlope (V₁ i) (cv i) * m₁ i)) - j| ≤ C) →
        (∀ m, 0 < w m) → (∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2) → (∀ j, 0 ≤ M j) →
        (∀ j : ℕ, a < (j : ℝ) → j ≤ n →
          (3 + B) * a + B * j + j + 20 * Real.log j + 2 ≤ M j) →
        (∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) →
        (∑ m ∈ Finset.range n, |pairSlope (V₁ m) (cv m)| * (M m + M (m + 1)) ≤ K) →
        0 ≤ ε → ε ≤ 1 / 2 →
        IsBoxComparison P Q (fun m => L (m + ⌊a⌋₊)) (fun m => N₀ (m + ⌊a⌋₊))
          (fun m => w (m + ⌊a⌋₊)) (fun m => M' (m + ⌊a⌋₊)) (n - ⌊a⌋₊) ε →
        max 1 (result1Threshold vmin vmax) ≤ a → 4 ≤ n →
        4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * vmin →
        (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
          (P (barrierEventPair L n (fun j => -a - B * j) (fun j => a + j + hf j)
                (fun j => -a - B * j) (fun j => a + j + hf j))).toReal
            ≤ 3 * (result1Const vmin vmax * (1 + 2 * C)
                * (15 + B + K + 10 * Real.log 2)) ^ 2 * min 1 (a / Real.sqrt n) ^ 2 :=
  proposition7_upper_of_law_of_threshold hN₀m hN₀i hN₀law hvmin hvlo₁ hvhi₁ hvlo₂ hvhi₂ hC hK0 hB
    (thousand_le_result1Threshold vmin vmax)

end RMF
