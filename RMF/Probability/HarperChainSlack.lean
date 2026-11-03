/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.HarperChainPair

/-!
# Lemma 4 at slack `ρ`

Lemma 4 (`RMF.measure_barrierEvent_le`, `RMF.le_measure_barrierEvent`) and its two-point upper
bound (`RMF.measure_barrierEventPair_le`) cap the window sum `∑_{m<j} w m` at `2` and move the
barrier by `2`: Harper's `± 2`, for his windows `1/(m+1)²`.  The proofs use the `2` only through
the containment of a slice in the moved barrier, and that holds for any cap `ρ`; in the lower
bounds, `0 ≤ ρ` is the cap at `j = 0`.

At the windows `ε_w/(m+1)²` the cap is `2ε_w` (`RMF.sum_mul_blockWindow_le`), so the shift of the
barrier drops from `2` to `2ε_w`.

Every proof here is the corresponding one of Lemma 4 with `2` replaced by `ρ`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ### One point -/

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The upper containment at slack `ρ`**: `RMF.sliceEvent_subset_barrierEvent_widen` with the
window sum capped at `ρ` and the barrier widened by `ρ`. -/
lemma sliceEvent_subset_barrierEvent_widen_slack {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {w : ℕ → ℝ}
    {n : ℕ} {c u v : ℕ → ℝ} {ω : Ω} {ρ : ℝ}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hx : ω ∈ sliceEvent X w n c) (hb : ω ∈ barrierEvent X n u v) :
    sliceEvent Y w n c ⊆ barrierEvent Y n (fun j => u j - ρ) (fun j => v j + ρ) := by
  intro ω' hy j hj1 hjn
  have hd := abs_sub_le_iff.mp ((abs_walk_sub_walk_le hx hy hjn).trans (hwsum j hjn))
  have hbj := hb j hj1 hjn
  rw [Set.mem_Icc] at hbj ⊢
  exact ⟨by linarith [hbj.1, hd.1], by linarith [hbj.2, hd.2]⟩

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The lower containment at slack `ρ`**: `RMF.sliceEvent_subset_barrierEvent_of_narrow` with
the window sum capped at `ρ` and the barrier narrowed by `ρ`. -/
lemma sliceEvent_subset_barrierEvent_of_narrow_slack {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {w : ℕ → ℝ}
    {n : ℕ} {c u v : ℕ → ℝ} {ω : Ω} {ρ : ℝ}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hx : ω ∈ sliceEvent X w n c)
    (hb : ω ∈ barrierEvent X n (fun j => u j + ρ) (fun j => v j - ρ)) :
    sliceEvent Y w n c ⊆ barrierEvent Y n u v := by
  intro ω' hy j hj1 hjn
  have hd := abs_sub_le_iff.mp ((abs_walk_sub_walk_le hx hy hjn).trans (hwsum j hjn))
  have hbj := hb j hj1 hjn
  rw [Set.mem_Icc] at hbj ⊢
  simp only at hbj
  exact ⟨by linarith [hbj.1, hd.1], by linarith [hbj.2, hd.2]⟩

/-- **Lemma 4 at slack `ρ`, upper bound**: `RMF.measure_barrierEvent_le` with the window sum
capped at `ρ` and the Gaussian barrier widened by `ρ` rather than `2`. -/
theorem measure_barrierEvent_le_slack {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {X : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {w M M' u v : ℕ → ℝ} {n : ℕ}
    {ε ρ : ℝ}
    (hX : ∀ m, Measurable (X m)) (hN : ∀ m, Measurable (N m))
    (hw : ∀ m, 0 < w m)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u j ∧ v j ≤ M j) (hε : 0 ≤ ε)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsWindowComparison P Q X N w M' n ε) :
    (P (barrierEvent X n u v)).toReal
      ≤ (1 + ε) * (Q (barrierEvent N n (fun j => u j - ρ) (fun j => v j + ρ))).toReal := by
  classical
  set A := barrierEvent X n u v with hAdef
  set Bw := barrierEvent N n (fun j => u j - ρ) (fun j => v j + ρ) with hBwdef
  set F : (Fin n → ℤ) → Set Ω := fun k => A ∩ sliceEvent X w n (gridPoint w n k) with hFdef
  set G : (Fin n → ℤ) → Set Ω' :=
    fun k => if (F k).Nonempty then sliceEvent N w n (gridPoint w n k) else ∅ with hGdef
  -- measurability
  have hFmeas : ∀ k, MeasurableSet (F k) := fun k =>
    (measurableSet_barrierEvent hX n u v).inter (measurableSet_sliceEvent hX w n _)
  have hGmeas : ∀ k, MeasurableSet (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · simpa only [hGdef, if_pos h] using measurableSet_sliceEvent hN w n (gridPoint w n k)
    · simpa only [hGdef, if_neg h] using MeasurableSet.empty
  -- disjointness, on both sides
  have hFdisj : Pairwise (Function.onFun Disjoint F) := fun k k' hne =>
    (sliceEvent_gridPoint_disjoint hw hne).mono Set.inter_subset_right Set.inter_subset_right
  have hGdisj : Pairwise (Function.onFun Disjoint G) := by
    intro k k' hne
    simp only [hGdef, Function.onFun]
    split_ifs
    · exact sliceEvent_gridPoint_disjoint hw hne
    all_goals simp
  -- the barrier is the disjoint union of its slices
  have hAunion : A = ⋃ k, F k := by
    ext ω
    refine ⟨fun hω => Set.mem_iUnion.mpr ⟨gridIndex X w n ω, hω, mem_sliceEvent_gridPoint hw ω⟩,
      fun h => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact hk.1
  -- transfer of one inequality from `ℝ` to `ℝ≥0∞`
  have hconv : ∀ (s : Set Ω) (t : Set Ω'), (P s).toReal ≤ (1 + ε) * (Q t).toReal →
      P s ≤ ENNReal.ofReal (1 + ε) * Q t := by
    intro s t h
    rw [← ENNReal.ofReal_toReal (measure_ne_top P s), ← ENNReal.ofReal_toReal (measure_ne_top Q t),
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal h
  have hGpos : ∀ k, (F k).Nonempty → G k = sliceEvent N w n (gridPoint w n k) := by
    intro k h
    simp only [hGdef]
    rw [if_pos h]
  -- the slice-by-slice estimate
  have hslice : ∀ k, P (F k) ≤ ENNReal.ofReal (1 + ε) * Q (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωA, hωs⟩ := h
      -- the witness pins `k` down: it lies in its own slice too, and slices are disjoint
      have hkeq : k = gridIndex X w n ω := by
        by_contra hne
        exact Set.disjoint_left.mp (sliceEvent_gridPoint_disjoint (X := X) hw hne) hωs
          (mem_sliceEvent_gridPoint hw ω)
      have henv : ∀ m, m < n → |gridPoint w n k m| ≤ M' m := by
        intro m hm
        rw [hkeq]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hM hMM hωA hm
      have hup := (hcmp (gridPoint w n k) henv).2
      rw [hGpos k ⟨ω, hωA, hωs⟩]
      exact le_trans (measure_mono Set.inter_subset_right) (hconv _ _ hup)
    · have : F k = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [this]
  -- every non-empty slice sits inside the widened barrier
  have hGsub : (⋃ k, G k) ⊆ Bw := by
    refine Set.iUnion_subset fun k => ?_
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωA, hωs⟩ := h
      rw [hGpos k ⟨ω, hωA, hωs⟩]
      exact sliceEvent_subset_barrierEvent_widen_slack hwsum hωs hωA
    · simp only [hGdef, if_neg h]
      exact Set.empty_subset _
  -- assemble in `ℝ≥0∞`
  have key : P A ≤ ENNReal.ofReal (1 + ε) * Q Bw := by
    have h := mul_measure_le_of_cellwise (μ := P) (ν := Q) (S := A) (T := Bw) (a := 1)
      (b := ENNReal.ofReal (1 + ε)) hFmeas hGmeas hFdisj hGdisj hAunion.subset hGsub
      fun k => by rw [one_mul]; exact hslice k
    rwa [one_mul] at h
  -- and transport back to `ℝ`
  have hle := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top Q Bw)) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hle

/-! ### Two points -/

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The two-point upper containment at slack `ρ`**, one coordinate at a time. -/
lemma sliceEventOf_subset_barrierEventPair_widen_slack {Z : ℕ → Ω → ℝ × ℝ} {Y : ℕ → Ω' → ℝ × ℝ}
    {w c d : ℕ → ℝ} {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {ω : Ω} {ρ : ℝ}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hx : ω ∈ sliceEventOf Z n (boxCell w c d)) (hb : ω ∈ barrierEventPair Z n u₁ v₁ u₂ v₂) :
    sliceEventOf Y n (boxCell w c d)
      ⊆ barrierEventPair Y n (fun j => u₁ j - ρ) (fun j => v₁ j + ρ)
          (fun j => u₂ j - ρ) (fun j => v₂ j + ρ) := by
  rw [sliceEventOf_boxCell] at hx
  rw [sliceEventOf_boxCell, barrierEventPair]
  exact Set.inter_subset_inter (sliceEvent_subset_barrierEvent_widen_slack hwsum hx.1 hb.1)
    (sliceEvent_subset_barrierEvent_widen_slack hwsum hx.2 hb.2)

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The two-point lower containment at slack `ρ`**, one coordinate at a time. -/
lemma sliceEventOf_subset_barrierEventPair_of_narrow_slack {Z : ℕ → Ω → ℝ × ℝ} {Y : ℕ → Ω' → ℝ × ℝ}
    {w c d : ℕ → ℝ} {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {ω : Ω} {ρ : ℝ}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hx : ω ∈ sliceEventOf Z n (boxCell w c d))
    (hb : ω ∈ barrierEventPair Z n (fun j => u₁ j + ρ) (fun j => v₁ j - ρ)
      (fun j => u₂ j + ρ) (fun j => v₂ j - ρ)) :
    sliceEventOf Y n (boxCell w c d) ⊆ barrierEventPair Y n u₁ v₁ u₂ v₂ := by
  rw [sliceEventOf_boxCell] at hx
  rw [sliceEventOf_boxCell, barrierEventPair]
  exact Set.inter_subset_inter (sliceEvent_subset_barrierEvent_of_narrow_slack hwsum hx.1 hb.1)
    (sliceEvent_subset_barrierEvent_of_narrow_slack hwsum hx.2 hb.2)

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- `RMF.sliceEventOf_subset_barrierEventPair_widen_slack` at the grid cell. -/
lemma sliceEventOf_gridBox_subset_widen_slack {Z : ℕ → Ω → ℝ × ℝ} {Y : ℕ → Ω' → ℝ × ℝ}
    {w : ℕ → ℝ} {n : ℕ} {k : (Fin n → ℤ) × (Fin n → ℤ)} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {ω : Ω} {ρ : ℝ}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hx : ω ∈ sliceEventOf Z n (gridBox w n k)) (hb : ω ∈ barrierEventPair Z n u₁ v₁ u₂ v₂) :
    sliceEventOf Y n (gridBox w n k)
      ⊆ barrierEventPair Y n (fun j => u₁ j - ρ) (fun j => v₁ j + ρ)
          (fun j => u₂ j - ρ) (fun j => v₂ j + ρ) :=
  sliceEventOf_subset_barrierEventPair_widen_slack hwsum hx hb

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- `RMF.sliceEventOf_subset_barrierEventPair_of_narrow_slack` at the grid cell. -/
lemma sliceEventOf_gridBox_subset_of_narrow_slack {Z : ℕ → Ω → ℝ × ℝ} {Y : ℕ → Ω' → ℝ × ℝ}
    {w : ℕ → ℝ} {n : ℕ} {k : (Fin n → ℤ) × (Fin n → ℤ)} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {ω : Ω} {ρ : ℝ}
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hx : ω ∈ sliceEventOf Z n (gridBox w n k))
    (hb : ω ∈ barrierEventPair Z n (fun j => u₁ j + ρ) (fun j => v₁ j - ρ)
      (fun j => u₂ j + ρ) (fun j => v₂ j - ρ)) :
    sliceEventOf Y n (gridBox w n k) ⊆ barrierEventPair Y n u₁ v₁ u₂ v₂ :=
  sliceEventOf_subset_barrierEventPair_of_narrow_slack hwsum hx hb

/-- **Lemma 4 at two heights and slack `ρ`, upper bound**: `RMF.measure_barrierEventPair_le` with
the window sum capped at `ρ` and both Gaussian tubes widened by `ρ` rather than `2`. -/
theorem measure_barrierEventPair_le_slack {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Z : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' → ℝ × ℝ}
    {w M M' u₁ v₁ u₂ v₂ : ℕ → ℝ} {n : ℕ} {ε ρ : ℝ}
    (hZ : ∀ m, Measurable (Z m)) (hN : ∀ m, Measurable (N m)) (hw : ∀ m, 0 < w m)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM₁ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hM₂ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₂ j ∧ v₂ j ≤ M j) (hε : 0 ≤ ε)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsBoxComparison P Q Z N w M' n ε) :
    (P (barrierEventPair Z n u₁ v₁ u₂ v₂)).toReal
      ≤ (1 + ε) * (Q (barrierEventPair N n (fun j => u₁ j - ρ) (fun j => v₁ j + ρ)
          (fun j => u₂ j - ρ) (fun j => v₂ j + ρ))).toReal := by
  classical
  set A := barrierEventPair Z n u₁ v₁ u₂ v₂ with hAdef
  set Bw := barrierEventPair N n (fun j => u₁ j - ρ) (fun j => v₁ j + ρ)
    (fun j => u₂ j - ρ) (fun j => v₂ j + ρ) with hBwdef
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
      exact sliceEventOf_gridBox_subset_widen_slack hwsum hωs hωA
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

/-- **Lemma 4 at two heights and slack `ρ`, lower bound**: with the window sum capped at `ρ`, the
two-point barrier probability under `P` is at least `1 - ε` times the bivariate Gaussian one for
both tubes narrowed by `ρ`. -/
theorem le_measure_barrierEventPair_slack {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Z : ℕ → Ω → ℝ × ℝ} {N : ℕ → Ω' → ℝ × ℝ}
    {w M M' u₁ v₁ u₂ v₂ : ℕ → ℝ} {n : ℕ} {ε ρ : ℝ}
    (hZ : ∀ m, Measurable (Z m)) (hN : ∀ m, Measurable (N m)) (hw : ∀ m, 0 < w m)
    (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ ρ)
    (hM0 : ∀ j, 0 ≤ M j)
    (hM₁ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j ∧ v₁ j ≤ M j)
    (hM₂ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₂ j ∧ v₂ j ≤ M j)
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m)
    (hcmp : IsBoxComparison P Q Z N w M' n ε) :
    (1 - ε) * (Q (barrierEventPair N n (fun j => u₁ j + ρ) (fun j => v₁ j - ρ)
        (fun j => u₂ j + ρ) (fun j => v₂ j - ρ))).toReal
      ≤ (P (barrierEventPair Z n u₁ v₁ u₂ v₂)).toReal := by
  classical
  set A := barrierEventPair Z n u₁ v₁ u₂ v₂ with hAdef
  set B := barrierEventPair N n (fun j => u₁ j + ρ) (fun j => v₁ j - ρ)
    (fun j => u₂ j + ρ) (fun j => v₂ j - ρ) with hBdef
  rcases le_or_gt (1 - ε) 0 with hneg | hpos
  · nlinarith [ENNReal.toReal_nonneg (a := Q B), ENNReal.toReal_nonneg (a := P A)]
  -- `0 ≤ ρ` is the sum over no windows
  have hρ : 0 ≤ ρ := by simpa using hwsum 0 (Nat.zero_le n)
  have hnar₁ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₁ j + ρ ∧ v₁ j - ρ ≤ M j := by
    intro j hj1 hjn
    obtain ⟨h1, h2⟩ := hM₁ j hj1 hjn
    exact ⟨by linarith, by linarith⟩
  have hnar₂ : ∀ j, 1 ≤ j → j ≤ n → -M j ≤ u₂ j + ρ ∧ v₂ j - ρ ≤ M j := by
    intro j hj1 hjn
    obtain ⟨h1, h2⟩ := hM₂ j hj1 hjn
    exact ⟨by linarith, by linarith⟩
  set F : ((Fin n → ℤ) × (Fin n → ℤ)) → Set Ω' :=
    fun k => B ∩ sliceEventOf N n (gridBox w n k) with hFdef
  set G : ((Fin n → ℤ) × (Fin n → ℤ)) → Set Ω :=
    fun k => if (F k).Nonempty then sliceEventOf Z n (gridBox w n k) else ∅ with hGdef
  have hFmeas : ∀ k, MeasurableSet (F k) := fun k =>
    (measurableSet_barrierEventPair hN n _ _ _ _).inter
      (measurableSet_sliceEventOf_gridBox hN w n k)
  have hGmeas : ∀ k, MeasurableSet (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · simpa only [hGdef, if_pos h] using measurableSet_sliceEventOf_gridBox hZ w n k
    · simpa only [hGdef, if_neg h] using MeasurableSet.empty
  have hFdisj : Pairwise (Function.onFun Disjoint F) := fun k k' hne =>
    (sliceEventOf_gridBox_disjoint hw hne).mono Set.inter_subset_right Set.inter_subset_right
  have hGdisj : Pairwise (Function.onFun Disjoint G) := by
    intro k k' hne
    simp only [hGdef, Function.onFun]
    split_ifs
    · exact sliceEventOf_gridBox_disjoint hw hne
    all_goals simp
  have hBunion : B = ⋃ k, F k := by
    ext ω
    refine ⟨fun hω => Set.mem_iUnion.mpr ⟨(gridIndex (fun m ω => (N m ω).1) w n ω,
      gridIndex (fun m ω => (N m ω).2) w n ω), hω, mem_sliceEventOf_gridBox hw ω⟩, fun h => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact hk.1
  have hconv : ∀ (t : Set Ω') (r : Set Ω), (1 - ε) * (Q t).toReal ≤ (P r).toReal →
      ENNReal.ofReal (1 - ε) * Q t ≤ P r := by
    intro t r h
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q t), ← ENNReal.ofReal_toReal (measure_ne_top P r),
      ← ENNReal.ofReal_mul hpos.le]
    exact ENNReal.ofReal_le_ofReal h
  have hGpos : ∀ k, (F k).Nonempty → G k = sliceEventOf Z n (gridBox w n k) := by
    intro k h
    simp only [hGdef]
    rw [if_pos h]
  have hslice : ∀ k, ENNReal.ofReal (1 - ε) * Q (F k) ≤ P (G k) := by
    intro k
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωB, hωs⟩ := h
      have hkeq : k = (gridIndex (fun m ω => (N m ω).1) w n ω,
          gridIndex (fun m ω => (N m ω).2) w n ω) := by
        by_contra hne
        exact Set.disjoint_left.mp (sliceEventOf_gridBox_disjoint (Z := N) hw hne) hωs
          (mem_sliceEventOf_gridBox hw ω)
      have hk₁ : k.1 = gridIndex (fun m ω => (N m ω).1) w n ω := by rw [hkeq]
      have hk₂ : k.2 = gridIndex (fun m ω => (N m ω).2) w n ω := by rw [hkeq]
      have henv₁ : ∀ m, m < n → |gridPoint w n k.1 m| ≤ M' m := by
        intro m hm
        rw [hk₁]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hnar₁ hMM hωB.1 hm
      have henv₂ : ∀ m, m < n → |gridPoint w n k.2 m| ≤ M' m := by
        intro m hm
        rw [hk₂]
        exact abs_gridPoint_le_of_mem_barrierEvent hw hM0 hnar₂ hMM hωB.2 hm
      have hlow : (1 - ε) * (Q (sliceEventOf N n (gridBox w n k))).toReal
          ≤ (P (sliceEventOf Z n (gridBox w n k))).toReal :=
        (hcmp (gridPoint w n k.1) (gridPoint w n k.2) henv₁ henv₂).1
      rw [hGpos k ⟨ω, hωB, hωs⟩]
      refine le_trans ?_ (hconv _ _ hlow)
      gcongr
      exact Set.inter_subset_right
    · have : F k = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [this]
  have hGsub : (⋃ k, G k) ⊆ A := by
    refine Set.iUnion_subset fun k => ?_
    by_cases h : (F k).Nonempty
    · obtain ⟨ω, hωB, hωs⟩ := h
      rw [hGpos k ⟨ω, hωB, hωs⟩]
      exact sliceEventOf_gridBox_subset_of_narrow_slack hwsum hωs hωB
    · simp only [hGdef, if_neg h]
      exact Set.empty_subset _
  have key : ENNReal.ofReal (1 - ε) * Q B ≤ P A := by
    have h := mul_measure_le_of_cellwise (μ := Q) (ν := P) (S := B) (T := A)
      (a := ENNReal.ofReal (1 - ε)) (b := 1) hFmeas hGmeas hFdisj hGdisj hBunion.subset hGsub
      fun k => by rw [one_mul]; exact hslice k
    rwa [one_mul] at h
  have hle := ENNReal.toReal_mono (measure_ne_top P A) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le] at hle

end RMF
