/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2Prefix
import RMF.UniformLower.PairWindowData
import RMF.Probability.PairBallotSum

/-!
# HP2's post part: the post tube and the two-fold block data

Two heights `h₁, h₂ ∈ halfWindow k` at depth `d` (`e^{-1} ≤ |h₁ - h₂|e^{k+d} ≤ 1`) decorrelate from
block `d` on; the post part starts at `b = RMF.hp2PostStart d` (`d` for `d ≥ 4`, `min(d + 2, 4)`
below, where the two-fold determinant bound `RMF.pair_block_comparison_inputs_det` needs the
difference phase past `e`) and runs over the blocks `b ≤ m < r` under the two-fold tilt.  The post
tube `RMF.hp2PostTube` at a start `z` is HP1's tube from block `b` on: on `RMF.hp1Tube` each walk
lies in its post tube at `z = RMF.windowZ` at block `b` (`RMF.mem_hp2PostTube_of_mem_hp1Tube`).

This file has the post bound's ingredients; the bound itself, from `k ≥ 20`, is in
`RMF/UniformLower/HP2PostFloor.lean`.

* **The two-fold block data** `RMF.pairMeanH`, `RMF.pairVarH`, `RMF.pairCovH`, and the covariance
  by the cosine sums (`RMF.abs_pairCovH_le`).
* **The cosine sums by tiers**: `RMF.diffTier` for the difference frequency, `RMF.sumTier` for the
  sum frequencies, and their sums (`RMF.sum_diffTier_le`, `RMF.sum_sumTier_le`).
* **The product form**: the pair ballot's bracket as a product (`RMF.pairBallot_bracket_le`) and
  its simplification (`RMF.post_Cpost_simplify`).
* **The pair mass** over any run of blocks (`RMF.integral_normSq_mul_normSq_blocks_le`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

section Tube

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The post start at depth `d`**: `b = d` for `d ≥ 4`, `b = min(d + 2, 4)` for `d ≤ 3`. -/
def hp2PostStart (d : ℕ) : ℕ := if 4 ≤ d then d else min (d + 2) 4

/-- **HP2's post tube at start `z`**: the height walk's blocks `b ≤ m < b + n`, as the walk at
offset `k + b`, started at the centred value `z` at block `b`, stays in
`[Mean_j - A - B(b + j) - ρ, Mean_j + a + ρ]` relative to the one-point tilted means
`RMF.windowMeanH` of those blocks, `1 ≤ j ≤ n` (`RMF.hp2Tube` from block `b` on). -/
def hp2PostTube (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k b n : ℕ) (σ h a A B ρ z : ℝ) : Set Ω :=
  barrierEvent (halfBlock X ((k : ℝ) + b) σ h) n
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) - A - B * ((b : ℝ) + j)
      - ρ - z)
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) + a + ρ - z)

omit [MeasurableSpace Ω] in
/-- Block `i` at offset `k + b` is block `i + b` at offset `k`. -/
lemma halfBlock_add (X : ℕ → Ω → ℂ) (k b : ℕ) (σ h : ℝ) (i : ℕ) :
    halfBlock X ((k : ℝ) + b) σ h i = halfBlock X k σ h (i + b) := by
  funext ω
  rw [halfBlock, halfBlock, primeBlockSub_add]

omit [MeasurableSpace Ω] in
/-- The walk at offset `k + b` is the walk at offset `k` from block `b`. -/
lemma walk_halfBlock_add (X : ℕ → Ω → ℂ) (k b : ℕ) (σ h : ℝ) (j : ℕ) (ω : Ω) :
    walk (halfBlock X ((k : ℝ) + b) σ h) j ω
      = walk (halfBlock X k σ h) (b + j) ω - walk (halfBlock X k σ h) b ω := by
  rw [walk_apply, walk_apply, walk_apply, Finset.sum_range_add, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [halfBlock_add, add_comm i b]

/-- **HP2's tube lies in its post tube at the walk's own start**: on `RMF.hp2Tube` over `M ≥ b + n`
blocks, the post walk from block `b` stays in the post tube at `z = RMF.windowZ` at block `b`. -/
lemma mem_hp2PostTube_of_mem_hp2Tube {y k M b n : ℕ} {σ h a A B ρ : ℝ} (hbn : b + n ≤ M)
    {ω : Ω} (hω : ω ∈ hp2Tube X μ y k M σ h a A B ρ) :
    ω ∈ hp2PostTube X μ y k b n σ h a A B ρ (windowZ X μ y k σ h b ω) := by
  intro j hj1 hjn
  have hT := Set.mem_Icc.1 (hω (b + j) (by omega) (by omega))
  have hwalk := walk_halfBlock_add X k b σ h j ω
  have hmean : ∑ i ∈ Finset.range (b + j), windowMeanH X μ y k σ h i
      = ∑ i ∈ Finset.range b, windowMeanH X μ y k σ h i
        + ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b) := by
    rw [Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm b i]
  have hcast : ((b + j : ℕ) : ℝ) = (b : ℝ) + j := by push_cast; ring
  simp only at hT
  rw [hcast, hmean] at hT
  refine Set.mem_Icc.2 ⟨?_, ?_⟩ <;> simp only [windowZ] <;> linarith [hT.1, hT.2]

/-- **HP1's tube lies in its post tube**: `RMF.hp1Tube` over `r ≥ b + n` blocks, at HP1's
parameters `(3/2, 5/2, 3, 10⁻¹⁵)`. -/
lemma mem_hp2PostTube_of_mem_hp1Tube {y k r b n : ℕ} {σ h : ℝ} (hbn : b + n ≤ r) {ω : Ω}
    (hω : ω ∈ hp1Tube X μ y k r σ h) :
    ω ∈ hp2PostTube X μ y k b n σ h (3 / 2) (5 / 2) 3 (1 / 10 ^ 15)
      (windowZ X μ y k σ h b ω) :=
  mem_hp2PostTube_of_mem_hp2Tube hbn (by rw [hp2Tube_hp1]; exact hω)

/-- **The start lies in the tube**: on `RMF.hp2Tube` over `M ≥ b ≥ 1` blocks,
`windowZ` at block `b` is in `[-A - Bb - ρ, a + ρ]`. -/
lemma windowZ_mem_of_mem_hp2Tube_of_le {y k M b : ℕ} {σ h a A B ρ : ℝ} (hb : 1 ≤ b)
    (hbM : b ≤ M) {ω : Ω} (hω : ω ∈ hp2Tube X μ y k M σ h a A B ρ) :
    -A - B * b - ρ ≤ windowZ X μ y k σ h b ω ∧ windowZ X μ y k σ h b ω ≤ a + ρ := by
  have h1 := Set.mem_Icc.1 (hω b hb hbM)
  unfold windowZ
  constructor <;> linarith [h1.1, h1.2]

end Tube

/-! ### The two-fold block data -/

section PairData

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The two-fold tilted mean of block `m` (offset `k`) of the walk at height `h`, under the tilt
by `‖F_y(s₁)‖²‖F_y(s₂)‖²`, `sᵢ = ½+σ+ihᵢ` (`h = h₁` or `h₂`). -/
noncomputable def pairMeanH (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h₁ h₂ h : ℝ) (m : ℕ) :
    ℝ :=
  blockMeanAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
    (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m)

/-- The two-fold matched variance of block `m` of the walk at height `h`. -/
noncomputable def pairVarH (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h₁ h₂ h : ℝ) (m : ℕ) :
    ℝ :=
  ((blockMatchedVarAdd₂ X μ y (shiftLine σ h₁) (shiftLine σ h₂)
    (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (primeBlockSub k m) : ℝ≥0) : ℝ)

/-- The two-fold covariance of block `m` of the two walks. -/
noncomputable def pairCovH (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h₁ h₂ : ℝ) (m : ℕ) : ℝ :=
  blockMatchedCovAdd X μ y (shiftLine σ h₁) (shiftLine σ h₂)
    (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂)))
    (primeBlockSub k m)

end PairData

/-! ### The block cosine sums of a pair, by tiers

With `D = h₁ - h₂` at depth `d` (`e^{-1} ≤ |D|e^{k+d} ≤ 1`) block `d + i` of the difference
frequency is `blockCos` at `ξ + i`, `ξ = d + log|D| + k ∈ [-1, 0]`: the certified ranges of
`RMF.blockCos_zero_bounds_one_point` and its twins for `i ≤ 3`, the explicit prime number theorem
(`3e^{1-i}`) beyond.  The sum frequencies `2hᵢ, h₁ + h₂ ∈ [2e^{-(k+1)}, 2e^{-k}]` have the ranges
of `RMF.blockCosSum_sum_bounds` on blocks `2, 3` and decay as `1.5e^{1-m}`. -/

section Tiers

/-- **The difference frequency's phase**: `e^{-1} ≤ |D|e^{k+d} ≤ 1` puts `d + log|D| + k` in
`[-1, 0]`. -/
lemma depth_phase_mem {k d : ℕ} {D : ℝ} (hd1 : Real.exp (-1) ≤ |D| * Real.exp ((k : ℝ) + d))
    (hd2 : |D| * Real.exp ((k : ℝ) + d) ≤ 1) :
    0 < |D| ∧ -1 ≤ (d : ℝ) + (Real.log |D| + k) ∧ (d : ℝ) + (Real.log |D| + k) ≤ 0 := by
  have hD0 : 0 < |D| := by
    rcases (abs_nonneg D).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hd1
      exact absurd hd1 (not_le.2 (Real.exp_pos _))
  have ha : (d : ℝ) + (Real.log |D| + k) = Real.log (|D| * Real.exp ((k : ℝ) + d)) := by
    rw [Real.log_mul hD0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine ⟨hD0, ?_, ?_⟩
  · rw [ha]
    have := Real.log_le_log (Real.exp_pos _) hd1
    rwa [Real.log_exp] at this
  · rw [ha]
    exact Real.log_nonpos (by positivity) hd2

/-- **The difference frequency's tier** at phase index `i` (block `d + i`): the certified ranges
widened by `0.0101` for `i ≤ 3`, `3e^{1-i}` beyond. -/
noncomputable def diffTier (i : ℕ) : ℝ :=
  if i = 0 then 0.8101 else if i = 1 then 0.7601 else if i = 2 then 0.3601
  else if i = 3 then 0.2601 else 3 * Real.exp (1 - i)

/-- **The sum frequencies' tier** at block `m ≥ 2`: the ranges of `RMF.blockCosSum_sum_bounds` on
blocks `2, 3`, `1.5e^{1-m}` beyond. -/
noncomputable def sumTier (m : ℕ) : ℝ :=
  if m = 2 then 0.3101 else if m = 3 then 0.1461 else 1.5 * Real.exp (1 - m)

lemma diffTier_nonneg (i : ℕ) : 0 ≤ diffTier i := by
  unfold diffTier
  split_ifs <;> positivity

lemma sumTier_nonneg (m : ℕ) : 0 ≤ sumTier m := by
  unfold sumTier
  split_ifs <;> positivity

/-- **A tier sum with a geometric tail**: if `0 ≤ f` and `f i ≤ Ce^{-i}` for `i ≥ L`, then
`∑_{j<n} f(s + j) ≤ ∑_{s≤i<L} f i + 1.59Ce^{-L}` for every `n`. -/
lemma sum_range_shift_le_of_tail {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) {s L : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (htail : ∀ i, L ≤ i → f i ≤ C * Real.exp (-(i : ℝ))) (n : ℕ) :
    ∑ j ∈ Finset.range n, f (s + j)
      ≤ ∑ i ∈ Finset.Ico s L, f i + C * Real.exp (-(L : ℝ)) * 1.59 := by
  have hIco : ∑ j ∈ Finset.range n, f (s + j) = ∑ i ∈ Finset.Ico s (s + n), f i := by
    rw [Finset.sum_Ico_eq_sum_range, show s + n - s = n by omega]
  rw [hIco]
  have hsub : Finset.Ico s (s + n) ⊆ Finset.Ico s L ∪ Finset.Ico L (s + n) := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_union] at hi ⊢
    omega
  have hdisj : Disjoint (Finset.Ico s L) (Finset.Ico L (s + n)) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_Ico] at h1 h2
    omega
  have htail' : ∑ i ∈ Finset.Ico L (s + n), f i ≤ C * Real.exp (-(L : ℝ)) * 1.59 := by
    have h := sum_mul_exp_neg_mul_le_numeral_of_le (c := C) (K := 1) (B := 0) hC zero_le_one
      le_rfl (n := L) (s := Finset.Ico L (s + n)) (fun i hi => (Finset.mem_Ico.1 hi).1)
    refine le_trans (Finset.sum_le_sum fun i hi => ?_) (le_trans h (le_of_eq (by ring)))
    rw [show C * Real.exp (-(i : ℝ)) * (1 + 0 * (2 * (i : ℝ) + 1)) = C * Real.exp (-(i : ℝ))
      by ring]
    exact htail i (Finset.mem_Ico.1 hi).1
  calc ∑ i ∈ Finset.Ico s (s + n), f i
      ≤ ∑ i ∈ Finset.Ico s L ∪ Finset.Ico L (s + n), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hf i
    _ = ∑ i ∈ Finset.Ico s L, f i + ∑ i ∈ Finset.Ico L (s + n), f i :=
        Finset.sum_union hdisj
    _ ≤ _ := by linarith

/-- The difference tiers past `3`: `diffTier i ≤ 3e·e^{-i}` for `i ≥ 4`. -/
lemma diffTier_le_tail {i : ℕ} (hi : 4 ≤ i) :
    diffTier i ≤ 3 * Real.exp 1 * Real.exp (-(i : ℝ)) := by
  simp only [diffTier, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
    show i ≠ 3 by omega, if_false]
  rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]

/-- The sum tiers past `3`: `sumTier m ≤ 1.5e·e^{-m}` for `m ≥ 4`. -/
lemma sumTier_le_tail {m : ℕ} (hm : 4 ≤ m) :
    sumTier m ≤ 1.5 * Real.exp 1 * Real.exp (-(m : ℝ)) := by
  simp only [sumTier, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
  rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]

/-- `3e·e^{-4}·1.59 ≤ 0.2375` and `1.5e·e^{-4}·1.59 ≤ 0.1188`. -/
lemma tier_tail_numerals :
    3 * Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ)) * 1.59 ≤ 0.2375
      ∧ 1.5 * Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ)) * 1.59 ≤ 0.1188 := by
  have he : Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ)) = Real.exp (-3) := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp (-3) ≤ 0.04979 := by
    have h20 : (20.085 : ℝ) ≤ Real.exp 3 := by
      simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 3) (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 3)]
    nlinarith
  constructor
  · rw [show 3 * Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ)) * 1.59
      = 4.77 * (Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ))) by ring, he]
    linarith
  · rw [show 1.5 * Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ)) * 1.59
      = 2.385 * (Real.exp 1 * Real.exp (-((4 : ℕ) : ℝ))) by ring, he]
    linarith

/-- **The difference tiers summed from phase `s`**: `∑_{j<n} diffTier(s + j)` is at most
`2.428, 1.618, 0.858` for `s = 0, 1, 2`. -/
lemma sum_diffTier_le (n : ℕ) :
    ∑ j ∈ Finset.range n, diffTier (0 + j) ≤ 2.428
      ∧ ∑ j ∈ Finset.range n, diffTier (1 + j) ≤ 1.618
      ∧ ∑ j ∈ Finset.range n, diffTier (2 + j) ≤ 0.858 := by
  have ht := tier_tail_numerals.1
  have hpos : (0 : ℝ) ≤ 3 * Real.exp 1 := by positivity
  have h := fun (s : ℕ) =>
    sum_range_shift_le_of_tail diffTier_nonneg (s := s) (L := 4) hpos
      (fun i hi => diffTier_le_tail hi) n
  refine ⟨?_, ?_, ?_⟩
  · refine (h 0).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, diffTier]
    norm_num
    linarith
  · refine (h 1).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, diffTier]
    norm_num
    linarith
  · refine (h 2).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, diffTier]
    norm_num
    linarith

/-- **The sum tiers summed from block `b ≥ 2`**: `∑_{j<n} sumTier(b + j)` is at most `0.575`,
`0.265`, `0.1188` for `b = 2`, `b = 3`, `b ≥ 4`. -/
lemma sum_sumTier_le (n : ℕ) :
    ∑ j ∈ Finset.range n, sumTier (2 + j) ≤ 0.575
      ∧ ∑ j ∈ Finset.range n, sumTier (3 + j) ≤ 0.265
      ∧ ∀ b, 4 ≤ b → ∑ j ∈ Finset.range n, sumTier (b + j) ≤ 0.1188 := by
  have ht := tier_tail_numerals.2
  have hpos : (0 : ℝ) ≤ 1.5 * Real.exp 1 := by positivity
  have h := fun (s : ℕ) =>
    sum_range_shift_le_of_tail sumTier_nonneg (s := s) (L := 4) hpos
      (fun i hi => sumTier_le_tail hi) n
  refine ⟨?_, ?_, fun b hb => ?_⟩
  · refine (h 2).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sumTier]
    norm_num
    linarith
  · refine (h 3).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sumTier]
    norm_num
    linarith
  · have hb' := sum_range_shift_le_of_tail sumTier_nonneg hpos
      (fun i hi => sumTier_le_tail (le_trans hb hi)) (s := b) (L := b) n
    rw [Finset.Ico_self, Finset.sum_empty, zero_add] at hb'
    refine hb'.trans (le_trans ?_ ht)
    have hb4 : Real.exp (-(b : ℝ)) ≤ Real.exp (-((4 : ℕ) : ℝ)) :=
      Real.exp_le_exp.2 (by
        have : ((4 : ℕ) : ℝ) ≤ b := by exact_mod_cast hb
        linarith)
    have := mul_le_mul_of_nonneg_left hb4 hpos
    nlinarith

end Tiers

/-! ### The post blocks' two-fold statistics -/

section PostData

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The two-fold variances' lower tier at block `m ≥ 2`: `0.3649, 0.4219, 0.4575` for `m = 2`,
`m = 3`, `m ≥ 4`. -/
noncomputable def varLoTier (m : ℕ) : ℝ :=
  if m = 2 then 0.3649 else if m = 3 then 0.4219 else 0.4575

/-- The two-fold variances' upper tier at block `m ≥ 2`: `0.6551, 0.5731, 0.5375` for `m = 2`,
`m = 3`, `m ≥ 4`. -/
noncomputable def varHiTier (m : ℕ) : ℝ :=
  if m = 2 then 0.6551 else if m = 3 then 0.5731 else 0.5375

/-- **The two-fold covariance by the cosine sums**:
`|cov_m| ≤ (|C_m(h₁-h₂)| + |C_m(h₁+h₂)|)/2 + e^{-m}/10²⁰`
(`RMF.abs_blockMatchedCovAdd_sub_le_decay`). -/
lemma abs_pairCovH_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ} {σ h₁ h₂ : ℝ}
    (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    |pairCovH X μ y k σ h₁ h₂ m|
      ≤ (|blockCosSum k σ (h₁ - h₂) m| + |blockCosSum k σ (h₁ + h₂) m|) / 2
        + Real.exp (-(m : ℝ)) / 10 ^ 20 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have h := abs_blockMatchedCovAdd_sub_le_decay hX y (h₁ := h₁) (h₂ := h₂) hσ (by positivity)
    (by linarith [Nat.cast_nonneg (α := ℝ) m]) hB
  have htri := abs_add_le (blockCosSum k σ (h₁ - h₂) m) (blockCosSum k σ (h₁ + h₂) m)
  unfold pairCovH
  have h2 := abs_sub_abs_le_abs_sub (blockMatchedCovAdd X μ y (shiftLine σ h₁) (shiftLine σ h₂)
    (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂)))
    (primeBlockSub k m)) ((blockCosSum k σ (h₁ - h₂) m + blockCosSum k σ (h₁ + h₂) m) / 2)
  rw [abs_div, abs_two] at h2
  linarith

end PostData

/-! ### The pair's push against the one-point centring

The two-fold means exceed the one-point ones by `Δ_m = C_m(h₁-h₂) + C_m(h₁+h₂)` per block (within
`2e^{-m}/10²⁰`), and the pair ballot's ceilings are raised by `max_j(-∑_{i<j}Δ_{b+i})`.  The
sum-frequency part is at most `e^{1-b}` however long (the uniform tail). -/

section Push

/-- The damping of the post blocks: `σe^{k+m+1} ≤ 1/200` for a block `m < b + n` when
`σe^{k+b+n} ≤ 1/200`. -/
lemma sigma_exp_le_of_lt {k b n m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hσn : σ * Real.exp ((k : ℝ) + ((b : ℝ) + n)) ≤ 1 / 200) (hm : m < b + n) :
    σ * Real.exp ((k : ℝ) + (m : ℝ) + 1) ≤ 1 / 200 := by
  refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hσ) hσn
  have : (m : ℝ) + 1 ≤ (b : ℝ) + n := by exact_mod_cast hm
  linarith

/-- `∑_{i<j} e^{-(i+b)} ≤ 1.59`: the geometric series. -/
lemma sum_exp_neg_add_le (b j : ℕ) :
    ∑ i ∈ Finset.range j, Real.exp (-((i + b : ℕ) : ℝ)) ≤ 1.59 := by
  have h1 := sum_exp_neg_le ((Finset.range j).image (fun m => m + b))
  rw [Finset.sum_image (fun a _ c _ hac => by omega)] at h1
  refine h1.trans ?_
  have he1 : (2.7182 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [div_le_iff₀ (by linarith)]
  linarith

end Push

/-! ### The post bound in the product form `Cpost·(A₁ + c')(A₂ + c')/n` -/

/-- **The pair ballot's bracket as a product**: for `A₁, A₂ ≥ 0`, `c' > 0`, `v ≥ 0` and
`0 ≤ K ≤ K₀`,
`(A₁ + c')(A₂ + c') + K((A₁ + c')√v + v) ≤ (A₁ + c')(A₂ + c')(1 + K₀(√v + v/c')/c')`: the slope term
is charged at the worst `A₂ = 0`. -/
lemma pairBallot_bracket_le {A₁ A₂ c' v K K₀ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hc' : 0 < c')
    (hv : 0 ≤ v) (hK : 0 ≤ K) (hKK : K ≤ K₀) :
    (A₁ + c') * (A₂ + c') + K * ((A₁ + c') * √v + v)
      ≤ (A₁ + c') * (A₂ + c') * (1 + K₀ * (√v + v / c') / c') := by
  have hX : 0 < A₁ + c' := by linarith
  have hY : 0 < A₂ + c' := by linarith
  have hs : 0 ≤ √v := Real.sqrt_nonneg v
  have hvc : v ≤ (A₁ + c') * (v / c') := by
    rw [mul_div_assoc', le_div_iff₀ hc']
    nlinarith
  have h1 : K * ((A₁ + c') * √v + v) ≤ K₀ * ((A₁ + c') * (√v + v / c')) := by
    have hK0 : 0 ≤ K₀ := hK.trans hKK
    have hin : (A₁ + c') * √v + v ≤ (A₁ + c') * (√v + v / c') := by nlinarith
    calc K * ((A₁ + c') * √v + v) ≤ K₀ * ((A₁ + c') * √v + v) :=
          mul_le_mul_of_nonneg_right hKK (by positivity)
      _ ≤ K₀ * ((A₁ + c') * (√v + v / c')) := mul_le_mul_of_nonneg_left hin hK0
  have h2 : K₀ * ((A₁ + c') * (√v + v / c'))
      ≤ K₀ * ((A₁ + c') * (√v + v / c')) * ((A₂ + c') / c') := by
    have hge : 1 ≤ (A₂ + c') / c' := by rw [le_div_iff₀ hc']; linarith
    have h0 : 0 ≤ K₀ * ((A₁ + c') * (√v + v / c')) := by
      have hK0 : 0 ≤ K₀ := hK.trans hKK
      positivity
    nlinarith
  have h3 : K₀ * ((A₁ + c') * (√v + v / c')) * ((A₂ + c') / c')
      = (A₁ + c') * (A₂ + c') * (K₀ * (√v + v / c') / c') := by
    field_simp
  nlinarith

/-- `√(2/(πα₁n))·√(2/(πα₂n)) ≤ (2/π)/(n√(α₁α₂))` for `α₁, α₂, n > 0` (an equality). -/
lemma sqrt_two_div_mul_le {α₁ α₂ N : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hN : 0 < N) :
    √(2 / (π * (α₁ * N))) * √(2 / (π * (α₂ * N))) ≤ 2 / π / √(α₁ * α₂) / N := by
  have hπ := Real.pi_pos
  have hs : 0 < √(α₁ * α₂) := Real.sqrt_pos.2 (by positivity)
  have hT : 0 ≤ 2 / π / √(α₁ * α₂) / N := by positivity
  rw [← Real.sqrt_mul (by positivity)]
  rw [show 2 / π / √(α₁ * α₂) / N = √((2 / π / √(α₁ * α₂) / N) ^ 2) from
    (Real.sqrt_sq hT).symm]
  refine Real.sqrt_le_sqrt (le_of_eq ?_)
  have hsq : √(α₁ * α₂) ^ 2 = α₁ * α₂ := Real.sq_sqrt (by positivity)
  field_simp
  rw [hsq]

/-! ### The numerals -/

/-- `e^{-3} ≤ 0.04979`, `e^{-2} ≤ 0.135336`, `e^{-1} ≤ 0.36788`. -/
lemma exp_neg_small_numerals :
    Real.exp (-3) ≤ 0.04979 ∧ Real.exp (-2) ≤ 0.135336 ∧ Real.exp (-1) ≤ 0.36788 := by
  have h3 : (20.085 : ℝ) ≤ Real.exp 3 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.71828) (k := 3) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have h2 : (7.38905 : ℝ) ≤ Real.exp 2 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.718281) (k := 2) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have h1 : (2.71828 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  refine ⟨?_, ?_, ?_⟩ <;> rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)] <;>
    nlinarith

/-- The difference tiers' maxima: `0.8101` from phase `0`, `0.7601` from `1`, `0.3601` from `2`. -/
lemma diffTier_le_max (i : ℕ) :
    diffTier i ≤ 0.8101 ∧ (1 ≤ i → diffTier i ≤ 0.7601) ∧ (2 ≤ i → diffTier i ≤ 0.3601) := by
  have h3 := exp_neg_small_numerals.1
  have htail : 4 ≤ i → diffTier i ≤ 0.1494 := fun hi => by
    simp only [diffTier, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
      show i ≠ 3 by omega, if_false]
    have : Real.exp (1 - i) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by
      have : (4 : ℝ) ≤ i := by exact_mod_cast hi
      linarith)
    linarith
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with h | h | h | h | h
  · subst h; refine ⟨by norm_num [diffTier], fun h => by omega, fun h => by omega⟩
  · subst h; refine ⟨by norm_num [diffTier], fun _ => by norm_num [diffTier], fun h => by omega⟩
  · subst h; exact ⟨by norm_num [diffTier], fun _ => by norm_num [diffTier],
      fun _ => by norm_num [diffTier]⟩
  · subst h; exact ⟨by norm_num [diffTier], fun _ => by norm_num [diffTier],
      fun _ => by norm_num [diffTier]⟩
  · have := htail h
    exact ⟨by linarith, fun _ => by linarith, fun _ => by linarith⟩

/-- The sum tiers' maxima: `0.3101` from block `2`, `0.1461` from `3`, `0.0747` from `4`. -/
lemma sumTier_le_max {m : ℕ} (hm : 2 ≤ m) :
    sumTier m ≤ 0.3101 ∧ (3 ≤ m → sumTier m ≤ 0.1461) ∧ (4 ≤ m → sumTier m ≤ 0.0747) := by
  have h3 := exp_neg_small_numerals.1
  have htail : 4 ≤ m → sumTier m ≤ 0.0747 := fun hi => by
    simp only [sumTier, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
    have : Real.exp (1 - m) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by
      have : (4 : ℝ) ≤ m := by exact_mod_cast hi
      linarith)
    linarith
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h
  · subst h; exact ⟨by norm_num [sumTier], fun h => by omega, fun h => by omega⟩
  · subst h; exact ⟨by norm_num [sumTier], fun _ => by norm_num [sumTier], fun h => by omega⟩
  · have := htail h
    exact ⟨by linarith, fun _ => by linarith, fun _ => this⟩

/-- **Simplifying the product form**: with `β ≤ α` coordinatewise, `K_f ≤ K_n`, `c' ≤ c_h` and
`(1 + e^{-100})(2/π)K_n ≤ C₀`, the product-form bound
`(1 + e^{-100})(2/π)/√(α₁α₂)·K_f(A₁ + c')(A₂ + c')/N` is at most
`C₀/√(β₁β₂)·(A₁ + c_h)(A₂ + c_h)/N`. -/
lemma post_Cpost_simplify {α₁ α₂ β₁ β₂ Kf Kn C₀ c' ch A₁ A₂ N : ℝ} (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (h₁ : β₁ ≤ α₁) (h₂ : β₂ ≤ α₂) (hKf0 : 0 ≤ Kf) (hKf : Kf ≤ Kn)
    (hC : (1 + Real.exp (-100)) * (2 / π) * Kn ≤ C₀) (hc' : 0 ≤ c') (hch : c' ≤ ch)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hN : 0 < N) :
    (1 + Real.exp (-100)) * (2 / π / √(α₁ * α₂)) * Kf * (A₁ + c') * (A₂ + c') / N
      ≤ C₀ / √(β₁ * β₂) * (A₁ + ch) * (A₂ + ch) / N := by
  have hπ := Real.pi_pos
  have hsβ : 0 < √(β₁ * β₂) := Real.sqrt_pos.2 (by positivity)
  have hsα : √(β₁ * β₂) ≤ √(α₁ * α₂) :=
    Real.sqrt_le_sqrt (mul_le_mul h₁ h₂ hβ₂.le (hβ₁.le.trans h₁))
  have hinv : 1 / √(α₁ * α₂) ≤ 1 / √(β₁ * β₂) :=
    one_div_le_one_div_of_le hsβ hsα
  have hX : (A₁ + c') * (A₂ + c') ≤ (A₁ + ch) * (A₂ + ch) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hK : (1 + Real.exp (-100)) * (2 / π) * Kf ≤ C₀ :=
    le_trans (mul_le_mul_of_nonneg_left hKf (by positivity)) hC
  have hK0 : 0 ≤ (1 + Real.exp (-100)) * (2 / π) * Kf := by positivity
  have hC0 : 0 ≤ C₀ := le_trans hK0 hK
  rw [div_le_div_iff_of_pos_right hN]
  calc (1 + Real.exp (-100)) * (2 / π / √(α₁ * α₂)) * Kf * (A₁ + c') * (A₂ + c')
      = ((1 + Real.exp (-100)) * (2 / π) * Kf) * (1 / √(α₁ * α₂))
        * ((A₁ + c') * (A₂ + c')) := by ring
    _ ≤ C₀ * (1 / √(β₁ * β₂)) * ((A₁ + ch) * (A₂ + ch)) := by
        gcongr
    _ = C₀ / √(β₁ * β₂) * (A₁ + ch) * (A₂ + ch) := by ring

/-- **The slope factor at a lower `c`**: `1 + K(√v + v/c')/c' ≤ 1 + K(s + v/c_l)/c_l` for
`c' ≥ c_l > 0`, `√v ≤ s`, `K, v ≥ 0`. -/
lemma slope_factor_le {K v s cl c' : ℝ} (hK : 0 ≤ K) (hv : 0 ≤ v) (hs : √v ≤ s)
    (hcl : 0 < cl) (hc' : cl ≤ c') :
    1 + K * (√v + v / c') / c' ≤ 1 + K * (s + v / cl) / cl := by
  have hc'0 : 0 < c' := lt_of_lt_of_le hcl hc'
  have h1 : v / c' ≤ v / cl := div_le_div_of_nonneg_left hv hcl hc'
  have h2 : √v + v / c' ≤ s + v / cl := by linarith
  have h3 : (√v + v / c') / c' ≤ (s + v / cl) / cl := by
    have h0 : 0 ≤ √v + v / c' := by positivity
    calc (√v + v / c') / c' ≤ (s + v / cl) / c' := div_le_div_of_nonneg_right h2 hc'0.le
      _ ≤ (s + v / cl) / cl := div_le_div_of_nonneg_left (by linarith) hcl hc'
  have := mul_le_mul_of_nonneg_left h3 hK
  rw [mul_div_assoc, mul_div_assoc]
  linarith

/-- `(1 + e^{-100})(2/π) ≤ 0.636621`. -/
lemma two_div_pi_mul_le : (1 + Real.exp (-100)) * (2 / π) ≤ 0.636621 := by
  have hπ := Real.pi_gt_d6
  have he : Real.exp (-100) ≤ 1 / 10 ^ 6 := by
    have h : (10 : ℝ) ^ 6 ≤ Real.exp 100 := by
      simpa using le_exp_natCast_of_le_pow (c := 2) (k := 100) (by norm_num)
        (by linarith [Real.exp_one_gt_d9]) (by norm_num)
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h
  have h2 : 2 / π ≤ 2 / 3.141592 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ.le
  have h20 : 0 ≤ 2 / π := by positivity
  nlinarith

/-- `2e^{-40} ≤ 10⁻⁴`. -/
lemma two_exp_neg_forty_le : 2 * Real.exp (-40) ≤ 1 / 10 ^ 4 := by
  have h : (10 : ℝ) ^ 5 ≤ Real.exp 40 := by
    simpa using le_exp_natCast_of_le_pow (c := 2) (k := 40) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have h1 : Real.exp (-40) ≤ 1 / 10 ^ 5 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h
  linarith

/-- The variance tiers' ranges from block `2`, `3`, `4` on. -/
lemma varTier_bounds {m : ℕ} (hm : 2 ≤ m) :
    (0.3649 ≤ varLoTier m ∧ varHiTier m ≤ 0.6551)
      ∧ (3 ≤ m → 0.4219 ≤ varLoTier m ∧ varHiTier m ≤ 0.5731)
      ∧ (4 ≤ m → 0.4575 ≤ varLoTier m ∧ varHiTier m ≤ 0.5375) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h
  · subst h
    exact ⟨by norm_num [varLoTier, varHiTier], fun h => by omega, fun h => by omega⟩
  · subst h
    exact ⟨by norm_num [varLoTier, varHiTier], fun _ => by norm_num [varLoTier, varHiTier],
      fun h => by omega⟩
  · have e₁ : varLoTier m = 0.4575 := by
      simp only [varLoTier, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
    have e₂ : varHiTier m = 0.5375 := by
      simp only [varHiTier, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
    rw [e₁, e₂]
    exact ⟨by norm_num, fun _ => by norm_num, fun _ => by norm_num⟩

/-- `√x ≤ s` from `x ≤ s²`, `s ≥ 0`. -/
lemma sqrt_le_of_le_sq {x s : ℝ} (hs : 0 ≤ s) (h : x ≤ s ^ 2) : √x ≤ s :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hs))

/-! ### The difference phase two blocks past the depth -/

section Depths

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The difference phase two blocks on: `e^{-1} ≤ |D|e^{k+d}` gives `e ≤ |D|e^{k+d+2}`. -/
lemma exp_one_le_of_depth {k d : ℕ} {D : ℝ} (hd1 : Real.exp (-1) ≤ |D| * Real.exp ((k : ℝ) + d)) :
    Real.exp 1 ≤ |D| * Real.exp ((k : ℝ) + ((d + 2 : ℕ) : ℝ)) := by
  have he : Real.exp ((k : ℝ) + ((d + 2 : ℕ) : ℝ)) = Real.exp ((k : ℝ) + d) * Real.exp 2 := by
    rw [← Real.exp_add]
    push_cast
    ring_nf
  have h2 : Real.exp 1 = Real.exp (-1) * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  rw [he, h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hd1 (Real.exp_pos _).le

end Depths

/-! ### The pair mass over the post and the bridge

`E‖F_B(s₁)‖²‖F_B(s₂)‖² ≤ E‖F_B(s₁)‖²E‖F_B(s₂)‖²·exp(∑_{m∈B}(2(C_m(D) + C_m(S)) + e^{-m}/10²⁰))`
over any run `B` of consecutive blocks (the per-block `RMF.integral_normSq_mul_normSq_block_le`,
multiplied over the blocks by the exact product formulas). -/

section Mass

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- Consecutive prime ranges multiply, for the pair moment. -/
lemma integral_normSq_mul_normSq_Ico_split (hX : IsRademacherPrimeValues X μ) {y₀ y₁ y₂ : ℕ}
    (h₀ : y₀ ≤ y₁) (h₁ : y₁ ≤ y₂) (s₁ s₂ : ℂ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₂ s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₂ s₂ ω‖ ^ 2
        ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₁ ω‖
            ^ 2 * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s₂
              ω‖ ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₁ y₂ s₁ ω‖
            ^ 2 * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₁ y₂ s₂
              ω‖ ^ 2 ∂μ := by
  have hf := hX.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq,
    hf.integral_norm_randomEulerProductIco_sq_mul_sq,
    hf.integral_norm_randomEulerProductIco_sq_mul_sq, ← primesIco_union h₀ h₁,
    Finset.prod_union (disjoint_primesIco y₀ y₁ y₂)]

/-- Consecutive prime ranges multiply, for the one-point moment. -/
lemma integral_normSq_Ico_split (hX : IsRademacherPrimeValues X μ) {y₀ y₁ y₂ : ℕ}
    (h₀ : y₀ ≤ y₁) (h₁ : y₁ ≤ y₂) (s : ℂ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₂ s ω‖ ^ 2
        ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖
            ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₁ y₂ s ω‖
            ^ 2 ∂μ := by
  have hf := hX.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq, hf.integral_norm_randomEulerProductIco_sq,
    hf.integral_norm_randomEulerProductIco_sq, ← primesIco_union h₀ h₁,
    Finset.prod_union (disjoint_primesIco y₀ y₁ y₂)]

/-- **The pair mass over consecutive blocks**: over the blocks `m₁ ≤ m < m₁ + j` at offset
`θ ≥ 20` on the line `½ + σ`, `σ ≥ 0`,
`E‖F(s₁)‖²‖F(s₂)‖² ≤ E‖F(s₁)‖²E‖F(s₂)‖²·exp(∑_m (2(C_m(h₁-h₂) + C_m(h₁+h₂)) + e^{-m}/10²⁰))`,
`F` the Euler product over `(blockScale θ m₁, blockScale θ (m₁ + j)]`: the per-block
`RMF.integral_normSq_mul_normSq_block_le`, multiplied over the blocks. -/
theorem integral_normSq_mul_normSq_blocks_le (hX : IsRademacherPrimeValues X μ)
    {θ σ h₁ h₂ : ℝ} (hσ : 0 ≤ σ) (hθ : 20 ≤ θ) (m₁ j : ℕ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp (∑ m ∈ Finset.Ico m₁ (m₁ + j),
            (2 * (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m)
              + Real.exp (-(m : ℝ)) / 10 ^ 20)) := by
  have hf := hX.isRademacherRMF
  have hY : ∀ a b : ℕ, a ≤ b → ⌊blockScale θ a⌋₊ + 1 ≤ ⌊blockScale θ b⌋₊ + 1 := fun a b hab =>
    Nat.succ_le_succ (Nat.floor_mono (blockScale_mono θ hab))
  induction j with
  | zero =>
    have hempty : ∀ y : ℕ, primesIco y y = ∅ := fun y => by
      ext p
      simp only [mem_primesIco, Finset.notMem_empty, iff_false, not_and]
      intro _ h1 h2
      omega
    simp only [add_zero, Finset.Ico_self, Finset.sum_empty, Real.exp_zero, mul_one]
    rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq, hf.integral_norm_randomEulerProductIco_sq,
      hf.integral_norm_randomEulerProductIco_sq, hempty, Finset.prod_empty, Finset.prod_empty,
      Finset.prod_empty, one_mul]
  | succ j ih =>
    have hm : 20 ≤ ((m₁ + j : ℕ) : ℝ) + θ := by linarith [Nat.cast_nonneg (α := ℝ) (m₁ + j)]
    have hblock := integral_normSq_mul_normSq_block_le hX (θ := θ) (σ := σ) (h₁ := h₁) (h₂ := h₂)
      (m := m₁ + j) hσ (by linarith) hm
    have h01 := hY m₁ (m₁ + j) (by omega)
    have h12 := hY (m₁ + j) (m₁ + j + 1) (by omega)
    rw [show m₁ + (j + 1) = m₁ + j + 1 by omega,
      integral_normSq_mul_normSq_Ico_split hX h01 h12, integral_normSq_Ico_split hX h01 h12,
      integral_normSq_Ico_split hX h01 h12, Finset.sum_Ico_succ_top (by omega), Real.exp_add]
    -- nonnegativity
    have hP0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
      integral_nonneg fun ω => by positivity
    have hB0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ (m₁ + j)⌋₊ + 1) (⌊blockScale θ (m₁ + j + 1)⌋₊ + 1) (shiftLine σ h₁) ω‖
          ^ 2 * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ (m₁ + j)⌋₊ + 1) (⌊blockScale θ (m₁ + j + 1)⌋₊ + 1) (shiftLine σ h₂) ω‖
          ^ 2 ∂μ :=
      integral_nonneg fun ω => by positivity
    have hQ0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp (∑ m ∈ Finset.Ico m₁ (m₁ + j),
            (2 * (blockCosSum θ σ (h₁ - h₂) m + blockCosSum θ σ (h₁ + h₂) m)
              + Real.exp (-(m : ℝ)) / 10 ^ 20)) := by
      have h1 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ :=
        integral_nonneg fun ω => by positivity
      have h2 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale θ m₁⌋₊ + 1) (⌊blockScale θ (m₁ + j)⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
        integral_nonneg fun ω => by positivity
      positivity
    calc _ ≤ _ := mul_le_mul ih hblock hB0 hQ0
      _ = _ := by ring

end Mass

end RMF
