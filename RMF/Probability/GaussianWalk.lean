/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Probability.Independence.Basic
import RMF.Probability.GaussianEstimates

/-!
# Gaussian random walks, and the lower bound of Harper's (A1)

Harper's Probability Results 1 and 2 concern a random walk `S j = G 0 + … + G (j-1)` whose
increments are independent centred Gaussians with variances confined to a fixed interval.
This file sets up that walk and proves the **lower** half of the constant-barrier estimate
(A1) that both of them rest on:

`P(S j ≤ c for all j ≤ n)  ≥  2c · exp(-c² / 2V) / √(2π V)`,   `V = ∑_{m < n} v m`

(`RMF.IsGaussianWalk.le_measure_forall_le`).  Taking `c ≍ √V` — that is, `c ≍ √n` when the
variances are bounded above and below — the right-hand side is `≍ c / √n`.

## The route

1. *The walk is Gaussian.*  `RMF.IsGaussianWalk.map_finsetSum` gives the law of any finite
   block of increments; the marginal `RMF.IsGaussianWalk.map_walk` and the block law
   `RMF.IsGaussianWalk.map_walk_sub` are special cases.
2. *Lévy's inequality* (`RMF.IsGaussianWalk.measure_exists_gt_le`):
   `P(max_{j ≤ n} S j > c) ≤ 2 P(S n > c)`.  Split the event into the disjoint first-passage
   events `A k`; on `A k` the walk is already above `c`, so if the block `[k, n)` is
   non-negative — which happens with probability at least a half, *independently* of `A k`,
   since `A k` involves only the increments before `k` — then the endpoint is above `c` too.
3. *Reflection* (`RMF.IsGaussianWalk.measure_abs_le_le_measure_forall_le`): combining Lévy
   with the symmetry of the walk, `P(S j ≤ c ∀ j ≤ n) ≥ P(|S n| ≤ c)`.
4. *Anti-concentration* (`RMF.le_measure_Icc_gaussianReal`): the Gaussian density on
   `[-c, c]` is at least its endpoint value.

Nothing here is asymptotic, and **the increments are not assumed identically distributed** —
which is exactly the gap Harper points to when he notes that (A1) is hard to reference for
unequal (though comparable) variances.  The matching *upper* bound is a different and harder
argument, in `RMF/Probability/Barrier.lean` and `RMF/Probability/Overshoot.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*}

/-! ### The walk -/

/-- The partial sums `S j = G 0 + … + G (j - 1)` of a sequence of increments. -/
noncomputable def walk (G : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ := ∑ m ∈ Finset.range j, G m

lemma walk_apply (G : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) :
    walk G j ω = ∑ m ∈ Finset.range j, G m ω := by
  simp [walk, Finset.sum_apply]

@[simp]
lemma walk_zero (G : ℕ → Ω → ℝ) : walk G 0 = 0 := by simp [walk]

lemma walk_succ (G : ℕ → Ω → ℝ) (j : ℕ) : walk G (j + 1) = walk G j + G j := by
  simp [walk, Finset.sum_range_succ]

variable [MeasurableSpace Ω]

/-- **A Gaussian walk.**  The increments are independent and centred Gaussian, the `m`-th
having variance `v m`.  The variance bounds that Harper imposes are kept separate, as
hypotheses on `v`, so that this structure can be reused. -/
structure IsGaussianWalk (G : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0) (μ : Measure Ω) : Prop where
  /-- Each increment is measurable. -/
  measurable : ∀ m, Measurable (G m)
  /-- The increments are independent. -/
  indep : iIndepFun G μ
  /-- The `m`-th increment is centred Gaussian with variance `v m`. -/
  map_eq : ∀ m, μ.map (G m) = gaussianReal 0 (v m)

/-- **The step variances are bracketed**: `0 < vmin` and `vmin ≤ v m ≤ vmax` for every `m`.
Harper's barrier estimates are uniform over walks whose increments have variance in a fixed
positive band, and this is that band.  It is not a field of `RMF.IsGaussianWalk`, which is kept free
of the bounds so that it can be reused, but the three conditions always travel together. -/
structure VarBracket (v : ℕ → ℝ≥0) (vmin vmax : ℝ) : Prop where
  /-- The lower end of the band is positive. -/
  pos : 0 < vmin
  /-- Every step's variance is at least `vmin`. -/
  lo : ∀ i, vmin ≤ (v i : ℝ)
  /-- Every step's variance is at most `vmax`. -/
  hi : ∀ i, (v i : ℝ) ≤ vmax

variable {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurable_walk (h : IsGaussianWalk G v μ) (j : ℕ) :
    Measurable (walk G j) := by
  rw [funext (walk_apply G j)]
  exact Finset.measurable_sum _ fun m _ => h.measurable m

/-- **The law of any finite block of increments.**  Independent centred Gaussians add up to a
centred Gaussian whose variance is the sum. -/
lemma IsGaussianWalk.map_finsetSum (h : IsGaussianWalk G v μ) (s : Finset ℕ) :
    μ.map (∑ m ∈ s, G m) = gaussianReal 0 (∑ m ∈ s, v m) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, gaussianReal_zero_var]
      rw [show (0 : Ω → ℝ) = fun _ => (0 : ℝ) from rfl, Measure.map_const]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (G a), add_comm (v a),
        gaussianReal_add_gaussianReal_of_indepFun
          (h.indep.indepFun_finsetSum_of_notMem h.measurable ha) ih (h.map_eq a), zero_add]

/-- **The marginal law of the walk.** -/
lemma IsGaussianWalk.map_walk (h : IsGaussianWalk G v μ) (j : ℕ) :
    μ.map (walk G j) = gaussianReal 0 (∑ m ∈ Finset.range j, v m) :=
  h.map_finsetSum _

/-! ### Anti-concentration -/

/-- The total variance up to time `j` is at least `j·v₋`, hence nonzero.  Shared by the window
estimates below. -/
lemma sum_var_ne_zero_and_sqrt_le {vmin : ℝ}
    (hvmin : 0 < vmin) (hv : ∀ m, vmin ≤ (v m : ℝ)) {j : ℕ} (hj : j ≠ 0) :
    (∑ m ∈ Finset.range j, v m) ≠ 0 ∧
      √(2 * π * ((j : ℝ) * vmin)) ≤ √(2 * π * ((∑ m ∈ Finset.range j, v m : ℝ≥0) : ℝ)) := by
  have hsum : (vmin * j : ℝ) ≤ ((∑ m ∈ Finset.range j, v m : ℝ≥0) : ℝ) := by
    push_cast
    calc (vmin * j : ℝ) = ∑ _m ∈ Finset.range j, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ m ∈ Finset.range j, (v m : ℝ) := Finset.sum_le_sum fun m _ => hv m
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
  refine ⟨?_, Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos, hsum])⟩
  intro hcon
  rw [hcon] at hsum
  simp at hsum
  nlinarith

/-! ### Symmetry, and the law of a block of increments

Two facts feed the reflection (Lévy) argument for the lower bound of Harper's (A1): a centred
Gaussian puts at least half its mass on `[0, ∞)` (`RMF.half_le_gaussianReal_Ici`), and the
increments over a block `k ≤ m < n` again form a centred Gaussian, independent of everything
before `k`.
-/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The increments strictly between `k` and `n` are exactly the block sum. -/
lemma walk_sub_eq (G : ℕ → Ω → ℝ) {k n : ℕ} (hkn : k ≤ n) :
    walk G n - walk G k = ∑ m ∈ Finset.Ico k n, G m := by
  rw [walk, walk, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hkn]
  abel

/-- **The law of a block of the walk.** -/
lemma IsGaussianWalk.map_walk_sub (h : IsGaussianWalk G v μ) {k n : ℕ} (hkn : k ≤ n) :
    μ.map (walk G n - walk G k) = gaussianReal 0 (∑ m ∈ Finset.Ico k n, v m) := by
  rw [walk_sub_eq G hkn]
  exact h.map_finsetSum _

/-- **Half the mass moves forward.**  A block of the walk is non-negative with probability at
least a half — the symmetry input to the reflection argument. -/
lemma IsGaussianWalk.half_le_measure_walk_sub_nonneg (h : IsGaussianWalk G v μ) {k n : ℕ}
    (hkn : k ≤ n) : 1 / 2 ≤ μ {ω | 0 ≤ walk G n ω - walk G k ω} := by
  have hmeas : Measurable (walk G n - walk G k) :=
    (h.measurable_walk n).sub (h.measurable_walk k)
  have hset : μ {ω | 0 ≤ walk G n ω - walk G k ω}
      = μ.map (walk G n - walk G k) (Set.Ici 0) := by
    rw [Measure.map_apply hmeas measurableSet_Ici]
    rfl
  rw [hset, h.map_walk_sub hkn]
  exact half_le_gaussianReal_Ici _

/-! ### Lévy's inequality

The lower bound of Harper's (A1) rests on a reflection argument.  Split the event that the
walk ever exceeds `c` into the disjoint events `A k` — "`k` is the first time it does".  On
`A k` the walk is already above `c`, so if the remaining block `[k, n)` is non-negative then
the endpoint is above `c` too; and that block is non-negative with probability at least a half
(`RMF.IsGaussianWalk.half_le_measure_walk_sub_nonneg`) *independently* of `A k`, which depends
only on the increments before `k`.  Summing over `k` gives

`P(max_{j ≤ n} S j > c) ≤ 2 P(S n > c)`,

and hence `P(max_{j ≤ n} S j ≤ c) ≥ P(|S n| ≤ c)`.  The increments are not assumed identically
distributed: that is the gap Harper points to when he says (A1) is hard to reference.
-/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- For `j ≤ k`, the value `walk G j` is a function of the increments indexed by
`Finset.range k`. -/
lemma walk_eq_sum_attach (G : ℕ → Ω → ℝ) {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    walk G j ω = ∑ i ∈ (Finset.range k).attach, if (i : ℕ) < j then G i ω else 0 := by
  rw [Finset.sum_attach (Finset.range k) fun m => if m < j then G m ω else 0, walk_apply,
    ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- The partial sums of a prefix of increments, as a function of the prefix alone. -/
noncomputable def prefixSums (k : ℕ) (x : ↥(Finset.range k) → ℝ) : ℕ → ℝ :=
  fun j => ∑ i ∈ (Finset.range k).attach, if (i : ℕ) < j then x i else 0

/-- The partial sums of a block of increments, as a function of the block alone. -/
noncomputable def blockSums (k n : ℕ) (y : ↥(Finset.Ico k n) → ℝ) : ℕ → ℝ :=
  fun j => ∑ i ∈ (Finset.Ico k n).attach, if (i : ℕ) < j then y i else 0

lemma measurable_prefixSums (k : ℕ) : Measurable (prefixSums k) := by
  refine measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun i _ => ?_
  by_cases hij : (i : ℕ) < j
  · simpa [prefixSums, hij] using measurable_pi_apply i
  · simp [hij]

lemma measurable_blockSums (k n : ℕ) : Measurable (blockSums k n) := by
  refine measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun i _ => ?_
  by_cases hij : (i : ℕ) < j
  · simpa [hij] using measurable_pi_apply i
  · simp [hij]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma prefixSums_comp (G : ℕ → Ω → ℝ) {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    prefixSums k (fun i => G i ω) j = walk G j ω :=
  (walk_eq_sum_attach G hjk ω).symm

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma blockSums_comp (G : ℕ → Ω → ℝ) {k n j : ℕ} (hkj : k ≤ j) (hjn : j ≤ n) (ω : Ω) :
    blockSums k n (fun i => G i ω) j = walk G j ω - walk G k ω := by
  rw [blockSums, Finset.sum_attach (Finset.Ico k n) fun m => if m < j then G m ω else 0,
    ← Finset.sum_filter]
  have hfil : (Finset.Ico k n).filter (· < j) = Finset.Ico k j := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hfil, walk_apply, walk_apply, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hkj]
  ring

omit [IsProbabilityMeasure μ] in
/-- **The prefix is independent of a later block.** -/
lemma IsGaussianWalk.indepFun_prefixSums_blockSums (h : IsGaussianWalk G v μ) (k n : ℕ) :
    IndepFun (fun ω => prefixSums k fun i => G i ω)
      (fun ω => blockSums k n fun i => G i ω) μ := by
  have hdisj : Disjoint (Finset.range k) (Finset.Ico k n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    omega
  exact (h.indep.indepFun_finset _ _ hdisj h.measurable).comp
    (measurable_prefixSums k) (measurable_blockSums k n)

/-! ### First passage -/

/-- The event that `k` is the first time the walk exceeds `c`. -/
def firstPassage (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∀ j < k, walk G j ω ≤ c) ∧ c < walk G k ω}

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurableSet_firstPassage (h : IsGaussianWalk G v μ) (c : ℝ) (k : ℕ) :
    MeasurableSet (firstPassage G c k) := by
  have hrw : firstPassage G c k
      = (⋂ j ∈ Set.Iio k, {ω | walk G j ω ≤ c}) ∩ {ω | c < walk G k ω} := by
    ext ω
    simp [firstPassage]
  rw [hrw]
  exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (h.measurable_walk j) measurable_const).inter
    (measurableSet_lt measurable_const (h.measurable_walk k))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma pairwiseDisjoint_firstPassage (G : ℕ → Ω → ℝ) (c : ℝ) (s : Set ℕ) :
    s.PairwiseDisjoint (firstPassage G c) := by
  intro k _ l _ hkl
  refine Set.disjoint_left.mpr fun ω hk hl => ?_
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · exact absurd (hl.1 k hlt) (not_le.mpr hk.2)
  · exact absurd (hk.1 l hlt) (not_le.mpr hl.2)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma iUnion_firstPassage (G : ℕ → Ω → ℝ) (c : ℝ) (m : ℕ) :
    ⋃ k ∈ Finset.range (m + 1), firstPassage G c k = {ω | ∃ j ≤ m, c < walk G j ω} := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, firstPassage, exists_prop]
  constructor
  · rintro ⟨k, hk, -, hck⟩
    exact ⟨k, Nat.lt_succ_iff.mp hk, hck⟩
  · rintro ⟨j, hjm, hj⟩
    have hex : ∃ j, c < walk G j ω := ⟨j, hj⟩
    refine ⟨Nat.find hex, ?_, fun i hi => ?_, Nat.find_spec hex⟩
    · exact Nat.lt_succ_of_le ((Nat.find_min' hex hj).trans hjm)
    · exact not_lt.mp (Nat.find_min hex hi)

/-- The paths whose first passage above `c` happens at time `k` form a measurable set. -/
lemma measurableSet_passagePaths (c : ℝ) (k : ℕ) :
    MeasurableSet {f : ℕ → ℝ | (∀ j < k, f j ≤ c) ∧ c < f k} := by
  have hsplit : {f : ℕ → ℝ | (∀ j < k, f j ≤ c) ∧ c < f k}
      = (⋂ j ∈ Set.Iio k, {f : ℕ → ℝ | f j ≤ c}) ∩ {f : ℕ → ℝ | c < f k} := by
    ext f; simp
  rw [hsplit]
  exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (measurable_pi_apply j) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_pi_apply k))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- First passage, read off the prefix path alone. -/
lemma firstPassage_eq_preimage_prefixSums (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) :
    firstPassage G c k
      = (fun ω => prefixSums k fun i => G i ω) ⁻¹' {f : ℕ → ℝ | (∀ j < k, f j ≤ c) ∧ c < f k} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, firstPassage]
  rw [prefixSums_comp G le_rfl ω]
  exact and_congr_left fun _ =>
    forall_congr' fun j => forall_congr' fun hj => by rw [prefixSums_comp G hj.le ω]

/-- **Lévy's inequality.**  The running maximum of a Gaussian walk exceeds `c` with at most
twice the probability that the endpoint does. -/
theorem IsGaussianWalk.measure_exists_gt_le (h : IsGaussianWalk G v μ) (n : ℕ) (c : ℝ) :
    μ {ω | ∃ j ≤ n, c < walk G j ω} ≤ 2 * μ {ω | c < walk G n ω} := by
  classical
  set A : ℕ → Set Ω := firstPassage G c with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := h.measurableSet_firstPassage c
  have hunion : {ω | ∃ j ≤ n, c < walk G j ω} = ⋃ k ∈ Finset.range (n + 1), A k :=
    (iUnion_firstPassage G c n).symm
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint A :=
    pairwiseDisjoint_firstPassage G c _
  -- each first-passage event is at most twice its intersection with `{S n > c}`
  have hkey : ∀ k ∈ Finset.range (n + 1),
      μ (A k) ≤ 2 * μ (A k ∩ {ω | c < walk G n ω}) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    -- `A k` and the block `[k, n)` are independent
    have hApre : A k = (fun ω => prefixSums k fun i => G i ω) ⁻¹'
        {f : ℕ → ℝ | (∀ j < k, f j ≤ c) ∧ c < f k} := by
      rw [hA]; exact firstPassage_eq_preimage_prefixSums G c k
    have hBpre : {ω | 0 ≤ walk G n ω - walk G k ω}
        = (fun ω => blockSums k n fun i => G i ω) ⁻¹' {f : ℕ → ℝ | 0 ≤ f n} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, blockSums_comp G hkn le_rfl ω]
    have hBmeas : MeasurableSet {f : ℕ → ℝ | (∀ j < k, f j ≤ c) ∧ c < f k} :=
      measurableSet_passagePaths c k
    have hprod : μ (A k ∩ {ω | 0 ≤ walk G n ω - walk G k ω})
        = μ (A k) * μ {ω | 0 ≤ walk G n ω - walk G k ω} := by
      rw [hApre, hBpre]
      exact (h.indepFun_prefixSums_blockSums k n).measure_inter_preimage_eq_mul _ _ hBmeas
        (measurableSet_le measurable_const (measurable_pi_apply n))
    have hsub : A k ∩ {ω | 0 ≤ walk G n ω - walk G k ω} ⊆ A k ∩ {ω | c < walk G n ω} := by
      rintro ω ⟨hω, hω'⟩
      exact ⟨hω, lt_of_lt_of_le hω.2 (by simpa using sub_nonneg.mp hω')⟩
    have htwo : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    calc μ (A k) = 2 * (1 / 2) * μ (A k) := by rw [htwo, one_mul]
      _ = 2 * (μ (A k) * (1 / 2)) := by ring
      _ ≤ 2 * (μ (A k) * μ {ω | 0 ≤ walk G n ω - walk G k ω}) := by
          gcongr
          exact h.half_le_measure_walk_sub_nonneg hkn
      _ = 2 * μ (A k ∩ {ω | 0 ≤ walk G n ω - walk G k ω}) := by rw [hprod]
      _ ≤ 2 * μ (A k ∩ {ω | c < walk G n ω}) := by gcongr
  calc μ {ω | ∃ j ≤ n, c < walk G j ω}
      = ∑ k ∈ Finset.range (n + 1), μ (A k) := by
        rw [hunion, measure_biUnion_finset hdisj fun k _ => hAmeas k]
    _ ≤ ∑ k ∈ Finset.range (n + 1), 2 * μ (A k ∩ {ω | c < walk G n ω}) :=
        Finset.sum_le_sum hkey
    _ = 2 * ∑ k ∈ Finset.range (n + 1), μ (A k ∩ {ω | c < walk G n ω}) := by
        rw [Finset.mul_sum]
    _ = 2 * μ ((⋃ k ∈ Finset.range (n + 1), A k) ∩ {ω | c < walk G n ω}) := by
        rw [Set.iUnion₂_inter, measure_biUnion_finset
          (hdisj.mono fun k => Set.inter_subset_left)
          fun k _ => (hAmeas k).inter (measurableSet_lt measurable_const (h.measurable_walk n))]
    _ ≤ 2 * μ {ω | c < walk G n ω} := by gcongr; exact Set.inter_subset_right

/-- The two tails of the walk at time `n` have equal mass. -/
lemma IsGaussianWalk.measure_lt_neg_eq (h : IsGaussianWalk G v μ) (n : ℕ) (c : ℝ) :
    μ {ω | walk G n ω < -c} = μ {ω | c < walk G n ω} := by
  have h1 : μ {ω | walk G n ω < -c} = μ.map (walk G n) (Set.Iio (-c)) := by
    rw [Measure.map_apply (h.measurable_walk n) measurableSet_Iio]; rfl
  have h2 : μ {ω | c < walk G n ω} = μ.map (walk G n) (Set.Ioi c) := by
    rw [Measure.map_apply (h.measurable_walk n) measurableSet_Ioi]; rfl
  rw [h1, h2, h.map_walk n]
  exact gaussianReal_Iio_neg_eq_Ioi _ _

/-- **The reflection lower bound**, the lower half of Harper's (A1).  Staying below `c` for
all `n` steps is at least as likely as the endpoint alone landing in `[-c, c]`.

This is Lévy's inequality plus the symmetry of the walk, and it is *not* asymptotic: it holds
for every `n` and every `c ≥ 0`, with no largeness hypothesis and no assumption that the
increments are identically distributed. -/
theorem IsGaussianWalk.measure_abs_le_le_measure_forall_le (h : IsGaussianWalk G v μ)
    (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    μ {ω | |walk G n ω| ≤ c} ≤ μ {ω | ∀ j ≤ n, walk G j ω ≤ c} := by
  have hEm : MeasurableSet {ω | |walk G n ω| ≤ c} :=
    measurableSet_le (h.measurable_walk n).abs measurable_const
  have hFm : MeasurableSet {ω | ∀ j ≤ n, walk G j ω ≤ c} := by
    have : {ω | ∀ j ≤ n, walk G j ω ≤ c} = ⋂ j ∈ Set.Iic n, {ω | walk G j ω ≤ c} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (h.measurable_walk j) measurable_const
  -- the complements
  have hFc : {ω | ∀ j ≤ n, walk G j ω ≤ c}ᶜ = {ω | ∃ j ≤ n, c < walk G j ω} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, exists_prop]
  have hEc : {ω | |walk G n ω| ≤ c}ᶜ
      = {ω | walk G n ω < -c} ∪ {ω | c < walk G n ω} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union, abs_le, not_and_or, not_le]
  have hdisj : Disjoint {ω | walk G n ω < -c} {ω | c < walk G n ω} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith
  -- the complement of the barrier event is no larger than the complement of the window event
  have hcompl : μ {ω | ∀ j ≤ n, walk G j ω ≤ c}ᶜ ≤ μ {ω | |walk G n ω| ≤ c}ᶜ := by
    rw [hFc, hEc, measure_union hdisj (measurableSet_lt measurable_const (h.measurable_walk n)),
      h.measure_lt_neg_eq n c, ← two_mul]
    exact h.measure_exists_gt_le n c
  -- and complements are what the two probabilities differ by
  have hE := measure_add_measure_compl hEm (μ := μ)
  have hF := measure_add_measure_compl hFm (μ := μ)
  have hle : μ {ω | |walk G n ω| ≤ c} + μ {ω | |walk G n ω| ≤ c}ᶜ
      ≤ μ {ω | ∀ j ≤ n, walk G j ω ≤ c} + μ {ω | |walk G n ω| ≤ c}ᶜ := by
    rw [hE, ← hF]
    gcongr
  exact ENNReal.add_le_add_iff_right (measure_ne_top _ _) |>.mp hle

/-- **The lower bound of Harper's (A1).**  With `V = ∑_{m < n} v m` the variance at time `n`,
`P(S j ≤ c for all j ≤ n) ≥ 2c · exp(-c² / 2V) / √(2π V)` for every `n` and every `c ≥ 0`.  At
`c ≍ √V` (`c ≍ √n` for bracketed variances) the right-hand side is `≍ c/√n`.  The reflection bound
`RMF.IsGaussianWalk.measure_abs_le_le_measure_forall_le` and the Gaussian density estimate; no
largeness hypothesis, and the increments need not be identically distributed. -/
theorem IsGaussianWalk.le_measure_forall_le (h : IsGaussianWalk G v μ) {n : ℕ}
    (hV : (∑ m ∈ Finset.range n, v m) ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal (2 * c * rexp (-c ^ 2 / (2 * (∑ m ∈ Finset.range n, v m : ℝ≥0)))
        / √(2 * π * (∑ m ∈ Finset.range n, v m : ℝ≥0)))
      ≤ μ {ω | ∀ j ≤ n, walk G j ω ≤ c} := by
  refine le_trans ?_ (h.measure_abs_le_le_measure_forall_le n hc)
  have hset : μ {ω | |walk G n ω| ≤ c}
      = gaussianReal 0 (∑ m ∈ Finset.range n, v m) (Set.Icc (-c) c) := by
    rw [← h.map_walk n, Measure.map_apply (h.measurable_walk n) measurableSet_Icc]
    congr 1
    ext ω
    simp [abs_le]
  rw [hset]
  exact le_measure_Icc_gaussianReal hV c

/-! ### The negated walk -/

omit [IsProbabilityMeasure μ] in
/-- The negated walk is again a Gaussian walk, with the same variances. -/
lemma IsGaussianWalk.neg (h : IsGaussianWalk G v μ) : IsGaussianWalk (fun m => -G m) v μ where
  measurable m := (h.measurable m).neg
  indep := h.indep.comp (fun _ x => -x) fun _ => measurable_neg
  map_eq m := by
    have hcomp : (-G m : Ω → ℝ) = (fun x : ℝ => -x) ∘ G m := rfl
    rw [hcomp, ← Measure.map_map measurable_neg (h.measurable m), h.map_eq m,
      gaussianReal_map_neg, neg_zero]

/-! ### Centring a drifted Gaussian family

`IsGaussianWalk` asks for *centred* increments, but the families that arise carry a drift: Harper's
block Gaussian `N m` has mean `θ m ≈ 1`, one per block, and Proposition 5 consumes the pair
`N m = G m + θ m` with `G` the centred walk.  Subtracting the mean is the whole of the translation,
and it costs nothing: `gaussianReal_map_sub_const` moves the law, `iIndepFun.comp` moves the
independence, and measurability is `Measurable.sub_const`.

The point of isolating this is that *nothing here is about primes*.  Any family with Gaussian
marginals and independent coordinates centres, whatever its means are. -/

omit [IsProbabilityMeasure μ] in
/-- Subtracting its own mean centres a Gaussian. -/
lemma map_sub_const_of_map_eq_gaussianReal {N : Ω → ℝ} {c : ℝ} {u : ℝ≥0} (hN : Measurable N)
    (hlaw : μ.map N = gaussianReal c u) :
    μ.map (fun ω => N ω - c) = gaussianReal 0 u := by
  have hcomp : (fun ω => N ω - c) = (fun x : ℝ => x - c) ∘ N := rfl
  have hsub : Measurable fun x : ℝ => x - c := measurable_id.sub_const c
  rw [hcomp, ← Measure.map_map hsub hN, hlaw,
    gaussianReal_map_sub_const, sub_self]

omit [IsProbabilityMeasure μ] in
/-- **A drifted Gaussian family, centred into a walk.**

The increments `G m = N m - c m` are what Proposition 5's `hGw` asks for, and `N m = G m + c m`
recovers its `hNG` by `ring`.  Note the hypotheses are needed at *every* index, not just below a
horizon — `IsGaussianWalk` is a statement about the whole family. -/
theorem isGaussianWalk_sub_const {N : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hNm : ∀ m, Measurable (N m)) (hNi : iIndepFun N μ)
    (hlaw : ∀ m, μ.map (N m) = gaussianReal (c m) (v m)) :
    IsGaussianWalk (fun m ω => N m ω - c m) v μ where
  measurable m := (hNm m).sub_const (c m)
  indep := by
    have h := hNi.comp (fun m => fun x : ℝ => x - c m) fun m => measurable_id.sub_const (c m)
    simpa [Function.comp_def] using h
  map_eq m := map_sub_const_of_map_eq_gaussianReal (hNm m) (hlaw m)

end RMF

