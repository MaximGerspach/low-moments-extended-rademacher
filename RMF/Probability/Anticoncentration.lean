/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Overshoot

/-!
# Harper's (A2): anti-concentration of the running maximum

Harper's (A2) states that for a Gaussian walk with comparable variances, for any `b` and any
`c ≥ 1`,

`P( max_{j ≤ n} S j ∈ [b, b + c] ) ≪ c / √n`.

We take the window **half-open**, `{b < max ≤ b+c}`.  That is not a weakening: in the one place
Harper applies (A2) the two barriers being compared are constant, so the difference of the two
barrier events is exactly `{S j ≤ b+c ∀ j} ∖ {S j ≤ b ∀ j} = {b < max ≤ b+c}`.  It also matches
`RMF.firstPassage`, which crosses strictly, and it avoids having to show `{max = b}` is null — a
case Harper passes over, and one that is genuinely delicate at `b = 0`, where `S 0 = 0`.

The proof has four steps.  Let `F k` be the event that `k` is the first time the walk rises above
`b`; these are disjoint and their union over `k ≤ n` is `{max > b}`.

1. Decompose along `F k`.
2. For `k ≤ n/2`: on `F k` the walk is already above `b`, so staying below `b + c` forces the
   suffix never to rise by more than `c`.  Prefix and suffix are independent, so the probabilities
   multiply, and (A1) bounds the suffix factor by `≪ c/√(n-k) ≪ c/√n`.  Summing costs nothing,
   since `∑_k P(F k) ≤ 1`.
3. For `k > n/2`: the maximum is attained after time `⌊n/2⌋`, so it equals `S_{⌊n/2⌋} + M` with
   `M` the running maximum of the second half — independent of `S_{⌊n/2⌋}`.
4. `S_{⌊n/2⌋}` is Gaussian of variance `≍ n`, so a window of width `c` costs `≪ c/√n`, *uniformly
   in the shift* `M`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-- The paths that stay below `c` on `[k, n]` form a measurable set. -/
lemma measurableSet_suffixPaths (c : ℝ) (k n : ℕ) :
    MeasurableSet {f : ℕ → ℝ | ∀ j, k ≤ j → j ≤ n → f j ≤ c} := by
  have hsplit : {f : ℕ → ℝ | ∀ j, k ≤ j → j ≤ n → f j ≤ c}
      = ⋂ j ∈ Set.Icc k n, {f : ℕ → ℝ | f j ≤ c} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
    exact ⟨fun hf j hj => hf j hj.1 hj.2, fun hf j h1 h2 => hf j ⟨h1, h2⟩⟩
  rw [hsplit]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (measurable_pi_apply j) measurable_const

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The suffix barrier event, read off the block path alone. -/
lemma suffixBarrier_eq_preimage_blockSums (G : ℕ → Ω → ℝ) (c : ℝ) (k n : ℕ) :
    {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c}
      = (fun ω => blockSums k n fun i => G i ω) ⁻¹'
          {f : ℕ → ℝ | ∀ j, k ≤ j → j ≤ n → f j ≤ c} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact forall_congr' fun j => forall_congr' fun hkj => forall_congr' fun hjn => by
    rw [blockSums_comp G hkj hjn ω]

omit [IsProbabilityMeasure μ] in
/-- **(A2), step 2: the factorisation.**  First passage at time `k` depends only on the prefix,
the suffix barrier only on the block after `k`, and the two are independent. -/
lemma IsGaussianWalk.measure_firstPassage_inter_suffixBarrier (h : IsGaussianWalk G v μ)
    (b c : ℝ) (k n : ℕ) :
    μ (firstPassage G b k ∩ {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c})
      = μ (firstPassage G b k) * μ {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c} := by
  rw [firstPassage_eq_preimage_prefixSums, suffixBarrier_eq_preimage_blockSums]
  exact (h.indepFun_prefixSums_blockSums k n).measure_inter_preimage_eq_mul _ _
    (measurableSet_passagePaths b k) (measurableSet_suffixPaths c k n)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **(A2), step 2: the containment.**  Once the walk has passed above `b` at time `k`, it can
only stay below `b + c` if the suffix never rises by more than `c`.  This is where the window
width `c` becomes a barrier for the suffix walk. -/
lemma firstPassage_inter_barrier_subset (G : ℕ → Ω → ℝ) (b c : ℝ) (k n : ℕ) :
    firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c}
      ⊆ firstPassage G b k ∩ {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c} := by
  rintro ω ⟨hk, hb⟩
  exact ⟨hk, fun j _ hjn => by linarith [hb j hjn, hk.2]⟩

/-! ### Shifting the walk

Every step of Harper’s curved-barrier induction applies a barrier estimate to a *suffix* of the
walk: having controlled the path up to time `k`, one restarts at `k` and asks the same question of
`G_k, G_{k+1}, …`.  For that to be legitimate the suffix must itself be a Gaussian walk of the same
class, with the variances shifted — which is the content of `IsGaussianWalk.shift`.  It is short,
but nothing downstream can be stated without it. -/

omit [IsProbabilityMeasure μ] in
/-- **The suffix walk.**  Dropping the first `k` increments leaves a Gaussian walk with the
shifted variances.  Every barrier estimate applies to it verbatim, which is what lets an induction
slide the barrier along the path.  Variance bounds are preserved for free, being universally
quantified over the index. -/
lemma IsGaussianWalk.shift (h : IsGaussianWalk G v μ) (k : ℕ) :
    IsGaussianWalk (fun m => G (m + k)) (fun m => v (m + k)) μ where
  measurable m := h.measurable (m + k)
  indep := h.indep.precomp fun _ _ hab => by omega
  map_eq m := h.map_eq (m + k)

omit [MeasurableSpace Ω] in
/-- The suffix walk is an increment of the original: `S′_j = S_{k+j} − S_k`. -/
lemma walk_shift (G : ℕ → Ω → ℝ) (k j : ℕ) (ω : Ω) :
    walk (fun m => G (m + k)) j ω = walk G (k + j) ω - walk G k ω := by
  simp only [walk_apply, Finset.sum_range_add]
  rw [add_sub_cancel_left]
  exact Finset.sum_congr rfl fun m _ => by rw [add_comm]

/-- **The shifted window, for (A2).**  `P(S_j + M ∈ [b, b + c]) ≤ c/√(2π j v₋)` for any measurable
`M` independent of `S_j`: conditioning on `M` moves the window but not its length, and the Gaussian
bound is uniform in the location.  Step 4 of (A2) uses it at `j = ⌊n/2⌋`, with `M` the running
maximum of the second half of the walk. -/
lemma IsGaussianWalk.measure_walk_add_mem_Icc_le (h : IsGaussianWalk G v μ) {vmin : ℝ}
    (hvmin : 0 < vmin) (hv : ∀ m, vmin ≤ (v m : ℝ)) {j : ℕ} (hj : j ≠ 0)
    {M : Ω → ℝ} (hM : Measurable M) (hindep : IndepFun (walk G j) M μ)
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (μ {ω | walk G j ω + M ω ∈ Set.Icc b (b + c)}).toReal ≤ c / √(2 * π * ((j : ℝ) * vmin)) := by
  obtain ⟨hne, hsqrt⟩ := sum_var_ne_zero_and_sqrt_le hvmin hv hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
  have hspos : (0 : ℝ) < √(2 * π * ((j : ℝ) * vmin)) :=
    Real.sqrt_pos.mpr (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal (div_nonneg hc hspos.le) ?_
  refine (measure_add_mem_Icc_le_of_indepFun hne (h.measurable_walk j) hM hindep
    (h.map_walk j) b c).trans ?_
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hc hspos hsqrt)

/-! ### The suffix barrier

The suffix event of the factorisation is a barrier event for the shifted walk, which is what lets
(A1) be applied to it. -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Staying within `c` of `S k` on `[k, n]` is exactly the barrier event at height `c` for the
suffix walk, run for `n - k` steps. -/
lemma suffixBarrier_eq_shiftBarrier (G : ℕ → Ω → ℝ) (c : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c}
      = {ω | ∀ i ≤ n - k, walk (fun m => G (m + k)) i ω ≤ c} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hf i hi
    rw [walk_shift]
    exact hf (k + i) (Nat.le_add_right _ _) (by omega)
  · intro hg j hkj hjn
    have hi := hg (j - k) (by omega)
    rw [walk_shift, show k + (j - k) = j from by omega] at hi
    exact hi

/-- The constant of (A1)'s upper bound,
`√3 + 5((c + 1)/√(2π v₋) + overshootConstMgf v₋ v₊/√(π v₋))`, with the overshoot constant from the
moment generating function.  It depends only on the variance bounds and the barrier height, not on
the walk, which is what lets (A1) be applied to every shifted walk and the results be summed over
`k`. -/
noncomputable def barrierConst (vmin vmax c : ℝ) : ℝ :=
  √3 + 5 * ((c + 1) / √(2 * π * vmin) + overshootConstMgf vmin vmax / √(π * vmin))

/-- **(A2), the near half.**  For a first passage at time `k`, the probability of also staying
below `b + c` is at most `P(F k)` times `≪ c/√(n-k)`.  Everything to the right of `P(F k)` is
independent of `k` except the `√(n-k)`, which is why the sum over `k ≤ n/2` telescopes into a
single `c/√n`. -/
theorem IsGaussianWalk.measure_firstPassage_inter_barrier_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax)
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) {n k : ℕ} (hkn : k ≤ n)
    (hnk : 1 ≤ n - k) :
    (μ (firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c})).toReal
      ≤ (μ (firstPassage G b k)).toReal * (barrierConst vmin vmax c / √((n - k : ℕ) : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  calc (μ (firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c})).toReal
      ≤ (μ (firstPassage G b k ∩
          {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c})).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono (firstPassage_inter_barrier_subset G b c k n))
    _ = (μ (firstPassage G b k)).toReal
          * (μ {ω | ∀ j, k ≤ j → j ≤ n → walk G j ω - walk G k ω ≤ c}).toReal := by
        rw [h.measure_firstPassage_inter_suffixBarrier, ENNReal.toReal_mul]
    _ = (μ (firstPassage G b k)).toReal * barrierProb μ (fun m => G (m + k)) c (n - k) := by
        rw [suffixBarrier_eq_shiftBarrier G c hkn, barrierProb]
    _ ≤ (μ (firstPassage G b k)).toReal * (barrierConst vmin vmax c / √((n - k : ℕ) : ℝ)) := by
        gcongr
        exact (h.shift k).barrierProb_le_of_comparable_mgf hc
          ⟨hvmin, fun i => hlo (i + k), fun i => hhi (i + k)⟩ hnk

/-- The constant of (A1) is non-negative. -/
lemma barrierConst_nonneg {vmin vmax c : ℝ} (hvmin : 0 < vmin) (hc : 0 ≤ c) :
    0 ≤ barrierConst vmin vmax c := by
  have hD := overshootConstMgf_nonneg (vmax := vmax) hvmin
  have h2 : (0 : ℝ) < √(π * vmin) := Real.sqrt_pos.2 (by positivity)
  have ha : (0 : ℝ) ≤ (c + 1) / √(2 * π * vmin) := by positivity
  have hb : (0 : ℝ) ≤ overshootConstMgf vmin vmax / √(π * vmin) := div_nonneg hD h2.le
  have hs : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  rw [barrierConst]
  linarith

/-- **(A2), the near half.**  Summing the per-passage bound over `k ≤ n/2`.  Two things make the
sum collapse: the first-passage events are disjoint, so their probabilities sum to at most `1`;
and for `k ≤ n/2` the suffix still has at least half the steps, so `1/√(n-k) ≤ √2/√n` uniformly
in `k`.  The result is a single `c/√n`, with no loss from the summation. -/
theorem IsGaussianWalk.measure_biUnion_firstPassage_inter_barrier_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax)
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    (μ (⋃ k ∈ Finset.range (n / 2 + 1),
        (firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c}))).toReal
      ≤ barrierConst vmin vmax c * √2 / √(n : ℝ) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  set K := barrierConst vmin vmax c with hK
  have hKnn : 0 ≤ K := barrierConst_nonneg hvmin hc
  have hnR : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  set B := {ω | ∀ j ≤ n, walk G j ω ≤ b + c} with hBdef
  have hBmeas : MeasurableSet B := h.measurableSet_forall_le (b + c) n
  have hmeas : ∀ k, MeasurableSet (firstPassage G b k ∩ B) := fun k =>
    (h.measurableSet_firstPassage b k).inter hBmeas
  have hdisj : (↑(Finset.range (n / 2 + 1)) : Set ℕ).PairwiseDisjoint
      fun k => firstPassage G b k ∩ B := fun i hi j hj hij =>
    (pairwiseDisjoint_firstPassage G b _ hi hj hij).mono Set.inter_subset_left
      Set.inter_subset_left
  -- each term, with the `√(n-k)` replaced by the uniform `√n/√2`
  have hstep : ∀ k ∈ Finset.range (n / 2 + 1),
      (μ (firstPassage G b k ∩ B)).toReal
        ≤ (μ (firstPassage G b k)).toReal * (K * √2 / √(n : ℝ)) := by
    intro k hk
    have hk2 : k ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkn : k ≤ n := by omega
    have hnk : 1 ≤ n - k := by omega
    have hnkR : (0 : ℝ) < √((n - k : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnk)
    have hcmp : √(n : ℝ) ≤ √2 * √((n - k : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      have : n ≤ 2 * (n - k) := by omega
      exact_mod_cast this
    refine (h.measure_firstPassage_inter_barrier_le ⟨hvmin, hlo, hhi⟩ b hc hkn hnk).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    rw [div_le_div_iff₀ hnkR hnR]
    nlinarith [Real.sqrt_nonneg ((n - k : ℕ) : ℝ), Real.sqrt_nonneg (n : ℝ)]
  -- the first-passage events are disjoint, so their masses sum to at most one
  have hsum1 : ∑ k ∈ Finset.range (n / 2 + 1), (μ (firstPassage G b k)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top μ _),
      ← measure_biUnion_finset (pairwiseDisjoint_firstPassage G b _)
        (fun k _ => h.measurableSet_firstPassage b k)]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  rw [measure_biUnion_finset hdisj (fun k _ => hmeas k),
    ENNReal.toReal_sum (fun k _ => measure_ne_top μ _)]
  calc ∑ k ∈ Finset.range (n / 2 + 1), (μ (firstPassage G b k ∩ B)).toReal
      ≤ ∑ k ∈ Finset.range (n / 2 + 1),
          (μ (firstPassage G b k)).toReal * (K * √2 / √(n : ℝ)) := Finset.sum_le_sum hstep
    _ = (∑ k ∈ Finset.range (n / 2 + 1), (μ (firstPassage G b k)).toReal)
          * (K * √2 / √(n : ℝ)) := by rw [← Finset.sum_mul]
    _ ≤ 1 * (K * √2 / √(n : ℝ)) := by gcongr
    _ = K * √2 / √(n : ℝ) := one_mul _

/-! ### The far half: `k > n/2`

Here the suffix is too short for (A1) to say anything, and Harper argues differently.  On the event
that the first passage happens after `⌊n/2⌋`, the maximum is attained after that time, so it equals
`S_{⌊n/2⌋} + M` with `M` the running maximum of the second half — a function of the later increments
alone, hence independent of `S_{⌊n/2⌋}`.  The window bound under an independent shift then applies
with no knowledge of `M` whatsoever. -/

/-- The running maximum of a path over a finite set of times, floored at `0`.  The floor is
harmless in the application — the time `⌊n/2⌋` itself contributes exactly `0` — and it removes the
need to carry a non-emptiness proof through the definition. -/
noncomputable def pathMax (s : Finset ℕ) (f : ℕ → ℝ) : ℝ := s.fold max 0 f

lemma pathMax_le {s : Finset ℕ} {f : ℕ → ℝ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ j ∈ s, f j ≤ C) :
    pathMax s f ≤ C :=
  (Finset.fold_max_le C).2 ⟨h0, hf⟩

lemma le_pathMax {s : Finset ℕ} {f : ℕ → ℝ} {j : ℕ} (hj : j ∈ s) : f j ≤ pathMax s f :=
  (Finset.le_fold_max (f j)).2 (Or.inr ⟨j, hj, le_rfl⟩)

lemma measurable_pathMax (s : Finset ℕ) : Measurable (pathMax s) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hrw : pathMax (∅ : Finset ℕ) = fun _ : ℕ → ℝ => (0 : ℝ) := by
        funext f; simp [pathMax]
      rw [hrw]; exact measurable_const
  | insert a s ha ih =>
      have hrw : pathMax (insert a s) = fun f : ℕ → ℝ => max (f a) (pathMax s f) := by
        funext f; simp only [pathMax, Finset.fold_insert ha]
      rw [hrw]
      exact (measurable_pi_apply a).max ih

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- The suffix running maximum, read off the block path alone. -/
lemma pathMax_eq_blockSums (G : ℕ → Ω → ℝ) {m n : ℕ} (ω : Ω) :
    pathMax (Finset.Ico (m + 1) (n + 1)) (fun j => walk G j ω - walk G m ω)
      = pathMax (Finset.Ico (m + 1) (n + 1)) (blockSums m n fun i => G i ω) := by
  refine Finset.fold_congr ?_
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact (blockSums_comp G (by omega) (by omega) ω).symm

omit [IsProbabilityMeasure μ] in
/-- The endpoint of the first half is independent of the running maximum of the second. -/
lemma IsGaussianWalk.indepFun_walk_pathMax (h : IsGaussianWalk G v μ) (m n : ℕ) :
    IndepFun (walk G m)
      (fun ω => pathMax (Finset.Ico (m + 1) (n + 1)) fun j => walk G j ω - walk G m ω) μ := by
  refine ((h.indepFun_prefixSums_blockSums m n).comp (measurable_pi_apply m)
    (measurable_pathMax (Finset.Ico (m + 1) (n + 1)))).congr ?_ ?_
  · filter_upwards with ω
    exact prefixSums_comp G le_rfl ω
  · filter_upwards with ω
    exact (pathMax_eq_blockSums G ω).symm

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **(A2), the far half: the containment.**  If the first passage above `b` happens at a time
`k > m`, and the walk never exceeds `b + c`, then `S_m + M` lies in `[b, b+c]`: it is at least
`S_k > b` because `k` is one of the times the maximum ranges over, and at most `b + c` because
every `S_j` is. -/
lemma firstPassage_inter_barrier_subset_far (G : ℕ → Ω → ℝ) (b : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {m n k : ℕ} (hmk : m < k) (hkn : k ≤ n) :
    firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c}
      ⊆ {ω | walk G m ω
          + pathMax (Finset.Ico (m + 1) (n + 1)) (fun j => walk G j ω - walk G m ω)
            ∈ Set.Icc b (b + c)} := by
  rintro ω ⟨hk, hB⟩
  have hmb : walk G m ω ≤ b := hk.1 m hmk
  constructor
  · have hmem : k ∈ Finset.Ico (m + 1) (n + 1) := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    have := le_pathMax (f := fun j => walk G j ω - walk G m ω) hmem
    linarith [hk.2]
  · have : pathMax (Finset.Ico (m + 1) (n + 1)) (fun j => walk G j ω - walk G m ω)
        ≤ b + c - walk G m ω := by
      refine pathMax_le (by linarith) fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      have := hB j (by omega)
      linarith
    linarith

/-- **(A2), the far half.**  For `k > ⌊n/2⌋` the suffix is too short for (A1), but the maximum is
then attained after time `⌊n/2⌋`, so it equals `S_{⌊n/2⌋} + M` with `M` independent of
`S_{⌊n/2⌋}`.  A Gaussian of variance `≳ n` puts at most `c/√(2π ⌊n/2⌋ v₋)` on a window of length
`c`, uniformly in the shift, and nothing about `M` is needed beyond independence. -/
theorem IsGaussianWalk.measure_biUnion_firstPassage_far_le (h : IsGaussianWalk G v μ) {vmin : ℝ}
    (hvmin : 0 < vmin) (hlo : ∀ i, vmin ≤ (v i : ℝ)) (b : ℝ) {c : ℝ} (hc : 0 ≤ c) {n : ℕ}
    (hn : 2 ≤ n) :
    (μ (⋃ k ∈ Finset.Ico (n / 2 + 1) (n + 1),
        (firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c}))).toReal
      ≤ c / √(2 * π * (((n / 2 : ℕ) : ℝ) * vmin)) := by
  set m := n / 2 with hmdef
  have hm0 : m ≠ 0 := by omega
  have hMmeas : Measurable fun ω =>
      pathMax (Finset.Ico (m + 1) (n + 1)) fun j => walk G j ω - walk G m ω :=
    (measurable_pathMax _).comp
      (measurable_pi_lambda _ fun j => (h.measurable_walk j).sub (h.measurable_walk m))
  have hsub : (⋃ k ∈ Finset.Ico (m + 1) (n + 1),
      (firstPassage G b k ∩ {ω | ∀ j ≤ n, walk G j ω ≤ b + c}))
      ⊆ {ω | walk G m ω
          + pathMax (Finset.Ico (m + 1) (n + 1)) (fun j => walk G j ω - walk G m ω)
            ∈ Set.Icc b (b + c)} := by
    refine Set.iUnion₂_subset fun k hk => ?_
    have hk' := Finset.mem_Ico.1 hk
    exact firstPassage_inter_barrier_subset_far G b hc (by omega) (by omega)
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)) ?_
  exact h.measure_walk_add_mem_Icc_le hvmin hlo hm0 hMmeas (h.indepFun_walk_pathMax m n) b hc

/-! ### (A2) itself -/

/-- The constant of (A2), `barrierConst v₋ v₊ c · √2 + 2c/√(2π v₋)`: it depends only on the
variance bounds and the window width. -/
noncomputable def maxWindowConst (vmin vmax c : ℝ) : ℝ :=
  barrierConst vmin vmax c * √2 + 2 * c / √(2 * π * vmin)

lemma one_le_maxWindowConst {vmin vmax c : ℝ} (hvmin : 0 < vmin) (hc : 0 ≤ c) :
    1 ≤ maxWindowConst vmin vmax c := by
  have hD := overshootConstMgf_nonneg (vmax := vmax) hvmin
  have hpv : (0 : ℝ) < √(π * vmin) := Real.sqrt_pos.2 (by positivity)
  have hb : (0 : ℝ) ≤ overshootConstMgf vmin vmax / √(π * vmin) := div_nonneg hD hpv.le
  have ha : (0 : ℝ) ≤ (c + 1) / √(2 * π * vmin) := by positivity
  have h3 : (1 : ℝ) ≤ √3 := Real.one_le_sqrt.2 (by norm_num)
  have h2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have hK : (1 : ℝ) ≤ barrierConst vmin vmax c := by rw [barrierConst]; linarith
  have hlast : (0 : ℝ) ≤ 2 * c / √(2 * π * vmin) := by positivity
  have hprod : (1 : ℝ) ≤ barrierConst vmin vmax c * √2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ barrierConst vmin vmax c * √2 := by
          exact mul_le_mul hK h2 (by norm_num) (by linarith)
  rw [maxWindowConst]
  linarith

lemma barrierConst_mono {vmin vmax c c' : ℝ} (hvmin : 0 < vmin) (hcc : c ≤ c') :
    barrierConst vmin vmax c ≤ barrierConst vmin vmax c' := by
  have hpos : (0 : ℝ) < √(2 * π * vmin) := Real.sqrt_pos.2 (by positivity)
  rw [barrierConst, barrierConst]
  gcongr

/-- **The (A1) constant is affine in the barrier height**, with slope `5/√(2π v₋)`.  Linear growth,
not only monotonicity, is what the application needs: a barrier height of size `Λ⁴` then costs a
constant of size `Λ⁴`, not merely something larger than `A(0)`. -/
lemma barrierConst_eq_affine (vmin vmax c : ℝ) :
    barrierConst vmin vmax c = barrierConst vmin vmax 0 + 5 * c / √(2 * π * vmin) := by
  rw [barrierConst, barrierConst]
  ring

/-- The linear-growth constant of `RMF.barrierConst`, `barrierConst v₋ v₊ 0 + 5K/√(2π v₋)`:
`A(c) ≤ barrierConstBound v₋ v₊ K · M` whenever `c ≤ K·M` and `M ≥ 1`. -/
noncomputable def barrierConstBound (vmin vmax K : ℝ) : ℝ :=
  barrierConst vmin vmax 0 + 5 * K / √(2 * π * vmin)

lemma barrierConstBound_nonneg {vmin vmax K : ℝ} (hvmin : 0 < vmin) (hK : 0 ≤ K) :
    0 ≤ barrierConstBound vmin vmax K := by
  have h0 : (0 : ℝ) ≤ barrierConst vmin vmax 0 := barrierConst_nonneg hvmin le_rfl
  have h1 : (0 : ℝ) ≤ 5 * K / √(2 * π * vmin) := by positivity
  rw [barrierConstBound]
  linarith

/-- **Linear growth of the (A1) constant.**  The `M ≥ 1` is what lets the constant term `A(0)` be
absorbed into the leading one. -/
lemma barrierConst_le_mul {vmin vmax c K M : ℝ} (hvmin : 0 < vmin) (hM : 1 ≤ M)
    (hc : c ≤ K * M) :
    barrierConst vmin vmax c ≤ barrierConstBound vmin vmax K * M := by
  have hs : (0 : ℝ) < √(2 * π * vmin) := Real.sqrt_pos.2 (by positivity)
  have h0 : (0 : ℝ) ≤ barrierConst vmin vmax 0 := barrierConst_nonneg hvmin le_rfl
  have hkey : 5 * c / √(2 * π * vmin) ≤ 5 * K / √(2 * π * vmin) * M := by
    rw [show 5 * K / √(2 * π * vmin) * M = 5 * (K * M) / √(2 * π * vmin) by ring]
    gcongr
  have h3 : barrierConst vmin vmax 0 ≤ barrierConst vmin vmax 0 * M :=
    le_mul_of_one_le_right h0 hM
  rw [barrierConst_eq_affine, barrierConstBound, add_mul]
  linarith

/-- The linear-growth constant of `RMF.maxWindowConst`,
`barrierConstBound v₋ v₊ K · √2 + 2K/√(2π v₋)`. -/
noncomputable def maxWindowConstBound (vmin vmax K : ℝ) : ℝ :=
  barrierConstBound vmin vmax K * √2 + 2 * K / √(2 * π * vmin)

lemma maxWindowConstBound_nonneg {vmin vmax K : ℝ} (hvmin : 0 < vmin) (hK : 0 ≤ K) :
    0 ≤ maxWindowConstBound vmin vmax K := by
  have hb : (0 : ℝ) ≤ barrierConstBound vmin vmax K := barrierConstBound_nonneg hvmin hK
  have h1 : (0 : ℝ) ≤ barrierConstBound vmin vmax K * √2 := mul_nonneg hb (Real.sqrt_nonneg 2)
  have h2 : (0 : ℝ) ≤ 2 * K / √(2 * π * vmin) := by positivity
  rw [maxWindowConstBound]
  linarith

/-- **Linear growth of the (A2) constant**, inherited from `RMF.barrierConst_le_mul`. -/
lemma maxWindowConst_le_mul {vmin vmax c K M : ℝ} (hvmin : 0 < vmin) (hM : 1 ≤ M)
    (hc : c ≤ K * M) :
    maxWindowConst vmin vmax c ≤ maxWindowConstBound vmin vmax K * M := by
  have hs : (0 : ℝ) < √(2 * π * vmin) := Real.sqrt_pos.2 (by positivity)
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have h1 := barrierConst_le_mul (vmax := vmax) hvmin hM hc
  have h2 : 2 * c / √(2 * π * vmin) ≤ 2 * K / √(2 * π * vmin) * M := by
    rw [show 2 * K / √(2 * π * vmin) * M = 2 * (K * M) / √(2 * π * vmin) by ring]
    gcongr
  have h3 : barrierConst vmin vmax c * √2 ≤ barrierConstBound vmin vmax K * √2 * M :=
    calc barrierConst vmin vmax c * √2 ≤ barrierConstBound vmin vmax K * M * √2 :=
          mul_le_mul_of_nonneg_right h1 hs2
      _ = barrierConstBound vmin vmax K * √2 * M := by ring
  rw [maxWindowConst, maxWindowConstBound, add_mul]
  linarith

/-- **Harper’s (A2).**  For a Gaussian walk with variances in `[v₋, v₊]`, the running maximum puts
at most `≪ c/√n` on a window of width `c`:

`P( b < max_{j ≤ n} S j ≤ b + c ) ≤ maxWindowConst v₋ v₊ c / √n`,

for every `b`, every `c ≥ 0` and every `n ≥ 1`.  The window is half-open, which is the form the
application needs and the form the first-passage decomposition produces. -/
theorem IsGaussianWalk.measure_max_mem_Ioc_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    (b : ℝ) {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    (μ ({ω | ∃ j ≤ n, b < walk G j ω} \ {ω | ∃ j ≤ n, b + c < walk G j ω})).toReal
      ≤ maxWindowConst vmin vmax c / √(n : ℝ) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  set B := {ω | ∀ j ≤ n, walk G j ω ≤ b + c} with hBdef
  have hnR : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  -- `n = 1` is trivial: the constant already exceeds `1`.
  rcases eq_or_lt_of_le hn with h1 | h2
  · have hn1 : (n : ℝ) = 1 := by rw [← h1]; norm_num
    rw [hn1, Real.sqrt_one, div_one]
    refine le_trans ?_ (one_le_maxWindowConst (vmax := vmax) hvmin hc)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  -- the main case, `n ≥ 2`
  have hn2 : 2 ≤ n := h2
  have hsub : {ω | ∃ j ≤ n, b < walk G j ω} \ {ω | ∃ j ≤ n, b + c < walk G j ω}
      ⊆ (⋃ k ∈ Finset.range (n / 2 + 1), (firstPassage G b k ∩ B))
        ∪ (⋃ k ∈ Finset.Ico (n / 2 + 1) (n + 1), (firstPassage G b k ∩ B)) := by
    rintro ω ⟨h₁, h₂⟩
    have hB : ω ∈ B := fun j hj => not_lt.1 fun hcon => h₂ ⟨j, hj, hcon⟩
    have hF : ω ∈ ⋃ k ∈ Finset.range (n + 1), firstPassage G b k := by
      rw [iUnion_firstPassage G b n]; exact h₁
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hF
    obtain ⟨k, hk, hFk⟩ := hF
    by_cases hcase : k ≤ n / 2
    · exact Or.inl (Set.mem_biUnion (Finset.mem_range.2 (by omega)) ⟨hFk, hB⟩)
    · exact Or.inr (Set.mem_biUnion (Finset.mem_Ico.2 ⟨by omega, by omega⟩) ⟨hFk, hB⟩)
  -- the far half, converted to `√n`
  have hfar : (μ (⋃ k ∈ Finset.Ico (n / 2 + 1) (n + 1), (firstPassage G b k ∩ B))).toReal
      ≤ 2 * c / √(2 * π * vmin) / √(n : ℝ) := by
    refine (h.measure_biUnion_firstPassage_far_le hvmin hlo b hc hn2).trans ?_
    have hvpos : (0 : ℝ) < √(2 * π * vmin) := Real.sqrt_pos.2 (by positivity)
    have hmpos : (0 : ℝ) < √(((n / 2 : ℕ) : ℝ)) := Real.sqrt_pos.2 (by
      have : 0 < n / 2 := by omega
      exact_mod_cast this)
    have hsplit : √(2 * π * (((n / 2 : ℕ) : ℝ) * vmin))
        = √(2 * π * vmin) * √(((n / 2 : ℕ) : ℝ)) := by
      rw [show 2 * π * (((n / 2 : ℕ) : ℝ) * vmin) = (2 * π * vmin) * ((n / 2 : ℕ) : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
    have hnm : √(n : ℝ) ≤ 2 * √(((n / 2 : ℕ) : ℝ)) := by
      rw [show (2 : ℝ) * √(((n / 2 : ℕ) : ℝ)) = √(4 * ((n / 2 : ℕ) : ℝ)) by
        rw [Real.sqrt_mul (by norm_num),
          show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      refine Real.sqrt_le_sqrt ?_
      have : n ≤ 4 * (n / 2) := by omega
      exact_mod_cast this
    have hkey : c * √(2 * π * vmin) * √(n : ℝ)
        ≤ c * √(2 * π * vmin) * (2 * √(((n / 2 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hnm (by positivity)
    rw [hsplit, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [hkey]
  -- add the two halves
  have hnear :=
    h.measure_biUnion_firstPassage_inter_barrier_le ⟨hvmin, hlo, hhi⟩ b hc (by omega : 1 ≤ n)
  calc (μ ({ω | ∃ j ≤ n, b < walk G j ω} \ {ω | ∃ j ≤ n, b + c < walk G j ω})).toReal
      ≤ (μ ((⋃ k ∈ Finset.range (n / 2 + 1), (firstPassage G b k ∩ B))
          ∪ (⋃ k ∈ Finset.Ico (n / 2 + 1) (n + 1), (firstPassage G b k ∩ B)))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ (μ (⋃ k ∈ Finset.range (n / 2 + 1), (firstPassage G b k ∩ B))).toReal
          + (μ (⋃ k ∈ Finset.Ico (n / 2 + 1) (n + 1), (firstPassage G b k ∩ B))).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) (measure_union_le _ _)
    _ ≤ barrierConst vmin vmax c * √2 / √(n : ℝ) + 2 * c / √(2 * π * vmin) / √(n : ℝ) :=
        add_le_add hnear hfar
    _ = maxWindowConst vmin vmax c / √(n : ℝ) := by rw [maxWindowConst, add_div]

end RMF
