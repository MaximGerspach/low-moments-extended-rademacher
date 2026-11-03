/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ProbabilityResult1
import RMF.Probability.CurvedBarrierLower
import RMF.Probability.Result1Lower

/-!
# The inductive step for the downward barrier

Probability Result 1's *lower* bound runs Harper's freezing induction on `a − 10 log(min{j,L})`,
the barrier that **decreases**.  Harper calls it "very similar" and writes none of it.

Almost everything is inherited.  `RMF/Probability/ProbabilityLemma1.lean` states the split, the
middle range and the tail round trip for an *arbitrary* barrier, so this file supplies only the
envelope data.  In particular `RMF.prefixSet` and `RMF.suffixSet` are used directly — the downward
barrier needs no sets of its own.

## What is genuinely different

**The two levels exchange roles.**  Downward the level-`L` barrier lies *below* the level-`M` one,
so the one-step estimate reads `Q⁻(M) ≤ mid + (1+ρ)·Q⁻(L)`, and the middle range is run with the
level-`M` barrier.  `RMF.IsGaussianWalk.suffixSet_tail_pointwise` gives both directions from one
round trip, so nothing has to be re-proved.

**The round-trip floor is not the split threshold.**  Upward the two coincide: the tail condition
`x_N ≤ −T` gives `a + 10 log M − x_N ≥ T` for free, because `a + 10 log M ≥ 0`.  Downward the
corresponding quantity is `a − 10 log L − x_N ≥ a − 10 log L + T`, and `a ≤ 1000Λ` is an *upper*
bound on `a`, so it gives nothing: `a − 10 log L` may be very negative.

The repair is to let the round trip use its own floor `T₁ < T`.  With the split at `T = Λ⁴` and
`T₁ = Λ⁴/2` the hypothesis becomes `Λ⁴/2 ≤ a − 200Λ + Λ⁴`, which holds as soon as `Λ³ ≥ 400`; and
the ratio is still `O(Λ/T₁) = O(1/Λ³)`, so the exponent budget is unchanged.  `Λ ≥ 8` suffices, and
at every level that is what `RMF.exists_maximal_iterLog_ge` delivers once `a ≥ 8000`.

**The middle range is bounded at the split time, not at the freeze point.**  The downward barrier
is non-increasing, so its supremum over `j ≥ N` sits at `j = N` and equals `a − 10 log N`.  That is
smaller than `a`, so the (A1) constant is *smaller* than in the upward development.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-! ### The envelope data of the downward barrier -/

section Envelope

variable {a L M : ℝ} {N : ℕ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Before the split time the two levels agree, so the prefix conditions coincide. -/
lemma frozenBarrierLower_agree (hNM : (N : ℝ) ≤ M) (hML : M ≤ L) :
    ∀ j ≤ N, frozenBarrierLower a L j = frozenBarrierLower a M j := by
  intro j hj
  have hjM : (j : ℝ) ≤ M := le_trans (by exact_mod_cast hj) hNM
  rw [frozenBarrierLower_of_le (le_trans hjM hML), frozenBarrierLower_of_le hjM]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Past the split time the level-`M` barrier is constant. -/
lemma frozenBarrierLower_const (hMN : M ≤ (N : ℝ) + 1) :
    ∀ j, N < j → frozenBarrierLower a M j = a - 10 * Real.log M := by
  intro j hj
  have hjR : M ≤ (j : ℝ) := le_trans hMN (by exact_mod_cast hj)
  rw [frozenBarrierLower, min_eq_right hjR]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Past the split time the level-`L` barrier is at least `a − 10 log L`. -/
lemma frozenBarrierLower_ge (hL : 0 < L) :
    ∀ j, N < j → a - 10 * Real.log L ≤ frozenBarrierLower a L j := by
  intro j hj
  have hj1 : 1 ≤ j := by omega
  have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hpos : (0 : ℝ) < min (j : ℝ) L := lt_min (by linarith) hL
  have := Real.log_le_log hpos (min_le_right (j : ℝ) L)
  simp only [frozenBarrierLower]
  linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Past the split time the level-`L` barrier is at most the level-`M` constant: for `j > N` one
has `min{j,L} ≥ M`, since `M ≤ N+1 ≤ j` and `M ≤ L`. -/
lemma frozenBarrierLower_le_const_of_lt (hM : 0 < M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L) :
    ∀ j, N < j → frozenBarrierLower a L j ≤ a - 10 * Real.log M := by
  intro j hj
  have hjR : M ≤ (j : ℝ) := le_trans hMN (by exact_mod_cast hj)
  have hmin : M ≤ min (j : ℝ) L := le_min hjR hML
  have := Real.log_le_log hM hmin
  simp only [frozenBarrierLower]
  linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **The downward barrier attains its supremum at the split time.**  From `j ≥ N` on it is at most
`a − 10 log N`, which is what the middle range uses.  Note this is smaller than `a`, so the (A1)
constant is smaller than in the upward development. -/
lemma frozenBarrierLower_le_at_split (hN : 1 ≤ N) (hNM : (N : ℝ) ≤ M) :
    ∀ j, N ≤ j → frozenBarrierLower a M j ≤ a - 10 * Real.log N := by
  intro j hj
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmin : (N : ℝ) ≤ min (j : ℝ) M := le_min (by exact_mod_cast hj) hNM
  have := Real.log_le_log (by linarith) hmin
  simp only [frozenBarrierLower]
  linarith

end Envelope

/-! ### The tail range, integrated -/

/-- **The tail range, integrated, downward.**  Over any measurable set of prefix paths whose
endpoint is at most `−T`, the level-`M` joint probability exceeds the level-`L` one by a factor of
at most `1 + ρ`.

The round trip uses its own floor `T₁`, which is what the downward barrier needs: the split
threshold `T` alone would require `a ≥ 10 log L`. -/
theorem IsGaussianWalk.measure_prefix_inter_suffixLower_tail_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a L M T T₁ : ℝ} {N n : ℕ} (hN : 1 ≤ N)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hT₁ : 0 < T₁) (hnN : 1 ≤ n - N) (hTn : T₁ ≤ √((((n - N : ℕ)) : ℝ) * vmin))
    (hfloor : T₁ ≤ a - 10 * Real.log L + T)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) (hAsub : A ⊆ {x | x N ≤ -T}) :
    μ ({ω | (prefixSums N fun i => G i ω) ∈ A}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixSet (frozenBarrierLower a M) N n (prefixSums N fun i => G i ω)})
      ≤ ENNReal.ofReal
            (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T₁ (n - N))
        * μ ({ω | (prefixSums N fun i => G i ω) ∈ A}
            ∩ {ω | (blockSums N n fun i => G i ω)
                ∈ suffixSet (frozenBarrierLower a L) N n (prefixSums N fun i => G i ω)}) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := le_trans hN1 hNM
  have hL1 : (1 : ℝ) ≤ L := le_trans hM1 hML
  have hlogML : Real.log M ≤ Real.log L := Real.log_le_log (by linarith) hML
  have hband : a - 10 * Real.log L - (a - 10 * Real.log M)
      = -(10 * Real.log L - 10 * Real.log M) := by ring
  rw [h.measure_prefix_inter_block N n hA (measurableSet_suffixSet (frozenBarrierLower a M) N n),
    h.measure_prefix_inter_block N n hA (measurableSet_suffixSet (frozenBarrierLower a L) N n),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict hA] with x hx
  have hxT : x N ≤ -T := hAsub hx
  have hgen := h.suffixSet_tail_pointwise (β := frozenBarrierLower a L)
    (β₀ := frozenBarrierLower a M) (c := a - 10 * Real.log M)
    (clo := a - 10 * Real.log L) (chi := a - 10 * Real.log M)
    ⟨hvmin, hlo, hhi⟩ hT₁ hnN hTn (frozenBarrierLower_const hMN)
    (frozenBarrierLower_ge (by linarith)) (frozenBarrierLower_le_const_of_lt (by linarith) hMN hML)
    (by linarith) le_rfl (x := x) (by linarith)
  rw [show a - 10 * Real.log M - (a - 10 * Real.log L)
      = 10 * Real.log L - 10 * Real.log M by ring] at hgen
  exact hgen.2

/-! ### The one-step comparison, downward

The two levels exchange roles: it is the level-`M` probability that is bounded, by the middle range
plus `(1+ρ)` times the level-`L` one.  Everything else is the upward proof with the envelope data of
this file substituted. -/

/-- **The one-step comparison for the downward barrier.**  The level-`M` barrier probability is at
most the middle-range contribution plus `(1 + ρ)` times the level-`L` one.

The middle-range constant is `A(a - 10 log N + T)`, smaller than the upward `A(a + 10 log L + T)`,
because the downward barrier attains its supremum at the split time. -/
theorem IsGaussianWalk.curvedBarrierLower_step_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L M T T₁ : ℝ} {N n : ℕ} (hN : 1 ≤ N)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hT₁ : 0 < T₁) (hNn : N ≤ n) (hnN : 1 ≤ n - N)
    (hTn : T₁ ≤ √((((n - N : ℕ)) : ℝ) * vmin))
    (hfloor : T₁ ≤ a - 10 * Real.log L + T) :
    μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrierLower a M j}
      ≤ ENNReal.ofReal
            (barrierConst vmin vmax (a - 10 * Real.log N + T) / √((((n - N : ℕ)) : ℝ)))
          * μ {ω | (prefixSums N fun i => G i ω)
              ∈ prefixSet (frozenBarrierLower a M) N ∩ {x | -T < x N}}
        + ENNReal.ofReal
            (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T₁ (n - N))
          * μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrierLower a L j} := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  classical
  set Pm : Set (ℕ → ℝ) := prefixSet (frozenBarrierLower a M) N ∩ {x | -T < x N} with hPm
  set Pt : Set (ℕ → ℝ) := prefixSet (frozenBarrierLower a M) N ∩ {x | x N ≤ -T} with hPt
  have hmP : Measurable fun ω => prefixSums N fun i => G i ω :=
    (measurable_prefixSums N).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hmB : Measurable fun ω => blockSums N n fun i => G i ω :=
    (measurable_blockSums N n).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hPmm : MeasurableSet Pm :=
    (measurableSet_prefixSet _ N).inter
      (measurableSet_lt measurable_const (measurable_pi_apply N))
  have hPtm : MeasurableSet Pt :=
    (measurableSet_prefixSet _ N).inter
      (measurableSet_le (measurable_pi_apply N) measurable_const)
  have hunion : prefixSet (frozenBarrierLower a M) N = Pm ∪ Pt := by
    ext x
    simp only [hPm, hPt, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hx
      rcases lt_or_ge (-T) (x N) with hlt | hge
      · exact Or.inl ⟨hx, hlt⟩
      · exact Or.inr ⟨hx, hge⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hdisj : Disjoint ({ω | (prefixSums N fun i => G i ω) ∈ Pm}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixSet (frozenBarrierLower a M) N n (prefixSums N fun i => G i ω)})
      ({ω | (prefixSums N fun i => G i ω) ∈ Pt}
        ∩ {ω | (blockSums N n fun i => G i ω)
            ∈ suffixSet (frozenBarrierLower a M) N n (prefixSums N fun i => G i ω)}) := by
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    have hm := h1.1
    have ht := h2.1
    simp only [hPm, hPt, Set.mem_setOf_eq, Set.mem_inter_iff] at hm ht
    linarith [hm.2, ht.2]
  have hmeasT : MeasurableSet ({ω | (prefixSums N fun i => G i ω) ∈ Pt}
      ∩ {ω | (blockSums N n fun i => G i ω)
          ∈ suffixSet (frozenBarrierLower a M) N n (prefixSums N fun i => G i ω)}) :=
    (hmP hPtm).inter ((hmP.prodMk hmB) (measurableSet_suffixSet _ N n))
  have hpre : {ω | (prefixSums N fun i => G i ω) ∈ Pm ∪ Pt}
      = {ω | (prefixSums N fun i => G i ω) ∈ Pm}
        ∪ {ω | (prefixSums N fun i => G i ω) ∈ Pt} := rfl
  rw [barrier_event_eq G (frozenBarrierLower a M) hNn, hunion, hpre,
    Set.union_inter_distrib_right, measure_union hdisj hmeasT]
  gcongr
  · exact h.measure_prefixSet_inter_suffixSet_le ⟨hvmin, hlo, hhi⟩
      (frozenBarrierLower_le_at_split hN hNM) hnN hPmm (by rw [hPm])
  · refine le_trans (h.measure_prefix_inter_suffixLower_tail_le ⟨hvmin, hlo, hhi⟩ hN hNM hMN hML
      hT₁ hnN hTn hfloor hPtm (by rw [hPt]; exact Set.inter_subset_right)) ?_
    gcongr
    rw [barrier_event_eq G (frozenBarrierLower a L) hNn]
    refine Set.inter_subset_inter_left _ fun ω hω => ?_
    have hmem : (prefixSums N fun i => G i ω)
        ∈ prefixSet (frozenBarrierLower a M) N := hω.1
    rwa [← prefixSet_congr (frozenBarrierLower_agree hNM hML)] at hmem

/-! ### The two numeric inputs

Both are cheaper than upward.  The window the prefix event confines `S_N` to has width
`a − 10 log N + T` rather than `a + 10 log N + T`, and the (A1) bound on the whole curved barrier is
at the constant `a` rather than `a + 10 log L`. -/

/-- **The middle mass, downward.**  The prefix event with endpoint above `−T` sits inside a window
of width `a − 10 log N + T` for `S_N`: below by the split, above by the barrier at time `N`, which
is `a − 10 log N` since `N ≤ M`. -/
theorem IsGaussianWalk.measure_prefix_midLower_le (h : IsGaussianWalk G v μ) {a M T : ℝ}
    {N : ℕ} (hNM : (N : ℝ) ≤ M) (hV : (∑ m ∈ Finset.range N, v m) ≠ 0) :
    μ {ω | (prefixSums N fun i => G i ω)
        ∈ prefixSet (frozenBarrierLower a M) N ∩ {x | -T < x N}}
      ≤ ENNReal.ofReal ((a - 10 * Real.log N + T)
          / √(2 * π * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ))) := by
  have hsub : {ω | (prefixSums N fun i => G i ω)
        ∈ prefixSet (frozenBarrierLower a M) N ∩ {x | -T < x N}}
      ⊆ walk G N ⁻¹' Set.Icc (-T) (-T + (a - 10 * Real.log N + T)) := by
    rintro ω ⟨h1, h2⟩
    have hpe : prefixSums N (fun i => G i ω) N = walk G N ω := prefixSums_comp G (le_refl N) ω
    simp only [Set.mem_setOf_eq] at h2
    rw [hpe] at h2
    have hup := h1 N le_rfl
    rw [frozenBarrierLower, min_eq_left hNM, hpe] at hup
    exact ⟨h2.le, by linarith⟩
  refine le_trans (measure_mono hsub) ?_
  rw [← Measure.map_apply (h.measurable_walk N) measurableSet_Icc, h.map_walk N]
  exact measure_Icc_gaussianReal_le_ofReal 0 hV _ _

/-- **(A1) upper for the downward curved barrier.**  The barrier never exceeds `a`, so (A1) applies
at that constant height — with no `log L` in it, unlike the upward case. -/
theorem IsGaussianWalk.measure_frozenBarrierLower_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrierLower a L j}
      ≤ ENNReal.ofReal (barrierConst vmin vmax a / √(n : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hnR : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsub : {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrierLower a L j}
      ⊆ {ω | ∀ j ≤ n, walk G j ω ≤ a} :=
    fun ω hω j hj => (hω j hj).trans (frozenBarrierLower_le_const hL j)
  refine le_trans (measure_mono hsub) ?_
  refine ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (div_nonneg (barrierConst_nonneg hvmin ha) hnR.le) |>.2 ?_
  exact h.barrierProb_le_of_comparable_mgf ha ⟨hvmin, hlo, hhi⟩ hn

/-! ### The one-step comparison in real form

As upward, the comparison is proved in `ℝ≥0∞`, where the multiplicative phrasing keeps subtraction
out of the way, and transported to `ℝ` once. -/

/-- The downward one-step comparison, with every quantity a real number. -/
theorem IsGaussianWalk.curvedBarrierProbLower_step_le (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a L M T T₁ : ℝ} {N n : ℕ} (hN : 1 ≤ N)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hML : M ≤ L)
    (hT₁ : 0 < T₁) (hNn : N ≤ n) (hnN : 1 ≤ n - N)
    (hTn : T₁ ≤ √((((n - N : ℕ)) : ℝ) * vmin))
    (hfloor : T₁ ≤ a - 10 * Real.log L + T)
    (hmid0 : 0 ≤ a - 10 * Real.log N + T) :
    curvedBarrierProbLower μ G a M n
      ≤ barrierConst vmin vmax (a - 10 * Real.log N + T) / √((((n - N : ℕ)) : ℝ))
          * (μ {ω | (prefixSums N fun i => G i ω)
              ∈ prefixSet (frozenBarrierLower a M) N ∩ {x | -T < x N}}).toReal
        + (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T₁ (n - N))
          * curvedBarrierProbLower μ G a L n := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := le_trans hN1 hNM
  have hc0 : (0 : ℝ) ≤ 10 * Real.log L - 10 * Real.log M := by
    linarith [Real.log_le_log (by linarith : (0 : ℝ) < M) hML]
  have hA1 : (0 : ℝ)
      ≤ barrierConst vmin vmax (a - 10 * Real.log N + T) / √((((n - N : ℕ)) : ℝ)) :=
    div_nonneg (barrierConst_nonneg hvmin hmid0) (Real.sqrt_nonneg _)
  have hratio : (0 : ℝ)
      ≤ tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T₁ (n - N) :=
    tailRatio_nonneg hvmin hc0 hT₁.le _
  have hstep := h.curvedBarrierLower_step_le ⟨hvmin, hlo, hhi⟩ hN hNM hMN hML hT₁ hNn hnN hTn hfloor
  have hfin1 : ENNReal.ofReal
        (barrierConst vmin vmax (a - 10 * Real.log N + T) / √((((n - N : ℕ)) : ℝ)))
      * μ {ω | (prefixSums N fun i => G i ω)
          ∈ prefixSet (frozenBarrierLower a M) N ∩ {x | -T < x N}} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hfin2 : ENNReal.ofReal
        (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) T₁ (n - N))
      * μ {ω | ∀ j ≤ n, walk G j ω ≤ frozenBarrierLower a L j} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have := ENNReal.toReal_mono (by finiteness) hstep
  rwa [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA1, ENNReal.toReal_ofReal (by linarith)] at this

/-! ### The one-step estimate, assembled

Both contributions collapse onto `1/(Λ²√n)` by the *same* two arithmetic lemmas as upward —
`RMF.middle_term_le` and `RMF.tail_term_le` — with different, and smaller, numerals:

* `a − 10 log N + T ≤ a + Λ⁴ ≤ 1001Λ⁴`, where upward it was `(1001 + c₀)Λ⁴`, because
  `−10 log N ≤ 0`;
* the (A1) bound on the whole curved barrier is at `a ≤ 1000Λ`, where upward it was
  `a + 10 log M ≤ (1000 + c₀)Λ`.

**One hypothesis carries the whole downward development**, `2c₀ ≤ Λ³`.  It gives both positivity
conditions that were free upward: `0 ≤ a − 10 log N + T` for the middle range, and
`T₁ ≤ a − 10 log L + T` for the round-trip floor.  At Harper’s `c₀ = 200` it reads `Λ ≥ 8`, and
`Λ ≥ 8` at every level is what `RMF.exists_maximal_iterLog_ge (b := a/1000)` delivers once
`a ≥ 8000`. -/

/-- The per-level constant of the downward induction.  The `√2` inside `D` is the price of splitting
at `⌊M⌋`; the missing factor `2` in the tail term, relative to the upward `stepConst`, is the price
of the round trip running at floor `T₁ = T/2`. -/
noncomputable def stepConstLower (vmin vmax c₀ : ℝ) : ℝ :=
  √2 * (barrierConstBound vmin vmax 1001 * 1001 * (√2 / √(2 * π * vmin)))
    + maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax) / Real.exp (-(1 : ℝ) / 2)
        * barrierConstBound vmin vmax 1000

lemma stepConstLower_nonneg {vmin vmax c₀ : ℝ} (hvmin : 0 < vmin) (hc₀ : 0 ≤ c₀) :
    0 ≤ stepConstLower vmin vmax c₀ := by
  have h1 : (0 : ℝ) ≤ barrierConstBound vmin vmax 1001 :=
    barrierConstBound_nonneg hvmin (by norm_num)
  have h2 : (0 : ℝ) ≤ barrierConstBound vmin vmax 1000 :=
    barrierConstBound_nonneg hvmin (by norm_num)
  have h3 : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ := maxWindowConstBound_nonneg hvmin hc₀
  have hA : (0 : ℝ)
      ≤ √2 * (barrierConstBound vmin vmax 1001 * 1001 * (√2 / √(2 * π * vmin))) :=
    mul_nonneg (Real.sqrt_nonneg 2)
      (mul_nonneg (mul_nonneg h1 (by norm_num)) (by positivity))
  have hB : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax)
      / Real.exp (-(1 : ℝ) / 2) * barrierConstBound vmin vmax 1000 :=
    mul_nonneg (div_nonneg (mul_nonneg h3 (Real.sqrt_nonneg _)) (by positivity)) h2
  rw [stepConstLower]
  linarith

/-- **The one-step estimate of the downward induction.**  Moving the freeze point from `L` in to `M`
changes the curved-barrier probability by at most `stepConstLower/(Λ²√n)`. -/
theorem IsGaussianWalk.abs_curvedBarrierProbLower_sub_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a Λ L M c₀ : ℝ} {N n : ℕ}
    (hΛ : 1 ≤ Λ) (ha : 0 ≤ a) (haΛ : a ≤ 1000 * Λ) (hML : M ≤ L)
    (hlogL : 10 * Real.log L ≤ c₀ * Λ) (hΛM : Λ ^ 20 ≤ M)
    (hNM : (N : ℝ) ≤ M) (hMN : M ≤ (N : ℝ) + 1) (hN : 1 ≤ N) (hNn : 2 * N ≤ n)
    (hc₀Λ : 2 * c₀ ≤ Λ ^ 3)
    (hTn : Λ ^ 4 / 2 ≤ √((((n - N : ℕ)) : ℝ) * vmin)) :
    |curvedBarrierProbLower μ G a L n - curvedBarrierProbLower μ G a M n|
      ≤ stepConstLower vmin vmax c₀ / (Λ ^ 2 * √(n : ℝ)) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ4 : (1 : ℝ) ≤ Λ ^ 4 := one_le_pow₀ hΛ
  have hT : (0 : ℝ) < Λ ^ 4 := by positivity
  have hT₁ : (0 : ℝ) < Λ ^ 4 / 2 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := le_trans hN1 hNM
  have hL1 : (1 : ℝ) ≤ L := le_trans hM1 hML
  have hNn' : N ≤ n := by omega
  have hn : 1 ≤ n := by omega
  have hnN : 1 ≤ n - N := by omega
  have hmn : (n : ℝ) ≤ 2 * (((n - N : ℕ)) : ℝ) := by
    have hcast : (((n - N : ℕ)) : ℝ) = (n : ℝ) - (N : ℝ) := Nat.cast_sub hNn'
    have h2N : (2 : ℝ) * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    rw [hcast]; linarith
  -- the logarithms
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hlogM0 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  have hlogNM : Real.log N ≤ Real.log M := Real.log_le_log (by linarith) hNM
  have hlogML : Real.log M ≤ Real.log L := Real.log_le_log (by linarith) hML
  have hc₀ : (0 : ℝ) ≤ c₀ := nonneg_of_mul_nonneg_left (by linarith) hΛ0
  have hΛΛ4 : Λ ≤ Λ ^ 4 := le_self_pow₀ hΛ (by norm_num)
  -- `c₀Λ ≤ Λ⁴/2` is what `2c₀ ≤ Λ³` is for
  have hkey : c₀ * Λ ≤ Λ ^ 4 / 2 := by
    linarith [mul_le_mul_of_nonneg_right hc₀Λ hΛ0.le]
  have hmid0 : (0 : ℝ) ≤ a - 10 * Real.log N + Λ ^ 4 := by linarith
  have hfloor : Λ ^ 4 / 2 ≤ a - 10 * Real.log L + Λ ^ 4 := by linarith
  have hargY : a - 10 * Real.log N + Λ ^ 4 ≤ 1001 * Λ ^ 4 := by linarith
  have hwin : 10 * Real.log L - 10 * Real.log M ≤ c₀ * Λ := by linarith
  -- the two (A1) constants, by linear growth
  have hA1 : barrierConst vmin vmax (a - 10 * Real.log N + Λ ^ 4)
      ≤ barrierConstBound vmin vmax 1001 * Λ ^ 4 := barrierConst_le_mul hvmin hΛ4 hargY
  have hA2 : barrierConst vmin vmax a ≤ barrierConstBound vmin vmax 1000 * Λ :=
    barrierConst_le_mul hvmin hΛ (by linarith)
  have hA1nn : (0 : ℝ) ≤ barrierConst vmin vmax (a - 10 * Real.log N + Λ ^ 4) :=
    barrierConst_nonneg hvmin hmid0
  have hA2nn : (0 : ℝ) ≤ barrierConst vmin vmax a := barrierConst_nonneg hvmin ha
  -- the first block’s standard deviation
  have hΛ2N : Λ ^ 20 ≤ 2 * (N : ℝ) := by linarith
  have hVcast : ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ) = ∑ m ∈ Finset.range N, ((v m : ℝ)) :=
    NNReal.coe_sum _ _
  have hsum : (N : ℝ) * vmin ≤ ∑ m ∈ Finset.range N, ((v m : ℝ)) := by
    calc (N : ℝ) * vmin = ∑ _m ∈ Finset.range N, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.range N, ((v m : ℝ)) := Finset.sum_le_sum fun m _ => hlo m
  have hVpos : (0 : ℝ) < ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ) := by
    rw [hVcast]
    exact Finset.sum_pos (fun m _ => lt_of_lt_of_le hvmin (hlo m))
      (Finset.nonempty_range_iff.2 (by omega))
  have hVN : (∑ m ∈ Finset.range N, v m) ≠ 0 := by
    intro hc; rw [hc] at hVpos; simp at hVpos
  have hVlow : Λ ^ 20 * vmin ≤ 2 * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ) := by
    rw [hVcast]
    have h1 : Λ ^ 20 * vmin ≤ (2 * (N : ℝ)) * vmin := mul_le_mul_of_nonneg_right hΛ2N hvmin.le
    have h2 : (2 * (N : ℝ)) * vmin = 2 * ((N : ℝ) * vmin) := by ring
    linarith
  have hs : Λ ^ 10 / (√2 / √(2 * π * vmin))
      ≤ √(2 * π * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ)) := by
    have hs2 : √2 ≠ 0 := ne_of_gt (by positivity)
    have hpv : √(π * vmin) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have e1 : √((Λ ^ 10) ^ 2 * (π * vmin)) = Λ ^ 10 * √(π * vmin) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have e2 : √(2 * π * vmin) = √2 * √(π * vmin) := by
      rw [show 2 * π * vmin = 2 * (π * vmin) by ring, Real.sqrt_mul (by norm_num)]
    have hrw : Λ ^ 10 / (√2 / √(2 * π * vmin)) = √((Λ ^ 10) ^ 2 * (π * vmin)) := by
      rw [e1, e2]; field_simp
    rw [hrw]
    refine Real.sqrt_le_sqrt ?_
    have hπ := Real.pi_pos
    linarith [mul_le_mul_of_nonneg_left hVlow hπ.le]
  -- the middle mass and the level-`L` probability
  have hmidR : (μ {ω | (prefixSums N fun i => G i ω)
        ∈ prefixSet (frozenBarrierLower a M) N ∩ {x | -(Λ ^ 4) < x N}}).toReal
      ≤ (a - 10 * Real.log N + Λ ^ 4)
          / √(2 * π * ((∑ m ∈ Finset.range N, v m : ℝ≥0) : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg hmid0 (Real.sqrt_nonneg _))
      (h.measure_prefix_midLower_le hNM hVN)
  have hQL : curvedBarrierProbLower μ G a L n ≤ barrierConst vmin vmax a / √(n : ℝ) := by
    simp only [curvedBarrierProbLower]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hA2nn (Real.sqrt_nonneg _))
      (h.measure_frozenBarrierLower_le ⟨hvmin, hlo, hhi⟩ hL1 ha hn)
  -- the round-trip ratio
  have hρ0 : (0 : ℝ)
      ≤ tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4 / 2) (n - N) :=
    tailRatio_nonneg hvmin (by linarith) (by positivity) _
  have hρ : tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4 / 2) (n - N)
      ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax)
          / Real.exp (-(1 : ℝ) / 2) / Λ ^ 3 := by
    refine le_trans (tailRatio_le hvmax hT₁ hnN (maxWindowConst_le_mul hvmin hΛ hwin))
      (le_of_eq ?_)
    have hE : Real.exp (-(1 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hΛne : Λ ≠ 0 := ne_of_gt hΛ0
    field_simp
  -- the two terms, collapsed
  have h1 : curvedBarrierProbLower μ G a M n
      ≤ √2 * (barrierConstBound vmin vmax 1001 * 1001 * (√2 / √(2 * π * vmin)))
            / (Λ ^ 2 * √(n : ℝ))
        + (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4 / 2) (n - N))
            * curvedBarrierProbLower μ G a L n := by
    refine le_trans (h.curvedBarrierProbLower_step_le ⟨hvmin, hlo, hhi⟩ hN hNM hMN hML hT₁ hNn' hnN
      hTn hfloor hmid0) (add_le_add ?_ le_rfl)
    refine le_trans (mul_le_mul_of_nonneg_left hmidR (by positivity)) ?_
    exact middle_term_le hΛ (by positivity) hA1nn hmid0 hA1 hargY hs hnN hn hmn
  have h2 : tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4 / 2) (n - N)
        * curvedBarrierProbLower μ G a L n
      ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax) / Real.exp (-(1 : ℝ) / 2)
          * barrierConstBound vmin vmax 1000 / (Λ ^ 2 * √(n : ℝ)) :=
    le_trans (mul_le_mul_of_nonneg_left hQL hρ0) (tail_term_le hΛ hn hρ0 hA2nn hρ hA2)
  -- recombine; downward the free direction is `Q⁻(L) ≤ Q⁻(M)`
  have hmono : curvedBarrierProbLower μ G a L n ≤ curvedBarrierProbLower μ G a M n :=
    curvedBarrierProbLower_anti (μ := μ) (by linarith : (0 : ℝ) < M) hML n
  have hring : (1 + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4 / 2) (n - N))
        * curvedBarrierProbLower μ G a L n
      = curvedBarrierProbLower μ G a L n
        + tailRatio vmin vmax (10 * Real.log L - 10 * Real.log M) (Λ ^ 4 / 2) (n - N)
          * curvedBarrierProbLower μ G a L n := by ring
  have hsplit : stepConstLower vmin vmax c₀ / (Λ ^ 2 * √(n : ℝ))
      = √2 * (barrierConstBound vmin vmax 1001 * 1001 * (√2 / √(2 * π * vmin)))
            / (Λ ^ 2 * √(n : ℝ))
        + maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax) / Real.exp (-(1 : ℝ) / 2)
            * barrierConstBound vmin vmax 1000 / (Λ ^ 2 * √(n : ℝ)) := by
    rw [stepConstLower]; ring
  have hMb0 : (0 : ℝ)
      ≤ √2 * (barrierConstBound vmin vmax 1001 * 1001 * (√2 / √(2 * π * vmin)))
        / (Λ ^ 2 * √(n : ℝ)) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
      (mul_nonneg (mul_nonneg (barrierConstBound_nonneg hvmin (by norm_num)) (by norm_num))
        (by positivity))) (by positivity)
  have hTb0 : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ * √(2 * π * vmax)
      / Real.exp (-(1 : ℝ) / 2) * barrierConstBound vmin vmax 1000 / (Λ ^ 2 * √(n : ℝ)) := by
    have h3 : (0 : ℝ) ≤ maxWindowConstBound vmin vmax c₀ := maxWindowConstBound_nonneg hvmin hc₀
    exact div_nonneg (mul_nonneg (div_nonneg (mul_nonneg h3 (Real.sqrt_nonneg _))
      (by positivity)) (barrierConstBound_nonneg hvmin (by norm_num))) (by positivity)
  rw [abs_le, hsplit]
  exact ⟨by linarith, by linarith⟩

/-! ### Probability Lemma 1, downward

The telescope is barrier-agnostic — `RMF.abs_sub_telescope_iterLog` takes the chain of one-step
estimates and nothing else — so this is the upward assembly with the downward step substituted. -/

/-- **Probability Lemma 1 for the downward barrier.**  Along a chain of real freeze points
`L 0 ≥ ⋯ ≥ L k` with integer split times `N i` bracketing `L (i+1)`.

The one hypothesis with no upward counterpart is `hthr : 2c₀ ≤ log_{i+1}³ n`, which buys the two
positivity conditions of the downward step. -/
theorem IsGaussianWalk.abs_curvedBarrierProbLower_sub_iterLog (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a c₀ : ℝ} (ha : 0 ≤ a) (hc₀ : 0 ≤ c₀)
    {L : ℕ → ℝ} {N : ℕ → ℕ} {k n : ℕ}
    (hgood : IterLogGood k (n : ℝ)) (haΛ : a ≤ 1000 * iterLog k (n : ℝ))
    (hmono : ∀ i < k, L (i + 1) ≤ L i)
    (hlogL : ∀ i < k, 10 * Real.log (L i) ≤ c₀ * iterLog (i + 1) (n : ℝ))
    (hpow : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 20 ≤ L (i + 1))
    (hsplitL : ∀ i < k, ((N i : ℕ) : ℝ) ≤ L (i + 1))
    (hsplitU : ∀ i < k, L (i + 1) ≤ ((N i : ℕ) : ℝ) + 1)
    (hNone : ∀ i < k, 1 ≤ N i)
    (hhalf : ∀ i < k, 2 * N i ≤ n)
    (hthr : ∀ i < k, 2 * c₀ ≤ iterLog (i + 1) (n : ℝ) ^ 3)
    (hfloor : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 4 / 2 ≤ √(((n - N i : ℕ) : ℝ) * vmin)) :
    |curvedBarrierProbLower μ G a (L 0) n - curvedBarrierProbLower μ G a (L k) n|
      ≤ stepConstLower vmin vmax c₀ * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by simpa using hgood.one_le (Nat.zero_le k)
  have hR : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  refine abs_sub_telescope_iterLog (f := fun i => curvedBarrierProbLower μ G a (L i) n)
    (stepConstLower_nonneg hvmin hc₀) hR hgood ?_
  intro i hi
  have hΛ : (1 : ℝ) ≤ iterLog (i + 1) (n : ℝ) := hgood.one_le hi
  have haΛi : a ≤ 1000 * iterLog (i + 1) (n : ℝ) := by
    have := iterLog_le_iterLog hi hgood
    linarith
  have key := h.abs_curvedBarrierProbLower_sub_le ⟨hvmin, hlo, hhi⟩ hΛ ha haΛi (hmono i hi)
    (hlogL i hi) (hpow i hi) (hsplitL i hi) (hsplitU i hi) (hNone i hi) (hhalf i hi)
    (hthr i hi) (hfloor i hi)
  rwa [mul_comm (iterLog (i + 1) (n : ℝ) ^ 2) (√(n : ℝ))] at key

/-- **Probability Lemma 1, downward, with Harper’s left-hand side.** -/
theorem IsGaussianWalk.abs_measure_forall_le_sub_iterLog_lower (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a c₀ : ℝ} (ha : 0 ≤ a) (hc₀ : 0 ≤ c₀)
    {L : ℕ → ℝ} {N : ℕ → ℕ} {k n : ℕ}
    (hgood : IterLogGood k (n : ℝ)) (haΛ : a ≤ 1000 * iterLog k (n : ℝ))
    (hL0 : (n : ℝ) ≤ L 0)
    (hmono : ∀ i < k, L (i + 1) ≤ L i)
    (hlogL : ∀ i < k, 10 * Real.log (L i) ≤ c₀ * iterLog (i + 1) (n : ℝ))
    (hpow : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 20 ≤ L (i + 1))
    (hsplitL : ∀ i < k, ((N i : ℕ) : ℝ) ≤ L (i + 1))
    (hsplitU : ∀ i < k, L (i + 1) ≤ ((N i : ℕ) : ℝ) + 1)
    (hNone : ∀ i < k, 1 ≤ N i)
    (hhalf : ∀ i < k, 2 * N i ≤ n)
    (hthr : ∀ i < k, 2 * c₀ ≤ iterLog (i + 1) (n : ℝ) ^ 3)
    (hfloor : ∀ i < k, iterLog (i + 1) (n : ℝ) ^ 4 / 2 ≤ √(((n - N i : ℕ) : ℝ) * vmin)) :
    |(μ {ω | ∀ j ≤ n, walk G j ω ≤ a - 10 * Real.log j}).toReal
        - curvedBarrierProbLower μ G a (L k) n|
      ≤ stepConstLower vmin vmax c₀ * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  rw [← curvedBarrierProbLower_of_le (μ := μ) (G := G) (a := a) hL0]
  exact h.abs_curvedBarrierProbLower_sub_iterLog ⟨hvmin, hlo, hhi⟩ ha hc₀ hgood haΛ hmono hlogL
    hpow hsplitL hsplitU hNone hhalf hthr hfloor

/-- **Probability Lemma 1, downward, as Harper states it.**  At `L_i = (log_i n)²⁰` with split times
`⌊(log_{i+1} n)²⁰⌋`, and `n` large in the same sense as upward.

The extra hypothesis relative to the upward version is `hgood8 : ∀ i ≤ k, 8 ≤ log_i n`, which is
exactly what `RMF.exists_maximal_iterLog_ge (b := a/1000)` gives once `a ≥ 8000`. -/
theorem IsGaussianWalk.abs_measure_forall_le_sub_iterLog_lower_pow (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {a : ℝ} (ha : 0 ≤ a) {k n : ℕ}
    (hgood8 : ∀ i ≤ k, (8 : ℝ) ≤ iterLog i (n : ℝ))
    (haΛ : a ≤ 1000 * iterLog k (n : ℝ))
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ))
    (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin) :
    |(μ {ω | ∀ j ≤ n, walk G j ω ≤ a - 10 * Real.log j}).toReal
        - curvedBarrierProbLower μ G a (iterLog k (n : ℝ) ^ 20) n|
      ≤ stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
          / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hgood : IterLogGood k (n : ℝ) := fun i hi => le_trans (by norm_num) (hgood8 i hi)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by simpa using hgood.one_le (Nat.zero_le k)
  have hle1 : ∀ i, i < k → iterLog (i + 1) (n : ℝ) ≤ Real.log n := by
    intro i hi
    have h2 := iterLog_le_iterLog (Nat.succ_le_succ (Nat.zero_le i)) (hgood.mono hi)
    rwa [iterLog_one] at h2
  have hpos : ∀ i, i < k → (0 : ℝ) < iterLog (i + 1) (n : ℝ) := fun i hi => hgood.pos hi
  have hpow8 : ∀ i, i < k → ∀ m : ℕ, iterLog (i + 1) (n : ℝ) ^ m ≤ Real.log n ^ m :=
    fun i hi m => pow_le_pow_left₀ (hpos i hi).le (hle1 i hi) m
  have hhalfAll : ∀ i < k, 2 * ⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ ≤ n := by
    intro i hi
    have hfl : ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) ≤ iterLog (i + 1) (n : ℝ) ^ 20 :=
      Nat.floor_le (by positivity)
    have hR : (2 : ℝ) * ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      linarith [hpow8 i hi 20]
    exact_mod_cast hR
  refine h.abs_measure_forall_le_sub_iterLog_lower (L := fun i => iterLog i (n : ℝ) ^ 20)
    (N := fun i => ⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊) ⟨hvmin, hlo, hhi⟩ ha (by norm_num) hgood haΛ
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hhalfAll ?_ ?_
  · simpa using le_self_pow₀ hn1 (by norm_num)
  · intro i hi
    exact pow_le_pow_left₀ (hpos i hi).le (iterLog_le_iterLog (Nat.le_succ i) (hgood.mono hi)) 20
  · intro i hi
    rw [Real.log_pow, iterLog_succ]
    push_cast
    linarith
  · intro i _
    exact le_rfl
  · intro i _
    exact Nat.floor_le (by positivity)
  · intro i _
    exact (Nat.lt_floor_add_one _).le
  · intro i hi
    refine Nat.le_floor ?_
    push_cast
    exact one_le_pow₀ (hgood.one_le hi)
  · intro i hi
    have h8 : (8 : ℝ) ≤ iterLog (i + 1) (n : ℝ) := hgood8 (i + 1) hi
    have : (8 : ℝ) ^ 3 ≤ iterLog (i + 1) (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) h8 3
    norm_num at this ⊢
    linarith
  · intro i hi
    have h4 : (0 : ℝ) < iterLog (i + 1) (n : ℝ) ^ 4 / 2 := by
      have := pow_pos (hpos i hi) 4; linarith
    have hhi2 := hhalfAll i hi
    have hcast : ((n - ⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ)
        = (n : ℝ) - ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) :=
      Nat.cast_sub (by omega)
    have hNn : (2 : ℝ) * ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hhi2
    have hNv : ((⌊iterLog (i + 1) (n : ℝ) ^ 20⌋₊ : ℕ) : ℝ) * vmin ≤ ((n : ℝ) / 2) * vmin :=
      mul_le_mul_of_nonneg_right (by linarith) hvmin.le
    rw [Real.le_sqrt' h4, hcast]
    nlinarith [hpow8 i hi 8, hbig2, hNv, pow_pos (hpos i hi) 8]

/-! ### Probability Result 1, lower bound, the substantive regime

`a ≥ 20 log n` is handled without any induction in `RMF/Probability/ProbabilityResult1.lean`.
For `a < 20 log n` the endgame is Harper’s, run downwards: choose `k` maximal
with `log_k n ≥ a/1000`, apply the downward Probability Lemma 1 at that level, and observe that the
frozen barrier is then the *constant* `a − 200 log_{k+1} n > 4a/5`, where (A1) **lower** finishes.

Unlike the upper bound, the accumulated error is **subtracted**, so it must be beaten by the main
term.  That is what forces a genuine threshold on `a`: the error is `≪ 10⁶C/(a²√n)` and the main
term `≳ αa/√n`, so one needs `a³ ≳ C/α`.  The lazy bound `≤ C/√n` that sufficed upward is useless
here. -/

/-- **Probability Result 1, lower bound, by the downward induction**:
`α/4 · min{1, a/√n} ≤ P(S_j ≤ a + h(j) ∀ 1 ≤ j ≤ n)` for `h(j) ≥ -10 log j`.  The (A1) lower bound
is the hypothesis `hA1` (met in `RMF.IsGaussianWalk.result1_lower`), so `α` is threaded
from the caller.  `8000 ≤ a` gives `a/1000 ≥ 8` at every level, `hthr` makes the accumulated error
smaller than the main term, and `a ≤ 1000n` makes the terminal level exist. -/
theorem IsGaussianWalk.le_measure_forall_le_of_lt_log (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {α : ℝ} (hα : 0 < α)
    (hA1 : ∀ c : ℝ, 1 ≤ c → ∀ m : ℕ, 1 ≤ m → α * min 1 (c / √(m : ℝ)) ≤ barrierProb μ G c m)
    {a : ℝ} (ha : 8000 ≤ a)
    (hthr : 4 * 1000000 * (stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹)
      ≤ α * a ^ 2)
    {n : ℕ} (hn : 1 ≤ n) (hle : a ≤ 1000 * (n : ℝ))
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → -(10 * Real.log j) ≤ hf j) :
    α / 4 * min 1 (a / √(n : ℝ))
      ≤ (μ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}).toReal := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.2 hnR
  -- the event with the extreme barrier is contained in the target
  have hsub : {ω | ∀ j ≤ n, walk G j ω ≤ a - 10 * Real.log j}
      ⊆ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j} := by
    intro ω hω j hj1 hjn
    linarith [hω j hjn, hhf j hj1 hjn]
  refine le_trans ?_ (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))
  -- the terminal level
  have han : a / 1000 ≤ (n : ℝ) := by linarith
  obtain ⟨k, hPk, hk1⟩ := exists_maximal_iterLog_ge (b := a / 1000) (by linarith) han
  have hgood8 : ∀ i ≤ k, (8 : ℝ) ≤ iterLog i (n : ℝ) :=
    fun i hi => le_trans (by linarith) (hPk i hi)
  have hgood : IterLogGood k (n : ℝ) := fun i hi => le_trans (by norm_num) (hgood8 i hi)
  have haΛ : a ≤ 1000 * iterLog k (n : ℝ) := by linarith [hPk k le_rfl]
  have htk : (8 : ℝ) ≤ iterLog k (n : ℝ) := hgood8 k le_rfl
  have htk2 : (a / 1000) ^ 2 ≤ iterLog k (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (hPk k le_rfl) 2
  -- the downward Probability Lemma 1
  have hPL := (abs_le.1 (h.abs_measure_forall_le_sub_iterLog_lower_pow ⟨hvmin, hlo, hhi⟩ ha0
    hgood8 haΛ hbig hbig2)).1
  -- the terminal frozen barrier is the constant `a - 200 log_{k+1} n > 4a/5`
  have hL1 : (1 : ℝ) ≤ iterLog k (n : ℝ) ^ 20 := one_le_pow₀ (by linarith)
  have hlogL : 10 * Real.log (iterLog k (n : ℝ) ^ 20) = 200 * iterLog (k + 1) (n : ℝ) := by
    rw [Real.log_pow, iterLog_succ]; push_cast; ring
  have hQL : barrierProb μ G (4 * a / 5) n
      ≤ curvedBarrierProbLower μ G a (iterLog k (n : ℝ) ^ 20) n := by
    refine le_trans (barrierProb_mono (μ := μ) G ?_ n)
      (barrierProb_le_curvedBarrierProbLower (μ := μ) hL1 n)
    rw [hlogL]
    linarith
  -- (A1) lower at `4a/5`
  have hmain : α / 2 * min 1 (a / √(n : ℝ)) ≤ barrierProb μ G (4 * a / 5) n := by
    refine le_trans ?_ (hA1 (4 * a / 5) (by linarith) n hn)
    have h0 := mul_le_mul_of_nonneg_left
      (half_min_one_div_le (by linarith : a / 2 ≤ 4 * a / 5) hsn.le) hα.le
    calc α / 2 * min 1 (a / √(n : ℝ)) = α * (1 / 2 * min 1 (a / √(n : ℝ))) := by ring
      _ ≤ α * min 1 (4 * a / 5 / √(n : ℝ)) := h0
  -- the accumulated error is smaller than a quarter of the main term
  have hCnn : (0 : ℝ) ≤ stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ :=
    mul_nonneg (stepConstLower_nonneg hvmin (by norm_num))
      (le_of_lt (inv_pos.2 one_sub_inv_exp_sq_pos))
  have hE : stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹
        / (√(n : ℝ) * iterLog k (n : ℝ) ^ 2)
      ≤ α / 4 * min 1 (a / √(n : ℝ)) := by
    have htpos : (0 : ℝ) < iterLog k (n : ℝ) ^ 2 := by positivity
    rcases le_or_gt (a / √(n : ℝ)) 1 with hc | hc
    · rw [min_eq_right hc, div_le_iff₀ (by positivity)]
      have hrw : α / 4 * (a / √(n : ℝ)) * (√(n : ℝ) * iterLog k (n : ℝ) ^ 2)
          = α / 4 * a * iterLog k (n : ℝ) ^ 2 := by
        field_simp
      rw [hrw]
      have h1 : α / 4 * a * (a / 1000) ^ 2 ≤ α / 4 * a * iterLog k (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left htk2 (by positivity)
      have h2 : 4 * 1000000 * (stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹) * a
          ≤ α * a ^ 2 * a := mul_le_mul_of_nonneg_right hthr (by linarith)
      linarith [h1, h2, mul_nonneg hCnn (by linarith : (0 : ℝ) ≤ a - 1)]
    · rw [min_eq_left hc.le, div_le_iff₀ (by positivity)]
      have hprod : (a / 1000) ^ 2 ≤ √(n : ℝ) * iterLog k (n : ℝ) ^ 2 :=
        htk2.trans (le_mul_of_one_le_left htpos.le hsn1)
      have h1 : α / 4 * (a / 1000) ^ 2 ≤ α / 4 * (√(n : ℝ) * iterLog k (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      linarith [h1, hthr]
  linarith

/-! ### Probability Result 1, lower bound

The two regimes combine.  `a ≥ 20 log n` needs no induction at all; `a < 20 log n` is the
substantive case, and there `min{1, a/√n} = a/√n`. -/

/-- The lower constant of Probability Result 1, `barrierConstLow v₋ v₊ / 4`.  Like the upper one it
is a function of the variance bounds alone. -/
noncomputable def result1LowerConst (vmin vmax : ℝ) : ℝ := barrierConstLow vmin vmax / 4

/-- The threshold on `a`.  `8000` is what makes `a/1000 ≥ 8`, the level threshold the downward
induction needs; the second term is what makes the induction’s accumulated error — which is
*subtracted* — smaller than the main term.

**The second term binds, and by a long way.**  At the variance bracket the chain uses,
`v₋ = 1/16`, `v₊ = 9/2`, it is `1.59·10¹¹`: `stepConstLower = 3.11·10¹⁴` against
`barrierConstLow = 0.057`, and the threshold is `2000√(stepConstLower/((1-e^{-2})barrierConstLow))`.
-/
noncomputable def result1Threshold (vmin vmax : ℝ) : ℝ :=
  max 8000 (√(4 * 1000000 * (stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹)
    / barrierConstLow vmin vmax))

lemma result1LowerConst_pos {vmin vmax : ℝ} (hvmin : 0 < vmin) (hvmax : 0 < vmax) :
    0 < result1LowerConst vmin vmax := by
  rw [result1LowerConst]
  exact div_pos (barrierConstLow_pos hvmin hvmax) (by norm_num)

/-- **Probability Result 1, lower bound.**  Both regimes combined, with a named constant. -/
theorem IsGaussianWalk.result1_lower (h : IsGaussianWalk G v μ) {vmin vmax : ℝ}
    (hv : VarBracket v vmin vmax)
    {a : ℝ} (ha : result1Threshold vmin vmax ≤ a) {n : ℕ} (hn : 1 ≤ n)
    (hbig : 2 * Real.log n ^ 20 ≤ (n : ℝ)) (hbig2 : 2 * Real.log n ^ 8 ≤ (n : ℝ) * vmin)
    {hf : ℕ → ℝ} (hhf : ∀ j, 1 ≤ j → j ≤ n → -(10 * Real.log j) ≤ hf j) :
    result1LowerConst vmin vmax * min 1 (a / √(n : ℝ))
      ≤ (μ {ω | ∀ j, 1 ≤ j → j ≤ n → walk G j ω ≤ a + hf j}).toReal := by
  obtain ⟨hvmin, hlo, hhi⟩ := hv
  have hvmax : (0 : ℝ) < vmax := lt_of_lt_of_le hvmin ((hlo 0).trans (hhi 0))
  have hLpos : (0 : ℝ) < barrierConstLow vmin vmax := barrierConstLow_pos hvmin hvmax
  have ha8000 : (8000 : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hmnn : (0 : ℝ) ≤ min 1 (a / √(n : ℝ)) := le_min zero_le_one (by positivity)
  have hthr : 4 * 1000000 * (stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹)
      ≤ barrierConstLow vmin vmax * a ^ 2 := by
    have h0 : √(4 * 1000000 * (stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹)
        / barrierConstLow vmin vmax) ≤ a := le_trans (le_max_right _ _) ha
    have hy : (0 : ℝ) ≤ 4 * 1000000 * (stepConstLower vmin vmax 200
        * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹) / barrierConstLow vmin vmax := by
      have hC : (0 : ℝ) ≤ stepConstLower vmin vmax 200 * (1 - (Real.exp 1 ^ 2)⁻¹)⁻¹ :=
        mul_nonneg (stepConstLower_nonneg hvmin (by norm_num))
          (le_of_lt (inv_pos.2 one_sub_inv_exp_sq_pos))
      positivity
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h0 2
    rw [Real.sq_sqrt hy, div_le_iff₀ hLpos] at hsq
    linarith
  rcases le_or_gt (20 * Real.log n) a with hcase | hcase
  · refine le_trans ?_ (h.le_measure_forall_le_of_log_le ⟨hvmin, hlo, hhi⟩
    (by linarith) hn hcase hhf)
    rw [result1LowerConst]
    exact mul_le_mul_of_nonneg_right (by linarith) hmnn
  · have hlogn : Real.log n ≤ (n : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (n : ℝ)); linarith
    refine le_trans ?_ (h.le_measure_forall_le_of_lt_log ⟨hvmin, hlo, hhi⟩ hLpos
      (fun c hc m hm => h.barrierConstLow_le_barrierProb ⟨hvmin, hlo, hhi⟩ (by linarith) hm)
      ha8000 hthr hn (by linarith) hbig hbig2 hhf)
    rw [result1LowerConst]

/-! ### Probability Result 1

Harper (arXiv:1703.06654, §3.2): *"Let `a` and `n` be large, and let `G₁, …, G_n` be independent
Gaussian random variables, each having mean zero and variance between `1/20` and `20` (say).  Then
uniformly for any function `h(j)` satisfying `|h(j)| ≤ 10 log j`, we have*

`P(∑_{m=1}^{j} G_m ≤ a + h(j)  ∀1 ≤ j ≤ n) ≍ min{1, a/√n}`.

Three points of correspondence.  *"Uniformly"*: both constants are named functions of the variance
bounds alone, so they are uniform in the walk, in `h`, in `a` and in `n` — which is what Proposition
5 needs, since there the walk changes with `x` and `n`.  *"Large"*: `a` past an explicit threshold,
and `n` large in the sense of Probability Lemma 1.  *"Variance between 1/20 and 20"*: replaced by
arbitrary `0 < v₋ ≤ v₊`, which is more general. -/

/-- Result 1's lower threshold is above its upper one, `1000`. -/
lemma thousand_le_result1Threshold (vmin vmax : ℝ) : (1000 : ℝ) ≤ result1Threshold vmin vmax :=
  le_trans (by norm_num) (le_max_left _ _)

universe u

/-- **`RMF.Result1Lower` by the iterated-logarithm induction**, at `RMF.result1Threshold` and
`RMF.result1LowerConst` (`RMF.IsGaussianWalk.result1_lower`). -/
theorem result1Lower_iteratedLog (vmin vmax : ℝ) :
    Result1Lower.{u} vmin vmax (result1Threshold vmin vmax) (result1LowerConst vmin vmax) := by
  intro Ω _ μ _ G v h hv a ha n hn hbig hbig2 hf hhf
  exact h.result1_lower hv ha hn hbig hbig2 hhf

end RMF
