/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.GaussianWalk

/-!
# The barrier estimate for a Gaussian walk

Harper's (A1), upper half: for a Gaussian walk whose increment variances lie in a fixed
interval — **not** assumed identically distributed —

`P(S j ≤ c for all j ≤ n) ≪ c / √n`   (`RMF.IsGaussianWalk.barrierProb_le`),

conditional on a uniform bound `D₀` for the expected overshoot at the first passage of the
barrier.

## The route

Running the reflection idea of Lévy's inequality backwards gives a recursion in `n`.  At the
first passage `k` the walk sits above the barrier by the overshoot `Δ`, and the endpoint falls
back below the barrier exactly when the remaining block `R` satisfies `R ≤ -Δ`.  Splitting
`{R ≤ 0}` into `{R ≤ -Δ}` and the window `{-Δ < R ≤ 0}` and bounding the latter by
`RMF.measure_Ioc_neg_le` — independence turns the joint law into a product, and Fubini reduces
it to a one-dimensional window estimate — gives, after summing over the passages,

`q n ≤ q ⌊n/2⌋ / 2 + κ / √n`,  `κ ≍ c + D₀`  (`RMF.IsGaussianWalk.barrierProb_recursion`),

which iterates to the barrier estimate (`RMF.iterate_halving`).

Nothing here assumes identical distribution.  The barrier `c` enters `κ` linearly, so no
reduction to `c ≍ 1` is needed, and the statement is about `max_{j ≤ n} S j` directly.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-! ### The conditioning step

The recursion needs, at each first-passage time `k`, that the remaining block `R` undershoots
the overshoot `Δ` — an event coupling a variable measurable at time `k` with an independent
Gaussian.  Independence turns the joint law into a product, and Fubini reduces the estimate to
the one-dimensional window bound.
-/

/-- If `R` is independent of `Z` and puts mass at most `K` times
the length on every interval, then `R` lands in the random window `(-Z, 0]` — whose length is
`Z⁺` — with probability at most `K · E[Z⁺]`.

Only the anti-concentration hypothesis on `R` is used, not that it is Gaussian. -/
theorem measure_Ioc_neg_le {Z R : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hZ : Measurable Z)
    (hR : Measurable R) (hind : IndepFun Z R μ)
    (hanti : ∀ a b : ℝ, μ.map R (Set.Ioc a (a + b)) ≤ ENNReal.ofReal (K * b)) :
    μ {ω | R ω ∈ Set.Ioc (-Z ω) 0}
      ≤ ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (max (Z ω) 0) ∂μ := by
  have hSmeas : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc (-p.1) 0} := by
    have hrw : {p : ℝ × ℝ | p.2 ∈ Set.Ioc (-p.1) 0}
        = {p : ℝ × ℝ | -p.1 < p.2} ∩ {p : ℝ × ℝ | p.2 ≤ 0} := by
      ext p
      simp [Set.mem_Ioc]
    rw [hrw]
    exact (measurableSet_lt measurable_fst.neg measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hslice : ∀ z : ℝ, Prod.mk z ⁻¹' {p : ℝ × ℝ | p.2 ∈ Set.Ioc (-p.1) 0}
      = Set.Ioc (-z) 0 := fun z => rfl
  calc μ {ω | R ω ∈ Set.Ioc (-Z ω) 0}
      = ((μ.map Z).prod (μ.map R)) {p : ℝ × ℝ | p.2 ∈ Set.Ioc (-p.1) 0} := by
        rw [← hind.map_prod_eq_prod_map_map hZ.aemeasurable hR.aemeasurable,
          Measure.map_apply (hZ.prodMk hR) hSmeas]
        rfl
    _ = ∫⁻ z, (μ.map R) (Set.Ioc (-z) 0) ∂(μ.map Z) := by
        rw [Measure.prod_apply hSmeas]
        exact lintegral_congr fun z => by rw [hslice z]
    _ ≤ ∫⁻ z, ENNReal.ofReal (K * max z 0) ∂(μ.map Z) := by
        refine lintegral_mono fun z => ?_
        refine le_trans (measure_mono ?_) (hanti (-z) (max z 0))
        rcases le_total 0 z with hz | hz
        · rw [max_eq_left hz, neg_add_cancel]
        · rw [Set.Ioc_eq_empty (by simpa using hz)]
          exact Set.empty_subset _
    _ = ENNReal.ofReal K * ∫⁻ z, ENNReal.ofReal (max z 0) ∂(μ.map Z) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun z => ENNReal.ofReal_mul hK
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (max (Z ω) 0) ∂μ := by
        rw [lintegral_map (by fun_prop) hZ]

/-- The variable fed to the conditioning step: the overshoot on the first-passage event and
zero off it, so that the event is exactly `{Z > 0}`. -/
noncomputable def passageZ (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (firstPassage G c k).indicator (fun ω => walk G k ω - c) ω

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma firstPassage_eq_preimage (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) :
    firstPassage G c k = passageZ G c k ⁻¹' Set.Ioi 0 := by
  ext ω
  constructor
  · intro hk
    simp only [Set.mem_preimage, Set.mem_Ioi, passageZ, Set.indicator_of_mem hk]
    linarith [hk.2]
  · intro hz
    by_contra hk
    simp only [Set.mem_preimage, Set.mem_Ioi, passageZ, Set.indicator_of_notMem hk] at hz
    exact lt_irrefl 0 hz

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma passageZ_nonneg (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ passageZ G c k ω := by
  by_cases hk : ω ∈ firstPassage G c k
  · simp only [passageZ, Set.indicator_of_mem hk]
    linarith [hk.2]
  · simp [passageZ, Set.indicator_of_notMem hk]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma max_passageZ_eq (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (ω : Ω) :
    max (passageZ G c k ω) 0 = passageZ G c k ω :=
  max_eq_left (passageZ_nonneg G c k ω)

/-- The overshoot at the first passage above `c`, and `0` if the walk never exceeds `c` by
time `m`.  The summands have disjoint supports, so at most one is non-zero. -/
noncomputable def overshoot (G : ℕ → Ω → ℝ) (c : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), passageZ G c k ω

/-! ### The per-passage estimate -/

/-- The first-passage variable, read off the prefix of partial sums. -/
private noncomputable def passageφ (c : ℝ) (k : ℕ) (f : ℕ → ℝ) : ℝ :=
  {g : ℕ → ℝ | (∀ j < k, g j ≤ c) ∧ c < g k}.indicator (fun g => g k - c) f

private lemma measurableSet_passageSet (c : ℝ) (k : ℕ) :
    MeasurableSet {g : ℕ → ℝ | (∀ j < k, g j ≤ c) ∧ c < g k} := by
  have hrw : {g : ℕ → ℝ | (∀ j < k, g j ≤ c) ∧ c < g k}
      = (⋂ j ∈ Set.Iio k, {g : ℕ → ℝ | g j ≤ c}) ∩ {g : ℕ → ℝ | c < g k} := by
    ext g
    simp
  rw [hrw]
  exact (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (measurable_pi_apply j) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_pi_apply k))

private lemma measurable_passageφ (c : ℝ) (k : ℕ) : Measurable (passageφ c k) :=
  Measurable.indicator (by fun_prop) (measurableSet_passageSet c k)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
private lemma passageφ_comp (G : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (ω : Ω) :
    passageφ c k (prefixSums k fun i => G i ω) = passageZ G c k ω := by
  have hmem : (prefixSums k (fun i => G i ω) ∈
      {g : ℕ → ℝ | (∀ j < k, g j ≤ c) ∧ c < g k}) ↔ ω ∈ firstPassage G c k := by
    simp only [Set.mem_setOf_eq, firstPassage]
    rw [prefixSums_comp G le_rfl ω]
    exact and_congr_left fun _ =>
      forall_congr' fun j => forall_congr' fun hj => by rw [prefixSums_comp G hj.le ω]
  by_cases hk : ω ∈ firstPassage G c k
  · rw [passageφ, Set.indicator_of_mem (hmem.mpr hk), passageZ, Set.indicator_of_mem hk,
      prefixSums_comp G le_rfl ω]
  · rw [passageφ, Set.indicator_of_notMem (fun hcon => hk (hmem.mp hcon)), passageZ,
      Set.indicator_of_notMem hk]

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurable_passageZ (h : IsGaussianWalk G v μ) (c : ℝ) (k : ℕ) :
    Measurable (passageZ G c k) :=
  Measurable.indicator ((h.measurable_walk k).sub measurable_const)
    (h.measurableSet_firstPassage c k)

omit [IsProbabilityMeasure μ] in
/-- The first-passage variable is independent of the block of increments after it. -/
lemma IsGaussianWalk.indepFun_passageZ (h : IsGaussianWalk G v μ) (c : ℝ) {n k : ℕ}
    (hkn : k ≤ n) : IndepFun (passageZ G c k) (fun ω => walk G n ω - walk G k ω) μ := by
  have hcomp := (h.indepFun_prefixSums_blockSums k n).comp (measurable_passageφ c k)
    (measurable_pi_apply n)
  simp only [Function.comp_def] at hcomp
  have h1 : (fun ω => passageφ c k (prefixSums k fun i => G i ω)) = passageZ G c k :=
    funext (passageφ_comp G c k)
  have h2 : (fun ω => (blockSums k n fun i => G i ω) n)
      = fun ω => walk G n ω - walk G k ω :=
    funext fun ω => blockSums_comp G hkn le_rfl ω
  rwa [h1, h2] at hcomp

/-- **The per-passage estimate.**  At a first passage the walk sits above the barrier by the
overshoot; the remaining block is non-positive with probability at least a half, independently
of the passage, and the loss caused by the overshoot is what the conditioning step bounds. -/
theorem IsGaussianWalk.half_measure_firstPassage_le (h : IsGaussianWalk G v μ) (c : ℝ)
    {n k : ℕ} (hkn : k ≤ n) (hV : (∑ i ∈ Finset.Ico k n, v i) ≠ 0) :
    μ (firstPassage G c k) * (1 / 2)
      ≤ μ (firstPassage G c k ∩ {ω | walk G n ω ≤ c})
        + ENNReal.ofReal ((√(2 * π * ((∑ i ∈ Finset.Ico k n, v i : ℝ≥0) : ℝ)))⁻¹)
          * ∫⁻ ω, ENNReal.ofReal (max (passageZ G c k ω) 0) ∂μ := by
  have hRmeas : Measurable fun ω => walk G n ω - walk G k ω :=
    (h.measurable_walk n).sub (h.measurable_walk k)
  have hZmeas := h.measurable_passageZ c k
  have hind := h.indepFun_passageZ c hkn
  have hRlaw : μ.map (fun ω => walk G n ω - walk G k ω)
      = gaussianReal 0 (∑ i ∈ Finset.Ico k n, v i) := h.map_walk_sub hkn
  have hsplit : firstPassage G c k ∩ {ω | walk G n ω - walk G k ω ≤ 0}
      = (firstPassage G c k ∩ {ω | walk G n ω ≤ c})
        ∪ (firstPassage G c k ∩
            {ω | walk G n ω - walk G k ω ∈ Set.Ioc (-passageZ G c k ω) 0}) := by
    ext ω
    by_cases hk : ω ∈ firstPassage G c k
    · have hZ : passageZ G c k ω = walk G k ω - c := by
        simp only [passageZ, Set.indicator_of_mem hk]
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_Ioc, hZ, hk,
        true_and]
      constructor
      · intro hle
        rcases lt_or_ge c (walk G n ω) with hc | hc
        · exact Or.inr ⟨by linarith, hle⟩
        · exact Or.inl hc
      · rintro (hc | ⟨-, h2⟩)
        · linarith [hk.2]
        · exact h2
    · simp [hk]
  have hdisj : Disjoint (firstPassage G c k ∩ {ω | walk G n ω ≤ c})
      (firstPassage G c k ∩
        {ω | walk G n ω - walk G k ω ∈ Set.Ioc (-passageZ G c k ω) 0}) := by
    refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
    have hZ : passageZ G c k ω = walk G k ω - c := by
      simp only [passageZ, Set.indicator_of_mem h1.1]
    have hlow := h2.2.1
    have hup := h1.2
    rw [hZ] at hlow
    simp only [Set.mem_setOf_eq] at hup
    linarith
  have hmeas2 : MeasurableSet (firstPassage G c k ∩
      {ω | walk G n ω - walk G k ω ∈ Set.Ioc (-passageZ G c k ω) 0}) := by
    refine (h.measurableSet_firstPassage c k).inter ?_
    exact (measurableSet_lt hZmeas.neg hRmeas).inter (measurableSet_le hRmeas measurable_const)
  have hprod : μ (firstPassage G c k ∩ {ω | walk G n ω - walk G k ω ≤ 0})
      = μ (firstPassage G c k) * μ {ω | walk G n ω - walk G k ω ≤ 0} := by
    rw [firstPassage_eq_preimage]
    exact hind.measure_inter_preimage_eq_mul _ _ measurableSet_Ioi measurableSet_Iic
  have hhalf : (1 : ℝ≥0∞) / 2 ≤ μ {ω | walk G n ω - walk G k ω ≤ 0} := by
    rw [show {ω | walk G n ω - walk G k ω ≤ 0}
        = (fun ω => walk G n ω - walk G k ω) ⁻¹' Set.Iic 0 from rfl,
      ← Measure.map_apply hRmeas measurableSet_Iic, hRlaw]
    exact half_le_gaussianReal_Iic _
  calc μ (firstPassage G c k) * (1 / 2)
      ≤ μ (firstPassage G c k) * μ {ω | walk G n ω - walk G k ω ≤ 0} := by gcongr
    _ = μ (firstPassage G c k ∩ {ω | walk G n ω - walk G k ω ≤ 0}) := hprod.symm
    _ = μ (firstPassage G c k ∩ {ω | walk G n ω ≤ c})
          + μ (firstPassage G c k ∩
              {ω | walk G n ω - walk G k ω ∈ Set.Ioc (-passageZ G c k ω) 0}) := by
        rw [hsplit, measure_union hdisj hmeas2]
    _ ≤ μ (firstPassage G c k ∩ {ω | walk G n ω ≤ c})
          + μ {ω | walk G n ω - walk G k ω ∈ Set.Ioc (-passageZ G c k ω) 0} := by
        gcongr
        exact Set.inter_subset_right
    _ ≤ _ := by
        gcongr
        refine measure_Ioc_neg_le (by positivity) hZmeas hRmeas hind fun a b => ?_
        rw [hRlaw]
        exact measure_Ioc_gaussianReal_le hV a b

/-! ### Summing over the passages -/

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma overshoot_eq_sum_max (G : ℕ → Ω → ℝ) (c : ℝ) (m : ℕ) (ω : Ω) :
    overshoot G c m ω = ∑ k ∈ Finset.range (m + 1), max (passageZ G c k ω) 0 :=
  Finset.sum_congr rfl fun k _ => (max_passageZ_eq G c k ω).symm

/-- **The summed estimate.**  Adding the per-passage bounds over all first passages up to time
`m`, with `2m ≤ n` so that every remaining block has variance at least `n vmin / 2`. -/
theorem IsGaussianWalk.half_measure_exists_le (h : IsGaussianWalk G v μ) (c : ℝ) {vmin : ℝ}
    (hvmin : 0 < vmin) (hv : ∀ i, vmin ≤ (v i : ℝ)) {n m : ℕ} (hmn : 2 * m ≤ n) (hn : 0 < n) :
    μ {ω | ∃ j ≤ m, c < walk G j ω} * (1 / 2)
      ≤ μ ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c})
        + ENNReal.ofReal ((√(π * n * vmin))⁻¹)
          * ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ := by
  have hmn' : m ≤ n := by omega
  -- every remaining block carries variance at least `n vmin / 2`
  have hVlow : ∀ k ≤ m,
      π * n * vmin ≤ 2 * π * ((∑ i ∈ Finset.Ico k n, v i : ℝ≥0) : ℝ) := by
    intro k hk
    have hcard : (n : ℝ) ≤ 2 * ((Finset.Ico k n).card : ℝ) := by
      rw [Nat.card_Ico]
      have : k ≤ n := hk.trans hmn'
      push_cast [Nat.cast_sub this]
      have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
      have h2 : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    have hsum : ((Finset.Ico k n).card : ℝ) * vmin
        ≤ ((∑ i ∈ Finset.Ico k n, v i : ℝ≥0) : ℝ) := by
      push_cast
      calc ((Finset.Ico k n).card : ℝ) * vmin = ∑ _i ∈ Finset.Ico k n, vmin := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.Ico k n, (v i : ℝ) := Finset.sum_le_sum fun i _ => hv i
    have hpi := Real.pi_pos
    calc π * n * vmin ≤ π * (2 * ((Finset.Ico k n).card : ℝ)) * vmin :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hpi.le) hvmin.le
      _ = 2 * π * (((Finset.Ico k n).card : ℝ) * vmin) := by ring
      _ ≤ 2 * π * ((∑ i ∈ Finset.Ico k n, v i : ℝ≥0) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  have hVne : ∀ k ≤ m, (∑ i ∈ Finset.Ico k n, v i) ≠ 0 := by
    intro k hk hcon
    have hlow := hVlow k hk
    rw [hcon] at hlow
    simp only [NNReal.coe_zero, mul_zero] at hlow
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have : (0 : ℝ) < π * n * vmin := by positivity
    linarith
  have hmeasS : MeasurableSet {ω | walk G n ω ≤ c} :=
    measurableSet_le (h.measurable_walk n) measurable_const
  have hdisj := pairwiseDisjoint_firstPassage G c (Finset.range (m + 1) : Finset ℕ)
  calc μ {ω | ∃ j ≤ m, c < walk G j ω} * (1 / 2)
      = (∑ k ∈ Finset.range (m + 1), μ (firstPassage G c k)) * (1 / 2) := by
        rw [← iUnion_firstPassage G c m,
          measure_biUnion_finset hdisj fun k _ => h.measurableSet_firstPassage c k]
    _ = ∑ k ∈ Finset.range (m + 1), μ (firstPassage G c k) * (1 / 2) := Finset.sum_mul _ _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), (μ (firstPassage G c k ∩ {ω | walk G n ω ≤ c})
          + ENNReal.ofReal ((√(π * n * vmin))⁻¹)
            * ∫⁻ ω, ENNReal.ofReal (max (passageZ G c k ω) 0) ∂μ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine (h.half_measure_firstPassage_le c (hkm.trans hmn') (hVne k hkm)).trans ?_
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        have h1 : (0 : ℝ) < √(π * n * vmin) := by
          have hp : (0 : ℝ) < π * n * vmin := by positivity
          positivity
        have hsq : √(π * n * vmin)
            ≤ √(2 * π * ((∑ i ∈ Finset.Ico k n, v i : ℝ≥0) : ℝ)) :=
          Real.sqrt_le_sqrt (hVlow k hkm)
        have hfac : ENNReal.ofReal ((√(2 * π * ((∑ i ∈ Finset.Ico k n, v i : ℝ≥0) : ℝ)))⁻¹)
            ≤ ENNReal.ofReal ((√(π * n * vmin))⁻¹) :=
          ENNReal.ofReal_le_ofReal ((inv_le_inv₀ (lt_of_lt_of_le h1 hsq) h1).mpr hsq)
        exact add_le_add le_rfl (mul_le_mul' hfac le_rfl)
    _ = (∑ k ∈ Finset.range (m + 1), μ (firstPassage G c k ∩ {ω | walk G n ω ≤ c}))
          + ENNReal.ofReal ((√(π * n * vmin))⁻¹)
            * ∑ k ∈ Finset.range (m + 1),
              ∫⁻ ω, ENNReal.ofReal (max (passageZ G c k ω) 0) ∂μ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
        congr 1
        · rw [← iUnion_firstPassage G c m, Set.iUnion₂_inter,
            measure_biUnion_finset (hdisj.mono fun k => Set.inter_subset_left)
              fun k _ => (h.measurableSet_firstPassage c k).inter hmeasS]
        · congr 1
          rw [← lintegral_finsetSum _ fun k _ =>
            ((h.measurable_passageZ c k).max measurable_const).ennreal_ofReal]
          refine lintegral_congr fun ω => ?_
          rw [overshoot_eq_sum_max, ENNReal.ofReal_sum_of_nonneg fun k _ => le_max_right _ _]

/-! ### The recursion -/

/-- The probability that the walk stays below the barrier `c` up to time `n`. -/
noncomputable def barrierProb (μ : Measure Ω) (G : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  (μ {ω | ∀ j ≤ n, walk G j ω ≤ c}).toReal

omit [IsProbabilityMeasure μ] in
lemma IsGaussianWalk.measurableSet_forall_le (h : IsGaussianWalk G v μ) (c : ℝ) (n : ℕ) :
    MeasurableSet {ω | ∀ j ≤ n, walk G j ω ≤ c} := by
  have hrw : {ω | ∀ j ≤ n, walk G j ω ≤ c} = ⋂ j ∈ Set.Iic n, {ω | walk G j ω ≤ c} := by
    ext ω
    simp
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    measurableSet_le (h.measurable_walk j) measurable_const

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma compl_forall_le (G : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) :
    {ω | ∀ j ≤ n, walk G j ω ≤ c}ᶜ = {ω | ∃ j ≤ n, c < walk G j ω} := by
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, exists_prop]

lemma measure_exists_gt_toReal (h : IsGaussianWalk G v μ) (c : ℝ) (n : ℕ) :
    (μ {ω | ∃ j ≤ n, c < walk G j ω}).toReal = 1 - barrierProb μ G c n := by
  rw [← compl_forall_le G c n, prob_compl_eq_one_sub (h.measurableSet_forall_le c n),
    ENNReal.toReal_sub_of_le prob_le_one (by finiteness), ENNReal.toReal_one, barrierProb]

/-- Half the mass of the endpoint lies above `c`, up to the window `(-1, c]`. -/
lemma IsGaussianWalk.half_le_measure_gt (h : IsGaussianWalk G v μ) (c : ℝ) {n : ℕ}
    (hVn : (∑ i ∈ Finset.range n, v i) ≠ 0) :
    (1 : ℝ≥0∞) / 2 ≤ μ {ω | c < walk G n ω}
      + ENNReal.ofReal ((√(2 * π * ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ)))⁻¹ * (c + 1)) := by
  have hsub : Set.Ici (0 : ℝ) ⊆ Set.Ioi c ∪ Set.Ioc (-1) ((-1) + (c + 1)) := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    rcases lt_or_ge c x with hcx | hcx
    · exact Or.inl hcx
    · refine Or.inr ⟨by linarith, by linarith⟩
  have hgt : μ {ω | c < walk G n ω}
      = gaussianReal 0 (∑ i ∈ Finset.range n, v i) (Set.Ioi c) := by
    rw [← h.map_walk n, Measure.map_apply (h.measurable_walk n) measurableSet_Ioi]
    rfl
  calc (1 : ℝ≥0∞) / 2
      ≤ gaussianReal 0 (∑ i ∈ Finset.range n, v i) (Set.Ici 0) := half_le_gaussianReal_Ici _
    _ ≤ gaussianReal 0 (∑ i ∈ Finset.range n, v i) (Set.Ioi c)
        + gaussianReal 0 (∑ i ∈ Finset.range n, v i) (Set.Ioc (-1) ((-1) + (c + 1))) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ _ := by
        rw [hgt]
        exact add_le_add le_rfl (measure_Ioc_gaussianReal_le hVn _ _)

/-- **The recursion.**  Staying below the barrier for `n` steps costs a factor `1/2` against
staying below it for `m ≤ n/2` steps, plus an error `≪ (c + D₀)/√n`. -/
theorem IsGaussianWalk.barrierProb_recursion (h : IsGaussianWalk G v μ) {c : ℝ} (hc : 0 ≤ c)
    {vmin : ℝ} (hvmin : 0 < vmin) (hv : ∀ i, vmin ≤ (v i : ℝ)) {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hD : ∀ m, ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ ≤ ENNReal.ofReal D₀)
    {n m : ℕ} (hmn : 2 * m ≤ n) (hn : 0 < n) :
    barrierProb μ G c n ≤ barrierProb μ G c m / 2
      + (c + 1) / √(2 * π * (n * vmin)) + D₀ / √(π * n * vmin) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hVn : (n : ℝ) * vmin ≤ ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ) := by
    push_cast
    calc (n : ℝ) * vmin = ∑ _i ∈ Finset.range n, vmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range n, (v i : ℝ) := Finset.sum_le_sum fun i _ => hv i
  have hVne : (∑ i ∈ Finset.range n, v i) ≠ 0 := by
    intro hcon
    rw [hcon] at hVn
    simp only [NNReal.coe_zero] at hVn
    nlinarith
  -- the two disjoint ways of exceeding the barrier by time `n`
  have hsubU : {ω | c < walk G n ω}
      ∪ ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c})
      ⊆ {ω | ∃ j ≤ n, c < walk G j ω} := by
    rintro ω (hω | ⟨⟨j, hjm, hj⟩, -⟩)
    · exact ⟨n, le_rfl, hω⟩
    · exact ⟨j, hjm.trans (by omega), hj⟩
  have hdisjU : Disjoint {ω | c < walk G n ω}
      ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c}) := by
    refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
    have hA : c < walk G n ω := h1
    have hB : walk G n ω ≤ c := h2.2
    linarith
  have hmeas2 : MeasurableSet ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c}) := by
    rw [← compl_forall_le G c m]
    exact (h.measurableSet_forall_le c m).compl.inter
      (measurableSet_le (h.measurable_walk n) measurable_const)
  have hU : μ {ω | c < walk G n ω}
      + μ ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c})
      ≤ μ {ω | ∃ j ≤ n, c < walk G j ω} := by
    rw [← measure_union hdisjU hmeas2]
    exact measure_mono hsubU
  -- the master inequality, in `ℝ≥0∞`
  have hmain : (1 : ℝ≥0∞) / 2 + μ {ω | ∃ j ≤ m, c < walk G j ω} * (1 / 2)
      ≤ μ {ω | ∃ j ≤ n, c < walk G j ω}
        + ENNReal.ofReal ((√(2 * π * ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ)))⁻¹ * (c + 1))
        + ENNReal.ofReal ((√(π * n * vmin))⁻¹ * D₀) := by
    have h1 := h.half_le_measure_gt c hVne
    have h2 := h.half_measure_exists_le c hvmin hv hmn hn
    have h3 : ENNReal.ofReal ((√(π * n * vmin))⁻¹)
        * ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ
        ≤ ENNReal.ofReal ((√(π * n * vmin))⁻¹ * D₀) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' le_rfl (hD m)
    calc (1 : ℝ≥0∞) / 2 + μ {ω | ∃ j ≤ m, c < walk G j ω} * (1 / 2)
        ≤ (μ {ω | c < walk G n ω}
            + ENNReal.ofReal ((√(2 * π * ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ)))⁻¹ * (c + 1)))
          + (μ ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c})
            + ENNReal.ofReal ((√(π * n * vmin))⁻¹ * D₀)) := add_le_add h1 (h2.trans (by gcongr))
      _ = (μ {ω | c < walk G n ω}
            + μ ({ω | ∃ j ≤ m, c < walk G j ω} ∩ {ω | walk G n ω ≤ c}))
          + ENNReal.ofReal ((√(2 * π * ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ)))⁻¹ * (c + 1))
          + ENNReal.ofReal ((√(π * n * vmin))⁻¹ * D₀) := by ring
      _ ≤ _ := by gcongr
  -- pass to real numbers
  have hfin : ∀ s : Set Ω, μ s ≠ ⊤ := fun s => measure_ne_top μ s
  have htoReal := ENNReal.toReal_mono (by finiteness) hmain
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    measure_exists_gt_toReal h c n, measure_exists_gt_toReal h c m] at htoReal
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at htoReal
  -- and simplify the two error terms
  have hsqrt1 : (c + 1) / √(2 * π * ((n : ℝ) * vmin))
      ≥ (√(2 * π * ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ)))⁻¹ * (c + 1) := by
    rw [ge_iff_le, div_eq_inv_mul]
    have hb : (0 : ℝ) < √(2 * π * ((n : ℝ) * vmin)) := by
      have : (0 : ℝ) < 2 * π * ((n : ℝ) * vmin) := by positivity
      positivity
    have hle : √(2 * π * ((n : ℝ) * vmin))
        ≤ √(2 * π * ((∑ i ∈ Finset.range n, v i : ℝ≥0) : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (lt_of_lt_of_le hb hle) hb).mpr hle)
      (by linarith)
  have hsqrt2 : (√(π * n * vmin))⁻¹ * D₀ = D₀ / √(π * n * vmin) := by
    rw [div_eq_inv_mul]
  linarith [htoReal, hsqrt1]

/-! ### Iterating the recursion -/

/-- Iterating a halving recursion.  This is pure real analysis. -/
lemma iterate_halving {q : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hq1 : ∀ n, q n ≤ 1)
    (hrec : ∀ n, 4 ≤ n → q n ≤ q (n / 2) / 2 + κ / √n) :
    ∀ n, 1 ≤ n → q n ≤ (√3 + 5 * κ) / √n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : (0 : ℝ) < √n := Real.sqrt_pos.mpr hnpos
    have hC : √3 ≤ √3 + 5 * κ := by linarith
    by_cases hn4 : 4 ≤ n
    · -- inductive step
      have hhalf : 1 ≤ n / 2 := by omega
      have hlt : n / 2 < n := by omega
      have hIH := ih (n / 2) hlt hhalf
      have hh : (0 : ℝ) < √((n / 2 : ℕ) : ℝ) := by
        have : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hhalf
        exact Real.sqrt_pos.mpr this
      -- `2n ≤ 5⌊n/2⌋` for `n ≥ 4`, with equality at `n = 5`: the sharp halving ratio
      have hten : 4 * (n : ℝ) ≤ 10 * ((n / 2 : ℕ) : ℝ) := by
        have h45 : 4 * n ≤ 10 * (n / 2) := by omega
        exact_mod_cast h45
      have hCpos : (0 : ℝ) ≤ √3 + 5 * κ := by positivity
      have hkey : 2 * √n ≤ √10 * √((n / 2 : ℕ) : ℝ) := by
        have h1 : √(4 * (n : ℝ)) ≤ √(10 * ((n / 2 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hten
        rwa [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
          show √(4 : ℝ) = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      have hstep : (√3 + 5 * κ) / √((n / 2 : ℕ) : ℝ) / 2
          ≤ (√10 / 4) * ((√3 + 5 * κ) / √n) := by
        have hrw : (√10 / 4) * ((√3 + 5 * κ) / √n) = (√10 * (√3 + 5 * κ)) / (4 * √n) := by
          field_simp
        rw [div_div, hrw, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hkey hCpos]
      have hfin : (√10 / 4) * ((√3 + 5 * κ) / √n) + κ / √n ≤ (√3 + 5 * κ) / √n := by
        rw [← sub_nonneg]
        have hs10 : √10 * √10 = 10 := Real.mul_self_sqrt (by norm_num)
        have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
        have hid : (√3 + 5 * κ) / √n - ((√10 / 4) * ((√3 + 5 * κ) / √n) + κ / √n)
            = ((1 - √10 / 4) * (√3 + 5 * κ) - κ) / √n := by
          field_simp
          ring
        rw [hid]
        refine div_nonneg ?_ hsq.le
        have h10 : √10 ≤ 3.1623 := by nlinarith [hs10, Real.sqrt_nonneg 10]
        have h31 : (1.73 : ℝ) ≤ √3 := by nlinarith [hs3, Real.sqrt_nonneg 3]
        nlinarith [h10, h31, hκ, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - √10 / 4) hκ]
      calc q n ≤ q (n / 2) / 2 + κ / √n := hrec n hn4
        _ ≤ (√3 + 5 * κ) / √((n / 2 : ℕ) : ℝ) / 2 + κ / √n := by gcongr
        _ ≤ (√10 / 4) * ((√3 + 5 * κ) / √n) + κ / √n := by gcongr
        _ ≤ (√3 + 5 * κ) / √n := hfin
    · -- base cases `n ≤ 3`
      have hn3 : (n : ℝ) ≤ 3 := by
        have : n ≤ 3 := by omega
        exact_mod_cast this
      have : √n ≤ √3 := Real.sqrt_le_sqrt hn3
      calc q n ≤ 1 := hq1 n
        _ = √n / √n := (div_self hsq.ne').symm
        _ ≤ (√3 + 5 * κ) / √n := by
            gcongr
            exact this.trans hC

/-- **The barrier estimate for a Gaussian walk with comparable variances**, conditional on a
uniform bound `D₀` for the expected overshoot at the first passage:
`P(S_j ≤ c ∀ j ≤ n) ≤ (√3 + 5((c+1)/√(2π v₋) + D₀/√(π v₋)))/√n`.  `D₀` is supplied by Lawler–Limic,
Lemma 5.1.9, transferred to this setting (`RMF/Probability/Overshoot.lean`); cf. step (97) of
Lemma 19 in Arguin–Bourgade–Radziwiłł, *The Fyodorov–Hiary–Keating conjecture II*, Appendix B. -/
theorem IsGaussianWalk.barrierProb_le (h : IsGaussianWalk G v μ) {c : ℝ} (hc : 0 ≤ c)
    {vmin : ℝ} (hvmin : 0 < vmin) (hv : ∀ i, vmin ≤ (v i : ℝ)) {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hD : ∀ m, ∫⁻ ω, ENNReal.ofReal (overshoot G c m ω) ∂μ ≤ ENNReal.ofReal D₀) {n : ℕ}
    (hn : 1 ≤ n) :
    barrierProb μ G c n
      ≤ (√3 + 5 * ((c + 1) / √(2 * π * vmin) + D₀ / √(π * vmin))) / √n := by
  set κ := (c + 1) / √(2 * π * vmin) + D₀ / √(π * vmin) with hκdef
  have hκ : 0 ≤ κ := by positivity
  have hq1 : ∀ j, barrierProb μ G c j ≤ 1 := fun j => by
    rw [barrierProb, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by finiteness) prob_le_one
  have hrec : ∀ j, 4 ≤ j → barrierProb μ G c j ≤ barrierProb μ G c (j / 2) / 2 + κ / √j := by
    intro j hj
    have hjpos : 0 < j := by omega
    refine (h.barrierProb_recursion hc hvmin hv hD₀ hD (m := j / 2) (by omega) hjpos).trans ?_
    have e1 : √(2 * π * ((j : ℝ) * vmin)) = √(2 * π * vmin) * √j := by
      rw [show 2 * π * ((j : ℝ) * vmin) = (2 * π * vmin) * j by ring,
        Real.sqrt_mul (by positivity)]
    have e2 : √(π * (j : ℝ) * vmin) = √(π * vmin) * √j := by
      rw [show π * (j : ℝ) * vmin = (π * vmin) * j by ring, Real.sqrt_mul (by positivity)]
    have hs1 : √(2 * π * vmin) ≠ 0 := by positivity
    have hs2 : √(π * vmin) ≠ 0 := by positivity
    have hs3 : √((j : ℝ)) ≠ 0 := by
      have hjr : (0 : ℝ) < j := by exact_mod_cast hjpos
      positivity
    have heq : ((c + 1) / √(2 * π * vmin) + D₀ / √(π * vmin)) / √((j : ℝ))
        = (c + 1) / (√(2 * π * vmin) * √((j : ℝ)))
          + D₀ / (√(π * vmin) * √((j : ℝ))) := by
      field_simp
    rw [e1, e2, hκdef, heq]
    linarith
  exact iterate_halving hκ hq1 hrec n hn

end RMF
