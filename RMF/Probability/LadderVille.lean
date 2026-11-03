/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.FreeStartAveraged

/-!
# The ladder bound by Ville

For an independent family `Y₀, Y₁, …` of real random variables, `t ≥ 0` with `E e^{-tY_i} < ∞`,
and the walk `T_j = Y₀ + … + Y_{j-1}`:

* **the ladder bound with an exit level** (`RMF.measureReal_ladderEvent_inter_ladderExit_le`):
  `P(T_1, …, T_m > 0 and z + T_j ≤ 0 for some m < j ≤ n)
    ≤ E[1{T_1, …, T_m > 0} min(1, F e^{-t(z + T_m)})]`, `F = ∏_{m ≤ i < n} max(1, E e^{-tY_i})`;
* **the ladder with the first `m` steps kept exact** (`RMF.le_measureReal_ladderEvent`):
  `E[1{T_1, …, T_m > 0}(1 - F_m e^{-tT_m})] ≤ P(T_1, …, T_K > 0)`,
  `F_m = ∏_{m ≤ i < K} max(1, E e^{-tY_i})`.

Both come from one potential (`RMF.ladderPotential`): on the start `{T_1, …, T_m > 0}` it is `1`
once `z + T_i ≤ 0` for some `m < i ≤ j`, and `min(1, G_j e^{-t(z + T_j)})` before,
`G_j = ∏_{j ≤ i < n} max(1, E e^{-tY_i})`.  It does not increase in expectation
(`RMF.integral_ladderPotential_succ_le`): the next step is independent of the past, and
`E min(1, cX) ≤ min(1, c EX)`.  The `max` keeps a step with `E e^{-tY_i} < 1` from being spent on
the steps before it.  Starting the potential at step `m` is the conditioning on the first `m`
steps.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

section LadderVille

variable {Ω : Type*}

/-- **The ladder event**: the walk `T_i = Y₀ + … + Y_{i-1}` is positive at every step
`1 ≤ i ≤ n`. -/
def ladderEvent (Y : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ i, 1 ≤ i → i ≤ n → 0 < walk Y i ω}

/-- **The exit event**: `z + T_i ≤ 0` at some step `m < i ≤ j`. -/
def ladderExit (Y : ℕ → Ω → ℝ) (z : ℝ) (m j : ℕ) : Set Ω :=
  {ω | ∃ i, m < i ∧ i ≤ j ∧ z + walk Y i ω ≤ 0}

lemma mem_ladderEvent {Y : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} :
    ω ∈ ladderEvent Y n ↔ ∀ i, 1 ≤ i → i ≤ n → 0 < walk Y i ω := Iff.rfl

lemma mem_ladderExit {Y : ℕ → Ω → ℝ} {z : ℝ} {m j : ℕ} {ω : Ω} :
    ω ∈ ladderExit Y z m j ↔ ∃ i, m < i ∧ i ≤ j ∧ z + walk Y i ω ≤ 0 := Iff.rfl

/-- On the ladder event the walk at its last step is nonnegative. -/
lemma walk_nonneg_of_mem_ladderEvent {Y : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (hω : ω ∈ ladderEvent Y n) : 0 ≤ walk Y n ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (hω n hn le_rfl).le

/-- **The ladder potential**: on the start `{T_1, …, T_m > 0}`, `1` once `z + T_i ≤ 0` for some
`m < i ≤ j`, else `min(1, G e^{-t(z + T_j)})`; `0` off the start. -/
noncomputable def ladderPotential (Y : ℕ → Ω → ℝ) (m j : ℕ) (z t G : ℝ) (ω : Ω) : ℝ :=
  (ladderEvent Y m ∩ ladderExit Y z m j).indicator (fun _ => (1 : ℝ)) ω
    + (ladderEvent Y m \ ladderExit Y z m j).indicator
        (fun ω => min 1 (G * Real.exp (-(t * (z + walk Y j ω))))) ω

variable [MeasurableSpace Ω] {P : Measure Ω} {Y : ℕ → Ω → ℝ}

lemma measurableSet_ladderEvent (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    MeasurableSet (ladderEvent Y n) := by
  have hrw : ladderEvent Y n = ⋂ i ∈ Set.Icc 1 n, {ω | 0 < walk Y i ω} := by
    ext ω
    simp only [mem_ladderEvent, Set.mem_iInter, Set.mem_Icc, Set.mem_setOf_eq]
    exact ⟨fun h i hi => h i hi.1 hi.2, fun h i h1 h2 => h i ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
    measurableSet_lt measurable_const (measurable_walk_of hY i)

lemma measurableSet_ladderExit (hY : ∀ i, Measurable (Y i)) (z : ℝ) (m j : ℕ) :
    MeasurableSet (ladderExit Y z m j) := by
  have hrw : ladderExit Y z m j = ⋃ i ∈ Set.Ioc m j, {ω | z + walk Y i ω ≤ 0} := by
    ext ω
    simp only [mem_ladderExit, Set.mem_iUnion, Set.mem_Ioc, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun ⟨i, h1, h2, h3⟩ => ⟨i, ⟨h1, h2⟩, h3⟩, fun ⟨i, ⟨h1, h2⟩, h3⟩ => ⟨i, h1, h2, h3⟩⟩
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _) fun i _ =>
    measurableSet_le (measurable_const.add (measurable_walk_of hY i)) measurable_const

/-- **The prefix is independent of the next step**, for any independent family: the generic form
of `RMF.IsGaussianWalk.indepFun_prefixSums_step`. -/
lemma indepFun_prefixSums_step_of_iIndepFun (hind : iIndepFun Y P) (hY : ∀ i, Measurable (Y i))
    (n : ℕ) : IndepFun (fun ω => prefixSums n fun i => Y i ω) (Y n) P := by
  have hcomp := (indepFun_prefixSums_blockSums_of_iIndepFun hind hY n (n + 1)).comp
    (measurable_id (α := ℕ → ℝ)) (measurable_pi_apply (n + 1))
  have h1 : (id ∘ fun ω => prefixSums n fun i => Y i ω) = fun ω => prefixSums n fun i => Y i ω :=
    rfl
  have h2 : ((fun y : ℕ → ℝ => y (n + 1)) ∘ fun ω => blockSums n (n + 1) fun i => Y i ω)
      = Y n := by
    funext ω
    simp only [Function.comp_apply]
    rw [blockSums_comp Y (by omega) le_rfl ω, walk_succ]
    simp
  rwa [h1, h2] at hcomp

/-- **A fibrewise bound, conditionally**, for a step of any law: if `R` is independent of `X`,
`Φ` and `Ψ` are measurable and bounded by `1`, and `∫ Φ(x, ·) d(law of R) ≤ Ψ(x)` for `x ∈ S`, then
`E[1_{X ∈ S}Φ(X, R)] ≤ E[1_{X ∈ S}Ψ(X)]`.  `RMF.integral_indicator_comp_le_of_indepFun` is the
case of a Gaussian step. -/
lemma integral_indicator_comp_le_of_indepFun_map [IsProbabilityMeasure P] {α : Type*}
    [MeasurableSpace α] {X : Ω → α} {R : Ω → ℝ} {S : Set α} {Φ : α × ℝ → ℝ} {Ψ : α → ℝ}
    (hX : Measurable X) (hR : Measurable R) (hS : MeasurableSet S) (hΦ : Measurable Φ)
    (hΨ : Measurable Ψ) (hΦb : ∀ p, |Φ p| ≤ 1) (hΨb : ∀ x, |Ψ x| ≤ 1) (hind : IndepFun X R P)
    (hle : ∀ x ∈ S, ∫ r, Φ (x, r) ∂(P.map R) ≤ Ψ x) :
    ∫ ω, (X ⁻¹' S).indicator (fun ω => Φ (X ω, R ω)) ω ∂P
      ≤ ∫ ω, (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω ∂P := by
  have hprod := hind.map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable
  set F : α × ℝ → ℝ := (Prod.fst ⁻¹' S).indicator Φ with hF
  have hFm : Measurable F := hΦ.indicator (measurable_fst hS)
  have hL : (fun ω => (X ⁻¹' S).indicator (fun ω => Φ (X ω, R ω)) ω)
      = fun ω => F (X ω, R ω) := by
    funext ω
    by_cases hω : X ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ X ⁻¹' S from hω), hF,
        Set.indicator_of_mem (show (X ω, R ω) ∈ Prod.fst ⁻¹' S from hω)]
    · rw [Set.indicator_of_notMem (show ω ∉ X ⁻¹' S from hω), hF,
        Set.indicator_of_notMem (show (X ω, R ω) ∉ Prod.fst ⁻¹' S from hω)]
  set H : α → ℝ := S.indicator Ψ with hH
  have hHm : Measurable H := hΨ.indicator hS
  have hR2 : (fun ω => (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω) = fun ω => H (X ω) := by
    funext ω
    by_cases hω : X ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ X ⁻¹' S from hω), hH, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem (show ω ∉ X ⁻¹' S from hω), hH, Set.indicator_of_notMem hω]
  have hFb : ∀ p, F p ∈ Set.Icc (-1) 1 := by
    intro p
    rw [hF]
    by_cases hp : p ∈ Prod.fst ⁻¹' S
    · rw [Set.indicator_of_mem hp]
      exact abs_le.1 (hΦb p)
    · rw [Set.indicator_of_notMem hp]
      exact ⟨by norm_num, by norm_num⟩
  have hHb : ∀ x, H x ∈ Set.Icc (-1) 1 := by
    intro x
    rw [hH]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact abs_le.1 (hΨb x)
    · rw [Set.indicator_of_notMem hx]
      exact ⟨by norm_num, by norm_num⟩
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hFint : Integrable F ((P.map X).prod (P.map R)) :=
    Integrable.of_mem_Icc (-1) 1 hFm.aemeasurable (ae_of_all _ hFb)
  have hHint : Integrable H (P.map X) :=
    Integrable.of_mem_Icc (-1) 1 hHm.aemeasurable (ae_of_all _ hHb)
  rw [hL, hR2, ← integral_map (hX.prodMk hR).aemeasurable hFm.aestronglyMeasurable, hprod,
    ← integral_map hX.aemeasurable hHm.aestronglyMeasurable, integral_prod F hFint]
  refine integral_mono hFint.integral_prod_left hHint fun x => ?_
  by_cases hx : x ∈ S
  · have hF' : ∀ r, F (x, r) = Φ (x, r) := fun r => by
      rw [hF, Set.indicator_of_mem (show (x, r) ∈ Prod.fst ⁻¹' S from hx)]
    simp only [hF', hH, Set.indicator_of_mem hx]
    exact hle x hx
  · have hF' : ∀ r, F (x, r) = 0 := fun r => by
      rw [hF, Set.indicator_of_notMem (show (x, r) ∉ Prod.fst ⁻¹' S from hx)]
    simp only [hF', hH, Set.indicator_of_notMem hx, integral_zero, le_refl]

/-- `E min(1, cg) ≤ min(1, c Eg)` for `g ≥ 0` integrable and `c ≥ 0`. -/
lemma integral_min_one_mul_le [IsProbabilityMeasure P] {g : Ω → ℝ} (hgm : Measurable g)
    (hg : Integrable g P) (hg0 : ∀ ω, 0 ≤ g ω) {c : ℝ} (hc : 0 ≤ c) :
    ∫ ω, min 1 (c * g ω) ∂P ≤ min 1 (c * ∫ ω, g ω ∂P) := by
  have hmin : Integrable (fun ω => min 1 (c * g ω)) P := by
    refine Integrable.of_bound (measurable_const.min (hgm.const_mul c)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (mul_nonneg hc (hg0 ω)))]
    exact min_le_left _ _
  refine le_min ?_ ?_
  · calc ∫ ω, min 1 (c * g ω) ∂P ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono hmin (integrable_const 1) fun ω => min_le_left _ _
      _ = 1 := by simp
  · calc ∫ ω, min 1 (c * g ω) ∂P ≤ ∫ ω, c * g ω ∂P :=
          integral_mono hmin (hg.const_mul c) fun ω => min_le_right _ _
      _ = c * ∫ ω, g ω ∂P := integral_const_mul c _

/-- The ladder potential is measurable. -/
lemma measurable_ladderPotential (hY : ∀ i, Measurable (Y i)) (m j : ℕ) (z t G : ℝ) :
    Measurable (ladderPotential Y m j z t G) := by
  unfold ladderPotential
  exact (measurable_const.indicator ((measurableSet_ladderEvent hY m).inter
      (measurableSet_ladderExit hY z m j))).add
    ((measurable_const.min (measurable_const.mul ((measurable_const.mul
      (measurable_const.add (measurable_walk_of hY j))).neg.exp))).indicator
        ((measurableSet_ladderEvent hY m).diff (measurableSet_ladderExit hY z m j)))

/-- The ladder potential is integrable: it takes values in `[0, 1]` when `G ≥ 0`. -/
lemma integrable_ladderPotential [IsProbabilityMeasure P] (hY : ∀ i, Measurable (Y i))
    (m j : ℕ) (z t : ℝ) {G : ℝ} (hG : 0 ≤ G) :
    Integrable (ladderPotential Y m j z t G) P := by
  refine Integrable.of_bound (measurable_ladderPotential hY m j z t G).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => ?_)
  unfold ladderPotential
  rw [Real.norm_eq_abs]
  by_cases hE : ω ∈ ladderExit Y z m j
  · rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m \ ladderExit Y z m j from
      fun h => h.2 hE), add_zero]
    by_cases hL : ω ∈ ladderEvent Y m
    · rw [Set.indicator_of_mem (show ω ∈ ladderEvent Y m ∩ ladderExit Y z m j from ⟨hL, hE⟩),
        abs_one]
    · rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m ∩ ladderExit Y z m j from
        fun h => hL h.1), abs_zero]
      norm_num
  · rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m ∩ ladderExit Y z m j from
      fun h => hE h.2), zero_add]
    by_cases hL : ω ∈ ladderEvent Y m
    · rw [Set.indicator_of_mem (show ω ∈ ladderEvent Y m \ ladderExit Y z m j from ⟨hL, hE⟩),
        abs_of_nonneg (le_min zero_le_one (mul_nonneg hG (Real.exp_pos _).le))]
      exact min_le_left _ _
    · rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m \ ladderExit Y z m j from
        fun h => hL h.1), abs_zero]
      norm_num

/-- On the ladder event `T_m ≥ 0`, so `1 - G e^{-tT_m}` is bounded there, hence integrable. -/
lemma integrableOn_ladderEvent_one_sub_mul_exp [IsFiniteMeasure P] (hY : ∀ i, Measurable (Y i))
    {t : ℝ} (ht : 0 ≤ t) (G : ℝ) (m : ℕ) :
    IntegrableOn (fun ω => 1 - G * Real.exp (-(t * walk Y m ω))) (ladderEvent Y m) P := by
  have hm : Measurable fun ω => 1 - G * Real.exp (-(t * walk Y m ω)) :=
    measurable_const.sub (measurable_const.mul
      ((measurable_const.mul (measurable_walk_of hY m)).neg.exp))
  refine Integrable.of_bound hm.aestronglyMeasurable (1 + |G|)
    (ae_restrict_of_forall_mem (measurableSet_ladderEvent hY m) fun ω hω => ?_)
  have h0 := walk_nonneg_of_mem_ladderEvent hω
  have he1 : Real.exp (-(t * walk Y m ω)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht h0))
  have he0 : 0 < Real.exp (-(t * walk Y m ω)) := Real.exp_pos _
  rw [Real.norm_eq_abs]
  calc |1 - G * Real.exp (-(t * walk Y m ω))|
      ≤ |1| + |G * Real.exp (-(t * walk Y m ω))| := abs_sub _ _
    _ ≤ 1 + |G| := by
      rw [abs_one, abs_mul, abs_of_pos he0]
      linarith [mul_le_of_le_one_right (abs_nonneg G) he1]

/-- **The ladder potential does not increase in expectation**: for `t ≥ 0`, `G ≥ 1`, `m ≤ j` and
`e^{-tY_j}` integrable, `E Φ_{j+1}(G) ≤ E Φ_j(max(1, E e^{-tY_j})·G)`.  The step `Y_j` is
independent of the prefix (`RMF.integral_indicator_comp_le_of_indepFun_map`), and an exit at step
`j + 1` puts the potential at `1`, where `min(1, G e^{-t(z + T_{j+1})})` already is. -/
theorem integral_ladderPotential_succ_le [IsProbabilityMeasure P] (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) {t z G : ℝ} (ht : 0 ≤ t) (hG : 1 ≤ G) {m j : ℕ} (hmj : m ≤ j)
    (hint : Integrable (fun ω => Real.exp (-(t * Y j ω))) P) :
    ∫ ω, ladderPotential Y m (j + 1) z t G ω ∂P
      ≤ ∫ ω, ladderPotential Y m j z t
          (max 1 (∫ ω', Real.exp (-(t * Y j ω')) ∂P) * G) ω ∂P := by
  classical
  set E : ℝ := ∫ ω', Real.exp (-(t * Y j ω')) ∂P
  have hG0 : 0 ≤ G := by linarith
  have hEG0 : 0 ≤ max 1 E * G := mul_nonneg (le_trans zero_le_one (le_max_left 1 E)) hG0
  -- the prefix up to step `j`, and the two events read off it
  set X : Ω → ℕ → ℝ := fun ω => prefixSums j fun i => Y i ω
  have hXm : Measurable X :=
    (measurable_prefixSums j).comp (measurable_pi_lambda _ fun i => hY i)
  have hXw : ∀ ω i, i ≤ j → X ω i = walk Y i ω := fun ω i hi => prefixSums_comp Y hi ω
  set SL : Set (ℕ → ℝ) := {f | ∀ i, 1 ≤ i → i ≤ m → 0 < f i} with hSLdef
  set SE : Set (ℕ → ℝ) := {f | ∃ i, m < i ∧ i ≤ j ∧ z + f i ≤ 0} with hSEdef
  have hSLm : MeasurableSet SL := by
    have hrw : SL = ⋂ i ∈ Set.Icc 1 m, {f : ℕ → ℝ | 0 < f i} := by
      ext f
      simp only [hSLdef, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
      exact ⟨fun h i hi => h i hi.1 hi.2, fun h i h1 h2 => h i ⟨h1, h2⟩⟩
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
      measurableSet_lt measurable_const (measurable_pi_apply i)
  have hSEm : MeasurableSet SE := by
    have hrw : SE = ⋃ i ∈ Set.Ioc m j, {f : ℕ → ℝ | z + f i ≤ 0} := by
      ext f
      simp only [hSEdef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioc, exists_prop]
      exact ⟨fun ⟨i, h1, h2, h3⟩ => ⟨i, ⟨h1, h2⟩, h3⟩, fun ⟨i, ⟨h1, h2⟩, h3⟩ => ⟨i, h1, h2, h3⟩⟩
    rw [hrw]
    exact MeasurableSet.biUnion (Set.to_countable _) fun i _ =>
      measurableSet_le (measurable_const.add (measurable_pi_apply i)) measurable_const
  have hLX : ∀ ω, ω ∈ ladderEvent Y m ↔ X ω ∈ SL := by
    intro ω
    rw [mem_ladderEvent]
    refine forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hi => ?_
    rw [hXw ω i (le_trans hi hmj)]
  have hEX : ∀ ω, ω ∈ ladderExit Y z m j ↔ X ω ∈ SE := by
    intro ω
    rw [mem_ladderExit]
    refine exists_congr fun i => and_congr_right fun _ => and_congr_right fun hi => ?_
    rw [hXw ω i hi]
  -- the potential after the step, as a function of the prefix and the step
  set Φ : (ℕ → ℝ) × ℝ → ℝ := fun p => min 1 (G * Real.exp (-(t * (z + p.1 j + p.2))))
    with hΦdef
  set Ψ : (ℕ → ℝ) → ℝ := fun f => min 1 (max 1 E * G * Real.exp (-(t * (z + f j))))
    with hΨdef
  have hΦm : Measurable Φ :=
    measurable_const.min (measurable_const.mul ((measurable_const.mul ((measurable_const.add
      ((measurable_pi_apply j).comp measurable_fst)).add measurable_snd)).neg.exp))
  have hΨm : Measurable Ψ :=
    measurable_const.min (measurable_const.mul ((measurable_const.mul (measurable_const.add
      (measurable_pi_apply j))).neg.exp))
  have hΦb : ∀ p, |Φ p| ≤ 1 := fun p => by
    rw [abs_of_nonneg (le_min zero_le_one (mul_nonneg hG0 (Real.exp_pos _).le))]
    exact min_le_left _ _
  have hΨb : ∀ f, |Ψ f| ≤ 1 := fun f => by
    rw [abs_of_nonneg (le_min zero_le_one (mul_nonneg hEG0 (Real.exp_pos _).le))]
    exact min_le_left _ _
  -- one step, for a fixed prefix
  have hle : ∀ f ∈ SL \ SE, ∫ r, Φ (f, r) ∂(P.map (Y j)) ≤ Ψ f := by
    intro f _
    have hΦf : Measurable fun r : ℝ => Φ (f, r) :=
      hΦm.comp (measurable_const.prodMk measurable_id)
    rw [integral_map (hY j).aemeasurable hΦf.aestronglyMeasurable]
    set a : ℝ := Real.exp (-(t * (z + f j))) with hadef
    have ha0 : 0 ≤ a := (Real.exp_pos _).le
    have hpt : ∀ ω, Φ (f, Y j ω) = min 1 (G * a * Real.exp (-(t * Y j ω))) := by
      intro ω
      simp only [hΦdef]
      rw [mul_assoc, hadef, ← Real.exp_add]
      congr 3
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hgm : Measurable fun ω => Real.exp (-(t * Y j ω)) := ((hY j).const_mul t).neg.exp
    refine le_trans (integral_min_one_mul_le hgm hint (fun ω => (Real.exp_pos _).le)
      (mul_nonneg hG0 ha0)) (min_le_min_left 1 ?_)
    calc G * a * E ≤ G * a * max 1 E := mul_le_mul_of_nonneg_left (le_max_right 1 E)
          (mul_nonneg hG0 ha0)
      _ = max 1 E * G * a := by ring
  have hcond := integral_indicator_comp_le_of_indepFun_map hXm (hY j) (hSLm.diff hSEm) hΦm hΨm
    hΦb hΨb (indepFun_prefixSums_step_of_iIndepFun hind hY j) hle
  -- the two potentials, pointwise
  have hstep : ∀ ω, walk Y (j + 1) ω = walk Y j ω + Y j ω := fun ω => by
    rw [walk_succ]
    rfl
  have hpt1 : ∀ ω, ladderPotential Y m (j + 1) z t G ω
      = (ladderEvent Y m ∩ ladderExit Y z m j).indicator (fun _ => (1 : ℝ)) ω
        + (X ⁻¹' (SL \ SE)).indicator (fun ω => Φ (X ω, Y j ω)) ω := by
    intro ω
    have hΦω : Φ (X ω, Y j ω) = min 1 (G * Real.exp (-(t * (z + walk Y (j + 1) ω)))) := by
      simp only [hΦdef, hXw ω j le_rfl, hstep ω]
      congr 3
      ring
    unfold ladderPotential
    by_cases hL : ω ∈ ladderEvent Y m
    · by_cases hE : ω ∈ ladderExit Y z m j
      · have hE1 : ω ∈ ladderExit Y z m (j + 1) := by
          obtain ⟨i, h1, h2, h3⟩ := mem_ladderExit.1 hE
          exact mem_ladderExit.2 ⟨i, h1, by omega, h3⟩
        have hnS : ω ∉ X ⁻¹' (SL \ SE) := fun h => h.2 ((hEX ω).1 hE)
        rw [Set.indicator_of_mem (show ω ∈ ladderEvent Y m ∩ ladderExit Y z m (j + 1) from
            ⟨hL, hE1⟩),
          Set.indicator_of_notMem (show ω ∉ ladderEvent Y m \ ladderExit Y z m (j + 1) from
            fun h => h.2 hE1),
          Set.indicator_of_mem (show ω ∈ ladderEvent Y m ∩ ladderExit Y z m j from ⟨hL, hE⟩),
          Set.indicator_of_notMem hnS]
      · have hS : ω ∈ X ⁻¹' (SL \ SE) := ⟨(hLX ω).1 hL, fun h => hE ((hEX ω).2 h)⟩
        rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m ∩ ladderExit Y z m j from
            fun h => hE h.2),
          Set.indicator_of_mem hS, zero_add, hΦω]
        by_cases hj1 : z + walk Y (j + 1) ω ≤ 0
        · have hE1 : ω ∈ ladderExit Y z m (j + 1) :=
            mem_ladderExit.2 ⟨j + 1, by omega, le_rfl, hj1⟩
          rw [Set.indicator_of_mem (show ω ∈ ladderEvent Y m ∩ ladderExit Y z m (j + 1) from
              ⟨hL, hE1⟩),
            Set.indicator_of_notMem (show ω ∉ ladderEvent Y m \ ladderExit Y z m (j + 1) from
              fun h => h.2 hE1), add_zero]
          have hexp : 1 ≤ Real.exp (-(t * (z + walk Y (j + 1) ω))) :=
            Real.one_le_exp (neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos ht hj1))
          exact (min_eq_left (one_le_mul_of_one_le_of_one_le hG hexp)).symm
        · have hE1 : ω ∉ ladderExit Y z m (j + 1) := by
            intro h
            obtain ⟨i, h1, h2, h3⟩ := mem_ladderExit.1 h
            rcases Nat.lt_or_ge i (j + 1) with hi | hi
            · exact hE (mem_ladderExit.2 ⟨i, h1, by omega, h3⟩)
            · have hij : i = j + 1 := by omega
              rw [hij] at h3
              exact hj1 h3
          rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m ∩ ladderExit Y z m (j + 1) from
              fun h => hE1 h.2),
            Set.indicator_of_mem (show ω ∈ ladderEvent Y m \ ladderExit Y z m (j + 1) from
              ⟨hL, hE1⟩), zero_add]
    · have hnS : ω ∉ X ⁻¹' (SL \ SE) := fun h => hL ((hLX ω).2 h.1)
      rw [Set.indicator_of_notMem (show ω ∉ ladderEvent Y m ∩ ladderExit Y z m (j + 1) from
          fun h => hL h.1),
        Set.indicator_of_notMem (show ω ∉ ladderEvent Y m \ ladderExit Y z m (j + 1) from
          fun h => hL h.1),
        Set.indicator_of_notMem (show ω ∉ ladderEvent Y m ∩ ladderExit Y z m j from
          fun h => hL h.1),
        Set.indicator_of_notMem hnS]
  have hpt0 : ∀ ω, ladderPotential Y m j z t (max 1 E * G) ω
      = (ladderEvent Y m ∩ ladderExit Y z m j).indicator (fun _ => (1 : ℝ)) ω
        + (X ⁻¹' (SL \ SE)).indicator (fun ω => Ψ (X ω)) ω := by
    intro ω
    unfold ladderPotential
    congr 1
    by_cases hS : ω ∈ ladderEvent Y m \ ladderExit Y z m j
    · have hS' : ω ∈ X ⁻¹' (SL \ SE) := ⟨(hLX ω).1 hS.1, fun h => hS.2 ((hEX ω).2 h)⟩
      rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS']
      simp only [hΨdef, hXw ω j le_rfl]
    · have hS' : ω ∉ X ⁻¹' (SL \ SE) :=
        fun h => hS ⟨(hLX ω).2 h.1, fun h' => h.2 ((hEX ω).1 h')⟩
      rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS']
  -- integrate
  have hAm : MeasurableSet (ladderEvent Y m ∩ ladderExit Y z m j) :=
    (measurableSet_ladderEvent hY m).inter (measurableSet_ladderExit hY z m j)
  have hSX : MeasurableSet (X ⁻¹' (SL \ SE)) := hXm (hSLm.diff hSEm)
  have hi1 : Integrable
      (fun ω => (ladderEvent Y m ∩ ladderExit Y z m j).indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hiΦ : Integrable (fun ω => (X ⁻¹' (SL \ SE)).indicator (fun ω => Φ (X ω, Y j ω)) ω) P := by
    refine Integrable.of_bound ((hΦm.comp (hXm.prodMk (hY j))).indicator
      hSX).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ X ⁻¹' (SL \ SE)
    · rw [Set.indicator_of_mem hω]
      exact hΦb _
    · rw [Set.indicator_of_notMem hω, abs_zero]
      norm_num
  have hiΨ : Integrable (fun ω => (X ⁻¹' (SL \ SE)).indicator (fun ω => Ψ (X ω)) ω) P := by
    refine Integrable.of_bound ((hΨm.comp hXm).indicator hSX).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ X ⁻¹' (SL \ SE)
    · rw [Set.indicator_of_mem hω]
      exact hΨb _
    · rw [Set.indicator_of_notMem hω, abs_zero]
      norm_num
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
    integral_congr_ae (Filter.Eventually.of_forall hpt0), integral_add hi1 hiΦ,
    integral_add hi1 hiΨ]
  linarith

/-- **The ladder bound with an exit level** (Ville, per-step factors).  For `t ≥ 0`, `m ≤ n` and
`e^{-tY_i}` integrable for `m ≤ i < n`:
`P(T_1, …, T_m > 0 and z + T_j ≤ 0 for some m < j ≤ n)
  ≤ E[1{T_1, …, T_m > 0} min(1, F e^{-t(z + T_m)})]`, `F = ∏_{m ≤ i < n} max(1, E e^{-tY_i})`.
The potential `RMF.ladderPotential` from step `m` to step `n`. -/
theorem measureReal_ladderEvent_inter_ladderExit_le [IsProbabilityMeasure P]
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P) {t : ℝ} (ht : 0 ≤ t) (z : ℝ) {m n : ℕ}
    (hmn : m ≤ n) (hint : ∀ i, m ≤ i → i < n → Integrable (fun ω => Real.exp (-(t * Y i ω))) P) :
    P.real (ladderEvent Y m ∩ ladderExit Y z m n)
      ≤ ∫ ω in ladderEvent Y m, min 1 ((∏ i ∈ Finset.Ico m n,
          max 1 (∫ ω', Real.exp (-(t * Y i ω')) ∂P)) * Real.exp (-(t * (z + walk Y m ω)))) ∂P := by
  set Gf : ℕ → ℝ := fun j => ∏ i ∈ Finset.Ico j n, max 1 (∫ ω', Real.exp (-(t * Y i ω')) ∂P)
  have hG1 : ∀ j, 1 ≤ Gf j := fun j => Finset.one_le_prod fun i _ => le_max_left _ _
  have hGstep : ∀ j, j < n → Gf j = max 1 (∫ ω', Real.exp (-(t * Y j ω')) ∂P) * Gf (j + 1) :=
    fun j hj => Finset.prod_eq_prod_Ico_succ_bot hj _
  -- the potential does not increase from step `m` to step `n`
  have hchain : ∀ j, m ≤ j → j ≤ n →
      ∫ ω, ladderPotential Y m j z t (Gf j) ω ∂P ≤ ∫ ω, ladderPotential Y m m z t (Gf m) ω ∂P := by
    intro j hmj
    induction j, hmj using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ j hmj ih =>
        intro hjn
        refine le_trans ?_ (ih (by omega))
        rw [hGstep j (by omega)]
        exact integral_ladderPotential_succ_le hY hind ht (hG1 _) hmj (hint j hmj (by omega))
  -- the exit event is under the potential at step `n`
  have hend : P.real (ladderEvent Y m ∩ ladderExit Y z m n)
      ≤ ∫ ω, ladderPotential Y m n z t (Gf n) ω ∂P := by
    have hAm : MeasurableSet (ladderEvent Y m ∩ ladderExit Y z m n) :=
      (measurableSet_ladderEvent hY m).inter (measurableSet_ladderExit hY z m n)
    rw [← integral_indicator_one hAm]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hAm)
      (integrable_ladderPotential hY m n z t (le_trans zero_le_one (hG1 n))) fun ω => ?_
    unfold ladderPotential
    have h0 : 0 ≤ (ladderEvent Y m \ ladderExit Y z m n).indicator
        (fun ω => min 1 (Gf n * Real.exp (-(t * (z + walk Y n ω))))) ω :=
      Set.indicator_nonneg (fun ω _ => le_min zero_le_one
        (mul_nonneg (le_trans zero_le_one (hG1 n)) (Real.exp_pos _).le)) ω
    have h1 : (ladderEvent Y m ∩ ladderExit Y z m n).indicator (1 : Ω → ℝ) ω
        = (ladderEvent Y m ∩ ladderExit Y z m n).indicator (fun _ => (1 : ℝ)) ω := rfl
    linarith
  -- at step `m` nothing has exited yet
  have hstart : ∫ ω, ladderPotential Y m m z t (Gf m) ω ∂P
      = ∫ ω in ladderEvent Y m, min 1 (Gf m * Real.exp (-(t * (z + walk Y m ω)))) ∂P := by
    have hEx0 : ladderExit Y z m m = ∅ := by
      ext ω
      simp only [mem_ladderExit, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, h1, h2, -⟩
      omega
    rw [← integral_indicator (measurableSet_ladderEvent hY m)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [ladderPotential, hEx0, Set.inter_empty, Set.sdiff_empty, Set.indicator_empty,
      zero_add]
  calc P.real (ladderEvent Y m ∩ ladderExit Y z m n)
      ≤ ∫ ω, ladderPotential Y m n z t (Gf n) ω ∂P := hend
    _ ≤ ∫ ω, ladderPotential Y m m z t (Gf m) ω ∂P := hchain n hmn le_rfl
    _ = _ := hstart

/-- **The ladder with the first `m` steps kept exact** (Ville after them).  For an independent
family with `t ≥ 0`, `m ≤ K` and `e^{-tY_i}` integrable for `m ≤ i < K`:
`E[1{T_1, …, T_m > 0}(1 - F_m e^{-tT_m})] ≤ P(T_1, …, T_K > 0)`,
`F_m = ∏_{m ≤ i < K} max(1, E e^{-tY_i})` (`1` when `m = K`).  The rest of the walk, from
`T_m > 0`, is `RMF.measureReal_ladderEvent_inter_ladderExit_le` at `z = 0`. -/
theorem le_measureReal_ladderEvent [IsProbabilityMeasure P] (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) {t : ℝ} (ht : 0 ≤ t) {m K : ℕ} (hmK : m ≤ K)
    (hint : ∀ i, m ≤ i → i < K → Integrable (fun ω => Real.exp (-(t * Y i ω))) P) :
    ∫ ω in ladderEvent Y m, (1 - (∏ i ∈ Finset.Ico m K,
        max 1 (∫ ω', Real.exp (-(t * Y i ω')) ∂P)) * Real.exp (-(t * walk Y m ω))) ∂P
      ≤ P.real (ladderEvent Y K) := by
  set F : ℝ := ∏ i ∈ Finset.Ico m K, max 1 (∫ ω', Real.exp (-(t * Y i ω')) ∂P)
  have hF1 : 1 ≤ F := Finset.one_le_prod fun i _ => le_max_left _ _
  have hG := measureReal_ladderEvent_inter_ladderExit_le hY hind ht 0 hmK hint
  simp only [zero_add] at hG
  have hLm := measurableSet_ladderEvent hY m
  have hset : ladderEvent Y K = ladderEvent Y m \ (ladderEvent Y m ∩ ladderExit Y 0 m K) := by
    ext ω
    rw [Set.mem_sdiff, Set.mem_inter_iff, mem_ladderEvent, mem_ladderEvent, mem_ladderExit]
    constructor
    · intro h
      refine ⟨fun i h1 h2 => h i h1 (le_trans h2 hmK), fun ⟨_, i, h1, h2, h3⟩ => ?_⟩
      have := h i (by omega) h2
      linarith
    · rintro ⟨h1, h2⟩ i hi1 hiK
      by_cases him : i ≤ m
      · exact h1 i hi1 him
      · by_contra hneg
        exact h2 ⟨h1, i, by omega, hiK, by linarith⟩
  rw [hset]
  refine le_trans ?_ le_measureReal_sdiff
  have hminm : Measurable fun ω => min 1 (F * Real.exp (-(t * walk Y m ω))) :=
    measurable_const.min (measurable_const.mul
      ((measurable_const.mul (measurable_walk_of hY m)).neg.exp))
  have hmin' : Integrable (fun ω => min 1 (F * Real.exp (-(t * walk Y m ω)))) P := by
    refine Integrable.of_bound hminm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one
      (mul_nonneg (le_trans zero_le_one hF1) (Real.exp_pos _).le))]
    exact min_le_left _ _
  have hmin : IntegrableOn (fun ω => min 1 (F * Real.exp (-(t * walk Y m ω))))
      (ladderEvent Y m) P := hmin'.integrableOn
  have hone : IntegrableOn (fun _ => (1 : ℝ)) (ladderEvent Y m) P :=
    (integrable_const (1 : ℝ)).integrableOn
  calc ∫ ω in ladderEvent Y m, (1 - F * Real.exp (-(t * walk Y m ω))) ∂P
      ≤ ∫ ω in ladderEvent Y m, (1 - min 1 (F * Real.exp (-(t * walk Y m ω)))) ∂P :=
        setIntegral_mono_on (integrableOn_ladderEvent_one_sub_mul_exp hY ht F m)
          (hone.sub hmin) hLm fun ω _ => by
            linarith [min_le_right 1 (F * Real.exp (-(t * walk Y m ω)))]
    _ = P.real (ladderEvent Y m)
          - ∫ ω in ladderEvent Y m, min 1 (F * Real.exp (-(t * walk Y m ω))) ∂P := by
        rw [integral_sub hone hmin, setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ P.real (ladderEvent Y m) - P.real (ladderEvent Y m ∩ ladderExit Y 0 m K) := by
        linarith [hG]

end LadderVille

end RMF
