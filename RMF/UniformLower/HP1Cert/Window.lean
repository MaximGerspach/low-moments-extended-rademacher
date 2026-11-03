/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Cert.Basic
import RMF.Weighted.MesoscopicChaos

/-!
# HP1's window event and its window integral, generic part

HP1's window event `RMF.hp1Event` at the certificate's global parameters, and what turns the
per-height bound into the window integral:

* **The event and its superset** (`RMF.hp1Event_subset`): `hp1Event ⊆ H(k,h) ∩ E″_>(k)` with the
  window barrier `RMF.hp1Tube` (the height walk in its tube `[Mean_j(h) - A - Bj - ρ,
  Mean_j(h) + a + ρ]`, `1 ≤ j ≤ r`) and `RMF.hp1After` (the real walk `≤ 0` for `2 ≤ j ≤ r`),
  the same sets for every cell of the window.
* **Measurability in the height**: the tilted means `RMF.windowMeanH` in closed form
  (`RMF.measurable_windowMeanH`), so both events are jointly measurable in `(ω, h)` and the window's
  integrand is integrable (`RMF.integrableOn_integral_indicator_normSq`).
* **The tilt identity** (`RMF.setIntegral_normSq_eq_tiltedMeasure`): `E[1_A‖F_y(s)‖²] =
  ℙ'(A)·E‖F_y(s)‖²`, and `E‖F_y(½+σ+ih)‖² = ∏_{p<y}(1 + p^{-1-2σ})` does not depend on `h`.
* **The window from its cells** (`RMF.le_setIntegral_halfWindow_of_cells`): a lower bound `c·p(i)`
  on cell `i` integrates to `c·e^{-k}∑_i p(i)(e^{-i/80} - e^{-(i+1)/80})`.
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The event -/

/-- **HP1's window event at height `h`** (blocks `m < r` at offset `k`), at `a = 3/2, A = 5/2,
B = 3`, `A' = 40, B' = 2, M₁ = 7`, `ρ = 10⁻¹⁵`: the height walk in
`[Mean_j(h) - A - Bj - ρ, Mean_j(h) + a + ρ]`, the real walk in `[-M₁ - ρ, M₁ + ρ]` at `j = 1` and
in `[-A' - B'j - ρ, 0]` for `2 ≤ j ≤ r`. -/
def hp1Event (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k r : ℕ) (σ h : ℝ) : Set Ω :=
  barrierEventPair (fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω)) r
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - 5 / 2 - 3 * j - 1 / 10 ^ 15)
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + 3 / 2 + 1 / 10 ^ 15)
    (fun j => if j = 1 then -7 - 1 / 10 ^ 15 else -40 - 2 * j - 1 / 10 ^ 15)
    (fun j => if j = 1 then 7 + 1 / 10 ^ 15 else 0)

/-- **The window barrier `H(k,h)`** at the certificate's parameters: the walk of `log|F(½+σ+ih)|`
from scale `k` stays in `[Mean_j(h) - 5/2 - 3j - ρ, Mean_j(h) + 3/2 + ρ]` for `1 ≤ j ≤ r`,
`Mean_j(h)` the sum of the tilted means `RMF.windowMeanH`, `ρ = 10⁻¹⁵`. -/
def hp1Tube (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k r : ℕ) (σ h : ℝ) : Set Ω :=
  barrierEvent (halfBlock X k σ h) r
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - 5 / 2 - 3 * j - 1 / 10 ^ 15)
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + 3 / 2 + 1 / 10 ^ 15)

/-- **The delayed `E″_>(k)`, up to the compared block count `r`**: the walk of `log|F(½+σ)|` from
scale `k` is `≤ 0` at every `2 ≤ j ≤ r` (no constraint at `j = 1`, none past `r`). -/
def hp1After (X : ℕ → Ω → ℂ) (σ : ℝ) (k r : ℕ) : Set Ω :=
  {ω | ∀ j, 2 ≤ j → j ≤ r → walk (halfBlock X k σ 0) j ω ≤ 0}

/-- **The event lies in `H(k,h) ∩ E″_>(k)`**, the same two sets for every height's cell. -/
lemma hp1Event_subset (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k r : ℕ) (σ h : ℝ) :
    hp1Event X μ y k r σ h ⊆ hp1Tube X μ y k r σ h ∩ hp1After X σ k r := by
  intro ω hω
  obtain ⟨h₁, h₂⟩ := hω
  refine ⟨h₁, fun j hj2 hjr => ?_⟩
  have := (h₂ j (by omega) hjr).2
  simp only [show j ≠ 1 by omega, if_false] at this
  exact this

lemma measurableSet_hp1Event (hX : IsRademacherPrimeValues X μ) (y k r : ℕ) (σ h : ℝ) :
    MeasurableSet (hp1Event X μ y k r σ h) :=
  measurableSet_barrierEventPair
    (fun m => (measurable_halfBlock hX _ _ _ m).prodMk (measurable_halfBlock hX _ _ _ m)) r _ _ _ _

/-- **The side conditions of `RMF.le_measure_windowEvent_of_hyps_floor` at a cell's numerals `P`**
(`n₀ = 2000`, `A' = 40`, `B' = 2`, `A_W = 6`, and `a, A, B, K₂` of the event): `v₋ > 0`,
`2v₊ < B`, `(a + A + 2B)² ≤ 2(n₀ - 2)v₋`, `t ≥ 0`, `σ_R² > 0`, `K_late ≤ L`, `K₂ + K_R + A_W ≤ A'`,
`B_W ≤ B'`. -/
def HP1CellSide (P : HP1CellNumerals) : Prop :=
  0 < P.vmin ∧ 2 * P.vmax < 3
    ∧ (3 / 2 + 5 / 2 + 2 * 3) ^ 2 ≤ 2 * (((2000 : ℕ) - 2 : ℝ) * P.vmin)
    ∧ 0 ≤ P.t ∧ 0 < P.σR2 ∧ P.Klate ≤ P.L ∧ 10 + P.KR + 6 ≤ 40 ∧ P.BW ≤ 2

/-! ### Measurability in the height -/

/-- The tilted mean of `log‖1 + zw‖` in closed form (`RMF.integral_localLogAdd_tilted_rademacherLaw`
at `a = w`), as a function of `w`. -/
noncomputable def tiltedLocalMean (w : ℂ) : ℝ :=
  (Real.log (1 + (2 * w.re + ‖w‖ ^ 2)) / 2 * (1 + 2 * w.re + ‖w‖ ^ 2)
    + Real.log (1 + (-(2 * w.re) + ‖w‖ ^ 2)) / 2 * (1 - 2 * w.re + ‖w‖ ^ 2))
    / (2 * (1 + ‖w‖ ^ 2))

lemma measurable_tiltedLocalMean : Measurable tiltedLocalMean := by
  unfold tiltedLocalMean
  have hre : Measurable fun w : ℂ => w.re := Complex.measurable_re
  have hn : Measurable fun w : ℂ => ‖w‖ := measurable_norm
  refine Measurable.div ?_ ?_
  · refine Measurable.add ?_ ?_
    · exact ((Real.measurable_log.comp (measurable_const.add
        ((measurable_const.mul hre).add (hn.pow_const 2)))).div_const 2).mul
        ((measurable_const.add (measurable_const.mul hre)).add (hn.pow_const 2))
    · exact ((Real.measurable_log.comp (measurable_const.add
        ((measurable_const.mul hre).neg.add (hn.pow_const 2)))).div_const 2).mul
        ((measurable_const.sub (measurable_const.mul hre)).add (hn.pow_const 2))
  · exact measurable_const.mul (measurable_const.add (hn.pow_const 2))

/-- **The height block's tilted mean in closed form**: for a block below the cutoff,
`Mean(h) = ∑_{p ∈ block} RMF.tiltedLocalMean (p^{-(½+σ+ih)})`. -/
lemma windowMeanH_eq (hX : IsRademacherPrimeValues X μ) {y k m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) (h : ℝ) :
    windowMeanH X μ y k σ h m
      = ∑ p ∈ primeBlockSub k m, tiltedLocalMean (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  unfold windowMeanH blockMeanAdd
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_comp_tiltedMeasure_rademacher hX y hs (hB hp) (measurable_localLogAdd _),
    integral_localLogAdd_tilted_rademacherLaw (norm_prime_cpow_neg_lt_one p.2 hs)]
  rfl

/-- **The tilted means are measurable in the height** (blocks below the cutoff). -/
lemma measurable_windowMeanH (hX : IsRademacherPrimeValues X μ) {y k m : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    Measurable fun h => windowMeanH X μ y k σ h m := by
  rw [funext (windowMeanH_eq hX hσ hB)]
  exact Finset.measurable_sum _ fun p _ =>
    measurable_tiltedLocalMean.comp (continuous_cpow_neg_shiftLine p.2.pos σ).measurable

/-- The height walk is jointly measurable in `(ω, h)`. -/
lemma measurable_walk_halfBlock_prod (hX : IsRademacherPrimeValues X μ) (θ σ : ℝ) (j : ℕ) :
    Measurable fun q : Ω × ℝ => walk (halfBlock X θ σ q.2) j q.1 := by
  have hterm : ∀ p : Nat.Primes, Measurable fun q : Ω × ℝ =>
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (X (p : ℕ) q.1) := by
    intro p
    have h1 : Measurable fun q : Ω × ℝ => X (p : ℕ) q.1 :=
      (hX.measurable (p : ℕ) p.2).comp measurable_fst
    have h2 : Measurable fun q : Ω × ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      (continuous_cpow_neg_shiftLine p.2.pos σ).measurable.comp measurable_snd
    have h3 : Measurable fun q : Ω × ℝ =>
        (1 : ℂ) + X (p : ℕ) q.1 * ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      measurable_const.add (h1.mul h2)
    simp only [localLogAdd]
    exact Real.measurable_log.comp h3.norm
  simp only [walk_apply, halfBlock]
  exact Finset.measurable_sum _ fun m _ => Finset.measurable_sum _ fun p _ => hterm p

/-- The window barrier is jointly measurable in `(ω, h)`. -/
lemma measurableSet_prod_hp1Tube (hX : IsRademacherPrimeValues X μ) {y k r : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) :
    MeasurableSet {q : Ω × ℝ | q.1 ∈ hp1Tube X μ y k r σ q.2} := by
  have hmean : ∀ j, j ≤ r → Measurable fun q : Ω × ℝ =>
      ∑ i ∈ Finset.range j, windowMeanH X μ y k σ q.2 i := by
    intro j hj
    exact Finset.measurable_sum _ fun i hi =>
      (measurable_windowMeanH hX hσ (hy i (lt_of_lt_of_le (Finset.mem_range.1 hi) hj))).comp
        measurable_snd
  have hrw : {q : Ω × ℝ | q.1 ∈ hp1Tube X μ y k r σ q.2}
      = ⋂ j ∈ Set.Icc 1 r,
          ({q : Ω × ℝ | ∑ i ∈ Finset.range j, windowMeanH X μ y k σ q.2 i - 5 / 2 - 3 * j
              - 1 / 10 ^ 15 ≤ walk (halfBlock X k σ q.2) j q.1}
            ∩ {q : Ω × ℝ | walk (halfBlock X k σ q.2) j q.1
              ≤ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ q.2 i + 3 / 2 + 1 / 10 ^ 15}) := by
    ext q
    simp only [hp1Tube, barrierEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_Icc]
    exact ⟨fun h j hj => ⟨(h j hj.1 hj.2).1, (h j hj.1 hj.2).2⟩,
      fun h j h1 h2 => ⟨(h j ⟨h1, h2⟩).1, (h j ⟨h1, h2⟩).2⟩⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j hj => ?_
  have hw := measurable_walk_halfBlock_prod hX (k : ℝ) σ j
  have hm := hmean j hj.2
  exact (measurableSet_le ((hm.sub_const _).sub_const _ |>.sub_const _) hw).inter
    (measurableSet_le hw ((hm.add_const _).add_const _))

/-- The superset `H(k,h) ∩ E″_>(k)` is jointly measurable in `(ω, h)`. -/
lemma measurableSet_prod_hp1Tube_inter_hp1After (hX : IsRademacherPrimeValues X μ) {y k r : ℕ}
    {σ : ℝ} (hσ : 0 ≤ σ) (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) :
    MeasurableSet {q : Ω × ℝ | q.1 ∈ hp1Tube X μ y k r σ q.2 ∩ hp1After X σ k r} := by
  have h2 : MeasurableSet (hp1After X σ k r) := by
    have hrw : hp1After X σ k r = ⋂ j ∈ Set.Icc 2 r, {ω | walk (halfBlock X k σ 0) j ω ≤ 0} := by
      ext ω
      simp only [hp1After, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
      exact ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (measurable_walk_of (measurable_halfBlock hX _ _ _) j) measurable_const
  exact (measurableSet_prod_hp1Tube hX hσ hy).inter (measurable_fst h2)

/-- **The window's integrand is integrable in the height**: for any family of events jointly
measurable in `(ω, h)`, `h ↦ E[1_{S h}‖F_y(½+σ+ih)‖²]` is integrable on the window. -/
lemma integrableOn_integral_indicator_normSq (hX : IsRademacherPrimeValues X μ) (y k : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) (S : ℝ → Set Ω) (hS : MeasurableSet {q : Ω × ℝ | q.1 ∈ S q.2}) :
    IntegrableOn (fun h => ∫ ω, (S h).indicator (fun ω =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖ ^ 2)
        ω ∂μ) (halfWindow k) := by
  haveI := hX.isProbabilityMeasure
  have hI : volume (halfWindow k) ≠ ⊤ := by
    rw [halfWindow]
    exact measure_Icc_lt_top.ne
  have h := (integrable_uncurry_indicator_normSq_primesIco hX 0 y hσ hI S hS).integral_prod_right
  simp only [Function.uncurry_apply_pair, randomEulerProductIco_zero] at h
  exact h

/-! ### The tilt identity -/

/-- **The tilt identity**: `E[1_A‖F_y(s)‖²] = ℙ'(A)·E‖F_y(s)‖²` for the tilted measure `ℙ'` of
`RMF.tiltedMeasure`, `Re s > 0`. -/
lemma setIntegral_normSq_eq_tiltedMeasure (hX : IsRademacherPrimeValues X μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2 ∂μ
      = (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ A).toReal
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2 ∂μ := by
  have hf := hX.isRademacherRMF
  have hpos := hf.integral_norm_randomEulerProduct_sq_pos y s
  rw [hf.tiltedMeasure_apply y hs hA, ENNReal.toReal_ofReal (div_nonneg
    (setIntegral_nonneg hA fun ω _ => by positivity) hpos.le), div_mul_cancel₀ _ hpos.ne']

/-- **The weight's mean does not depend on the height**:
`E‖F_y(½+σ+ih)‖² = ∏_{p<y}(1 + p^{-1-2σ})`. -/
lemma integral_normSq_randomEulerProduct_shiftLine (hX : IsRademacherPrimeValues X μ) (y : ℕ)
    (σ h : ℝ) :
    ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖ ^ 2
        ∂μ = ∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-1 - 2 * σ)) := by
  rw [hX.isRademacherRMF.integral_norm_randomEulerProduct_sq' y, re_shiftLine]
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 2
  ring

/-! ### The window from its cells -/

/-- **The window integral from lower bounds on the cells**: if `g ≥ 0` is integrable on
`halfWindow k` and `g ≥ c·p(i)` on cell `i` (`RMF.hp1Cell`), `i < 80`, then
`∫_{halfWindow k} g ≥ c·e^{-k}∑_{i<80} p(i)(e^{-i/80} - e^{-(i+1)/80})`, Lebesgue measure in `h`. -/
theorem le_setIntegral_halfWindow_of_cells {g : ℝ → ℝ} {k : ℕ} (hg : IntegrableOn g (halfWindow k))
    {c : ℝ} {p : ℕ → ℝ} (hc : ∀ i < 80, ∀ h ∈ hp1Cell k i, c * p i ≤ g h) :
    c * Real.exp (-(k : ℝ)) * ∑ i ∈ Finset.range 80, p i * hp1WindowWeight i
      ≤ ∫ h in halfWindow k, g h := by
  set a : ℕ → ℝ := fun i => Real.exp (-((k : ℝ) + (i : ℝ) / 80)) with ha
  have hanti : ∀ i, a (i + 1) ≤ a i := fun i => by
    simp only [ha]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have hsub : ∀ i < 80, Set.uIcc (a (i + 1)) (a i) ⊆ halfWindow k := by
    intro i hi
    rw [Set.uIcc_of_le (hanti i)]
    have hi' : ((i : ℝ) + 1) ≤ 80 := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [ha, halfWindow]
    refine Set.Icc_subset_Icc (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 ?_)
    · push_cast
      have : ((i : ℝ) + 1) / 80 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hi'
      linarith
    · have : (0 : ℝ) ≤ (i : ℝ) / 80 := by positivity
      linarith
  have hII : ∀ i < 80, IntervalIntegrable g volume (a (i + 1)) (a i) := fun i hi =>
    (hg.mono_set (hsub i hi)).intervalIntegrable
  -- the window as an interval integral, split at the cells
  have hwin : ∫ h in halfWindow k, g h = ∑ i ∈ Finset.range 80, ∫ h in a (i + 1)..a i, g h := by
    have h80 : a 80 = Real.exp (-((k : ℝ) + 1)) := by
      simp only [ha]
      norm_num
    have h0 : a 0 = Real.exp (-(k : ℝ)) := by
      simp only [ha]
      norm_num
    have hle : a 80 ≤ a 0 := by
      rw [h80, h0]
      exact Real.exp_le_exp.2 (by linarith)
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g) (a := a)
      (n := 80) fun i hi => (hII i hi).symm
    rw [halfWindow, ← h80, ← h0, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_symm, ← hsum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => (intervalIntegral.integral_symm _ _).symm
  -- each cell
  have hcell : ∀ i < 80, c * p i * (Real.exp (-(k : ℝ)) * hp1WindowWeight i)
      ≤ ∫ h in a (i + 1)..a i, g h := by
    intro i hi
    have hlen : a i - a (i + 1) = Real.exp (-(k : ℝ)) * hp1WindowWeight i := by
      simp only [ha, hp1WindowWeight]
      push_cast
      rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring
    have hmono := intervalIntegral.integral_mono_on (f := fun _ => c * p i) (hanti i)
      intervalIntegrable_const (hII i hi) (fun h hh => hc i hi h (by
        simp only [hp1Cell, ha] at hh ⊢
        push_cast at hh ⊢
        exact hh))
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono
    exact (le_of_eq (by ring)).trans hmono
  rw [hwin, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have := hcell i (Finset.mem_range.1 hi)
  calc c * Real.exp (-(k : ℝ)) * (p i * hp1WindowWeight i)
      = c * p i * (Real.exp (-(k : ℝ)) * hp1WindowWeight i) := by ring
    _ ≤ _ := this

end RMF
