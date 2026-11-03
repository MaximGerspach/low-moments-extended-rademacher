/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.GaussianHP1
import RMF.Probability.CapDepth
import RMF.Probability.PairBallot

/-!
# The window's first moment, Gaussian side

The Gaussian setting of the first moment on the window: a Gaussian height walk `Z` (variances `v`)
on `Ω₁` and an independent Gaussian residual walk `W` (variances `s`) on `Ω₂`, with slopes `β` and
drifts `d`, give the pair family `(Z_m, d_m + β_m Z_m + W_m)` on `Ω₁ × Ω₂` — the regression form
of `RMF.gaussianPairLaw`.  The window event is two-sided: height in `[-A - Bj, a]`, real walk in
`[-M₁, M₁]` at `j = 1` (delayed) and in `[-A' - B'j, -ρ]` for `2 ≤ j ≤ n`.  Its probability is
bounded below in `RMF.le_measure_windowEvent_gaussian_v2` and
`RMF.le_measure_windowEvent_gaussian_short`, from the steps proved here:

* **The start**, blocks `0, 1` aggregated: `(U₂, V₂)` is a pair law (`RMF.map_startPair_eq`);
  `U₁ ≤ a` costs `P(Z₀ > a)E[min((-Z₁)⁺, C)]` (`RMF.integral_indicator_startWeight_le`), the other
  start constraints Gaussian tails (`RMF.startTails`).
* **The height suffix** (`RMF.IsGaussianWalk.le_measure_tube_inter_slope`,
  `RMF.ofReal_suffixLow_le`): the ballot less the relative floor loss, less the slope walk
  `∑ β_m Z_m` paid by a margin `L`: past a block `m₀` it is bounded on the tube, before `m₀` its
  excess is a prefix event charged relatively by the survival bound after `m₀`
  (`RMF.IsGaussianWalk.measureReal_prefix_inter_survive_le`).
* **The exponential maximal bound** with every step paid its factor `exp(max(0, td_m + t²v_m/2))`
  (`RMF.IsGaussianWalk.measureReal_survivalSet_compl_le_exp_sum`).
* **The losses** `RMF.hp1Loss` and the ballot slope `RMF.hp1Slope` of the resulting bound.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace RMF

/-! ### Scaled walks -/

section Scaled

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}

/-- **A Gaussian walk with scaled steps**: step `m` times `c m` is `N(0, c_m²v_m)`. -/
lemma IsGaussianWalk.const_mul (h : IsGaussianWalk G v μ) (c : ℕ → ℝ) :
    IsGaussianWalk (fun m ω => c m * G m ω) (fun m => ⟨c m ^ 2, sq_nonneg _⟩ * v m) μ where
  measurable m := (h.measurable m).const_mul (c m)
  indep := by
    have hc := h.indep.comp (fun m => fun x : ℝ => c m * x)
      (fun m => measurable_const.mul measurable_id)
    convert hc using 1
    funext m ω
    rfl
  map_eq m := by
    have hmap : μ.map (fun ω => c m * G m ω) = (μ.map (G m)).map (fun x => c m * x) := by
      rw [Measure.map_map (by fun_prop) (h.measurable m)]
      rfl
    rw [hmap, h.map_eq m, gaussianReal_map_const_mul, mul_zero]
    rfl

end Scaled

/-! ### The exponential potential with a cost per step -/

/-- **One Gaussian step of the potential, any drift**: the step costs at most the factor
`exp(max(0, td + t²V/2))`, since `min(1, cX) ≤ c·min(1, X)` for `c ≥ 1`. -/
lemma integral_expPotential_gaussian_le_mul {t z x d : ℝ} {V : ℝ≥0} :
    ∫ r, expPotential t z (x + r + d) ∂(gaussianReal 0 V)
      ≤ Real.exp (max 0 (t * d + t ^ 2 * (V : ℝ) / 2)) * expPotential t z x := by
  have hm : Measurable fun r : ℝ => expPotential t z (x + r + d) :=
    (measurable_expPotential t z).comp ((measurable_const.add measurable_id).add measurable_const)
  have hint1 : Integrable (fun r => expPotential t z (x + r + d)) (gaussianReal 0 V) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]
        exact abs_expPotential_le_one _ _ _)
  set q := t * d + t ^ 2 * (V : ℝ) / 2 with hq
  have hc1 : 1 ≤ Real.exp (max 0 q) := Real.one_le_exp (le_max_left _ _)
  have hle1 : ∫ r, expPotential t z (x + r + d) ∂(gaussianReal 0 V) ≤ 1 := by
    calc ∫ r, expPotential t z (x + r + d) ∂(gaussianReal 0 V)
        ≤ ∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 V) :=
          integral_mono hint1 (integrable_const 1) fun r => expPotential_le_one _ _ _
      _ = 1 := by simp
  have hle2 : ∫ r, expPotential t z (x + r + d) ∂(gaussianReal 0 V)
      ≤ Real.exp q * Real.exp (t * (x - z)) := by
    have hmgf : ∫ r, Real.exp (t * r) ∂(gaussianReal 0 V) = Real.exp ((V : ℝ) * t ^ 2 / 2) := by
      have := congrFun (mgf_id_gaussianReal (μ := 0) (v := V)) t
      simpa [mgf] using this
    have hexpint : Integrable (fun r => Real.exp (t * (x + d - z)) * Real.exp (t * r))
        (gaussianReal 0 V) := (integrable_exp_mul_gaussianReal t).const_mul _
    have hpt : ∀ r, expPotential t z (x + r + d)
        ≤ Real.exp (t * (x + d - z)) * Real.exp (t * r) := by
      intro r
      rw [← Real.exp_add]
      refine le_trans (min_le_right _ _) (le_of_eq ?_)
      congr 1
      ring
    calc ∫ r, expPotential t z (x + r + d) ∂(gaussianReal 0 V)
        ≤ ∫ r, Real.exp (t * (x + d - z)) * Real.exp (t * r) ∂(gaussianReal 0 V) :=
          integral_mono hint1 hexpint hpt
      _ = Real.exp (t * (x + d - z)) * Real.exp ((V : ℝ) * t ^ 2 / 2) := by
          rw [integral_const_mul, hmgf]
      _ = Real.exp q * Real.exp (t * (x - z)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hq]
          ring
  have hE : expPotential t z x = min 1 (Real.exp (t * (x - z))) := rfl
  rw [hE]
  rcases le_total (Real.exp (t * (x - z))) 1 with h | h
  · rw [min_eq_right h]
    calc _ ≤ Real.exp q * Real.exp (t * (x - z)) := hle2
      _ ≤ Real.exp (max 0 q) * Real.exp (t * (x - z)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (le_max_right _ _)) (Real.exp_pos _).le
  · rw [min_eq_left h, mul_one]
    exact le_trans hle1 hc1

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **The frozen potential grows by at most the step's factor**
`exp(max(0, td_k + t²v_k/2))`, for `t ≥ 0`, by the one-step bound
`RMF.integral_expPotential_gaussian_le_mul`. -/
theorem IsGaussianWalk.integral_frozenPotential_succ_le_mul (h : IsGaussianWalk G v μ)
    {d : ℕ → ℝ} {t z : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ∫ ω, frozenPotential G d t z (k + 1) ω ∂μ
      ≤ Real.exp (max 0 (t * d k + t ^ 2 * (v k : ℝ) / 2))
        * ∫ ω, frozenPotential G d t z k ω ∂μ := by
  set c := Real.exp (max 0 (t * d k + t ^ 2 * (v k : ℝ) / 2)) with hcdef
  have hc1 : 1 ≤ c := Real.one_le_exp (le_max_left _ _)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  set g : ℕ → ℝ := fun j => z - driftSum d j with hgdef
  set A : Set Ω := survivalSet G g k with hAdef
  have hAm : MeasurableSet A := by
    rw [hAdef, survivalSet_eq_preimage G g k]
    exact ((measurable_prefixSums k).comp (measurable_pi_lambda _ fun i => h.measurable i))
      (measurableSet_forall_le_pi g k)
  set X : Ω → ℕ → ℝ := fun ω => prefixSums k fun i => G i ω with hXdef
  have hX : Measurable X :=
    (measurable_prefixSums k).comp (measurable_pi_lambda _ fun i => h.measurable i)
  set S : Set (ℕ → ℝ) := {f | ∀ j ≤ k, f j ≤ g j} with hSdef
  have hS : MeasurableSet S := measurableSet_forall_le_pi g k
  have hA : A = X ⁻¹' S := survivalSet_eq_preimage G g k
  have hpre : ∀ ω, X ω k = walk G k ω := fun ω => prefixSums_comp G le_rfl ω
  have hstepω : ∀ ω, walk G (k + 1) ω = walk G k ω + G k ω := fun ω => by
    rw [walk_succ]
    rfl
  have hDk : driftSum d (k + 1) = driftSum d k + d k := by
    simp [driftSum, Finset.sum_range_succ]
  -- the potential after the step, as a function of the prefix and the step
  set Φ₀ : (ℕ → ℝ) × ℝ → ℝ := fun p => expPotential t z (p.1 k + driftSum d k + p.2 + d k)
    with hΦ₀def
  have hΦ₀m : Measurable Φ₀ :=
    (measurable_expPotential t z).comp (((((measurable_pi_apply k).comp measurable_fst).add
      measurable_const).add measurable_snd).add measurable_const)
  set Φ : (ℕ → ℝ) × ℝ → ℝ := fun p => Φ₀ p / c with hΦdef
  have hΦm : Measurable Φ := hΦ₀m.div_const c
  have hΦb : ∀ p, |Φ p| ≤ 1 := by
    intro p
    rw [hΦdef, abs_of_nonneg (div_nonneg (expPotential_nonneg _ _ _) hc0.le),
      div_le_one hc0]
    exact le_trans (expPotential_le_one _ _ _) hc1
  set Ψ : (ℕ → ℝ) → ℝ := fun f => expPotential t z (f k + driftSum d k) with hΨdef
  have hΨm : Measurable Ψ :=
    (measurable_expPotential t z).comp ((measurable_pi_apply k).add measurable_const)
  have hle : ∀ f ∈ S, ∫ r, Φ (f, r) ∂(gaussianReal 0 (v k)) ≤ Ψ f := by
    intro f _
    have h1 := integral_expPotential_gaussian_le_mul (t := t) (z := z) (x := f k + driftSum d k)
      (d := d k) (V := v k)
    simp only [hΦdef, hΦ₀def]
    rw [integral_div, div_le_iff₀ hc0]
    calc ∫ r, expPotential t z (f k + driftSum d k + r + d k) ∂(gaussianReal 0 (v k))
        ≤ c * expPotential t z (f k + driftSum d k) := h1
      _ = Ψ f * c := by rw [hΨdef]; ring
  have hcond := integral_indicator_comp_le_of_indepFun hX (h.measurable k) hS hΦm hΨm
    hΦb (fun f => abs_expPotential_le_one _ _ _) (h.indepFun_prefixSums_step k) (h.map_eq k) hle
  -- pointwise: the new potential is the complement plus the stepped potential on `A`
  have hA1 : survivalSet G g (k + 1) = A ∩ {ω | walk G (k + 1) ω ≤ g (k + 1)} :=
    survivalSet_succ G g k
  have hpt : ∀ ω, frozenPotential G d t z (k + 1) ω
      = Aᶜ.indicator (fun _ => (1 : ℝ)) ω
        + c * (X ⁻¹' S).indicator (fun ω => Φ (X ω, G k ω)) ω := by
    intro ω
    have hΦω : c * Φ (X ω, G k ω)
        = expPotential t z (walk G (k + 1) ω + driftSum d (k + 1)) := by
      simp only [hΦdef, hΦ₀def, hpre, hstepω, hDk]
      rw [mul_div_cancel₀ _ hc0.ne']
      congr 1
      ring
    by_cases hω : ω ∈ A
    · have hωS : ω ∈ X ⁻¹' S := by rw [← hA]; exact hω
      rw [Set.indicator_of_notMem (show ω ∉ Aᶜ from fun h' => h' hω),
        Set.indicator_of_mem hωS, hΦω, zero_add]
      unfold frozenPotential
      by_cases hω1 : ω ∈ survivalSet G (fun j => z - driftSum d j) (k + 1)
      · rw [Set.indicator_of_notMem (show ω ∉ (survivalSet G (fun j => z - driftSum d j)
          (k + 1))ᶜ from fun h' => h' hω1), Set.indicator_of_mem hω1, zero_add]
      · rw [Set.indicator_of_mem (show ω ∈ (survivalSet G (fun j => z - driftSum d j)
          (k + 1))ᶜ from hω1), Set.indicator_of_notMem hω1, add_zero]
        have hexit : z < walk G (k + 1) ω + driftSum d (k + 1) := by
          have hnot : ¬ (walk G (k + 1) ω ≤ g (k + 1)) := by
            intro hle1
            exact hω1 (by rw [← hgdef, hA1]; exact ⟨hω, hle1⟩)
          simp only [hgdef] at hnot
          push Not at hnot
          linarith
        rw [expPotential_eq_one_of_lt ht hexit]
    · have hωS : ω ∉ X ⁻¹' S := by rw [← hA]; exact hω
      rw [Set.indicator_of_mem (show ω ∈ Aᶜ from hω), Set.indicator_of_notMem hωS, mul_zero,
        add_zero]
      unfold frozenPotential
      have hω1 : ω ∉ survivalSet G (fun j => z - driftSum d j) (k + 1) := by
        intro h'
        rw [← hgdef, hA1] at h'
        exact hω h'.1
      rw [Set.indicator_of_mem (show ω ∈ (survivalSet G (fun j => z - driftSum d j)
        (k + 1))ᶜ from hω1), Set.indicator_of_notMem hω1, add_zero]
  have hk : ∀ ω, frozenPotential G d t z k ω
      = Aᶜ.indicator (fun _ => (1 : ℝ)) ω + (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω := by
    intro ω
    unfold frozenPotential
    rw [← hA]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      simp only [hΨdef, hpre]
      rfl
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  -- integrate
  have hint1 : Integrable (fun ω => Aᶜ.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hAm.compl
  have hintΦ : Integrable (fun ω => (X ⁻¹' S).indicator (fun ω => Φ (X ω, G k ω)) ω) μ := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hΦm.comp (hX.prodMk (h.measurable k))).indicator (hX hS)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ X ⁻¹' S
      · rw [Set.indicator_of_mem hω]
        exact hΦb _
      · rw [Set.indicator_of_notMem hω, abs_zero]
        norm_num
  have hintΨ : Integrable (fun ω => (X ⁻¹' S).indicator (fun ω => Ψ (X ω)) ω) μ := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hΨm.comp hX).indicator (hX hS)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ X ⁻¹' S
      · rw [Set.indicator_of_mem hω]
        exact abs_expPotential_le_one _ _ _
      · rw [Set.indicator_of_notMem hω, abs_zero]
        norm_num
  have hA0 : 0 ≤ ∫ ω, Aᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_congr_ae (Filter.Eventually.of_forall hk),
    integral_add hint1 (hintΦ.const_mul c), integral_add hint1 hintΨ, integral_const_mul]
  nlinarith

/-- **The exponential maximal bound, the steps paid.**  For `t ≥ 0` and `z ≥ 0`, the drifted walk
`S_j + D_j` exceeds `z` before step `n` with probability at most
`exp(-tz + ∑_{m<n} max(0, td_m + t²v_m/2))`: steps with `td_m + t²v_m/2 ≤ 0` are free, the others
pay their factor (`RMF.IsGaussianWalk.integral_frozenPotential_succ_le_mul`). -/
theorem IsGaussianWalk.measureReal_survivalSet_compl_le_exp_sum (h : IsGaussianWalk G v μ)
    {d : ℕ → ℝ} {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) (n : ℕ) :
    μ.real (survivalSet G (fun j => z - driftSum d j) n)ᶜ
      ≤ Real.exp (-(t * z) + ∑ m ∈ Finset.range n, max 0 (t * d m + t ^ 2 * (v m : ℝ) / 2)) := by
  have h0 : ∫ ω, frozenPotential G d t z 0 ω ∂μ ≤ Real.exp (-(t * z)) := by
    have hsurv0 : survivalSet G (fun j => z - driftSum d j) 0 = Set.univ := by
      ext ω
      simp only [survivalSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp [walk_zero, driftSum, hz]
    have hval : ∀ ω, frozenPotential G d t z 0 ω = expPotential t z 0 := by
      intro ω
      unfold frozenPotential
      rw [hsurv0, Set.compl_univ, Set.indicator_of_notMem (Set.notMem_empty ω),
        Set.indicator_of_mem (Set.mem_univ ω), zero_add]
      simp [walk_zero, driftSum]
    rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const, smul_eq_mul]
    simp only [probReal_univ, one_mul]
    unfold expPotential
    refine le_trans (min_le_right _ _) (le_of_eq ?_)
    congr 1
    ring
  have hmono : ∀ k, ∫ ω, frozenPotential G d t z k ω ∂μ
      ≤ Real.exp (-(t * z) + ∑ m ∈ Finset.range k, max 0 (t * d m + t ^ 2 * (v m : ℝ) / 2)) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
        calc ∫ ω, frozenPotential G d t z (k + 1) ω ∂μ
            ≤ Real.exp (max 0 (t * d k + t ^ 2 * (v k : ℝ) / 2))
              * ∫ ω, frozenPotential G d t z k ω ∂μ :=
              h.integral_frozenPotential_succ_le_mul ht k
          _ ≤ Real.exp (max 0 (t * d k + t ^ 2 * (v k : ℝ) / 2))
              * Real.exp (-(t * z)
                + ∑ m ∈ Finset.range k, max 0 (t * d m + t ^ 2 * (v m : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
          _ = Real.exp (-(t * z)
                + ∑ m ∈ Finset.range (k + 1), max 0 (t * d m + t ^ 2 * (v m : ℝ) / 2)) := by
              rw [← Real.exp_add, Finset.sum_range_succ]
              congr 1
              ring
  -- the complement is below the potential
  have hAm : MeasurableSet (survivalSet G (fun j => z - driftSum d j) n) := by
    rw [survivalSet_eq_preimage]
    exact ((measurable_prefixSums n).comp (measurable_pi_lambda _ fun i => h.measurable i))
      (measurableSet_forall_le_pi _ n)
  have hle : ∀ ω, (survivalSet G (fun j => z - driftSum d j) n)ᶜ.indicator
      (fun _ => (1 : ℝ)) ω ≤ frozenPotential G d t z n ω := by
    intro ω
    unfold frozenPotential
    have := Set.indicator_nonneg (s := survivalSet G (fun j => z - driftSum d j) n)
      (f := fun ω => expPotential t z (walk G n ω + driftSum d n))
      (fun ω _ => expPotential_nonneg _ _ _) ω
    linarith
  have hintP : Integrable (frozenPotential G d t z n) μ := by
    refine Integrable.of_bound ?_ 2 (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((measurable_const.indicator hAm.compl).add
        (((measurable_expPotential t z).comp ((h.measurable_walk n).add
          measurable_const)).indicator hAm)).aestronglyMeasurable
    · unfold frozenPotential
      rw [Real.norm_eq_abs]
      have h1 : |(survivalSet G (fun j => z - driftSum d j) n)ᶜ.indicator
          (fun _ => (1 : ℝ)) ω| ≤ 1 := by
        by_cases hω : ω ∈ (survivalSet G (fun j => z - driftSum d j) n)ᶜ
        · rw [Set.indicator_of_mem hω, abs_one]
        · rw [Set.indicator_of_notMem hω, abs_zero]
          norm_num
      have h2 : |(survivalSet G (fun j => z - driftSum d j) n).indicator
          (fun ω => expPotential t z (walk G n ω + driftSum d n)) ω| ≤ 1 := by
        by_cases hω : ω ∈ survivalSet G (fun j => z - driftSum d j) n
        · rw [Set.indicator_of_mem hω]
          exact abs_expPotential_le_one _ _ _
        · rw [Set.indicator_of_notMem hω, abs_zero]
          norm_num
      exact le_trans (abs_add_le _ _) (by linarith)
  calc μ.real (survivalSet G (fun j => z - driftSum d j) n)ᶜ
      = ∫ ω, (survivalSet G (fun j => z - driftSum d j) n)ᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        (integral_indicator_one hAm.compl).symm
    _ ≤ ∫ ω, frozenPotential G d t z n ω ∂μ :=
        integral_mono ((integrable_const (1 : ℝ)).indicator hAm.compl) hintP hle
    _ ≤ _ := hmono n

/-- `D_j` for the drift `-d - B` is `-D_j - Bj`. -/
lemma driftSum_neg_sub (d : ℕ → ℝ) (B : ℝ) (j : ℕ) :
    driftSum (fun m => -d m - B) j = -driftSum d j - B * j := by
  simp only [driftSum, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

/-! ### The suffix: a tube, and the slope walk paid relatively -/

/-- **A prefix event, then survival.**  The paths on which the slope walk `∑_{m<i} r_m G_m`
passes `Lb` by step `m₀` and which stay below `z ≥ 0` on `[m₀, n]` have probability at most
`K((z + c)P(Bad) + √(P(Bad)m₀v₊))`, `K = √(2/(π(n-m₀)v₋))`, `c = √(πv₊/2)`: given the prefix, the
survival costs `(z - S_{m₀} + c)K` (`RMF.IsGaussianWalk.measureReal_forall_le_le_sqrt`), and
`E[1_Bad|S_{m₀}|] ≤ √(P(Bad)E S_{m₀}²)`. -/
theorem IsGaussianWalk.measureReal_prefix_inter_survive_le (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n m₀ : ℕ} (hm₀ : m₀ < n)
    (r : ℕ → ℝ) (Lb : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    μ.real ({ω | ∃ i ≤ m₀, Lb < walk (fun m ω => r m * G m ω) i ω}
        ∩ {ω | ∀ j, m₀ ≤ j → j ≤ n → walk G j ω ≤ z})
      ≤ √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin)))
        * ((z + √(π * vmax / 2)) * μ.real {ω | ∃ i ≤ m₀, Lb < walk (fun m ω => r m * G m ω) i ω}
          + √(μ.real {ω | ∃ i ≤ m₀, Lb < walk (fun m ω => r m * G m ω) i ω}
            * ((m₀ : ℝ) * vmax))) := by
  classical
  set Bad : Set Ω := {ω | ∃ i ≤ m₀, Lb < walk (fun m ω => r m * G m ω) i ω} with hBad
  set c : ℝ := √(π * vmax / 2) with hcdef
  set K : ℝ := √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin))) with hKdef
  have hvmin := hv.pos
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hv.lo 0) (hv.hi 0))
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hrG := h.const_mul r
  have hBadm : MeasurableSet Bad := by
    have hrw : Bad = ⋃ i ∈ Set.Iic m₀, {ω | Lb < walk (fun m ω => r m * G m ω) i ω} := by
      ext ω
      simp [hBad]
    rw [hrw]
    exact MeasurableSet.biUnion (Set.to_countable _) fun i _ =>
      measurableSet_lt measurable_const (hrG.measurable_walk i)
  -- the prefix, read as the walk and the slope walk, and the suffix
  set φ : (↥(Finset.range m₀) → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun x => (prefixSums m₀ x, prefixSums m₀ fun i => r i * x i) with hφ
  have hφm : Measurable φ := by
    refine (measurable_prefixSums m₀).prodMk ((measurable_prefixSums m₀).comp ?_)
    exact measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i)
  set X : Ω → (ℕ → ℝ) × (ℕ → ℝ) := fun ω => φ fun i => G i ω with hXdef
  set Y : Ω → (ℕ → ℝ) := fun ω => blockSums m₀ n fun i => G i ω with hYdef
  have hXm : Measurable X := hφm.comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hYm : Measurable Y :=
    (measurable_blockSums m₀ n).comp (measurable_pi_lambda _ fun i => h.measurable (i : ℕ))
  have hind : IndepFun X Y μ := by
    have hdisj : Disjoint (Finset.range m₀) (Finset.Ico m₀ n) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_Ico] at hb
      omega
    exact (h.indep.indepFun_finset _ _ hdisj h.measurable).comp hφm (measurable_blockSums m₀ n)
  have hX1 : ∀ ω, (X ω).1 m₀ = walk G m₀ ω := fun ω => by
    change prefixSums m₀ (fun i => G i ω) m₀ = walk G m₀ ω
    exact prefixSums_comp G le_rfl ω
  have hX2 : ∀ ω j, j ≤ m₀ → (X ω).2 j = walk (fun m ω => r m * G m ω) j ω := fun ω j hj => by
    change prefixSums m₀ (fun i => r i * G i ω) j = walk (fun m ω => r m * G m ω) j ω
    exact prefixSums_comp (fun m ω => r m * G m ω) hj ω
  set S : Set (((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) :=
    {p | (∃ i ≤ m₀, Lb < p.1.2 i) ∧ ∀ j, m₀ ≤ j → j ≤ n → p.1.1 m₀ + p.2 j ≤ z} with hSdef
  have hS : MeasurableSet S := by
    have hrw : S = (⋃ i ∈ Set.Iic m₀, {p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) | Lb < p.1.2 i})
        ∩ ⋂ j ∈ Set.Icc m₀ n,
          {p : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) | p.1.1 m₀ + p.2 j ≤ z} := by
      ext p
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
        Set.mem_Iic, Set.mem_Icc, exists_prop]
      exact and_congr_right fun _ => ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
    rw [hrw]
    refine (MeasurableSet.biUnion (Set.to_countable _) fun i _ => ?_).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_)
    · exact measurableSet_lt measurable_const
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
    · exact measurableSet_le (((measurable_pi_apply m₀).comp
        (measurable_fst.comp measurable_fst)).add ((measurable_pi_apply j).comp measurable_snd))
        measurable_const
  have hset : Bad ∩ {ω | ∀ j, m₀ ≤ j → j ≤ n → walk G j ω ≤ z}
      = (fun ω => (X ω, Y ω)) ⁻¹' S := by
    ext ω
    simp only [hBad, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, hSdef]
    refine and_congr ?_ ?_
    · exact exists_congr fun i => and_congr_right fun hi => by rw [hX2 ω i hi]
    · refine forall_congr' fun j => forall_congr' fun hj1 => forall_congr' fun hjn => ?_
      rw [hX1 ω, hYdef]
      simp only
      rw [blockSums_comp G hj1 hjn ω]
      constructor <;> intro hh <;> linarith
  -- the fibre bound
  set Bad' : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {x | ∃ i ≤ m₀, Lb < x.2 i} with hBad'
  have hBad'm : MeasurableSet Bad' := by
    have hrw : Bad' = ⋃ i ∈ Set.Iic m₀, {x : (ℕ → ℝ) × (ℕ → ℝ) | Lb < x.2 i} := by
      ext x
      simp [hBad']
    rw [hrw]
    exact MeasurableSet.biUnion (Set.to_countable _) fun i _ =>
      measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_snd)
  set ψ : (ℕ → ℝ) × (ℕ → ℝ) → ℝ := Bad'.indicator (fun x => K * (|z - x.1 m₀| + c)) with hψ
  have hψm : Measurable ψ :=
    (measurable_const.mul (((measurable_const.sub ((measurable_pi_apply m₀).comp
      measurable_fst)).abs).add measurable_const)).indicator hBad'm
  have hfib : ∀ x, (μ.map Y) (Prod.mk x ⁻¹' S) ≤ ENNReal.ofReal (ψ x) := by
    intro x
    by_cases hx : x ∈ Bad'
    · have hslice : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
      rw [Measure.map_apply hYm hslice]
      have hpre : Y ⁻¹' (Prod.mk x ⁻¹' S)
          = {ω | ∀ k ≤ n - m₀, walk (fun m => G (m + m₀)) k ω ≤ z - x.1 m₀} := by
        ext ω
        simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, hYdef]
        constructor
        · rintro ⟨-, hh⟩ k hk
          have h1 := hh (m₀ + k) (by omega) (by omega)
          rw [blockSums_comp G (by omega) (by omega) ω] at h1
          rw [walk_shift]
          linarith
        · intro hh
          refine ⟨hx, fun j hj1 hjn => ?_⟩
          have h1 := hh (j - m₀) (by omega)
          rw [walk_shift, show m₀ + (j - m₀) = j by omega] at h1
          rw [blockSums_comp G hj1 hjn ω]
          linarith
      rw [hpre, ← ofReal_measureReal (measure_ne_top _ _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hψ, Set.indicator_of_mem hx]
      rcases le_or_gt 0 (z - x.1 m₀) with hy | hy
      · have hv' : VarBracket (fun m => v (m + m₀)) vmin vmax :=
          ⟨hv.pos, fun i => hv.lo (i + m₀), fun i => hv.hi (i + m₀)⟩
        have hb := (h.shift m₀).measureReal_forall_le_le_sqrt hv' hc0 le_rfl
          (n := n - m₀) (by omega) hy
        calc _ ≤ (z - x.1 m₀ + c) * √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin))) := hb
          _ ≤ K * (|z - x.1 m₀| + c) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (z - x.1 m₀)]) hK0
      · have hempty : {ω | ∀ k ≤ n - m₀, walk (fun m => G (m + m₀)) k ω ≤ z - x.1 m₀} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
          exact ⟨0, Nat.zero_le _, by rw [walk_zero]; simpa using hy⟩
        rw [hempty, measureReal_empty]
        exact mul_nonneg hK0 (by positivity)
    · have hempty : Prod.mk x ⁻¹' S = ∅ := by
        ext y
        simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        exact fun hh => hx hh.1
      rw [hempty, measure_empty]
      exact bot_le
  -- back on `Ω`
  have hψX : ∀ ω, ψ (X ω) = Bad.indicator (fun ω => K * (|z - walk G m₀ ω| + c)) ω := by
    intro ω
    have hmem : X ω ∈ Bad' ↔ ω ∈ Bad := by
      simp only [hBad', hBad, Set.mem_setOf_eq]
      exact exists_congr fun i => and_congr_right fun hi => by rw [hX2 ω i hi]
    by_cases hω : ω ∈ Bad
    · rw [hψ, Set.indicator_of_mem (hmem.2 hω), Set.indicator_of_mem hω, hX1 ω]
    · rw [hψ, Set.indicator_of_notMem (fun h' => hω (hmem.1 h')), Set.indicator_of_notMem hω]
  have hSint : Integrable (walk G m₀) μ :=
    integrable_of_hasLaw_gaussianReal (h.measurable_walk m₀) (h.map_walk m₀)
  have hS2int : Integrable (fun ω => walk G m₀ ω * walk G m₀ ω) μ :=
    integrable_mul_self_of_hasLaw_gaussianReal (h.measurable_walk m₀) (h.map_walk m₀)
  have hint : Integrable (fun ω => ψ (X ω)) μ := by
    have h1 : Integrable (fun ω => K * (|z - walk G m₀ ω| + c)) μ :=
      ((((integrable_const z).sub hSint).abs).add (integrable_const c)).const_mul K
    exact (h1.indicator hBadm).congr (Filter.Eventually.of_forall fun ω => (hψX ω).symm)
  have hnn : 0 ≤ᵐ[μ] fun ω => ψ (X ω) := Filter.Eventually.of_forall fun ω => by
    change 0 ≤ ψ (X ω)
    rw [hψX]
    exact Set.indicator_nonneg (fun ω _ => mul_nonneg hK0 (by positivity)) ω
  have hlint : μ ((fun ω => (X ω, Y ω)) ⁻¹' S) ≤ ENNReal.ofReal (∫ ω, ψ (X ω) ∂μ) := by
    rw [measure_preimage_prod_eq_lintegral hXm hYm hind hS]
    calc ∫⁻ x, (μ.map Y) (Prod.mk x ⁻¹' S) ∂(μ.map X)
        ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂(μ.map X) := lintegral_mono hfib
      _ = ∫⁻ ω, ENNReal.ofReal (ψ (X ω)) ∂μ :=
          lintegral_map (ENNReal.measurable_ofReal.comp hψm) hXm
      _ = ENNReal.ofReal (∫ ω, ψ (X ω) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  -- the integral
  have hES2 : ∫ ω, walk G m₀ ω * walk G m₀ ω ∂μ ≤ (m₀ : ℝ) * vmax := by
    rw [integral_sq_of_hasLaw_gaussianReal (h.measurable_walk m₀) (h.map_walk m₀)]
    have := sum_range_var_le (v := v) hv.hi m₀
    simpa using this
  have hCS : ∫ ω, Bad.indicator (fun ω => |walk G m₀ ω|) ω ∂μ
      ≤ √(μ.real Bad * ((m₀ : ℝ) * vmax)) := by
    have hsq : Integrable (fun ω => |walk G m₀ ω| ^ 2) μ :=
      hS2int.congr (Filter.Eventually.of_forall fun ω => by
        change walk G m₀ ω * walk G m₀ ω = |walk G m₀ ω| ^ 2
        rw [sq_abs, sq])
    have h1 := sq_integral_indicator_le (μ := μ) hBadm hSint.abs hsq
    have h2 : ∫ ω, Bad.indicator (fun ω => |walk G m₀ ω| ^ 2) ω ∂μ ≤ (m₀ : ℝ) * vmax := by
      refine le_trans (integral_mono (hsq.indicator hBadm) hsq fun ω => ?_) ?_
      · exact Set.indicator_le_self' (fun ω _ => sq_nonneg _) ω
      · refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall
          fun ω => ?_))) hES2
        simp only
        rw [sq_abs, sq]
    have h3 : (∫ ω, Bad.indicator (fun ω => |walk G m₀ ω|) ω ∂μ) ^ 2
        ≤ μ.real Bad * ((m₀ : ℝ) * vmax) := by
      rw [mul_comm]
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 measureReal_nonneg)
    exact Real.le_sqrt_of_sq_le h3
  have hpt : ∀ ω, ψ (X ω) ≤ K * ((z + c) * Bad.indicator (fun _ => (1 : ℝ)) ω
      + Bad.indicator (fun ω => |walk G m₀ ω|) ω) := by
    intro ω
    rw [hψX]
    by_cases hω : ω ∈ Bad
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      have := abs_sub z (walk G m₀ ω)
      rw [abs_of_nonneg hz] at this
      linarith
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      simp
  have hbound : ∫ ω, ψ (X ω) ∂μ
      ≤ K * ((z + c) * μ.real Bad + √(μ.real Bad * ((m₀ : ℝ) * vmax))) := by
    have hi1 : Integrable (fun ω => Bad.indicator (fun _ => (1 : ℝ)) ω) μ :=
      (integrable_const (1 : ℝ)).indicator hBadm
    have hi2 : Integrable (fun ω => Bad.indicator (fun ω => |walk G m₀ ω|) ω) μ :=
      hSint.abs.indicator hBadm
    calc ∫ ω, ψ (X ω) ∂μ
        ≤ ∫ ω, K * ((z + c) * Bad.indicator (fun _ => (1 : ℝ)) ω
            + Bad.indicator (fun ω => |walk G m₀ ω|) ω) ∂μ :=
          integral_mono hint (((hi1.const_mul (z + c)).add hi2).const_mul K) hpt
      _ = K * ((z + c) * μ.real Bad
            + ∫ ω, Bad.indicator (fun ω => |walk G m₀ ω|) ω ∂μ) := by
          rw [integral_const_mul, integral_add (hi1.const_mul (z + c)) hi2, integral_const_mul,
            integral_indicator_const _ hBadm, smul_eq_mul, mul_one]
      _ ≤ K * ((z + c) * μ.real Bad + √(μ.real Bad * ((m₀ : ℝ) * vmax))) := by
          gcongr
  rw [hset, measureReal_def]
  exact le_trans (ENNReal.toReal_le_of_le_ofReal (integral_nonneg_of_ae hnn) hlint) hbound

/-- **The tube with the slope walk paid, from below.**  For a flat ceiling `z ≥ 0` and a floor
below `-D - Bi`, the Gaussian walk stays in the tube and the slope walk `∑_{m<i} r_m G_m` stays
below `L` on `[0, n]` with probability at least the ballot less the floor loss
(`RMF.IsGaussianWalk.le_measure_barrierEvent_flat_depth`) less the slope loss
`K((z + c)P_R + √(P_R m₀v₊))`, `P_R = exp(-(L-K')²/(2σ²))`.  Past `m₀` the slope walk moves by at
most `K'` on the tube (the envelope `Menv` of the tube started at `x₀`); before `m₀` it passes
`L - K'` with probability at most `P_R`
(`RMF.IsGaussianWalk.measureReal_survivalSet_compl_le_exp_sum`), and that event is charged
relatively (`RMF.IsGaussianWalk.measureReal_prefix_inter_survive_le`). -/
theorem IsGaussianWalk.le_measure_tube_inter_slope (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n m₀ : ℕ} (hm₀ : m₀ < n) (r : ℕ → ℝ)
    {lo Menv : ℕ → ℝ} {z D B L K σ2 x₀ : ℝ} (hz : 0 ≤ z) (hD : 0 ≤ D) (hB : 2 * vmax < B)
    (hlo : ∀ i : ℕ, 1 ≤ i → lo i ≤ -D - B * i) (hMenv0 : ∀ i, 0 ≤ Menv i)
    (hMenv : ∀ i, 1 ≤ i → i ≤ n → -Menv i ≤ x₀ + lo i ∧ x₀ + z ≤ Menv i)
    (hx₀ : |x₀| ≤ Menv 0)
    (hK : ∑ m ∈ Finset.Ico m₀ n, |r m| * (Menv m + Menv (m + 1)) ≤ K) (hKL : K ≤ L)
    (hσ : ∑ m ∈ Finset.range m₀, r m ^ 2 * (v m : ℝ) ≤ σ2) (hσ0 : 0 < σ2) :
    ballotLinear vmin vmax n z - floorLossDepth D B vmin vmax n z
      - √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin)))
        * ((z + √(π * vmax / 2)) * Real.exp (-((L - K) ^ 2 / (2 * σ2)))
          + √(Real.exp (-((L - K) ^ 2 / (2 * σ2))) * ((m₀ : ℝ) * vmax)))
      ≤ (μ (barrierEvent G n lo (fun _ => z)
          ∩ {ω | ∀ i ≤ n, walk (fun m ω => r m * G m ω) i ω ≤ L})).toReal := by
  set T := barrierEvent G n lo (fun _ => z) with hT
  set R := {ω | ∀ i ≤ n, walk (fun m ω => r m * G m ω) i ω ≤ L} with hR
  set Bad : Set Ω := {ω | ∃ i ≤ m₀, L - K < walk (fun m ω => r m * G m ω) i ω} with hBad
  set Surv : Set Ω := {ω | ∀ j, m₀ ≤ j → j ≤ n → walk G j ω ≤ z} with hSurv
  set PR := Real.exp (-((L - K) ^ 2 / (2 * σ2))) with hPR
  set Kr := √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin))) with hKr
  set c := √(π * vmax / 2) with hc
  have hrG := h.const_mul r
  have hn : 1 ≤ n := by omega
  have hK0 : 0 ≤ K := le_trans (Finset.sum_nonneg fun m _ =>
    mul_nonneg (abs_nonneg _) (add_nonneg (hMenv0 _) (hMenv0 _))) hK
  have hRm : MeasurableSet R := by
    have hrw : R = ⋂ i ∈ Set.Iic n, {ω | walk (fun m ω => r m * G m ω) i ω ≤ L} := by
      ext ω
      simp [hR]
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
      measurableSet_le (hrG.measurable_walk i) measurable_const
  -- the ballot, less the floor
  have hball := h.le_measure_barrierEvent_flat_depth hv hn z hD hB hlo
  -- the envelope on the tube
  have henv : ∀ ω ∈ T, ∀ i ≤ n, |x₀ + walk G i ω| ≤ Menv i := by
    intro ω hω i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simpa [walk_zero] using hx₀
    · have hb := hω i hi1 hi
      rw [Set.mem_Icc] at hb
      obtain ⟨h1, h2⟩ := hMenv i hi1 hi
      rw [abs_le]
      constructor <;> linarith [hb.1, hb.2]
  have hinc : ∀ ω ∈ T, ∀ m, m < n → |G m ω| ≤ Menv m + Menv (m + 1) := by
    intro ω hω m hm
    have e : G m ω = (x₀ + walk G (m + 1) ω) - (x₀ + walk G m ω) := by
      rw [walk_succ, Pi.add_apply]
      ring
    rw [e]
    calc _ ≤ |x₀ + walk G (m + 1) ω| + |x₀ + walk G m ω| := abs_sub _ _
      _ ≤ Menv (m + 1) + Menv m := add_le_add (henv ω hω (m + 1) hm) (henv ω hω m hm.le)
      _ = _ := by ring
  -- past `m₀` the slope walk moves by at most `K` on the tube
  have hlate : ∀ ω ∈ T, ∀ i, m₀ ≤ i → i ≤ n →
      walk (fun m ω => r m * G m ω) i ω ≤ walk (fun m ω => r m * G m ω) m₀ ω + K := by
    intro ω hω i hi1 hin
    have hsub : walk (fun m ω => r m * G m ω) i ω - walk (fun m ω => r m * G m ω) m₀ ω
        = ∑ m ∈ Finset.Ico m₀ i, r m * G m ω := by
      have := congrFun (walk_sub_eq (fun m ω => r m * G m ω) hi1) ω
      simpa [Finset.sum_apply] using this
    have hbound : ∑ m ∈ Finset.Ico m₀ i, r m * G m ω ≤ K := by
      calc ∑ m ∈ Finset.Ico m₀ i, r m * G m ω
          ≤ ∑ m ∈ Finset.Ico m₀ i, |r m| * (Menv m + Menv (m + 1)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hm' := Finset.mem_Ico.1 hm
            calc r m * G m ω ≤ |r m * G m ω| := le_abs_self _
              _ = |r m| * |G m ω| := abs_mul _ _
              _ ≤ |r m| * (Menv m + Menv (m + 1)) :=
                  mul_le_mul_of_nonneg_left (hinc ω hω m (by omega)) (abs_nonneg _)
        _ ≤ ∑ m ∈ Finset.Ico m₀ n, |r m| * (Menv m + Menv (m + 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hin)
              fun m _ _ => mul_nonneg (abs_nonneg _) (add_nonneg (hMenv0 _) (hMenv0 _))
        _ ≤ K := hK
    linarith
  -- a slope failure on the tube is a prefix event followed by survival
  have hsub : T \ R ⊆ Bad ∩ Surv := by
    rintro ω ⟨hωT, hωR⟩
    refine ⟨?_, ?_⟩
    · simp only [hR, Set.mem_setOf_eq, not_forall, not_le] at hωR
      obtain ⟨i, hi, hiL⟩ := hωR
      rcases le_or_gt i m₀ with him | him
      · exact ⟨i, him, by linarith⟩
      · exact ⟨m₀, le_rfl, by linarith [hlate ω hωT i him.le hi]⟩
    · intro j hj1 hjn
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa [walk_zero] using hz
      · exact (hωT j hj hjn).2
  -- the prefix event has probability at most `P_R`
  have hBadR : μ.real Bad ≤ PR := by
    have hBadeq : Bad = (survivalSet (fun m ω => r m * G m ω)
        (fun j => (L - K) - driftSum (fun _ => 0) j) m₀)ᶜ := by
      ext ω
      simp only [hBad, survivalSet, driftSum, Finset.sum_const_zero, sub_zero,
        Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, exists_prop]
    have ht0 : 0 ≤ (L - K) / σ2 := div_nonneg (by linarith) hσ0.le
    have hexp := hrG.measureReal_survivalSet_compl_le_exp_sum (d := fun _ => 0) ht0
      (by linarith : 0 ≤ L - K) m₀
    rw [← hBadeq] at hexp
    have hsum : ∑ m ∈ Finset.range m₀, max 0 ((L - K) / σ2 * 0
        + ((L - K) / σ2) ^ 2 * ((⟨r m ^ 2, sq_nonneg _⟩ * v m : ℝ≥0) : ℝ) / 2)
        ≤ ((L - K) / σ2) ^ 2 * σ2 / 2 := by
      have hterm : ∀ m ∈ Finset.range m₀, max 0 ((L - K) / σ2 * 0
          + ((L - K) / σ2) ^ 2 * ((⟨r m ^ 2, sq_nonneg _⟩ * v m : ℝ≥0) : ℝ) / 2)
          = ((L - K) / σ2) ^ 2 / 2 * (r m ^ 2 * (v m : ℝ)) := by
        intro m _
        have hco : ((⟨r m ^ 2, sq_nonneg _⟩ * v m : ℝ≥0) : ℝ) = r m ^ 2 * (v m : ℝ) := by
          rw [NNReal.coe_mul]
          rfl
        rw [hco, max_eq_right (by positivity)]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      calc ((L - K) / σ2) ^ 2 / 2 * ∑ m ∈ Finset.range m₀, r m ^ 2 * (v m : ℝ)
          ≤ ((L - K) / σ2) ^ 2 / 2 * σ2 := mul_le_mul_of_nonneg_left hσ (by positivity)
        _ = ((L - K) / σ2) ^ 2 * σ2 / 2 := by ring
    refine le_trans hexp (Real.exp_le_exp.2 ?_)
    have hid : -((L - K) / σ2 * (L - K)) + ((L - K) / σ2) ^ 2 * σ2 / 2
        = -((L - K) ^ 2 / (2 * σ2)) := by
      field_simp
      ring
    linarith
  -- combine
  have hA := h.measureReal_prefix_inter_survive_le hv hm₀ r (L - K) hz
  have hmono : Kr * ((z + c) * μ.real Bad + √(μ.real Bad * ((m₀ : ℝ) * vmax)))
      ≤ Kr * ((z + c) * PR + √(PR * ((m₀ : ℝ) * vmax))) := by
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hvmax : 0 ≤ vmax := le_trans hv.pos.le (le_trans (hv.lo 0) (hv.hi 0))
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Real.sqrt_nonneg _)
    · exact mul_le_mul_of_nonneg_left hBadR (by linarith)
    · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hBadR (by positivity))
  have hdiff : μ.real (T \ R) ≤ Kr * ((z + c) * PR + √(PR * ((m₀ : ℝ) * vmax))) :=
    le_trans (measureReal_mono hsub) (le_trans hA hmono)
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := T) hRm
  have hTreal : (μ T).toReal = μ.real T := rfl
  change _ ≤ μ.real (T ∩ R)
  linarith

end Walk

/-! ### Gaussian tools for the start -/

section Tools

/-- **Chernoff for a real Gaussian, lower tail**: `P(X ≤ m - x) ≤ exp(-x²/(2V))` for `x ≥ 0`
(at `V = 0` the right side is `1`). -/
lemma gaussianReal_real_Iic_sub_le {m x : ℝ} {V : ℝ≥0} (hx : 0 ≤ x) :
    (gaussianReal m V).real (Set.Iic (m - x)) ≤ Real.exp (-(x ^ 2 / (2 * V))) := by
  rcases eq_or_lt_of_le V.coe_nonneg with hV | hV
  · rw [← hV, mul_zero, div_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal m V) (X := id) (t := -(x / V)) (m - x)
    (by have := div_nonneg hx hV.le; linarith) (integrable_exp_mul_gaussianReal _)
  rw [mgf_id_gaussianReal] at h
  have hset : {ω : ℝ | id ω ≤ m - x} = Set.Iic (m - x) := rfl
  rw [hset, ← Real.exp_add] at h
  refine le_trans h (le_of_eq (congrArg Real.exp ?_))
  field_simp
  ring

/-- **Chernoff for a real Gaussian, upper tail**: `P(X ≥ m + x) ≤ exp(-x²/(2V))` for `x ≥ 0`. -/
lemma gaussianReal_real_Ici_add_le {m x : ℝ} {V : ℝ≥0} (hx : 0 ≤ x) :
    (gaussianReal m V).real (Set.Ici (m + x)) ≤ Real.exp (-(x ^ 2 / (2 * V))) := by
  rcases eq_or_lt_of_le V.coe_nonneg with hV | hV
  · rw [← hV, mul_zero, div_zero, neg_zero, Real.exp_zero]
    exact measureReal_le_one
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal m V) (X := id) (t := x / V) (m + x)
    (div_nonneg hx hV.le) (integrable_exp_mul_gaussianReal _)
  rw [mgf_id_gaussianReal] at h
  have hset : {ω : ℝ | m + x ≤ id ω} = Set.Ici (m + x) := rfl
  rw [hset, ← Real.exp_add] at h
  refine le_trans h (le_of_eq (congrArg Real.exp ?_))
  field_simp
  ring

/-- `exp(-x²/(2V))` decreases in `x ≥ 0`. -/
lemma exp_neg_sq_div_le {x y V : ℝ} (hV : 0 ≤ V) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp (-(y ^ 2 / (2 * V))) ≤ Real.exp (-(x ^ 2 / (2 * V))) := by
  refine Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right ?_ (by positivity)))
  exact pow_le_pow_left₀ hx hxy 2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **The lower tail of a Gaussian variable**: `P(X ≤ m - x) ≤ exp(-x²/(2V))`. -/
lemma measureReal_le_sub_le_of_map_eq {X : Ω → ℝ} (hX : Measurable X) {m : ℝ} {V : ℝ≥0}
    (hlaw : P.map X = gaussianReal m V) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | X ω ≤ m - x} ≤ Real.exp (-(x ^ 2 / (2 * V))) := by
  have h : P.real {ω | X ω ≤ m - x} = (gaussianReal m V).real (Set.Iic (m - x)) := by
    rw [← hlaw, map_measureReal_apply hX measurableSet_Iic]
    rfl
  rw [h]
  exact gaussianReal_real_Iic_sub_le hx

omit [IsProbabilityMeasure P] in
/-- **The upper tail of a Gaussian variable**: `P(X ≥ m + x) ≤ exp(-x²/(2V))`. -/
lemma measureReal_add_le_le_of_map_eq {X : Ω → ℝ} (hX : Measurable X) {m : ℝ} {V : ℝ≥0}
    (hlaw : P.map X = gaussianReal m V) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | m + x ≤ X ω} ≤ Real.exp (-(x ^ 2 / (2 * V))) := by
  have h : P.real {ω | m + x ≤ X ω} = (gaussianReal m V).real (Set.Ici (m + x)) := by
    rw [← hlaw, map_measureReal_apply hX measurableSet_Ici]
    rfl
  rw [h]
  exact gaussianReal_real_Ici_add_le hx

/-- **A Gaussian and a sheared independent Gaussian**: for `X ~ N(0, v)`, `v > 0`, and
`Y ~ N(0, s)` independent, `(X, βX + Y) ~ gaussianPairLaw 0 0 v (β²v + s) (βv)`. -/
lemma map_pair_shear_eq_gaussianPairLaw {X Y : Ω → ℝ} {v s : ℝ≥0} (hv : 0 < (v : ℝ)) (β : ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (hXlaw : P.map X = gaussianReal 0 v) (hYlaw : P.map Y = gaussianReal 0 s) :
    P.map (fun ω => (X ω, β * X ω + Y ω))
      = gaussianPairLaw 0 0 v (β ^ 2 * v + s) (β * v) := by
  have hmap : P.map (fun ω => (X ω, β * X ω + Y ω))
      = (P.map (fun ω => (X ω, Y ω))).map (fun p : ℝ × ℝ => (p.1, β * p.1 + p.2)) := by
    rw [Measure.map_map (by fun_prop) (hX.prodMk hY)]
    rfl
  rw [hmap, hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hXlaw, hYlaw]
  have hs : gaussianReal 0 s = (gaussianReal 0 1).map (fun w => Real.sqrt s * w) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt s.coe_nonneg]
  have hprod : (gaussianReal 0 v).prod ((gaussianReal 0 1).map (fun w => Real.sqrt s * w))
      = ((gaussianReal 0 v).prod (gaussianReal 0 1)).map
          (Prod.map id (fun w => Real.sqrt s * w)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
  rw [hs, hprod, Measure.map_map (by fun_prop) (by fun_prop), gaussianPairLaw]
  have hslope : pairSlope (v : ℝ) (β * v) = β := by
    rw [pairSlope, mul_div_assoc, div_self hv.ne', mul_one]
  have hresid : pairResidVar (v : ℝ) (β ^ 2 * v + s) (β * v) = s := by
    rw [pairResidVar]
    field_simp
    ring
  rw [hslope, hresid, Real.toNNReal_coe]
  congr 1
  funext z
  simp

end Tools

/-! ### The start's main term, on the pair law -/

/-- The start's ballot weight `min((a - u)⁺, C)`. -/
noncomputable def startWeight (a C u : ℝ) : ℝ := min (max (a - u) 0) C

lemma startWeight_nonneg {a C : ℝ} (hC : 0 ≤ C) (u : ℝ) : 0 ≤ startWeight a C u :=
  le_min (le_max_right _ _) hC

lemma startWeight_le {a C : ℝ} (u : ℝ) : startWeight a C u ≤ C := min_le_right _ _

lemma antitone_startWeight (a C : ℝ) : Antitone (startWeight a C) := by
  intro x y hxy
  unfold startWeight
  exact min_le_min_right _ (max_le_max_right _ (by linarith))

lemma measurable_startWeight (a C : ℝ) : Measurable (startWeight a C) := by
  unfold startWeight
  fun_prop

/-- On `[a - C, a]` the weight is `a - u`. -/
lemma startWeight_eq {a C u : ℝ} (h1 : a - C ≤ u) (h2 : u ≤ a) : startWeight a C u = a - u := by
  unfold startWeight
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

/-- Above `a` the weight vanishes. -/
lemma startWeight_eq_zero {a C u : ℝ} (hC : 0 ≤ C) (h : a ≤ u) : startWeight a C u = 0 := by
  unfold startWeight
  rw [max_eq_right (by linarith), min_eq_left hC]

/-! ### The start, blocks `0` and `1` aggregated -/

section Start

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
  {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

omit [IsProbabilityMeasure Q₁] in
/-- A function of the first factor has, under the product, its law under `Q₁`. -/
lemma map_comp_fst_prod {f : Ω₁ → ℝ} (hf : Measurable f) :
    (Q₁.prod Q₂).map (fun ω => f ω.1) = Q₁.map f := by
  have h : (fun ω : Ω₁ × Ω₂ => f ω.1) = f ∘ Prod.fst := rfl
  rw [h, ← Measure.map_map hf measurable_fst, map_fst_prod_eq]

/-- A function of the second factor has, under the product, its law under `Q₂`. -/
lemma map_comp_snd_prod {f : Ω₂ → ℝ} (hf : Measurable f) :
    (Q₁.prod Q₂).map (fun ω => f ω.2) = Q₂.map f := by
  have h : (fun ω : Ω₁ × Ω₂ => f ω.2) = f ∘ Prod.snd := rfl
  rw [h, ← Measure.map_map hf measurable_snd, map_snd_prod_eq]

/-- **One block in law**: `(Z_m, β_m Z_m + W_m) ~ gaussianPairLaw 0 0 v_m (β_m²v_m + s_m) (β_m v_m)`
under the product measure. -/
lemma map_blockPair_eq (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂) (β : ℕ → ℝ)
    {m : ℕ} (hvm : 0 < (v m : ℝ)) :
    (Q₁.prod Q₂).map (fun ω => (Z m ω.1, β m * Z m ω.1 + W m ω.2))
      = gaussianPairLaw 0 0 (v m) (β m ^ 2 * v m + s m) (β m * v m) :=
  map_pair_shear_eq_gaussianPairLaw hvm (β m) ((hZ.measurable m).comp measurable_fst)
    ((hW.measurable m).comp measurable_snd) (indepFun_comp_fst_snd (Z m) (W m))
    (by rw [map_comp_fst_prod (hZ.measurable m), hZ.map_eq m])
    (by rw [map_comp_snd_prod (hW.measurable m), hW.map_eq m])

/-- Cauchy–Schwarz for one sheared block: `(βv)² ≤ v(β²v + s)`. -/
lemma sq_mul_le_blockPair (β : ℝ) (v s : ℝ≥0) :
    (β * v) ^ 2 ≤ (v : ℝ) * (β ^ 2 * v + s) := by
  have := mul_nonneg v.coe_nonneg s.coe_nonneg
  nlinarith

/-- **The start in law**: `(U₂, Y₂) = (Z₀ + Z₁, (β₀Z₀ + W₀) + (β₁Z₁ + W₁))` is the pair law at the
summed parameters (`RMF.gaussianPairLaw_conv`). -/
lemma map_startPair_eq (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂) (β : ℕ → ℝ)
    (hv0 : 0 < (v 0 : ℝ)) (hv1 : 0 < (v 1 : ℝ)) :
    (Q₁.prod Q₂).map (fun ω => (Z 0 ω.1 + Z 1 ω.1,
        (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2)))
      = gaussianPairLaw 0 0 (v 0 + v 1) (β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1))
          (β 0 * v 0 + β 1 * v 1) := by
  set G₀ : Ω₁ × Ω₂ → ℝ × ℝ := fun ω => (Z 0 ω.1, β 0 * Z 0 ω.1 + W 0 ω.2) with hG₀
  set G₁ : Ω₁ × Ω₂ → ℝ × ℝ := fun ω => (Z 1 ω.1, β 1 * Z 1 ω.1 + W 1 ω.2) with hG₁
  have hm : ∀ i, Measurable fun ω : Ω₁ × Ω₂ => (Z i ω.1, β i * Z i ω.1 + W i ω.2) := fun i =>
    ((hZ.measurable i).comp measurable_fst).prodMk ((((hZ.measurable i).comp
      measurable_fst).const_mul _).add ((hW.measurable i).comp measurable_snd))
  have hpair := iIndepFun_pairProd hZ.measurable hW.measurable hZ.indep hW.indep
    (P := Q₁) (Q := Q₂)
  have hind : IndepFun G₀ G₁ (Q₁.prod Q₂) := by
    have h01 := hpair.indepFun (show (0 : ℕ) ≠ 1 by decide)
    exact h01.comp (φ := fun p : ℝ × ℝ => (p.1, β 0 * p.1 + p.2))
      (ψ := fun p : ℝ × ℝ => (p.1, β 1 * p.1 + p.2)) (by fun_prop) (by fun_prop)
  have hfun : (fun ω : Ω₁ × Ω₂ => (Z 0 ω.1 + Z 1 ω.1,
      (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2))) = G₀ + G₁ := by
    funext ω
    simp [hG₀, hG₁]
  rw [hfun, hind.map_add_eq_map_conv_map (hm 0) (hm 1), map_blockPair_eq hZ hW β hv0,
    map_blockPair_eq hZ hW β hv1,
    gaussianPairLaw_conv hv0.le (by positivity) (sq_mul_le_blockPair _ _ _) hv1.le
      (by positivity) (sq_mul_le_blockPair _ _ _), add_zero]

/-- **The start above the ceiling costs little**: on `{Z₀ > a}` the weight at `Z₀ + Z₁` is at most
the weight at `a + Z₁`, and `Z₀ ⊥ Z₁`, so the loss is `P(Z₀ > a)·E[min((-Z₁)⁺, C)]`. -/
lemma integral_indicator_startWeight_le (hZ : IsGaussianWalk Z v Q₁) {a C : ℝ} (hC : 0 ≤ C) :
    ∫ ω, {ω : Ω₁ × Ω₂ | a < Z 0 ω.1}.indicator
        (fun ω => startWeight a C (Z 0 ω.1 + Z 1 ω.1)) ω ∂(Q₁.prod Q₂)
      ≤ (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 C x ∂(gaussianReal 0 (v 1)) := by
  set g₁ : ℝ → ℝ := (Set.Ioi a).indicator (fun _ => (1 : ℝ)) with hg₁
  have hg₁m : Measurable g₁ := measurable_const.indicator measurableSet_Ioi
  have hsw : Measurable (startWeight 0 C) := measurable_startWeight 0 C
  have hpt : ∀ ω : Ω₁ × Ω₂, {ω : Ω₁ × Ω₂ | a < Z 0 ω.1}.indicator
      (fun ω => startWeight a C (Z 0 ω.1 + Z 1 ω.1)) ω
      ≤ g₁ (Z 0 ω.1) * startWeight 0 C (Z 1 ω.1) := by
    intro ω
    by_cases h : a < Z 0 ω.1
    · rw [Set.indicator_of_mem (show ω ∈ {ω : Ω₁ × Ω₂ | a < Z 0 ω.1} from h), hg₁,
        Set.indicator_of_mem (show Z 0 ω.1 ∈ Set.Ioi a from h), one_mul]
      have heq : startWeight 0 C (Z 1 ω.1) = startWeight a C (a + Z 1 ω.1) := by
        unfold startWeight
        ring_nf
      rw [heq]
      exact antitone_startWeight a C (by linarith)
    · rw [Set.indicator_of_notMem (show ω ∉ {ω : Ω₁ × Ω₂ | a < Z 0 ω.1} from h), hg₁,
        Set.indicator_of_notMem (show Z 0 ω.1 ∉ Set.Ioi a from h), zero_mul]
  have hbd1 : ∀ x, |g₁ x| ≤ 1 := fun x => by
    rw [hg₁]
    by_cases hx : x ∈ Set.Ioi a
    · rw [Set.indicator_of_mem hx, abs_one]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      norm_num
  have hbd2 : ∀ a' x, |startWeight a' C x| ≤ C := fun a' x => by
    rw [abs_of_nonneg (startWeight_nonneg hC x)]
    exact startWeight_le x
  have hint1 : Integrable (fun ω : Ω₁ × Ω₂ => {ω : Ω₁ × Ω₂ | a < Z 0 ω.1}.indicator
      (fun ω => startWeight a C (Z 0 ω.1 + Z 1 ω.1)) ω) (Q₁.prod Q₂) := by
    refine Integrable.of_bound (((measurable_startWeight a C).comp
      (((hZ.measurable 0).comp measurable_fst).add ((hZ.measurable 1).comp
        measurable_fst))).indicator (measurableSet_lt measurable_const
          ((hZ.measurable 0).comp measurable_fst))).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ω ∈ {ω : Ω₁ × Ω₂ | a < Z 0 ω.1}
    · rw [Set.indicator_of_mem h]
      exact hbd2 _ _
    · rw [Set.indicator_of_notMem h, abs_zero]
      exact hC
  have hint2 : Integrable (fun ω : Ω₁ × Ω₂ => g₁ (Z 0 ω.1) * startWeight 0 C (Z 1 ω.1))
      (Q₁.prod Q₂) := by
    refine Integrable.of_bound ((hg₁m.comp ((hZ.measurable 0).comp measurable_fst)).mul
      (hsw.comp ((hZ.measurable 1).comp measurable_fst))).aestronglyMeasurable (1 * C)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbd1 _) (hbd2 _ _) (abs_nonneg _) zero_le_one
  have hind : IndepFun (g₁ ∘ Z 0) (startWeight 0 C ∘ Z 1) Q₁ :=
    (hZ.indep.indepFun (show (0 : ℕ) ≠ 1 by decide)).comp hg₁m hsw
  have hmul := hind.integral_fun_mul_eq_mul_integral
    (hg₁m.comp (hZ.measurable 0)).aestronglyMeasurable
    (hsw.comp (hZ.measurable 1)).aestronglyMeasurable
  simp only [Function.comp_apply] at hmul
  have hfst : ∫ ω : Ω₁ × Ω₂, g₁ (Z 0 ω.1) * startWeight 0 C (Z 1 ω.1) ∂(Q₁.prod Q₂)
      = ∫ ω, g₁ (Z 0 ω) * startWeight 0 C (Z 1 ω) ∂Q₁ :=
    integral_comp_fst (f := fun ω => g₁ (Z 0 ω) * startWeight 0 C (Z 1 ω))
      ((hg₁m.comp (hZ.measurable 0)).mul (hsw.comp (hZ.measurable 1))).aestronglyMeasurable
  have hlaw0 : ∫ ω, g₁ (Z 0 ω) ∂Q₁ = (gaussianReal 0 (v 0)).real (Set.Ioi a) := by
    rw [← integral_map (hZ.measurable 0).aemeasurable hg₁m.aestronglyMeasurable, hZ.map_eq 0,
      hg₁, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one]
  have hlaw1 : ∫ ω, startWeight 0 C (Z 1 ω) ∂Q₁
      = ∫ x, startWeight 0 C x ∂(gaussianReal 0 (v 1)) := by
    rw [← integral_map (hZ.measurable 1).aemeasurable hsw.aestronglyMeasurable, hZ.map_eq 1]
  calc _ ≤ ∫ ω : Ω₁ × Ω₂, g₁ (Z 0 ω.1) * startWeight 0 C (Z 1 ω.1) ∂(Q₁.prod Q₂) :=
        integral_mono hint1 hint2 hpt
    _ = _ := by rw [hfst, hmul, hlaw0, hlaw1]

/-- The four Gaussian tails the start pays at weight `C`:
`e^{-(A+B)²/(2v₀)} + e^{-(A+2B)²/(2(v₀+v₁))} + 2e^{-(M₁-|d₀|)²/(2σ₁²)} + e^{-(K₂+d₀+d₁)²/(2S)}`,
`σ₁² = β₀²v₀ + s₀`, `S = σ₁² + β₁²v₁ + s₁`. -/
noncomputable def startTails (v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ A B M₁ K₂ : ℝ) : ℝ :=
  Real.exp (-((A + B) ^ 2 / (2 * v₀))) + Real.exp (-((A + 2 * B) ^ 2 / (2 * (v₀ + v₁))))
    + 2 * Real.exp (-((M₁ - |d₀|) ^ 2 / (2 * (β₀ ^ 2 * v₀ + s₀))))
    + Real.exp (-((K₂ + d₀ + d₁) ^ 2 / (2 * (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁)))))

end Start

/-! ### The window event, split into a start and two suffixes -/

section Assembly

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

omit [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] in
/-- The height walk of the pair family. -/
lemma walk_hp1_fst (Z : ℕ → Ω₁ → ℝ) (W : ℕ → Ω₂ → ℝ) (β d : ℕ → ℝ) (j : ℕ) (ω : Ω₁ × Ω₂) :
    walk (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ).1) j ω
      = walk Z j ω.1 := by
  simp [walk_apply]

omit [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] in
/-- The real walk of the pair family: drift, slope walk and residual walk. -/
lemma walk_hp1_snd (Z : ℕ → Ω₁ → ℝ) (W : ℕ → Ω₂ → ℝ) (β d : ℕ → ℝ) (j : ℕ) (ω : Ω₁ × Ω₂) :
    walk (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ).2) j ω
      = driftSum d j + walk (fun m ω => β m * Z m ω) j ω.1 + walk W j ω.2 := by
  simp [walk_apply, driftSum, Finset.sum_add_distrib]

omit [MeasurableSpace Ω₁] in
/-- A walk at step `2 + i` is its value at `2` plus the shifted walk at `i`. -/
lemma walk_two_add (G : ℕ → Ω₁ → ℝ) (i : ℕ) (ω : Ω₁) :
    walk G (2 + i) ω = (G 0 ω + G 1 ω) + walk (fun m => G (m + 2)) i ω := by
  rw [walk_shift]
  simp [walk_apply, Finset.sum_range_succ]

/-- The drift at step `2 + i` is `d₀ + d₁` plus the shifted drift at `i`. -/
lemma driftSum_two_add (d : ℕ → ℝ) (i : ℕ) :
    driftSum d (2 + i) = d 0 + d 1 + driftSum (fun m => d (m + 2)) i := by
  simp only [driftSum, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by rw [add_comm]

variable {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **The height suffix from a start `u` of the box, linearised.**
`RMF.IsGaussianWalk.le_measure_tube_inter_slope` for the walk from block `2`, the ballot bounded
below by its slope `κ(a - u)` (`RMF.le_ballotLinear_of_mem`), the floor loss by `α e^{-u}`, and the
part `K_r P_R (a - u)` of the slope loss taken off the ballot's slope. -/
theorem ofReal_suffixLow_le (hZ : IsGaussianWalk Z v Q₁) (β : ℕ → ℝ) {n m₀ : ℕ}
    (hm₀ : m₀ + 3 ≤ n) {vmin vmax a A B L Klate σR2 u : ℝ} (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → vmin ≤ (v m : ℝ) ∧ (v m : ℝ) ≤ vmax) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hB : 2 * vmax < B) (hCn : (a + A + 2 * B) ^ 2 ≤ 2 * (((n - 2 : ℕ) : ℝ) * vmin))
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1)))
      ≤ Klate) (hKL : Klate ≤ L)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2), β m ^ 2 * (v m : ℝ) ≤ σR2) (hσR0 : 0 < σR2)
    (hu : u ∈ Set.Icc (-A - 2 * B) a) :
    ENNReal.ofReal ((2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)))
            / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax))
          - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
            * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))) * (a - u)
        - (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
              * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
              / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (-u)
          + √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
            * (√(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
              + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax)))))
      ≤ Q₁ (barrierEvent (fun m => Z (m + 2)) (n - 2) (fun i => -A - B * ((i : ℝ) + 2) - u)
          (fun _ => a - u)
        ∩ {ω₁ | ∀ i ≤ n - 2, walk (fun m ω => β (m + 2) * Z (m + 2) ω) i ω₁ ≤ L}) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hvb 2 le_rfl).1 (hvb 2 le_rfl).2)
  have hB0 : 0 ≤ B := by linarith
  have hv : VarBracket (fun m => v (m + 2)) vmin vmax :=
    ⟨hvmin, fun i => (hvb (i + 2) (by omega)).1, fun i => (hvb (i + 2) (by omega)).2⟩
  have hMenv0 : ∀ i : ℕ, 0 ≤ a + A + B * ((i : ℝ) + 2) := fun i => by
    have : 0 ≤ B * ((i : ℝ) + 2) := mul_nonneg hB0 (by positivity)
    linarith
  have hKsum : ∑ m ∈ Finset.Ico m₀ (n - 2), |β (m + 2)|
      * ((a + A + B * ((m : ℝ) + 2)) + (a + A + B * (((m + 1 : ℕ) : ℝ) + 2))) ≤ Klate := by
    refine le_trans (le_of_eq ?_) hKlate
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show n - 2 - m₀ = n - (m₀ + 2) by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show m₀ + 2 + k = m₀ + k + 2 by omega]
    push_cast
    ring
  have hσsum : ∑ m ∈ Finset.range m₀, β (m + 2) ^ 2 * (v (m + 2) : ℝ) ≤ σR2 := by
    refine le_trans (le_of_eq ?_) hσR
    rw [Finset.sum_Ico_eq_sum_range, show m₀ + 2 - 2 = m₀ by omega]
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm k 2]
  have htube := (hZ.shift 2).le_measure_tube_inter_slope hv (n := n - 2) (m₀ := m₀) (by omega)
    (fun m => β (m + 2)) (lo := fun i => -A - B * ((i : ℝ) + 2) - u)
    (Menv := fun i => a + A + B * ((i : ℝ) + 2)) (z := a - u) (D := A + 2 * B + u) (B := B)
    (L := L) (K := Klate) (σ2 := σR2) (x₀ := u) (by linarith) (by linarith) hB
    (fun i _ => by linarith) hMenv0
    (fun i _ _ => ⟨by linarith, by nlinarith [mul_nonneg hB0 (Nat.cast_nonneg (α := ℝ) i)]⟩)
    (by
      rw [abs_le]
      constructor <;> nlinarith)
    hKsum hKL hσsum hσR0
  refine (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (le_trans ?_ htube)
  -- the three comparisons
  set C := a + A + 2 * B with hCdef
  set c := √(π * vmax / 2) with hcdef
  set N := ((n - 2 : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast (show 1 ≤ n - 2 by omega)
  have hball : 2 * (1 - C ^ 2 / (2 * (N * vmin))) / √(2 * π * (N * vmax)) * (a - u)
      ≤ ballotLinear vmin vmax (n - 2) (a - u) := by
    have h := le_ballotLinear_of_mem (vmax := vmax) hvmin (n := n - 2) (by omega)
      (c := a - u) (bL := a - u) (bU := C) (by linarith) le_rfl (by linarith) hCn
    calc _ = 2 * (a - u) * (1 - C ^ 2 / (2 * (N * vmin))) / √(2 * π * (N * vmax)) := by ring
      _ ≤ _ := h
  have hfloor : floorLossDepth (A + 2 * B + u) B vmin vmax (n - 2) (a - u)
      ≤ Real.exp (-(A + 2 * B)) * (C + c + 2)
          * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
          / (√N * (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (-u) := by
    have hden : 0 ≤ √N * (Real.exp ((B - 2 * vmax) / 2) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _)
        (by have := Real.one_le_exp (show 0 ≤ (B - 2 * vmax) / 2 by linarith); linarith)
    have hM : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
      le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
    unfold floorLossDepth
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ a - u)]
    have he : Real.exp (-(A + 2 * B + u)) = Real.exp (-(A + 2 * B)) * Real.exp (-u) := by
      rw [← Real.exp_add]
      ring_nf
    rw [he, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hden
    have hE : 0 ≤ Real.exp (-(A + 2 * B)) * Real.exp (-u) := by positivity
    calc Real.exp (-(A + 2 * B)) * Real.exp (-u) * (a - u + c + 2)
          * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        ≤ Real.exp (-(A + 2 * B)) * Real.exp (-u) * (C + c + 2)
          * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) := by
          gcongr
          linarith
      _ = _ := by ring
  have hslope : √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
        * ((a - u + c) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
          + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax)))
      = √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
          * (a - u)
        + √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
          * (c * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
            + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax))) := by
    ring
  linarith

/-- `√(c/(n-k)) ≤ √(cn₀/(n₀-k))/√n` for `c ≥ 0`, `k < n₀ ≤ n`. -/
lemma sqrt_div_natSub_le {c : ℝ} (hc : 0 ≤ c) {k n₀ n : ℕ} (hk : k < n₀) (hn : n₀ ≤ n) :
    √(c / ((n - k : ℕ) : ℝ)) ≤ √(c * n₀ / ((n₀ : ℝ) - k)) / √(n : ℝ) := by
  have hnk : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub (by omega)]
  have hk' : (k : ℝ) < n₀ := by exact_mod_cast hk
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < (n₀ : ℝ) - k := by linarith
  have hN : 0 < (n : ℝ) - k := by linarith
  have hn0 : 0 < (n : ℝ) := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [hnk, ← Real.sqrt_div' _ hn0.le]
  refine Real.sqrt_le_sqrt ?_
  rw [div_div, div_le_div_iff₀ hN (by positivity)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg hc hk0, mul_nonneg (mul_nonneg hc hk0) (sub_nonneg.2 hn')]

/-- The ballot slope at horizon `n - 2` is at least its value at `n₀`, over `√n`. -/
lemma ballotSlope_ge {n₀ n : ℕ} (hn₀ : 3 ≤ n₀) (hn : n₀ ≤ n) {vmin vmax C : ℝ}
    (hvmin : 0 < vmin) (hvmax : 0 < vmax) (hC : C ^ 2 ≤ 2 * (((n₀ : ℝ) - 2) * vmin)) :
    2 * (1 - C ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / √(2 * π * vmax) / √(n : ℝ)
      ≤ 2 * (1 - C ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)))
          / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) := by
  have hN : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < ((n₀ : ℝ) - 2) * vmin := by nlinarith
  have hN1 : ((n₀ : ℝ) - 2) * vmin ≤ ((n - 2 : ℕ) : ℝ) * vmin := by
    rw [hN]
    nlinarith
  have h1 : 0 ≤ 1 - C ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hC
  have h2 : 1 - C ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))
      ≤ 1 - C ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)) := by
    have := div_le_div_of_nonneg_left (sq_nonneg C) (by positivity : 0 < 2 * (((n₀ : ℝ) - 2)
      * vmin)) (by linarith : 2 * (((n₀ : ℝ) - 2) * vmin) ≤ 2 * (((n - 2 : ℕ) : ℝ) * vmin))
    linarith
  have hsq : √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) ≤ √(2 * π * vmax) * √(n : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [hN]
    nlinarith [Real.pi_pos]
  have hpos : 0 < √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) := by
    refine Real.sqrt_pos.2 ?_
    rw [hN]
    have : (1 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    positivity
  rw [div_div]
  calc 2 * (1 - C ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / (√(2 * π * vmax) * √(n : ℝ))
      ≤ 2 * (1 - C ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)))
          / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hsq
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hpos.le

/-- `E[e^{-U₂}] = e^{(v₀+v₁)/2}` for the start's height `U₂ = Z₀ + Z₁`, with integrability. -/
lemma integral_exp_neg_start (hZ : IsGaussianWalk Z v Q₁) :
    Integrable (fun ω : Ω₁ × Ω₂ => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) (Q₁.prod Q₂)
      ∧ ∫ ω, Real.exp (-(Z 0 ω.1 + Z 1 ω.1)) ∂(Q₁.prod Q₂)
        = Real.exp (((v 0 : ℝ) + v 1) / 2) := by
  have hU : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 + Z 1 ω.1 :=
    ((hZ.measurable 0).comp measurable_fst).add ((hZ.measurable 1).comp measurable_fst)
  have hwalk : (fun ω₁ => Z 0 ω₁ + Z 1 ω₁) = walk Z 2 := by
    funext ω₁
    simp [walk_apply, Finset.sum_range_succ]
  have hlaw : (Q₁.prod Q₂).map (fun ω => Z 0 ω.1 + Z 1 ω.1) = gaussianReal 0 (v 0 + v 1) := by
    have h := map_comp_fst_prod (Q₁ := Q₁) (Q₂ := Q₂) (f := fun ω₁ => Z 0 ω₁ + Z 1 ω₁)
      ((hZ.measurable 0).add (hZ.measurable 1))
    rw [h, hwalk, hZ.map_walk 2]
    simp [Finset.sum_range_succ]
  have hint : Integrable (fun ω : Ω₁ × Ω₂ => Real.exp (-1 * (Z 0 ω.1 + Z 1 ω.1)))
      (Q₁.prod Q₂) := by
    have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v 0 + v 1) (-1)
    rw [← hlaw] at h1
    exact (integrable_map_measure (by fun_prop) hU.aemeasurable).1 h1
  have hmgf := mgf_gaussianReal hlaw (-1)
  refine ⟨hint.congr (Filter.Eventually.of_forall fun ω => by simp), ?_⟩
  have e : ∫ ω, Real.exp (-(Z 0 ω.1 + Z 1 ω.1)) ∂(Q₁.prod Q₂)
      = mgf (fun ω => Z 0 ω.1 + Z 1 ω.1) (Q₁.prod Q₂) (-1) := by
    rw [mgf]
    congr 1
    funext ω
    ring_nf
  rw [e, hmgf]
  push_cast
  congr 1
  ring

/-! ### The losses and the slope of the window's lower bound -/

/-- The additive losses of `RMF.hp1LowerBoundV2` and `RMF.hp1LowerBoundShort`, `√n` removed: the
floor loss `√(n₀/(n₀-2))e^{-(A+2B)}(C + c + 2)M/(e^{(B-2v₊)/2} - 1)·e^{V/2}`, `c = √(πv₊/2)`,
`M = max(√(4/(πv₋)), √(2/(e(B-2v₊))))`, and the slope loss `K_r(cP_R + √(P_R m₀v₊))`,
`K_r = √(2n₀/(π(n₀-2-m₀)v₋))`, `P_R = e^{-(L-K)²/(2σ²)}`. -/
noncomputable def hp1Loss (n₀ m₀ : ℕ) (vmin vmax V a A B L Klate σR2 : ℝ) : ℝ :=
  √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
      * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        / (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (V / 2)
    + √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
      * (√(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
        + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax)))

/-- The ballot slope of `RMF.hp1LowerBoundV2`, the slope loss's linear part removed:
`max(0, 2(1 - C²/(2(n₀-2)v₋))/√(2πv₊) - K_r P_R)`, `C = a + A + 2B`. -/
noncomputable def hp1Slope (n₀ m₀ : ℕ) (vmin vmax a A B L Klate σR2 : ℝ) : ℝ :=
  max (2 * (1 - (a + A + 2 * B) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))) / √(2 * π * vmax)
    - √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))))
    0

/-- `RMF.hp1Loss` is nonnegative. -/
lemma hp1Loss_nonneg {n₀ m₀ : ℕ} {vmin vmax V a A B L Klate σR2 : ℝ}
    (hC : 0 ≤ a + A + 2 * B) (hB : 2 * vmax ≤ B) :
    0 ≤ hp1Loss n₀ m₀ vmin vmax V a A B L Klate σR2 := by
  have hE : 0 ≤ Real.exp ((B - 2 * vmax) / 2) - 1 := by
    have := Real.one_le_exp (show 0 ≤ (B - 2 * vmax) / 2 by linarith)
    linarith
  have hM : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hc : 0 ≤ √(π * vmax / 2) := Real.sqrt_nonneg _
  unfold hp1Loss
  refine add_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (by linarith)) hM) hE)) (Real.exp_pos _).le)
    (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hc
      (Real.exp_pos _).le) (Real.sqrt_nonneg _)))

/-- The final comparison of `RMF.le_measure_windowEvent_gaussian_v2`, as real arithmetic. -/
lemma hp1_final_arith {WL Wr J κ κ₀ X Y Y₀ sn P : ℝ} (hWr : max WL 0 ≤ Wr)
    (hJ : 0 ≤ κ → κ * X - Y ≤ J) (hκ : 0 < κ₀ → κ₀ / sn ≤ κ) (hY : Y ≤ Y₀ / sn)
    (hκ₀ : 0 ≤ κ₀) (hY₀ : 0 ≤ Y₀) (hsn : 0 < sn) (hP : max J 0 * Wr ≤ P) (hP0 : 0 ≤ P) :
    max WL 0 * (κ₀ * X - Y₀) / sn ≤ P := by
  have hW0 : 0 ≤ max WL 0 := le_max_right _ _
  rcases le_or_gt (κ₀ * X - Y₀) 0 with hneg | hpos
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hW0 hneg)
      hsn.le) hP0
  · have hκX : 0 < κ₀ * X := by linarith
    have hκ₀' : 0 < κ₀ := by
      rcases eq_or_lt_of_le hκ₀ with h | h
      · rw [← h, zero_mul] at hκX
        exact absurd hκX (lt_irrefl 0)
      · exact h
    have hX0 : 0 < X := pos_of_mul_pos_right hκX hκ₀
    have hκ' := hκ hκ₀'
    have hκ0 : 0 ≤ κ := le_trans (div_nonneg hκ₀ hsn.le) hκ'
    have h1 : κ₀ / sn * X ≤ κ * X := mul_le_mul_of_nonneg_right hκ' hX0.le
    have hJ' : (κ₀ * X - Y₀) / sn ≤ max J 0 := by
      refine le_trans ?_ (le_max_left _ _)
      have e : (κ₀ * X - Y₀) / sn = κ₀ / sn * X - Y₀ / sn := by ring
      rw [e]
      linarith [hJ hκ0]
    have hq0 : 0 ≤ (κ₀ * X - Y₀) / sn := div_nonneg hpos.le hsn.le
    calc max WL 0 * (κ₀ * X - Y₀) / sn = max WL 0 * ((κ₀ * X - Y₀) / sn) := by ring
      _ ≤ Wr * max J 0 := mul_le_mul hWr hJ' hq0 (le_trans hW0 hWr)
      _ = max J 0 * Wr := mul_comm _ _
      _ ≤ P := hP

/-- `√(2/(π(n-2-m₀)v₋)) ≤ √(2n₀/(π(n₀-2-m₀)v₋))/√n` for `m₀ + 3 ≤ n₀ ≤ n`. -/
lemma sqrt_slopeLoss_le {n₀ m₀ n : ℕ} (hn₀ : m₀ + 3 ≤ n₀) (hn : n₀ ≤ n) {vmin : ℝ}
    (hvmin : 0 < vmin) :
    √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
      ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) / √(n : ℝ) := by
  have h1 := sqrt_div_natSub_le (c := 2 / (π * vmin))
    (div_nonneg zero_le_two (mul_nonneg Real.pi_pos.le hvmin.le)) (k := 2 + m₀)
    (n₀ := n₀) (n := n) (by omega) hn
  have e1 : 2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))
      = 2 / (π * vmin) / ((n - (2 + m₀) : ℕ) : ℝ) := by
    rw [show n - 2 - m₀ = n - (2 + m₀) by omega, div_div]
    ring
  have e2 : 2 / (π * vmin) * n₀ / ((n₀ : ℝ) - ((2 + m₀ : ℕ) : ℝ))
      = 2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)) := by
    push_cast
    rw [div_mul_eq_mul_div, div_div, show (n₀ : ℝ) - (2 + m₀) = (n₀ : ℝ) - 2 - m₀ by ring]
    congr 1
    ring
  rw [← e1, e2] at h1
  exact h1

end Assembly

end RMF
