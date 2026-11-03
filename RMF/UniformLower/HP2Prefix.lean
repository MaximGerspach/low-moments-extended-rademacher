/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Cert.Window
import RMF.UniformLower.WindowBlockDataDecay
import RMF.Probability.SlabBallot
import RMF.Probability.RademacherComparisonGeneric
import RMF.Probability.HarperChainSlack

/-!
# HP2's prefix: one walk with the weight `e^{2Z}A²`

After AM–GM on the products, a pair's prefix term is one walk under its own one-point tilt at
`s_h`, `E[1_{H^{pre}}‖F^{pre}(s_h)‖⁴A²] = E‖F^{pre}‖²·e^{2Mean_M}·E'_h[1_{H^{pre}}e^{2Z_M}A(Z_M)²]`,
with `Z_M = RMF.windowZ` the height walk centred at its tilted means, `H^{pre} = RMF.hp2Tube` the
tube of `RMF.hp1Tube` over the first `M` blocks, and `A(z) = max(b - z, 0) + c`, `b ≤ a + ρ`.  The
prefix term is bounded from `k ≥ 20` in `RMF/UniformLower/HP2PrefixBound.lean`; this file has its
ingredients.

* **The exact slab** (`RMF.IsGaussianWalk.measureReal_survive_slab_le_third`): a centred Gaussian
  walk below `y ≥ 0` ending in `[y - d - w, y - d]` has probability at most
  `(y + c)(d + w + c)w·2/(π√(2πS₁S₂S₃))`.
* **The weight below the ceiling**: at most `e^{2(t+c-1)}` (`RMF.exp_mul_sq_le_of_le`).
* **One slab, by the comparison**: a tube with its endpoint in a slab is a barrier event
  (`RMF.barrierEvent_inter_slab_subset`), and on the Gaussian side the floor is dropped
  (`RMF.walk_slab_of_mem_barrierEvent`).
* **The mass factor** (`RMF.exp_two_mul_sum_windowMeanH_div_prod_le`):
  `e^{2Mean_M}/∏_{pre}(1 + p^{-1-2σ}) ≤ exp(∑_{m<M}(S_m + C_m(2h)) + 5·10⁻²⁰)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

section ExactSlab

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **The exact slab, by time reversal.**  For a Gaussian walk with its endpoint in the slab
`[x - d - w, x - d]`: the reversed last block stays below `d + w`, and the middle increment lands
in a window of width `w`:
`P(S_j ≤ x ∀ j ≤ M, S_M ∈ [x - d - w, x - d])
  ≤ P(S_j ≤ x ∀ j ≤ M')·P(S_{M-i} - S_M ≤ d + w ∀ i ≤ K)·w/√(2π∑_{M' ≤ i < M-K} v_i)`. -/
theorem IsGaussianWalk.measure_survive_slab_le_sum (h : IsGaussianWalk G v μ) (x d w : ℝ)
    {M' K M : ℕ} (hMK : M' + K < M) (hv : ∀ i ∈ Finset.Ico M' (M - K), v i ≠ 0) :
    μ {ω | (∀ j ≤ M, walk G j ω ≤ x) ∧ x - d - w ≤ walk G M ω ∧ walk G M ω ≤ x - d}
      ≤ μ {ω | ∀ j ≤ M', walk G j ω ≤ x}
        * μ {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w}
        * ENNReal.ofReal (w / √(2 * π * ∑ i ∈ Finset.Ico M' (M - K), (v i : ℝ))) := by
  classical
  set S : Finset ℕ := Finset.range M' ∪ Finset.Ico (M - K) M with hSdef
  set T : Finset ℕ := Finset.Ico M' (M - K) with hTdef
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [hSdef, hTdef, Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at ha hb
    omega
  have hind0 := h.indep.indepFun_finset S T hST h.measurable
  -- the prefix and last-block paths, and the middle increment
  set φ : (S → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) := fun y =>
    (prefixSums M' fun i => y ⟨i, Finset.mem_union_left _ i.2⟩,
      blockSums (M - K) M fun i => y ⟨i, Finset.mem_union_right _ i.2⟩) with hφdef
  set ψ : (T → ℝ) → ℝ := fun z => blockSums M' (M - K) z (M - K) with hψdef
  have hφ : Measurable φ :=
    ((RMF.measurable_prefixSums M').comp
      (measurable_pi_lambda _ fun i => measurable_pi_apply _)).prodMk
      ((measurable_blockSums (M - K) M).comp
        (measurable_pi_lambda _ fun i => measurable_pi_apply _))
  have hψ : Measurable ψ := (measurable_pi_apply (M - K)).comp (measurable_blockSums M' (M - K))
  set X : Ω → (ℕ → ℝ) × (ℕ → ℝ) := fun ω =>
    (prefixSums M' fun i => G i ω, blockSums (M - K) M fun i => G i ω) with hXdef
  set Mid : Ω → ℝ := fun ω => walk G (M - K) ω - walk G M' ω with hMiddef
  have hXφ : X = φ ∘ fun ω (i : S) => G i ω := rfl
  have hMidψ : Mid = ψ ∘ fun ω (i : T) => G i ω := by
    funext ω
    simp only [hMiddef, hψdef, Function.comp_apply]
    exact (blockSums_comp G (by omega) le_rfl ω).symm
  have hind : IndepFun X Mid μ := by
    rw [hXφ, hMidψ]
    exact hind0.comp hφ hψ
  have hXm : Measurable X := by
    rw [hXφ]
    exact hφ.comp (measurable_pi_lambda _ fun i => h.measurable i)
  have hMidm : Measurable Mid := (h.measurable_walk _).sub (h.measurable_walk _)
  -- the middle variance, summed
  set W : ℝ≥0 := ∑ m ∈ Finset.Ico M' (M - K), v m with hWdef
  have hMmem : M' ∈ Finset.Ico M' (M - K) := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  have hWne : W ≠ 0 := fun h0 =>
    hv M' hMmem ((Finset.sum_eq_zero_iff.1 h0) M' hMmem)
  have hWR : ((W : ℝ≥0) : ℝ) = ∑ i ∈ Finset.Ico M' (M - K), (v i : ℝ) := by
    rw [hWdef, NNReal.coe_sum]
  have hlaw : μ.map Mid = gaussianReal 0 W := h.map_walk_sub (by omega)
  -- the sets
  set S₁ : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {p | (∀ j ≤ M', p.1 j ≤ x) ∧ ∀ i ≤ K, p.2 (M - i) - p.2 M ≤ d + w} with hS₁def
  have hS₁m : MeasurableSet S₁ := by
    have h2 : MeasurableSet
        {p : (ℕ → ℝ) × (ℕ → ℝ) | ∀ i ≤ K, p.2 (M - i) - p.2 M ≤ d + w} := by
      have : {p : (ℕ → ℝ) × (ℕ → ℝ) | ∀ i ≤ K, p.2 (M - i) - p.2 M ≤ d + w}
          = ⋂ i ∈ Set.Iic K, {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 (M - i) - p.2 M ≤ d + w} := by
        ext p
        simp
      rw [this]
      exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
        measurableSet_le (by fun_prop) measurable_const
    exact (measurable_fst (measurableSet_forall_le_pi (fun _ => x) M')).inter h2
  set ζ : (ℕ → ℝ) × (ℕ → ℝ) → ℝ := fun p => x - d - p.1 M' - p.2 M with hζdef
  have hζ : Measurable ζ :=
    (measurable_const.sub ((measurable_pi_apply _).comp measurable_fst)).sub
      ((measurable_pi_apply _).comp measurable_snd)
  have hXpre : ∀ ω j, j ≤ M' → (X ω).1 j = walk G j ω := fun ω j hj => prefixSums_comp G hj ω
  have hXlast : ∀ ω j, M - K ≤ j → j ≤ M → (X ω).2 j = walk G j ω - walk G (M - K) ω :=
    fun ω j h1 h2 => blockSums_comp G h1 h2 ω
  have hsub : {ω | (∀ j ≤ M, walk G j ω ≤ x) ∧ x - d - w ≤ walk G M ω ∧ walk G M ω ≤ x - d}
      ⊆ X ⁻¹' S₁ ∩ {ω | Mid ω ∈ Set.Icc (ζ (X ω) - w) (ζ (X ω))} := by
    rintro ω ⟨hsurv, hlo, hhi⟩
    have hXM : (X ω).2 M = walk G M ω - walk G (M - K) ω := hXlast ω M (by omega) le_rfl
    have hXM' : (X ω).1 M' = walk G M' ω := hXpre ω M' le_rfl
    refine ⟨⟨fun j hj => ?_, fun i hi => ?_⟩, ?_, ?_⟩
    · rw [hXpre ω j hj]
      exact hsurv j (by omega)
    · rw [hXlast ω (M - i) (by omega) (by omega), hXM]
      have := hsurv (M - i) (by omega)
      linarith
    · simp only [hζdef, hXM', hXM, hMiddef]
      linarith
    · simp only [hζdef, hXM', hXM, hMiddef]
      linarith
  have hwin := measure_inter_mem_Icc_le hWne hXm hMidm hS₁m hζ hind hlaw w
  -- the prefix and the reversed last block are independent
  have hsplit : μ (X ⁻¹' S₁) = μ {ω | ∀ j ≤ M', walk G j ω ≤ x}
      * μ {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w} := by
    have hdisj : Disjoint (Finset.range M') (Finset.Ico (M - K) M) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
      omega
    have hind2 : IndepFun (fun ω => prefixSums M' fun i => G i ω)
        (fun ω => blockSums (M - K) M fun i => G i ω) μ :=
      (h.indep.indepFun_finset _ _ hdisj h.measurable).comp
        (RMF.measurable_prefixSums M') (measurable_blockSums (M - K) M)
    have hpre : X ⁻¹' S₁
        = (fun ω => prefixSums M' fun i => G i ω) ⁻¹' {f : ℕ → ℝ | ∀ j ≤ M', f j ≤ x}
          ∩ (fun ω => blockSums (M - K) M fun i => G i ω)
            ⁻¹' {b : ℕ → ℝ | ∀ i ≤ K, b (M - i) - b M ≤ d + w} := rfl
    have hbm : MeasurableSet {b : ℕ → ℝ | ∀ i ≤ K, b (M - i) - b M ≤ d + w} := by
      have : {b : ℕ → ℝ | ∀ i ≤ K, b (M - i) - b M ≤ d + w}
          = ⋂ i ∈ Set.Iic K, {b : ℕ → ℝ | b (M - i) - b M ≤ d + w} := by
        ext b
        simp
      rw [this]
      exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
        measurableSet_le (by fun_prop) measurable_const
    rw [hpre, hind2.measure_inter_preimage_eq_mul _ _
      (measurableSet_forall_le_pi (fun _ => x) M') hbm]
    congr 1
    · congr 1
      exact (survivalSet_eq_preimage G (fun _ => x) M').symm
    · congr 1
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      refine forall_congr' fun i => forall_congr' fun hi => ?_
      rw [blockSums_comp G (by omega) (by omega) ω, blockSums_comp G (by omega) le_rfl ω,
        walk_reverse G (by omega : i ≤ M) ω]
      constructor <;> intro hh <;> linarith
  calc μ {ω | (∀ j ≤ M, walk G j ω ≤ x) ∧ x - d - w ≤ walk G M ω ∧ walk G M ω ≤ x - d}
      ≤ μ (X ⁻¹' S₁ ∩ {ω | Mid ω ∈ Set.Icc (ζ (X ω) - w) (ζ (X ω))}) := measure_mono hsub
    _ ≤ μ (X ⁻¹' S₁) * ENNReal.ofReal (w / √(2 * π * W)) := hwin
    _ = _ := by rw [hsplit, hWR]

/-- **The exact slab ballot with summed variances.**  For `v_i ≠ 0` and `c ≥ √(πv_i/2)` on the
steps `i < M`, a ceiling `y ≥ 0`, `w ≥ 0`, `d + w ≥ 0` and a split `1 ≤ M'`, `1 ≤ K`, `M' + K < M`:
`P(S_j ≤ y ∀ j ≤ M, S_M ∈ [y - d - w, y - d])
  ≤ (y + c)√(2/(πS₁))·(d + w + c)√(2/(πS₃))·w/√(2πS₂)` with `S₁, S₂, S₃` the variance sums over
`[0, M')`, `[M', M - K)`, `[M - K, M)`: the prefix at the ceiling `y`, the reversed last block
below `d + w`, the middle in a window of width `w`. -/
theorem IsGaussianWalk.measureReal_survive_slab_le_sqrt (h : IsGaussianWalk G v μ) {M' K M : ℕ}
    (hv : ∀ i, i < M → v i ≠ 0) {c : ℝ} (hc0 : 0 < c) (hc : ∀ i, i < M → √(π * v i / 2) ≤ c)
    {y d w : ℝ} (hy : 0 ≤ y) (hdw : 0 ≤ d + w) (hw : 0 ≤ w) (hM' : 1 ≤ M') (hK : 1 ≤ K)
    (hMK : M' + K < M) :
    μ.real {ω | (∀ j ≤ M, walk G j ω ≤ y) ∧ y - d - w ≤ walk G M ω ∧ walk G M ω ≤ y - d}
      ≤ (y + c) * √(2 / (π * ∑ i ∈ Finset.range M', (v i : ℝ)))
        * ((d + w + c) * √(2 / (π * ∑ i ∈ Finset.Ico (M - K) M, (v i : ℝ))))
        * (w / √(2 * π * ∑ i ∈ Finset.Ico M' (M - K), (v i : ℝ))) := by
  have htwin := h.measure_survive_slab_le_sum y d w hMK fun i hi =>
    hv i (by have := (Finset.mem_Ico.1 hi).2; omega)
  -- the prefix, at the ceiling `y`
  have hpre : μ.real {ω | ∀ j ≤ M', walk G j ω ≤ y}
      ≤ (y + c) * √(2 / (π * ∑ i ∈ Finset.range M', (v i : ℝ))) :=
    h.measureReal_survival_le_sqrt_of_lt (g := fun _ => y) hy hM' (fun _ _ => le_rfl)
      (fun i hi => hv i (by omega)) hc0 (fun i hi => hc i (by omega))
  -- the reversed last block, below `d + w`
  have hlast : μ.real {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w}
      ≤ (d + w + c) * √(2 / (π * ∑ i ∈ Finset.Ico (M - K) M, (v i : ℝ))) := by
    have h1 := (h.reverse M).measureReal_survival_le_sqrt_of_lt (g := fun _ => d + w) hdw hK
      (fun _ _ => le_rfl) (fun i hi => hv (revIdx M i) (revIdx_lt (by omega) hi)) hc0
      (fun i hi => hc (revIdx M i) (revIdx_lt (by omega) hi))
    have hrev : ∑ i ∈ Finset.range K, (v (revIdx M i) : ℝ)
        = ∑ i ∈ Finset.Ico (M - K) M, (v i : ℝ) :=
      sum_range_revIdx (fun i => (v i : ℝ)) (by omega)
    calc μ.real {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w}
        ≤ (d + w + c) * √(2 / (π * ∑ i ∈ Finset.range K, (v (revIdx M i) : ℝ))) := h1
      _ = _ := by rw [hrev]
  -- back to `ℝ`
  set δ : ℝ := w / √(2 * π * ∑ i ∈ Finset.Ico M' (M - K), (v i : ℝ)) with hδdef
  have hδ : 0 ≤ δ := div_nonneg hw (Real.sqrt_nonneg _)
  have hfin : μ {ω | ∀ j ≤ M', walk G j ω ≤ y}
      * μ {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w} * ENNReal.ofReal δ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      ENNReal.ofReal_ne_top
  have hreal : μ.real {ω | (∀ j ≤ M, walk G j ω ≤ y) ∧ y - d - w ≤ walk G M ω ∧ walk G M ω ≤ y - d}
      ≤ μ.real {ω | ∀ j ≤ M', walk G j ω ≤ y}
        * μ.real {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w} * δ := by
    have h1 := ENNReal.toReal_mono hfin htwin
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ] at h1
  have hpre0 : 0 ≤ (y + c) * √(2 / (π * ∑ i ∈ Finset.range M', (v i : ℝ))) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  calc μ.real {ω | (∀ j ≤ M, walk G j ω ≤ y) ∧ y - d - w ≤ walk G M ω ∧ walk G M ω ≤ y - d}
      ≤ μ.real {ω | ∀ j ≤ M', walk G j ω ≤ y}
        * μ.real {ω | ∀ i ≤ K, walk (fun m => -G (revIdx M m)) i ω ≤ d + w} * δ := hreal
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hpre hlast measureReal_nonneg hpre0) hδ

/-- **The exact slab ballot at the split `M' = K = ⌊M/3⌋`.**  For `M ≥ 3`, `v_i ≠ 0` and
`c ≥ √(πv_i/2)` on the steps `i < M`, `y ≥ 0`, `w ≥ 0`, `d + w ≥ 0` and lower bounds
`0 < S₁, S₂, S₃` on the variance sums over `[0, ⌊M/3⌋)`, `[⌊M/3⌋, M - ⌊M/3⌋)`, `[M - ⌊M/3⌋, M)`:
`P(S_j ≤ y ∀ j ≤ M, S_M ∈ [y - d - w, y - d]) ≤ (y + c)(d + w + c)w·2/(π√(2πS₁S₂S₃))`. -/
theorem IsGaussianWalk.measureReal_survive_slab_le_third (h : IsGaussianWalk G v μ) {M : ℕ}
    (hv : ∀ i, i < M → v i ≠ 0) {c : ℝ} (hc0 : 0 < c) (hc : ∀ i, i < M → √(π * v i / 2) ≤ c)
    {y d w : ℝ} (hy : 0 ≤ y) (hdw : 0 ≤ d + w) (hw : 0 ≤ w) (hM : 3 ≤ M) {S₁ S₂ S₃ : ℝ}
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hS₃ : 0 < S₃)
    (h₁ : S₁ ≤ ∑ i ∈ Finset.range (M / 3), (v i : ℝ))
    (h₂ : S₂ ≤ ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), (v i : ℝ))
    (h₃ : S₃ ≤ ∑ i ∈ Finset.Ico (M - M / 3) M, (v i : ℝ)) :
    μ.real {ω | (∀ j ≤ M, walk G j ω ≤ y) ∧ y - d - w ≤ walk G M ω ∧ walk G M ω ≤ y - d}
      ≤ (y + c) * (d + w + c) * w * (2 / (π * √(2 * π * (S₁ * S₂ * S₃)))) := by
  have hπ := Real.pi_pos
  have hmain := h.measureReal_survive_slab_le_sqrt (M' := M / 3) (K := M / 3) hv hc0 hc hy hdw
    hw (by omega) (by omega) (by omega)
  have hq₁ : √(2 / (π * ∑ i ∈ Finset.range (M / 3), (v i : ℝ))) ≤ √(2 / (π * S₁)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left h₁ hπ.le))
  have hq₃ : √(2 / (π * ∑ i ∈ Finset.Ico (M - M / 3) M, (v i : ℝ))) ≤ √(2 / (π * S₃)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left h₃ hπ.le))
  have hq₂ : w / √(2 * π * ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), (v i : ℝ))
      ≤ w / √(2 * π * S₂) :=
    div_le_div_of_nonneg_left hw (by positivity)
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h₂ (by positivity)))
  have hyc : 0 ≤ y + c := by linarith
  have hdc : 0 ≤ d + w + c := by linarith
  calc μ.real {ω | (∀ j ≤ M, walk G j ω ≤ y) ∧ y - d - w ≤ walk G M ω ∧ walk G M ω ≤ y - d}
      ≤ (y + c) * √(2 / (π * ∑ i ∈ Finset.range (M / 3), (v i : ℝ)))
        * ((d + w + c) * √(2 / (π * ∑ i ∈ Finset.Ico (M - M / 3) M, (v i : ℝ))))
        * (w / √(2 * π * ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), (v i : ℝ))) := hmain
    _ ≤ (y + c) * √(2 / (π * S₁)) * ((d + w + c) * √(2 / (π * S₃))) * (w / √(2 * π * S₂)) := by
        gcongr
    _ = (y + c) * (d + w + c) * w * (√(2 / (π * S₁)) * √(2 / (π * S₃)) / √(2 * π * S₂)) := by
        ring
    _ = (y + c) * (d + w + c) * w * (2 / (π * √(2 * π * (S₁ * S₂ * S₃)))) := by
        rw [sqrt_slab_eq hS₁ hS₂ hS₃]

end ExactSlab

/-! ### The sums over the exact slabs -/

/-- The binomial coefficient `C(n+1,1) = n + 1` in `ℝ`. -/
lemma cast_choose_one_add (n : ℕ) : (((n + 1).choose 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
  rw [Nat.choose_one_right]
  push_cast
  ring

/-- `∑_ℓ x^ℓ(ℓ + b)³ = 6/(1 - x)⁴ + 6(b - 2)/(1 - x)³ + (3b² - 9b + 7)/(1 - x)² + (b - 1)³/(1 - x)`
for `0 ≤ x < 1`. -/
lemma hasSum_geom_mul_add_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (b : ℝ) :
    HasSum (fun ℓ : ℕ => x ^ ℓ * ((ℓ : ℝ) + b) ^ 3)
      (6 / (1 - x) ^ 4 + 6 * (b - 2) / (1 - x) ^ 3 + (3 * b ^ 2 - 9 * b + 7) / (1 - x) ^ 2
        + (b - 1) ^ 3 / (1 - x)) := by
  have hx : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h0 := hasSum_choose_mul_geometric_of_norm_lt_one 0 hx
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hx
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hx
  have h3 := hasSum_choose_mul_geometric_of_norm_lt_one 3 hx
  rw [show 6 / (1 - x) ^ 4 + 6 * (b - 2) / (1 - x) ^ 3 + (3 * b ^ 2 - 9 * b + 7) / (1 - x) ^ 2
        + (b - 1) ^ 3 / (1 - x)
      = 6 * (1 / (1 - x) ^ (3 + 1)) + 6 * (b - 2) * (1 / (1 - x) ^ (2 + 1))
        + (3 * b ^ 2 - 9 * b + 7) * (1 / (1 - x) ^ (1 + 1))
        + (b - 1) ^ 3 * (1 / (1 - x) ^ (0 + 1)) by ring]
  refine ((((h3.mul_left 6).add (h2.mul_left (6 * (b - 2)))).add
    (h1.mul_left (3 * b ^ 2 - 9 * b + 7))).add (h0.mul_left ((b - 1) ^ 3))).congr_fun
    fun ℓ => ?_
  have e1 := cast_choose_one_add ℓ
  obtain ⟨e2, e3, -⟩ := cast_choose_slab ℓ
  simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one]
  linear_combination 2 * x ^ ℓ * e3 - ((ℓ : ℝ) + 3 * b - 3) * x ^ ℓ * e2
    - (3 * b ^ 2 - 9 * b + 7) * x ^ ℓ * e1

/-! ### The weight below the ceiling -/

section Slabs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `e^{2z}(max(b - z, 0) + c)² ≤ e^{2(t + c - 1)}` for `z ≤ t`, `b ≤ t`, `c ≥ 0`: with
`u = t + c - z ≥ 0` the weight is at most `e^{2z}u²`, and `u ≤ e^{u-1}`. -/
lemma exp_mul_sq_le_of_le {z t b c : ℝ} (hz : z ≤ t) (hb : b ≤ t) (hc : 0 ≤ c) :
    Real.exp (2 * z) * (max (b - z) 0 + c) ^ 2 ≤ Real.exp (2 * (t + c - 1)) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t + c - z := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hm0 : 0 ≤ max (b - z) 0 + c := add_nonneg (le_max_right _ _) hc
  have hm : max (b - z) 0 + c ≤ u := by
    have : max (b - z) 0 ≤ t - z := max_le (by linarith) (by linarith)
    rw [hu]
    linarith
  have hexp : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have hsq : u ^ 2 ≤ Real.exp (u - 1) ^ 2 := pow_le_pow_left₀ hu0 hexp 2
  have he0 : 0 ≤ Real.exp (2 * z) := (Real.exp_pos _).le
  calc Real.exp (2 * z) * (max (b - z) 0 + c) ^ 2 ≤ Real.exp (2 * z) * u ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hm 2) he0
    _ ≤ Real.exp (2 * z) * Real.exp (u - 1) ^ 2 := mul_le_mul_of_nonneg_left hsq he0
    _ = Real.exp (2 * (t + c - 1)) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, hu]
        ring_nf

/-- **A bounded weight's expectation**: if `0 ≤ f ≤ C` on `T`, then `E[1_T f] ≤ C` under a
probability measure. -/
lemma integral_indicator_le_of_le {P : Measure Ω} [IsProbabilityMeasure P] {T : Set Ω}
    {f : Ω → ℝ} {C : ℝ} (hf0 : ∀ ω ∈ T, 0 ≤ f ω) (hf : ∀ ω ∈ T, f ω ≤ C) (hC : 0 ≤ C) :
    ∫ ω, T.indicator f ω ∂P ≤ C := by
  have hpt : ∀ ω, T.indicator f ω ≤ C := fun ω => by
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω]; exact hf ω hω
    · rw [Set.indicator_of_notMem hω]; exact hC
  calc ∫ ω, T.indicator f ω ∂P ≤ ∫ _, C ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg hf0 ω)
          (integrable_const C) (ae_of_all _ hpt)
    _ = C := by rw [integral_const, probReal_univ, one_smul]

end Slabs

/-! ### The prefix tube -/

section Tube

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The height walk after `M` blocks, centred**: `Z_M = walk_M - Mean_M`, with `Mean_M` the sum of
the tilted means `RMF.windowMeanH` of the blocks `m < M`. -/
noncomputable def windowZ (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k : ℕ) (σ h : ℝ) (M : ℕ) (ω : Ω) :
    ℝ :=
  walk (halfBlock X k σ h) M ω - ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i

/-- **HP2's prefix tube** at `(a, A, B, ρ)`: the height walk over the first `M` blocks in
`[Mean_j - A - Bj - ρ, Mean_j + a + ρ]`, `1 ≤ j ≤ M` (`RMF.hp1Tube` with free parameters). -/
def hp2Tube (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k M : ℕ) (σ h a A B ρ : ℝ) : Set Ω :=
  barrierEvent (halfBlock X k σ h) M
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ)
    (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ)

/-- At HP1's parameters `(a, A, B, ρ) = (3/2, 5/2, 3, 10⁻¹⁵)` the prefix tube over `M` blocks is
`RMF.hp1Tube` over `M` blocks. -/
lemma hp2Tube_hp1 (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k M : ℕ) (σ h : ℝ) :
    hp2Tube X μ y k M σ h (3 / 2) (5 / 2) 3 (1 / 10 ^ 15) = hp1Tube X μ y k M σ h := rfl

/-- **HP1's tube lies in each of its prefix tubes**: `H(k,h)` over `r` blocks is contained in its
restriction to the first `M ≤ r` blocks. -/
lemma hp1Tube_subset_hp2Tube {r M : ℕ} (hM : M ≤ r) (y k : ℕ) (σ h : ℝ) :
    hp1Tube X μ y k r σ h ⊆ hp2Tube X μ y k M σ h (3 / 2) (5 / 2) 3 (1 / 10 ^ 15) :=
  fun _ hω j hj1 hjM => hω j hj1 (le_trans hjM hM)

lemma measurableSet_hp2Tube (hX : IsRademacherPrimeValues X μ) (y k M : ℕ) (σ h a A B ρ : ℝ) :
    MeasurableSet (hp2Tube X μ y k M σ h a A B ρ) :=
  measurableSet_barrierEvent (measurable_halfBlock hX _ _ _) _ _ _

lemma measurable_windowZ (hX : IsRademacherPrimeValues X μ) (y k : ℕ) (σ h : ℝ) (M : ℕ) :
    Measurable (windowZ X μ y k σ h M) :=
  (measurable_walk_of (measurable_halfBlock hX _ _ _) M).sub_const _

/-- **On the tube the centred endpoint is in `[-A - BM - ρ, a + ρ]`** (`M ≥ 1`). -/
lemma windowZ_mem_of_mem_hp2Tube {y k M : ℕ} {σ h a A B ρ : ℝ} (hM : 1 ≤ M) {ω : Ω}
    (hω : ω ∈ hp2Tube X μ y k M σ h a A B ρ) :
    -A - B * M - ρ ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ := by
  have h1 := Set.mem_Icc.1 (hω M hM le_rfl)
  unfold windowZ
  constructor <;> linarith [h1.1, h1.2]

/-- **On the tube the centred endpoint is at most `a + ρ`**, for every `M` (at `M = 0` it is
`0`). -/
lemma windowZ_le_of_mem_hp2Tube {y k M : ℕ} {σ h a A B ρ : ℝ} (ha : 0 ≤ a + ρ) {ω : Ω}
    (hω : ω ∈ hp2Tube X μ y k M σ h a A B ρ) : windowZ X μ y k σ h M ω ≤ a + ρ := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    simp only [windowZ, walk_zero, Pi.zero_apply, Finset.range_zero, Finset.sum_empty, sub_zero]
    exact ha
  · exact (windowZ_mem_of_mem_hp2Tube hpos hω).2

end Tube

/-! ### One slab, by the comparison -/

section SlabEvents

variable {Ω : Type*}

/-- **A tube with its endpoint in a slab is a barrier event** whose last barrier is the slab, the
floor kept as a `max`. -/
lemma barrierEvent_inter_slab_subset {Y : ℕ → Ω → ℝ} {M : ℕ} {u v : ℕ → ℝ} {lo hi : ℝ} :
    barrierEvent Y M u v ∩ {ω | lo ≤ walk Y M ω ∧ walk Y M ω ≤ hi}
      ⊆ barrierEvent Y M (fun j => if j = M then max (u M) lo else u j)
          (fun j => if j = M then hi else v j) := by
  rintro ω ⟨hT, hlo, hhi⟩ j hj1 hjM
  have hTj := Set.mem_Icc.1 (hT j hj1 hjM)
  change walk Y j ω ∈ Set.Icc (if j = M then max (u M) lo else u j) (if j = M then hi else v j)
  by_cases hj : j = M
  · rw [if_pos hj, if_pos hj]
    rw [hj] at hTj ⊢
    exact ⟨max_le hTj.1 hlo, hhi⟩
  · rw [if_neg hj, if_neg hj]
    exact hTj

/-- **The Gaussian side of a slab.**  If `walk N j = walk G j + m_j` for `j ≤ M`, the ceilings
satisfy `v_j ≤ m_j + t`, `v_M = m_M + t - d`, and `u_M ≥ m_M + t - d - w`, then a path in the
barrier event of `N` widened by `s` has its `G`-path below `t + s` on `[0, M]`, ending in
`[t + s - d - (w + 2s), t + s - d]`: the floor is dropped. -/
lemma walk_slab_of_mem_barrierEvent {N G : ℕ → Ω → ℝ} {M : ℕ} {m u v : ℕ → ℝ} {t s d w : ℝ}
    (hM : 1 ≤ M) (hNG : ∀ j, j ≤ M → ∀ ω, walk N j ω = walk G j ω + m j)
    (hv : ∀ j, 1 ≤ j → j ≤ M → v j ≤ m j + t) (hvM : v M = m M + t - d)
    (huM : m M + t - d - w ≤ u M) (hts : 0 ≤ t + s) {ω : Ω}
    (hω : ω ∈ barrierEvent N M (fun j => u j - s) (fun j => v j + s)) :
    (∀ j ≤ M, walk G j ω ≤ t + s) ∧ t + s - d - (w + 2 * s) ≤ walk G M ω
      ∧ walk G M ω ≤ t + s - d := by
  have hMω : u M - s ≤ walk N M ω ∧ walk N M ω ≤ v M + s := Set.mem_Icc.1 (hω M hM le_rfl)
  have hNM := hNG M le_rfl ω
  refine ⟨fun j hj => ?_, by linarith [hMω.1], by linarith [hMω.2]⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    simp only [walk_zero, Pi.zero_apply]
    exact hts
  · have hjω : u j - s ≤ walk N j ω ∧ walk N j ω ≤ v j + s := Set.mem_Icc.1 (hω j hpos hj)
    have h1 := hNG j hj ω
    have h2 := hv j hpos hj
    linarith [hjω.2]

end SlabEvents

/-! ### The weighted prefix term -/

section Weighted

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The weight `1_{tube} e^{2Z_M}(max(b - Z_M, 0) + c)²` is integrable (at most
`e^{2(a + ρ + c - 1)}`, `RMF.exp_mul_sq_le_of_le`), for any finite measure. -/
lemma integrable_indicator_hp2Tube_exp_mul_sq (hX : IsRademacherPrimeValues X μ) {P : Measure Ω}
    [IsFiniteMeasure P] {y k M : ℕ} {σ h a A B ρ b c : ℝ} (haρ : 0 ≤ a + ρ) (hb : b ≤ a + ρ)
    (hc : 0 ≤ c) :
    Integrable (fun ω => (hp2Tube X μ y k M σ h a A B ρ).indicator (fun ω =>
        Real.exp (2 * windowZ X μ y k σ h M ω)
          * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ 2) ω) P := by
  have hZ := measurable_windowZ hX y k σ h M
  have hF : Measurable fun ω => Real.exp (2 * windowZ X μ y k σ h M ω)
      * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ 2 :=
    (Real.measurable_exp.comp (measurable_const.mul hZ)).mul
      ((((measurable_const.sub hZ).max measurable_const).add measurable_const).pow_const 2)
  refine (integrable_const (Real.exp (2 * (a + ρ + c - 1)))).mono'
    (hF.indicator (measurableSet_hp2Tube hX y k M σ h a A B ρ)).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ (hp2Tube X μ y k M σ h a A B ρ).indicator (fun ω =>
      Real.exp (2 * windowZ X μ y k σ h M ω)
        * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ 2) ω :=
    Set.indicator_nonneg (fun ω _ => by positivity) ω
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  by_cases hω : ω ∈ hp2Tube X μ y k M σ h a A B ρ
  · rw [Set.indicator_of_mem hω]
    exact exp_mul_sq_le_of_le (windowZ_le_of_mem_hp2Tube haρ hω) hb hc
  · rw [Set.indicator_of_notMem hω]
    exact (Real.exp_pos _).le

end Weighted

/-! ### The mass factor -/

section Mass

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **One block's mass**: `2μ̃_m - ∑_{p∈B_m} log(1 + p^{-1-2σ}) = S_m + C_m(2h)` within
`3e^{-m}/10²⁰` (`RMF.abs_blockMeanAdd_height_sub_le_decay`; `|log(1 + t) - t| ≤ 2t²`,
`RMF.abs_log_one_add_sub_le`, with `t = p^{-1-2σ} ≤ e^{-m}/10⁴⁰`). -/
lemma abs_two_mul_windowMeanH_sub_log_le (hX : IsRademacherPrimeValues X μ) {y k m : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    |2 * windowMeanH X μ y k σ h m
        - ∑ p ∈ primeBlockSub k m, Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)|
      ≤ 3 * (Real.exp (-(m : ℝ)) / 10 ^ 20) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmk : (20 : ℝ) ≤ (m : ℝ) + k := by
    have : (20 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmean : |windowMeanH X μ y k σ h m
      - (blockRpowSum k σ m + blockCosSum k σ (2 * h) m / 2)|
      ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 :=
    abs_blockMeanAdd_height_sub_le_decay hX y (h := h) hσ hk0 hmk hB
  have hq : (Real.exp (-((m : ℝ) + k)) / 10 ^ 40) ^ 2 ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 := by
    have hx0 : 0 ≤ Real.exp (-((m : ℝ) + k)) / 10 ^ 40 := by positivity
    have hx1 : Real.exp (-((m : ℝ) + k)) / 10 ^ 40 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact le_trans (Real.exp_le_one_iff.2 (by linarith)) (by norm_num)
    have hxm : Real.exp (-((m : ℝ) + k)) / 10 ^ 40 ≤ Real.exp (-(m : ℝ)) / 10 ^ 40 :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (by positivity)
    calc (Real.exp (-((m : ℝ) + k)) / 10 ^ 40) ^ 2
        ≤ Real.exp (-((m : ℝ) + k)) / 10 ^ 40 := by nlinarith
      _ ≤ _ := hxm
  have hlog : |∑ p ∈ primeBlockSub k m, Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      - blockRpowSum k σ m| ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by
    rw [blockRpowSum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (sum_primeBlockSub_le_of_le_mul_rpow_decay hσ hmk (C := 2) (by norm_num) fun p hp => ?_)
    have ht0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have ht := (rpow_le_of_mem_primeBlockSub_decay hσ hmk hp).trans hq
    have hem : Real.exp (-(m : ℝ)) / 10 ^ 40 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      exact le_trans (Real.exp_le_one_iff.2 (by linarith [Nat.cast_nonneg (α := ℝ) m]))
        (by norm_num)
    have ht2 : |((p : ℕ) : ℝ) ^ (-1 - 2 * σ)| ≤ 1 / 2 := by
      rw [abs_of_nonneg ht0]
      exact ht.trans hem
    calc |Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) - ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ 2 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) ^ 2 := abs_log_one_add_sub_le ht2
      _ = 2 * (((p : ℕ) : ℝ) ^ (-1 - 2 * σ) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) := by ring
      _ ≤ 2 * (Real.exp (-(m : ℝ)) / 10 ^ 40 * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht ht0) (by norm_num)
  rw [abs_le] at hmean hlog ⊢
  constructor <;> linarith [hmean.1, hmean.2, hlog.1, hlog.2]

/-- **The mass factor in closed form** (HP2's prefix): for the blocks `m < M` at offset `k ≥ 20`
below the tilt cutoff, `2Mean_M - ∑_{p∈pre} log(1 + p^{-1-2σ}) = ∑_{m<M}(S_m + C_m(2h))` within
`5·10⁻²⁰`, `S_m = RMF.blockRpowSum`, `C_m(2h) = RMF.blockCosSum` at `2h`, with errors decaying in
the block (`RMF.abs_two_mul_windowMeanH_sub_log_le`, `∑_m e^{-m} ≤ e/(e-1)`). -/
theorem abs_two_mul_sum_windowMeanH_sub_log_le (hX : IsRademacherPrimeValues X μ) {y k M : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) :
    |2 * ∑ m ∈ Finset.range M, windowMeanH X μ y k σ h m
        - ∑ m ∈ Finset.range M, ∑ p ∈ primeBlockSub k m,
          Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∑ m ∈ Finset.range M, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)|
      ≤ 5 / 10 ^ 20 := by
  have heq : 2 * ∑ m ∈ Finset.range M, windowMeanH X μ y k σ h m
        - ∑ m ∈ Finset.range M, ∑ p ∈ primeBlockSub k m,
          Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - ∑ m ∈ Finset.range M, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
      = ∑ m ∈ Finset.range M, (2 * windowMeanH X μ y k σ h m
        - ∑ p ∈ primeBlockSub k m, Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hE := sum_exp_neg_le (Finset.range M)
  have he : Real.exp 1 / (Real.exp 1 - 1) ≤ 5 / 3 := by
    have h1 := Real.exp_one_gt_d9
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rw [heq]
  calc _ ≤ ∑ m ∈ Finset.range M, |2 * windowMeanH X μ y k σ h m
        - ∑ p ∈ primeBlockSub k m, Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
        - (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range M, 3 * (Real.exp (-(m : ℝ)) / 10 ^ 20) :=
        Finset.sum_le_sum fun m hm =>
          abs_two_mul_windowMeanH_sub_log_le hX hk hσ (hy m (Finset.mem_range.1 hm))
    _ = 3 / 10 ^ 20 * ∑ m ∈ Finset.range M, Real.exp (-(m : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ 3 / 10 ^ 20 * (5 / 3) := mul_le_mul_of_nonneg_left (hE.trans he) (by norm_num)
    _ = 5 / 10 ^ 20 := by norm_num

/-- **The mass factor**: `e^{2Mean_M}/E‖F_pre(s_h)‖² ≤ exp(∑_{m<M}(S_m + C_m(2h)) + 5·10⁻²⁰)`,
where `E‖F_pre(s_h)‖² = ∏_{m<M}∏_{p∈B_m}(1 + p^{-1-2σ})` for Rademacher values
(`RMF.abs_two_mul_sum_windowMeanH_sub_log_le`). -/
theorem exp_two_mul_sum_windowMeanH_div_prod_le (hX : IsRademacherPrimeValues X μ) {y k M : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) :
    Real.exp (2 * ∑ m ∈ Finset.range M, windowMeanH X μ y k σ h m)
        / ∏ m ∈ Finset.range M, ∏ p ∈ primeBlockSub k m, (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      ≤ Real.exp (∑ m ∈ Finset.range M, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
        + 5 / 10 ^ 20) := by
  have hprod : ∏ m ∈ Finset.range M, ∏ p ∈ primeBlockSub k m,
        (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))
      = Real.exp (∑ m ∈ Finset.range M, ∑ p ∈ primeBlockSub k m,
        Real.log (1 + ((p : ℕ) : ℝ) ^ (-1 - 2 * σ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Real.exp_log (by positivity)]
  rw [hprod, ← Real.exp_sub]
  refine Real.exp_le_exp.2 ?_
  have := abs_le.1 (abs_two_mul_sum_windowMeanH_sub_log_le hX (h := h) hk hσ hy)
  linarith [this.2]

end Mass

end RMF
