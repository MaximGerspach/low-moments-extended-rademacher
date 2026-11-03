/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.DecompositionQ
import RMF.UniformLower.HP1CertFloor
import RMF.UniformLower.HP2WindowExt
import RMF.UniformLower.SmallPrimesSharp
import RMF.UniformLower.C3NumeralsK
import RMF.UniformLower.BlockCosineFloor
import RMF.NumberTheory.MertensExplicit
import RMF.EulerProduct.RademacherExplicit
import RMF.Weighted.MesoscopicSum

/-!
# Per scale: exact Hölder, the head in the weight, the sum over scales

The per-scale estimate at exponent `q` with the smallest primes kept in the weight, and its sum
over scales.

* **The mass** `RMF.headWindowMass`: `(e^{2k}/2)∫_{halfWindow k} 1_{H(k,h)}‖F_{[0,y)}(s_h)‖² dh`,
  `H = RMF.hp1Tube`, over every prime below the cutoff (no `RMF.halfHeadConst`).
* **Multiplicity**: `∑_k 1_{E_k}a_k^q ≤ m^{1-q}(∑_k a_k)^q`
  (`RMF.sum_indicator_rpow_le_mul_rpow_sum`); `E(k) = halfLadder X σ k₀ k ∩ hp1After X σ k r(k)` has
  multiplicity `2` once `k₂ - k₁ ≤ r(k₁)` for `k₁ + 2 ≤ k₂`
  (`RMF.card_filter_mem_halfLadder_inter_hp1After_le_two`): every scale in `[k₀, T]` at the maximal
  `r(k) = T - k`.
* **Exact Hölder with a weight** (`RMF.rpow_div_rpow_le_integral_weight_rpow`) and the low × high
  split give the per-scale value `RMF.le_integral_indicator_rpow_headWindowMass`, its hypotheses in
  the shapes of (C3)*, HP1, (C2)* and HP2's window integral; with the four plugged in,
  `RMF.le_integral_indicator_rpow_headWindowMass_numeral`.
* **The sum over scales**: the factor `2^{2q-1}` from multiplicity two and the Rademacher symmetry
  (`RMF.le_integral_rpow_integral_lineDiv_head_symm`).
* **Explicit inputs**: `E‖F_{[c_k,y)}(s_σ)‖²e^k ≥ e^{-0.592}/(2σ)`
  (`RMF.le_integral_normSq_high_mul_exp`); `N_q(k) ≥ exp(-q(1-2q)(k + 0.7866 + 9.003e^{-k}))` for
  `q ≤ ½` (`RMF.le_integral_rpow_norm_low`).
* **The main term**, `σL = V`, `G = e^{-0.592}/2`, `Γ = RMF.perScaleConst`:
  `L^{-q}E[(∫_ℝ‖F_{[0,y)}(½+σ+it)/(σ+it)‖²dt)^q] ≥ 2^{2q-1}(G/V)^q∑_k Γ(q,k-k₀)N_q(k)(T-k)^{-q/2}`
  (`RMF.le_rpow_mul_integral_rpow_integral_lineDiv_numeral`; with `N_q` explicit,
  `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_explicit`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The window mass with the head in the weight -/

section Mass

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The scale-`k` window mass, the head kept in the weight**:
`(e^{2k}/2)∫_{halfWindow k} 1_{H(k,h)}‖F_{[0,y)}(½+σ+ih)‖² dh`, with `H(k,h) = RMF.hp1Tube`
(the tube of HP1 and HP2) and `F_{[0,y)}` over every prime below the cutoff `y`. -/
noncomputable def headWindowMass (X : ℕ → Ω → ℂ) (μ : Measure Ω) (σ : ℝ) (k r y : ℕ) (ω : Ω) :
    ℝ :=
  Real.exp (2 * (k : ℝ)) / 2 * ∫ h in halfWindow k,
    (hp1Tube X μ y k r σ h).indicator
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h) ω‖ ^ 2) ω

lemma headWindowMass_nonneg (X : ℕ → Ω → ℂ) (μ : Measure Ω) (σ : ℝ) (k r y : ℕ) (ω : Ω) :
    0 ≤ headWindowMass X μ σ k r y ω :=
  mul_nonneg (by positivity) (integral_nonneg fun _ => Set.indicator_nonneg (fun _ _ => by
    positivity) ω)

/-- The mass with `F_{[0,y)}` written as a block product. -/
lemma headWindowMass_eq_Ico (X : ℕ → Ω → ℂ) (μ : Measure Ω) (σ : ℝ) (k r y : ℕ) (ω : Ω) :
    headWindowMass X μ σ k r y ω = Real.exp (2 * (k : ℝ)) / 2 * ∫ h in halfWindow k,
      (hp1Tube X μ y k r σ h).indicator
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
          (shiftLine σ h) ω‖ ^ 2) ω := by
  simp only [headWindowMass, randomEulerProductIco_zero]

omit [MeasurableSpace Ω] in
/-- `E″_>(k)` is measurable for the algebra of any prime range containing its blocks. -/
lemma measurableSet_primeAlgebra_hp1After (σ : ℝ) {k r b : ℕ}
    (hb : scaleCut ((k : ℝ) + r) ≤ b) :
    MeasurableSet[primeAlgebra X (scaleCut (k : ℝ)) b] (hp1After X σ k r) := by
  have hrw : hp1After X σ k r = ⋂ j ∈ Set.Icc 2 r, {ω | walk (halfBlock X k σ 0) j ω ≤ 0} := by
    ext ω
    simp only [hp1After, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j hj => ?_
  exact measurableSet_le ((measurable_primeAlgebra_walk (X := X) (k : ℝ) σ 0 hj.2).mono
    (primeAlgebra_mono le_rfl hb) le_rfl) measurable_const

lemma measurableSet_hp1After (hX : IsRademacherPrimeValues X μ) (σ : ℝ) (k r : ℕ) :
    MeasurableSet (hp1After X σ k r) :=
  measurableSet_of_primeAlgebra hX
    (measurableSet_primeAlgebra_hp1After (X := X) σ (b := scaleCut ((k : ℝ) + r)) le_rfl)

/-- At a fixed `ω` the mass's integrand is integrable in the height. -/
lemma integrableOn_hp1Tube_normSq (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 0 ≤ σ)
    {k r y : ℕ} (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (ω : Ω) :
    IntegrableOn (fun h => (hp1Tube X μ y k r σ h).indicator
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h) ω‖ ^ 2) ω) (halfWindow k) := by
  have hcont : Continuous fun h : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h) ω‖ ^ 2 := by
    simpa only [randomEulerProductIco_zero] using
      continuous_normSq_randomEulerProductIco_shiftLine (X := X) 0 y σ ω
  have hslice : MeasurableSet {h : ℝ | ω ∈ hp1Tube X μ y k r σ h} :=
    measurable_prodMk_left (measurableSet_prod_hp1Tube hX hσ hy)
  have hrw : (fun h : ℝ => (hp1Tube X μ y k r σ h).indicator
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ h) ω‖ ^ 2) ω)
      = Set.indicator {h : ℝ | ω ∈ hp1Tube X μ y k r σ h}
        (fun h => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ h) ω‖ ^ 2) := by
    funext h
    by_cases hm : ω ∈ hp1Tube X μ y k r σ h
    · rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (show h ∈ {h : ℝ | ω ∈ hp1Tube X μ y k r σ h} from hm)]
    · rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show h ∉ {h : ℝ | ω ∈ hp1Tube X μ y k r σ h} from hm)]
  rw [hrw, halfWindow]
  exact (hcont.integrableOn_Icc).indicator hslice

/-- The mass is measurable. -/
lemma aestronglyMeasurable_headWindowMass (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 ≤ σ) {k r y : ℕ} (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) :
    AEStronglyMeasurable (fun ω => headWindowMass X μ σ k r y ω) μ := by
  have hbase := integrable_uncurry_indicator_normSq_primesIco hX 0 y hσ
    (volume_halfWindow_ne_top k) (fun h => hp1Tube X μ y k r σ h)
    (measurableSet_prod_hp1Tube hX hσ hy)
  have h := (hbase.integral_prod_left.aestronglyMeasurable).const_mul
    (Real.exp (2 * (k : ℝ)) / 2)
  exact h.congr (Filter.Eventually.of_forall fun ω =>
    (headWindowMass_eq_Ico X μ σ k r y ω).symm)

/-- The mass is bounded. -/
lemma ae_headWindowMass_le (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 0 ≤ σ)
    (k r y : ℕ) :
    ∀ᵐ ω ∂μ, headWindowMass X μ σ k r y ω
      ≤ Real.exp (2 * (k : ℝ)) / 2
        * ((∏ p ∈ primesIco 0 y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
          * volume.real (halfWindow k)) := by
  filter_upwards [ae_forall_norm_indicator_normSq_Ico_le hX 0 y hσ
    (fun h => hp1Tube X μ y k r σ h)] with ω hω
  rw [headWindowMass_eq_Ico]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (le_abs_self _) ?_
  rw [← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const
    (lt_of_le_of_ne le_top (volume_halfWindow_ne_top k)) fun h _ => hω h

end Mass

/-! ### Multiplicity -/

section Multiplicity

/-- **The power mean below exponent one**: `∑_{i∈s} a_i^q ≤ |s|^{1-q}(∑_{i∈s} a_i)^q` for
`a_i ≥ 0` and `0 ≤ q ≤ 1` (Jensen for the concave `x ↦ x^q`). -/
lemma sum_rpow_le_card_rpow_mul_rpow_sum {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ i ∈ s, a i ^ q ≤ (s.card : ℝ) ^ (1 - q) * (∑ i ∈ s, a i) ^ q := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg le_rfl _)
  · have hn : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
    have hS0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
    have hJ := (Real.concaveOn_rpow hq0 hq1).le_map_sum (t := s)
      (w := fun _ => (s.card : ℝ)⁻¹) (p := a) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp) (fun i hi => Set.mem_Ici.2 (ha i hi))
    simp only [smul_eq_mul] at hJ
    rw [← Finset.mul_sum, ← Finset.mul_sum, Real.mul_rpow (by positivity) hS0,
      Real.inv_rpow hn.le] at hJ
    have hnq : 0 < (s.card : ℝ) ^ q := Real.rpow_pos_of_pos hn q
    have hsub : (s.card : ℝ) ^ (1 - q) = (s.card : ℝ) / (s.card : ℝ) ^ q := by
      rw [Real.rpow_sub hn, Real.rpow_one]
    rw [hsub]
    have h2 := mul_le_mul_of_nonneg_left hJ hn.le
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at h2
    calc ∑ i ∈ s, a i ^ q ≤ (s.card : ℝ) * (((s.card : ℝ) ^ q)⁻¹ * (∑ i ∈ s, a i) ^ q) := h2
      _ = (s.card : ℝ) / (s.card : ℝ) ^ q * (∑ i ∈ s, a i) ^ q := by
        rw [div_eq_mul_inv]; ring

open Classical in
/-- **`q`-th powers add along events of multiplicity `m`.**  If every point lies in at most `m`
of the events `E k`, `k ∈ K`, then for `a k ≥ 0` and `0 ≤ q ≤ 1`,
`∑_{k ∈ K} 1_{E k}(a k)^q ≤ m^{1-q}(∑_{k ∈ K} a k)^q` pointwise. -/
lemma sum_indicator_rpow_le_mul_rpow_sum {α : Type*} {K : Finset ℕ} {E : ℕ → Set α} {m : ℕ}
    (hm : ∀ x, (K.filter fun k => x ∈ E k).card ≤ m)
    {a : ℕ → α → ℝ} (ha : ∀ k x, 0 ≤ a k x) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x : α) :
    ∑ k ∈ K, Set.indicator (E k) (fun x => a k x ^ q) x
      ≤ (m : ℝ) ^ (1 - q) * (∑ k ∈ K, a k x) ^ q := by
  classical
  set S := K.filter fun k => x ∈ E k with hS
  have h1 : ∑ k ∈ K, Set.indicator (E k) (fun x => a k x ^ q) x = ∑ k ∈ S, a k x ^ q := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : x ∈ E k
    · rw [Set.indicator_of_mem hk, if_pos hk]
    · rw [Set.indicator_of_notMem hk, if_neg hk]
  have h2 : ∑ k ∈ S, a k x ≤ ∑ k ∈ K, a k x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => ha k x
  rw [h1]
  refine (sum_rpow_le_card_rpow_mul_rpow_sum S (fun k _ => ha k x) hq0 hq1).trans ?_
  exact mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hm x) (by linarith))
    (Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => ha k x) h2 hq0)
    (Real.rpow_nonneg (Finset.sum_nonneg fun k _ => ha k x) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

variable {Ω : Type*}

/-- **`E(k₁)` and `E(k₂)` are disjoint two scales apart**: for `k₀ ≤ k₁`, `k₁ + 2 ≤ k₂` and
`k₂ - k₁ ≤ r₁`, the ladder at `k₂` puts the walk strictly higher at `k₂` than at `k₁`, and the
after event at `k₁` does not (its constraint at `j = k₂ - k₁ ∈ [2, r₁]`). -/
lemma disjoint_halfLadder_inter_hp1After (X : ℕ → Ω → ℂ) (σ : ℝ) {k₀ k₁ k₂ r₁ r₂ : ℕ}
    (hk₀ : k₀ ≤ k₁) (h12 : k₁ + 2 ≤ k₂) (hr : k₂ - k₁ ≤ r₁) :
    Disjoint (halfLadder X σ k₀ k₁ ∩ hp1After X σ k₁ r₁)
      (halfLadder X σ k₀ k₂ ∩ hp1After X σ k₂ r₂) := by
  refine Set.disjoint_left.2 fun ω hω hω' => ?_
  have hlt := hω'.1 (k₁ - k₀) (by omega)
  have hle := hω.2 (k₂ - k₁) (by omega) hr
  rw [walk_halfBlock_shift X σ 0 hk₀, show k₁ - k₀ + (k₂ - k₁) = k₂ - k₀ from by omega] at hle
  linarith

open Classical in
/-- **Multiplicity two**: every `ω` lies in at most two of the events
`E(k) = halfLadder X σ k₀ k ∩ hp1After X σ k (r k)`, `k ∈ K`, when `k₀ ≤ k` on `K` and
`k₂ - k₁ ≤ r k₁` for `k₁ + 2 ≤ k₂` in `K` (consecutive scales may overlap). -/
lemma card_filter_mem_halfLadder_inter_hp1After_le_two (X : ℕ → Ω → ℂ) (σ : ℝ) {k₀ : ℕ}
    {K : Finset ℕ} {r : ℕ → ℕ} (hK : ∀ k ∈ K, k₀ ≤ k)
    (hr : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ + 2 ≤ k₂ → k₂ - k₁ ≤ r k₁) (ω : Ω) :
    (K.filter fun k => ω ∈ halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).card ≤ 2 := by
  classical
  set S := K.filter fun k => ω ∈ halfLadder X σ k₀ k ∩ hp1After X σ k (r k) with hS
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]
    simp
  · have hk₁S : S.min' hne ∈ S := S.min'_mem hne
    have hsub : S ⊆ {S.min' hne, S.min' hne + 1} := by
      intro k hk
      have hle : S.min' hne ≤ k := S.min'_le k hk
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      have h2 : S.min' hne + 2 ≤ k := by omega
      have hk₁K := (Finset.mem_filter.1 hk₁S).1
      have hkK := (Finset.mem_filter.1 hk).1
      exact Set.disjoint_left.1 (disjoint_halfLadder_inter_hp1After X σ (hK _ hk₁K) h2
        (hr _ hk₁K k hkK h2)) (Finset.mem_filter.1 hk₁S).2 (Finset.mem_filter.1 hk).2
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

end Multiplicity

/-! ### Exact Hölder with a weight -/

section Holder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Exact Hölder with a weight**: for a measurable weight `w ≥ 0`, `Y ≥ 0`, `0 < q < 1`,
`0 < N ≤ ∫ wY` and `∫ wY² ≤ D`, `N^{2-q}/D^{1-q} ≤ ∫ wY^q` — Paley–Zygmund in exact form
(`RMF.rpow_integral_div_rpow_integral_sq_le_integral_rpow`) under the measure `w·μ`. -/
theorem rpow_div_rpow_le_integral_weight_rpow {w Y : Ω → ℝ} (hwm : Measurable w)
    (hw : ∀ ω, 0 ≤ w ω) (hY : ∀ ω, 0 ≤ Y ω) {q N D : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (h1 : Integrable (fun ω => w ω * Y ω ^ q) μ) (h2 : Integrable (fun ω => w ω * Y ω ^ 2) μ)
    (hN : 0 < N)
    (hNle : N ≤ ∫ ω, w ω * Y ω ∂μ) (hDle : (∫ ω, w ω * Y ω ^ 2 ∂μ) ≤ D) :
    N ^ (2 - q) / D ^ (1 - q) ≤ ∫ ω, w ω * Y ω ^ q ∂μ := by
  set w' : Ω → NNReal := fun ω => Real.toNNReal (w ω) with hw'
  have hw'm : Measurable w' := hwm.real_toNNReal
  have hcoe : ∀ ω, ((w' ω : NNReal) : ℝ) = w ω := fun ω => Real.coe_toNNReal _ (hw ω)
  set ν : Measure Ω := μ.withDensity (fun ω => (w' ω : ENNReal)) with hν
  have hint : ∀ g : Ω → ℝ, (∫ ω, g ω ∂ν) = ∫ ω, w ω * g ω ∂μ := by
    intro g
    rw [hν, integral_withDensity_eq_integral_smul hw'm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, hcoe]
  have hintg : ∀ g : Ω → ℝ, Integrable (fun ω => w ω * g ω) μ → Integrable g ν := by
    intro g hg
    rw [hν, integrable_withDensity_iff_integrable_smul hw'm]
    refine hg.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, hcoe]
  have hsq : ∀ ω, Y ω ^ (2 : ℝ) = Y ω ^ 2 := fun ω => Real.rpow_two _
  have h2' : Integrable (fun ω => w ω * Y ω ^ (2 : ℝ)) μ :=
    h2.congr (Filter.Eventually.of_forall fun ω => by simp only [hsq])
  have hI2 : (∫ ω, Y ω ^ (2 : ℝ) ∂ν) = ∫ ω, w ω * Y ω ^ 2 ∂μ := by
    rw [hint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hsq])
  -- the second moment is positive, since the first is
  have hpos : 0 < ∫ ω, w ω * Y ω ^ 2 ∂μ := by
    rcases lt_or_eq_of_le (integral_nonneg fun ω => mul_nonneg (hw ω) (sq_nonneg (Y ω)) :
      (0 : ℝ) ≤ ∫ ω, w ω * Y ω ^ 2 ∂μ) with h | h
    · exact h
    · exfalso
      have hz := (integral_eq_zero_iff_of_nonneg
        (fun ω => mul_nonneg (hw ω) (sq_nonneg (Y ω))) h2).1 h.symm
      have hz' : (fun ω => w ω * Y ω) =ᵐ[μ] 0 := by
        filter_upwards [hz] with ω hω
        have hω' : w ω * Y ω ^ 2 = 0 := hω
        rcases mul_eq_zero.1 hω' with h0 | h0
        · simp [h0]
        · simp [pow_eq_zero_iff (two_ne_zero) |>.1 h0]
      have : (∫ ω, w ω * Y ω ∂μ) = 0 := by
        rw [integral_congr_ae hz']
        simp
      linarith
  have hH := rpow_integral_div_rpow_integral_sq_le_integral_rpow (μ := ν) hq0 hq1
    (Filter.Eventually.of_forall hY) (hintg _ h1) (hintg _ h2') (by rw [hI2]; exact hpos)
  rw [hint (fun ω => Y ω), hI2, hint (fun ω => Y ω ^ q)] at hH
  refine le_trans ?_ hH
  have hNle' : N ^ (2 - q) ≤ (∫ ω, w ω * Y ω ∂μ) ^ (2 - q) :=
    Real.rpow_le_rpow hN.le hNle (by linarith)
  have hDle' : (∫ ω, w ω * Y ω ^ 2 ∂μ) ^ (1 - q) ≤ D ^ (1 - q) :=
    Real.rpow_le_rpow hpos.le hDle (by linarith)
  exact div_le_div₀ (Real.rpow_nonneg (hN.le.trans hNle) _) hNle'
    (Real.rpow_pos_of_pos hpos _) hDle'

end Holder

/-! ### Low × high at one height and at a pair of heights

The ladder `halfLadder X σ k₀ k` lives on the primes below `c_k = scaleCut k`, the tube `H(k,h)` and
`E″_>(k) = RMF.hp1After` on those of `[c_k, y)`, so both moments factorise across `c_k`
(`RMF.setIntegral_mul_split_primeAlgebra`). -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The cut `c_k` lies below the tubes' cutoff. -/
lemma scaleCut_le_of_cut_le {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    scaleCut (k : ℝ) ≤ y :=
  (cut_mono k (Nat.zero_le r)).trans hyr

/-- The tube and `E″_>(k)` are events of the primes of `[c_k, y)`. -/
lemma measurableSet_primeAlgebra_hp1Tube_inter_hp1After (μ : Measure Ω) (σ h : ℝ)
    {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    MeasurableSet[primeAlgebra X (scaleCut (k : ℝ)) y]
      (hp1Tube X μ y k r σ h ∩ hp1After X σ k r) :=
  (primeAlgebra_mono le_rfl hyr _ (measurableSet_primeAlgebra_hp1Tube (X := X) (μ := μ) y k
    (le_refl r) σ h)).inter
    (measurableSet_primeAlgebra_hp1After σ (by rw [scaleCut_add]; exact hyr))

/-- **The numerator at one height factorises across `c_k`**: against the weight
`1_{L∩E″}‖F_{[0,c_k)}(σ)‖^{2q-2}`, `E[… 1_{H(k,h)}‖F_{[0,y)}(s_h)‖²]` is (C3)*'s low integral
times `E[1_{H∩E″}‖F_{[c_k,y)}(s_h)‖²]`. -/
theorem integral_indicator_rpowQ_mul_indicator_normSq_eq_head
    (hX : IsRademacherPrimeValues X μ) {σ h q : ℝ} {k₀ k r y : ℕ} (hk : k₀ ≤ k)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    (∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω
        * Set.indicator (hp1Tube X μ y k r σ h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
            (shiftLine σ h) ω‖ ^ 2) ω ∂μ)
      = (∫ ω in halfLadder X σ k₀ k,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
                (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
                (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ)
        * ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω ∂μ := by
  have hcy : scaleCut (k : ℝ) ≤ y := scaleCut_le_of_cut_le hyr
  have hA : MeasurableSet[primeAlgebra X 0 (scaleCut (k : ℝ))] (halfLadder X σ k₀ k) :=
    primeAlgebra_mono (Nat.zero_le _) le_rfl _
      (measurableSet_primeAlgebra_halfLadder (X := X) σ hk le_rfl)
  have hB := measurableSet_primeAlgebra_hp1Tube_inter_hp1After (X := X) μ σ h hyr
  have hsplit := setIntegral_mul_split_primeAlgebra (X := X) (μ := μ) hX hA hB
    (measurable_twistPolyQ q (primesIco 0 (scaleCut (k : ℝ))) σ h)
    (measurable_normSqPoly (primesIco (scaleCut (k : ℝ)) y) (shiftLine σ h))
  simp only [twistPolyQ_primesIco, normSqPoly_primesIco] at hsplit
  have hAm : MeasurableSet (halfLadder X σ k₀ k) := measurableSet_of_primeAlgebra hX hA
  have hBm : MeasurableSet (hp1Tube X μ y k r σ h ∩ hp1After X σ k r) :=
    measurableSet_of_primeAlgebra hX hB
  rw [integral_indicator hBm, ← hsplit, ← integral_indicator (hAm.inter hBm)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  by_cases hL : ω ∈ halfLadder X σ k₀ k
  · by_cases hT : ω ∈ hp1Tube X μ y k r σ h
    · by_cases hE : ω ∈ hp1After X σ k r
      · rw [Set.indicator_of_mem (Set.mem_inter hL hE), Set.indicator_of_mem hT,
          Set.indicator_of_mem (Set.mem_inter hL (Set.mem_inter hT hE)),
          normSq_randomEulerProductIco_split (Nat.zero_le _) hcy]
        ring
      · have n1 : ω ∉ halfLadder X σ k₀ k ∩ hp1After X σ k r := fun hc => hE hc.2
        have n2 : ω ∉ halfLadder X σ k₀ k ∩ (hp1Tube X μ y k r σ h ∩ hp1After X σ k r) :=
          fun hc => hE hc.2.2
        rw [Set.indicator_of_notMem n1, Set.indicator_of_notMem n2, zero_mul]
    · have n2 : ω ∉ halfLadder X σ k₀ k ∩ (hp1Tube X μ y k r σ h ∩ hp1After X σ k r) :=
        fun hc => hT hc.2.1
      rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem n2, mul_zero]
  · have n1 : ω ∉ halfLadder X σ k₀ k ∩ hp1After X σ k r := fun hc => hL hc.1
    have n2 : ω ∉ halfLadder X σ k₀ k ∩ (hp1Tube X μ y k r σ h ∩ hp1After X σ k r) :=
      fun hc => hL hc.1
    rw [Set.indicator_of_notMem n1, Set.indicator_of_notMem n2, zero_mul]

/-- **The denominator at a pair of heights factorises across `c_k`**: against
`‖F_{[0,c_k)}(σ)‖^{2q-4}`, `E[… 1_{H₁}‖F_{[0,y)}(s₁)‖²·1_{H₂}‖F_{[0,y)}(s₂)‖²]` is (C2)*'s low
integral times `E[1_{H₁∩H₂}‖F_{[c_k,y)}(s₁)‖²‖F_{[c_k,y)}(s₂)‖²]`. -/
theorem integral_rpowQ_mul_pair_eq_head (hX : IsRademacherPrimeValues X μ)
    {σ h₁ h₂ q : ℝ} {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4)
        * Set.indicator (hp1Tube X μ y k r σ h₁)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
              (shiftLine σ h₁) ω‖ ^ 2) ω
        * Set.indicator (hp1Tube X μ y k r σ h₂)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
              (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4) ∂μ)
        * ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
  have hcy : scaleCut (k : ℝ) ≤ y := scaleCut_le_of_cut_le hyr
  have hT : ∀ h : ℝ, MeasurableSet[primeAlgebra X (scaleCut (k : ℝ)) y]
      (hp1Tube X μ y k r σ h) := fun h =>
    primeAlgebra_mono le_rfl hyr _ (measurableSet_primeAlgebra_hp1Tube (X := X) (μ := μ) y k
      (le_refl r) σ h)
  have hsplit := setIntegral_mul_split_primeAlgebra (X := X) (μ := μ) hX
    (A := (Set.univ : Set Ω)) (B := hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂)
    MeasurableSet.univ ((hT h₁).inter (hT h₂))
    (measurable_twistPairPolyQ q (primesIco 0 (scaleCut (k : ℝ))) σ h₁ h₂)
    (measurable_pairPoly (primesIco (scaleCut (k : ℝ)) y) (shiftLine σ h₁) (shiftLine σ h₂))
  rw [Set.univ_inter, setIntegral_univ] at hsplit
  simp only [twistPairPolyQ_primesIco, pairPoly_primesIco] at hsplit
  have hBm : MeasurableSet (hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂) :=
    (measurableSet_of_primeAlgebra hX (hT h₁)).inter (measurableSet_of_primeAlgebra hX (hT h₂))
  rw [← hsplit, ← integral_indicator hBm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  by_cases h1 : ω ∈ hp1Tube X μ y k r σ h₁
  · by_cases h2 : ω ∈ hp1Tube X μ y k r σ h₂
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
        Set.indicator_of_mem (Set.mem_inter h1 h2),
        normSq_randomEulerProductIco_split (Nat.zero_le _) hcy (shiftLine σ h₁),
        normSq_randomEulerProductIco_split (Nat.zero_le _) hcy (shiftLine σ h₂)]
      ring
    · have n2 : ω ∉ hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂ := fun hc => h2 hc.2
      rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem n2, mul_zero]
  · have n1 : ω ∉ hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂ := fun hc => h1 hc.1
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem n1, mul_zero, zero_mul]

/-- **HP1's window integral, high part**: HP1's statement over `F_{[0,y)}`
(`RMF.le_integral_hp1Tube_inter_hp1After_window_numeral_floor`, `P₁ = 0.31689`) with the primes
below `c_k` divided out — `E‖F_{[0,c_k)}(s_h)‖² = ∏_{p<c_k}(1 + p^{-1-2σ})` factors out of both
sides at every height:
`(1 - e^{-100})/√r·E‖F_{[c_k,y)}(s_σ)‖²·e^{-k}·P₁ ≤ ∫_W E[1_{H∩E″}‖F_{[c_k,y)}(s_h)‖²] dh`. -/
theorem le_integral_window_high_of_full (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) {P₁ : ℝ}
    (hHP1 : (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * P₁
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * P₁
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω ∂μ := by
  have hcy : scaleCut (k : ℝ) ≤ y := scaleCut_le_of_cut_le hyr
  set m : ℝ := ∏ p ∈ primesIco 0 (scaleCut (k : ℝ)), (1 + (p : ℝ) ^ (-1 - 2 * σ)) with hm
  have hm0 : 0 < m := Finset.prod_pos fun p _ => by positivity
  -- the primes below `c_k` factor out at every height
  have hsplit : ∀ h : ℝ, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
          ^ 2) ω ∂μ
      = m * ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω ∂μ := by
    intro h
    have hB := measurableSet_primeAlgebra_hp1Tube_inter_hp1After (X := X) μ σ h hyr
    have hBm : MeasurableSet (hp1Tube X μ y k r σ h ∩ hp1After X σ k r) :=
      measurableSet_of_primeAlgebra hX hB
    have hs := setIntegral_mul_split_primeAlgebra (X := X) (μ := μ) hX
      (A := (Set.univ : Set Ω)) MeasurableSet.univ hB
      (measurable_normSqPoly (primesIco 0 (scaleCut (k : ℝ))) (shiftLine σ h))
      (measurable_normSqPoly (primesIco (scaleCut (k : ℝ)) y) (shiftLine σ h))
    rw [Set.univ_inter, setIntegral_univ] at hs
    simp only [normSqPoly_primesIco] at hs
    rw [integral_normSq_Ico_eq_prod hX 0 (scaleCut (k : ℝ)) σ h] at hs
    rw [integral_indicator hBm, integral_indicator hBm, ← hs]
    refine setIntegral_congr_fun hBm fun ω _ => ?_
    rw [← randomEulerProductIco_zero, normSq_randomEulerProductIco_split (Nat.zero_le _) hcy]
  -- and so do they at height `0`, without the event
  have hfull : ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ 0) ω‖ ^ 2 ∂μ
      = m * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ := by
    rw [integral_normSq_randomEulerProduct_shiftLine hX y σ 0,
      integral_normSq_Ico_eq_prod hX (scaleCut (k : ℝ)) y σ 0, hm, ← primesIco_zero,
      ← primesIco_union (Nat.zero_le _) hcy, Finset.prod_union (disjoint_primesIco _ _ _)]
  rw [hfull, integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_const_mul]
    at hHP1
  have e : (1 - Real.exp (-100)) / √(r : ℝ)
        * (m * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * P₁
      = m * ((1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * P₁) := by
    ring
  rw [e] at hHP1
  exact le_of_mul_le_mul_left hHP1 hm0

end Split

/-! ### The two moments per scale -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- A window integral of a product against a lower bound: `c·H ≤ ∫_W f·g` when `c ≤ f` on `W`,
`g ≥ 0`, `H ≤ ∫_W g` and `f·g` is integrable on `W`. -/
lemma mul_le_setIntegral_mul_of_le {W : Set ℝ} (hW : MeasurableSet W) {f g : ℝ → ℝ} {c H : ℝ}
    (hc : 0 ≤ c) (hg : ∀ h, 0 ≤ g h) (hf : ∀ h ∈ W, c ≤ f h)
    (hint : IntegrableOn (fun h => f h * g h) W) (hH : H ≤ ∫ h in W, g h) :
    c * H ≤ ∫ h in W, f h * g h := by
  calc c * H ≤ c * ∫ h in W, g h := mul_le_mul_of_nonneg_left hH hc
    _ = ∫ h in W, c * g h := (integral_const_mul _ _).symm
    _ ≤ ∫ h in W, f h * g h := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => mul_nonneg hc (hg h))
        hint ?_
      exact (ae_restrict_iff' hW).2 (Filter.Eventually.of_forall fun h hh =>
        mul_le_mul_of_nonneg_right (hf h hh) (hg h))

/-- **The first moment per scale**: from (C3)*'s bound on the window and a lower bound `H` for HP1's
high window integral, `E[1_{L∩E″}‖F_{[0,c_k)}(σ)‖^{2q-2}·mass_k] ≥ (e^{2k}/2)·c₃·N_q(k)·H`,
`N_q(k) = E‖F_{[0,c_k)}(σ)‖^{2q}`. -/
theorem le_integral_indicator_rpowQ_mul_headWindowMass (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq1 : q ≤ 1) {k₀ k r y : ℕ} (hk : k₀ ≤ k)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) {c₃ H : ℝ} (hc₃ : 0 ≤ c₃)
    (hC3 : ∀ h ∈ halfWindow k,
      c₃ * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
        ≤ ∫ ω in halfLadder X σ k₀ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ)
    (hH : H ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω ∂μ) :
    Real.exp (2 * (k : ℝ)) / 2 * (c₃ * (∫ ω, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) 0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
          ^ (2 * q) ∂μ) * H)
      ≤ ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω
          * headWindowMass X μ σ k r y ω ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hy := primeBlockSub_subset_of_cut_le hyr
  have hEm : MeasurableSet (halfLadder X σ k₀ k ∩ hp1After X σ k r) :=
    (measurableSet_halfLadder hX σ k₀ k).inter (measurableSet_hp1After hX σ k r)
  have hψm : AEStronglyMeasurable (fun ω => Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
        (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω) μ :=
    (((measurable_norm_randomEulerProductIco hX 0 (scaleCut (k : ℝ))
      (shiftLine σ 0)).pow_const _).indicator hEm).aestronglyMeasurable
  have hd0 : 0 < blockEnvDown 0 (scaleCut (k : ℝ)) σ := blockEnvDown_pos _ _ hσ
  have hψb : ∀ᵐ ω ∂μ, ‖Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
        (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω‖
        ≤ blockEnvDown 0 (scaleCut (k : ℝ)) σ ^ (2 * q - 2) := by
    filter_upwards [ae_forall_norm_randomEulerProductIco_env hX 0 (scaleCut (k : ℝ)) hσ]
      with ω hω
    have hd := (hω 0).1
    by_cases hm : ω ∈ halfLadder X σ k₀ k ∩ hp1After X σ k r
    · rw [Set.indicator_of_mem hm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos hd0 hd (by linarith)
    · rw [Set.indicator_of_notMem hm, norm_zero]
      positivity
  have hSmeas := measurableSet_prod_hp1Tube (X := X) (μ := μ) hX hσ hy
  have hWfin := volume_halfWindow_ne_top k
  have hswap := integral_mul_setIntegral_indicator_normSq_Ico_eq hX 0 y hσ
    (fun h => hp1Tube X μ y k r σ h) hSmeas hWfin _ hψm hψb
  have hmass : (∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω
          * headWindowMass X μ σ k r y ω ∂μ)
      = Real.exp (2 * (k : ℝ)) / 2 * ∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω
          * (∫ h in halfWindow k, Set.indicator (hp1Tube X μ y k r σ h)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
              (shiftLine σ h) ω‖ ^ 2) ω) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [headWindowMass_eq_Ico]
    ring
  have hfac : ∀ h : ℝ, (∫ ω, Set.indicator (halfLadder X σ k₀ k ∩ hp1After X σ k r)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)) ω
        * Set.indicator (hp1Tube X μ y k r σ h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
            (shiftLine σ h) ω‖ ^ 2) ω ∂μ)
      = (∫ ω in halfLadder X σ k₀ k,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
                (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
                (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ)
        * ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω ∂μ :=
    fun h => integral_indicator_rpowQ_mul_indicator_normSq_eq_head hX hk hyr
  have hint := (integrableOn_integral_mul_indicator_normSq hX 0 y hσ
    (fun h => hp1Tube X μ y k r σ h) hSmeas hWfin _ hψm hψb).congr_fun
    (fun h _ => hfac h) measurableSet_Icc
  have hN₀0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  rw [hmass, hswap, integral_congr_ae (Filter.Eventually.of_forall hfac)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_setIntegral_mul_of_le measurableSet_Icc (mul_nonneg hc₃ hN₀0)
    (fun h => integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => by positivity) ω)
    hC3 hint hH

/-- **The second moment per scale**: from (C2)*'s bound at every pair of heights of the window and
HP2's pair integral over `F_{[c_k,y)}` (`RMF.integral_integral_pair_rest_le_two_thousand`),
`E[‖F_{[0,c_k)}(σ)‖^{2q-4}·mass_k²] ≤ (e^{4k}/4)·C₂N_q(k)·(E‖F_{[c_k,y)}(s_σ)‖²)²e^{-2k}Q/r`. -/
theorem integral_rpowQ_mul_headWindowMass_sq_le (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq1 : q ≤ 1) {k r y : ℕ} (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    {C₂ Q : ℝ} (hC₂ : 0 ≤ C₂)
    (hC2 : ∀ h₁ ∈ halfWindow k, ∀ h₂ ∈ halfWindow k,
      (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4) ∂μ)
        ≤ C₂ * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
    (hHP2 : ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * Q / r) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4)
        * headWindowMass X μ σ k r y ω ^ 2 ∂μ)
      ≤ Real.exp (4 * (k : ℝ)) / 4 * ((C₂ * ∫ ω, ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) 0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
            ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
          * Real.exp (-2 * (k : ℝ)) * Q / r)) := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hy := primeBlockSub_subset_of_cut_le hyr
  have hN₀0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hd0 : 0 < blockEnvDown 0 (scaleCut (k : ℝ)) σ := blockEnvDown_pos _ _ hσ
  have hTm : ∀ h, MeasurableSet (hp1Tube X μ y k r σ h) := fun h =>
    measurableSet_of_primeAlgebra hX (primeAlgebra_mono le_rfl hyr _
      (measurableSet_primeAlgebra_hp1Tube (X := X) (μ := μ) y k (le_refl r) σ h))
  have hSmeas := measurableSet_prod_hp1Tube (X := X) (μ := μ) hX hσ hy
  have hWfin := volume_halfWindow_ne_top k
  -- the mass squared
  have hsq : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4)
        * headWindowMass X μ σ k r y ω ^ 2 ∂μ)
      = Real.exp (4 * (k : ℝ)) / 4 * ∫ ω, ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) 0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖
            ^ (2 * q - 4)
          * (∫ h in halfWindow k, Set.indicator (hp1Tube X μ y k r σ h)
            (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 y
              (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ := by
    have hexp : Real.exp (2 * (k : ℝ)) ^ 2 = Real.exp (4 * (k : ℝ)) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [headWindowMass_eq_Ico]
    rw [mul_pow, div_pow, hexp]
    ring
  have hψb : ∀ᵐ ω ∂μ, ‖‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4)‖
        ≤ blockEnvDown 0 (scaleCut (k : ℝ)) σ ^ (2 * q - 4) := by
    filter_upwards [ae_forall_norm_randomEulerProductIco_env hX 0 (scaleCut (k : ℝ)) hσ]
      with ω hω
    have hd := (hω 0).1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hd0 hd (by linarith)
  have hpair : ∀ h₁ ∈ halfWindow k, ∀ h₂ ∈ halfWindow k,
      (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4)
          * Set.indicator (hp1Tube X μ y k r σ h₁)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                0 y (shiftLine σ h₁) ω‖ ^ 2) ω
          * Set.indicator (hp1Tube X μ y k r σ h₂)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                0 y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
        ≤ (C₂ * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
          * ∫ ω, Set.indicator (hp1Tube X μ y k r σ h₁)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (hp1Tube X μ y k r σ h₂)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ := by
    intro h₁ hh₁ h₂ hh₂
    rw [integral_rpowQ_mul_pair_eq_head hX hyr, ← integral_indicator ((hTm h₁).inter (hTm h₂))]
    have hright : (∫ ω, Set.indicator (hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ)
        = ∫ ω, Set.indicator (hp1Tube X μ y k r σ h₁)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2) ω
            * Set.indicator (hp1Tube X μ y k r σ h₂)
              (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2) ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => Set.inter_indicator_mul _ _ ω)
    rw [hright]
    refine mul_le_mul_of_nonneg_right (hC2 h₁ hh₁ h₂ hh₂) ?_
    exact integral_nonneg fun ω => mul_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) ω)
      (Set.indicator_nonneg (fun _ _ => by positivity) ω)
  have hcomp := integral_mul_sq_setIntegral_le hX 0 y (scaleCut (k : ℝ)) y hσ
    (fun h => hp1Tube X μ y k r σ h) hTm hSmeas (W := halfWindow k) measurableSet_Icc hWfin _
    ((measurable_norm_randomEulerProductIco hX 0 (scaleCut (k : ℝ))
      (shiftLine σ 0)).pow_const _).aestronglyMeasurable hψb hpair
  have hexp2 : (∫ ω, (∫ h in halfWindow k, Set.indicator (hp1Tube X μ y k r σ h)
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2) ω) ^ 2 ∂μ)
      = ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
          ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₁) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ := by
    rw [integral_sq_setIntegral_indicator_normSq_Ico_eq hX (scaleCut (k : ℝ)) y hσ _ hTm hSmeas
      hWfin]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h₁ => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun h₂ => ?_)
    beta_reduce
    rw [← integral_indicator ((hTm h₁).inter (hTm h₂))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (Set.inter_indicator_mul _ _ ω).symm)
  rw [hsq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine hcomp.trans ?_
  rw [hexp2]
  exact mul_le_mul_of_nonneg_left hHP2 (mul_nonneg hC₂ hN₀0)

end Moments

/-! ### The per-scale value -/

section PerScaleValue

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The per-scale constant in closed form: for positive `c₃, C₂, a, Q, n, z`,
`(c₃naz/2)^{2-q}/(C₂nQz²/4)^{1-q} = c₃^{2-q}C₂^{-(1-q)}2^{-q}a^{2-q}Q^{-(1-q)}·n·z^q`. -/
lemma perScale_rpow_arith {c₃ C₂ a Q n z : ℝ} (q : ℝ) (hc₃ : 0 < c₃) (hC₂ : 0 < C₂)
    (ha : 0 < a) (hQ : 0 < Q) (hn : 0 < n) (hz : 0 < z) :
    (c₃ * n * a * z / 2) ^ (2 - q) / (C₂ * n * Q * z ^ 2 / 4) ^ (1 - q)
      = c₃ ^ (2 - q) * C₂ ^ (-(1 - q)) * 2 ^ (-q) * a ^ (2 - q) * Q ^ (-(1 - q)) * n
        * z ^ q := by
  have h1 : 0 < c₃ * n * a * z / 2 := by positivity
  have h2 : 0 < C₂ * n * Q * z ^ 2 / 4 := by positivity
  have hl1 : Real.log (c₃ * n * a * z / 2)
      = Real.log c₃ + Real.log n + Real.log a + Real.log z - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) hz.ne',
      Real.log_mul (by positivity) ha.ne', Real.log_mul hc₃.ne' hn.ne']
  have hl2 : Real.log (C₂ * n * Q * z ^ 2 / 4)
      = Real.log C₂ + Real.log n + Real.log Q + 2 * Real.log z - 2 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hQ.ne', Real.log_mul hC₂.ne' hn.ne', Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2, ← Real.exp_sub, hl1, hl2,
    Real.rpow_def_of_pos hc₃, Real.rpow_def_of_pos hC₂,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos hz]
  conv_rhs => rw [← Real.exp_log hn]
  simp only [← Real.exp_add]
  congr 1
  ring

omit [MeasurableSpace Ω] in
/-- `1_S·F^{2q}·(M/F²)^q = 1_S·M^q` where `F > 0`. -/
private lemma indicator_rpow_mul_div_rpow {S : Set Ω} {F M : Ω → ℝ} {q : ℝ} {ω : Ω}
    (hF : 0 < F ω) (hM : 0 ≤ M ω) :
    Set.indicator S (fun ω => F ω ^ (2 * q)) ω * (M ω / F ω ^ 2) ^ q
      = Set.indicator S (fun ω => M ω ^ q) ω := by
  by_cases hm : ω ∈ S
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Real.div_rpow hM (by positivity),
      show F ω ^ 2 = F ω ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_mul hF.le]
    push_cast
    field_simp
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]

omit [MeasurableSpace Ω] in
/-- `1_S·F^{2q}·(M/F²) = 1_S·F^{2q-2}·M` where `F > 0`. -/
private lemma indicator_rpow_mul_div {S : Set Ω} {F M : Ω → ℝ} {q : ℝ} {ω : Ω}
    (hF : 0 < F ω) :
    Set.indicator S (fun ω => F ω ^ (2 * q)) ω * (M ω / F ω ^ 2)
      = Set.indicator S (fun ω => F ω ^ (2 * q - 2)) ω * M ω := by
  by_cases hm : ω ∈ S
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Real.rpow_sub hF,
      show F ω ^ (2 : ℝ) = F ω ^ 2 by rw [Real.rpow_two]]
    field_simp
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul, zero_mul]

omit [MeasurableSpace Ω] in
/-- `1_S·F^{2q}·(M/F²)² ≤ F^{2q-4}·M²` where `F > 0`. -/
private lemma indicator_rpow_mul_div_sq_le {S : Set Ω} {F M : Ω → ℝ} {q : ℝ} {ω : Ω}
    (hF : 0 < F ω) :
    Set.indicator S (fun ω => F ω ^ (2 * q)) ω * (M ω / F ω ^ 2) ^ 2
      ≤ F ω ^ (2 * q - 4) * M ω ^ 2 := by
  have heq : F ω ^ (2 * q) * (M ω / F ω ^ 2) ^ 2 = F ω ^ (2 * q - 4) * M ω ^ 2 := by
    rw [Real.rpow_sub hF, show F ω ^ (4 : ℝ) = F ω ^ 4 by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    field_simp
  by_cases hm : ω ∈ S
  · rw [Set.indicator_of_mem hm, heq]
  · rw [Set.indicator_of_notMem hm, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg hF.le _) (sq_nonneg _)

/-- **The per-scale value by exact Hölder, the head in the weight.**  With
`w = 1_{E(k)}‖F_{[0,c_k)}(σ)‖^{2q}`, `Y = mass_k/‖F_{[0,c_k)}(σ)‖²` and
`E(k) = halfLadder X σ k₀ k ∩ hp1After X σ k r`, for `0 < q < 1`:
`E[1_{E(k)}mass_k^q] ≥ c₃^{2-q}C₂^{-(1-q)}2^{-q}((1 - e^{-100})P₁)^{2-q}Q^{-(1-q)}·N_q(k)·
(E‖F_{[c_k,y)}(s_σ)‖²e^k/√r)^q`, `N_q(k) = E‖F_{[0,c_k)}(σ)‖^{2q}`.  Each hypothesis is a producer's
conclusion as stated there:
* `hC3`, (C3)*: `RMF.le_setIntegral_halfLadder_twistQ_c3FloorK` at `a = 0`,
  `c₃ = c3FloorK q (k - k₀)`;
* `hHP1`, HP1: `RMF.le_integral_hp1Tube_inter_hp1After_window_numeral_floor`, `P₁ = 0.31689`;
* `hC2`, (C2)*: `RMF.integral_twistQ_pair_le_sharp`, `C₂ = e^{2(1-q)+0.50001}`;
* `hHP2`, HP2: `RMF.integral_integral_pair_rest_le_two_thousand`, `Q = 6482`. -/
theorem le_integral_indicator_rpow_headWindowMass (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 < q) (hq1 : q < 1) {k₀ k r y : ℕ} (hk : k₀ ≤ k)
    (hr : 0 < r) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) {c₃ C₂ P₁ Q : ℝ} (hc₃ : 0 < c₃)
    (hC₂ : 0 < C₂) (hP₁ : 0 < P₁) (hQ : 0 < Q)
    (hC3 : ∀ h ∈ halfWindow k,
      c₃ * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
        ≤ ∫ ω in halfLadder X σ k₀ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ)
    (hHP1 : (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * P₁
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ)
    (hC2 : ∀ h₁ ∈ halfWindow k, ∀ h₂ ∈ halfWindow k,
      (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ h₂) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 4) ∂μ)
        ≤ C₂ * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
    (hHP2 : ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * Q / r) :
    c₃ ^ (2 - q) * C₂ ^ (-(1 - q)) * 2 ^ (-q) * ((1 - Real.exp (-100)) * P₁) ^ (2 - q)
        * Q ^ (-(1 - q))
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ) / √(r : ℝ)) ^ q
      ≤ ∫ ω, (halfLadder X σ k₀ k ∩ hp1After X σ k r).indicator
          (fun ω => headWindowMass X μ σ k r y ω ^ q) ω ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hy := primeBlockSub_subset_of_cut_le hyr
  set F₀ : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    0 (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ with hF₀
  set M : Ω → ℝ := fun ω => headWindowMass X μ σ k r y ω with hM
  set S : Set Ω := halfLadder X σ k₀ k ∩ hp1After X σ k r with hS
  set N₀ : ℝ := ∫ ω, F₀ ω ^ (2 * q) ∂μ with hN₀
  set Eh : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ with hEh
  set a : ℝ := (1 - Real.exp (-100)) * P₁ with ha
  set z : ℝ := Eh * Real.exp (k : ℝ) / √(r : ℝ) with hz
  -- measurability and the envelopes
  have hSm : MeasurableSet S :=
    (measurableSet_halfLadder hX σ k₀ k).inter (measurableSet_hp1After hX σ k r)
  have hF₀m : Measurable F₀ :=
    measurable_norm_randomEulerProductIco hX 0 (scaleCut (k : ℝ)) (shiftLine σ 0)
  have hMm : AEStronglyMeasurable M μ := aestronglyMeasurable_headWindowMass hX hσ hy
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => headWindowMass_nonneg X μ σ k r y ω
  have henv := ae_forall_norm_randomEulerProductIco_env hX 0 (scaleCut (k : ℝ)) hσ
  have hd0 : 0 < blockEnvDown 0 (scaleCut (k : ℝ)) σ := blockEnvDown_pos _ _ hσ
  set up : ℝ := blockEnvUp 0 (scaleCut (k : ℝ)) σ with hup
  set dn : ℝ := blockEnvDown 0 (scaleCut (k : ℝ)) σ with hdn
  have hpos : ∀ᵐ ω ∂μ, 0 < F₀ ω := by
    filter_upwards [henv] with ω hω
    exact lt_of_lt_of_le hd0 (hω 0).1
  set Mb : ℝ := Real.exp (2 * (k : ℝ)) / 2
    * ((∏ p ∈ primesIco 0 y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 * volume.real (halfWindow k))
    with hMb
  have hMb' : ∀ᵐ ω ∂μ, M ω ≤ Mb := ae_headWindowMass_le hX hσ k r y
  have hup0 : 0 ≤ up := by
    obtain ⟨ω, hω⟩ := henv.exists
    exact le_trans (norm_nonneg _) (hω 0).2
  -- positivity of the constants
  have hN₀pos : 0 < N₀ := by
    have hint : Integrable (fun ω => F₀ ω ^ (2 * q)) μ := by
      refine (integrable_const (up ^ (2 * q))).mono'
        ((hF₀m.pow_const _).aestronglyMeasurable) ?_
      filter_upwards [henv] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_rpow (norm_nonneg _) (hω 0).2 (by linarith)
    have hle : (∫ _ : Ω, dn ^ (2 * q) ∂μ) ≤ N₀ := by
      refine integral_mono_ae (integrable_const _) hint ?_
      filter_upwards [henv] with ω hω
      exact Real.rpow_le_rpow hd0.le (hω 0).1 (by linarith)
    rw [integral_const, probReal_univ, one_smul] at hle
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hd0 _) hle
  have hEhpos : 0 < Eh := by
    rw [hEh, integral_normSq_Ico_eq_prod hX (scaleCut (k : ℝ)) y σ 0]
    exact Finset.prod_pos fun p _ => by positivity
  have hr0 : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
  have hzpos : 0 < z := by rw [hz]; positivity
  have hapos : 0 < a := mul_pos (by linarith [exp_neg_hundred_le_half]) hP₁
  -- the two moments
  have hH := le_integral_window_high_of_full hX hyr hHP1
  have hNum := le_integral_indicator_rpowQ_mul_headWindowMass hX hσ hq1.le hk hyr hc₃.le hC3 hH
  have hDen := integral_rpowQ_mul_headWindowMass_sq_le hX hσ hq1.le hyr hC₂.le hC2 hHP2
  have hNeq : Real.exp (2 * (k : ℝ)) / 2 * (c₃ * N₀ * ((1 - Real.exp (-100)) / √(r : ℝ) * Eh
      * Real.exp (-(k : ℝ)) * P₁)) = c₃ * N₀ * a * z / 2 := by
    rw [ha, hz, show Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) * Real.exp (k : ℝ) by
      rw [← Real.exp_add]; ring_nf, Real.exp_neg (k : ℝ)]
    field_simp
  have hDeq : Real.exp (4 * (k : ℝ)) / 4 * ((C₂ * N₀) * (Eh ^ 2 * Real.exp (-2 * (k : ℝ)) * Q
      / r)) = C₂ * N₀ * Q * z ^ 2 / 4 := by
    have hsr : √(r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt (Nat.cast_nonneg r)
    rw [hz, div_pow, mul_pow, hsr, show Real.exp (4 * (k : ℝ))
      = (Real.exp (k : ℝ) ^ 2) * (Real.exp (k : ℝ) ^ 2) by
        rw [← pow_add, ← Real.exp_nat_mul]; ring_nf,
      show Real.exp (-2 * (k : ℝ)) = (Real.exp (k : ℝ) ^ 2)⁻¹ by
        rw [← Real.exp_nat_mul, ← Real.exp_neg]; ring_nf]
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    field_simp
  rw [hNeq] at hNum
  rw [hDeq] at hDen
  -- the weight and the variable
  set w : Ω → ℝ := fun ω => Set.indicator S (fun ω => F₀ ω ^ (2 * q)) ω with hw
  set Y : Ω → ℝ := fun ω => M ω / F₀ ω ^ 2 with hY
  have hw0 : ∀ ω, 0 ≤ w ω := fun ω =>
    Set.indicator_nonneg (fun ω _ => Real.rpow_nonneg (norm_nonneg _) _) ω
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => div_nonneg (hM0 ω) (sq_nonneg _)
  have hwm : Measurable w := (hF₀m.pow_const _).indicator hSm
  have hYm : AEStronglyMeasurable Y μ :=
    (hMm.aemeasurable.div (hF₀m.pow_const 2).aemeasurable).aestronglyMeasurable
  have hwb : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ up ^ (2 * q) := by
    filter_upwards [henv] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 ω)]
    by_cases hm : ω ∈ S
    · simp only [hw]
      rw [Set.indicator_of_mem hm]
      exact Real.rpow_le_rpow (norm_nonneg _) (hω 0).2 (by linarith)
    · simp only [hw]
      rw [Set.indicator_of_notMem hm]
      exact Real.rpow_nonneg hup0 _
  have hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ Mb / dn ^ 2 := by
    filter_upwards [henv, hMb'] with ω hω hMle
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]
    exact div_le_div₀ (le_trans (hM0 ω) hMle) hMle (by positivity)
      (pow_le_pow_left₀ hd0.le (hω 0).1 2)
  have hwb0 : 0 ≤ up ^ (2 * q) := Real.rpow_nonneg hup0 _
  have h1 : Integrable (fun ω => w ω * Y ω ^ q) μ := by
    refine (integrable_const (up ^ (2 * q) * (Mb / dn ^ 2) ^ q)).mono'
      (hwm.aestronglyMeasurable.mul (hYm.aemeasurable.pow_const q).aestronglyMeasurable) ?_
    filter_upwards [hwb, hYb] with ω hw1 hw2
    rw [norm_mul]
    refine mul_le_mul hw1 ?_ (norm_nonneg _) hwb0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hY0 ω) _)]
    refine Real.rpow_le_rpow (hY0 ω) ?_ hq0.le
    exact le_trans (le_abs_self _) (by rwa [← Real.norm_eq_abs])
  have h2 : Integrable (fun ω => w ω * Y ω ^ 2) μ := by
    refine (integrable_const (up ^ (2 * q) * (Mb / dn ^ 2) ^ 2)).mono'
      (hwm.aestronglyMeasurable.mul (hYm.pow 2)) ?_
    filter_upwards [hwb, hYb] with ω hw1 hw2
    rw [norm_mul, norm_pow]
    exact mul_le_mul hw1 (pow_le_pow_left₀ (norm_nonneg _) hw2 2) (by positivity) hwb0
  -- the two moments of the weighted variable
  have hNle : c₃ * N₀ * a * z / 2 ≤ ∫ ω, w ω * Y ω ∂μ := by
    refine le_trans hNum (le_of_eq (integral_congr_ae ?_))
    filter_upwards [hpos] with ω hω
    exact (indicator_rpow_mul_div (S := S) (F := F₀) (M := M) hω).symm
  have hDle : (∫ ω, w ω * Y ω ^ 2 ∂μ) ≤ C₂ * N₀ * Q * z ^ 2 / 4 := by
    refine le_trans (integral_mono_ae h2 ?_ ?_) hDen
    · refine (integrable_const (dn ^ (2 * q - 4) * Mb ^ 2)).mono'
        (((hF₀m.pow_const _).aestronglyMeasurable).mul (hMm.pow 2)) ?_
      filter_upwards [henv, hMb'] with ω hω hMle
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hd0 (hω 0).1 (by linarith))
        (pow_le_pow_left₀ (hM0 ω) hMle 2) (by positivity) (by positivity)
    · filter_upwards [hpos] with ω hω
      exact indicator_rpow_mul_div_sq_le (S := S) (F := F₀) (M := M) hω
  have hNpos : 0 < c₃ * N₀ * a * z / 2 := by positivity
  have hmain := rpow_div_rpow_le_integral_weight_rpow hwm hw0 hY0 hq0 hq1 h1 h2 hNpos hNle hDle
  rw [perScale_rpow_arith q hc₃ hC₂ hapos hQ hN₀pos hzpos] at hmain
  refine le_trans (le_of_eq ?_) (hmain.trans (le_of_eq (integral_congr_ae ?_)))
  · ring
  · filter_upwards [hpos] with ω hω
    exact indicator_rpow_mul_div_rpow (S := S) (F := F₀) (M := M) hω (hM0 ω)

end PerScaleValue

/-! ### The per-scale value with the producers' numerals -/

section Numerals

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- `c3FloorK q K ≥ 0.03849 > 0` on `0 ≤ q ≤ 11/20`. -/
lemma c3FloorK_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11 / 20) (K : ℕ) : 0 < c3FloorK q K := by
  unfold c3FloorK
  split_ifs with h
  · have hn0 : ((⌊400 * q⌋₊ : ℕ) : ℝ) ≤ 400 * q := Nat.floor_le (by positivity)
    have hn : ⌊400 * q⌋₊ < 200 := by
      have : ((⌊400 * q⌋₊ : ℕ) : ℝ) < 200 := by linarith [h.2]
      exact_mod_cast this
    linarith [c3OneTab_ge _ hn]
  · linarith [c3Floor_ge hq0 hq1]

/-- **The per-scale value with every producer plugged in**: for `k₀ ≥ 20`, `k₀ < k`, `0 < q ≤
½ + 1/20` (and `k - k₀ ≤ K_max(q)` below `½`), `r ≥ 2000` maximal for the damping
`σe^{k+r} ≤ 1/200 < σe^{k+r+1}` and the cutoff `y ≥ c_{k+r}`:
`E[1_{E(k)}mass_k^q] ≥ c₃^{2-q}C₂^{-(1-q)}2^{-q}((1 - e^{-100})·0.31689)^{2-q}·6482^{-(1-q)}·N_q(k)·
(E‖F_{[c_k,y)}(s_σ)‖²e^k/√r)^q` with `c₃ = c3FloorK q (k - k₀)`, `C₂ = e^{2(1-q)+0.50001}`. -/
theorem le_integral_indicator_rpow_headWindowMass_numeral (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {k₀ k r y : ℕ}
    (hk₀ : 20 ≤ k₀) (hk : k₀ < k) (hK : q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1))
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hr : 2000 ≤ r) :
    c3FloorK q (k - k₀) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ) / √(r : ℝ)) ^ q
      ≤ ∫ ω, (halfLadder X σ k₀ k ∩ hp1After X σ k r).indicator
          (fun ω => headWindowMass X μ σ k r y ω ^ q) ω ∂μ := by
  have hk20 : 20 ≤ k := by omega
  have hy := primeBlockSub_subset_of_cut_le hyr
  have hση : σ * Real.exp k ≤ 1 / 200 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (by linarith [Nat.cast_nonneg (α := ℝ) r])) hσ) hσr
  refine le_integral_indicator_rpow_headWindowMass hX hσ hq0 (by linarith) hk.le (by omega) hyr
    (c3FloorK_pos hq0.le (by linarith) _) (Real.exp_pos _) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · intro h hh
    exact le_setIntegral_halfLadder_twistQ_c3FloorK hX (Nat.zero_le _) hk₀ hk hσ hση hq0.le hq1
      hK hh
  · exact le_integral_hp1Tube_inter_hp1After_window_numeral_floor hX hk20 hσ hσr hy hr
  · intro h₁ hh₁ h₂ hh₂
    exact integral_twistQ_pair_le_sharp hX hk20 hσ hq0.le (by linarith)
      (le_trans (Real.exp_pos _).le hh₁.1) hh₁.2 (le_trans (Real.exp_pos _).le hh₂.1) hh₂.2
  · exact integral_integral_pair_rest_le_two_thousand hX hk20 hσr hσr' hyr hr

end Numerals

/-! ### `E‖F_{[c_k,y)}(s_σ)‖²e^k` from below

`E‖F_{[c_k,y)}(s_σ)‖² = ∏_{c_k≤p<y}(1 + p^{-1-2σ}) ≥ exp(∑p^{-1-2σ} - ∑p^{-2-4σ})`; the prime sum
over the full blocks `[k, k+n)` is the damped integral `∫_{e^k}^{e^{k+n}} e^{-2σu}/u du` up to the
two-regime error `3.16·10⁻⁶` (`RMF.abs_sum_blockCosSum_sub_integral_le_two_regime`), and
`∫_a^3 e^{-s}/s ds ≥ log(3/a) + einPoly 9 3 - einPoly 9 a ≥ log(1/a) - 0.5916` by the alternating
Taylor bound.  So `E‖F_{[c_k,y)}(s_σ)‖²e^k ≥ e^{-0.592}/(2σ)`. -/

section High

/-- `e^{-s}/s ≥ 1/s + ∑_{i<2K+1}(-1)^{i+1}s^i/(i+1)!` for `s > 0`. -/
lemma ein_le_exp_neg_div (K : ℕ) {s : ℝ} (hs : 0 < s) :
    s⁻¹ + ∑ i ∈ Finset.range (2 * K + 1), (-1) ^ (i + 1) * s ^ i / ((i + 1).factorial : ℝ)
      ≤ Real.exp (-s) / s := by
  have h := exp_neg_taylor_alt (2 * K + 2) hs.le
  rw [show 2 * K + 2 = 2 * (K + 1) by ring, pow_mul, neg_one_sq, one_pow, one_mul] at h
  have hP : expNegPoly (2 * (K + 1)) s
      = 1 + s * ∑ i ∈ Finset.range (2 * K + 1), (-1) ^ (i + 1) * s ^ i
        / ((i + 1).factorial : ℝ) := by
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, expNegPoly, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow, pow_succ s i]
    ring
  rw [hP] at h
  rw [le_div_iff₀ hs]
  have e : (s⁻¹ + ∑ i ∈ Finset.range (2 * K + 1), (-1) ^ (i + 1) * s ^ i
      / ((i + 1).factorial : ℝ)) * s
      = 1 + s * ∑ i ∈ Finset.range (2 * K + 1), (-1) ^ (i + 1) * s ^ i
        / ((i + 1).factorial : ℝ) := by
    field_simp
  rw [e]
  linarith

/-- **The exponential integral from below by Taylor's polynomial**: for `0 < x₁ ≤ x₂`,
`log x₂ - log x₁ + einPoly (2K+1) x₂ - einPoly (2K+1) x₁ ≤ ∫_{x₁}^{x₂} e^{-s}/s ds`. -/
theorem ein_le_integral_exp_neg_div (K : ℕ) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) :
    Real.log x₂ - Real.log x₁ + einPoly (2 * K + 1) x₂ - einPoly (2 * K + 1) x₁
      ≤ ∫ s in x₁..x₂, Real.exp (-s) / s := by
  have hpos : ∀ s ∈ Set.uIcc x₁ x₂, 0 < s := fun s hs => by
    rw [Set.uIcc_of_le hx] at hs
    exact hx₁.trans_le hs.1
  set g : ℝ → ℝ := fun s =>
    s⁻¹ + ∑ i ∈ Finset.range (2 * K + 1), (-1) ^ (i + 1) * s ^ i / ((i + 1).factorial : ℝ)
    with hg
  have hgc : ContinuousOn g (Set.uIcc x₁ x₂) := by
    refine ContinuousOn.add (continuousOn_inv₀.mono fun s hs => (hpos s hs).ne') ?_
    exact (continuous_finsetSum _ fun i _ => by fun_prop).continuousOn
  have hd : ∀ s ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun s => Real.log s + einPoly (2 * K + 1) s) (g s) s :=
    fun s hs => (Real.hasDerivAt_log (hpos s hs).ne').add (hasDerivAt_einPoly (2 * K + 1) s)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hgc.intervalIntegrable
  have hle : ∫ s in x₁..x₂, g s ≤ ∫ s in x₁..x₂, Real.exp (-s) / s :=
    intervalIntegral.integral_mono_on hx hgc.intervalIntegrable
      (intervalIntegrable_exp_neg_div hx₁ hx) fun s hs => ein_le_exp_neg_div K (hx₁.trans_le hs.1)
  rw [hFTC] at hle
  linarith

/-- `log 3 + einPoly 9 3 ≥ -0.5916` (the value is `-0.59156…`). -/
lemma log_three_add_einPoly_ge : -0.5916 ≤ Real.log 3 + einPoly 9 3 := by
  have h := Real.log_three_gt_d9
  simp only [einPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  linarith

/-- `einPoly 9 a ≤ 0` for `0 ≤ a ≤ 1`. -/
lemma einPoly_nine_nonpos {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : einPoly 9 a ≤ 0 := by
  simp only [einPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  have h2 : a ^ 2 ≤ a := by nlinarith
  have h3 : a ^ 4 ≤ a ^ 3 := by nlinarith [pow_nonneg ha0 3]
  have h5 : a ^ 6 ≤ a ^ 5 := by nlinarith [pow_nonneg ha0 5]
  have h7 : a ^ 8 ≤ a ^ 7 := by nlinarith [pow_nonneg ha0 7]
  nlinarith [pow_nonneg ha0 3, pow_nonneg ha0 5, pow_nonneg ha0 7, pow_nonneg ha0 9]

/-- **The damped integral from below**: for `0 < 2σA ≤ 1` and `2σB ≥ 3`,
`∫_A^B e^{-2σu}/u du ≥ log(1/(2σA)) - 0.5916`. -/
theorem le_integral_exp_mul_div {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (ha : 2 * σ * A ≤ 1) (hB : 3 ≤ 2 * σ * B) :
    Real.log (1 / (2 * σ * A)) - 0.5916
      ≤ ∫ u in A..B, Real.exp (-(2 * σ) * u) / u := by
  have hc : 0 < 2 * σ := by positivity
  have ha0 : 0 < 2 * σ * A := by positivity
  rw [integral_exp_mul_div_eq_comp hc]
  have h3 : 2 * σ * A ≤ 3 := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp_neg_div ha0 h3) (intervalIntegrable_exp_neg_div (by norm_num) hB)
  have htail : 0 ≤ ∫ s in (3 : ℝ)..2 * σ * B, Real.exp (-s) / s :=
    intervalIntegral.integral_nonneg hB fun s hs => by
      have : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
      positivity
  have hT := ein_le_integral_exp_neg_div 4 ha0 h3
  have hE := log_three_add_einPoly_ge
  have hE0 := einPoly_nine_nonpos ha0.le ha
  rw [Real.log_div one_ne_zero ha0.ne', Real.log_one]
  norm_num at hT
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **`E‖F_{[c_k,y)}(s_σ)‖²e^k` from below**: for `k ≥ 20`, `σ > 0`, `2σe^k ≤ 1` and `n` full
blocks below the cutoff (`c_{k+n} ≤ y`) reaching the damping (`2σe^{k+n} ≥ 3`),
`E‖F_{[c_k,y)}(s_σ)‖²·e^k ≥ e^{-0.592}/(2σ)`. -/
theorem le_integral_normSq_high_mul_exp (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ : 0 < σ) {k n y : ℕ} (hk : 20 ≤ k) (hny : ⌊blockScale k n⌋₊ + 1 ≤ y)
    (ha : 2 * σ * Real.exp (k : ℝ) ≤ 1) (hℓ : 3 ≤ 2 * σ * Real.exp ((n : ℝ) + k)) :
    Real.exp (-0.592) / (2 * σ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ) := by
  have hc0 : scaleCut (k : ℝ) = ⌊blockScale k 0⌋₊ + 1 := rfl
  set t : ℕ → ℝ := fun p => (p : ℝ) ^ (-1 - 2 * σ) with ht
  have ht0 : ∀ p, 0 ≤ t p := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- the moment as a product, and the product from below
  have hprod : Real.exp (rangeCosSum (scaleCut (k : ℝ)) y σ 0 - rangeSqSum (scaleCut (k : ℝ)) y σ)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ := by
    rw [integral_normSq_Ico_eq_prod hX (scaleCut (k : ℝ)) y σ 0, rangeCosSum, rangeSqSum,
      ← Finset.sum_sub_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p _ => ?_
    have e : Real.cos (0 * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ) - ((p : ℝ) ^ (-1 - 2 * σ)) ^ 2
        = t p - t p ^ 2 := by simp [ht]
    rw [e]
    exact exp_sub_sq_le_one_add (ht0 p)
  -- the quadratic remainder
  have hsq : rangeSqSum (scaleCut (k : ℝ)) y σ ≤ 1 / 10 ^ 20 := by
    have h := rangeSqSum_rest_le (r := 0) (y := y) hk hσ.le
    rw [← hc0] at h
    linarith
  -- the linear sum over the full blocks
  have hcut : scaleCut (k : ℝ) ≤ ⌊blockScale k n⌋₊ + 1 := by
    rw [hc0]; exact cut_mono k (Nat.zero_le n)
  have hlin : ∑ m ∈ Finset.Ico 0 n, blockCosSum k σ 0 m
      ≤ rangeCosSum (scaleCut (k : ℝ)) y σ 0 := by
    rw [rangeCosSum_split hcut hny, hc0, rangeCosSum_cut_eq k (Nat.zero_le n) σ 0]
    have hrest : 0 ≤ rangeCosSum (⌊blockScale k n⌋₊ + 1) y σ 0 := by
      unfold rangeCosSum
      exact Finset.sum_nonneg fun p _ => by simp only [zero_mul, Real.cos_zero, one_mul]; positivity
    linarith
  have htel := abs_sum_blockCosSum_sub_integral_le_two_regime (τ := 0) (σ := σ) (θ := k)
    (Nat.zero_le n) le_rfl hσ.le (by simp)
  have herr : blockCosTelErr (k : ℝ) 0 0 ≤ 3.16 / 10 ^ 6 :=
    blockCosTelErr_le_numeral (by simp only [Nat.cast_zero, zero_add]; exact_mod_cast hk)
      le_rfl (by positivity)
  have hint : ∫ u in Real.exp (((0 : ℕ) : ℝ) + k)..Real.exp ((n : ℝ) + k),
        Real.cos (0 * u) * Real.exp (-(2 * σ) * u) / u
      = ∫ u in Real.exp (k : ℝ)..Real.exp ((n : ℝ) + k), Real.exp (-(2 * σ) * u) / u := by
    simp only [zero_mul, Real.cos_zero, one_mul, Nat.cast_zero, zero_add]
  rw [hint] at htel
  have hI := le_integral_exp_mul_div hσ (Real.exp_pos _) ha hℓ
  have hsum : Real.log (1 / (2 * σ * Real.exp (k : ℝ))) - 0.592
      ≤ rangeCosSum (scaleCut (k : ℝ)) y σ 0 - rangeSqSum (scaleCut (k : ℝ)) y σ := by
    have := (abs_le.1 htel).1
    linarith
  have hlog : Real.log (1 / (2 * σ * Real.exp (k : ℝ))) - 0.592
      = Real.log (Real.exp (-0.592) / (2 * σ * Real.exp (k : ℝ))) := by
    rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  rw [hlog] at hsum
  have hmain := le_trans (Real.exp_le_exp.2 hsum) hprod
  rw [Real.exp_log (by positivity)] at hmain
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * σ)]
  have hE : 0 < Real.exp (k : ℝ) := Real.exp_pos _
  calc Real.exp (-0.592) = Real.exp (-0.592) / (2 * σ * Real.exp (k : ℝ))
        * (2 * σ * Real.exp (k : ℝ)) := by field_simp
    _ ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * (2 * σ * Real.exp (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = _ := by ring

end High

/-! ### `N_q(k) = E‖F_{[0,c_k)}(σ)‖^{2q}` from below, `0 ≤ q ≤ ½`

Prime by prime, `E|1 + X u|^{2q} = ((1+u)^{2q} + (1-u)^{2q})/2 ≥ 1 + β log(1 - u²)`, `β = q(1-2q)`
(`RMF.one_add_log_le_rademacher_local`: the difference vanishes to first order at `u = 0` and is
convex, by Bernoulli twice), then `u² ≤ 1/p` and the chord of the concave `β ↦ log(1 + βL)` on
`[0, 1/8]`: `E|1 + X p^{-1/2-σ}|^{2q} ≥ exp(-β·w(p))`, `w(p) = -8log(1 + log(1 - 1/p)/8)`.  With
`w(2) ≤ ½ + 0.2289`, `w(3) ≤ ⅓ + 0.0836`, `w(p) ≤ 1/p + 0.84/p²` for `p ≥ 5`, and Mertens with
`M ≤ 0.2641`: `N_q(k) ≥ exp(-q(1-2q)(k + 0.7866 + 9.003e^{-k}))`. -/

section Low

/-- **The Rademacher local moment from below**: for `0 ≤ a ≤ 1` and `0 ≤ u < 1`,
`((1+u)^a + (1-u)^a)/2 ≥ 1 + (a(1-a)/2)·log(1 - u²)`. -/
theorem one_add_log_le_rademacher_local {a u : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u < 1) :
    1 + a * (1 - a) / 2 * Real.log (1 - u ^ 2) ≤ ((1 + u) ^ a + (1 - u) ^ a) / 2 := by
  set β : ℝ := a * (1 - a) / 2 with hβ
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ 1 - a := by linarith
    rw [hβ]; positivity
  -- the difference and its first two derivatives on `(-1, 1)`
  have hd1 : ∀ v : ℝ, -1 < v → v < 1 →
      HasDerivAt (fun v => ((1 + v) ^ a + (1 - v) ^ a) / 2 - 1 - β * Real.log (1 - v ^ 2))
        (a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1)) + β * (2 * v / (1 - v ^ 2))) v := by
    intro v hv1 hv2
    have hp : (0 : ℝ) < 1 + v := by linarith
    have hm : (0 : ℝ) < 1 - v := by linarith
    have hs : (0 : ℝ) < 1 - v ^ 2 := by nlinarith
    have h1 : HasDerivAt (fun v : ℝ => (1 + v) ^ a) (1 * a * (1 + v) ^ (a - 1)) v :=
      ((hasDerivAt_id' v).const_add 1).rpow_const (Or.inl hp.ne')
    have h2 : HasDerivAt (fun v : ℝ => (1 - v) ^ a) (-1 * a * (1 - v) ^ (a - 1)) v :=
      ((hasDerivAt_id' v).const_sub 1).rpow_const (Or.inl hm.ne')
    have h3 : HasDerivAt (fun v : ℝ => Real.log (1 - v ^ 2))
        (-((2 : ℕ) * v ^ (2 - 1)) / (1 - v ^ 2)) v :=
      ((hasDerivAt_pow 2 v).const_sub 1).log hs.ne'
    have h := (((h1.add h2).div_const 2).sub_const 1).sub (h3.const_mul β)
    refine h.congr_deriv ?_
    norm_num
    ring
  have hd2 : ∀ v : ℝ, -1 < v → v < 1 →
      HasDerivAt (fun v => a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1))
          + β * (2 * v / (1 - v ^ 2)))
        (a / 2 * ((a - 1) * (1 + v) ^ (a - 2) + (a - 1) * (1 - v) ^ (a - 2))
          + β * (2 * (1 + v ^ 2) / (1 - v ^ 2) ^ 2)) v := by
    intro v hv1 hv2
    have hp : (0 : ℝ) < 1 + v := by linarith
    have hm : (0 : ℝ) < 1 - v := by linarith
    have hs : (0 : ℝ) < 1 - v ^ 2 := by nlinarith
    have h1 : HasDerivAt (fun v : ℝ => (1 + v) ^ (a - 1)) (1 * (a - 1) * (1 + v) ^ (a - 1 - 1)) v :=
      ((hasDerivAt_id' v).const_add 1).rpow_const (Or.inl hp.ne')
    have h2 : HasDerivAt (fun v : ℝ => (1 - v) ^ (a - 1))
        (-1 * (a - 1) * (1 - v) ^ (a - 1 - 1)) v :=
      ((hasDerivAt_id' v).const_sub 1).rpow_const (Or.inl hm.ne')
    have hn : HasDerivAt (fun v : ℝ => 2 * v) (2 * 1) v := (hasDerivAt_id' v).const_mul 2
    have hdd : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-((2 : ℕ) * v ^ (2 - 1))) v :=
      (hasDerivAt_pow 2 v).const_sub 1
    have h3 := hn.div hdd hs.ne'
    have h := ((h1.sub h2).const_mul (a / 2)).add (h3.const_mul β)
    refine h.congr_deriv ?_
    rw [show a - 1 - 1 = a - 2 by ring]
    norm_num
    ring
  -- the second derivative is nonnegative on `[0, 1)`
  have hd2nn : ∀ v : ℝ, 0 ≤ v → v < 1 →
      0 ≤ a / 2 * ((a - 1) * (1 + v) ^ (a - 2) + (a - 1) * (1 - v) ^ (a - 2))
        + β * (2 * (1 + v ^ 2) / (1 - v ^ 2) ^ 2) := by
    intro v hv0 hv1
    have hp : (0 : ℝ) < 1 + v := by linarith
    have hm : (0 : ℝ) < 1 - v := by linarith
    have hbp : (1 + v) ^ a ≤ 1 + a * v :=
      rpow_one_add_le_one_add_mul_self (by linarith) ha0 ha1
    have hbm : (1 - v) ^ a ≤ 1 - a * v := by
      have h := rpow_one_add_le_one_add_mul_self (s := -v) (by linarith) ha0 ha1
      rw [← sub_eq_add_neg] at h
      linarith
    have ep : (1 + v) ^ (a - 2) = (1 + v) ^ a / (1 + v) ^ 2 := by
      rw [Real.rpow_sub hp, Real.rpow_two]
    have em : (1 - v) ^ (a - 2) = (1 - v) ^ a / (1 - v) ^ 2 := by
      rw [Real.rpow_sub hm, Real.rpow_two]
    have eq2 : 2 * (1 + v ^ 2) / (1 - v ^ 2) ^ 2 = 1 / (1 + v) ^ 2 + 1 / (1 - v) ^ 2 := by
      have h1 : (1 - v ^ 2) ^ 2 = (1 + v) ^ 2 * (1 - v) ^ 2 := by ring
      rw [h1]
      field_simp
      ring
    have hkey : (1 + v) ^ (a - 2) + (1 - v) ^ (a - 2) ≤ 1 / (1 + v) ^ 2 + 1 / (1 - v) ^ 2 := by
      rw [ep, em]
      have hA : 0 < (1 + v) ^ 2 := by positivity
      have hB : 0 < (1 - v) ^ 2 := by positivity
      have hAB : 1 / (1 + v) ^ 2 ≤ 1 / (1 - v) ^ 2 :=
        one_div_le_one_div_of_le hB (by nlinarith)
      have h1 : (1 + v) ^ a / (1 + v) ^ 2 ≤ (1 + a * v) / (1 + v) ^ 2 :=
        div_le_div_of_nonneg_right hbp hA.le
      have h2 : (1 - v) ^ a / (1 - v) ^ 2 ≤ (1 - a * v) / (1 - v) ^ 2 :=
        div_le_div_of_nonneg_right hbm hB.le
      have e1 : (1 + a * v) / (1 + v) ^ 2 = 1 / (1 + v) ^ 2 + a * v * (1 / (1 + v) ^ 2) := by
        ring
      have e2 : (1 - a * v) / (1 - v) ^ 2 = 1 / (1 - v) ^ 2 - a * v * (1 / (1 - v) ^ 2) := by
        ring
      have hav : 0 ≤ a * v := mul_nonneg ha0 hv0
      nlinarith [mul_le_mul_of_nonneg_left hAB hav]
    have e : a / 2 * ((a - 1) * (1 + v) ^ (a - 2) + (a - 1) * (1 - v) ^ (a - 2))
        + β * (2 * (1 + v ^ 2) / (1 - v ^ 2) ^ 2)
        = β * ((1 / (1 + v) ^ 2 + 1 / (1 - v) ^ 2)
          - ((1 + v) ^ (a - 2) + (1 - v) ^ (a - 2))) := by
      rw [eq2, hβ]
      ring
    rw [e]
    exact mul_nonneg hβ0 (by linarith)
  -- the first derivative is nonnegative on `[0, 1)`
  have hI : interior (Set.Ico (0 : ℝ) 1) = Set.Ioo 0 1 := interior_Ico
  have hmono1 : MonotoneOn (fun v => a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1))
      + β * (2 * v / (1 - v ^ 2))) (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun v hv => (hd2 v (by linarith [hv.1]) hv.2).continuousAt.continuousWithinAt)
      (fun v hv => ?_) (fun v hv => ?_)
    · rw [hI] at hv
      exact (hd2 v (by linarith [hv.1]) hv.2).differentiableAt.differentiableWithinAt
    · rw [hI] at hv
      rw [(hd2 v (by linarith [hv.1]) hv.2).deriv]
      exact hd2nn v hv.1.le hv.2
  have hd1nn : ∀ v : ℝ, 0 ≤ v → v < 1 →
      0 ≤ a / 2 * ((1 + v) ^ (a - 1) - (1 - v) ^ (a - 1)) + β * (2 * v / (1 - v ^ 2)) := by
    intro v hv0 hv1
    have h := hmono1 ⟨le_rfl, zero_lt_one⟩ ⟨hv0, hv1⟩ hv0
    simpa using h
  -- the difference is nonnegative on `[0, 1)`
  have hmono : MonotoneOn (fun v => ((1 + v) ^ a + (1 - v) ^ a) / 2 - 1
      - β * Real.log (1 - v ^ 2)) (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun v hv => (hd1 v (by linarith [hv.1]) hv.2).continuousAt.continuousWithinAt)
      (fun v hv => ?_) (fun v hv => ?_)
    · rw [hI] at hv
      exact (hd1 v (by linarith [hv.1]) hv.2).differentiableAt.differentiableWithinAt
    · rw [hI] at hv
      rw [(hd1 v (by linarith [hv.1]) hv.2).deriv]
      exact hd1nn v hv.1.le hv.2
  have h := hmono ⟨le_rfl, zero_lt_one⟩ ⟨hu0, hu1⟩ hu0
  simp only [add_zero, sub_zero, Real.one_rpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Real.log_one, mul_zero] at h
  linarith

/-- **The chord of `β ↦ log(1 + βL)` on `[0, 1/8]`**: `8β·log(1 + L/8) ≤ log(1 + βL)` for
`0 ≤ β ≤ 1/8` and `L > -8` (concavity of the logarithm). -/
lemma mul_log_le_log_one_add_mul {β L : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 8) (hL : -8 < L) :
    8 * β * Real.log (1 + L / 8) ≤ Real.log (1 + β * L) := by
  have hy : (0 : ℝ) < 1 + L / 8 := by linarith
  have ht0 : 0 ≤ 8 * β := by linarith
  have ht1 : 0 ≤ 1 - 8 * β := by linarith
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 hy)
    ht1 ht0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- The prime weight `w(p) = -8log(1 + log(1 - 1/p)/8)` of the lower bound for `N_q`. -/
noncomputable def lowPrimeWeight (p : ℕ) : ℝ := -8 * Real.log (1 + Real.log (1 - 1 / (p : ℝ)) / 8)

/-- **The local moment at a prime from below**: for `σ ≥ 0` and `0 ≤ q ≤ ½`,
`E|1 + X p^{-1/2-σ}|^{2q} ≥ exp(-q(1-2q)·w(p))`. -/
theorem exp_neg_mul_lowPrimeWeight_le {p : ℕ} (hp : p.Prime) {σ q : ℝ} (hσ : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    Real.exp (-(q * (1 - 2 * q)) * lowPrimeWeight p)
      ≤ ∫ z, ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q) ∂rademacherLaw := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hp0.le _
  have husq : u ^ 2 ≤ 1 / (p : ℝ) := by
    have h1 : u ^ 2 = (p : ℝ) ^ (-(1 + 2 * σ)) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    have h2 : (p : ℝ) ^ (-(1 + 2 * σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p) (by linarith)
    rw [h1, one_div, ← Real.rpow_neg_one]
    exact h2
  have hinv : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hu1 : u < 1 := by nlinarith
  rw [cpow_neg_shiftLine_zero p σ, integral_norm_one_add_mul_rpow_rademacherLaw_real hu0 hu1.le]
  have hD := one_add_log_le_rademacher_local (a := 2 * q) (u := u) (by linarith) (by linarith)
    hu0 hu1
  set β : ℝ := q * (1 - 2 * q) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg hq0 (by linarith)
  have hβ1 : β ≤ 1 / 8 := by nlinarith [sq_nonneg (q - 1 / 4)]
  have hβeq : 2 * q * (1 - 2 * q) / 2 = β := by rw [hβ]; ring
  rw [hβeq] at hD
  set L : ℝ := Real.log (1 - 1 / (p : ℝ)) with hL
  have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by linarith
  have hL0 : L ≤ 0 := Real.log_nonpos hpos.le (by linarith [one_div_pos.2 hp0])
  have hLlow : -1 ≤ L := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : (1 : ℝ) / 2 ≤ 1 - 1 / p)
    rw [one_div (2 : ℝ), Real.log_inv] at h
    rw [hL]
    linarith [Real.log_two_lt_d9]
  -- `log(1 - u²) ≥ log(1 - 1/p) = L`
  have hlog : L ≤ Real.log (1 - u ^ 2) :=
    Real.log_le_log hpos (by linarith)
  have hstep : 1 + β * L ≤ 1 + β * Real.log (1 - u ^ 2) := by nlinarith
  have hone : 0 < 1 + β * L := by nlinarith
  have hchord := mul_log_le_log_one_add_mul hβ0 hβ1 (by linarith : -8 < L)
  have hw : -(β) * lowPrimeWeight p = 8 * β * Real.log (1 + L / 8) := by
    rw [lowPrimeWeight, hL]
    ring
  rw [hw]
  calc Real.exp (8 * β * Real.log (1 + L / 8)) ≤ Real.exp (Real.log (1 + β * L)) :=
        Real.exp_le_exp.2 hchord
    _ = 1 + β * L := Real.exp_log hone
    _ ≤ _ := hstep.trans hD

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **`N_q` from below, prime by prime**: for `σ ≥ 0` and `0 ≤ q ≤ ½`,
`E‖F_{[0,c)}(σ)‖^{2q} ≥ exp(-q(1-2q)·∑_{p<c} w(p))`. -/
theorem exp_neg_mul_sum_lowPrimeWeight_le (hX : IsRademacherPrimeValues X μ) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (c : ℕ) :
    Real.exp (-(q * (1 - 2 * q)) * ∑ p ∈ primesIco 0 c, lowPrimeWeight p)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0 c
          (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  have hSp : ∀ p ∈ primesIco 0 c, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hbase : ∀ c : ℂ, Measurable fun z : ℂ => ‖1 + z * c‖ :=
    fun c => (measurable_const.add (measurable_id.mul measurable_const)).norm
  rw [integral_congr_ae (Filter.Eventually.of_forall
      (rpow_norm_randomEulerProductIco_eq_prod (X := X) 0 c (shiftLine σ 0) (2 * q))),
    hX.integral_prod hSp (fun p z => ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖ ^ (2 * q))
      fun p _ => ((hbase _).pow_const _).aestronglyMeasurable,
    Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le)
    fun p hp => exp_neg_mul_lowPrimeWeight_le (hSp p hp) hσ hq0 hq1

/-- `-log(1 - x) ≤ x + x²/2 + x³/(1 - x)` for `0 ≤ x < 1`. -/
lemma neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / 2 + x ^ 3 / (1 - x) := by
  have habs : |x| = x := abs_of_nonneg hx0
  have hlt : |x| < 1 := by rw [habs]; exact hx1
  have key := Real.abs_log_sub_add_sum_range_le hlt 2
  rw [habs] at key
  have h := (abs_le.1 key).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

/-- `w(p) ≤ ℓ + ℓ²/16 + ℓ³/(64(1 - ℓ/8))` for `ℓ = -log(1 - 1/p)`, `p ≥ 2`. -/
lemma lowPrimeWeight_le_of {p : ℕ} (hp : 2 ≤ p) {ℓ : ℝ}
    (hℓ : ℓ = -Real.log (1 - 1 / (p : ℝ))) :
    lowPrimeWeight p ≤ ℓ + ℓ ^ 2 / 16 + ℓ ^ 3 / (64 * (1 - ℓ / 8)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ, neg_nonneg]
    exact Real.log_nonpos hpos.le (by linarith [one_div_pos.2 (by linarith : (0 : ℝ) < p)])
  have hℓ1 : ℓ ≤ 1 := by
    have hp' : (1 : ℝ) / 2 ≤ 1 - 1 / p := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hp'
    rw [one_div (2 : ℝ), Real.log_inv] at h
    rw [hℓ]
    linarith [Real.log_two_lt_d9]
  have hy := neg_log_one_sub_le (x := ℓ / 8) (by positivity) (by linarith)
  have e : lowPrimeWeight p = 8 * -Real.log (1 - ℓ / 8) := by
    have e1 : 1 - ℓ / 8 = 1 + Real.log (1 - 1 / (p : ℝ)) / 8 := by
      rw [hℓ]
      ring
    rw [lowPrimeWeight, e1]
    ring
  rw [e]
  have e2 : 8 * (ℓ / 8 + (ℓ / 8) ^ 2 / 2 + (ℓ / 8) ^ 3 / (1 - ℓ / 8))
      = ℓ + ℓ ^ 2 / 16 + ℓ ^ 3 / (64 * (1 - ℓ / 8)) := by
    have : (1 : ℝ) - ℓ / 8 ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-- `w(2) ≤ ½ + 0.2289`. -/
lemma lowPrimeWeight_two_le : lowPrimeWeight 2 ≤ 1 / 2 + 0.2289 := by
  have h := lowPrimeWeight_le_of (p := 2) le_rfl (ℓ := Real.log 2) (by
    rw [show (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 2⁻¹ by norm_num, Real.log_inv, neg_neg])
  have hl1 := Real.log_two_lt_d9
  have hl0 := Real.log_two_gt_d9
  refine h.trans ?_
  have hsq : Real.log 2 ^ 2 ≤ 0.6931471808 ^ 2 := pow_le_pow_left₀ (by linarith) hl1.le 2
  have hcu : Real.log 2 ^ 3 ≤ 0.6931471808 ^ 3 := pow_le_pow_left₀ (by linarith) hl1.le 3
  have hden : 64 * (1 - 0.6931471808 / 8) ≤ 64 * (1 - Real.log 2 / 8) := by linarith
  have hfrac : Real.log 2 ^ 3 / (64 * (1 - Real.log 2 / 8))
      ≤ 0.6931471808 ^ 3 / (64 * (1 - 0.6931471808 / 8)) :=
    div_le_div₀ (by positivity) hcu (by norm_num) hden
  norm_num at hsq hfrac ⊢
  linarith

/-- `w(3) ≤ ⅓ + 0.0836`. -/
lemma lowPrimeWeight_three_le : lowPrimeWeight 3 ≤ 1 / 3 + 0.0836 := by
  have h := lowPrimeWeight_le_of (p := 3) (by norm_num) (ℓ := Real.log 3 - Real.log 2) (by
    rw [show (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = 2 / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
    ring)
  have hl1 := Real.log_three_lt_d9
  have hl0 := Real.log_two_gt_d9
  have hl3 := Real.log_three_gt_d9
  have hl2 := Real.log_two_lt_d9
  refine h.trans ?_
  set ℓ := Real.log 3 - Real.log 2 with hℓ
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓ1 : ℓ ≤ 0.4054651085 := by linarith
  have hsq : ℓ ^ 2 ≤ 0.4054651085 ^ 2 := pow_le_pow_left₀ hℓ0 hℓ1 2
  have hcu : ℓ ^ 3 ≤ 0.4054651085 ^ 3 := pow_le_pow_left₀ hℓ0 hℓ1 3
  have hden : 64 * (1 - 0.4054651085 / 8) ≤ 64 * (1 - ℓ / 8) := by linarith
  have hfrac : ℓ ^ 3 / (64 * (1 - ℓ / 8)) ≤ 0.4054651085 ^ 3 / (64 * (1 - 0.4054651085 / 8)) :=
    div_le_div₀ (by positivity) hcu (by norm_num) hden
  norm_num at hsq hfrac ⊢
  linarith

/-- `w(p) ≤ 1/p + 0.84/p²` for `p ≥ 5`. -/
lemma lowPrimeWeight_le_of_five_le {p : ℕ} (hp : 5 ≤ p) :
    lowPrimeWeight p ≤ 1 / p + 0.84 / (p : ℝ) ^ 2 := by
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  set v : ℝ := 1 / (p : ℝ) with hv
  have hv0 : 0 < v := by positivity
  have hv1 : v ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hp5
  have hℓ := neg_log_one_sub_le hv0.le (by linarith)
  set ℓ : ℝ := -Real.log (1 - v) with hℓdef
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef, neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  -- `ℓ ≤ v + 3v²/4`
  have hcube : v ^ 3 / (1 - v) ≤ v ^ 2 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [sq_nonneg v]
  have hℓv : ℓ ≤ v + 3 / 4 * v ^ 2 := by linarith
  have hℓv' : ℓ ≤ 23 / 20 * v := by nlinarith
  have hmain := lowPrimeWeight_le_of (by omega : 2 ≤ p) hℓdef
  -- the two corrections
  have h2 : ℓ ^ 2 ≤ (23 / 20) ^ 2 * v ^ 2 := by
    have := pow_le_pow_left₀ hℓ0 hℓv' 2
    nlinarith
  have hℓ8 : ℓ / 8 ≤ 23 / 800 := by nlinarith
  have h3 : ℓ ^ 3 / (64 * (1 - ℓ / 8)) ≤ ℓ ^ 2 * (23 / 100 / (64 * (1 - 23 / 800))) := by
    rw [div_le_iff₀ (by nlinarith)]
    have hl : ℓ ≤ 23 / 100 := by nlinarith
    have hA : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
    have hB : 64 * (1 - 23 / 800) ≤ 64 * (1 - ℓ / 8) := by linarith
    calc ℓ ^ 3 = ℓ ^ 2 * ℓ := by ring
      _ ≤ ℓ ^ 2 * (23 / 100) := mul_le_mul_of_nonneg_left hl hA
      _ = ℓ ^ 2 * (23 / 100 / (64 * (1 - 23 / 800))) * (64 * (1 - 23 / 800)) := by
          field_simp
      _ ≤ ℓ ^ 2 * (23 / 100 / (64 * (1 - 23 / 800))) * (64 * (1 - ℓ / 8)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
  have hv2 : 0.84 / (p : ℝ) ^ 2 = 0.84 * v ^ 2 := by
    rw [hv]
    field_simp
  rw [hv2]
  have hc : (23 / 20 : ℝ) ^ 2 * (1 / 16 + 23 / 100 / (64 * (1 - 23 / 800))) ≤ 0.09 := by
    norm_num
  nlinarith [sq_nonneg v]

open Classical in
/-- **The prime weights summed**: `∑_{p<c} w(p) ≤ ∑_{p<c} 1/p + 0.5225` (`p = 2, 3` exactly, the
rest by `0.84/p²` and `∑_{n≥5} n^{-2} ≤ 1/4`). -/
theorem sum_lowPrimeWeight_le (c : ℕ) :
    ∑ p ∈ primesIco 0 c, lowPrimeWeight p ≤ ∑ p ∈ primesIco 0 c, (1 : ℝ) / p + 0.5225 := by
  set S := primesIco 0 c with hS
  set b : ℕ → ℝ := fun p => if p = 2 then 0.2289 else if p = 3 then 0.0836
    else 0.84 / (p : ℝ) ^ 2 with hb
  have hb0 : ∀ p, 0 ≤ b p := fun p => by
    simp only [hb]
    split_ifs <;> positivity
  have hpt : ∀ p ∈ S, lowPrimeWeight p ≤ 1 / (p : ℝ) + b p := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    simp only [hb]
    split_ifs with h2 h3
    · subst h2
      have := lowPrimeWeight_two_le
      norm_num at this ⊢
      linarith
    · subst h3
      have := lowPrimeWeight_three_le
      norm_num at this ⊢
      linarith
    · have h5 : 5 ≤ p := by
        have h2' := hpp.two_le
        by_contra hlt
        interval_cases p
        · exact h2 rfl
        · exact h3 rfl
        · exact absurd hpp (by decide)
      exact lowPrimeWeight_le_of_five_le h5
  have hsub : S ⊆ {2, 3} ∪ Finset.Ico 5 c := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hpc : p < c := (mem_primesIco.1 hp).2.2
    rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico]
    by_cases h2 : p = 2
    · exact Or.inl (Or.inl h2)
    by_cases h3 : p = 3
    · exact Or.inl (Or.inr h3)
    refine Or.inr ⟨?_, hpc⟩
    have h2' := hpp.two_le
    by_contra hlt
    interval_cases p
    · exact h2 rfl
    · exact h3 rfl
    · exact absurd hpp (by decide)
  have hdisj : Disjoint ({2, 3} : Finset ℕ) (Finset.Ico 5 c) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Finset.mem_Ico] at hp'
    omega
  have hbS : ∑ p ∈ S, b p ≤ 0.5225 := by
    calc ∑ p ∈ S, b p ≤ ∑ p ∈ {2, 3} ∪ Finset.Ico 5 c, b p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hb0 p
      _ = b 2 + b 3 + ∑ p ∈ Finset.Ico 5 c, b p := by
          rw [Finset.sum_union hdisj, Finset.sum_pair (by norm_num)]
      _ = 0.2289 + 0.0836 + ∑ p ∈ Finset.Ico 5 c, 0.84 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
          have h2 : b 2 = 0.2289 := by simp [hb]
          have h3 : b 3 = 0.0836 := by simp [hb]
          have hs : ∑ p ∈ Finset.Ico 5 c, b p
              = ∑ p ∈ Finset.Ico 5 c, 0.84 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have h5 : 5 ≤ p := (Finset.mem_Ico.1 hp).1
            simp only [hb, if_neg (by omega : p ≠ 2), if_neg (by omega : p ≠ 3)]
            ring
          rw [h2, h3, hs]
      _ ≤ 0.2289 + 0.0836 + 0.84 * (1 / 4) := by
          rw [← Finset.mul_sum]
          have h := sum_inv_sq_Ico_le (m := 5) (by norm_num) c
          norm_num at h ⊢
          linarith
      _ = 0.5225 := by norm_num
  calc ∑ p ∈ S, lowPrimeWeight p ≤ ∑ p ∈ S, (1 / (p : ℝ) + b p) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ S, (1 : ℝ) / p + ∑ p ∈ S, b p := Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- **Mertens below the cut**: `∑_{p<c_k} 1/p ≤ k + 0.2641 + 9.003e^{-k}`
(`Mertens.sum_prime_div_eq` at `x = exp(e^k)`, `M ≤ 0.2641`). -/
theorem sum_inv_primesIco_scaleCut_le (k : ℕ) :
    ∑ p ∈ primesIco 0 (scaleCut (k : ℝ)), (1 : ℝ) / p
      ≤ k + 0.2641 + 9.003 / Real.exp (k : ℝ) := by
  set x : ℝ := blockScale (k : ℝ) 0 with hx
  have hlogx : Real.log x = Real.exp (k : ℝ) := by
    rw [hx, log_blockScale]
    simp
  have hx2 : (2 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ Real.exp (k : ℝ) := Real.one_le_exp (Nat.cast_nonneg k)
    have h2 : Real.exp 1 ≤ x := by
      rw [hx, blockScale]
      exact Real.exp_le_exp.2 (by rw [Nat.cast_zero, zero_add]; exact h1)
    linarith [Real.exp_one_gt_d9]
  have hS : primesIco 0 (scaleCut (k : ℝ)) = {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := by
    rw [primesIco_zero, scaleCut, primesBelow_succ_eq_filter_Ioc]
  have h := Mertens.sum_prime_div_eq x
  have hE : Mertens.E₂p x ≤ 9.003 / Real.exp (k : ℝ) := by
    rw [← hlogx]
    calc Mertens.E₂p x ≤ |Mertens.E₂p x| := le_abs_self _
      _ ≤ (Real.log 4 + 6 + Mertens.E₁) / Real.log x := Mertens.E₂p.abs_le hx2
      _ ≤ 9.003 / Real.log x := by
          have hl : 0 < Real.log x := by rw [hlogx]; exact Real.exp_pos _
          exact div_le_div_of_nonneg_right (by linarith [mertens_error_const_le]) hl.le
  rw [hS, h, hlogx, Real.log_exp]
  linarith [mertens_const_le]

/-- **`N_q(k)` from below**: for `σ ≥ 0` and `0 ≤ q ≤ ½`,
`E‖F_{[0,c_k)}(σ)‖^{2q} ≥ exp(-q(1-2q)(k + 0.7866 + 9.003e^{-k}))`. -/
theorem le_integral_rpow_norm_low (hX : IsRademacherPrimeValues X μ) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (k : ℕ) :
    Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ := by
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_neg_mul_sum_lowPrimeWeight_le hX hσ hq0 hq1 _)
  have hβ0 : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have h1 := sum_lowPrimeWeight_le (scaleCut (k : ℝ))
  have h2 := sum_inv_primesIco_scaleCut_le k
  have h3 : ∑ p ∈ primesIco 0 (scaleCut (k : ℝ)), lowPrimeWeight p
      ≤ (k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ) := by linarith
  nlinarith

end Low

/-! ### The sum over scales -/

section Sum

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The scale-`k` summand `1_S·mass_k^q` is integrable. -/
lemma integrable_indicator_rpow_headWindowMass (hX : IsRademacherPrimeValues X μ) {σ q : ℝ}
    (hσ : 0 ≤ σ) (hq0 : 0 ≤ q) {k r y : ℕ}
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) {S : Set Ω}
    (hSm : MeasurableSet S) :
    Integrable (fun ω => S.indicator (fun ω => headWindowMass X μ σ k r y ω ^ q) ω) μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hMm := aestronglyMeasurable_headWindowMass hX hσ hy
  refine (integrable_const ((Real.exp (2 * (k : ℝ)) / 2
    * ((∏ p ∈ primesIco 0 y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
      * volume.real (halfWindow k))) ^ q)).mono'
    (((hMm.aemeasurable.pow_const q).aestronglyMeasurable).indicator hSm) ?_
  filter_upwards [ae_headWindowMass_le hX hσ k r y] with ω hMle
  have hM0 := headWindowMass_nonneg X μ σ k r y ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ω' _ =>
    Real.rpow_nonneg (headWindowMass_nonneg X μ σ k r y ω') _) ω)]
  by_cases hm : ω ∈ S
  · rw [Set.indicator_of_mem hm]
    exact Real.rpow_le_rpow hM0 hMle hq0
  · rw [Set.indicator_of_notMem hm]
    exact Real.rpow_nonneg (le_trans hM0 hMle) _

end Sum

/-! ### The Rademacher symmetry

The values are real, so `‖F_{[0,y)}(½+σ-it)‖ = ‖F_{[0,y)}(½+σ+it)‖`
(`RMF.ae_forall_norm_randomEulerProduct_shiftLine_neg`): the line integral is twice its positive
half, and the windows all lie at positive heights — a free factor `2^q`. -/

section Symmetry

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The line integral is twice its positive half**, almost surely. -/
theorem ae_integral_lineDiv_eq_two_mul (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ}
    (hσ0 : 0 < σ) :
    ∀ᵐ ω ∂μ, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2)
      = 2 * ∫ u in Set.Ioi 0, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw 0 y,
    ae_forall_norm_randomEulerProduct_shiftLine_neg hX y σ] with ω hω0 hrefl
  have hω : ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1 := by
    simpa only [primesIco_zero] using hω0
  set g : ℝ → ℝ := fun u => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
    (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 with hg
  have hint : Integrable g := by
    simp only [hg]
    simp_rw [shiftLine_eq_half_add]
    exact integrable_line_div_sq_half_add hσ0 hω
  have heven : ∀ u, g (-u) = g u := by
    intro u
    simp only [hg, norm_div, div_pow]
    rw [hrefl u]
    congr 1
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
    ring
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
  rw [Set.compl_Ioi] at hsplit
  have hneg : ∫ u in Set.Iic (0 : ℝ), g u = ∫ u in Set.Ioi 0, g u := by
    have h := integral_comp_neg_Iic (0 : ℝ) g
    rw [neg_zero] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Iic fun u _ => (heven u).symm
  linarith

/-- **The masses, summed, are below half the line integral**, almost surely: the windows lie at
positive heights, and the line integral is twice its positive half. -/
theorem ae_sum_headWindowMass_le_half (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ0 : 0 < σ)
    {y : ℕ} {K : Finset ℕ} {r : ℕ → ℕ} (hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)))
    (hKy : ∀ k ∈ K, ⌊blockScale k (r k)⌋₊ + 1 ≤ y) :
    ∀ᵐ ω ∂μ, ∑ k ∈ K, headWindowMass X μ σ k (r k) y ω
      ≤ (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) / 2 := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw 0 y,
    ae_integral_lineDiv_eq_two_mul hX y hσ0] with ω hω0 htwo
  have hω : ∀ p ∈ Nat.primesBelow y, ‖X p ω‖ ≤ 1 := by
    simpa only [primesIco_zero] using hω0
  rw [htwo, mul_div_cancel_left₀ _ two_ne_zero]
  set F : ℝ → ℂ := fun t => randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
    (shiftLine σ t) ω with hF
  set F' : ℝ → ℂ := Set.indicator (Set.Ioi 0) F with hF'
  have hint0 : Integrable fun u : ℝ => ‖F u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [hF]
    simp_rw [shiftLine_eq_half_add]
    exact integrable_line_div_sq_half_add hσ0 hω
  have hF'eq : ∀ u : ℝ, ‖F' u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2
      = Set.indicator (Set.Ioi 0) (fun u => ‖F u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) u := by
    intro u
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [hF', Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [hF', Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      simp
  have hint : Integrable fun u : ℝ => ‖F' u / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
    simp_rw [hF'eq]
    exact hint0.indicator measurableSet_Ioi
  have hpos : ∀ k : ℕ, ∀ t ∈ halfWindow k, t ∈ Set.Ioi (0 : ℝ) := fun k t ht =>
    lt_of_lt_of_le (Real.exp_pos _) ht.1
  have hwin := sum_setIntegral_halfWindow_le_integral_div (K := K) (σ := σ) hσ0 (F := F')
    (f := fun k => Set.indicator (Set.Ioi 0) (fun h => (hp1Tube X μ y k (r k) σ h).indicator
      (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h) ω‖ ^ 2) ω))
    (fun k hk => (integrableOn_hp1Tube_normSq hX hσ0.le
      (primeBlockSub_subset_of_cut_le (hKy k hk)) ω).congr_fun
      (fun t ht => by beta_reduce; rw [Set.indicator_of_mem (hpos k t ht)]) measurableSet_Icc)
    (fun k _ t => Set.indicator_nonneg (fun _ _ => Set.indicator_nonneg
      (fun _ _ => by positivity) ω) t)
    (fun k _ t => by
      by_cases ht : t ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem ht, hF', Set.indicator_of_mem ht]
        by_cases hm : ω ∈ hp1Tube X μ y k (r k) σ t
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]
          positivity
      · rw [Set.indicator_of_notMem ht, hF', Set.indicator_of_notMem ht]
        simp)
    hint hKσ
  rw [integral_congr_ae (Filter.Eventually.of_forall hF'eq),
    integral_indicator measurableSet_Ioi] at hwin
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hwin
  rw [headWindowMass]
  congr 1
  exact setIntegral_congr_fun measurableSet_Icc fun t ht => by
    rw [Set.indicator_of_mem (hpos k t ht)]

/-- **The sum over scales with the Rademacher symmetry**: for `σ > 0`, `0 ≤ q ≤ 1`, scales
`k ∈ K` with `k₀ ≤ k`, `σ ≤ e^{-k}`, their blocks below the cutoff `y ≥ 3` and multiplicity two
(`k₂ - k₁ ≤ r(k₁)` for `k₁ + 2 ≤ k₂`), and lower bounds `γ_k ≤ E[1_{E(k)}mass_k^q]`,
`2^{2q-1}∑_{k∈K} γ_k ≤ E[(∫_ℝ ‖F_{[0,y)}(½+σ+iu)/(σ+iu)‖² du)^q]`. -/
theorem le_integral_rpow_integral_lineDiv_head_symm (hX : IsRademacherPrimeValues X μ) {σ : ℝ}
    (hσ0 : 0 < σ) {y : ℕ} (hy3 : 3 ≤ y) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {k₀ : ℕ}
    {K : Finset ℕ} {r : ℕ → ℕ} (hKσ : ∀ k ∈ K, σ ≤ Real.exp (-(k : ℝ)))
    (hK₀ : ∀ k ∈ K, k₀ ≤ k) (hmult : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ + 2 ≤ k₂ → k₂ - k₁ ≤ r k₁)
    (hKy : ∀ k ∈ K, ⌊blockScale k (r k)⌋₊ + 1 ≤ y) {γ : ℕ → ℝ}
    (hper : ∀ k ∈ K, γ k ≤ ∫ ω, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
      (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω ∂μ) :
    2 ^ (2 * q - 1) * ∑ k ∈ K, γ k
      ≤ ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hint : ∀ k ∈ K, Integrable (fun ω => (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
      (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω) μ := fun k hk =>
    integrable_indicator_rpow_headWindowMass hX hσ0.le hq0
      (primeBlockSub_subset_of_cut_le (hKy k hk))
      ((measurableSet_halfLadder hX σ k₀ k).inter (measurableSet_hp1After hX σ k (r k)))
  have hline : Integrable (fun ω => (∫ u : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q) μ := by
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have h := integrable_rpow_eulerProductLine_of_two_le hX (y := y') (by omega) hσ0 hq0
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    simp_rw [shiftLine_eq_half_add]
  have hpt : ∀ᵐ ω ∂μ, ∑ k ∈ K, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
        (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω
      ≤ 2 ^ (1 - 2 * q) * (∫ u : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q := by
    filter_upwards [ae_sum_headWindowMass_le_half hX hσ0 hKσ hKy] with ω hω
    have h1 := sum_indicator_rpow_le_mul_rpow_sum (K := K)
      (E := fun k => halfLadder X σ k₀ k ∩ hp1After X σ k (r k)) (m := 2)
      (fun x => by convert card_filter_mem_halfLadder_inter_hp1After_le_two X σ hK₀ hmult x)
      (a := fun k ω => headWindowMass X μ σ k (r k) y ω)
      (fun k ω => headWindowMass_nonneg X μ σ k (r k) y ω) hq0 hq1 ω
    refine h1.trans ?_
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    have hJ0 : 0 ≤ ∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have h3 := Real.rpow_le_rpow
      (Finset.sum_nonneg fun k _ => headWindowMass_nonneg X μ σ k (r k) y ω) hω hq0
    rw [Real.div_rpow hJ0 (by norm_num)] at h3
    calc (2 : ℝ) ^ (1 - q) * (∑ k ∈ K, headWindowMass X μ σ k (r k) y ω) ^ q
        ≤ 2 ^ (1 - q) * ((∫ u : ℝ, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ u) ω
              / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q / 2 ^ q) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 ^ (1 - 2 * q) * (∫ u : ℝ, ‖randomEulerProduct
            (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ u) ω
              / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q := by
          rw [show (1 : ℝ) - 2 * q = (1 - q) - q by ring,
            Real.rpow_sub (by norm_num : (0 : ℝ) < 2) (1 - q)]
          ring
  calc 2 ^ (2 * q - 1) * ∑ k ∈ K, γ k
      ≤ 2 ^ (2 * q - 1) * ∑ k ∈ K, ∫ ω, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
          (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω ∂μ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2 ^ (2 * q - 1) * ∫ ω, ∑ k ∈ K, (halfLadder X σ k₀ k ∩ hp1After X σ k (r k)).indicator
          (fun ω => headWindowMass X μ σ k (r k) y ω ^ q) ω ∂μ := by
        rw [integral_finsetSum K hint]
    _ ≤ 2 ^ (2 * q - 1) * ∫ ω, 2 ^ (1 - 2 * q) * (∫ u : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
            (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ :=
        mul_le_mul_of_nonneg_left
          (integral_mono_ae (integrable_finsetSum K hint) (hline.const_mul _) hpt)
          (by positivity)
    _ = ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
        rw [integral_const_mul, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          show 2 * q - 1 + (1 - 2 * q) = 0 by ring, Real.rpow_zero, one_mul]

end Symmetry

/-! ### The main term -/

section MainTerm

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The per-scale constant** at the producers' numerals, ladder length `K`:
`Γ(q, K) = c₃^{2-q}C₂^{-(1-q)}2^{-q}((1 - e^{-100})P₁)^{2-q}Q^{-(1-q)}` with `c₃ = c3FloorK q K`,
`C₂ = e^{2(1-q)+0.50001}`, `P₁ = 0.31689`, `Q = 6482`. -/
noncomputable def perScaleConst (q : ℝ) (K : ℕ) : ℝ :=
  c3FloorK q K ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
    * ((1 - Real.exp (-100)) * 0.31689) ^ (2 - q) * (6482 : ℝ) ^ (-(1 - q))

/-- The scale data at the maximal block count `r = T - k`: from `σe^T ≤ 1/200 < σe^{T+1}`,
`k + 2000 ≤ T` and `c_{T+7} ≤ y`, the hypotheses of
`RMF.le_integral_indicator_rpow_headWindowMass_numeral` and of `RMF.le_integral_normSq_high_mul_exp`
at `n = T + 7 - k`. -/
lemma scale_data_of_le {σ : ℝ} (hσ : 0 < σ) {T k y : ℕ} (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hkT : k ≤ T) :
    σ * Real.exp ((k : ℝ) + (T - k : ℕ)) ≤ 1 / 200
      ∧ 1 / 200 < σ * Real.exp ((k : ℝ) + (T - k : ℕ) + 1)
      ∧ ⌊blockScale k (T - k)⌋₊ + 1 ≤ y
      ∧ ⌊blockScale k (T + 7 - k)⌋₊ + 1 ≤ y
      ∧ 2 * σ * Real.exp (k : ℝ) ≤ 1
      ∧ 3 ≤ 2 * σ * Real.exp (((T + 7 - k : ℕ) : ℝ) + k)
      ∧ σ ≤ Real.exp (-(k : ℝ)) := by
  have hc1 : ((k : ℝ) + ((T - k : ℕ) : ℝ)) = T := by
    rw [Nat.cast_sub hkT]; ring
  have hc2 : (((T + 7 - k : ℕ) : ℝ) + k) = (T : ℝ) + 7 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hkT' : (k : ℝ) ≤ T := by exact_mod_cast hkT
  have hcut7 : ⌊blockScale k (T + 7 - k)⌋₊ + 1 ≤ y := by
    have h := scaleCut_add (k : ℝ) (T + 7 - k)
    rw [show (k : ℝ) + ((T + 7 - k : ℕ) : ℝ) = (T : ℝ) + 7 by rw [← hc2]; ring] at h
    rw [← h]
    exact hyT
  refine ⟨by rw [hc1]; exact hσT, by rw [hc1]; exact hσT',
    (cut_mono k (by omega : T - k ≤ T + 7 - k)).trans hcut7, hcut7, ?_, ?_, ?_⟩
  · have := Real.exp_le_exp.2 hkT'
    nlinarith
  · rw [hc2]
    have he6 : (300 : ℝ) ≤ Real.exp 6 := by
      have h := Real.exp_one_gt_d9
      have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h6]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) h.le 6]
    have e : Real.exp ((T : ℝ) + 7) = Real.exp ((T : ℝ) + 1) * Real.exp 6 := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos ((T : ℝ) + 1)]
  · have h1 : σ ≤ Real.exp (-(T : ℝ)) := by
      have e : σ = σ * Real.exp (T : ℝ) * Real.exp (-(T : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      rw [e]
      have h3 : 0 < Real.exp (-(T : ℝ)) := Real.exp_pos _
      nlinarith
    have h2 : Real.exp (-(T : ℝ)) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.2 (by linarith)
    linarith

/-- **The sum over scales with every producer plugged in**: for `0 < q ≤ ½ + 1/20`,
the ladder bottom `k₀ ≥ 20`, `T` maximal for the damping (`σe^T ≤ 1/200 < σe^{T+1}`), the cutoff
`y ≥ c_{T+7}`, scales `k ∈ K` in `(k₀, T - 2000]` (and `k - k₀ ≤ K_max(q)` below `½`), and the
maximal block counts `r = T - k`, with the Rademacher symmetry:
`2^{2q-1}∑_{k ∈ K} Γ(q, k - k₀)·N_q(k)·(E‖F_{[c_k,y)}(s_σ)‖²e^k/√(T - k))^q
  ≤ E[(∫_ℝ ‖F_{[0,y)}(½+σ+it)/(σ+it)‖² dt)^q]`. -/
theorem le_integral_rpow_integral_lineDiv_numeral (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 2000 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q) :
    2 ^ (2 * q - 1) * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q
      ≤ ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  have hy3 : 3 ≤ y := by
    have h5 : 5 ≤ scaleCut ((T : ℝ) + 7) :=
      five_le_scaleCut (by linarith [Nat.cast_nonneg (α := ℝ) T])
    omega
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  refine le_integral_rpow_integral_lineDiv_head_symm hX hσ hy3 hq0.le (by linarith) (k₀ := k₀)
    (r := fun k => T - k) (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.2.2.2.2)
    (fun k hk => (hK k hk).1.le) (fun k₁ _ k₂ hk₂ _ => by have := hkT k₂ hk₂; omega)
    (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.1) fun k hk => ?_
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
  exact le_integral_indicator_rpow_headWindowMass_numeral hX hσ.le hq0 hq1 hk₀ (hK k hk).1
    (hKq k hk) h1 h2 h3 (by have := (hK k hk).2; omega)

/-- **The main term with `E‖F_high‖²e^k` explicit**: under the hypotheses of
`RMF.le_integral_rpow_integral_lineDiv_numeral` and `σL = V` (`L = log x`, `σ = V/log x`),
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀)·N_q(k)·(T - k)^{-q/2}
  ≤ L^{-q}E[(∫_ℝ ‖F_{[0,y)}(½+σ+it)/(σ+it)‖² dt)^q]`, `G = e^{-0.592}/2 ≈ 0.2766`
(`RMF.le_integral_normSq_high_mul_exp`). -/
theorem le_rpow_mul_integral_rpow_integral_lineDiv_numeral (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 2000 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          y (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  have hmain := le_integral_rpow_integral_lineDiv_numeral hX hσ hq0 hq1 hk₀ hσT hσT' hyT hK hKq
  have hV : 0 < V := by rw [← hσV]; positivity
  set G : ℝ := Real.exp (-0.592) / 2 with hG
  have hG0 : 0 < G := by positivity
  have hLq : 0 < L ^ (-q) := Real.rpow_pos_of_pos hL _
  -- per scale: `(E‖F_high‖²e^k/√r)^q ≥ (G/σ)^q r^{-q/2}`
  have hper : ∀ k ∈ K, (G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    intro k hk
    obtain ⟨-, -, -, h4, h5, h6, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
    have hk20 : 20 ≤ k := by have := (hK k hk).1; omega
    have hE := le_integral_normSq_high_mul_exp hX hσ hk20 h4 h5 h6
    have hr0 : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have := (hK k hk).2
      exact_mod_cast (by omega : 0 < T - k)
    have hsq : 0 < √((T - k : ℕ) : ℝ) := Real.sqrt_pos.2 hr0
    have hG2 : G / σ = Real.exp (-0.592) / (2 * σ) := by rw [hG]; field_simp
    have hmono : G / σ / √((T - k : ℕ) : ℝ)
        ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by rw [hG2]; exact hE) hsq.le
    have hrpow := Real.rpow_le_rpow (by positivity) hmono hq0.le
    refine le_trans (le_of_eq ?_) hrpow
    rw [Real.div_rpow (by positivity) hsq.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le,
      Real.rpow_neg hr0.le, div_eq_mul_inv]
    congr 2
    ring_nf
  have hN0 : ∀ k ∈ K, 0 ≤ perScaleConst q (k - k₀)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ) := by
    intro k hk
    have hc3 := c3FloorK_pos hq0.le (by linarith) (k - k₀)
    refine mul_nonneg ?_ (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    unfold perScaleConst
    have : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
    positivity
  have hsum : (G / σ) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    calc (G / σ) ^ q * (perScaleConst q (k - k₀)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
        = perScaleConst q (k - k₀)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hper k hk) (hN0 k hk)
  have hGV : L ^ (-q) * (G / σ) ^ q = (G / V) ^ q := by
    rw [← hσV, Real.rpow_neg hL.le, ← Real.inv_rpow hL.le,
      ← Real.mul_rpow (inv_nonneg.2 hL.le) (by positivity)]
    congr 1
    field_simp
  have h2 : (0 : ℝ) < 2 ^ (2 * q - 1) := by positivity
  calc 2 ^ (2 * q - 1) * (G / V) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      = L ^ (-q) * (2 ^ (2 * q - 1) * ((G / σ) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))) := by
        rw [← hGV]; ring
    _ ≤ L ^ (-q) * (2 ^ (2 * q - 1) * ∑ k ∈ K, perScaleConst q (k - k₀)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum h2.le) hLq.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain hLq.le

/-- **The main term, fully explicit, `0 < q ≤ ½`**: `N_q(k) ≥ exp(-q(1-2q)(k + 0.7866 +
9.003e^{-k}))` (`RMF.le_integral_rpow_norm_low`) in
`RMF.le_rpow_mul_integral_rpow_integral_lineDiv_numeral`:
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀)e^{-q(1-2q)(k + 0.7866 + 9.003e^{-k})}(T - k)^{-q/2}
  ≤ L^{-q}E[(∫_ℝ ‖F_{[0,y)}(½+σ+it)/(σ+it)‖² dt)^q]`, `G = e^{-0.592}/2`. -/
theorem le_rpow_mul_integral_rpow_integral_lineDiv_explicit (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 2000 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q * ∑ k ∈ K, perScaleConst q (k - k₀)
        * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          y (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  refine le_trans ?_ (le_rpow_mul_integral_rpow_integral_lineDiv_numeral hX hσ hq0
    (by linarith) hk₀ hσT hσT' hyT hK hKq hL hσV)
  have hV : 0 < V := by rw [← hσV]; positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by positivity)
  have hc3 := c3FloorK_pos hq0.le (by linarith) (k - k₀)
  have hΓ : 0 ≤ perScaleConst q (k - k₀) := by
    unfold perScaleConst
    have : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
    positivity
  have hN := le_integral_rpow_norm_low (X := X) (μ := μ) hX hσ.le hq0.le hq1 k
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hΓ) ?_
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end MainTerm

end RMF
