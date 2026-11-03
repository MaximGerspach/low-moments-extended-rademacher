/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2Prefix
import RMF.UniformLower.ComparisonFloor

/-!
# HP2's prefix bound at the floor `20`, as a function of the depth

HP2's prefix term `E'_h[1_{H(k,h)}e^{2Z_M}(max(b - Z_M, 0) + c)²]` is at most one function
`RMF.hp2PrefixBound M c` of the depth, for every `h ∈ halfWindow k` and `k ≥ 20`, with every
block-data hypothesis discharged (`RMF.integral_hp1Tube_exp_mul_sq_le_hp2PrefixBound`).

* **One slab from `k ≥ 20`** (`RMF.tiltedMeasure_hp2Tube_slab_le_floor`): the comparison
  `RMF.exists_isGaussianWalk_rademacher_budget` with the envelope `800(m+1)`, the barriers inside
  `400j` (`a + A + B + ρ ≤ 398`).
* **Slabs of width `w`** (`RMF.integral_hp2Tube_exp_mul_le_width`): the comparison's widening
  costs `(1 + 4e^{-40}/w)²`, at most `1 + e^{-30}` at `w = 1/16`; the Abel sum `K₂(w, c)` in closed
  form (`RMF.slabAbelTwo`), `K₂(1/16, c) ≤ 0.532c³ + 0.8488c² + 0.8499c + 0.425`.
* **The pointwise bound for `c ≥ 1`**: `e^{2t}c²` (`RMF.exp_mul_sq_le_of_one_le`).
* **The block data on the window**: `V_i ≤ 0.6801`, so `c ≥ √(πV_i/2)` for `c ≥ 1.05`
  (`RMF.sqrt_pi_windowVarH_div_two_le`); `V_i ≥ RMF.hp2VarLo M i`, summed over the thirds into
  `RMF.hp2VarSum₁`, `₂`, `₃` (`RMF.hp2VarSums_le`), with closed forms `RMF.hp2VarSums_ge`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### One slab at the floor `20` -/

section FloorSlab

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The barrier envelope `400j` holds the tube's barriers at a block `j ≥ 1` whose summed mean is
at most `1.52j` in size, once `a, A, B, ρ ≥ 0` sum to at most `398`. -/
lemma hp2_envelope_floor {Mn a A B ρ : ℝ} {j : ℕ} (hj : 1 ≤ j) (hMn : |Mn| ≤ 1.52 * j)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (henv : a + A + B + ρ ≤ 398) :
    -(400 * (j : ℝ)) ≤ Mn - A - B * j - ρ ∧ Mn + a + ρ ≤ 400 * (j : ℝ) := by
  have hS := abs_le.1 hMn
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by linarith
  have h1 : (A + B + ρ) * j ≤ 398 * j := mul_le_mul_of_nonneg_right (by linarith) hj0
  have h2 : A + ρ ≤ (A + ρ) * j := le_mul_of_one_le_right (by linarith) hj1
  have h3 : (a + ρ) * j ≤ 398 * j := mul_le_mul_of_nonneg_right (by linarith) hj0
  have h4 : a + ρ ≤ (a + ρ) * j := le_mul_of_one_le_right (by linarith) hj1
  constructor <;> linarith

/-- **One slab of the prefix tube, from `k ≥ 20`.**  For `M ≥ 3`, tube parameters
`a, A, B, ρ ≥ 0` summing to at most `398`, `c ≥ √(πV_i/2)` and `0 < S₁, S₂, S₃` below the variance
sums over the thirds, under the one-point tilt at `s_h` the tube with
`Z_M ∈ [a + ρ - d - w, a + ρ - d]` has probability at most
`(1 + e^{-100})(a + ρ + 2e^{-40} + c)(d + w' + c)w'·2/(π√(2πS₁S₂S₃))`, `w' = w + 4e^{-40}`: the
comparison `RMF.exists_isGaussianWalk_rademacher_budget` (envelope `800(m+1)`, budget
`RMF.hp2Prefix_budget`), the upper slack lemma at `2e^{-40}`, the floor dropped and the exact slab
ballot `RMF.IsGaussianWalk.measureReal_survive_slab_le_third`. -/
theorem tiltedMeasure_hp2Tube_slab_le_floor (hX : IsRademacherPrimeValues X μ) {k M y : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσM : σ * Real.exp ((k : ℝ) + M) ≤ 1 / 200)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) (hM : 3 ≤ M)
    {a A B ρ c S₁ S₂ S₃ d w : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (henv : a + A + B + ρ ≤ 398) (hc0 : 0 < c)
    (hc : ∀ i, i < M → √(π * windowVarH X μ y k σ h i / 2) ≤ c)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hS₃ : 0 < S₃)
    (h₁ : S₁ ≤ ∑ i ∈ Finset.range (M / 3), windowVarH X μ y k σ h i)
    (h₂ : S₂ ≤ ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), windowVarH X μ y k σ h i)
    (h₃ : S₃ ≤ ∑ i ∈ Finset.Ico (M - M / 3) M, windowVarH X μ y k σ h i)
    (hd : 0 ≤ d) (hw : 0 ≤ w) :
    (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ).real
        (hp2Tube X μ y k M σ h a A B ρ ∩
          {ω | a + ρ - d - w ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - d})
      ≤ (1 + Real.exp (-100)) * ((a + ρ + 2 * Real.exp (-40) + c)
          * (d + (w + 4 * Real.exp (-40)) + c) * (w + 4 * Real.exp (-40))
          * (2 / (π * √(2 * π * (S₁ * S₂ * S₃))))) := by
  classical
  /- basic facts -/
  have hk' : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs₁ : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs₁
  have hσm : ∀ m, m < M → σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200 := fun m hm =>
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      have : ((m : ℝ) + 1) ≤ M := by exact_mod_cast hm
      linarith)) hσ) hσM
  have hin : ∀ m, m < M →
      1 / 100 ≤ windowVarH X μ y k σ h m ∧ windowVarH X μ y k σ h m ≤ 10 :=
    fun m hm => (window_block_comparison_inputs hX y hk hh hσ (hσm m hm) (hy m hm)).1
  /- the height means: at most `1.52` per block -/
  have hmean : ∀ i, i < M → |windowMeanH X μ y k σ h i| ≤ 1.52 :=
    fun i hi => (abs_window_block_means_le hX y hk hh hσ (hσm i hi) (hy i hi)).1
  have hsum : ∀ j, j ≤ M → |∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i| ≤ 1.52 * j := by
    intro j hj
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun i hi =>
      hmean i (by have := Finset.mem_range.1 hi; omega)) (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  /- the windows `e^{-40}/(m+1)²` and the envelopes -/
  have hwpos : ∀ m, 0 < Real.exp (-40) * blockWindow m := fun m => by
    unfold blockWindow; positivity
  have hwle : ∀ m : ℕ, Real.exp (-40) * blockWindow m ≤ 1 := by
    intro m
    have h1 : Real.exp (-40) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have h2 : blockWindow m ≤ 1 := by
      unfold blockWindow
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      nlinarith
    have h3 : 0 ≤ blockWindow m := by unfold blockWindow; positivity
    calc Real.exp (-40) * blockWindow m ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
      _ = 1 := one_mul 1
  have hwsum : ∀ j, j ≤ M →
      ∑ m ∈ Finset.range j, Real.exp (-40) * blockWindow m ≤ 2 * Real.exp (-40) :=
    fun j _ => by
      have := sum_mul_blockWindow_le (Real.exp_pos (-40)).le 0 j
      simpa only [add_zero] using this
  have hM0 : ∀ j : ℕ, 0 ≤ 400 * (j : ℝ) := fun j => by positivity
  have hMM : ∀ m, m < M → 400 * (m : ℝ) + 400 * ((m + 1 : ℕ) : ℝ)
      + Real.exp (-40) * blockWindow m ≤ 800 * ((m : ℝ) + 1) := by
    intro m _
    have hw1 := hwle m
    push_cast
    linarith
  /- the comparison (`RMF.exists_isGaussianWalk_rademacher_budget`) at offset `k` -/
  have hσtop : |σ| * Real.log (blockScale (k : ℝ) M) ≤ 1 := by
    rw [abs_of_nonneg hσ, log_blockScale, show (M : ℝ) + k = k + M by ring]
    linarith
  obtain ⟨Ω', mΩ', Q, G, N, v, hQ, hG, hNm, hNG, hvdef, hvl, -, hcmpk⟩ :=
    exists_isGaussianWalk_rademacher_budget hX (θ := (k : ℝ)) (σ := σ) (vl := 1 / 100)
      (K := 1.52) (r := M) (y := y) (s := shiftLine σ h) (u := shiftLine σ h)
      (w := fun m => Real.exp (-40) * blockWindow m)
      (M := fun m => 800 * ((m : ℝ) + 1)) hk' hy (re_shiftLine σ h) (re_shiftLine σ h)
      hσtop (fun m _ => ⟨hwpos m, hwle m⟩) le_rfl (fun m hm => hin m hm)
      (fun m hm => hmean m hm) (fun m _ => hp2Prefix_budget hk' (by norm_num) le_rfl m)
  haveI := hQ
  have hcmp0 : IsWindowComparison
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ) Q
      (halfBlock X k σ h) N (fun m => Real.exp (-40) * blockWindow m)
      (fun m => 800 * ((m : ℝ) + 1)) M (Real.exp (-100)) := by
    have h0 := hcmpk 0 (Nat.zero_le M)
    simp only [add_zero, Nat.sub_zero] at h0
    exact h0
  /- the Gaussian walk's block data -/
  have hvm : ∀ i, i < M → ((v i : ℝ≥0) : ℝ) = windowVarH X μ y k σ h i := fun i hi => by
    rw [hvdef i, blockGaussVarAddLt_of_lt hi]
    rfl
  have hwalkN : ∀ j, j ≤ M → ∀ ω, walk N j ω
      = walk G j ω + ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i := by
    intro j hj ω
    have hsumj : ∑ i ∈ Finset.range j,
          blockGaussMeanAddLt X μ (k : ℝ) y M (shiftLine σ h)
            (fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) i
        = ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i :=
      sum_blockGaussMeanAddLt_eq X μ (k : ℝ) y M (shiftLine σ h) _ hj
    rw [walk_apply, walk_apply, ← hsumj, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hNG i ω
  /- the slab as a barrier event, and the slack lemma -/
  obtain ⟨u, hu⟩ : ∃ f : ℕ → ℝ, f = fun j =>
      if j = M then max (∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i - A - B * M - ρ)
        (∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + a + ρ - d - w)
      else ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ f : ℕ → ℝ, f = fun j =>
      if j = M then ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + a + ρ - d
      else ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ := ⟨_, rfl⟩
  have hsubR : hp2Tube X μ y k M σ h a A B ρ ∩
      {ω | a + ρ - d - w ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - d}
      ⊆ barrierEvent (halfBlock X k σ h) M u v' := by
    have h1 : hp2Tube X μ y k M σ h a A B ρ ∩
        {ω | a + ρ - d - w ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - d}
        ⊆ hp2Tube X μ y k M σ h a A B ρ ∩
          {ω | ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + a + ρ - d - w
              ≤ walk (halfBlock X k σ h) M ω
            ∧ walk (halfBlock X k σ h) M ω
              ≤ ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + a + ρ - d} := by
      rintro ω ⟨hT, hlo, hhi⟩
      refine ⟨hT, ?_, ?_⟩ <;> unfold windowZ at hlo hhi <;> linarith
    refine h1.trans ?_
    rw [hu, hv']
    exact barrierEvent_inter_slab_subset
  have henvuv : ∀ j, 1 ≤ j → j ≤ M → -(400 * (j : ℝ)) ≤ u j ∧ v' j ≤ 400 * (j : ℝ) := by
    intro j hj1 hjM
    have hE := hp2_envelope_floor hj1 (hsum j hjM) ha hA hB hρ henv
    rw [hu, hv']
    simp only
    by_cases hj : j = M
    · rw [if_pos hj, if_pos hj]
      rw [hj] at hE
      rw [hj]
      exact ⟨le_trans hE.1 (le_max_left _ _), by linarith [hE.2]⟩
    · rw [if_neg hj, if_neg hj]
      exact hE
  have hslack := measure_barrierEvent_le_slack
    (P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
    (Q := Q) (X := halfBlock X k σ h) (N := N)
    (w := fun m => Real.exp (-40) * blockWindow m) (M := fun j => 400 * (j : ℝ))
    (M' := fun m => 800 * ((m : ℝ) + 1)) (u := u) (v := v') (n := M)
    (ε := Real.exp (-100)) (ρ := 2 * Real.exp (-40))
    (measurable_halfBlock hX _ _ _) hNm hwpos hwsum hM0 henvuv (Real.exp_pos _).le hMM hcmp0
  /- the Gaussian side: the floor dropped, the exact slab ballot -/
  have hsubG : barrierEvent N M (fun j => u j - 2 * Real.exp (-40))
        (fun j => v' j + 2 * Real.exp (-40))
      ⊆ {ω | (∀ j ≤ M, walk G j ω ≤ a + ρ + 2 * Real.exp (-40))
        ∧ a + ρ + 2 * Real.exp (-40) - d - (w + 4 * Real.exp (-40)) ≤ walk G M ω
        ∧ walk G M ω ≤ a + ρ + 2 * Real.exp (-40) - d} := by
    intro ω hω
    have hvj : ∀ j, 1 ≤ j → j ≤ M →
        v' j ≤ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + (a + ρ) := by
      intro j _ _
      rw [hv']
      dsimp only
      split_ifs with hj
      · rw [hj]; linarith
      · linarith
    have hvM : v' M = ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + (a + ρ) - d := by
      rw [hv']
      dsimp only
      rw [if_pos rfl]
      ring
    have hmax := le_max_right
      (∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i - A - B * M - ρ)
      (∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + a + ρ - d - w)
    have huM : ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i + (a + ρ) - d - w ≤ u M := by
      rw [hu]
      dsimp only
      rw [if_pos rfl]
      linarith
    have hmain := walk_slab_of_mem_barrierEvent (N := N) (G := G) (M := M)
      (m := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i) (u := u) (v := v')
      (t := a + ρ) (s := 2 * Real.exp (-40)) (d := d) (w := w) (by omega) hwalkN hvj hvM huM
      (by positivity) hω
    obtain ⟨hA1, hA2, hA3⟩ := hmain
    refine ⟨hA1, ?_, hA3⟩
    linarith
  have hvne : ∀ i, i < M → v i ≠ 0 := fun i _ h0 => by
    have h1 := hvl i
    rw [h0, NNReal.coe_zero] at h1
    norm_num at h1
  have hcv : ∀ i, i < M → √(π * (v i : ℝ) / 2) ≤ c := fun i hi => by
    rw [hvm i hi]
    exact hc i hi
  have h₁' : S₁ ≤ ∑ i ∈ Finset.range (M / 3), ((v i : ℝ≥0) : ℝ) :=
    h₁.trans (le_of_eq (Finset.sum_congr rfl fun i hi =>
      (hvm i (by have := Finset.mem_range.1 hi; omega)).symm))
  have h₂' : S₂ ≤ ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), ((v i : ℝ≥0) : ℝ) :=
    h₂.trans (le_of_eq (Finset.sum_congr rfl fun i hi =>
      (hvm i (by have := (Finset.mem_Ico.1 hi).2; omega)).symm))
  have h₃' : S₃ ≤ ∑ i ∈ Finset.Ico (M - M / 3) M, ((v i : ℝ≥0) : ℝ) :=
    h₃.trans (le_of_eq (Finset.sum_congr rfl fun i hi =>
      (hvm i (Finset.mem_Ico.1 hi).2).symm))
  have hball := hG.measureReal_survive_slab_le_third hvne hc0 hcv
    (y := a + ρ + 2 * Real.exp (-40)) (d := d) (w := w + 4 * Real.exp (-40))
    (by positivity) (by positivity) (by positivity) hM hS₁ hS₂ hS₃ h₁' h₂' h₃'
  /- assembled -/
  have hε0 : 0 ≤ 1 + Real.exp (-100) := by positivity
  calc (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ).real
        (hp2Tube X μ y k M σ h a A B ρ ∩
          {ω | a + ρ - d - w ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - d})
      ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
          (barrierEvent (halfBlock X k σ h) M u v')).toReal :=
        measureReal_mono hsubR
    _ ≤ (1 + Real.exp (-100)) * (Q (barrierEvent N M (fun j => u j - 2 * Real.exp (-40))
          (fun j => v' j + 2 * Real.exp (-40)))).toReal := hslack
    _ ≤ (1 + Real.exp (-100)) * Q.real {ω | (∀ j ≤ M, walk G j ω ≤ a + ρ + 2 * Real.exp (-40))
        ∧ a + ρ + 2 * Real.exp (-40) - d - (w + 4 * Real.exp (-40)) ≤ walk G M ω
        ∧ walk G M ω ≤ a + ρ + 2 * Real.exp (-40) - d} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubG) hε0
    _ ≤ _ := mul_le_mul_of_nonneg_left hball hε0

end FloorSlab

/-! ### Slabs of width `w` -/

section WidthSlabs

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **The weight on a set, by slabs of width `w`.**  If `lo ≤ Z ≤ t` on `T`, `w > 0`,
`t - lo < Lw`, `b ≤ t` and `c ≥ 0`, then `1_T e^{2Z}(max(b - Z, 0) + c)^j` is at most
`∑_{ℓ<L} 1_{T ∩ {t - (ℓ+1)w ≤ Z ≤ t - ℓw}}·e^{2(t-ℓw)}(ℓw + w + c)^j`. -/
lemma indicator_le_sum_slab_width {T : Set Ω} {Z : Ω → ℝ} {t lo b c w : ℝ} {j L : ℕ}
    (hT : ∀ ω ∈ T, lo ≤ Z ω ∧ Z ω ≤ t) (hw : 0 < w) (hL : t - lo < L * w) (hb : b ≤ t)
    (hc : 0 ≤ c) (ω : Ω) :
    T.indicator (fun ω => Real.exp (2 * Z ω) * (max (b - Z ω) 0 + c) ^ j) ω
      ≤ ∑ ℓ ∈ Finset.range L,
          (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}).indicator
            (fun _ => Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j) ω := by
  have hnn : ∀ ℓ ∈ Finset.range L,
      0 ≤ (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}).indicator
        (fun _ => Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j) ω :=
    fun ℓ _ => Set.indicator_nonneg (fun _ _ => mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (by positivity) j)) ω
  by_cases hω : ω ∈ T
  · rw [Set.indicator_of_mem hω]
    obtain ⟨hlo, hhi⟩ := hT ω hω
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (t - Z ω) / w := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg (by linarith) hw.le
    have huw : u * w = t - Z ω := by rw [hu]; field_simp
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = ⌊u⌋₊ := ⟨_, rfl⟩
    have h1 : (ℓ : ℝ) ≤ u := by rw [hℓ]; exact Nat.floor_le hu0
    have h2 : u < (ℓ : ℝ) + 1 := by rw [hℓ]; exact Nat.lt_floor_add_one u
    have huL : u < L := by
      rw [hu, div_lt_iff₀ hw]
      linarith
    have hℓL : ℓ < L := by rw [hℓ]; exact (Nat.floor_lt hu0).2 huL
    have h1w : (ℓ : ℝ) * w ≤ t - Z ω := by
      rw [← huw]; exact mul_le_mul_of_nonneg_right h1 hw.le
    have h2w : t - Z ω < ((ℓ : ℝ) + 1) * w := by
      rw [← huw]; exact mul_lt_mul_of_pos_right h2 hw
    have hmem : ω ∈ T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w} :=
      ⟨hω, by linarith, by linarith⟩
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_range.2 hℓL))
    rw [Set.indicator_of_mem hmem]
    have he : Real.exp (2 * Z ω) ≤ Real.exp (2 * (t - (ℓ : ℝ) * w)) :=
      Real.exp_le_exp.2 (by linarith)
    have hm0 : 0 ≤ max (b - Z ω) 0 + c := add_nonneg (le_max_right _ _) hc
    have hm : max (b - Z ω) 0 + c ≤ (ℓ : ℝ) * w + w + c := by
      have : max (b - Z ω) 0 ≤ (ℓ : ℝ) * w + w := max_le (by linarith) (by positivity)
      linarith
    exact mul_le_mul he (pow_le_pow_left₀ hm0 hm j) (pow_nonneg hm0 j) (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem hω]
    exact Finset.sum_nonneg hnn

/-- **The weighted expectation, by slabs of width `w`**: under the hypotheses of
`RMF.indicator_le_sum_slab_width`, for measurable `T` and `Z` and a probability measure `P`,
`E[1_T e^{2Z}(max(b - Z, 0) + c)^j]
  ≤ ∑_{ℓ<L} e^{2(t-ℓw)}(ℓw + w + c)^j·P(T, Z ∈ [t - (ℓ+1)w, t - ℓw])`. -/
lemma integral_indicator_le_sum_slab_width {P : Measure Ω} [IsProbabilityMeasure P] {T : Set Ω}
    {Z : Ω → ℝ} (hTm : MeasurableSet T) (hZ : Measurable Z) {t lo b c w : ℝ} {j L : ℕ}
    (hT : ∀ ω ∈ T, lo ≤ Z ω ∧ Z ω ≤ t) (hw : 0 < w) (hL : t - lo < L * w) (hb : b ≤ t)
    (hc : 0 ≤ c) :
    ∫ ω, T.indicator (fun ω => Real.exp (2 * Z ω) * (max (b - Z ω) 0 + c) ^ j) ω ∂P
      ≤ ∑ ℓ ∈ Finset.range L, Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j
          * P.real (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}) := by
  have hSm : ∀ ℓ : ℕ,
      MeasurableSet (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}) := fun ℓ =>
    hTm.inter ((measurableSet_le measurable_const hZ).inter
      (measurableSet_le hZ measurable_const))
  have hint : Integrable (fun ω => ∑ ℓ ∈ Finset.range L,
      (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}).indicator
        (fun _ => Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j) ω) P :=
    integrable_finsetSum _ fun ℓ _ => (integrable_const _).indicator (hSm ℓ)
  have hf0 : 0 ≤ᵐ[P] fun ω => T.indicator
      (fun ω => Real.exp (2 * Z ω) * (max (b - Z ω) 0 + c) ^ j) ω :=
    ae_of_all _ fun ω => Set.indicator_nonneg (fun ω _ => mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (add_nonneg (le_max_right _ _) hc) j)) ω
  calc ∫ ω, T.indicator (fun ω => Real.exp (2 * Z ω) * (max (b - Z ω) 0 + c) ^ j) ω ∂P
      ≤ ∫ ω, ∑ ℓ ∈ Finset.range L,
          (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}).indicator
            (fun _ => Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j) ω ∂P :=
        integral_mono_of_nonneg hf0 hint
          (ae_of_all _ fun ω => indicator_le_sum_slab_width hT hw hL hb hc ω)
    _ = ∑ ℓ ∈ Finset.range L, ∫ ω,
          (T ∩ {ω | t - ((ℓ : ℝ) + 1) * w ≤ Z ω ∧ Z ω ≤ t - (ℓ : ℝ) * w}).indicator
            (fun _ => Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j) ω ∂P :=
        integral_finsetSum _ fun ℓ _ => (integrable_const _).indicator (hSm ℓ)
    _ = _ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [integral_indicator_const _ (hSm ℓ), smul_eq_mul, mul_comm]

end WidthSlabs

/-! ### The Abel sums of width `w` -/

/-- **The slab sums of width `w`, assembled.**  If `∑_{ℓ<L} w e^{-2wℓ}(ℓw + w + c)^{j+1} ≤ K`, then
for `w > 0`, `c, e, ε, B ≥ 0` and `Y + c ≥ 0`:
`∑_{ℓ<L} e^{2(t-ℓw)}(ℓw + w + c)^j·(1 + ε)(Y + c)(ℓw + w + 4e + c)(w + 4e)B
  ≤ (1 + ε)(1 + 4e/w)²e^{2t}(Y + c)KB`: the comparison's widening is `w + 4e = (1 + 4e/w)w` and
`ℓw + w + 4e + c ≤ (1 + 4e/w)(ℓw + w + c)`. -/
lemma sum_exp_mul_slab_width_le {L j : ℕ} {t Y c e ε B K w : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hε : 0 ≤ ε) (hB : 0 ≤ B) (hY : 0 ≤ Y + c)
    (hK : ∑ ℓ ∈ Finset.range L, w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (j + 1)
      ≤ K) :
    ∑ ℓ ∈ Finset.range L, Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j
        * ((1 + ε) * ((Y + c) * ((ℓ : ℝ) * w + (w + 4 * e) + c) * (w + 4 * e) * B))
      ≤ (1 + ε) * (1 + 4 * e / w) ^ 2 * Real.exp (2 * t) * (Y + c) * K * B := by
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hf : 0 ≤ 4 * e / w := div_nonneg (by linarith) hw.le
  have hf1 : 0 ≤ 1 + 4 * e / w := by linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = (1 + ε) * (1 + 4 * e / w) ^ 2 * Real.exp (2 * t) * (Y + c) * B := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hε1 (sq_nonneg _))
      (Real.exp_pos _).le) hY) hB
  have hww : w + 4 * e = (1 + 4 * e / w) * w := by field_simp
  have hterm : ∀ ℓ : ℕ, Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j
        * ((1 + ε) * ((Y + c) * ((ℓ : ℝ) * w + (w + 4 * e) + c) * (w + 4 * e) * B))
      ≤ C * (w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (j + 1)) := by
    intro ℓ
    have hl0 : 0 ≤ (ℓ : ℝ) * w + c := by positivity
    have hl : (ℓ : ℝ) * w + (w + 4 * e) + c ≤ (1 + 4 * e / w) * ((ℓ : ℝ) * w + w + c) := by
      have h1 : 4 * e / w * w = 4 * e := div_mul_cancel₀ _ hw.ne'
      have h2 : 4 * e / w * w ≤ 4 * e / w * ((ℓ : ℝ) * w + w + c) :=
        mul_le_mul_of_nonneg_left (by linarith) hf
      nlinarith
    have hexp : Real.exp (2 * (t - (ℓ : ℝ) * w)) = Real.exp (2 * t) * Real.exp (-2 * w * ℓ) := by
      rw [← Real.exp_add]
      ring_nf
    have hP : 0 ≤ Real.exp (2 * t) * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ j
        * ((1 + ε) * (Y + c) * ((1 + 4 * e / w) * w) * B) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (pow_nonneg (by positivity) _))
        (mul_nonneg (mul_nonneg (mul_nonneg hε1 hY) (mul_nonneg hf1 hw.le)) hB)
    calc Real.exp (2 * (t - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j
          * ((1 + ε) * ((Y + c) * ((ℓ : ℝ) * w + (w + 4 * e) + c) * (w + 4 * e) * B))
        = Real.exp (2 * t) * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ j
          * ((1 + ε) * (Y + c) * ((1 + 4 * e / w) * w) * B)
          * ((ℓ : ℝ) * w + (w + 4 * e) + c) := by
          rw [hexp, ← hww]
          ring
      _ ≤ Real.exp (2 * t) * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ j
          * ((1 + ε) * (Y + c) * ((1 + 4 * e / w) * w) * B)
          * ((1 + 4 * e / w) * ((ℓ : ℝ) * w + w + c)) :=
          mul_le_mul_of_nonneg_left hl hP
      _ = C * (w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (j + 1)) := by
          rw [hC]
          ring
  calc _ ≤ ∑ ℓ ∈ Finset.range L,
        C * (w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (j + 1)) :=
        Finset.sum_le_sum fun ℓ _ => hterm ℓ
    _ = C * ∑ ℓ ∈ Finset.range L,
        w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (j + 1) := by
        rw [Finset.mul_sum]
    _ ≤ C * K := mul_le_mul_of_nonneg_left hK hC0
    _ = (1 + ε) * (1 + 4 * e / w) ^ 2 * Real.exp (2 * t) * (Y + c) * K * B := by
        rw [hC]
        ring

/-- **The Abel sum of width `w` for the weight `1`** (`j = 0`), in closed form: with
`x = e^{-2w}` and `b = 1 + c/w`, `K₀(w, c) = w²(1/(1-x)² + (b-1)/(1-x))`. -/
noncomputable def slabAbelZero (w c : ℝ) : ℝ :=
  w ^ 2 * (1 / (1 - Real.exp (-2 * w)) ^ 2 + (1 + c / w - 1) / (1 - Real.exp (-2 * w)))

/-- **The Abel sum of width `w` for the weight `A`** (`j = 1`), in closed form: with
`x = e^{-2w}` and `b = 1 + c/w`, `K₁(w, c) = w³(2/(1-x)³ + (2b-3)/(1-x)² + (b-1)²/(1-x))`. -/
noncomputable def slabAbelOne (w c : ℝ) : ℝ :=
  w ^ 3 * (2 / (1 - Real.exp (-2 * w)) ^ 3 + (2 * (1 + c / w) - 3) / (1 - Real.exp (-2 * w)) ^ 2
    + (1 + c / w - 1) ^ 2 / (1 - Real.exp (-2 * w)))

/-- **The Abel sum of width `w` for the weight `A²`**, in closed form: with `x = e^{-2w}` and
`b = 1 + c/w`, `K₂(w, c) = w⁴(6/(1-x)⁴ + 6(b-2)/(1-x)³ + (3b²-9b+7)/(1-x)² + (b-1)³/(1-x))`
(`RMF.hasSum_slabAbelTwo`). -/
noncomputable def slabAbelTwo (w c : ℝ) : ℝ :=
  w ^ 4 * (6 / (1 - Real.exp (-2 * w)) ^ 4 + 6 * (1 + c / w - 2) / (1 - Real.exp (-2 * w)) ^ 3
    + (3 * (1 + c / w) ^ 2 - 9 * (1 + c / w) + 7) / (1 - Real.exp (-2 * w)) ^ 2
    + (1 + c / w - 1) ^ 3 / (1 - Real.exp (-2 * w)))

/-- `∑_ℓ w e^{-2wℓ}(ℓw + w + c)³ = K₂(w, c)` for `w > 0`: `w⁴∑_ℓ x^ℓ(ℓ + b)³` at `x = e^{-2w}`,
`b = 1 + c/w` (`RMF.hasSum_geom_mul_add_three`). -/
lemma hasSum_slabAbelTwo {w : ℝ} (hw : 0 < w) (c : ℝ) :
    HasSum (fun ℓ : ℕ => w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ 3)
      (slabAbelTwo w c) := by
  have hx0 : 0 ≤ Real.exp (-2 * w) := (Real.exp_pos _).le
  have hx1 : Real.exp (-2 * w) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine ((hasSum_geom_mul_add_three hx0 hx1 (1 + c / w)).mul_left (w ^ 4)).congr_fun
    fun ℓ => ?_
  have hxℓ : Real.exp (-2 * w * ℓ) = Real.exp (-2 * w) ^ ℓ := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hlin : (ℓ : ℝ) * w + w + c = w * ((ℓ : ℝ) + (1 + c / w)) := by
    field_simp
    ring
  rw [hxℓ, hlin]
  ring

/-- **The partial Abel sums of width `w` are at most `K₂(w, c)`**, for `w > 0`, `c ≥ 0`. -/
lemma sum_slab_width_le_slabAbelTwo {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (L : ℕ) :
    ∑ ℓ ∈ Finset.range L, w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (2 + 1)
      ≤ slabAbelTwo w c :=
  sum_le_hasSum _ (fun ℓ _ => mul_nonneg (mul_nonneg hw.le (Real.exp_pos _).le)
    (pow_nonneg (by positivity) _)) (hasSum_slabAbelTwo hw c)

/-- **`K₂(w, c)` as a cubic in `c`**: with `u = w/(1 - e^{-2w})`,
`K₂(w, c) = uc³ + 3u²c² + (6u³ - 3wu²)c + (6u⁴ - 6wu³ + w²u²)`. -/
lemma slabAbelTwo_eq {w : ℝ} (hw : 0 < w) (c : ℝ) :
    slabAbelTwo w c = w / (1 - Real.exp (-2 * w)) * c ^ 3
      + 3 * (w / (1 - Real.exp (-2 * w))) ^ 2 * c ^ 2
      + (6 * (w / (1 - Real.exp (-2 * w))) ^ 3 - 3 * w * (w / (1 - Real.exp (-2 * w))) ^ 2) * c
      + (6 * (w / (1 - Real.exp (-2 * w))) ^ 4 - 6 * w * (w / (1 - Real.exp (-2 * w))) ^ 3
        + w ^ 2 * (w / (1 - Real.exp (-2 * w))) ^ 2) := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = c / w := ⟨_, rfl⟩
  have hcβ : c = w * β := by rw [hβ]; field_simp
  unfold slabAbelTwo
  rw [← hβ]
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 - Real.exp (-2 * w))⁻¹ := ⟨_, rfl⟩
  have e1 : ∀ n : ℕ, ∀ a : ℝ, a / (1 - Real.exp (-2 * w)) ^ n = a * q ^ n := fun n a => by
    rw [hq, inv_pow, div_eq_mul_inv]
  have e0 : ∀ a : ℝ, a / (1 - Real.exp (-2 * w)) = a * q := fun a => by
    rw [hq, div_eq_mul_inv]
  rw [e1 4, e1 3, e1 2, e0, e0, hcβ]
  ring

/-- The cubic's coefficients at `u ∈ [1/16, 0.531906]`: `u ≤ 0.532`, `3u² ≤ 0.8488`,
`6u³ - 3u²/16 ≤ 0.8499`, `6u⁴ - 6u³/16 + u²/256 ≤ 0.425`. -/
lemma slab_sixteenth_coeffs_le {u : ℝ} (h0 : 1 / 16 ≤ u) (h1 : u ≤ 0.531906) :
    u ≤ 0.532 ∧ 3 * u ^ 2 ≤ 0.8488 ∧ 6 * u ^ 3 - 3 * (1 / 16) * u ^ 2 ≤ 0.8499
      ∧ 6 * u ^ 4 - 6 * (1 / 16) * u ^ 3 + (1 / 16) ^ 2 * u ^ 2 ≤ 0.425 := by
  have hu0 : 0 ≤ u := by linarith
  have hsq : u ^ 2 ≤ 0.531906 ^ 2 := pow_le_pow_left₀ hu0 h1 2
  refine ⟨by linarith, by nlinarith, ?_, ?_⟩
  · have hf : 6 * u - 3 / 16 ≤ 6 * 0.531906 - 3 / 16 := by linarith
    have hf0 : 0 ≤ 6 * u - 3 / 16 := by linarith
    have := mul_le_mul hsq hf hf0 (sq_nonneg _)
    nlinarith
  · have hg : 6 * u ^ 2 - 3 / 8 * u + 1 / 256
        ≤ 6 * 0.531906 ^ 2 - 3 / 8 * 0.531906 + 1 / 256 := by
      nlinarith
    have hg0 : 0 ≤ 6 * u ^ 2 - 3 / 8 * u + 1 / 256 := by nlinarith
    have := mul_le_mul hsq hg hg0 (sq_nonneg _)
    nlinarith

/-- `e^{-1/8} ≤ 0.882498`. -/
lemma exp_neg_two_mul_sixteenth_le : Real.exp (-2 * (1 / 16)) ≤ 0.882498 := by
  interval_decide (trust := kernel)

/-- **The Abel sum at width `1/16`, as a cubic**: `K₂(1/16, c) ≤ 0.532c³ + 0.8488c² + 0.8499c +
0.425` for every `c ≥ 0` (true coefficients `0.53190, 0.84876, 0.84986, 0.42493`; `≈ 2.869` at
`c = 1.05`). -/
theorem slabAbelTwo_sixteenth_le {c : ℝ} (hc : 0 ≤ c) :
    slabAbelTwo (1 / 16) c ≤ 0.532 * c ^ 3 + 0.8488 * c ^ 2 + 0.8499 * c + 0.425 := by
  rw [slabAbelTwo_eq (by norm_num) c]
  have hx := exp_neg_two_mul_sixteenth_le
  have hx0 := Real.exp_pos (-2 * (1 / 16 : ℝ))
  have hx1 : Real.exp (-2 * (1 / 16 : ℝ)) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / 16 / (1 - Real.exp (-2 * (1 / 16 : ℝ))) := ⟨_, rfl⟩
  rw [← hu]
  have hd0 : 0 < 1 - Real.exp (-2 * (1 / 16 : ℝ)) := by linarith
  have hu0 : 1 / 16 ≤ u := by
    rw [hu, le_div_iff₀ hd0]
    linarith
  have hu1 : u ≤ 0.531906 := by
    rw [hu, div_le_iff₀ hd0]
    linarith
  obtain ⟨c3, c2, c1, c0⟩ := slab_sixteenth_coeffs_le hu0 hu1
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hc3 : 0 ≤ c ^ 3 := pow_nonneg hc 3
  have t3 := mul_le_mul_of_nonneg_right c3 hc3
  have t2 := mul_le_mul_of_nonneg_right c2 hc2
  have t1 := mul_le_mul_of_nonneg_right c1 hc
  linarith

/-- The comparison's widening at width `1/16`: `(1 + 4e^{-40}/(1/16))² ≤ 1 + e^{-30}`. -/
lemma one_add_widening_sixteenth_le :
    (1 + 4 * Real.exp (-40) / (1 / 16)) ^ 2 ≤ 1 + Real.exp (-30) := by
  have h10 : (20000 : ℝ) ≤ Real.exp 10 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 10) (N := 20000) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have hsplit : Real.exp (-40) = Real.exp (-30) / Real.exp 10 := by
    rw [← Real.exp_sub]; norm_num
  have hE0 : 0 < Real.exp (-30) := Real.exp_pos _
  have hE1 : Real.exp (-30) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have h40 : Real.exp (-40) ≤ Real.exp (-30) / 20000 := by
    rw [hsplit]
    exact div_le_div_of_nonneg_left hE0.le (by norm_num) h10
  have hkey : 4 * Real.exp (-40) / (1 / 16) ≤ Real.exp (-30) / 300 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  have hk0 : 0 ≤ 4 * Real.exp (-40) / (1 / 16) := by positivity
  have hk2 : (4 * Real.exp (-40) / (1 / 16)) ^ 2 ≤ (Real.exp (-30) / 300) ^ 2 :=
    pow_le_pow_left₀ hk0 hkey 2
  have hE2 : Real.exp (-30) ^ 2 ≤ Real.exp (-30) := by nlinarith
  nlinarith

/-! ### The weighted prefix term by slabs of width `w` -/

section WidthWeighted

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **HP2's prefix term by slabs of width `w`, from `k ≥ 20`.**  Under the hypotheses of
`RMF.tiltedMeasure_hp2Tube_slab_le_floor` (without `d, w`), a weight level `b ≤ a + ρ`,
`ρ' ≥ ρ + 2e^{-40}`, a width `w > 0` and an Abel sum
`∑_{ℓ<L} w e^{-2wℓ}(ℓw + w + c)^{j+1} ≤ K` for every `L` (`RMF.sum_slab_width_le_slabAbelTwo`),
under the one-point tilt at `s_h`:
`E[1_{tube} e^{2Z_M}(max(b - Z_M, 0) + c)^j]
  ≤ (1 + e^{-100})(1 + 4e^{-40}/w)²e^{2(a+ρ')}(a + ρ' + c)K·2/(π√(2πS₁S₂S₃))`.
The slabs `[a + ρ - (ℓ+1)w, a + ρ - ℓw]` (`RMF.integral_indicator_le_sum_slab_width`), each by
`RMF.tiltedMeasure_hp2Tube_slab_le_floor` at `(d, w) = (ℓw, w)`, summed by
`RMF.sum_exp_mul_slab_width_le`. -/
theorem integral_hp2Tube_exp_mul_le_width (hX : IsRademacherPrimeValues X μ) {k M y : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσM : σ * Real.exp ((k : ℝ) + M) ≤ 1 / 200)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) (hM : 3 ≤ M)
    {a A B ρ c S₁ S₂ S₃ b ρ' K w : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (henv : a + A + B + ρ ≤ 398) (hc0 : 0 < c)
    (hc : ∀ i, i < M → √(π * windowVarH X μ y k σ h i / 2) ≤ c)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hS₃ : 0 < S₃)
    (h₁ : S₁ ≤ ∑ i ∈ Finset.range (M / 3), windowVarH X μ y k σ h i)
    (h₂ : S₂ ≤ ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), windowVarH X μ y k σ h i)
    (h₃ : S₃ ≤ ∑ i ∈ Finset.Ico (M - M / 3) M, windowVarH X μ y k σ h i)
    (hb : b ≤ a + ρ) (hρ' : ρ + 2 * Real.exp (-40) ≤ ρ') (hw : 0 < w) {j : ℕ}
    (hK : ∀ L : ℕ, ∑ ℓ ∈ Finset.range L,
      w * Real.exp (-2 * w * ℓ) * ((ℓ : ℝ) * w + w + c) ^ (j + 1) ≤ K) :
    ∫ ω, (hp2Tube X μ y k M σ h a A B ρ).indicator (fun ω =>
        Real.exp (2 * windowZ X μ y k σ h M ω)
          * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ j) ω
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
      ≤ (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / w) ^ 2 * Real.exp (2 * (a + ρ'))
        * (a + ρ' + c) * K * (2 / (π * √(2 * π * (S₁ * S₂ * S₃)))) := by
  have hs₁ : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs₁
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌊(a + A + B * M + 2 * ρ) / w⌋₊ + 1 := ⟨_, rfl⟩
  have hLgt : a + ρ - (-A - B * M - ρ) < L * w := by
    have h1 := Nat.lt_floor_add_one ((a + A + B * M + 2 * ρ) / w)
    have h2 : (a + A + B * M + 2 * ρ) / w < L := by
      rw [hL]
      push_cast
      linarith
    rw [div_lt_iff₀ hw] at h2
    linarith
  have hdec := integral_indicator_le_sum_slab_width
    (P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
    (measurableSet_hp2Tube hX y k M σ h a A B ρ) (measurable_windowZ hX y k σ h M)
    (t := a + ρ) (lo := -A - B * M - ρ) (b := b) (c := c) (w := w) (j := j) (L := L)
    (fun ω hω => windowZ_mem_of_mem_hp2Tube (by omega) hω) hw hLgt hb hc0.le
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 / (π * √(2 * π * (S₁ * S₂ * S₃))) := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hslab : ∀ ℓ ∈ Finset.range L,
      Real.exp (2 * (a + ρ - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j
        * (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ).real
          (hp2Tube X μ y k M σ h a A B ρ ∩ {ω | a + ρ - ((ℓ : ℝ) + 1) * w
              ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - (ℓ : ℝ) * w})
      ≤ Real.exp (2 * (a + ρ - (ℓ : ℝ) * w)) * ((ℓ : ℝ) * w + w + c) ^ j
        * ((1 + Real.exp (-100)) * ((a + ρ + 2 * Real.exp (-40) + c)
          * ((ℓ : ℝ) * w + (w + 4 * Real.exp (-40)) + c) * (w + 4 * Real.exp (-40)) * Bc)) := by
    intro ℓ _
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by positivity) _))
    have hset : hp2Tube X μ y k M σ h a A B ρ ∩ {ω | a + ρ - ((ℓ : ℝ) + 1) * w
          ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - (ℓ : ℝ) * w}
        = hp2Tube X μ y k M σ h a A B ρ ∩ {ω | a + ρ - (ℓ : ℝ) * w - w
          ≤ windowZ X μ y k σ h M ω ∧ windowZ X μ y k σ h M ω ≤ a + ρ - (ℓ : ℝ) * w} := by
      congr 1
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩
    rw [hset, hBc]
    exact tiltedMeasure_hp2Tube_slab_le_floor hX hk hh hσ hσM hy hM ha hA hB hρ henv hc0 hc
      hS₁ hS₂ hS₃ h₁ h₂ h₃ (d := (ℓ : ℝ) * w) (w := w) (by positivity) hw.le
  have hsum := sum_exp_mul_slab_width_le (L := L) (j := j) (t := a + ρ)
    (Y := a + ρ + 2 * Real.exp (-40)) (c := c) (e := Real.exp (-40)) (ε := Real.exp (-100))
    (B := Bc) (K := K) (w := w) hw hc0.le (Real.exp_pos _).le (Real.exp_pos _).le hBc0
    (by positivity) (hK L)
  have hK0 : 0 ≤ K := le_trans (Finset.sum_nonneg fun ℓ _ => mul_nonneg
    (mul_nonneg hw.le (Real.exp_pos _).le) (pow_nonneg (by positivity) _)) (hK 0)
  have he1 : Real.exp (2 * (a + ρ)) ≤ Real.exp (2 * (a + ρ')) :=
    Real.exp_le_exp.2 (by linarith [Real.exp_pos (-40)])
  have he2 : a + ρ + 2 * Real.exp (-40) + c ≤ a + ρ' + c := by linarith
  have hE : Real.exp (2 * (a + ρ)) * (a + ρ + 2 * Real.exp (-40) + c)
      ≤ Real.exp (2 * (a + ρ')) * (a + ρ' + c) :=
    mul_le_mul he1 he2 (by positivity) (Real.exp_pos _).le
  have hF : 0 ≤ (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / w) ^ 2 * K * Bc := by
    positivity
  rw [← hBc]
  calc _ ≤ _ := hdec
    _ ≤ _ := Finset.sum_le_sum hslab
    _ ≤ (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / w) ^ 2 * Real.exp (2 * (a + ρ))
          * (a + ρ + 2 * Real.exp (-40) + c) * K * Bc := hsum
    _ = (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / w) ^ 2 * K * Bc
          * (Real.exp (2 * (a + ρ)) * (a + ρ + 2 * Real.exp (-40) + c)) := by ring
    _ ≤ (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / w) ^ 2 * K * Bc
          * (Real.exp (2 * (a + ρ')) * (a + ρ' + c)) := mul_le_mul_of_nonneg_left hE hF
    _ = (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / w) ^ 2 * Real.exp (2 * (a + ρ'))
          * (a + ρ' + c) * K * Bc := by ring

end WidthWeighted

/-! ### The pointwise bound for `c ≥ 1` -/

/-- **The weight below the ceiling, for `c ≥ 1`**: `e^{2z}(max(b - z, 0) + c)² ≤ e^{2t}c²` for
`z ≤ t`, `b ≤ t` — with `u = t - z ≥ 0`, `u + c ≤ c(1 + u) ≤ ce^u` (the weight is decreasing in
`u` when `c ≥ 1`; `RMF.exp_mul_sq_le_of_le` has `e^{2(t+c-1)}`, exponential in `c`). -/
lemma exp_mul_sq_le_of_one_le {z t b c : ℝ} (hz : z ≤ t) (hb : b ≤ t) (hc : 1 ≤ c) :
    Real.exp (2 * z) * (max (b - z) 0 + c) ^ 2 ≤ Real.exp (2 * t) * c ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t - z := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hm0 : 0 ≤ max (b - z) 0 + c := add_nonneg (le_max_right _ _) (by linarith)
  have hm : max (b - z) 0 + c ≤ u + c := by
    have : max (b - z) 0 ≤ u := max_le (by rw [hu]; linarith) hu0
    linarith
  have hexp : u + c ≤ c * Real.exp u := by
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) (by linarith : (0 : ℝ) ≤ c)
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1) hu0
    linarith
  have hsq : (max (b - z) 0 + c) ^ 2 ≤ (c * Real.exp u) ^ 2 :=
    pow_le_pow_left₀ hm0 (hm.trans hexp) 2
  have he : Real.exp (2 * t) = Real.exp (2 * z) * Real.exp u ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, hu]
    ring_nf
  calc Real.exp (2 * z) * (max (b - z) 0 + c) ^ 2 ≤ Real.exp (2 * z) * (c * Real.exp u) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = Real.exp (2 * t) * c ^ 2 := by rw [he]; ring

section Short

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Short prefixes on HP1's tube, for `c ≥ 1`**: for every `M ≤ r` and `b ≤ 3/2 + 10⁻¹⁵`,
`E[1_{H(k,h)} e^{2Z_M}(max(b - Z_M, 0) + c)²] ≤ e^{2(3/2 + 10⁻¹⁵)}c²`
(`RMF.exp_mul_sq_le_of_one_le` below the ceiling), `≈ 22.14` at `c = 1.05`. -/
theorem integral_hp1Tube_exp_mul_sq_le_short_of_one_le (hX : IsRademacherPrimeValues X μ)
    {k M r y : ℕ} {σ h b c : ℝ} (hσ : 0 ≤ σ) (hMr : M ≤ r) (hb : b ≤ 3 / 2 + 1 / 10 ^ 15)
    (hc : 1 ≤ c) :
    ∫ ω, (hp1Tube X μ y k r σ h).indicator (fun ω =>
        Real.exp (2 * windowZ X μ y k σ h M ω)
          * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ 2) ω
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
      ≤ Real.exp (2 * (3 / 2 + 1 / 10 ^ 15)) * c ^ 2 := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  exact integral_indicator_le_of_le (fun ω _ => by positivity)
    (fun ω hω => exp_mul_sq_le_of_one_le (windowZ_le_of_mem_hp2Tube (a := 3 / 2) (A := 5 / 2)
      (B := 3) (ρ := 1 / 10 ^ 15) (by norm_num) (hp1Tube_subset_hp2Tube hMr y k σ h hω)) hb hc)
    (by positivity)

end Short

/-! ### The block variances on the window from `k ≥ 20` -/

section Variances

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The doubled frequency's cosine sums on the window, sharp main term**: for
`h ∈ halfWindow k`, `|C_m(2h)| ≤ e^{1-m} + blockCosErr k m (2h)` on every block
(`RMF.abs_sum_cos_primeBlockSub_le_two_regime`, `2/(2he^{m+k}) ≤ e^{1-m}`). -/
lemma abs_blockCosSum_two_mul_le_window {k : ℕ} {σ h : ℝ} (hh : h ∈ halfWindow k)
    (hσ : 0 ≤ σ) (m : ℕ) :
    |blockCosSum k σ (2 * h) m| ≤ Real.exp (1 - m) + blockCosErr k m (2 * h) := by
  have h0 : 0 < h := (log_add_mem_of_mem_halfWindow hh).1
  have hτ0 : 0 < 2 * h := by linarith
  have hmain := abs_sum_cos_primeBlockSub_le_two_regime (2 * h) σ k m hτ0 hσ (by positivity)
  have hprod : Real.exp ((m : ℝ) - 1) ≤ h * Real.exp ((m : ℝ) + k) := by
    calc Real.exp ((m : ℝ) - 1) = Real.exp (-((k : ℝ) + 1)) * Real.exp ((m : ℝ) + k) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ h * Real.exp ((m : ℝ) + k) := mul_le_mul_of_nonneg_right hh.1 (Real.exp_pos _).le
  have hid : Real.exp (1 - (m : ℝ)) * (2 * Real.exp ((m : ℝ) - 1)) = 2 := by
    rw [mul_left_comm, ← Real.exp_add, show (1 - (m : ℝ)) + ((m : ℝ) - 1) = 0 by ring,
      Real.exp_zero, mul_one]
  have h1 : 2 / (2 * h * Real.exp ((m : ℝ) + k)) ≤ Real.exp (1 - m) := by
    rw [div_le_iff₀ (by positivity)]
    calc (2 : ℝ) = Real.exp (1 - (m : ℝ)) * (2 * Real.exp ((m : ℝ) - 1)) := hid.symm
      _ ≤ Real.exp (1 - (m : ℝ)) * (2 * h * Real.exp ((m : ℝ) + k)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  unfold blockCosSum
  linarith

/-- `e^{-2} ≤ 0.136`. -/
lemma exp_neg_two_le_numeral : Real.exp (-2) ≤ 0.136 := by
  have h2 : (7.38 : ℝ) ≤ Real.exp 2 := by
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    rw [hsq]
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
  linarith

/-- **The height variances on the window are at most `0.6801`**: for `k ≥ 20`,
`h ∈ halfWindow k`, `σ ≥ 0`, `σe^{k+m+1} ≤ 1/200` and block `m` below the cutoff,
`V_m = (S_m + C_m(2h))/2` within `10⁻²⁰` (`RMF.abs_blockMatchedVarAdd_height_sub_le`),
`S_m ≤ 1 + 1/150000`, and `C_m(2h)` at most `0.3601` — the certified doubled ranges
(`0.35, 0.35, 0.3` on blocks `0, 1, 2`) widened by `1/100 + 7.43·10⁻⁸`, and
`e^{-2} + 7.43·10⁻⁸` beyond (`RMF.abs_blockCosSum_two_mul_le_window`). -/
theorem windowVarH_le_window (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    windowVarH X μ y k σ h m ≤ 0.6801 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (20 : ℝ) ≤ (m : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hV := (abs_le.1 (abs_blockMatchedVarAdd_height_sub_le hX y (h := h) hσ hm hB)).2
  have hS := blockRpowSum_le (θ := (k : ℝ)) (m := m) hσ (by linarith)
  have hC : blockCosSum k σ (2 * h) m ≤ 0.3601 := by
    have he := (blockCosErr_window_le (m := m) hk hh).2
    obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
    obtain ⟨hξ1, hξ2⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
    have hδ : 2 * σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 100 := by linarith
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
          (blockCos_zero_bounds_doubled hξ1 hξ2)
        linarith [hC.2]
      · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
          (blockCos_one_bounds_doubled hξ1 hξ2)
        linarith [hC.2]
      · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
          (blockCos_two_bounds_doubled hξ1 hξ2)
        linarith [hC.2]
    · have h1 := (abs_le.1 (abs_blockCosSum_two_mul_le_window hh hσ m)).2
      have hm3' : (3 : ℝ) ≤ m := by exact_mod_cast hm3
      have he2 : Real.exp (1 - m) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
      linarith [exp_neg_two_le_numeral]
  unfold windowVarH
  linarith

/-- **`c ≥ √(πV_m/2)` on the window for every `c ≥ 1.05`**: `πV_m/2 ≤ 3.15·0.6801/2 ≤ 1.05²`
(`RMF.windowVarH_le_window`). -/
theorem sqrt_pi_windowVarH_div_two_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ}
    {σ h c : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) (hc : 1.05 ≤ c) :
    √(π * windowVarH X μ y k σ h m / 2) ≤ c := by
  have hV := windowVarH_le_window hX y hk hh hσ hσm hB
  have hV0 : 0 ≤ windowVarH X μ y k σ h m := NNReal.coe_nonneg _
  have hπV := mul_le_mul Real.pi_lt_d2.le hV hV0 (by norm_num)
  have h1 : π * windowVarH X μ y k σ h m / 2 ≤ 1.1025 := by linarith
  calc √(π * windowVarH X μ y k σ h m / 2) ≤ √1.1025 := Real.sqrt_le_sqrt h1
    _ = 1.05 := by
        rw [show (1.1025 : ℝ) = 1.05 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ c := hc

/-- **The cosine floor of block `i`** on the window's doubled frequency: `0.75, 0.65, 0.25` on
blocks `0, 1, 2` (the certified ranges of `RMF.blockCos_zero_bounds_doubled` and its twins) and
`e^{1-i}` beyond (`RMF.abs_blockCosSum_two_mul_le_window`). -/
noncomputable def hp2CosFloor : ℕ → ℝ
  | 0 => 0.75
  | 1 => 0.65
  | 2 => 0.25
  | i + 3 => Real.exp (-((i : ℝ) + 2))

/-- The cosine floors are nonnegative. -/
lemma hp2CosFloor_nonneg (i : ℕ) : 0 ≤ hp2CosFloor i := by
  match i with
  | 0 => norm_num [hp2CosFloor]
  | 1 => norm_num [hp2CosFloor]
  | 2 => norm_num [hp2CosFloor]
  | i + 3 => exact (Real.exp_pos _).le

/-- The cosine floors are at most `0.75` (`e^{1-i} ≤ e^{-2}` from block `3`). -/
lemma hp2CosFloor_le (i : ℕ) : hp2CosFloor i ≤ 0.75 := by
  match i with
  | 0 => norm_num [hp2CosFloor]
  | 1 => norm_num [hp2CosFloor]
  | 2 => norm_num [hp2CosFloor]
  | i + 3 =>
    have he : Real.exp (-((i : ℝ) + 2)) ≤ Real.exp (-2) :=
      Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) i])
    exact he.trans (exp_neg_two_le_numeral.trans (by norm_num))

/-- **The doubled frequency's cosine sums from below**: for `k ≥ 20`, `h ∈ halfWindow k` and a
damping `2σe^{k+i+1} ≤ δ`, `C_i(2h) ≥ -hp2CosFloor i - 7.43·10⁻⁸ - δ`. -/
lemma neg_hp2CosFloor_le_blockCosSum {k i : ℕ} {σ h δ : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ) (hδ : 2 * σ * Real.exp ((k : ℝ) + i + 1) ≤ δ)
    (hδ0 : 0 ≤ δ) :
    -hp2CosFloor i - 7.43 / 10 ^ 8 - δ ≤ blockCosSum k σ (2 * h) i := by
  have he := (blockCosErr_window_le (m := i) hk hh).2
  obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
  obtain ⟨hξ1, hξ2⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
  rcases Nat.lt_or_ge i 3 with hi3 | hi3
  · interval_cases i
    · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
        (blockCos_zero_bounds_doubled hξ1 hξ2)
      have hF : hp2CosFloor 0 = 0.75 := rfl
      linarith [hC.1]
    · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
        (blockCos_one_bounds_doubled hξ1 hξ2)
      have hF : hp2CosFloor 1 = 0.65 := rfl
      linarith [hC.1]
    · have hC := blockCosSum_mem_of_blockCos hσ (by linarith) hδ
        (blockCos_two_bounds_doubled hξ1 hξ2)
      have hF : hp2CosFloor 2 = 0.25 := rfl
      linarith [hC.1]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
    have hF : hp2CosFloor (j + 3) = Real.exp (1 - ((j + 3 : ℕ) : ℝ)) := by
      rw [show (1 : ℝ) - ((j + 3 : ℕ) : ℝ) = -((j : ℝ) + 2) by push_cast; ring]
      rfl
    have h1 := (abs_le.1 (abs_blockCosSum_two_mul_le_window hh hσ (j + 3))).1
    rw [hF]
    linarith

/-- **The variance floor of block `i` at depth `M`**:
`hp2VarLo M i = 1/2 - hp2CosFloor i/2 - e^{i+1-M}/100 - 4·10⁻⁶`, the damping term from
`σe^{k+M} ≤ 1/200` (`RMF.hp2VarLo_le_windowVarH`). -/
noncomputable def hp2VarLo (M i : ℕ) : ℝ :=
  1 / 2 - hp2CosFloor i / 2 - Real.exp ((i : ℝ) + 1 - M) / 100 - 4 / 10 ^ 6

/-- **The height variances from below**: for `k ≥ 20`, `h ∈ halfWindow k`, `σ ≥ 0`,
`σe^{k+M} ≤ 1/200` and a block `i` below the cutoff, `hp2VarLo M i ≤ V_i` (positive for
`i < M`, `RMF.le_hp2VarLo`):
`V_i ≥ (S_i + C_i(2h))/2 - 10⁻²⁰`, `S_i ≥ e^{-2η}(1 - 1/150000)`
(`RMF.sum_norm_sq_primeBlockSub_bounds_sharp` at `η = e^{i+1-M}/200`), and
`C_i(2h) ≥ -hp2CosFloor i - 7.43·10⁻⁸ - 2η` (`RMF.neg_hp2CosFloor_le_blockCosSum`). -/
theorem hp2VarLo_le_windowVarH (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k M i : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσM : σ * Real.exp ((k : ℝ) + M) ≤ 1 / 200)
    (hB : primeBlockSub k i ⊆ primesBelowSub y) :
    hp2VarLo M i ≤ windowVarH X μ y k σ h i := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : (20 : ℝ) ≤ (i : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) i]
  have hV := (abs_le.1 (abs_blockMatchedVarAdd_height_sub_le hX y (h := h) hσ hm hB)).1
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.exp ((i : ℝ) + 1 - M) / 200 := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hση : σ * Real.exp ((k : ℝ) + i + 1) ≤ η := by
    have hsplit : Real.exp ((k : ℝ) + i + 1)
        = Real.exp ((k : ℝ) + M) * Real.exp ((i : ℝ) + 1 - M) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit, hηdef]
    have hE := Real.exp_pos ((i : ℝ) + 1 - M)
    calc σ * (Real.exp ((k : ℝ) + M) * Real.exp ((i : ℝ) + 1 - M))
        = σ * Real.exp ((k : ℝ) + M) * Real.exp ((i : ℝ) + 1 - M) := by ring
      _ ≤ 1 / 200 * Real.exp ((i : ℝ) + 1 - M) := mul_le_mul_of_nonneg_right hσM hE.le
      _ = Real.exp ((i : ℝ) + 1 - M) / 200 := by ring
  have hS : 1 - 1 / 150000 - 2 * η ≤ blockRpowSum k σ i := by
    have hη : |σ| * Real.log (blockScale (k : ℝ) (i + 1)) ≤ η := by
      rw [abs_of_nonneg hσ, log_blockScale]
      push_cast
      rw [show (i : ℝ) + 1 + k = (k : ℝ) + i + 1 by ring]
      exact hση
    have hsum : blockRpowSum k σ i
        = ∑ p ∈ primeBlockSub k i, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))‖ ^ 2 :=
      Finset.sum_congr rfl fun p _ => (norm_sq_prime_cpow_neg p (re_shiftLine σ 0)).symm
    obtain ⟨hlo, -⟩ := sum_norm_sq_primeBlockSub_bounds_sharp
      (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (by linarith) hσ hη
      fun p _ => norm_sq_prime_cpow_neg p (re_shiftLine σ 0)
    rw [← hsum] at hlo
    have h1 : 1 - 2 * η ≤ Real.exp (-(2 * η)) := by
      linarith [Real.add_one_le_exp (-(2 * η))]
    have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 150000)
    linarith
  have hC := neg_hp2CosFloor_le_blockCosSum hk hh hσ (δ := 2 * η) (by linarith) (by linarith)
  unfold hp2VarLo windowVarH
  linarith

end Variances

/-! ### The variance sums over the thirds -/

/-- Every floor below the depth is at least `0.1149`: `hp2VarLo M i ≥ 1/2 - 0.375 - 1/100 - 4·10⁻⁶`
for `i < M`. -/
lemma le_hp2VarLo {M i : ℕ} (hi : i < M) : 0.1149 ≤ hp2VarLo M i := by
  have hF := hp2CosFloor_le i
  have he : Real.exp ((i : ℝ) + 1 - M) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : ((i : ℝ) + 1) ≤ M := by exact_mod_cast hi
    linarith)
  unfold hp2VarLo
  linarith

/-- **HP2's first variance sum at depth `M`**: `hp2VarLo M` over `[0, ⌊M/3⌋)`. -/
noncomputable def hp2VarSum₁ (M : ℕ) : ℝ := ∑ i ∈ Finset.range (M / 3), hp2VarLo M i

/-- **HP2's second variance sum at depth `M`**: `hp2VarLo M` over `[⌊M/3⌋, M - ⌊M/3⌋)`. -/
noncomputable def hp2VarSum₂ (M : ℕ) : ℝ := ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), hp2VarLo M i

/-- **HP2's third variance sum at depth `M`**: `hp2VarLo M` over `[M - ⌊M/3⌋, M)`. -/
noncomputable def hp2VarSum₃ (M : ℕ) : ℝ := ∑ i ∈ Finset.Ico (M - M / 3) M, hp2VarLo M i

/-- The first variance sum is positive from `M ≥ 3` (`RMF.le_hp2VarLo`). -/
lemma hp2VarSum₁_pos {M : ℕ} (hM : 3 ≤ M) : 0 < hp2VarSum₁ M :=
  Finset.sum_pos (fun i hi => lt_of_lt_of_le (by norm_num)
    (le_hp2VarLo (by have := Finset.mem_range.1 hi; omega)))
    ⟨0, Finset.mem_range.2 (by omega)⟩

/-- The second variance sum is positive from `M ≥ 3`. -/
lemma hp2VarSum₂_pos {M : ℕ} (hM : 3 ≤ M) : 0 < hp2VarSum₂ M :=
  Finset.sum_pos (fun i hi => lt_of_lt_of_le (by norm_num)
    (le_hp2VarLo (by have := (Finset.mem_Ico.1 hi).2; omega)))
    ⟨M / 3, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩

/-- The third variance sum is positive from `M ≥ 3`. -/
lemma hp2VarSum₃_pos {M : ℕ} (hM : 3 ≤ M) : 0 < hp2VarSum₃ M :=
  Finset.sum_pos (fun i hi => lt_of_lt_of_le (by norm_num)
    (le_hp2VarLo (Finset.mem_Ico.1 hi).2))
    ⟨M - M / 3, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩

section VarSumsWindow

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The three variance sums are below the true ones** on the window: for `k ≥ 20`,
`h ∈ halfWindow k`, `σ ≥ 0`, `σe^{k+M} ≤ 1/200` and the blocks `m < M` below the cutoff, each of
`RMF.hp2VarSum₁`, `₂`, `₃` is at most the corresponding sum of `V_i = RMF.windowVarH`
(`RMF.hp2VarLo_le_windowVarH` termwise). -/
theorem hp2VarSums_le (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k M : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσM : σ * Real.exp ((k : ℝ) + M) ≤ 1 / 200)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) :
    hp2VarSum₁ M ≤ ∑ i ∈ Finset.range (M / 3), windowVarH X μ y k σ h i
      ∧ hp2VarSum₂ M ≤ ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), windowVarH X μ y k σ h i
      ∧ hp2VarSum₃ M ≤ ∑ i ∈ Finset.Ico (M - M / 3) M, windowVarH X μ y k σ h i := by
  have key : ∀ i, i < M → hp2VarLo M i ≤ windowVarH X μ y k σ h i := fun i hi =>
    hp2VarLo_le_windowVarH hX y hk hh hσ hσM (hy i hi)
  refine ⟨Finset.sum_le_sum fun i hi => key i ?_, Finset.sum_le_sum fun i hi => key i ?_,
    Finset.sum_le_sum fun i hi => key i (Finset.mem_Ico.1 hi).2⟩
  · have := Finset.mem_range.1 hi
    omega
  · have := (Finset.mem_Ico.1 hi).2
    omega

end VarSumsWindow

/-- **The tail of the cosine floors**, `∑_{i ≥ i₀} hp2CosFloor i` in closed form:
`1.65 + T, 0.9 + T, 0.25 + T` for `i₀ = 0, 1, 2` and `e^{1-i₀}·e/(e-1)` beyond,
`T = e^{-2}·e/(e-1) ≈ 0.2141` (`RMF.sum_Ico_hp2CosFloor_le`). -/
noncomputable def hp2CosTail : ℕ → ℝ
  | 0 => 1.65 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1))
  | 1 => 0.9 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1))
  | 2 => 0.25 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1))
  | i + 3 => Real.exp (-((i : ℝ) + 2)) * (Real.exp 1 / (Real.exp 1 - 1))

/-- `∑_{i ∈ [i₀, N)} hp2CosFloor i ≤ hp2CosTail i₀`: past block `2` the floors are geometric,
`∑_t e^{-(j+2)}e^{-t} ≤ e^{-(j+2)}·e/(e-1)` (`RMF.sum_exp_neg_le`). -/
lemma sum_Ico_hp2CosFloor_le (i₀ N : ℕ) :
    ∑ i ∈ Finset.Ico i₀ N, hp2CosFloor i ≤ hp2CosTail i₀ := by
  have hgeo : ∀ j N : ℕ, ∑ i ∈ Finset.Ico (j + 3) N, hp2CosFloor i
      ≤ Real.exp (-((j : ℝ) + 2)) * (Real.exp 1 / (Real.exp 1 - 1)) := by
    intro j N
    rw [Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ t ∈ Finset.range (N - (j + 3)),
        hp2CosFloor (j + 3 + t) = Real.exp (-((j : ℝ) + 2)) * Real.exp (-(t : ℝ)) := by
      intro t _
      rw [show j + 3 + t = (j + t) + 3 by ring, ← Real.exp_add]
      change Real.exp (-(((j + t : ℕ) : ℝ) + 2)) = _
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_exp_neg_le _) (Real.exp_pos _).le
  have h3 : ∀ N : ℕ, ∑ i ∈ Finset.Ico 3 N, hp2CosFloor i
      ≤ Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := fun N => by
    have h := hgeo 0 N
    simp only [Nat.cast_zero, zero_add] at h
    exact h
  have h2 : ∀ N : ℕ, ∑ i ∈ Finset.Ico 2 N, hp2CosFloor i
      ≤ 0.25 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := fun N => by
    calc ∑ i ∈ Finset.Ico 2 N, hp2CosFloor i ≤ ∑ i ∈ Finset.Ico 2 (N + 3), hp2CosFloor i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
            fun i _ _ => hp2CosFloor_nonneg i
      _ = hp2CosFloor 2 + ∑ i ∈ Finset.Ico 3 (N + 3), hp2CosFloor i :=
          Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      _ ≤ 0.25 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := by
          have h := h3 (N + 3)
          have hF : hp2CosFloor 2 = 0.25 := rfl
          linarith
  have h1 : ∀ N : ℕ, ∑ i ∈ Finset.Ico 1 N, hp2CosFloor i
      ≤ 0.9 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := fun N => by
    calc ∑ i ∈ Finset.Ico 1 N, hp2CosFloor i ≤ ∑ i ∈ Finset.Ico 1 (N + 2), hp2CosFloor i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
            fun i _ _ => hp2CosFloor_nonneg i
      _ = hp2CosFloor 1 + ∑ i ∈ Finset.Ico 2 (N + 2), hp2CosFloor i :=
          Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      _ ≤ 0.9 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := by
          have h := h2 (N + 2)
          have hF : hp2CosFloor 1 = 0.65 := rfl
          linarith
  match i₀ with
  | 0 =>
    calc ∑ i ∈ Finset.Ico 0 N, hp2CosFloor i ≤ ∑ i ∈ Finset.Ico 0 (N + 1), hp2CosFloor i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
            fun i _ _ => hp2CosFloor_nonneg i
      _ = hp2CosFloor 0 + ∑ i ∈ Finset.Ico 1 (N + 1), hp2CosFloor i :=
          Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      _ ≤ 1.65 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := by
          have h := h1 (N + 1)
          have hF : hp2CosFloor 0 = 0.75 := rfl
          linarith
  | 1 => exact h1 N
  | 2 => exact h2 N
  | j + 3 => exact hgeo j N

/-- `e^{-2}·e/(e-1) ≤ 0.2142` (it is `1/(e(e-1)) ≈ 0.21410`). -/
lemma exp_neg_two_mul_div_le : Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) ≤ 0.2142 := by
  have he1 : (2.7182 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsplit : Real.exp (-2) * Real.exp 1 = Real.exp (-1) := by
    rw [← Real.exp_add]
    norm_num
  have hinv : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm1 : Real.exp (-1) ≤ 0.3679 := by
    nlinarith [mul_nonneg (Real.exp_pos (-1)).le (sub_nonneg.2 he1)]
  rw [mul_div_assoc', hsplit, div_le_iff₀ (by linarith)]
  linarith

/-- **The tails in numerals**: `hp2CosTail i ≤ 1.8642` always, `≤ 1.1142` from `i ≥ 1` and
`≤ 0.4642` from `i ≥ 2`. -/
lemma hp2CosTail_le (i : ℕ) :
    hp2CosTail i ≤ 1.8642 ∧ (1 ≤ i → hp2CosTail i ≤ 1.1142)
      ∧ (2 ≤ i → hp2CosTail i ≤ 0.4642) := by
  have hT := exp_neg_two_mul_div_le
  have hE : 0 ≤ Real.exp 1 / (Real.exp 1 - 1) :=
    div_nonneg (Real.exp_pos 1).le (by linarith [Real.exp_one_gt_d9])
  match i with
  | 0 =>
    have h0 : hp2CosTail 0 = 1.65 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := rfl
    exact ⟨by linarith, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
  | 1 =>
    have h0 : hp2CosTail 1 = 0.9 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := rfl
    exact ⟨by linarith, fun _ => by linarith, fun h => absurd h (by norm_num)⟩
  | 2 =>
    have h0 : hp2CosTail 2 = 0.25 + Real.exp (-2) * (Real.exp 1 / (Real.exp 1 - 1)) := rfl
    exact ⟨by linarith, fun _ => by linarith, fun _ => by linarith⟩
  | j + 3 =>
    have h0 : hp2CosTail (j + 3)
        = Real.exp (-((j : ℝ) + 2)) * (Real.exp 1 / (Real.exp 1 - 1)) := rfl
    have h1 : Real.exp (-((j : ℝ) + 2)) ≤ Real.exp (-2) :=
      Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have h2 := (mul_le_mul_of_nonneg_right h1 hE).trans hT
    exact ⟨by linarith, fun _ => by linarith, fun _ => by linarith⟩

/-- `∑_{i<M} e^{i+1-M} ≤ e/(e-1)`: the damping over the blocks below the depth. -/
lemma sum_range_exp_add_one_sub_le (M : ℕ) :
    ∑ i ∈ Finset.range M, Real.exp ((i : ℝ) + 1 - M) ≤ Real.exp 1 / (Real.exp 1 - 1) := by
  have hrefl := Finset.sum_range_reflect (fun i : ℕ => Real.exp ((i : ℝ) + 1 - M)) M
  beta_reduce at hrefl
  have hterm : ∀ j ∈ Finset.range M,
      Real.exp (((M - 1 - j : ℕ) : ℝ) + 1 - M) = Real.exp (-(j : ℝ)) := by
    intro j hj
    have hjM := Finset.mem_range.1 hj
    rw [Nat.cast_sub (show j ≤ M - 1 by omega), Nat.cast_sub (show 1 ≤ M by omega),
      Nat.cast_one]
    ring_nf
  rw [← hrefl, Finset.sum_congr rfl hterm]
  exact sum_exp_neg_le _

/-- **A sum of variance floors, in closed form**: for a set `s` of blocks in `[i₀, M)`,
`∑_{i∈s} hp2VarLo M i ≥ |s|(1/2 - 4·10⁻⁶) - hp2CosTail i₀/2 - 0.0159` (the damping
`∑ e^{i+1-M}/100 ≤ e/(100(e-1))`). -/
theorem card_mul_sub_le_sum_hp2VarLo {M i₀ : ℕ} {s : Finset ℕ}
    (hs : ∀ i ∈ s, i₀ ≤ i ∧ i < M) :
    (s.card : ℝ) * (1 / 2 - 4 / 10 ^ 6) - hp2CosTail i₀ / 2 - 0.0159
      ≤ ∑ i ∈ s, hp2VarLo M i := by
  have hF : ∑ i ∈ s, hp2CosFloor i ≤ hp2CosTail i₀ :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_Ico.2 (hs i hi))
      fun i _ _ => hp2CosFloor_nonneg i).trans (sum_Ico_hp2CosFloor_le i₀ M)
  have he1 : (2.7182 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hu : Real.exp 1 / (Real.exp 1 - 1) ≤ 1.5821 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hD : ∑ i ∈ s, Real.exp ((i : ℝ) + 1 - M) ≤ 1.5821 :=
    ((Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_range.2 (hs i hi).2)
      fun i _ _ => (Real.exp_pos _).le).trans (sum_range_exp_add_one_sub_le M)).trans hu
  have hsum : ∑ i ∈ s, hp2VarLo M i = ∑ _i ∈ s, (1 / 2 - 4 / 10 ^ 6 : ℝ)
      - (∑ i ∈ s, hp2CosFloor i) / 2 - (∑ i ∈ s, Real.exp ((i : ℝ) + 1 - M)) / 100 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold hp2VarLo
    ring
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- **The variance sums in closed form**: with `ν = 1/2 - 4·10⁻⁶` and `n = ⌊M/3⌋`,
`S₁(M) ≥ nν - hp2CosTail 0/2 - 0.0159`, `S₂(M) ≥ (M - 2n)ν - hp2CosTail n/2 - 0.0159` and
`S₃(M) ≥ nν - hp2CosTail (M - n)/2 - 0.0159` (`RMF.card_mul_sub_le_sum_hp2VarLo`; the tails are
at most `1.8642`, `1.1142` for `n ≥ 1` and `0.4642` for `M - n ≥ 2`, `RMF.hp2CosTail_le`). -/
theorem hp2VarSums_ge (M : ℕ) :
    ((M / 3 : ℕ) : ℝ) * (1 / 2 - 4 / 10 ^ 6) - hp2CosTail 0 / 2 - 0.0159 ≤ hp2VarSum₁ M
      ∧ ((M - M / 3 - M / 3 : ℕ) : ℝ) * (1 / 2 - 4 / 10 ^ 6) - hp2CosTail (M / 3) / 2 - 0.0159
        ≤ hp2VarSum₂ M
      ∧ ((M / 3 : ℕ) : ℝ) * (1 / 2 - 4 / 10 ^ 6) - hp2CosTail (M - M / 3) / 2 - 0.0159
        ≤ hp2VarSum₃ M := by
  refine ⟨?_, ?_, ?_⟩
  · have h := card_mul_sub_le_sum_hp2VarLo (M := M) (i₀ := 0) (s := Finset.range (M / 3))
      fun i hi => ⟨Nat.zero_le _, by have := Finset.mem_range.1 hi; omega⟩
    rw [Finset.card_range] at h
    exact h
  · have h := card_mul_sub_le_sum_hp2VarLo (M := M) (i₀ := M / 3)
      (s := Finset.Ico (M / 3) (M - M / 3))
      fun i hi => ⟨(Finset.mem_Ico.1 hi).1, by have := (Finset.mem_Ico.1 hi).2; omega⟩
    rw [Nat.card_Ico] at h
    exact h
  · have h := card_mul_sub_le_sum_hp2VarLo (M := M) (i₀ := M - M / 3)
      (s := Finset.Ico (M - M / 3) M) fun i hi => Finset.mem_Ico.1 hi
    rw [Nat.card_Ico, show M - (M - M / 3) = M / 3 by omega] at h
    exact h

/-! ### HP2's prefix bound at depth `M` -/

/-- **The Abel sum's cubic at width `1/16`**: `K₂(1/16, c) ≤ hp2PrefixK c` for `c ≥ 0`
(`RMF.slabAbelTwo_sixteenth_le`). -/
noncomputable def hp2PrefixK (c : ℝ) : ℝ := 0.532 * c ^ 3 + 0.8488 * c ^ 2 + 0.8499 * c + 0.425

/-- **The slab bound's prefactor**
`(1 + e^{-100})(1 + e^{-30})e^{2(3/2+ρ')}(3/2 + ρ' + c)·hp2PrefixK c`, `ρ' = 10⁻¹⁴`. -/
noncomputable def hp2SlabPrefactor (c : ℝ) : ℝ :=
  (1 + Real.exp (-100)) * (1 + Real.exp (-30)) * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14))
    * (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c

/-- **The slab bound at depth `M`**: `hp2SlabPrefactor c·2/(π√(2πS₁S₂S₃))` with the variance sums
`RMF.hp2VarSum₁`, `₂`, `₃` for `M ≥ 3`, and the pointwise `e^{2(3/2+10⁻¹⁵)}c²` for `M < 3`. -/
noncomputable def hp2SlabBound (M : ℕ) (c : ℝ) : ℝ :=
  if 3 ≤ M then hp2SlabPrefactor c
      * (2 / (π * √(2 * π * (hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M))))
  else Real.exp (2 * (3 / 2 + 1 / 10 ^ 15)) * c ^ 2

/-- **HP2's prefix bound at depth `M`**: the smaller of the pointwise bound
`e^{2(3/2+10⁻¹⁵)}c²` and the slab bound `RMF.hp2SlabBound M c`. -/
noncomputable def hp2PrefixBound (M : ℕ) (c : ℝ) : ℝ :=
  min (Real.exp (2 * (3 / 2 + 1 / 10 ^ 15)) * c ^ 2) (hp2SlabBound M c)

/-- The cubic is nonnegative for `c ≥ 0`. -/
lemma hp2PrefixK_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ hp2PrefixK c := by
  unfold hp2PrefixK
  positivity

/-- The slab bound's prefactor is nonnegative for `c ≥ 0`. -/
lemma hp2SlabPrefactor_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ hp2SlabPrefactor c := by
  have := hp2PrefixK_nonneg hc
  unfold hp2SlabPrefactor
  positivity

/-- `ρ' = 10⁻¹⁴` covers HP1's `ρ = 10⁻¹⁵` and the slack `2e^{-40}`. -/
lemma rho_add_two_mul_exp_neg_forty_le : (1 : ℝ) / 10 ^ 15 + 2 * Real.exp (-40) ≤ 1 / 10 ^ 14 := by
  have h40 : (10 : ℝ) ^ 16 ≤ Real.exp 40 := by
    simpa using le_exp_natCast_of_le_pow (c := 2.7) (k := 40) (N := 10 ^ 16) (by norm_num)
      (by linarith [Real.exp_one_gt_d9]) (by norm_num)
  have he : Real.exp (-40) ≤ 1 / 10 ^ 16 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h40
  linarith

section Prefix

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **HP2's prefix term on HP1's tube by slabs of width `1/16`**: for `3 ≤ M ≤ r`, `c > 0`,
`b ≤ 3/2 + 10⁻¹⁵` and the block data of `RMF.integral_hp2Tube_exp_mul_le_width`,
`E[1_{H(k,h)} e^{2Z_M}(max(b - Z_M, 0) + c)²] ≤ hp2SlabPrefactor c·2/(π√(2πS₁S₂S₃))`:
`K₂(1/16, c) ≤ hp2PrefixK c` (`RMF.slabAbelTwo_sixteenth_le`) and the widening
`(1 + 64e^{-40})² ≤ 1 + e^{-30}`. -/
theorem integral_hp1Tube_exp_mul_sq_le_sixteenth (hX : IsRademacherPrimeValues X μ)
    {k M r y : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσM : σ * Real.exp ((k : ℝ) + M) ≤ 1 / 200)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) (hM : 3 ≤ M) (hMr : M ≤ r)
    {c S₁ S₂ S₃ b : ℝ} (hc0 : 0 < c)
    (hc : ∀ i, i < M → √(π * windowVarH X μ y k σ h i / 2) ≤ c)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hS₃ : 0 < S₃)
    (h₁ : S₁ ≤ ∑ i ∈ Finset.range (M / 3), windowVarH X μ y k σ h i)
    (h₂ : S₂ ≤ ∑ i ∈ Finset.Ico (M / 3) (M - M / 3), windowVarH X μ y k σ h i)
    (h₃ : S₃ ≤ ∑ i ∈ Finset.Ico (M - M / 3) M, windowVarH X μ y k σ h i)
    (hb : b ≤ 3 / 2 + 1 / 10 ^ 15) :
    ∫ ω, (hp1Tube X μ y k r σ h).indicator (fun ω =>
        Real.exp (2 * windowZ X μ y k σ h M ω)
          * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ 2) ω
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
      ≤ hp2SlabPrefactor c * (2 / (π * √(2 * π * (S₁ * S₂ * S₃)))) := by
  have hs₁ : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs₁
  have hmain := integral_hp2Tube_exp_mul_le_width hX hk hh hσ hσM hy hM
    (a := 3 / 2) (A := 5 / 2) (B := 3) (ρ := 1 / 10 ^ 15) (ρ' := 1 / 10 ^ 14)
    (K := hp2PrefixK c) (w := 1 / 16) (b := b) (j := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc0 hc hS₁ hS₂ hS₃
    h₁ h₂ h₃ hb rho_add_two_mul_exp_neg_forty_le (by norm_num)
    (fun L => (sum_slab_width_le_slabAbelTwo (by norm_num) hc0.le L).trans
      (slabAbelTwo_sixteenth_le hc0.le))
  have hW := one_add_widening_sixteenth_le
  have hP : 0 ≤ (1 + Real.exp (-100)) * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14))
      * (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c * (2 / (π * √(2 * π * (S₁ * S₂ * S₃)))) := by
    have := hp2PrefixK_nonneg hc0.le
    positivity
  refine le_trans (integral_mono_of_nonneg
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun ω _ => by positivity) ω)
    (integrable_indicator_hp2Tube_exp_mul_sq hX (a := 3 / 2) (A := 5 / 2) (B := 3)
      (ρ := 1 / 10 ^ 15) (by norm_num) hb hc0.le) (ae_of_all _ fun ω => ?_)) (hmain.trans ?_)
  · exact Set.indicator_le_indicator_of_subset (hp1Tube_subset_hp2Tube hMr y k σ h)
      (fun ω => by positivity) ω
  · calc (1 + Real.exp (-100)) * (1 + 4 * Real.exp (-40) / (1 / 16)) ^ 2
          * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14)) * (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c
          * (2 / (π * √(2 * π * (S₁ * S₂ * S₃))))
        = (1 + 4 * Real.exp (-40) / (1 / 16)) ^ 2 * ((1 + Real.exp (-100))
          * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14)) * (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c
          * (2 / (π * √(2 * π * (S₁ * S₂ * S₃))))) := by ring
      _ ≤ (1 + Real.exp (-30)) * ((1 + Real.exp (-100))
          * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14)) * (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c
          * (2 / (π * √(2 * π * (S₁ * S₂ * S₃))))) := mul_le_mul_of_nonneg_right hW hP
      _ = hp2SlabPrefactor c * (2 / (π * √(2 * π * (S₁ * S₂ * S₃)))) := by
          unfold hp2SlabPrefactor
          ring

/-- **HP2's prefix bound, as a function of the depth only.**  For Rademacher prime values, a
window scale `k ≥ 20`, `h ∈ halfWindow k`, `σ ≥ 0` with `σe^{k+r} ≤ 1/200`, the compared blocks
`m < r` below the tilt cutoff `y`, a prefix `M ≤ r`, `c ≥ 1.05` and `b ≤ 3/2 + 10⁻¹⁵`, under the
one-point tilt at `s_h`:
`E[1_{H(k,h)} e^{2Z_M}(max(b - Z_M, 0) + c)²] ≤ RMF.hp2PrefixBound M c`.  The pointwise bound
(`RMF.integral_hp1Tube_exp_mul_sq_le_short_of_one_le`) for every `M`; for `M ≥ 3` the slabs of width
`1/16` (`RMF.integral_hp1Tube_exp_mul_sq_le_sixteenth`) with `c ≥ √(πV_i/2)`
(`RMF.sqrt_pi_windowVarH_div_two_le`) and the variance sums `RMF.hp2VarSums_le`. -/
theorem integral_hp1Tube_exp_mul_sq_le_hp2PrefixBound (hX : IsRademacherPrimeValues X μ)
    {k M r y : ℕ} {σ h b c : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hMr : M ≤ r)
    (hc : 1.05 ≤ c) (hb : b ≤ 3 / 2 + 1 / 10 ^ 15) :
    ∫ ω, (hp1Tube X μ y k r σ h).indicator (fun ω =>
        Real.exp (2 * windowZ X μ y k σ h M ω)
          * (max (b - windowZ X μ y k σ h M ω) 0 + c) ^ 2) ω
        ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
      ≤ hp2PrefixBound M c := by
  have hpt := integral_hp1Tube_exp_mul_sq_le_short_of_one_le hX (k := k) (y := y) (h := h)
    hσ hMr hb (by linarith : (1 : ℝ) ≤ c)
  refine le_min hpt ?_
  unfold hp2SlabBound
  split_ifs with hM3
  · have hσM : σ * Real.exp ((k : ℝ) + M) ≤ 1 / 200 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
        have : (M : ℝ) ≤ r := by exact_mod_cast hMr
        linarith)) hσ) hσr
    have hyM : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y := fun m hm => hy m (by omega)
    have hσm : ∀ i, i < M → σ * Real.exp ((k : ℝ) + i + 1) ≤ 1 / 200 := fun i hi =>
      le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
        have : ((i : ℝ) + 1) ≤ M := by exact_mod_cast hi
        linarith)) hσ) hσM
    obtain ⟨h₁, h₂, h₃⟩ := hp2VarSums_le hX y hk hh hσ hσM hyM
    exact integral_hp1Tube_exp_mul_sq_le_sixteenth hX hk hh hσ hσM hyM hM3 hMr (by linarith)
      (fun i hi => sqrt_pi_windowVarH_div_two_le hX y hk hh hσ (hσm i hi) (hyM i hi) hc)
      (hp2VarSum₁_pos hM3) (hp2VarSum₂_pos hM3) (hp2VarSum₃_pos hM3) h₁ h₂ h₃ hb
  · exact hpt

end Prefix

/-! ### The slab bound in closed form -/

/-- **The slab bound's prefactor in numerals**: `hp2SlabPrefactor c ≤ 20.0857(3/2 + 10⁻¹⁴ + c)·
hp2PrefixK c` for `c ≥ 0` (`e^{3+2·10⁻¹⁴} ≤ 20.08554`, `(1 + e^{-100})(1 + e^{-30}) ≤ 1 + 10⁻⁸`). -/
lemma hp2SlabPrefactor_le {c : ℝ} (hc : 0 ≤ c) :
    hp2SlabPrefactor c ≤ 20.0857 * ((3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c) := by
  have hlin : 0 ≤ (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c :=
    mul_nonneg (by positivity) (hp2PrefixK_nonneg hc)
  have he3 : Real.exp (2 * (3 / 2 + 1 / 10 ^ 14)) ≤ 20.08554 := by
    interval_decide (trust := kernel)
  have he20 := exp_neg_twenty_le_numeral
  have he100 : Real.exp (-100) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by norm_num)
  have he30 : Real.exp (-30) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by norm_num)
  have ha0 := Real.exp_pos (-100)
  have hb0 := Real.exp_pos (-30)
  have hab : Real.exp (-100) * Real.exp (-30) ≤ 1 / 485000000 * (1 / 485000000) :=
    mul_le_mul (he100.trans he20) (he30.trans he20) hb0.le (by norm_num)
  have h1 : (1 + Real.exp (-100)) * (1 + Real.exp (-30)) ≤ 1.00000001 := by
    have hexp : (1 + Real.exp (-100)) * (1 + Real.exp (-30))
        = 1 + Real.exp (-100) + Real.exp (-30) + Real.exp (-100) * Real.exp (-30) := by ring
    rw [hexp]
    linarith
  have hfac : (1 + Real.exp (-100)) * (1 + Real.exp (-30))
      * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14)) ≤ 20.0857 := by
    have h2 := mul_le_mul h1 he3 (Real.exp_pos _).le (by norm_num)
    linarith
  unfold hp2SlabPrefactor
  calc (1 + Real.exp (-100)) * (1 + Real.exp (-30)) * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14))
        * (3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c
      = (1 + Real.exp (-100)) * (1 + Real.exp (-30)) * Real.exp (2 * (3 / 2 + 1 / 10 ^ 14))
        * ((3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c) := by ring
    _ ≤ 20.0857 * ((3 / 2 + 1 / 10 ^ 14 + c) * hp2PrefixK c) :=
        mul_le_mul_of_nonneg_right hfac hlin

/-- **The slab bound from lower bounds on the variance sums**: for `M ≥ 3`, `c ≥ 0` and
`0 < L_j ≤ S_j(M)`, `hp2SlabBound M c ≤ hp2SlabPrefactor c·2/(π√(2πL₁L₂L₃))` (closed forms for
the `L_j` in `RMF.hp2VarSums_ge`). -/
theorem hp2SlabBound_le_of_le {M : ℕ} (hM : 3 ≤ M) {c L₁ L₂ L₃ : ℝ} (hc : 0 ≤ c)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃) (h₁ : L₁ ≤ hp2VarSum₁ M)
    (h₂ : L₂ ≤ hp2VarSum₂ M) (h₃ : L₃ ≤ hp2VarSum₃ M) :
    hp2SlabBound M c ≤ hp2SlabPrefactor c * (2 / (π * √(2 * π * (L₁ * L₂ * L₃)))) := by
  unfold hp2SlabBound
  rw [if_pos hM]
  refine mul_le_mul_of_nonneg_left ?_ (hp2SlabPrefactor_nonneg hc)
  have hprod : L₁ * L₂ * L₃ ≤ hp2VarSum₁ M * hp2VarSum₂ M * hp2VarSum₃ M :=
    mul_le_mul (mul_le_mul h₁ h₂ hL₂.le (hL₁.le.trans h₁)) h₃ hL₃.le
      (mul_nonneg (hL₁.le.trans h₁) (hL₂.le.trans h₂))
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hprod (by positivity))) Real.pi_pos.le

end RMF
