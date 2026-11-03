/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Grid.Data
import RMF.UniformLower.ComparisonFloor

/-!
# The window's first moment at the floor `20`, Rademacher side

The window's first moment from window scale `k ≥ 20`: under the tilt by `|F_y(½+σ+ih)|²` the
window event has probability at least `(1 - e^{-100})·RMF.hp1LowerBoundV2 … / √r`, with the
Gaussian side `RMF.le_measure_windowEvent_gaussian_v2`
(`RMF.le_measure_windowEvent_rademacher_floor`; with `RMF.HP1WindowHyps` bundled,
`RMF.le_measure_windowEvent_of_hyps_floor`, whose cell data
`RMF/UniformLower/HP1Grid/DataFloor.lean` discharges from `k ≥ 20`).

* **The comparison**: `RMF.exists_isBoxComparison_rademacher_budget` at offset `k`, windows
  `e^{-40}/(m+1)²`, envelope `58(m+1)`, variances in `[1/100, 1.01]`, determinants
  `RMF.windowBlockDet m`, means at most `2.03` (`RMF.window_block_comparison_inputs_budget`), and
  the budget `RMF.hp1_budget` from `k = 20`.
* **The barrier envelope from the event's own barriers** (`RMF.hp1FloorEnv`): `0` at `j = 0` (the
  barrier comparison asks for it only from `j = 1`) and `α + βj` from `j = 1`,
  `α = max(A, a, A', M₁) + ρ`, `β = max(B + 1.52, B')`: the height walk's summed means are at most
  `1.52j` (`RMF.abs_window_block_means_le`).  Two consecutive envelopes and a window fit in
  `58(m+1)` once `α + 2β ≤ 58` (`RMF.hp1FloorEnv_add_le`); at HP1's parameters
  `α + 2β = 49.04 + 10⁻¹⁵` (`RMF.hp1_floor_env_numeral`).
* **The slack, the regression realisation and the re-centring**: the barrier comparison at slack
  `ρ` (`RMF.le_measure_barrierEventPair_slack`), the comparison moved onto the regression
  realisation of the block laws, and the height walk re-centred by its means
  (`RMF.barrierEventPair_subset_of_add_fst`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace RMF

/-! ### The barrier envelope -/

/-- **HP1's barrier envelope at the floor**: `0` at `j = 0`, `α + βj` from `j = 1`. -/
noncomputable def hp1FloorEnv (α β : ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else α + β * j

lemma hp1FloorEnv_of_ne_zero (α β : ℝ) {j : ℕ} (hj : j ≠ 0) : hp1FloorEnv α β j = α + β * j := by
  rw [hp1FloorEnv, if_neg hj]

lemma hp1FloorEnv_nonneg {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (j : ℕ) : 0 ≤ hp1FloorEnv α β j := by
  unfold hp1FloorEnv
  split_ifs
  · exact le_rfl
  · positivity

/-- **Two consecutive barrier envelopes and a window fit in `C(m+1)`**: for `0 ≤ α`, a window
`w ≤ β` and `α + 2β ≤ C` (block `0`: `α + β + w`; block `m ≥ 1`: `2α + β(2m+1) + w`). -/
lemma hp1FloorEnv_add_le {α β C w : ℝ} (m : ℕ) (hα : 0 ≤ α) (hw : w ≤ β) (hC : α + 2 * β ≤ C) :
    hp1FloorEnv α β m + hp1FloorEnv α β (m + 1) + w ≤ C * ((m : ℝ) + 1) := by
  rw [hp1FloorEnv_of_ne_zero α β (Nat.succ_ne_zero m)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [hp1FloorEnv, if_pos rfl]
    push_cast
    linarith
  · rw [hp1FloorEnv_of_ne_zero α β (by omega)]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : 0 ≤ (C - α - 2 * β) * ((m : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ α * ((m : ℝ) - 1) := mul_nonneg hα (by linarith)
    push_cast
    linarith

/-- **HP1's envelope condition at its parameters** `(a, A, B) = (3/2, 5/2, 3)`, `A' = 40`,
`B' = 2`, `M₁ = 7`, `ρ = 10⁻¹⁵`: `α + 2β = 40 + 10⁻¹⁵ + 2·4.52 ≤ 58`. -/
lemma hp1_floor_env_numeral :
    max (max (5 / 2 : ℝ) (3 / 2)) (max 40 7) + 1 / 10 ^ 15 + 2 * max (3 + 1.52) 2 ≤ 58 := by
  norm_num [max_def]

/-! ### The window event at the floor -/

section RademacherFloor

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The window's first moment, Rademacher side, from `k ≥ 20`.**  For a Rademacher family, a
height `h` in the window at `k ≥ 20` and `r ≥ n₀` blocks with `σe^{k+r} ≤ 1/200` below the tilt's
cutoff `y`, under the tilt by `|F_y(½+σ+ih)|²` the window event has probability at least
`(1 - e^{-100})·RMF.hp1LowerBoundV2 … / √r`, given the envelope condition `α + 2β ≤ 58`,
`α = max(A, a, A', M₁) + ρ`, `β = max(B + 1.52, B')`, and hypotheses on the block data as in
`RMF.le_measure_windowEvent_gaussian_v2`.  The comparison is
`RMF.exists_isBoxComparison_rademacher_budget` (envelope `58(m+1)`, `RMF.hp1_budget`), the barrier
envelope `RMF.hp1FloorEnv α β`. -/
theorem le_measure_windowEvent_rademacher_floor (hX : IsRademacherPrimeValues X μ)
    {k r y n₀ m₀ : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y)
    (hn₀ : m₀ + 3 ≤ n₀) (hr : n₀ ≤ r)
    {vmin vmax a A B A' B' M₁ K₂ ρ L t Λ AW BW Klate KR σR2 : ℝ}
    (hρ : 2 * Real.exp (-40) ≤ ρ)
    (henv : max (max A a) (max A' M₁) + ρ + 2 * max (B + 1.52) B' ≤ 58)
    (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → m < r →
      vmin ≤ windowVarH X μ y k σ h m ∧ windowVarH X μ y k σ h m ≤ vmax)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 2 * vmax < B)
    (hCn : (a + A + 2 * B) ^ 2 ≤ 2 * (((n₀ : ℝ) - 2) * vmin))
    (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hΛ : ∑ m ∈ Finset.Ico 2 r,
      max 0 (t * windowMeanR X μ y k σ h m + t ^ 2 * (max (windowSlope X μ y k σ h m) 0 ^ 2
        * windowVarH X μ y k σ h m + windowResid X μ y k σ h m) / 2) ≤ Λ)
    (hBW : ∀ m, 2 ≤ m → m < r →
      windowResid X μ y k σ h m / 2 - windowMeanR X μ y k σ h m ≤ BW)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2),
      min (windowSlope X μ y k σ h m) 0 ^ 2 * windowVarH X μ y k σ h m ≤ σR2) (hσR0 : 0 < σR2)
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) r,
      |min (windowSlope X μ y k σ h m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate)
    (hKL : Klate ≤ L)
    (hKR : ∑ m ∈ Finset.Ico 2 r,
      |windowSlope X μ y k σ h m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR)
    (hM₁ : |windowMeanR X μ y k σ h 0| ≤ M₁)
    (hK₂ : 0 ≤ K₂ + windowMeanR X μ y k σ h 0 + windowMeanR X μ y k σ h 1)
    (hA' : K₂ + KR + AW ≤ A') (hBW' : BW ≤ B') (hB'0 : 0 ≤ B') :
    (1 - Real.exp (-100)) * hp1LowerBoundV2 n₀ m₀ vmin vmax
        (windowVarH X μ y k σ h 0) (windowVarH X μ y k σ h 1)
        (windowResid X μ y k σ h 0) (windowResid X μ y k σ h 1)
        (windowSlope X μ y k σ h 0) (windowSlope X μ y k σ h 1)
        (windowMeanR X μ y k σ h 0) (windowMeanR X μ y k σ h 1)
        a A B M₁ K₂ ρ L t Λ AW Klate σR2 / √(r : ℝ)
      ≤ (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
          (barrierEventPair (fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω)) r
            (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ)
            (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ)
            (fun j => if j = 1 then -M₁ - ρ else -A' - B' * j - ρ)
            (fun j => if j = 1 then M₁ + ρ else 0))).toReal := by
  classical
  /- basic facts -/
  have hk' : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs₁ : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs₁
  have hσm : ∀ m, m < r → σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200 := fun m hm =>
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      have : ((m : ℝ) + 1) ≤ r := by exact_mod_cast hm
      linarith)) hσ) hσr
  /- the per-block inputs: variances, determinants, means -/
  have hin : ∀ m, m < r →
      (1 / 100 ≤ windowVarH X μ y k σ h m ∧ windowVarH X μ y k σ h m ≤ 1.01)
        ∧ (1 / 100 ≤ windowVarR X μ y k σ h m ∧ windowVarR X μ y k σ h m ≤ 1.01)
        ∧ windowBlockDet m ≤ windowVarH X μ y k σ h m * windowVarR X μ y k σ h m
          - windowCov X μ y k σ h m ^ 2
        ∧ (|windowMeanH X μ y k σ h m| ≤ 2.03 ∧ |windowMeanR X μ y k σ h m| ≤ 2.03) :=
    fun m hm => window_block_comparison_inputs_budget hX y hk hh hσ (hσm m hm) (hy m hm)
  have hRpos : ∀ m, m < r → 0 < windowResid X μ y k σ h m := by
    intro m hm
    obtain ⟨⟨hV1l, -⟩, -, hdet, -⟩ := hin m hm
    have hV1 : (0 : ℝ) < windowVarH X μ y k σ h m := lt_of_lt_of_le (by norm_num) hV1l
    have hδ := le_windowBlockDet m
    rw [windowResid, pairResidVar, sub_pos, div_lt_iff₀ hV1]
    nlinarith [hdet, hδ]
  /- the height means: at most `1.52` per block -/
  have hmean : ∀ i, i < r → |windowMeanH X μ y k σ h i| ≤ 1.52 := fun i hi =>
    (abs_window_block_means_le hX y hk hh hσ (hσm i hi) (hy i hi)).1
  have hsum : ∀ j, j ≤ r → |∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i| ≤ 1.52 * j := by
    intro j hj
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun i hi =>
      hmean i (by have := Finset.mem_range.1 hi; omega)) (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  /- the windows `e^{-40}/(m+1)²` -/
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
  have hwsum : ∀ j, j ≤ r → ∑ m ∈ Finset.range j, Real.exp (-40) * blockWindow m ≤ ρ :=
    fun j _ => by
      have := sum_mul_blockWindow_le (Real.exp_pos (-40)).le 0 j
      simp only [add_zero] at this
      linarith
  /- the barrier envelope `RMF.hp1FloorEnv α β` from the event's barriers -/
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hM₁0 : 0 ≤ M₁ := le_trans (abs_nonneg _) hM₁
  have hvmax0 : 0 < vmax := lt_of_lt_of_le hvmin
    (le_trans (hvb 2 le_rfl (by omega)).1 (hvb 2 le_rfl (by omega)).2)
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = max (max A a) (max A' M₁) + ρ := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = max (B + 1.52) B' := ⟨_, rfl⟩
  have hαA : A + ρ ≤ α := by
    rw [hαdef]; linarith [le_max_left (max A a) (max A' M₁), le_max_left A a]
  have hαa : a + ρ ≤ α := by
    rw [hαdef]; linarith [le_max_left (max A a) (max A' M₁), le_max_right A a]
  have hαA' : A' + ρ ≤ α := by
    rw [hαdef]; linarith [le_max_right (max A a) (max A' M₁), le_max_left A' M₁]
  have hαM : M₁ + ρ ≤ α := by
    rw [hαdef]; linarith [le_max_right (max A a) (max A' M₁), le_max_right A' M₁]
  have hβB : B + 1.52 ≤ β := by rw [hβdef]; exact le_max_left _ _
  have hβB' : B' ≤ β := by rw [hβdef]; exact le_max_right _ _
  have hα0 : 0 ≤ α := by linarith
  have hβ0 : 1.52 ≤ β := by linarith
  have hαβ : α + 2 * β ≤ 58 := by rw [hαdef, hβdef]; exact henv
  have hM0 : ∀ j, 0 ≤ hp1FloorEnv α β j := hp1FloorEnv_nonneg hα0 (by linarith)
  have hM₁env : ∀ j, 1 ≤ j → j ≤ r →
      -hp1FloorEnv α β j ≤ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ
        ∧ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ ≤ hp1FloorEnv α β j := by
    intro j hj1 hjr
    have hS := abs_le.1 (hsum j hjr)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [hp1FloorEnv_of_ne_zero α β (by omega)]
    have h1 : (B + 1.52) * j ≤ β * j := mul_le_mul_of_nonneg_right hβB hj0
    have h2 : 1.52 * (j : ℝ) ≤ β * j := mul_le_mul_of_nonneg_right hβ0 hj0
    constructor <;> linarith
  have hM₂env : ∀ j, 1 ≤ j → j ≤ r →
      -hp1FloorEnv α β j ≤ (if j = 1 then -M₁ - ρ else -A' - B' * j - ρ)
        ∧ (if j = 1 then M₁ + ρ else 0) ≤ hp1FloorEnv α β j := by
    intro j hj1 _
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [hp1FloorEnv_of_ne_zero α β (by omega)]
    have h1 : B' * j ≤ β * j := mul_le_mul_of_nonneg_right hβB' hj0
    have h2 : 0 ≤ β * j := mul_nonneg (by linarith) hj0
    split_ifs with hj
    · rw [hj]
      push_cast
      constructor <;> linarith
    · constructor <;> linarith
  have hMM : ∀ m, m < r → hp1FloorEnv α β m + hp1FloorEnv α β (m + 1)
      + Real.exp (-40) * blockWindow m ≤ 58 * ((m : ℝ) + 1) := fun m _ =>
    hp1FloorEnv_add_le m hα0 (by linarith [hwle m]) hαβ
  /- the comparison (`RMF.exists_isBoxComparison_rademacher_budget`) at offset `k` -/
  have hσtop : |σ| * Real.log (blockScale (k : ℝ) r) ≤ 1 := by
    rw [abs_of_nonneg hσ, log_blockScale, show (r : ℝ) + k = k + r by ring]
    linarith
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmpk⟩ :=
    exists_isBoxComparison_rademacher_budget hX (θ := (k : ℝ)) (σ := σ) (r := r) (y := y)
      (s₁ := shiftLine σ h) (s₂ := shiftLine σ 0) (vl := 1 / 100) (vu := 1.01) (K := 2.03)
      (w := fun m => Real.exp (-40) * blockWindow m) (M := fun m => 58 * ((m : ℝ) + 1))
      (δ := windowBlockDet) hk' hy (re_shiftLine σ h) (re_shiftLine σ 0) hσtop
      (fun m _ => ⟨hwpos m, hwle m⟩) (by norm_num) (by norm_num)
      (fun m hm => (hin m hm).1) (fun m hm => (hin m hm).2.1)
      (fun m _ => lt_of_lt_of_le (by norm_num) (le_windowBlockDet m))
      (fun m hm => (hin m hm).2.2.1) (fun m hm => (hin m hm).2.2.2)
      (fun m _ => hp1_budget hk' (by norm_num) le_rfl m)
  have hcmp0 : IsBoxComparison
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ) Q
      (fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω)) N
      (fun m => Real.exp (-40) * blockWindow m) (fun m => 58 * ((m : ℝ) + 1)) r
      (Real.exp (-100)) := by
    have h0 := hcmpk 0 (Nat.zero_le r)
    have hZeq : (fun m ω => ∑ p ∈ primeBlockSub (k : ℝ) (m + 0),
        (localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h))) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))) (X (p : ℕ) ω)))
        = fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω) := by
      funext m ω
      rw [add_zero]
      exact Prod.ext Prod.fst_sum Prod.snd_sum
    rw [hZeq] at h0
    simpa only [add_zero, Nat.sub_zero] using h0
  /- the regression realisation of the block laws, padded past `r` -/
  obtain ⟨m₁', hm₁'⟩ : ∃ f : ℕ → ℝ, f = fun m => if m < r then windowMeanH X μ y k σ h m else 0 :=
    ⟨_, rfl⟩
  obtain ⟨m₂', hm₂'⟩ : ∃ f : ℕ → ℝ, f = fun m => if m < r then windowMeanR X μ y k σ h m else 0 :=
    ⟨_, rfl⟩
  obtain ⟨V₁', hV₁'⟩ : ∃ f : ℕ → ℝ,
      f = fun m => if m < r then windowVarH X μ y k σ h m else vmin := ⟨_, rfl⟩
  obtain ⟨V₂', hV₂'⟩ : ∃ f : ℕ → ℝ,
      f = fun m => if m < r then windowVarR X μ y k σ h m else vmin := ⟨_, rfl⟩
  obtain ⟨cv', hcv'⟩ : ∃ f : ℕ → ℝ, f = fun m => if m < r then windowCov X μ y k σ h m else 0 :=
    ⟨_, rfl⟩
  have hm₁r : ∀ m, m < r → m₁' m = windowMeanH X μ y k σ h m := fun m hm => by
    simp only [hm₁', if_pos hm]
  have hm₂r : ∀ m, m < r → m₂' m = windowMeanR X μ y k σ h m := fun m hm => by
    simp only [hm₂', if_pos hm]
  have hV₁r : ∀ m, m < r → V₁' m = windowVarH X μ y k σ h m := fun m hm => by
    simp only [hV₁', if_pos hm]
  have hV₂r : ∀ m, m < r → V₂' m = windowVarR X μ y k σ h m := fun m hm => by
    simp only [hV₂', if_pos hm]
  have hcvr : ∀ m, m < r → cv' m = windowCov X μ y k σ h m := fun m hm => by
    simp only [hcv', if_pos hm]
  obtain ⟨Ω₁, Ω₂, mΩ₁, mΩ₂, Q₁, Q₂, G₁, Zr, G₂, W, N', hQ₁, hQ₂, hG₁, hG₂, hN'm, hN'i, hshear,
    hZG, hWG, hN'law⟩ := exists_gaussianWalk_pair_regression m₁' m₂' V₁' V₂' cv'
  haveI := hQ₁
  haveI := hQ₂
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ≥0, v = fun i => (V₁' i).toNNReal := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℝ≥0,
      s = fun i => (pairResidVar (V₁' i) (V₂' i) (cv' i)).toNNReal := ⟨_, rfl⟩
  obtain ⟨β', hβdef'⟩ : ∃ β' : ℕ → ℝ, β' = fun i => pairSlope (V₁' i) (cv' i) := ⟨_, rfl⟩
  have hGv : IsGaussianWalk G₁ v Q₁ := by rw [hvdef]; exact hG₁
  have hGs : IsGaussianWalk G₂ s Q₂ := by rw [hsdef]; exact hG₂
  have hvm : ∀ m, m < r → ((v m : ℝ≥0) : ℝ) = windowVarH X μ y k σ h m := fun m hm => by
    rw [hvdef]
    simp only [hV₁r m hm]
    exact Real.coe_toNNReal _ (NNReal.coe_nonneg _)
  have hvpad : ∀ m, r ≤ m → ((v m : ℝ≥0) : ℝ) = vmin := fun m hm => by
    rw [hvdef]
    simp only [hV₁', if_neg (show ¬ m < r by omega)]
    exact Real.coe_toNNReal _ hvmin.le
  have hsm : ∀ m, m < r → ((s m : ℝ≥0) : ℝ) = windowResid X μ y k σ h m := fun m hm => by
    rw [hsdef]
    simp only [hV₁r m hm, hV₂r m hm, hcvr m hm]
    exact Real.coe_toNNReal _ (hRpos m hm).le
  have hβm : ∀ m, m < r → β' m = windowSlope X μ y k σ h m := fun m hm => by
    rw [hβdef']
    simp only [hV₁r m hm, hcvr m hm]
    rfl
  /- the comparison, moved onto the realisation -/
  have hcmp' : IsBoxComparison
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
      (Q₁.prod Q₂) (fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω)) N'
      (fun m => Real.exp (-40) * blockWindow m) (fun m => 58 * ((m : ℝ) + 1)) r
      (Real.exp (-100)) := by
    refine hcmp0.congr_law hNm hN'm hNi hN'i fun m hm => ?_
    rw [hNlaw m hm, hN'law m, hm₁r m hm, hm₂r m hm, hV₁r m hm, hV₂r m hm, hcvr m hm]
    rfl
  /- the barrier comparison at slack `ρ`, the barrier envelope `RMF.hp1FloorEnv α β` -/
  have hslack := le_measure_barrierEventPair_slack
    (P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
    (Q := Q₁.prod Q₂) (Z := fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω)) (N := N')
    (w := fun m => Real.exp (-40) * blockWindow m) (M := hp1FloorEnv α β)
    (M' := fun m => 58 * ((m : ℝ) + 1))
    (u₁ := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ)
    (v₁ := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ)
    (u₂ := fun j => if j = 1 then -M₁ - ρ else -A' - B' * j - ρ)
    (v₂ := fun j => if j = 1 then M₁ + ρ else 0) (n := r) (ε := Real.exp (-100)) (ρ := ρ)
    (fun m => (measurable_halfBlock hX _ _ _ m).prodMk (measurable_halfBlock hX _ _ _ m))
    hN'm hwpos hwsum hM0 hM₁env hM₂env hMM hcmp'
  /- the Gaussian side, v2 (`RMF.le_measure_windowEvent_gaussian_v2`) -/
  have hv0 : 0 < ((v 0 : ℝ≥0) : ℝ) := by
    rw [hvm 0 (by omega)]; linarith [(hin 0 (by omega)).1.1]
  have hv1 : 0 < ((v 1 : ℝ≥0) : ℝ) := by
    rw [hvm 1 (by omega)]; linarith [(hin 1 (by omega)).1.1]
  have hvmm : vmin ≤ vmax := le_trans (hvb 2 le_rfl (by omega)).1 (hvb 2 le_rfl (by omega)).2
  have hvb' : ∀ m, 2 ≤ m → vmin ≤ ((v m : ℝ≥0) : ℝ) ∧ ((v m : ℝ≥0) : ℝ) ≤ vmax := by
    intro m hm2
    rcases lt_or_ge m r with hmr | hmr
    · rw [hvm m hmr]; exact hvb m hm2 hmr
    · rw [hvpad m hmr]; exact ⟨le_rfl, hvmm⟩
  have hΛ' : ∑ m ∈ Finset.Ico 2 r, max 0 (t * m₂' m
      + t ^ 2 * (max (β' m) 0 ^ 2 * ((v m : ℝ≥0) : ℝ) + ((s m : ℝ≥0) : ℝ)) / 2) ≤ Λ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun m hm => ?_)) hΛ
    have hmr := (Finset.mem_Ico.1 hm).2
    rw [hm₂r m hmr, hsm m hmr, hβm m hmr, hvm m hmr]
  have hBW₂ : ∀ m, 2 ≤ m → m < r → ((s m : ℝ≥0) : ℝ) / 2 - m₂' m ≤ BW := fun m hm2 hmr => by
    rw [hsm m hmr, hm₂r m hmr]; exact hBW m hm2 hmr
  have hσR' : ∑ m ∈ Finset.Ico 2 (m₀ + 2), min (β' m) 0 ^ 2 * ((v m : ℝ≥0) : ℝ) ≤ σR2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun m hm => ?_)) hσR
    have hmr : m < r := by have := (Finset.mem_Ico.1 hm).2; omega
    rw [hβm m hmr, hvm m hmr]
  have hKlate' : ∑ m ∈ Finset.Ico (m₀ + 2) r,
      |min (β' m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun m hm => ?_)) hKlate
    rw [hβm m (Finset.mem_Ico.1 hm).2]
  have hKR' : ∑ m ∈ Finset.Ico 2 r,
      |β' m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun m hm => ?_)) hKR
    rw [hβm m (Finset.mem_Ico.1 hm).2]
  have hM₁' : |m₂' 0| ≤ M₁ := by rw [hm₂r 0 (by omega)]; exact hM₁
  have hK₂' : 0 ≤ K₂ + m₂' 0 + m₂' 1 := by
    rw [hm₂r 0 (by omega), hm₂r 1 (by omega)]; exact hK₂
  have hgauss := le_measure_windowEvent_gaussian_v2 hGv hGs β' m₂' hn₀ hr
    (vmin := vmin) (vmax := vmax) (a := a) (A := A) (B := B) (A' := A') (B' := B') (M₁ := M₁)
    (K₂ := K₂) (ρ := ρ) (L := L) (t := t) (Λ := Λ) (AW := AW) (BW := BW)
    (Klate := Klate) (KR := KR) (σR2 := σR2)
    hv0 hv1 hvmin hvb' ha hA hB hCn ht hAW hΛ' hBW₂ hσR' hσR0 hKlate' hKL hKR' hM₁' hK₂'
    hA' hBW' hB'0
  rw [hvm 0 (by omega), hvm 1 (by omega), hsm 0 (by omega), hsm 1 (by omega), hβm 0 (by omega),
    hβm 1 (by omega), hm₂r 0 (by omega), hm₂r 1 (by omega)] at hgauss
  /- re-centring walk 1: the Gaussian event lies in the narrowed event of the realisation -/
  have hsub : barrierEventPair
        (fun m ω => ((G₁ m ω.1, m₂' m + β' m * G₁ m ω.1 + G₂ m ω.2) : ℝ × ℝ)) r
        (fun j => -A - B * j) (fun _ => a)
        (fun j => if j = 1 then -M₁ else -A' - B' * j) (fun j => if j = 1 then M₁ else -ρ)
      ⊆ barrierEventPair N' r
        (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ + ρ)
        (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ - ρ)
        (fun j => (if j = 1 then -M₁ - ρ else -A' - B' * j - ρ) + ρ)
        (fun j => (if j = 1 then M₁ + ρ else 0) - ρ) := by
    refine barrierEventPair_subset_of_add_fst (c := windowMeanH X μ y k σ h)
      (fun m hm ω => ?_) (fun m _ ω => ?_) (fun j _ _ => ?_) (fun j _ _ => ?_)
      (fun j _ _ => ?_) (fun j _ _ => ?_)
    · rw [hshear m ω, hZG m ω.1, hm₁r m hm]
      simp only
      ring
    · rw [hshear m ω, hZG m ω.1, hWG m ω.2, hβdef']
      simp only
      ring
    · linarith
    · linarith
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  have hmono := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := Q₁.prod Q₂) hsub)
  have hε0 : 0 ≤ 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  rw [mul_div_assoc]
  exact le_trans (mul_le_mul_of_nonneg_left (le_trans hgauss hmono) hε0) hslack

/-- `RMF.le_measure_windowEvent_rademacher_floor` with its block-data hypotheses bundled as
`RMF.HP1WindowHyps`. -/
theorem le_measure_windowEvent_of_hyps_floor (hX : IsRademacherPrimeValues X μ)
    {k r y n₀ m₀ : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y)
    (hn₀ : m₀ + 3 ≤ n₀) (hr : n₀ ≤ r)
    {vmin vmax a A B A' B' M₁ K₂ ρ L t Λ AW BW Klate KR σR2 : ℝ}
    (hρ : 2 * Real.exp (-40) ≤ ρ)
    (henv : max (max A a) (max A' M₁) + ρ + 2 * max (B + 1.52) B' ≤ 58)
    (hvmin : 0 < vmin) (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 2 * vmax < B)
    (hCn : (a + A + 2 * B) ^ 2 ≤ 2 * (((n₀ : ℝ) - 2) * vmin)) (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hσR0 : 0 < σR2) (hKL : Klate ≤ L) (hA' : K₂ + KR + AW ≤ A') (hBW' : BW ≤ B')
    (hB'0 : 0 ≤ B')
    (hW : HP1WindowHyps X μ y k r m₀ σ h vmin vmax a A B t Λ BW σR2 Klate KR M₁ K₂) :
    (1 - Real.exp (-100)) * hp1LowerBoundV2 n₀ m₀ vmin vmax
        (windowVarH X μ y k σ h 0) (windowVarH X μ y k σ h 1)
        (windowResid X μ y k σ h 0) (windowResid X μ y k σ h 1)
        (windowSlope X μ y k σ h 0) (windowSlope X μ y k σ h 1)
        (windowMeanR X μ y k σ h 0) (windowMeanR X μ y k σ h 1)
        a A B M₁ K₂ ρ L t Λ AW Klate σR2 / √(r : ℝ)
      ≤ (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
          (barrierEventPair (fun m ω => (halfBlock X k σ h m ω, halfBlock X k σ 0 m ω)) r
            (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i - A - B * j - ρ)
            (fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h i + a + ρ)
            (fun j => if j = 1 then -M₁ - ρ else -A' - B' * j - ρ)
            (fun j => if j = 1 then M₁ + ρ else 0))).toReal := by
  obtain ⟨hvb, hΛ, hBW, hσR, hKlate, hKR, hM₁, hK₂⟩ := hW
  exact le_measure_windowEvent_rademacher_floor hX hk hh hσ hσr hy hn₀ hr hρ henv hvmin hvb ha
    hA hB hCn ht hAW hΛ hBW hσR hσR0 hKlate hKL hKR hM₁ hK₂ hA' hBW' hB'0

end RademacherFloor

end RMF
