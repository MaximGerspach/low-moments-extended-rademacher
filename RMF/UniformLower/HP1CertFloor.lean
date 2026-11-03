/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1CertFloor.Bound0
import RMF.UniformLower.HP1CertFloor.Bound1
import RMF.UniformLower.HP1CertFloor.Bound2
import RMF.UniformLower.HP1CertFloor.Bound3
import RMF.UniformLower.HP1CertFloor.Bound4
import RMF.UniformLower.HP1CertFloor.Bound5
import RMF.UniformLower.HP1CertFloor.Bound6
import RMF.UniformLower.HP1CertFloor.Bound7
import RMF.UniformLower.HP1CertFloor.Side
import RMF.UniformLower.HP1GridFloor
import RMF.UniformLower.HP1Floor
import RMF.UniformLower.HP1Cert

/-!
# HP1 certified at the floor `20`

HP1's certificate from window scales `k ≥ 20`, on the Rademacher side at the floor
(`RMF.le_measure_windowEvent_of_hyps_floor`) and cell data at the numerals
`RMF.hp1CellTableFloor` (`RMF.hp1CellData_of_lt_floor`), with the rows of
`RMF/UniformLower/HP1Cert/` re-used through the constants `RMF.hp1CellP1Floor`
(`RMF.hp1CellBound_of_lt_floor`).  The files:

* `RMF/UniformLower/HP1GridFloor/`, `RMF/UniformLower/HP1GridFloor.lean`: the numerals and the
  cells' data (emitted);
* `RMF/UniformLower/HP1CertFloor/Basic.lean`: the step in `Λ`, for the cells where the floor's
  `Λ` is larger;
* `RMF/UniformLower/HP1CertFloor/Table.lean`, `Side.lean`, `Bound*.lean`: the constants
  `p₁'(i)`, `P₁'`, the side conditions and the bounds per cell (emitted).

The results, for the event `RMF.hp1Event` and the window weight:

* `RMF.le_tiltedMeasure_hp1Event_floor`: on cell `i`, `ℙ'_h(event) ≥ (1 - e^{-100})p₁'(i)/√r`;
* `RMF.le_integral_indicator_hp1Event_floor`: the same times `E‖F_y(s_h)‖²` bounds
  `E[1_{event}‖F_y(s_h)‖²]`;
* `RMF.le_integral_window_of_superset_floor`: for a measurable family of events `S h` containing
  the event, `∫_{halfWindow k} E[1_{S h}‖F_y(s_h)‖²] dh ≥
  (1 - e^{-100})/√r·E‖F_y(s_σ)‖²·e^{-k}·P₁'`, and for the superset `H(k,h) ∩ E″_>(k)` the same
  with `P₁' ≥ 0.31689` (`RMF.le_integral_hp1Tube_inter_hp1After_window_numeral_floor`).
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **HP1's v2 bound on every cell at the floor**: `p₁'(i) ≤ RMF.hp1LowerBoundV2` on the start
ranges of cell `i < 80`, at its numerals `RMF.hp1CellTableFloor i` (the shards'
`RMF.hp1CellBoundFloor_part_s`). -/
theorem hp1CellBound_of_lt_floor {i : ℕ} (hi : i < 80) {v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ}
    (hs : HP1CellStart (hp1CellTableFloor i) v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁) :
    hp1CellP1Floor i ≤ hp1CellLowerBound (hp1CellTableFloor i) v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ := by
  rcases (show i ≤ 9 ∨ (10 ≤ i ∧ i ≤ 19) ∨ (20 ≤ i ∧ i ≤ 29) ∨ (30 ≤ i ∧ i ≤ 39)
      ∨ (40 ≤ i ∧ i ≤ 49) ∨ (50 ≤ i ∧ i ≤ 59) ∨ (60 ≤ i ∧ i ≤ 69) ∨ (70 ≤ i ∧ i ≤ 79) by omega)
    with h0 | ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩ | ⟨h4, h4'⟩ | ⟨h5, h5'⟩ | ⟨h6, h6'⟩ | ⟨h7, h7'⟩
  · exact hp1CellBoundFloor_part_0 (Nat.zero_le i) h0 hs
  · exact hp1CellBoundFloor_part_1 h1 h1' hs
  · exact hp1CellBoundFloor_part_2 h2 h2' hs
  · exact hp1CellBoundFloor_part_3 h3 h3' hs
  · exact hp1CellBoundFloor_part_4 h4 h4' hs
  · exact hp1CellBoundFloor_part_5 h5 h5' hs
  · exact hp1CellBoundFloor_part_6 h6 h6' hs
  · exact hp1CellBoundFloor_part_7 h7 h7' hs

/-- **HP1 at every height at the floor**: for `h` in cell `i < 80` of the window at `k ≥ 20`, with
`r ≥ 2000` blocks, `σe^{k+r} ≤ 1/200`, below the tilt's cutoff `y`, under the tilt by
`|F_y(½+σ+ih)|²` the event `RMF.hp1Event` has probability at least `(1 - e^{-100})p₁'(i)/√r`. -/
theorem le_tiltedMeasure_hp1Event_floor (hX : IsRademacherPrimeValues X μ) {k r y i : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hi : i < 80) (hh : h ∈ hp1Cell k i) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 2000 ≤ r) :
    (1 - Real.exp (-100)) * hp1CellP1Floor i / √(r : ℝ)
      ≤ (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
          (hp1Event X μ y k r σ h)).toReal := by
  have hd := hp1CellData_of_lt_floor hX hi hk hh hσ hσr hy (by omega)
  have hb := hp1CellBound_of_lt_floor hi hd.1
  obtain ⟨hvmin, hB, hCn, ht, hσR0, hKL, hA', hBW'⟩ := hp1CellSideFloor_of_lt hi
  have hw := le_measure_windowEvent_of_hyps_floor hX (n₀ := 2000) (m₀ := 8) (A' := 40) (B' := 2)
    (ρ := 1 / 10 ^ 15) (L := (hp1CellTableFloor i).L) (AW := 6) hk
    (hp1Cell_subset_halfWindow hi hh) hσ hσr hy (by norm_num) hr two_mul_exp_neg_forty_le
    hp1_floor_env_numeral hvmin (by norm_num) (by norm_num) hB hCn ht (by norm_num) hσR0 hKL hA'
    hBW' (by norm_num) hd.2
  have hε : 0 ≤ 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  have hr0 : 0 < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
  refine le_trans ?_ hw
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hε) hr0.le

/-- **Back through the tilt at the floor**: on cell `i`, `k ≥ 20`,
`E[1_{event}‖F_y(s_h)‖²] ≥ E‖F_y(s_h)‖²·(1 - e^{-100})p₁'(i)/√r`. -/
theorem le_integral_indicator_hp1Event_floor (hX : IsRademacherPrimeValues X μ) {k r y i : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hi : i < 80) (hh : h ∈ hp1Cell k i) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 2000 ≤ r) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
        ^ 2 ∂μ) * ((1 - Real.exp (-100)) * hp1CellP1Floor i / √(r : ℝ))
      ≤ ∫ ω, (hp1Event X μ y k r σ h).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  have hA := measurableSet_hp1Event hX y k r σ h
  have key := mul_le_mul_of_nonneg_right
    (le_tiltedMeasure_hp1Event_floor hX hk hi hh hσ hσr hy hr)
    (integral_nonneg (μ := μ) fun ω => sq_nonneg
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖)
  rw [integral_indicator hA, setIntegral_normSq_eq_tiltedMeasure hX y hs hA]
  exact (le_of_eq (mul_comm _ _)).trans key

/-- The per-height bound at the floor with the height-free weight `E‖F_y(½+σ)‖²`, for any
measurable event containing HP1's. -/
lemma le_integral_indicator_of_superset_floor (hX : IsRademacherPrimeValues X μ) {k r y i : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hi : i < 80) (hh : h ∈ hp1Cell k i) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 2000 ≤ r) {S : Set Ω}
    (hS : hp1Event X μ y k r σ h ⊆ S) (hSm : MeasurableSet S) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * hp1CellP1Floor i
      ≤ ∫ ω, S.indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  have h1 := le_integral_indicator_hp1Event_floor hX hk hi hh hσ hσr hy hr
  rw [integral_normSq_randomEulerProduct_shiftLine hX y σ h] at h1
  rw [integral_normSq_randomEulerProduct_shiftLine hX y σ 0]
  have hint := hX.isRademacherRMF.integrable_norm_randomEulerProduct_sq y (shiftLine σ h)
  have h2 : ∫ ω, (hp1Event X μ y k r σ h).indicator (fun ω =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
          ^ 2) ω ∂μ
      ≤ ∫ ω, S.indicator (fun ω =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
          ^ 2) ω ∂μ :=
    integral_mono (hint.indicator (measurableSet_hp1Event hX y k r σ h)) (hint.indicator hSm)
      fun ω => Set.indicator_le_indicator_of_subset hS (fun _ => by positivity) ω
  calc (1 - Real.exp (-100)) / √(r : ℝ) * (∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-1 - 2 * σ)))
        * hp1CellP1Floor i
      = (∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-1 - 2 * σ)))
        * ((1 - Real.exp (-100)) * hp1CellP1Floor i / √(r : ℝ)) := by ring
    _ ≤ _ := h1
    _ ≤ _ := h2

/-- **HP1's window integral at the floor for any measurable family of events containing HP1's**:
for `k ≥ 20`, `∫_{halfWindow k} E[1_{S h}‖F_y(s_h)‖²] dh` is at least
`(1 - e^{-100})/√r·E‖F_y(s_σ)‖²·e^{-k}·P₁'`, where
`P₁' = RMF.hp1WindowP1Floor = ∑_{i<80} p₁'(i)(e^{-i/80} - e^{-(i+1)/80})`. -/
theorem le_integral_window_of_superset_floor (hX : IsRademacherPrimeValues X μ) {k r y : ℕ}
    {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 2000 ≤ r) {S : ℝ → Set Ω}
    (hS : ∀ h ∈ halfWindow k, hp1Event X μ y k r σ h ⊆ S h)
    (hSm : MeasurableSet {q : Ω × ℝ | q.1 ∈ S q.2}) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * hp1WindowP1Floor
      ≤ ∫ h in halfWindow k, ∫ ω, (S h).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  have hmain := le_setIntegral_halfWindow_of_cells
    (integrableOn_integral_indicator_normSq hX y k hσ S hSm) (p := hp1CellP1Floor)
    (c := (1 - Real.exp (-100)) / √(r : ℝ)
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ)
    fun i hi h hh => le_integral_indicator_of_superset_floor hX hk hi hh hσ hσr hy hr
      (hS h (hp1Cell_subset_halfWindow hi hh)) (measurable_prodMk_right (y := h) hSm)
  rw [hp1WindowP1Floor]
  exact hmain

/-- **HP1's window integral at the floor for `H(k,h) ∩ E″_>(k)`**: the same bound for the
superset `RMF.hp1Tube ∩ RMF.hp1After` of the event. -/
theorem le_integral_hp1Tube_inter_hp1After_window_floor (hX : IsRademacherPrimeValues X μ)
    {k r y : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 2000 ≤ r) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * hp1WindowP1Floor
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ :=
  le_integral_window_of_superset_floor hX hk hσ hσr hy hr
    (fun h _ => hp1Event_subset X μ y k r σ h) (measurableSet_prod_hp1Tube_inter_hp1After hX hσ hy)

/-- **HP1's window integral at the floor for `H(k,h) ∩ E″_>(k)` with the explicit numeral**
`P₁' ≥ 0.31689`, for `k ≥ 20`. -/
theorem le_integral_hp1Tube_inter_hp1After_window_numeral_floor
    (hX : IsRademacherPrimeValues X μ) {k r y : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 2000 ≤ r) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * 0.31689
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  refine le_trans ?_ (le_integral_hp1Tube_inter_hp1After_window_floor hX hk hσ hσr hy hr)
  have hε : 0 ≤ 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  have hF : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
      (shiftLine σ 0) ω‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
  exact mul_le_mul_of_nonneg_left hp1WindowP1Floor_ge (by positivity)

end RMF
