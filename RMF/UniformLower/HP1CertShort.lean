/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1CertShort.Bound0
import RMF.UniformLower.HP1CertShort.Bound1
import RMF.UniformLower.HP1CertShort.Bound2
import RMF.UniformLower.HP1CertShort.Bound3
import RMF.UniformLower.HP1CertShort.Bound4
import RMF.UniformLower.HP1CertShort.Bound5
import RMF.UniformLower.HP1CertShort.Bound6
import RMF.UniformLower.HP1CertShort.Bound7
import RMF.UniformLower.HP1CertShort.Bound8
import RMF.UniformLower.HP1CertShort.Bound9
import RMF.UniformLower.HP1CertShort.Bound10
import RMF.UniformLower.HP1CertShort.Bound11
import RMF.UniformLower.HP1CertShort.Bound12
import RMF.UniformLower.HP1CertShort.Bound13
import RMF.UniformLower.HP1CertShort.Bound14
import RMF.UniformLower.HP1CertShort.Bound15
import RMF.UniformLower.HP1CertShort.Side
import RMF.UniformLower.HP1FloorShort

/-!
# HP1 certified on short tubes

HP1's certificate on tubes of `r ≥ 35` blocks at the rungs `n₀ ∈ {35, 50, 72, 115, 160}`, on the
Rademacher side on short tubes (`RMF.le_tiltedMeasure_hp1Event_short`) and the cell data of
`RMF/UniformLower/HP1GridShort.lean`.  The files:

* `RMF/UniformLower/HP1CertShort/Basic.lean`: the rows of `RMF/UniformLower/HP1Cert/` damped by
  the ballot's factor at the rung;
* `RMF/UniformLower/HP1CertShort/Table.lean`, `Side.lean`, `Bound*.lean` (emitted): the constants
  `RMF.hp1CellP1Short n₀ i`, the window sums, the side conditions, the rows as tables and the
  bounds per cell and rung.

The results:

* `RMF.hp1CellBoundShort_of_lt`: `p₁(n₀, i) ≤ RMF.hp1CellLowerBoundShort n₀` on every cell at
  every rung, the hypothesis `hb` of `RMF.le_tiltedMeasure_hp1Event_short`;
* `RMF.le_tiltedMeasure_hp1Event_short_rung`: on cell `i` at a rung `n₀ ≤ r`,
  `ℙ'_h(event) ≥ (1 - e^{-100})p₁(n₀, i)/√r`;
* `RMF.le_integral_window_of_superset_short`: the window integral from `k ≥ 20` at the rung's
  constant `RMF.hp1WindowP1Short n₀ = ∑_{i<80} p₁(n₀, i)(e^{-i/80} - e^{-(i+1)/80})`;
* `RMF.hp1P1ShortRung` (its numerals, `RMF.hp1P1ShortRung_le`) and the step function
  `RMF.hp1P1Short` at the largest rung `≤ r` (`RMF.monotone_hp1P1Short`);
* `RMF.le_integral_hp1Tube_inter_hp1After_window_short`: for `r ≥ 35`,
  `∫_{halfWindow k} E[1_{H(k,h) ∩ E″_>(k)}‖F_y(s_h)‖²] dh ≥
  (1 - e^{-100})/√r·E‖F_y(s_σ)‖²·e^{-k}·RMF.hp1P1Short r`, the floor's numeral form
  (`RMF.le_integral_hp1Tube_inter_hp1After_window_numeral_floor`) on short tubes.
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace RMF

/-! ### Every cell at every rung -/

/-- **HP1's short-tube bound on every cell at every rung** (the shards'
`RMF.hp1CellBoundShort_part_s`): `p₁(n₀, i) ≤ RMF.hp1CellLowerBoundShort n₀` on the start ranges
of cell `i < 80` at its numerals `RMF.hp1CellTableShort i`. -/
theorem hp1CellBoundShort_of_lt {n₀ i : ℕ}
    (hn₀ : n₀ = 35 ∨ n₀ = 50 ∨ n₀ = 72 ∨ n₀ = 115 ∨ n₀ = 160) (hi : i < 80)
    {v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ}
    (hs : HP1CellStart (hp1CellTableShort i) v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁) :
    hp1CellP1Short n₀ i
      ≤ hp1CellLowerBoundShort n₀ (hp1CellTableShort i) v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ := by
  rcases (show i ≤ 4 ∨ (5 ≤ i ∧ i ≤ 9) ∨ (10 ≤ i ∧ i ≤ 14) ∨ (15 ≤ i ∧ i ≤ 19)
      ∨ (20 ≤ i ∧ i ≤ 24) ∨ (25 ≤ i ∧ i ≤ 29) ∨ (30 ≤ i ∧ i ≤ 34) ∨ (35 ≤ i ∧ i ≤ 39)
      ∨ (40 ≤ i ∧ i ≤ 44) ∨ (45 ≤ i ∧ i ≤ 49) ∨ (50 ≤ i ∧ i ≤ 54) ∨ (55 ≤ i ∧ i ≤ 59)
      ∨ (60 ≤ i ∧ i ≤ 64) ∨ (65 ≤ i ∧ i ≤ 69) ∨ (70 ≤ i ∧ i ≤ 74) ∨ (75 ≤ i ∧ i ≤ 79) by omega)
    with h0 | ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩ | ⟨h4, h4'⟩ | ⟨h5, h5'⟩ | ⟨h6, h6'⟩ | ⟨h7, h7'⟩
      | ⟨h8, h8'⟩ | ⟨h9, h9'⟩ | ⟨h10, h10'⟩ | ⟨h11, h11'⟩ | ⟨h12, h12'⟩ | ⟨h13, h13'⟩
      | ⟨h14, h14'⟩ | ⟨h15, h15'⟩
  · exact hp1CellBoundShort_part_0 hn₀ h0 hs
  · exact hp1CellBoundShort_part_1 hn₀ h1 h1' hs
  · exact hp1CellBoundShort_part_2 hn₀ h2 h2' hs
  · exact hp1CellBoundShort_part_3 hn₀ h3 h3' hs
  · exact hp1CellBoundShort_part_4 hn₀ h4 h4' hs
  · exact hp1CellBoundShort_part_5 hn₀ h5 h5' hs
  · exact hp1CellBoundShort_part_6 hn₀ h6 h6' hs
  · exact hp1CellBoundShort_part_7 hn₀ h7 h7' hs
  · exact hp1CellBoundShort_part_8 hn₀ h8 h8' hs
  · exact hp1CellBoundShort_part_9 hn₀ h9 h9' hs
  · exact hp1CellBoundShort_part_10 hn₀ h10 h10' hs
  · exact hp1CellBoundShort_part_11 hn₀ h11 h11' hs
  · exact hp1CellBoundShort_part_12 hn₀ h12 h12' hs
  · exact hp1CellBoundShort_part_13 hn₀ h13 h13' hs
  · exact hp1CellBoundShort_part_14 hn₀ h14 h14' hs
  · exact hp1CellBoundShort_part_15 hn₀ h15 h15' hs

/-! ### The window at a rung -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **HP1 on a cell of a short tube at a rung**: for `h` in cell `i < 80` of the window at
`k ≥ 20`, with `r` blocks, `σe^{k+r} ≤ 1/200`, below the tilt's cutoff `y`, and a rung `n₀ ≤ r`,
under the tilt by `|F_y(½+σ+ih)|²` the event `RMF.hp1Event` has probability at least
`(1 - e^{-100})p₁(n₀, i)/√r` (`RMF.le_tiltedMeasure_hp1Event_short`, its side conditions and
cell bound discharged by `RMF.hp1CellSideShort_of_lt` and `RMF.hp1CellBoundShort_of_lt`). -/
theorem le_tiltedMeasure_hp1Event_short_rung (hX : IsRademacherPrimeValues X μ) {k r y i n₀ : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hi : i < 80) (hh : h ∈ hp1Cell k i) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y)
    (hn₀ : n₀ = 35 ∨ n₀ = 50 ∨ n₀ = 72 ∨ n₀ = 115 ∨ n₀ = 160) (hn₀r : n₀ ≤ r) :
    (1 - Real.exp (-100)) * hp1CellP1Short n₀ i / √(r : ℝ)
      ≤ (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
          (hp1Event X μ y k r σ h)).toReal := by
  have h35 : 35 ≤ n₀ := by rcases hn₀ with e | e | e | e | e <;> omega
  exact le_tiltedMeasure_hp1Event_short hX hk hi hh hσ hσr hy (by omega) (by omega) hn₀r
    (hp1CellSideShort_of_lt hi) (fun _ _ _ _ _ _ _ _ hs => hp1CellBoundShort_of_lt hn₀ hi hs)

/-- **Back through the tilt on short tubes**, for any measurable event containing HP1's, with the
height-free weight `E‖F_y(½+σ)‖²`: on cell `i` at a rung `n₀ ≤ r`, `k ≥ 20`,
`(1 - e^{-100})/√r·E‖F_y(s_σ)‖²·p₁(n₀, i) ≤ E[1_S‖F_y(s_h)‖²]`. -/
lemma le_integral_indicator_of_superset_short (hX : IsRademacherPrimeValues X μ)
    {k r y i n₀ : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hi : i < 80) (hh : h ∈ hp1Cell k i) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y)
    (hn₀ : n₀ = 35 ∨ n₀ = 50 ∨ n₀ = 72 ∨ n₀ = 115 ∨ n₀ = 160) (hn₀r : n₀ ≤ r) {S : Set Ω}
    (hS : hp1Event X μ y k r σ h ⊆ S) (hSm : MeasurableSet S) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * hp1CellP1Short n₀ i
      ≤ ∫ ω, S.indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  have hA := measurableSet_hp1Event hX y k r σ h
  -- the event's own integral, through the tilt (as `RMF.le_integral_indicator_hp1Event_floor`)
  have h1 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
        (shiftLine σ h) ω‖ ^ 2 ∂μ) * ((1 - Real.exp (-100)) * hp1CellP1Short n₀ i / √(r : ℝ))
      ≤ ∫ ω, (hp1Event X μ y k r σ h).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
    have key := mul_le_mul_of_nonneg_right
      (le_tiltedMeasure_hp1Event_short_rung hX hk hi hh hσ hσr hy hn₀ hn₀r)
      (integral_nonneg (μ := μ) fun ω => sq_nonneg
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖)
    rw [integral_indicator hA, setIntegral_normSq_eq_tiltedMeasure hX y hs hA]
    exact (le_of_eq (mul_comm _ _)).trans key
  -- the height-free weight, and the superset
  rw [integral_normSq_randomEulerProduct_shiftLine hX y σ h] at h1
  rw [integral_normSq_randomEulerProduct_shiftLine hX y σ 0]
  have hint := hX.isRademacherRMF.integrable_norm_randomEulerProduct_sq y (shiftLine σ h)
  have h2 : ∫ ω, (hp1Event X μ y k r σ h).indicator (fun ω =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
          ^ 2) ω ∂μ
      ≤ ∫ ω, S.indicator (fun ω =>
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
          ^ 2) ω ∂μ :=
    integral_mono (hint.indicator hA) (hint.indicator hSm)
      fun ω => Set.indicator_le_indicator_of_subset hS (fun _ => by positivity) ω
  calc (1 - Real.exp (-100)) / √(r : ℝ) * (∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-1 - 2 * σ)))
        * hp1CellP1Short n₀ i
      = (∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-1 - 2 * σ)))
        * ((1 - Real.exp (-100)) * hp1CellP1Short n₀ i / √(r : ℝ)) := by ring
    _ ≤ _ := h1
    _ ≤ _ := h2

/-- **HP1's window constant on short tubes at rung `n₀`**:
`P₁(n₀) = ∑_{i<80} p₁(n₀, i)(e^{-i/80} - e^{-(i+1)/80})`. -/
noncomputable def hp1WindowP1Short (n₀ : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 80, hp1CellP1Short n₀ i * hp1WindowWeight i

/-- **HP1's window integral on short tubes at a rung, for any measurable family of events
containing HP1's**: for `k ≥ 20` and a rung `n₀ ≤ r`, `∫_{halfWindow k} E[1_{S h}‖F_y(s_h)‖²] dh`
is at least `(1 - e^{-100})/√r·E‖F_y(s_σ)‖²·e^{-k}·RMF.hp1WindowP1Short n₀`. -/
theorem le_integral_window_of_superset_short (hX : IsRademacherPrimeValues X μ) {k r y n₀ : ℕ}
    {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y)
    (hn₀ : n₀ = 35 ∨ n₀ = 50 ∨ n₀ = 72 ∨ n₀ = 115 ∨ n₀ = 160) (hn₀r : n₀ ≤ r) {S : ℝ → Set Ω}
    (hS : ∀ h ∈ halfWindow k, hp1Event X μ y k r σ h ⊆ S h)
    (hSm : MeasurableSet {q : Ω × ℝ | q.1 ∈ S q.2}) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * hp1WindowP1Short n₀
      ≤ ∫ h in halfWindow k, ∫ ω, (S h).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  have hmain := le_setIntegral_halfWindow_of_cells
    (integrableOn_integral_indicator_normSq hX y k hσ S hSm) (p := hp1CellP1Short n₀)
    (c := (1 - Real.exp (-100)) / √(r : ℝ)
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ)
    fun i hi h hh => le_integral_indicator_of_superset_short hX hk hi hh hσ hσr hy hn₀ hn₀r
      (hS h (hp1Cell_subset_halfWindow hi hh)) (measurable_prodMk_right (y := h) hSm)
  rw [hp1WindowP1Short]
  exact hmain

/-- **HP1's window integral on short tubes at a rung for `H(k,h) ∩ E″_>(k)`**: the superset
`RMF.hp1Tube ∩ RMF.hp1After` of the event, at the rung's constant `RMF.hp1WindowP1Short n₀`. -/
theorem le_integral_hp1Tube_inter_hp1After_window_short_rung (hX : IsRademacherPrimeValues X μ)
    {k r y n₀ : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y)
    (hn₀ : n₀ = 35 ∨ n₀ = 50 ∨ n₀ = 72 ∨ n₀ = 115 ∨ n₀ = 160) (hn₀r : n₀ ≤ r) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * hp1WindowP1Short n₀
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ :=
  le_integral_window_of_superset_short hX hk hσ hσr hy hn₀ hn₀r
    (fun h _ => hp1Event_subset X μ y k r σ h) (measurableSet_prod_hp1Tube_inter_hp1After hX hσ hy)

/-! ### The certified constant per rung, and the step function -/

/-- The entries of a list of nonnegative reals are nonnegative, the default `0` included. -/
lemma getD_nonneg_of_forall_mem {l : List ℝ} (h : ∀ x ∈ l, 0 ≤ x) (i : ℕ) : 0 ≤ l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simpa using h a (by simp)
    | succ i => simpa using ih (fun x hx => h x (by simp [hx])) i

/-- **The window constant from below**: from `p₁(n₀, ·) ≥ 0` and a numeral lower sum at the
weights' lower bounds `RMF.hp1WindowWeightLo` (`RMF.hp1WindowWeightLo_le`). -/
lemma le_hp1WindowP1Short {n₀ : ℕ} {P : ℝ} (hp : ∀ x ∈ hp1CellP1ShortList n₀, 0 ≤ x)
    (hP : P ≤ ∑ i ∈ Finset.range 80, hp1CellP1Short n₀ i * hp1WindowWeightLo.getD i 0) :
    P ≤ hp1WindowP1Short n₀ :=
  le_trans hP (Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (hp1WindowWeightLo_le (Finset.mem_range.1 hi)) (getD_nonneg_of_forall_mem hp i))

/-- **HP1's certified constant on short tubes at the rungs**: numeral lower bounds of the window
constants `RMF.hp1WindowP1Short n₀` at `n₀ ∈ {35, 50, 72, 115, 160}` (`RMF.hp1P1ShortRung_le`),
`0` at every other `n₀`. -/
def hp1P1ShortRung : ℕ → ℝ
  | 35 => 0.28668
  | 50 => 0.30092
  | 72 => 0.31128
  | 115 => 0.32023
  | 160 => 0.32449
  | _ => 0

/-- The numerals `RMF.hp1P1ShortRung n₀` bound the window constants from below
(`RMF.hp1WindowSumShort_ge_n₀`). -/
theorem hp1P1ShortRung_le {n₀ : ℕ} (hn₀ : n₀ = 35 ∨ n₀ = 50 ∨ n₀ = 72 ∨ n₀ = 115 ∨ n₀ = 160) :
    hp1P1ShortRung n₀ ≤ hp1WindowP1Short n₀ := by
  rcases hn₀ with rfl | rfl | rfl | rfl | rfl
  · exact le_hp1WindowP1Short hp1CellP1ShortList_nonneg_35 hp1WindowSumShort_ge_35
  · exact le_hp1WindowP1Short hp1CellP1ShortList_nonneg_50 hp1WindowSumShort_ge_50
  · exact le_hp1WindowP1Short hp1CellP1ShortList_nonneg_72 hp1WindowSumShort_ge_72
  · exact le_hp1WindowP1Short hp1CellP1ShortList_nonneg_115 hp1WindowSumShort_ge_115
  · exact le_hp1WindowP1Short hp1CellP1ShortList_nonneg_160 hp1WindowSumShort_ge_160

/-- The largest rung of HP1's ladder on short tubes at most `r` (`35` below `50`). -/
def hp1RungShort (r : ℕ) : ℕ :=
  if 160 ≤ r then 160 else if 115 ≤ r then 115 else if 72 ≤ r then 72
  else if 50 ≤ r then 50 else 35

/-- On tubes of `r ≥ 35` blocks, `RMF.hp1RungShort r` is a rung, and at most `r`. -/
lemma hp1RungShort_spec {r : ℕ} (hr : 35 ≤ r) :
    (hp1RungShort r = 35 ∨ hp1RungShort r = 50 ∨ hp1RungShort r = 72 ∨ hp1RungShort r = 115
      ∨ hp1RungShort r = 160) ∧ hp1RungShort r ≤ r := by
  unfold hp1RungShort
  split_ifs <;> omega

/-- **HP1's certified constant on tubes of `r` blocks**: `RMF.hp1P1ShortRung` at the largest rung
`≤ r` (`RMF.hp1RungShort`), `0` below `35`. -/
def hp1P1Short (r : ℕ) : ℝ :=
  if 35 ≤ r then hp1P1ShortRung (hp1RungShort r) else 0

/-- `RMF.hp1P1Short` is a nondecreasing step function of the tube's length. -/
theorem monotone_hp1P1Short : Monotone hp1P1Short := by
  intro a b hab
  simp only [hp1P1Short, hp1RungShort]
  split_ifs <;> first | omega | norm_num [hp1P1ShortRung]

/-! ### The window on short tubes -/

/-- **HP1's window integral on short tubes for `H(k,h) ∩ E″_>(k)`**: for `k ≥ 20` and tubes of
`r ≥ 35` blocks with `σe^{k+r} ≤ 1/200` below the tilt's cutoff `y`,
`∫_{halfWindow k} E[1_{H(k,h) ∩ E″_>(k)}‖F_y(s_h)‖²] dh ≥
(1 - e^{-100})/√r·E‖F_y(s_σ)‖²·e^{-k}·RMF.hp1P1Short r`: the rung `RMF.hp1RungShort r ≤ r`
(`RMF.le_integral_hp1Tube_inter_hp1After_window_short_rung`) and its numeral
(`RMF.hp1P1ShortRung_le`). -/
theorem le_integral_hp1Tube_inter_hp1After_window_short (hX : IsRademacherPrimeValues X μ)
    {k r y : ℕ} {σ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hr : 35 ≤ r) :
    (1 - Real.exp (-100)) / √(r : ℝ)
        * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (-(k : ℝ)) * hp1P1Short r
      ≤ ∫ h in halfWindow k, ∫ ω, (hp1Tube X μ y k r σ h ∩ hp1After X σ k r).indicator (fun ω =>
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) ω‖
            ^ 2) ω ∂μ := by
  obtain ⟨hn₀, hn₀r⟩ := hp1RungShort_spec hr
  refine le_trans ?_ (le_integral_hp1Tube_inter_hp1After_window_short_rung hX hk hσ hσr hy hn₀
    hn₀r)
  have hε : 0 ≤ 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  have hF : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
      (shiftLine σ 0) ω‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
  rw [hp1P1Short, if_pos hr]
  exact mul_le_mul_of_nonneg_left (hp1P1ShortRung_le hn₀) (by positivity)

end RMF
