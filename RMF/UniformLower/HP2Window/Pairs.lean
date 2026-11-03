/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2Window.Cells

/-!
# HP2's window integral: the band volumes

In `t = |h₁ - h₂|e^k`, the pairs of `halfWindow k` with `t ≤ T` have Lebesgue measure
`e^{-2k}·RMF.hp2PairVol T`, `hp2PairVol T = L² - ((L - T)⁺)²`, `L = 1 - e^{-1}`
(`RMF.integral_hp2WinInner`; the inner measure is `min(b, h₁ + τ) - max(a, h₁ - τ)`,
`RMF.integral_min_sub_max`), so the cell `i` has the band `RMF.hp2Band i`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The band volumes -/

/-- `∫_c^τ max(0, u) du = (τ² - (max(c, 0))²)/2` for `c ≤ τ`, `0 ≤ τ`. -/
lemma integral_max_zero {c τ : ℝ} (hcτ : c ≤ τ) (hτ : 0 ≤ τ) :
    ∫ u in c..τ, max 0 u = (τ ^ 2 - (max c 0) ^ 2) / 2 := by
  have hcont : Continuous fun u : ℝ => max 0 u := continuous_const.max continuous_id
  rcases le_or_gt c 0 with hc | hc
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have h1 : ∫ u in c..0, max 0 u = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
        rw [Set.uIcc_of_le hc] at hu
        exact max_eq_left hu.2]
      simp
    have h2 : ∫ u in (0 : ℝ)..τ, max 0 u = τ ^ 2 / 2 := by
      rw [intervalIntegral.integral_congr (g := fun u => u) fun u hu => by
        rw [Set.uIcc_of_le hτ] at hu
        exact max_eq_right hu.1, integral_id]
      ring
    rw [h1, h2, max_eq_right hc]
    ring
  · rw [intervalIntegral.integral_congr (g := fun u => u) fun u hu => by
      rw [Set.uIcc_of_le hcτ] at hu
      exact max_eq_right (hc.le.trans hu.1), integral_id, max_eq_left hc.le]

/-- `min(b, h + τ) - max(a, h - τ) = 2τ - (h + τ - b)⁺ - (a + τ - h)⁺`. -/
lemma min_sub_max_eq (a b h τ : ℝ) :
    min b (h + τ) - max a (h - τ) = 2 * τ - max 0 (h + (τ - b)) - max 0 ((a + τ) - h) := by
  have e1 : min b (h + τ) = h + τ - max 0 (h + (τ - b)) := by
    rcases le_total (h + τ) b with h1 | h1
    · rw [min_eq_right h1, max_eq_left (by linarith)]; ring
    · rw [min_eq_left h1, max_eq_right (by linarith)]; ring
  have e2 : max a (h - τ) = h - τ + max 0 ((a + τ) - h) := by
    rcases le_total a (h - τ) with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
  rw [e1, e2]
  ring

/-- **The inner measure integrated**: for `a ≤ b`, `τ ≥ 0`,
`∫_a^b (min(b, h + τ) - max(a, h - τ)) dh = (b - a)² - ((b - a - τ)⁺)²`. -/
lemma integral_min_sub_max {a b τ : ℝ} (hab : a ≤ b) (hτ : 0 ≤ τ) :
    ∫ h in a..b, (min b (h + τ) - max a (h - τ)) = (b - a) ^ 2 - (max (b - a - τ) 0) ^ 2 := by
  have hc₁ : Continuous fun h : ℝ => max 0 (h + (τ - b)) :=
    continuous_const.max (continuous_id.add continuous_const)
  have hc₂ : Continuous fun h : ℝ => max 0 ((a + τ) - h) :=
    continuous_const.max (continuous_const.sub continuous_id)
  simp_rw [min_sub_max_eq a b _ τ]
  have s₁ := intervalIntegral.integral_sub (μ := volume) (a := a) (b := b)
    (f := fun h : ℝ => 2 * τ - max 0 (h + (τ - b))) (g := fun h : ℝ => max 0 ((a + τ) - h))
    ((continuous_const.sub hc₁).intervalIntegrable _ _) (hc₂.intervalIntegrable _ _)
  have s₂ := intervalIntegral.integral_sub (μ := volume) (a := a) (b := b)
    (f := fun _ : ℝ => 2 * τ) (g := fun h : ℝ => max 0 (h + (τ - b)))
    (continuous_const.intervalIntegrable _ _) (hc₁.intervalIntegrable _ _)
  rw [s₁, s₂, intervalIntegral.integral_const]
  have i₁ : ∫ h in a..b, max 0 (h + (τ - b)) = (τ ^ 2 - (max (τ - (b - a)) 0) ^ 2) / 2 := by
    rw [intervalIntegral.integral_comp_add_right (fun u => max 0 u),
      show a + (τ - b) = τ - (b - a) by ring, show b + (τ - b) = τ by ring]
    exact integral_max_zero (by linarith) hτ
  have i₂ : ∫ h in a..b, max 0 ((a + τ) - h) = (τ ^ 2 - (max (τ - (b - a)) 0) ^ 2) / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => max 0 u),
      show a + τ - b = τ - (b - a) by ring, show a + τ - a = τ by ring]
    exact integral_max_zero (by linarith) hτ
  rw [i₁, i₂, smul_eq_mul]
  rcases le_total τ (b - a) with h | h
  · rw [max_eq_right (by linarith : τ - (b - a) ≤ 0), max_eq_left (by linarith : 0 ≤ b - a - τ)]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ τ - (b - a)), max_eq_right (by linarith : b - a - τ ≤ 0)]
    ring

/-- `1_{[0,T]}(|h₁ - h₂|s) = 1_{[h₁ - T/s, h₁ + T/s]}(h₂)` for `s > 0`. -/
lemma indicator_Icc_abs_mul {s T c h₁ h₂ : ℝ} (hs : 0 < s) :
    (Set.Icc 0 T).indicator (fun _ => c) (|h₁ - h₂| * s)
      = (Set.Icc (h₁ - T / s) (h₁ + T / s)).indicator (fun _ => c) h₂ := by
  have hiff : |h₁ - h₂| * s ∈ Set.Icc 0 T ↔ h₂ ∈ Set.Icc (h₁ - T / s) (h₁ + T / s) := by
    simp only [Set.mem_Icc]
    rw [← le_div_iff₀ hs]
    have h0 : 0 ≤ |h₁ - h₂| * s := by positivity
    constructor
    · rintro ⟨-, h⟩
      have := abs_le.1 h
      constructor <;> linarith [this.1, this.2]
    · rintro ⟨h1, h2⟩
      exact ⟨h0, abs_le.2 ⟨by linarith, by linarith⟩⟩
  by_cases hm : h₂ ∈ Set.Icc (h₁ - T / s) (h₁ + T / s)
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.1 h))]

/-- **The inner integral of a band**: for `h₁ ∈ [a, b]`, `s > 0`, `T ≥ 0`,
`∫_{[a,b]} c·1{|h₁ - h₂|s ≤ T} dh₂ = c(min(b, h₁ + T/s) - max(a, h₁ - T/s))`. -/
lemma integral_indicator_Icc_abs_mul {a b s T c h₁ : ℝ} (hh₁ : h₁ ∈ Set.Icc a b) (hs : 0 < s)
    (hT : 0 ≤ T) :
    ∫ h₂ in Set.Icc a b, (Set.Icc 0 T).indicator (fun _ => c) (|h₁ - h₂| * s)
      = c * (min b (h₁ + T / s) - max a (h₁ - T / s)) := by
  simp_rw [indicator_Icc_abs_mul (T := T) (c := c) (h₁ := h₁) hs]
  rw [integral_indicator_const _ measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
    Set.Icc_inter_Icc, Real.volume_real_Icc_of_le, smul_eq_mul, mul_comm]
  · congr 1
    rw [sup_comm, inf_comm]
  · have hτ : 0 ≤ T / s := div_nonneg hT hs.le
    obtain ⟨h1, h2⟩ := hh₁
    exact le_inf (sup_le (by linarith) (by linarith)) (sup_le (by linarith) (by linarith))

/-- `c·1_{(α, β]}(t) = c(1_{[0,β]}(t) - 1_{[0,α]}(t))` for `α ≤ β` and `t ≥ 0`. -/
lemma indicator_Ioc_eq_sub {α β t c : ℝ} (hαβ : α ≤ β) (ht : 0 ≤ t) :
    (Set.Ioc α β).indicator (fun _ => c) t
      = c * ((Set.Icc 0 β).indicator (fun _ => (1 : ℝ)) t
        - (Set.Icc 0 α).indicator (fun _ => (1 : ℝ)) t) := by
  rcases le_or_gt t α with h1 | h1
  · have a₁ : t ∉ Set.Ioc α β := fun h => absurd h.1 (not_lt.2 h1)
    have a₂ : t ∈ Set.Icc 0 β := ⟨ht, h1.trans hαβ⟩
    have a₃ : t ∈ Set.Icc 0 α := ⟨ht, h1⟩
    rw [Set.indicator_of_notMem a₁, Set.indicator_of_mem a₂, Set.indicator_of_mem a₃]
    ring
  · have a₃ : t ∉ Set.Icc 0 α := fun h => absurd h.2 (not_le.2 h1)
    rw [Set.indicator_of_notMem a₃]
    rcases le_or_gt t β with h2 | h2
    · have a₁ : t ∈ Set.Ioc α β := ⟨h1, h2⟩
      have a₂ : t ∈ Set.Icc 0 β := ⟨ht, h2⟩
      rw [Set.indicator_of_mem a₁, Set.indicator_of_mem a₂]
      ring
    · have a₁ : t ∉ Set.Ioc α β := fun h => absurd h.2 (not_le.2 h2)
      have a₂ : t ∉ Set.Icc 0 β := fun h => absurd h.2 (not_le.2 h2)
      rw [Set.indicator_of_notMem a₁, Set.indicator_of_notMem a₂]
      ring

/-- `1_S` with value `c` is `c` times `1_S`. -/
lemma indicator_const_eq_mul (S : Set ℝ) (c t : ℝ) :
    S.indicator (fun _ => c) t = c * S.indicator (fun _ => (1 : ℝ)) t := by
  by_cases h : t ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- **The pair volume** `hp2PairVol T = L² - ((L - T)⁺)²`, `L = 1 - e^{-1}`: the Lebesgue measure of
the pairs of `[e^{-1}, 1]²` with `|y₁ - y₂| ≤ T`, `T ≥ 0`. -/
noncomputable def hp2PairVol (T : ℝ) : ℝ :=
  (1 - Real.exp (-1)) ^ 2 - (max (1 - Real.exp (-1) - T) 0) ^ 2

/-- **The band of cell `i`**: `hp2PairVol(e^{-i/40}) - hp2PairVol(e^{-(i+1)/40})`. -/
noncomputable def hp2Band (i : ℕ) : ℝ := hp2PairVol (hp2CellEnd i) - hp2PairVol (hp2CellEnd (i + 1))

/-- The window's inner measure `ℓ(h₁, τ) = min(e^{-k}, h₁ + τ) - max(e^{-(k+1)}, h₁ - τ)`. -/
noncomputable def hp2WinInner (k : ℕ) (h₁ τ : ℝ) : ℝ :=
  min (Real.exp (-(k : ℝ))) (h₁ + τ) - max (Real.exp (-((k : ℝ) + 1))) (h₁ - τ)

lemma continuous_hp2WinInner (k : ℕ) (τ : ℝ) : Continuous fun h₁ => hp2WinInner k h₁ τ := by
  unfold hp2WinInner
  exact (continuous_const.min (continuous_id.add continuous_const)).sub
    (continuous_const.max (continuous_id.sub continuous_const))

/-- **A band's volume on the window**: `∫_W ℓ(h₁, Te^{-k}) dh₁ = e^{-2k}·hp2PairVol T`, `T ≥ 0`. -/
lemma integral_hp2WinInner (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ h₁ in halfWindow k, hp2WinInner k h₁ (T / Real.exp (k : ℝ))
      = Real.exp (-2 * (k : ℝ)) * hp2PairVol T := by
  have hab : Real.exp (-((k : ℝ) + 1)) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have hs := Real.exp_pos (k : ℝ)
  rw [halfWindow, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  unfold hp2WinInner
  rw [integral_min_sub_max hab (div_nonneg hT hs.le)]
  have hL : Real.exp (-(k : ℝ)) - Real.exp (-((k : ℝ) + 1))
      = Real.exp (-(k : ℝ)) * (1 - Real.exp (-1)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  have hτ : T / Real.exp (k : ℝ) = Real.exp (-(k : ℝ)) * T := by
    rw [Real.exp_neg, div_eq_inv_mul]
  have hsq : Real.exp (-2 * (k : ℝ)) = Real.exp (-(k : ℝ)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have he := Real.exp_pos (-(k : ℝ))
  have hm : max (Real.exp (-(k : ℝ)) * (1 - Real.exp (-1) - T)) 0
      = Real.exp (-(k : ℝ)) * max (1 - Real.exp (-1) - T) 0 := by
    rw [mul_max_of_nonneg _ _ he.le, mul_zero]
  rw [hL, hτ, hsq, show Real.exp (-(k : ℝ)) * (1 - Real.exp (-1)) - Real.exp (-(k : ℝ)) * T
    = Real.exp (-(k : ℝ)) * (1 - Real.exp (-1) - T) by ring, hm]
  unfold hp2PairVol
  ring

/-- `hp2PairVol` is monotone on `[0, ∞)`. -/
lemma hp2PairVol_mono {T T' : ℝ} (h : T ≤ T') : hp2PairVol T ≤ hp2PairVol T' := by
  unfold hp2PairVol
  have hL : 0 ≤ 1 - Real.exp (-1) := by
    have := Real.exp_le_one_iff.2 (show (-1 : ℝ) ≤ 0 by norm_num)
    linarith
  have h1 : max (1 - Real.exp (-1) - T') 0 ≤ max (1 - Real.exp (-1) - T) 0 :=
    max_le_max (by linarith) le_rfl
  have h0 : 0 ≤ max (1 - Real.exp (-1) - T') 0 := le_max_right _ _
  nlinarith

/-- The bands are nonnegative. -/
lemma hp2Band_nonneg (i : ℕ) : 0 ≤ hp2Band i := by
  unfold hp2Band
  exact sub_nonneg.2 (hp2PairVol_mono (hp2CellEnd_anti (Nat.le_succ i)))

end RMF
