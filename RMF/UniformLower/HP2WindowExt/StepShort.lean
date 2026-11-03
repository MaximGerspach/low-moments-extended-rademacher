/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.RestShort
import RMF.UniformLower.HP2WindowExt.Step

/-!
# HP2's window integral: the step function with the rest on short tubes

`RMF/UniformLower/HP2WindowExt/Step.lean` for tubes of `r ≥ 35` blocks, the rest multiplied in by
`RMF.integral_hp1Tube_inter_rest_le_short`, so with `10⁻⁴` in place of `10⁻¹⁹` in every cell's
constant:

* on the cells of the depths `d ≤ r - 3`: `RMF.hp2WinCell r d j` times
  `RMF.hp2ExtFacS r d = e^{4e^{1-(r-d)} + 10⁻⁴}`;
* on the deep cells `j < N` and below them: `RMF.hp2WinDeep r·e^{2B_j + 10⁻⁴}` and
  `RMF.hp2WinDeep r·e^{2B_sat + 10⁻⁴}`, so the deep cells' average `Z` becomes `e^{10⁻⁴}Z`
  (`RMF.hp2ExtDeepAvgS_le`).

The window integral is at most `(E‖F_y(s_σ)‖²)²e^{-2k}·RMF.hp2ExtSumS r N B B_sat`
(`RMF.integral_integral_pair_rest_le_hp2ExtSumS`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The cell constants with the short factor -/

/-- **The rest's factor on the cells of depth `d`, short tubes**: `e^{4e^{1-(r-d)} + 10⁻⁴}`. -/
noncomputable def hp2ExtFacS (r d : ℕ) : ℝ :=
  Real.exp (4 * Real.exp (1 - ((r - d : ℕ) : ℝ)) + 1 / 10 ^ 4)

/-- **The cell constants on short tubes**: `hp2WinCell r d j·hp2ExtFacS r d` on the cell
`i = 40d + j` of the depths `d < r - 2`, `hp2WinDeep r·e^{2B_j + 10⁻⁴}` on the deep cell
`i = 40(r - 2) + j`. -/
noncomputable def hp2ExtCellS (r : ℕ) (B : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < 40 * (r - 2) then hp2WinCell r (i / 40) (i % 40) * hp2ExtFacS r (i / 40)
  else hp2WinDeep r * Real.exp (2 * B (i - 40 * (r - 2)) + 1 / 10 ^ 4)

/-- **The constant below the deep cells on short tubes**: `hp2WinDeep r·e^{2B_sat + 10⁻⁴}`. -/
noncomputable def hp2ExtSatS (r : ℕ) (Bsat : ℝ) : ℝ :=
  hp2WinDeep r * Real.exp (2 * Bsat + 1 / 10 ^ 4)

/-- **The sum over the cells on short tubes**: `∑_{i<40(r-2)+N} hp2ExtCellS r B i·hp2Band i
  + hp2ExtSatS r B_sat·hp2PairVol(a_{40(r-2)+N})`. -/
noncomputable def hp2ExtSumS (r N : ℕ) (B : ℕ → ℝ) (Bsat : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (40 * (r - 2) + N), hp2ExtCellS r B i * hp2Band i
    + hp2ExtSatS r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))

lemma hp2ExtCellS_nonneg (r : ℕ) (B : ℕ → ℝ) (i : ℕ) : 0 ≤ hp2ExtCellS r B i := by
  unfold hp2ExtCellS hp2ExtFacS
  split_ifs
  · exact mul_nonneg (hp2WinCell_nonneg r _ (Nat.mod_lt _ (by norm_num))) (Real.exp_pos _).le
  · exact mul_nonneg (hp2WinDeep_nonneg r) (Real.exp_pos _).le

lemma hp2ExtSatS_nonneg (r : ℕ) (Bsat : ℝ) : 0 ≤ hp2ExtSatS r Bsat :=
  mul_nonneg (hp2WinDeep_nonneg r) (Real.exp_pos _).le

/-- **The deep cells' average with the short factor**: at most `e^{10⁻⁴}Z` for any `Z` bounding
`∑_{j<N} e^{2B_j + 10⁻¹⁹}(a_j - a_{j+1}) + e^{2B_sat + 10⁻¹⁹}a_N` (the `Z` of
`RMF.hp2ExtDeep_le`). -/
lemma hp2ExtDeepAvgS_le {N : ℕ} {B : ℕ → ℝ} {Bsat Z : ℝ}
    (hZ : ∑ j ∈ Finset.range N, Real.exp (2 * B j + 1 / 10 ^ 19)
          * (hp2CellEnd j - hp2CellEnd (j + 1))
        + Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N ≤ Z) :
    ∑ j ∈ Finset.range N, Real.exp (2 * B j + 1 / 10 ^ 4)
          * (hp2CellEnd j - hp2CellEnd (j + 1))
        + Real.exp (2 * Bsat + 1 / 10 ^ 4) * hp2CellEnd N ≤ Real.exp (1 / 10 ^ 4) * Z := by
  set c : ℝ := Real.exp (1 / 10 ^ 4 - 1 / 10 ^ 19) with hc
  have he : ∀ b : ℝ, Real.exp (2 * b + 1 / 10 ^ 4) = c * Real.exp (2 * b + 1 / 10 ^ 19) :=
    fun b => by
      rw [hc, ← Real.exp_add]
      congr 1
      ring
  set S : ℝ := ∑ j ∈ Finset.range N, Real.exp (2 * B j + 1 / 10 ^ 19)
      * (hp2CellEnd j - hp2CellEnd (j + 1))
    + Real.exp (2 * Bsat + 1 / 10 ^ 19) * hp2CellEnd N with hS
  have hSeq : ∑ j ∈ Finset.range N, Real.exp (2 * B j + 1 / 10 ^ 4)
        * (hp2CellEnd j - hp2CellEnd (j + 1))
      + Real.exp (2 * Bsat + 1 / 10 ^ 4) * hp2CellEnd N = c * S := by
    rw [hS, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by rw [he]; ring
    · rw [he]
      ring
  have hS0 : 0 ≤ S :=
    add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le
      (sub_nonneg.2 (hp2CellEnd_anti (Nat.le_succ j)))) (mul_nonneg (Real.exp_pos _).le
      (hp2CellEnd_pos _).le)
  have hZ0 : 0 ≤ Z := hS0.trans hZ
  have hc1 : c ≤ Real.exp (1 / 10 ^ 4) := Real.exp_le_exp.2 (by norm_num)
  rw [hSeq]
  calc c * S ≤ c * Z := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
    _ ≤ Real.exp (1 / 10 ^ 4) * Z := mul_le_mul_of_nonneg_right hc1 hZ0

section Pair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The pair bound with the rest, cell by cell, on short tubes**:
`RMF.integral_pair_rest_le_cellStep` for `r ≥ 35` with the short constants `RMF.hp2ExtCellS`,
`RMF.hp2ExtSatS` (the rest by `RMF.integral_hp1Tube_inter_rest_le_short`): for `k ≥ 20`, heights
in the window, `σe^{k+r} ≤ 1/200 < σe^{k+r+1}`, the tilt cutoff `y ≥ c_r` and bounds `B_j`, `B_sat`
on the rest's damped integral over the deep cells and below them,
`E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²]
  ≤ E‖F_y(s₁)‖²E‖F_y(s₂)‖²·cellStep (40(r-2) + N) … (|h₁ - h₂|e^k)`. -/
theorem integral_pair_rest_le_cellStep_short (hX : IsRademacherPrimeValues X μ) {k r y N : ℕ}
    {σ h₁ h₂ : ℝ} {B : ℕ → ℝ} {Bsat : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 35 ≤ r) (hB : ∀ j < N, IsRestCosBound (hp2DeepEnd (j + 1)) (hp2DeepEnd j) (B j))
    (hsat : IsRestCosBound (-1) (hp2DeepEnd N) Bsat) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * cellStep (40 * (r - 2) + N) (hp2ExtCellS r B) (hp2ExtSatS r Bsat)
          (|h₁ - h₂| * Real.exp (k : ℝ)) := by
  have hσA := rest_damping_mem hσr hσr'
  have hA : 0 < Real.exp ((r : ℝ) + k) := Real.exp_pos _
  have hσ0 : 0 ≤ σ := (sigma_pos_of_damping hA hσA.1).le
  have hr7 : 7 ≤ r := by omega
  set t := |h₁ - h₂| * Real.exp (k : ℝ) with ht
  set U := restU k r y with hU
  set D := |h₁ - h₂| with hD
  have hAU : Real.exp ((r : ℝ) + k) ≤ U := exp_le_restU k r y
  have hD0 : 0 ≤ D := abs_nonneg _
  have htau : D * Real.exp ((r : ℝ) + k) = t * Real.exp (r : ℝ) := by
    rw [ht, add_comm, Real.exp_add]; ring
  have hE0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ) :=
    mul_nonneg (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
  -- the rest multiplies any bound over the blocks `m < r`
  have hrest : ∀ K : ℝ, (∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * K) → 0 ≤ K → ∀ c : ℝ, (∫ u in Real.exp ((r : ℝ) + k)..U,
          Real.cos (D * u) * Real.exp (-(2 * σ) * u) / u) ≤ c →
      ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * (K * Real.exp (2 * c + 1 / 10 ^ 4)) := by
    intro K hK hK0 c hc
    refine (integral_hp1Tube_inter_rest_le_short hX hk hr hσ0 hh₁ hh₂ hyr hK).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (mul_nonneg hE0 hK0)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (abs_sub_mul_exp_le_of_mem_halfWindow hh₁ hh₂).trans
    (by linarith [Real.exp_pos (-1)])
  refine le_mul_cellStep (fun i _ => hp2ExtCellS_nonneg r B i) (hp2ExtSatS_nonneg r Bsat) hE0
    ht0 ht1 (fun i hi hlo hup => ?_) fun hlast => ?_
  · by_cases hdeep : i < 40 * (r - 2)
    · -- a cell of depth `d = i/40 ≤ r - 3`
      set d := i / 40 with hd
      set j := i % 40 with hj
      have hij : 40 * d + j = i := Nat.div_add_mod i 40
      have hdr : d + 3 ≤ r := by omega
      have hj40 : j < 40 := Nat.mod_lt _ (by norm_num)
      have hmem : t ∈ Set.Ioc (hp2CellEnd (40 * d + j + 1)) (hp2CellEnd (40 * d + j)) := by
        rw [hij]; exact ⟨hlo, hup⟩
      have hcell := integral_pair_le_hp2WinCell hX hk hh₁ hh₂ hσ0 hσr hyr hj40
        (isHP2UCell_of_mem hmem) hdr hr7
      -- the rest's integral is at most `2e^{1-(r-d)}`
      have hDpos : 0 < D := by
        have h1 : 0 < t := lt_of_le_of_lt (Real.exp_pos _).le hlo
        rw [ht] at h1
        by_contra hc
        have h0 : D = 0 := le_antisymm (not_lt.1 hc) hD0
        rw [h0, zero_mul] at h1
        exact lt_irrefl 0 h1
      have hint := (abs_le.1 (abs_integral_cos_mul_exp_div_le hDpos hσ0 hA hAU)).2
      have hlow : Real.exp ((r : ℝ) - d - 1) ≤ D * Real.exp ((r : ℝ) + k) := by
        rw [htau]
        have h1 : hp2CellEnd (i + 1) * Real.exp (r : ℝ)
            = Real.exp ((r : ℝ) - ((i : ℝ) + 1) / 40) := by
          unfold hp2CellEnd
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        have h2 : Real.exp ((r : ℝ) - d - 1) ≤ Real.exp ((r : ℝ) - ((i : ℝ) + 1) / 40) := by
          refine Real.exp_le_exp.2 ?_
          have : (i : ℝ) + 1 ≤ 40 * d + 40 := by
            have : i + 1 ≤ 40 * d + 40 := by omega
            exact_mod_cast this
          linarith
        exact h2.trans (h1 ▸ mul_le_mul_of_nonneg_right hlo.le (Real.exp_pos _).le)
      have hbound : 2 / (D * Real.exp ((r : ℝ) + k)) ≤ 2 * Real.exp (1 - ((r - d : ℕ) : ℝ)) := by
        rw [div_le_iff₀ (by positivity)]
        have e : Real.exp (1 - ((r - d : ℕ) : ℝ)) * Real.exp ((r : ℝ) - d - 1) = 1 := by
          rw [← Real.exp_add]
          push_cast [show d ≤ r by omega]
          rw [show 1 - ((r : ℝ) - d) + ((r : ℝ) - d - 1) = 0 by ring, Real.exp_zero]
        have := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (1 - ((r - d : ℕ) : ℝ))).le
        nlinarith
      have hK0 := hp2WinCell_nonneg r d hj40
      refine (hrest _ hcell hK0 (2 * Real.exp (1 - ((r - d : ℕ) : ℝ))) (hint.trans hbound)).trans
        (le_of_eq ?_)
      have hc : hp2ExtCellS r B i = hp2WinCell r d j * hp2ExtFacS r d := by
        unfold hp2ExtCellS
        rw [if_pos hdeep]
      rw [hc]
      unfold hp2ExtFacS
      ring_nf
    · -- a deep cell `j = i - 40(r - 2)`
      set j := i - 40 * (r - 2) with hj
      have hij : 40 * (r - 2) + j = i := by omega
      have hjN : j < N := by omega
      have hwin := integral_pair_le_hp2WinDeep hX hk hh₁ hh₂ hσ0 hσr hyr (by omega : 4 ≤ r)
      have hlo' : hp2DeepEnd (j + 1) < D * Real.exp ((r : ℝ) + k) := by
        rw [htau, ← hp2CellEnd_deep_mul_exp (by omega : 2 ≤ r), show 40 * (r - 2) + (j + 1) = i + 1
          by omega]
        exact mul_lt_mul_of_pos_right hlo (Real.exp_pos _)
      have hup' : D * Real.exp ((r : ℝ) + k) ≤ hp2DeepEnd j := by
        rw [htau, ← hp2CellEnd_deep_mul_exp (by omega : 2 ≤ r), hij]
        exact mul_le_mul_of_nonneg_right hup (Real.exp_pos _).le
      have hint := hB j hjN hA hD0 hlo' hup' hσA.1 hσA.2 hAU
      refine (hrest _ hwin (hp2WinDeep_nonneg r) (B j) hint).trans (le_of_eq ?_)
      have hc : hp2ExtCellS r B i = hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 4) := by
        unfold hp2ExtCellS
        rw [if_neg hdeep]
      rw [hc]
  · -- below the deep cells
    have hdeep : t ≤ hp2CellEnd (40 * (r - 2)) :=
      hlast.trans (hp2CellEnd_anti (Nat.le_add_right _ _))
    have hwin := integral_pair_le_hp2WinDeep hX hk hh₁ hh₂ hσ0 hσr hyr (by omega : 4 ≤ r)
    have hup' : D * Real.exp ((r : ℝ) + k) ≤ hp2DeepEnd N := by
      rw [htau, ← hp2CellEnd_deep_mul_exp (by omega : 2 ≤ r)]
      exact mul_le_mul_of_nonneg_right hlast (Real.exp_pos _).le
    have hlo' : (-1 : ℝ) < D * Real.exp ((r : ℝ) + k) := by
      have : 0 ≤ D * Real.exp ((r : ℝ) + k) := by positivity
      linarith
    have hint := hsat hA hD0 hlo' hup' hσA.1 hσA.2 hAU
    exact hrest _ hwin (hp2WinDeep_nonneg r) Bsat hint

/-- **The window integral with the rest, through its step function, short tubes**: under the
hypotheses of `RMF.integral_pair_rest_le_cellStep_short` (so `r ≥ 35`),
`∫_W∫_W E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·hp2ExtSumS r N B B_sat`
— `RMF.integral_integral_pair_rest_le_hp2ExtSum` with the short constants. -/
theorem integral_integral_pair_rest_le_hp2ExtSumS (hX : IsRademacherPrimeValues X μ)
    {k r y N : ℕ} {σ : ℝ} {B : ℕ → ℝ} {Bsat : ℝ} (hk : 20 ≤ k)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 35 ≤ r) (hB : ∀ j < N, IsRestCosBound (hp2DeepEnd (j + 1)) (hp2DeepEnd j) (B j))
    (hsat : IsRestCosBound (-1) (hp2DeepEnd N) Bsat) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * hp2ExtSumS r N B Bsat := by
  have hW : MeasurableSet (halfWindow k) := by rw [halfWindow]; exact measurableSet_Icc
  set E : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ with hEdef
  have hE : ∀ h, ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h) ω‖ ^ 2 ∂μ = E := by
    intro h
    rw [hEdef, integral_normSq_Ico_eq_prod hX _ _ σ h, integral_normSq_Ico_eq_prod hX _ _ σ 0]
  have hG0 : ∀ h₁ h₂, 0 ≤ ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
    fun h₁ h₂ => setIntegral_nonneg_of_ae (ae_of_all _ fun ω => by positivity)
  have hpt : ∀ h₁ ∈ halfWindow k, ∀ h₂ ∈ halfWindow k,
      ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
        ≤ E ^ 2 * cellStep (40 * (r - 2) + N) (hp2ExtCellS r B) (hp2ExtSatS r Bsat)
          (|h₁ - h₂| * Real.exp (k : ℝ)) := by
    intro h₁ hh₁ h₂ hh₂
    have h := integral_pair_rest_le_cellStep_short hX hk hh₁ hh₂ hσr hσr' hyr hr hB hsat
    rw [hE h₁, hE h₂] at h
    simpa [sq] using h
  have hinner : ∀ h₁ ∈ halfWindow k, ∫ h₂ in halfWindow k,
      ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
        ≤ E ^ 2 * ∫ h₂ in halfWindow k, cellStep (40 * (r - 2) + N) (hp2ExtCellS r B)
          (hp2ExtSatS r Bsat) (|h₁ - h₂| * Real.exp (k : ℝ)) := by
    intro h₁ hh₁
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun h₂ => hG0 h₁ h₂)
      ((integrableOn_cellStep k _ _ _ h₁).const_mul _) ?_
    exact (ae_restrict_iff' hW).2 (ae_of_all _ fun h₂ hh₂ => hpt h₁ hh₁ h₂ hh₂)
  have hout : ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
      ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ ∫ h₁ in halfWindow k, E ^ 2 * ∫ h₂ in halfWindow k, cellStep (40 * (r - 2) + N)
          (hp2ExtCellS r B) (hp2ExtSatS r Bsat) (|h₁ - h₂| * Real.exp (k : ℝ)) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun h₁ =>
      integral_nonneg fun h₂ => hG0 h₁ h₂) ((integrableOn_integral_cellStep k _ _ _).const_mul _)
      ?_
    exact (ae_restrict_iff' hW).2 (ae_of_all _ hinner)
  refine hout.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_integral_cellStep]
  unfold hp2ExtSumS
  ring

end Pair

end RMF
