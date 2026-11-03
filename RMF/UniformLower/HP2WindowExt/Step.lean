/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2WindowExt.Rest

/-!
# HP2's window integral: the step function with the rest

The pair bound with every prime up to the tilt cutoff `y`, as a step function of
`t = |h₁ - h₂|e^k` over the cells `(a_{i+1}, a_i]`, `a_i = e^{-i/40}`
(`RMF.integral_pair_rest_le_cellStep`):

* on the cells of the depths `d ≤ r - 3`: the constant `RMF.hp2WinCell r d j` of
  `RMF/UniformLower/HP2Window/Cells.lean` times the rest's factor
  `RMF.hp2ExtFac r d = e^{4e^{1-(r-d)} + 10⁻¹⁹}` (the damped integral is at most
  `2/(|h₁ - h₂|e^{k+r}) ≤ 2e^{1-(r-d)}`);
* on the deep cells `j < N` (normalised frequency `τ = te^r ∈ (e^{2-(j+1)/40}, e^{2-j/40}]`):
  `RMF.hp2WinDeep r·e^{2B_j + 10⁻¹⁹}` for bounds `RMF.IsRestCosBound` `B_j` on the rest's damped
  integral; below them, `e^{2B_sat + 10⁻¹⁹}`.

The step function integrates exactly over the window's pairs (`RMF.integral_integral_cellStep`),
so the window integral is at most `(E‖F_y(s_σ)‖²)²e^{-2k}·RMF.hp2ExtSum r N B B_sat`
(`RMF.integral_integral_pair_rest_le_hp2ExtSum`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### Step functions over the cells -/

/-- **A step function over the cells** `(a_{i+1}, a_i]`, `i < n`, and `[0, a_n]`,
`a_i = e^{-i/40}` (`RMF.hp2CellEnd`), with the constants `c i` and `c'`. -/
noncomputable def cellStep (n : ℕ) (c : ℕ → ℝ) (c' t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (Set.Ioc (hp2CellEnd (i + 1)) (hp2CellEnd i)).indicator (fun _ => c i) t
    + (Set.Icc 0 (hp2CellEnd n)).indicator (fun _ => c') t

/-- The cell step function as a combination of `[0, a_i]`-indicators. -/
lemma cellStep_eq_ind (n : ℕ) (c : ℕ → ℝ) (c' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cellStep n c c' t
      = ∑ i ∈ Finset.range n, c i * ((Set.Icc 0 (hp2CellEnd i)).indicator (fun _ => (1 : ℝ)) t
          - (Set.Icc 0 (hp2CellEnd (i + 1))).indicator (fun _ => (1 : ℝ)) t)
        + c' * (Set.Icc 0 (hp2CellEnd n)).indicator (fun _ => (1 : ℝ)) t := by
  unfold cellStep
  rw [indicator_const_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    indicator_Ioc_eq_sub (hp2CellEnd_anti (Nat.le_succ i)) ht

/-- **The inner integral of a cell step function**: for `h₁ ∈ halfWindow k`,
`∫_W cellStep n c c' (|h₁ - h₂|e^k) dh₂` in the window's inner measures. -/
lemma integral_cellStep_inner (k n : ℕ) (c : ℕ → ℝ) (c' : ℝ) {h₁ : ℝ}
    (hh₁ : h₁ ∈ halfWindow k) :
    ∫ h₂ in halfWindow k, cellStep n c c' (|h₁ - h₂| * Real.exp (k : ℝ))
      = ∑ i ∈ Finset.range n, c i
          * (hp2WinInner k h₁ (hp2CellEnd i / Real.exp (k : ℝ))
            - hp2WinInner k h₁ (hp2CellEnd (i + 1) / Real.exp (k : ℝ)))
        + c' * hp2WinInner k h₁ (hp2CellEnd n / Real.exp (k : ℝ)) := by
  have hs := Real.exp_pos (k : ℝ)
  have hE : ∀ i, 0 ≤ hp2CellEnd i := fun i => (Real.exp_pos _).le
  have hW : halfWindow k = Set.Icc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ))) := rfl
  set ind : ℝ → ℝ → ℝ := fun T h₂ =>
    (Set.Icc 0 T).indicator (fun _ => (1 : ℝ)) (|h₁ - h₂| * Real.exp (k : ℝ)) with hind
  have hint : ∀ T, IntegrableOn (ind T) (halfWindow k) := by
    intro T
    have e : ind T = (Set.Icc (h₁ - T / Real.exp (k : ℝ)) (h₁ + T / Real.exp (k : ℝ))).indicator
        (fun _ => (1 : ℝ)) := funext fun h₂ => indicator_Icc_abs_mul hs
    rw [e]
    exact (integrableOn_const (C := (1 : ℝ))
      (hs := by rw [hW]; exact measure_Icc_lt_top.ne)).indicator measurableSet_Icc
  have hval : ∀ T, 0 ≤ T → ∫ h₂ in halfWindow k, ind T h₂
      = hp2WinInner k h₁ (T / Real.exp (k : ℝ)) := by
    intro T hT
    rw [hW] at hh₁
    have := integral_indicator_Icc_abs_mul (c := 1) hh₁ hs hT
    rw [one_mul] at this
    exact this
  have hstep : ∀ h₂ : ℝ, cellStep n c c' (|h₁ - h₂| * Real.exp (k : ℝ))
      = ∑ i ∈ Finset.range n, c i * (ind (hp2CellEnd i) h₂ - ind (hp2CellEnd (i + 1)) h₂)
        + c' * ind (hp2CellEnd n) h₂ := fun h₂ => cellStep_eq_ind n c c' (by positivity)
  rw [setIntegral_congr_fun (by rw [hW]; exact measurableSet_Icc) fun h₂ _ => hstep h₂]
  have hF : ∀ i, Integrable (fun h₂ => c i * (ind (hp2CellEnd i) h₂
      - ind (hp2CellEnd (i + 1)) h₂)) (volume.restrict (halfWindow k)) :=
    fun i => ((hint _).sub (hint _)).const_mul _
  rw [integral_add (integrable_finsetSum _ fun i _ => hF i) ((hint _).const_mul _),
    integral_finsetSum _ fun i _ => hF i, integral_const_mul, hval _ (hE _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_sub (hint _) (hint _), hval _ (hE _), hval _ (hE _)]

/-- **A cell step function integrated over the pairs**:
`∫_W∫_W cellStep n c c' (|h₁ - h₂|e^k) = e^{-2k}(∑_{i<n} c i·hp2Band i + c'·hp2PairVol a_n)`. -/
theorem integral_integral_cellStep (k n : ℕ) (c : ℕ → ℝ) (c' : ℝ) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k, cellStep n c c' (|h₁ - h₂| * Real.exp (k : ℝ))
      = Real.exp (-2 * (k : ℝ))
        * (∑ i ∈ Finset.range n, c i * hp2Band i + c' * hp2PairVol (hp2CellEnd n)) := by
  have hE : ∀ i, 0 ≤ hp2CellEnd i := fun i => (Real.exp_pos _).le
  have hW : halfWindow k = Set.Icc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ))) := rfl
  rw [setIntegral_congr_fun (by rw [hW]; exact measurableSet_Icc)
    fun h₁ hh₁ => integral_cellStep_inner k n c c' hh₁]
  have hint : ∀ τ : ℝ, IntegrableOn (fun h₁ => hp2WinInner k h₁ τ) (halfWindow k) := fun τ => by
    rw [hW]; exact (continuous_hp2WinInner k τ).integrableOn_Icc
  have hF : ∀ i, Integrable (fun h₁ => c i * (hp2WinInner k h₁ (hp2CellEnd i / Real.exp (k : ℝ))
      - hp2WinInner k h₁ (hp2CellEnd (i + 1) / Real.exp (k : ℝ))))
      (volume.restrict (halfWindow k)) := fun i => ((hint _).sub (hint _)).const_mul _
  rw [integral_add (integrable_finsetSum _ fun i _ => hF i) ((hint _).const_mul _),
    integral_finsetSum _ fun i _ => hF i, integral_const_mul, integral_hp2WinInner k (hE _),
    mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (hint _) (hint _), integral_hp2WinInner k (hE _),
      integral_hp2WinInner k (hE _)]
    unfold hp2Band
    ring
  · ring

/-- The cell step function is integrable in `h₂` over the window. -/
lemma integrableOn_cellStep (k n : ℕ) (c : ℕ → ℝ) (c' h₁ : ℝ) :
    IntegrableOn (fun h₂ => cellStep n c c' (|h₁ - h₂| * Real.exp (k : ℝ))) (halfWindow k) := by
  have hs := Real.exp_pos (k : ℝ)
  have hW : halfWindow k = Set.Icc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ))) := rfl
  have hint : ∀ T, IntegrableOn (fun h₂ => (Set.Icc 0 T).indicator (fun _ => (1 : ℝ))
      (|h₁ - h₂| * Real.exp (k : ℝ))) (halfWindow k) := by
    intro T
    have e : (fun h₂ => (Set.Icc 0 T).indicator (fun _ => (1 : ℝ)) (|h₁ - h₂| * Real.exp (k : ℝ)))
        = (Set.Icc (h₁ - T / Real.exp (k : ℝ)) (h₁ + T / Real.exp (k : ℝ))).indicator
          (fun _ => (1 : ℝ)) := funext fun h₂ => indicator_Icc_abs_mul hs
    rw [e]
    exact (integrableOn_const (C := (1 : ℝ))
      (hs := by rw [hW]; exact measure_Icc_lt_top.ne)).indicator measurableSet_Icc
  have e : (fun h₂ => cellStep n c c' (|h₁ - h₂| * Real.exp (k : ℝ)))
      = fun h₂ => ∑ i ∈ Finset.range n, c i * ((Set.Icc 0 (hp2CellEnd i)).indicator
            (fun _ => (1 : ℝ)) (|h₁ - h₂| * Real.exp (k : ℝ))
          - (Set.Icc 0 (hp2CellEnd (i + 1))).indicator (fun _ => (1 : ℝ))
            (|h₁ - h₂| * Real.exp (k : ℝ)))
        + c' * (Set.Icc 0 (hp2CellEnd n)).indicator (fun _ => (1 : ℝ))
          (|h₁ - h₂| * Real.exp (k : ℝ)) :=
    funext fun h₂ => cellStep_eq_ind n c c' (by positivity)
  rw [e]
  exact (integrable_finsetSum _ fun i _ => ((hint _).sub (hint _)).const_mul _).add
    ((hint _).const_mul _)

/-- The inner integral of a cell step function is integrable in `h₁` over the window. -/
lemma integrableOn_integral_cellStep (k n : ℕ) (c : ℕ → ℝ) (c' : ℝ) :
    IntegrableOn (fun h₁ => ∫ h₂ in halfWindow k, cellStep n c c' (|h₁ - h₂| * Real.exp (k : ℝ)))
      (halfWindow k) := by
  have hW : halfWindow k = Set.Icc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ))) := rfl
  have hint : ∀ τ : ℝ, IntegrableOn (fun h₁ => hp2WinInner k h₁ τ) (halfWindow k) := fun τ => by
    rw [hW]; exact (continuous_hp2WinInner k τ).integrableOn_Icc
  have hc : IntegrableOn (fun h₁ => ∑ i ∈ Finset.range n, c i
      * (hp2WinInner k h₁ (hp2CellEnd i / Real.exp (k : ℝ))
        - hp2WinInner k h₁ (hp2CellEnd (i + 1) / Real.exp (k : ℝ)))
      + c' * hp2WinInner k h₁ (hp2CellEnd n / Real.exp (k : ℝ))) (halfWindow k) :=
    (integrable_finsetSum _ fun i _ => ((hint _).sub (hint _)).const_mul _).add
      ((hint _).const_mul _)
  exact hc.congr_fun (fun h₁ hh₁ => (integral_cellStep_inner k n c c' hh₁).symm)
    (by rw [hW]; exact measurableSet_Icc)

/-- **A bound through a cell step function**: for `t ∈ [0, 1]`, nonnegative constants and a bound
`G ≤ E·c i` on each cell `i < n` and `G ≤ E·c'` below `a_n`, `G ≤ E·cellStep n c c' t`. -/
lemma le_mul_cellStep {n : ℕ} {c : ℕ → ℝ} {c' G E t : ℝ} (hc : ∀ i < n, 0 ≤ c i)
    (hc' : 0 ≤ c') (hE : 0 ≤ E) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcell : ∀ i < n, hp2CellEnd (i + 1) < t → t ≤ hp2CellEnd i → G ≤ E * c i)
    (hlast : t ≤ hp2CellEnd n → G ≤ E * c') :
    G ≤ E * cellStep n c c' t := by
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range n,
      (Set.Ioc (hp2CellEnd (i + 1)) (hp2CellEnd i)).indicator (fun _ => c i) t :=
    Finset.sum_nonneg fun i hi => Set.indicator_nonneg (fun _ _ => hc i (Finset.mem_range.1 hi)) t
  have hlast0 : 0 ≤ (Set.Icc 0 (hp2CellEnd n)).indicator (fun _ => c') t :=
    Set.indicator_nonneg (fun _ _ => hc') t
  rcases le_or_gt t (hp2CellEnd n) with h | h
  · refine (hlast h).trans (mul_le_mul_of_nonneg_left ?_ hE)
    have : (Set.Icc 0 (hp2CellEnd n)).indicator (fun _ => c') t = c' :=
      Set.indicator_of_mem (show t ∈ Set.Icc 0 (hp2CellEnd n) from ⟨ht0, h⟩) _
    unfold cellStep
    linarith
  · obtain ⟨i, hi, hlo, hup⟩ := exists_cell_of_lt h ht1
    refine (hcell i hi hlo hup).trans (mul_le_mul_of_nonneg_left ?_ hE)
    have hterm : (Set.Ioc (hp2CellEnd (i + 1)) (hp2CellEnd i)).indicator (fun _ => c i) t = c i :=
      Set.indicator_of_mem (show t ∈ Set.Ioc (hp2CellEnd (i + 1)) (hp2CellEnd i) from ⟨hlo, hup⟩) _
    have hin := Finset.single_le_sum (f := fun i => (Set.Ioc (hp2CellEnd (i + 1))
        (hp2CellEnd i)).indicator (fun _ => c i) t)
      (fun j hj => Set.indicator_nonneg (fun _ _ => hc j (Finset.mem_range.1 hj)) t)
      (Finset.mem_range.2 hi)
    unfold cellStep
    linarith

/-! ### The step function with the rest -/

/-- **The deep cells' ends** `e^{2 - j/40}` in the normalised frequency `|h₁ - h₂|e^{k+r}`. -/
noncomputable def hp2DeepEnd (j : ℕ) : ℝ := Real.exp (2 - (j : ℝ) / 40)

/-- `a_{40(r-2)+j}e^r = e^{2 - j/40}`. -/
lemma hp2CellEnd_deep_mul_exp {r : ℕ} (hr : 2 ≤ r) (j : ℕ) :
    hp2CellEnd (40 * (r - 2) + j) * Real.exp (r : ℝ) = hp2DeepEnd j := by
  unfold hp2CellEnd hp2DeepEnd
  rw [← Real.exp_add]
  congr 1
  push_cast [hr]
  ring

/-- **The rest's factor on the cells of depth `d`**: `e^{4e^{1-(r-d)} + 10⁻¹⁹}`. -/
noncomputable def hp2ExtFac (r d : ℕ) : ℝ :=
  Real.exp (4 * Real.exp (1 - ((r - d : ℕ) : ℝ)) + 1 / 10 ^ 19)

/-- **The cell constants with the rest**: `hp2WinCell r d j·hp2ExtFac r d` on the cell `i = 40d + j`
of the depths `d < r - 2`, `hp2WinDeep r·e^{2B_j + 10⁻¹⁹}` on the deep cell `i = 40(r - 2) + j`. -/
noncomputable def hp2ExtCell (r : ℕ) (B : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < 40 * (r - 2) then hp2WinCell r (i / 40) (i % 40) * hp2ExtFac r (i / 40)
  else hp2WinDeep r * Real.exp (2 * B (i - 40 * (r - 2)) + 1 / 10 ^ 19)

/-- **The constant below the deep cells, with the rest**: `hp2WinDeep r·e^{2B_sat + 10⁻¹⁹}`. -/
noncomputable def hp2ExtSat (r : ℕ) (Bsat : ℝ) : ℝ :=
  hp2WinDeep r * Real.exp (2 * Bsat + 1 / 10 ^ 19)

/-- **The sum over the cells with the rest**: `∑_{i<40(r-2)+N} hp2ExtCell r B i·hp2Band i
  + hp2ExtSat r B_sat·hp2PairVol(a_{40(r-2)+N})`. -/
noncomputable def hp2ExtSum (r N : ℕ) (B : ℕ → ℝ) (Bsat : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (40 * (r - 2) + N), hp2ExtCell r B i * hp2Band i
    + hp2ExtSat r Bsat * hp2PairVol (hp2CellEnd (40 * (r - 2) + N))

lemma hp2ExtCell_nonneg (r : ℕ) (B : ℕ → ℝ) (i : ℕ) : 0 ≤ hp2ExtCell r B i := by
  unfold hp2ExtCell hp2ExtFac
  split_ifs
  · exact mul_nonneg (hp2WinCell_nonneg r _ (Nat.mod_lt _ (by norm_num))) (Real.exp_pos _).le
  · exact mul_nonneg (hp2WinDeep_nonneg r) (Real.exp_pos _).le

lemma hp2ExtSat_nonneg (r : ℕ) (Bsat : ℝ) : 0 ≤ hp2ExtSat r Bsat :=
  mul_nonneg (hp2WinDeep_nonneg r) (Real.exp_pos _).le

section Pair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The damping of the rest in the normalised form: `2σe^{r+k} ∈ [1/(100e), 1/100]` for `r`
maximal. -/
lemma rest_damping_mem {k r : ℕ} {σ : ℝ} (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) :
    1 / (100 * Real.exp 1) ≤ 2 * σ * Real.exp ((r : ℝ) + k)
      ∧ 2 * σ * Real.exp ((r : ℝ) + k) ≤ 1 / 100 := by
  have e : Real.exp ((r : ℝ) + k) = Real.exp ((k : ℝ) + r) := by rw [add_comm]
  have e1 : Real.exp ((k : ℝ) + r + 1) = Real.exp ((k : ℝ) + r) * Real.exp 1 := Real.exp_add _ _
  rw [e]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    rw [e1] at hσr'
    nlinarith [Real.exp_pos 1]
  · linarith

/-- **The pair bound with the rest, cell by cell**: for `k ≥ 20`, heights in the window,
`σe^{k+r} ≤ 1/200 < σe^{k+r+1}`, the tilt cutoff `y ≥ c_r`, `r ≥ 2000` and bounds `B_j`, `B_sat`
on the rest's damped integral over the deep cells and below them,
`E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] ≤ E‖F_y(s₁)‖²E‖F_y(s₂)‖²·cellStep (40(r-2) + N) … (|h₁ - h₂|e^k)`
(the per-cell and deep bounds `RMF.integral_pair_le_hp2WinCell`, `RMF.integral_pair_le_hp2WinDeep`,
and the rest by `RMF.integral_hp1Tube_inter_rest_le`). -/
theorem integral_pair_rest_le_cellStep (hX : IsRademacherPrimeValues X μ) {k r y N : ℕ}
    {σ h₁ h₂ : ℝ} {B : ℕ → ℝ} {Bsat : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 2000 ≤ r) (hB : ∀ j < N, IsRestCosBound (hp2DeepEnd (j + 1)) (hp2DeepEnd j) (B j))
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
        * cellStep (40 * (r - 2) + N) (hp2ExtCell r B) (hp2ExtSat r Bsat)
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
        * (K * Real.exp (2 * c + 1 / 10 ^ 19)) := by
    intro K hK hK0 c hc
    refine (integral_hp1Tube_inter_rest_le hX hk hr hσ0 hh₁ hh₂ hyr hK).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (mul_nonneg hE0 hK0)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (abs_sub_mul_exp_le_of_mem_halfWindow hh₁ hh₂).trans
    (by linarith [Real.exp_pos (-1)])
  refine le_mul_cellStep (fun i _ => hp2ExtCell_nonneg r B i) (hp2ExtSat_nonneg r Bsat) hE0 ht0
    ht1 (fun i hi hlo hup => ?_) fun hlast => ?_
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
      have hc : hp2ExtCell r B i = hp2WinCell r d j * hp2ExtFac r d := by
        unfold hp2ExtCell
        rw [if_pos hdeep]
      rw [hc]
      unfold hp2ExtFac
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
      have hc : hp2ExtCell r B i = hp2WinDeep r * Real.exp (2 * B j + 1 / 10 ^ 19) := by
        unfold hp2ExtCell
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

/-- **The window integral with the rest, through its step function**: under the hypotheses of
`RMF.integral_pair_rest_le_cellStep`,
`∫_W∫_W E[1_{H₁∩H₂}‖F_y(s₁)‖²‖F_y(s₂)‖²] dh₂ dh₁ ≤ (E‖F_y(s_σ)‖²)²·e^{-2k}·hp2ExtSum r N B B_sat`
(`E‖F_y(s_h)‖² = ∏_{c₀≤p<y}(1 + p^{-1-2σ})` does not depend on `h`). -/
theorem integral_integral_pair_rest_le_hp2ExtSum (hX : IsRademacherPrimeValues X μ)
    {k r y N : ℕ} {σ : ℝ} {B : ℕ → ℝ} {Bsat : ℝ} (hk : 20 ≤ k)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1)) (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y)
    (hr : 2000 ≤ r) (hB : ∀ j < N, IsRestCosBound (hp2DeepEnd (j + 1)) (hp2DeepEnd j) (B j))
    (hsat : IsRestCosBound (-1) (hp2DeepEnd N) Bsat) :
    ∫ h₁ in halfWindow k, ∫ h₂ in halfWindow k,
        ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) ^ 2
        * Real.exp (-2 * (k : ℝ)) * hp2ExtSum r N B Bsat := by
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
        ≤ E ^ 2 * cellStep (40 * (r - 2) + N) (hp2ExtCell r B) (hp2ExtSat r Bsat)
          (|h₁ - h₂| * Real.exp (k : ℝ)) := by
    intro h₁ hh₁ h₂ hh₂
    have h := integral_pair_rest_le_cellStep hX hk hh₁ hh₂ hσr hσr' hyr hr hB hsat
    rw [hE h₁, hE h₂] at h
    simpa [sq] using h
  have hinner : ∀ h₁ ∈ halfWindow k, ∫ h₂ in halfWindow k,
      ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) y (shiftLine σ h₂) ω‖ ^ 2 ∂μ
        ≤ E ^ 2 * ∫ h₂ in halfWindow k, cellStep (40 * (r - 2) + N) (hp2ExtCell r B)
          (hp2ExtSat r Bsat) (|h₁ - h₂| * Real.exp (k : ℝ)) := by
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
          (hp2ExtCell r B) (hp2ExtSat r Bsat) (|h₁ - h₂| * Real.exp (k : ℝ)) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun h₁ =>
      integral_nonneg fun h₂ => hG0 h₁ h₂) ((integrableOn_integral_cellStep k _ _ _).const_mul _)
      ?_
    exact (ae_restrict_iff' hW).2 (ae_of_all _ hinner)
  refine hout.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_integral_cellStep]
  unfold hp2ExtSum
  ring

end Pair

end RMF
