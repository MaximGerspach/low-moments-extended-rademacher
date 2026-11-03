/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2Pair
import RMF.UniformLower.HP2PairCells.PostNumerals0
import RMF.UniformLower.HP2PairCells.PostNumerals1
import RMF.UniformLower.HP2PairCells.BridgeNumerals

/-!
# HP2's pair bound, per cell

The discharges of HP2's pair bound (`RMF.integral_hp1Tube_inter_le_hp2PairBoundOf`) per depth `d`
and `u`-cell `j` (`RMF.IsHP2UCell`: `|h₁ - h₂|e^{k+d} ∈ [e^{-(j+1)/40}, e^{-j/40}]`, `k ≥ 20`).

* **The prefix bound as a parameter**: `RMF.IsHP2PrefixBound` and the pair bound
  `RMF.integral_hp1Tube_inter_le_hp2PairBoundOf`.
* **L1, depth `0`**: the prefix term is `(3/2 + 10⁻¹⁵ + c)²` exactly (`RMF.isHP2PrefixBound_zero`).
* **L2, the prefix masses telescoped**: `∑_{m<d}C_m(2h) ≤ U_d ≤ U = 0.28546`
  (`RMF.sum_blockCosSum_two_mul_le_hp2PrefixCosU`), the exponent `RMF.hp2PrefixExponentTel`.
* **L3, short prefixes**: the exponential moment under the one-point tilt
  (`RMF.integral_exp_two_mul_windowZ_le`) gives the prefix bound `RMF.hp2ShortPrefixBound`
  (`≤ 3.6165w² + 0.36788w + 0.135336` at `d = 1`, `6.0551w² + …` at `d = 2`, `w = 3/2 + 10⁻¹⁵ + c`).
* **L4, per cell**: the mass `RMF.hp2CellMass_le`, the post bound with the cell's push
  `RMF.isHP2PostBound_cell_deep` (every `d ≥ 4`), `…_three`, `…_two`, `…_one`, `…_zero`, and the
  bridge `RMF.hp2CellBridge_zero_le` … `…_three_le`.  The numerals are the emitted tables of
  `RMF/UniformLower/HP2PairCells/`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The pair bound with a prefix bound as a parameter -/

section PrefixParam

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **A bound on one walk's prefix term** at depth `d`:
`E'_h[1_{H_d(k,h)}e^{2Z_d}(max(3/2 + 10⁻¹⁵ - Z_d, 0) + c)²] ≤ B` under the one-point tilt at `s_h`
with cutoff `y`.  Supplied by `RMF.hp2PrefixBound` (`RMF.isHP2PrefixBound_hp2PrefixBound`), exactly
at `d = 0` (`RMF.isHP2PrefixBound_zero`) and by exponential moments at `d = 1, 2`
(`RMF.isHP2PrefixBound_short`). -/
def IsHP2PrefixBound (X : ℕ → Ω → ℂ) (μ : Measure Ω) (y k d : ℕ) (σ h c B : ℝ) : Prop :=
  ∫ ω, (hp1Tube X μ y k d σ h).indicator (fun ω => Real.exp (2 * windowZ X μ y k σ h d ω)
      * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c) ^ 2) ω
    ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ) ≤ B

/-- `RMF.hp2PrefixBound` is a prefix bound
(`RMF.integral_hp1Tube_exp_mul_sq_le_hp2PrefixBound`). -/
theorem isHP2PrefixBound_hp2PrefixBound (hX : IsRademacherPrimeValues X μ) {k d y : ℕ}
    {σ h c : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσd : σ * Real.exp ((k : ℝ) + d) ≤ 1 / 200) (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y)
    (hc : 1.05 ≤ c) : IsHP2PrefixBound X μ y k d σ h c (hp2PrefixBound d c) :=
  integral_hp1Tube_exp_mul_sq_le_hp2PrefixBound hX (r := d) (M := d) hk hh hσ hσd
    (primeBlockSub_subset_of_cut_le hyd) le_rfl hc le_rfl

/-- A prefix bound is nonnegative. -/
lemma IsHP2PrefixBound.nonneg {y k d : ℕ} {σ h c B : ℝ}
    (hB : IsHP2PrefixBound X μ y k d σ h c B) : 0 ≤ B :=
  le_trans (integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => by positivity) ω) hB

/-- **One walk's prefix term, for any prefix bound** (`RMF.lintegral_hp1Tube_prefix_sq_le` with
the prefix bound a parameter): for `k ≥ 20`, the cutoff `y ≥ c_d`, `c ≥ 0` and a prefix bound `B`,
`E[1_{H_d(k,h)}(‖F^{pre}(s_h)‖²(A + c))²] ≤ (E‖F^{pre}(s_h)‖²)²·e^{∑_{m<d}(S_m + C_m(2h)) +
5·10⁻²⁰}·B`. -/
theorem lintegral_hp1Tube_prefix_sq_le_of (hX : IsRademacherPrimeValues X μ) {k d y : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y) {c B : ℝ}
    (hc : 0 ≤ c) (hB : IsHP2PrefixBound X μ y k d σ h c B) :
    ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h).indicator (fun ω =>
        (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2
          * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c)) ^ 2) ω) ∂μ
      ≤ ENNReal.ofReal ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
            + 5 / 10 ^ 20) * B) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  have hc0d : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k d⌋₊ + 1 := cut_mono k (Nat.zero_le _)
  have hy := primeBlockSub_subset_of_cut_le hyd
  set Pre : Set Ω := hp1Tube X μ y k d σ h with hPredef
  set sq : Ω → ℝ := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 with hsqdef
  set A : Ω → ℝ := fun ω => max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c with hAdef
  set Mean : ℝ := ∑ i ∈ Finset.range d, windowMeanH X μ y k σ h i with hMeandef
  set P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
    with hPdef
  have hsq0 : ∀ ω, 0 ≤ sq ω := fun ω => by simp only [hsqdef]; positivity
  have hPrem : MeasurableSet[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)]
      Pre := measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h
  have hsqm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)] sq :=
    measurable_primeAlgebra_normSq _ _ _
  have hAm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)] A :=
    ((measurable_const.sub (measurable_primeAlgebra_windowZ (X := X) (μ := μ) y k le_rfl σ
      h)).max measurable_const).add_const _
  have hpt : ∀ ω, ENNReal.ofReal (Pre.indicator (fun ω => (sq ω * A ω) ^ 2) ω)
      = ENNReal.ofReal (sq ω) * ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) := by
    intro ω
    by_cases hω : ω ∈ Pre
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ← ENNReal.ofReal_mul (hsq0 ω)]
      ring_nf
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero, mul_zero]
  have hgm : Measurable[primeAlgebra X (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)]
      fun ω => ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) :=
    ENNReal.measurable_ofReal.comp ((hsqm.mul (hAm.pow_const 2)).indicator hPrem)
  rw [lintegral_congr hpt]
  have htilt : ∫⁻ ω, ENNReal.ofReal (sq ω)
        * ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) ∂μ
      = ENNReal.ofReal (∫ ω, sq ω ∂μ)
        * ∫⁻ ω, ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) ∂P :=
    lintegral_normSq_mul_eq_tiltedMeasure hX hc0d hyd hs hgm
  rw [htilt]
  set W : Ω → ℝ := fun ω => Pre.indicator (fun ω => Real.exp (2 * windowZ X μ y k σ h d ω)
    * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c) ^ 2) ω with hWdef
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω)
      = ENNReal.ofReal (Real.exp (2 * Mean)) * ENNReal.ofReal (W ω) := by
    have hμ := ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
      (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1)
    filter_upwards [(tiltedMeasure_absolutelyContinuous _ y (shiftLine σ h) μ).ae_le hμ]
      with ω hω
    simp only [hWdef]
    by_cases hmem : ω ∈ Pre
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      simp only [hsqdef, hAdef]
      rw [normSq_prefix_eq_exp (μ := μ) (y := y) hσ hω]
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, ENNReal.ofReal_zero,
        mul_zero]
  have hint : Integrable W P :=
    integrable_indicator_hp2Tube_exp_mul_sq hX (P := P) (y := y) (k := k) (M := d)
      (σ := σ) (h := h) (a := 3 / 2) (A := 5 / 2) (B := 3) (ρ := 1 / 10 ^ 15)
      (b := 3 / 2 + 1 / 10 ^ 15) (by norm_num) le_rfl hc
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => by
    simp only [hWdef]
    exact Set.indicator_nonneg (fun ω _ => by positivity) ω
  have hlW : ∫⁻ ω, ENNReal.ofReal (Pre.indicator (fun ω => sq ω * A ω ^ 2) ω) ∂P
      = ENNReal.ofReal (Real.exp (2 * Mean) * ∫ ω, W ω ∂P) := by
    rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hW0),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hlW]
  have hmass := exp_two_mul_sum_windowMeanH_div_prod_le hX (M := d) (y := y) (h := h) hk hσ hy
  rw [← integral_normSq_blocks_eq_prod hX k d σ h] at hmass
  have hE1 : 1 ≤ ∫ ω, sq ω ∂μ := one_le_integral_normSq_Ico hX _ _ _
  have hmean : Real.exp (2 * Mean) ≤ (∫ ω, sq ω ∂μ)
      * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
        + 5 / 10 ^ 20) := by
    rw [div_le_iff₀ (by linarith)] at hmass
    simpa only [hsqdef, hMeandef, mul_comm] using hmass
  have hE0 : 0 ≤ ∫ ω, sq ω ∂μ := by linarith
  have hPB0 : 0 ≤ ∫ ω, W ω ∂P := integral_nonneg hW0
  rw [← ENNReal.ofReal_mul hE0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ ω, sq ω ∂μ) * (Real.exp (2 * Mean) * ∫ ω, W ω ∂P)
      ≤ (∫ ω, sq ω ∂μ) * (((∫ ω, sq ω ∂μ)
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
            + 5 / 10 ^ 20)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hmean hB hPB0 (by positivity)) hE0
    _ = _ := by simp only [hsqdef]; ring

/-- **The pair's prefix term by AM–GM, for any prefix bounds**
(`RMF.lintegral_hp1Tube_pair_le_prefix` with the prefix bounds `B₁`, `B₂` as parameters): for
`c ≥ 0`,
`E[1_{H_d(k,h₁)∩H_d(k,h₂)}W_{[0,d)}(A₁ + c)(A₂ + c)]
  ≤ E‖F^{pre}(s₁)‖²E‖F^{pre}(s₂)‖²·½∑ᵢ e^{∑_{m<d}(S_m + C_m(2hᵢ)) + 5·10⁻²⁰}·Bᵢ`. -/
theorem lintegral_hp1Tube_pair_le_prefix_of (hX : IsRademacherPrimeValues X μ) {k d y : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y) {c B₁ B₂ : ℝ}
    (hc : 0 ≤ c) (hB₁ : IsHP2PrefixBound X μ y k d σ h₁ c B₁)
    (hB₂ : IsHP2PrefixBound X μ y k d σ h₂ c B₂) :
    ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
          * ((max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ d ω) 0 + c)
            * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ d ω) 0 + c))) ω) ∂μ
      ≤ ENNReal.ofReal ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
          * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
          * ((Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
                + 5 / 10 ^ 20) * B₁
            + Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
                + 5 / 10 ^ 20) * B₂) / 2)) := by
  classical
  set sq : ℝ → Ω → ℝ := fun h ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
    X p ω) (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 with hsqdef
  set a : ℝ → Ω → ℝ := fun h ω =>
    max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h d ω) 0 + c with hadef
  set T : ℝ → Ω → ℝ := fun h ω =>
    (hp1Tube X μ y k d σ h).indicator (fun ω => (sq h ω * a h ω) ^ 2) ω with hTdef
  have hT0 : ∀ h ω, 0 ≤ T h ω := fun h ω => by
    simp only [hTdef]
    exact Set.indicator_nonneg (fun ω _ => by positivity) ω
  have hTm : ∀ h, Measurable (T h) := by
    intro h
    have hsqm := ((measurable_primeAlgebra_normSq (X := X) (⌊blockScale k 0⌋₊ + 1)
      (⌊blockScale k d⌋₊ + 1) (shiftLine σ h)).mono (primeAlgebra_le hX _ _) le_rfl)
    have ham : Measurable (a h) :=
      ((measurable_const.sub (measurable_windowZ hX y k σ h d)).max measurable_const).add_const _
    exact ((hsqm.mul ham).pow_const 2).indicator
      (measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h))
  have hpt : ∀ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
      (fun ω => sq h₁ ω * sq h₂ ω * (a h₁ ω * a h₂ ω)) ω)
      ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₁ ω)
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₂ ω) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by have := hT0 h₁ ω; positivity)
        (by have := hT0 h₂ ω; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := indicator_inter_mul_le (T₁ := hp1Tube X μ y k d σ h₁)
      (T₂ := hp1Tube X μ y k d σ h₂) (x := fun ω => sq h₁ ω * a h₁ ω)
      (y := fun ω => sq h₂ ω * a h₂ ω) ω
    have e : ∀ ω, sq h₁ ω * sq h₂ ω * (a h₁ ω * a h₂ ω)
        = sq h₁ ω * a h₁ ω * (sq h₂ ω * a h₂ ω) := fun ω => by ring
    simp only [e]
    exact h
  have hEq : ∫ ω, sq h₁ ω ∂μ = ∫ ω, sq h₂ ω ∂μ := by
    simp only [hsqdef]
    rw [integral_normSq_blocks_eq_prod hX k d σ h₁, integral_normSq_blocks_eq_prod hX k d σ h₂]
  have hP₁ := hB₁.nonneg
  have hP₂ := hB₂.nonneg
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₁ ω)
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₂ ω)) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal (T h₁ ω) ∂μ
        + ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal (T h₂ ω) ∂μ := by
      have hm₁ : Measurable fun ω => ENNReal.ofReal (1 / 2) * ENNReal.ofReal (T h₁ ω) :=
        (ENNReal.measurable_ofReal.comp (hTm h₁)).const_mul _
      rw [lintegral_add_left hm₁,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((∫ ω, sq h₁ ω ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
            + 5 / 10 ^ 20) * B₁)
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((∫ ω, sq h₂ ω ∂μ) ^ 2
          * Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
            + 5 / 10 ^ 20) * B₂) := by
      gcongr
      · exact lintegral_hp1Tube_prefix_sq_le_of hX hk hσ hyd hc hB₁
      · exact lintegral_hp1Tube_prefix_sq_le_of hX hk hσ hyd hc hB₂
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity), hEq]
      congr 1
      ring

/-- **HP2's pair bound with prefix bounds as parameters**:
`Cpost·e^{E_mass}·½∑ᵢ e^{μᵢ + 5·10⁻²⁰}·Bᵢ`. -/
noncomputable def hp2PairBoundOf (Cpost Emass μ₁ μ₂ B₁ B₂ : ℝ) : ℝ :=
  Cpost * Real.exp Emass
    * ((Real.exp (μ₁ + 5 / 10 ^ 20) * B₁ + Real.exp (μ₂ + 5 / 10 ^ 20) * B₂) / 2)

/-- The prefix masses at their bounds, for two prefix bounds. -/
lemma prefix_mass_le_of {A₁ A₂ μ₁ μ₂ B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (h₁ : A₁ ≤ μ₁)
    (h₂ : A₂ ≤ μ₂) :
    (Real.exp (A₁ + 5 / 10 ^ 20) * B₁ + Real.exp (A₂ + 5 / 10 ^ 20) * B₂) / 2
      ≤ (Real.exp (μ₁ + 5 / 10 ^ 20) * B₁ + Real.exp (μ₂ + 5 / 10 ^ 20) * B₂) / 2 := by
  have e₁ := mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (by linarith : A₁ + 5 / 10 ^ 20 ≤ μ₁ + 5 / 10 ^ 20)) hB₁
  have e₂ := mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (by linarith : A₂ + 5 / 10 ^ 20 ≤ μ₂ + 5 / 10 ^ 20)) hB₂
  linarith

/-- **HP2's pair bound at a pair of heights, with prefix bounds as parameters.**  On HP1's tubes
over `r` blocks with the cutoff `y ≥ c_r`, given `Cpost, ch, x ≥ 0`, the post bound
`RMF.IsHP2PostBound … Cpost ch`, the bridge's second moments at most `x²`, the pair mass at most
`E_mass`, the prefix masses at most `μᵢ` and prefix bounds `IsHP2PrefixBound … (ch + x) Bᵢ` for
the two walks:
`E[1_{H(k,h₁)∩H(k,h₂)}‖F(s₁)‖²‖F(s₂)‖²]
  ≤ E‖F(s₁)‖²E‖F(s₂)‖²·hp2PairBoundOf Cpost E_mass μ₁ μ₂ B₁ B₂/(r - b)`, `b = hp2PostStart d`. -/
theorem integral_hp1Tube_inter_le_hp2PairBoundOf (hX : IsRademacherPrimeValues X μ)
    {k d r y : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hbr : hp2PostStart d ≤ r)
    {Cpost ch x Emass μ₁ μ₂ B₁ B₂ : ℝ} (hpost : IsHP2PostBound X μ y k d r σ h₁ h₂ Cpost ch)
    (hCpost : 0 ≤ Cpost) (hch : 0 ≤ ch) (hx : 0 ≤ x)
    (hx₁ : ∑ i ∈ Finset.range (hp2PostStart d - d), pairVarH X μ y k σ h₁ h₂ h₁ (i + d)
        + (∑ i ∈ Finset.range (hp2PostStart d - d),
          (pairMeanH X μ y k σ h₁ h₂ h₁ (i + d) - windowMeanH X μ y k σ h₁ (i + d))) ^ 2 ≤ x ^ 2)
    (hx₂ : ∑ i ∈ Finset.range (hp2PostStart d - d), pairVarH X μ y k σ h₁ h₂ h₂ (i + d)
        + (∑ i ∈ Finset.range (hp2PostStart d - d),
          (pairMeanH X μ y k σ h₁ h₂ h₂ (i + d) - windowMeanH X μ y k σ h₂ (i + d))) ^ 2 ≤ x ^ 2)
    (hmass : ∑ m ∈ Finset.Ico d r, (2 * (blockCosSum k σ (h₁ - h₂) m
        + blockCosSum k σ (h₁ + h₂) m) + Real.exp (-(m : ℝ)) / 10 ^ 20) ≤ Emass)
    (hμ₁ : ∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m) ≤ μ₁)
    (hμ₂ : ∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m) ≤ μ₂)
    (hB₁ : IsHP2PrefixBound X μ y k d σ h₁ (ch + x) B₁)
    (hB₂ : IsHP2PrefixBound X μ y k d σ h₂ (ch + x) B₂) :
    ∫ ω in hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * hp2PairBoundOf Cpost Emass μ₁ μ₂ B₁ B₂ / ((r - hp2PostStart d : ℕ) : ℝ) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hdb := le_hp2PostStart d
  have hdr : d ≤ r := hdb.trans hbr
  have hc0d : ⌊blockScale k 0⌋₊ + 1 ≤ ⌊blockScale k d⌋₊ + 1 := cut_mono k (Nat.zero_le d)
  have hcdb : ⌊blockScale k d⌋₊ + 1 ≤ ⌊blockScale k (hp2PostStart d)⌋₊ + 1 := cut_mono k hdb
  have hcbr : ⌊blockScale k (hp2PostStart d)⌋₊ + 1 ≤ ⌊blockScale k r⌋₊ + 1 := cut_mono k hbr
  have hcdr : ⌊blockScale k d⌋₊ + 1 ≤ ⌊blockScale k r⌋₊ + 1 := cut_mono k hdr
  have hyb : ⌊blockScale k (hp2PostStart d)⌋₊ + 1 ≤ y := hcbr.trans hyr
  have hyd : ⌊blockScale k d⌋₊ + 1 ≤ y := hcdb.trans hyb
  have hy := primeBlockSub_subset_of_cut_le hyb
  have hyb' : ∀ i, i < hp2PostStart d - d → primeBlockSub k (i + d) ⊆ primesBelowSub y :=
    fun i hi => hy (i + d) (by omega)
  have hbx₁ := (integral_bridgeZ_sq_eq (h₁ := h₁) (h₂ := h₂) (h := h₁) (b := hp2PostStart d) hX hk
    hσ hyb').2
  have hbx₂ := (integral_bridgeZ_sq_eq (h₁ := h₁) (h₂ := h₂) (h := h₂) (b := hp2PostStart d) hX hk
    hσ hyb').2
  rw [← hbx₁] at hx₁
  rw [← hbx₂] at hx₂
  set N : ℝ := ((r - hp2PostStart d : ℕ) : ℝ) with hNdef
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have step1 := lintegral_hp1Tube_pair_le_post hX hσ hbr hyr hpost
  have step2 := lintegral_pre_le_bridge (X := X) (μ := μ) (h₁ := h₁) (h₂ := h₂) hX hk hσ hdb hyb
    hCpost hN hch hx hx₁ hx₂
  have step3 := lintegral_hp1Tube_pair_le_prefix_of hX hk hσ hyd (by linarith) hB₁ hB₂
  have hP₁ := hB₁.nonneg
  have hP₂ := hB₂.nonneg
  set Q : ℝ := (Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₁) m)
        + 5 / 10 ^ 20) * B₁
      + Real.exp (∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h₂) m)
        + 5 / 10 ^ 20) * B₂) / 2 with hQdef
  set E₁d : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ with hE₁ddef
  set E₂d : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ with hE₂ddef
  have hpt3 : ∀ ω, ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
        * (Cpost * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ d ω) 0 + ch + x)
          * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ d ω) 0 + ch + x) / N)) ω)
      = ENNReal.ofReal (Cpost / N)
        * ENNReal.ofReal ((hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂).indicator
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k d⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2
            * ((max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₁ d ω) 0 + (ch + x))
              * (max (3 / 2 + 1 / 10 ^ 15 - windowZ X μ y k σ h₂ d ω) 0 + (ch + x)))) ω) := by
    intro ω
    by_cases hω : ω ∈ hp1Tube X μ y k d σ h₁ ∩ hp1Tube X μ y k d σ h₂
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        ← ENNReal.ofReal_mul (div_nonneg hCpost hN)]
      congr 1
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero,
        mul_zero]
  have hL : ∫⁻ ω, ENNReal.ofReal ((hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂).indicator
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2) ω) ∂μ
      ≤ ENNReal.ofReal ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
            X p ω) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1)
              (shiftLine σ h₁) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖
              ^ 2 ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k d⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (shiftLine σ h₁) ω‖
              ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k d⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (shiftLine σ h₂) ω‖
              ^ 2 ∂μ) * (Cpost / N * (E₁d * E₂d * Q)))) := by
    refine step1.trans ?_
    refine (mul_le_mul_right step2 _).trans ?_
    rw [lintegral_congr hpt3, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right step3 _) _) _).trans ?_
    have hEp : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖
            ^ 2 ∂μ := integral_nonneg fun ω => by positivity
    have hEb : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k d⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k d⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (shiftLine σ h₂) ω‖
            ^ 2 ∂μ := integral_nonneg fun ω => by positivity
    rw [← ENNReal.ofReal_mul (div_nonneg hCpost hN), ← ENNReal.ofReal_mul hEb,
      ← ENNReal.ofReal_mul hEp]
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hsplitP := integral_normSq_mul_normSq_Ico_split hX hcdb hcbr (shiftLine σ h₁)
    (shiftLine σ h₂)
  have hmassP := integral_normSq_mul_normSq_blocks_le hX (θ := k) (h₁ := h₁) (h₂ := h₂) hσ hk' d
    (r - d)
  rw [show d + (r - d) = r by omega] at hmassP
  have hexp := Real.exp_le_exp.2 hmass
  have hM : (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k d⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k d⌋₊ + 1) (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (shiftLine σ h₂) ω‖
            ^ 2 ∂μ)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k (hp2PostStart d)⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖
            ^ 2 ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k d⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (⌊blockScale k d⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
        * Real.exp Emass := by
    rw [← hsplitP]
    refine hmassP.trans (mul_le_mul_of_nonneg_left hexp ?_)
    exact mul_nonneg (integral_nonneg fun ω => by positivity)
      (integral_nonneg fun ω => by positivity)
  have hsq₁ := integral_normSq_Ico_split hX hc0d hcdr (shiftLine σ h₁)
  have hsq₂ := integral_normSq_Ico_split hX hc0d hcdr (shiftLine σ h₂)
  have hQ : Q ≤ (Real.exp (μ₁ + 5 / 10 ^ 20) * B₁ + Real.exp (μ₂ + 5 / 10 ^ 20) * B₂) / 2 :=
    prefix_mass_le_of hP₁ hP₂ hμ₁ hμ₂
  have hQ0 : 0 ≤ Q := by
    simp only [hQdef]
    positivity
  have hH : MeasurableSet (hp1Tube X μ y k r σ h₁ ∩ hp1Tube X μ y k r σ h₂) :=
    (measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₁)).inter
      (measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_hp1Tube y k le_rfl σ h₂))
  have hFm : Measurable fun ω =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 :=
    ((measurable_norm_randomEulerProductIco_sqfree hX _ _ _).pow_const 2).mul
      ((measurable_norm_randomEulerProductIco_sqfree hX _ _ _).pow_const 2)
  rw [← integral_indicator hH, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun ω _ => by positivity) ω)
    (hFm.indicator hH).aestronglyMeasurable]
  have hRHS0 : 0 ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ)
      * hp2PairBoundOf Cpost Emass μ₁ μ₂ B₁ B₂ / N := by
    have h1 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₁) ω‖ ^ 2 ∂μ :=
      integral_nonneg fun ω => by positivity
    have h2 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (⌊blockScale k 0⌋₊ + 1) (⌊blockScale k r⌋₊ + 1) (shiftLine σ h₂) ω‖ ^ 2 ∂μ :=
      integral_nonneg fun ω => by positivity
    unfold hp2PairBoundOf
    positivity
  refine ENNReal.toReal_le_of_le_ofReal hRHS0 (hL.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hsq₁, hsq₂]
  unfold hp2PairBoundOf
  exact pair_assembly_le (integral_nonneg fun ω => by positivity)
    (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
    (integral_nonneg fun ω => by positivity) hCpost hN hQ0 hM hQ

end PrefixParam

/-! ### L1: depth `0` exactly

At `d = 0` the prefix is empty: `Z_0 = 0`, so the prefix term is `(3/2 + 10⁻¹⁵ + c)²` exactly
(`RMF.isHP2PrefixBound_zero`). -/

section DepthZero

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The centred walk after `0` blocks is `0`. -/
lemma windowZ_zero (y k : ℕ) (σ h : ℝ) (ω : Ω) : windowZ X μ y k σ h 0 ω = 0 := by
  simp [windowZ, walk]

/-- **L1(a): the prefix term at depth `0` is `(3/2 + 10⁻¹⁵ + c)²`**: `Z_0 = 0`, and the tilt is a
probability measure. -/
theorem isHP2PrefixBound_zero (hX : IsRademacherPrimeValues X μ) (y k : ℕ) {σ h c : ℝ}
    (hσ : 0 ≤ σ) (hc : 0 ≤ c) :
    IsHP2PrefixBound X μ y k 0 σ h c ((3 / 2 + 1 / 10 ^ 15 + c) ^ 2) := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  refine integral_indicator_le_of_le (fun ω _ => by positivity) (fun ω _ => ?_) (by positivity)
  rw [windowZ_zero, mul_zero, Real.exp_zero, one_mul, sub_zero,
    max_eq_left (by norm_num : (0 : ℝ) ≤ 3 / 2 + 1 / 10 ^ 15)]

end DepthZero

/-! ### L2: the prefix masses telescoped

The doubled frequency's prefix sum is a partial integral from its phase
`x = log(2h) + k ∈ [log 2 - 1, log 2]`: `∑_{m<d}C_m(2h) = J(x, d + x)` up to
`3.16·10⁻⁶ + e^{-3}/100` (`RMF.abs_sum_blockCosSum_sub_cosExpInt`); over the phases
`J(x, 1 + x) ≤ 0.28495`, `J(x, 2 + x) ≤ -0.19964` and `J(x, d + x) = J(x, 2) + J(2, d + x)` beyond
(`RMF.hp2Phase_one`, `RMF.hp2Phase_two`, `RMF.hp2Phase_zero_two`, the tail `Φ`). -/

section PrefixTel

/-- **L2's prefix cosine masses** `U_d`: `0, 0.28546, -0.19913, -0.06711` for `d = 0, 1, 2, 3` and
`-0.11003` for `d ≥ 4`. -/
noncomputable def hp2PrefixCosU (d : ℕ) : ℝ :=
  if d = 0 then 0 else if d = 1 then 0.28546 else if d = 2 then -0.19913
    else if d = 3 then -0.06711 else -0.11003

/-- The prefix's damping: from `σe^{k+d+3} ≤ 1/200`, `2σ(e^{d+k} - e^k) ≤ 0.0004979`. -/
lemma prefix_damping_le {k d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hσd : σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) ≤ 1 / 200) :
    2 * σ * (Real.exp (((0 : ℕ) : ℝ) + d + k) - Real.exp (((0 : ℕ) : ℝ) + k)) ≤ 0.0004979 := by
  have h3 := exp_neg_small_numerals.1
  have e : Real.exp (((0 : ℕ) : ℝ) + d + k)
      = Real.exp ((k : ℝ) + ((d : ℝ) + 3)) * Real.exp (-3) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hB : σ * Real.exp (((0 : ℕ) : ℝ) + d + k) ≤ 0.04979 / 200 := by
    rw [e, ← mul_assoc]
    calc σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) * Real.exp (-3) ≤ 1 / 200 * 0.04979 :=
          mul_le_mul hσd h3 (Real.exp_pos _).le (by norm_num)
      _ = 0.04979 / 200 := by ring
  have := two_mul_sigma_damping_le hσ hB (Real.exp_pos (((0 : ℕ) : ℝ) + k)).le
  linarith

/-- **L2: the doubled frequency's prefix sum, telescoped**: for `k ≥ 20`, `h ∈ halfWindow k` and
`σe^{k+d+3} ≤ 1/200`, `∑_{m<d}C_m(2h) ≤ U_d` (`RMF.hp2PrefixCosU`). -/
theorem sum_blockCosSum_two_mul_le_hp2PrefixCosU {k d : ℕ} {σ h : ℝ} (hk : 20 ≤ k)
    (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσd : σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) ≤ 1 / 200) :
    ∑ m ∈ Finset.range d, blockCosSum k σ (2 * h) m ≤ hp2PrefixCosU d := by
  obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
  obtain ⟨hx₁, hx₂⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ2 : 2 * h ≤ 2 * Real.exp (-20) := by
    have := Real.exp_le_exp.2 (show -(k : ℝ) ≤ -20 by linarith)
    linarith [hh.2]
  have hT := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := 0) (j := d) hk hσ
    (by positivity) hτ2)
  have hD := prefix_damping_le (k := k) (d := d) hσ hσd
  simp only [add_zero, Nat.cast_zero, zero_add] at hT hD
  obtain ⟨l2l, l2u⟩ := log_two_numerals
  have hΦ2 := cosExpAnti_two_cosExpTail_two_mem.2
  have hJ2 := hp2Phase_zero_two hx₁ hx₂
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ 4 ≤ d) with h0' | h1 | h2 | h3 | h4
  · subst h0'
    simp [hp2PrefixCosU]
  · subst h1
    rw [show hp2PrefixCosU 1 = 0.28546 by simp [hp2PrefixCosU]]
    simp only [Nat.cast_one] at hT hD
    have hJ := hp2Phase_one hx₁ hx₂
    linarith [hT.2]
  · subst h2
    rw [show hp2PrefixCosU 2 = -0.19913 by simp [hp2PrefixCosU]]
    simp only [Nat.cast_ofNat] at hT hD
    have hJ := (hp2Phase_two hx₁ hx₂).2
    linarith [hT.2]
  · subst h3
    rw [show hp2PrefixCosU 3 = -0.06711 by simp [hp2PrefixCosU]]
    simp only [Nat.cast_ofNat] at hT hD
    have e := cosExpInt_add (Real.log (2 * h) + k) 2 (3 + (Real.log (2 * h) + k))
    have hJ := abs_le.1 (abs_cosExpInt_two_sub_le
      (by linarith : (2 : ℝ) ≤ 3 + (Real.log (2 * h) + k)))
    have hK := abs_le.1 ((abs_cosExpTail_le_phase (v := 3 + (Real.log (2 * h) + k))).2.1
      (by linarith))
    linarith [hT.2]
  · rw [show hp2PrefixCosU d = -0.11003 by
      simp [hp2PrefixCosU, show d ≠ 0 by omega, show d ≠ 1 by omega, show d ≠ 2 by omega,
        show d ≠ 3 by omega]]
    have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast h4
    have e := cosExpInt_add (Real.log (2 * h) + k) 2 (d + (Real.log (2 * h) + k))
    have hJ := abs_le.1 (abs_cosExpInt_two_sub_le
      (by linarith : (2 : ℝ) ≤ d + (Real.log (2 * h) + k)))
    have hK := abs_le.1 ((abs_cosExpTail_le_phase (v := d + (Real.log (2 * h) + k))).2.2
      (by linarith))
    linarith [hT.2]

/-- **L2: the prefix-mass exponent, telescoped**: `(1 + 1/150000)d + U_d`. -/
noncomputable def hp2PrefixExponentTel (d : ℕ) : ℝ := (1 + 1 / 150000) * d + hp2PrefixCosU d

/-- **L2: the prefix masses at their telescoped bound**: for `k ≥ 20`, `h ∈ halfWindow k` and
`σe^{k+d+3} ≤ 1/200`, `∑_{m<d}(S_m + C_m(2h)) ≤ hp2PrefixExponentTel d`. -/
theorem hp2PrefixExponentTel_le {k d : ℕ} {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσd : σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) ≤ 1 / 200) :
    ∑ m ∈ Finset.range d, (blockRpowSum k σ m + blockCosSum k σ (2 * h) m)
      ≤ hp2PrefixExponentTel d := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hS : ∑ m ∈ Finset.range d, blockRpowSum k σ m ≤ (1 + 1 / 150000) * d := by
    have h := Finset.sum_le_sum fun m (_ : m ∈ Finset.range d) =>
      blockRpowSum_le (θ := k) (m := m) hσ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    linarith
  rw [Finset.sum_add_distrib]
  unfold hp2PrefixExponentTel
  linarith [sum_blockCosSum_two_mul_le_hp2PrefixCosU hk hh hσ hσd]

end PrefixTel

/-! ### L3: short prefixes by the exponential moment

Under the one-point tilt the prefix's primes are independent
(`RMF.iIndepFun_localLogAdd_tiltedMeasure_rademacher`), so
`E'[e^{2Z_M}] = ∏_p E'[e^{2(ξ_p - E'ξ_p)}] ≤ e^{2(1 + 10⁻³⁰)∑_{m<M}V_m}` with `|ξ_p| ≤ (11/5)10⁻⁴⁰`
(`RMF.integral_exp_two_mul_windowZ_le`); pointwise
`e^{2z}(max(b - z, 0) + c)² ≤ (b + c)²e^{2z} + (b + c)e^{-1} + e^{-2}` (`RMF.exp_mul_sq_le_short`).
The prefix bound is `RMF.hp2ShortPrefixBound M c`, against the `e^{2b}c²` of `RMF.hp2PrefixBound`
at `M = 1, 2`. -/

section Short

/-- **`e^t` to second order**: `e^t ≤ 1 + t + (1/2 + δ)t²` for `|t| ≤ 4δ ≤ 1` (`Real.exp_bound` at
order three, `(2/9)|t|³ ≤ δt²`). -/
lemma exp_le_add_mul_sq_of_abs_le {t δ : ℝ} (ht : |t| ≤ 4 * δ) (hδ : δ ≤ 1 / 4) :
    Real.exp t ≤ 1 + t + (1 / 2 + δ) * t ^ 2 := by
  have h1 : |t| ≤ 1 := by linarith
  have h := (abs_le.1 (Real.exp_bound h1 (n := 3) (by norm_num))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h3 : |t| ^ 3 ≤ 4 * δ * t ^ 2 := by
    rw [show |t| ^ 3 = |t| * |t| ^ 2 by ring, sq_abs]
    exact mul_le_mul_of_nonneg_right ht (sq_nonneg _)
  have hδ0 : 0 ≤ δ := by linarith [abs_nonneg t]
  have h4 := mul_nonneg hδ0 (sq_nonneg t)
  linarith

/-- **One small variable's exponential moment**: under a probability measure, a measurable `Y` with
`|Y| ≤ δ ≤ 1/4` a.s. has `E[e^{2(Y - EY)}] ≤ e^{2(1 + 2δ)(E[Y²] - (EY)²)}`. -/
lemma integral_exp_two_mul_sub_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) {δ : ℝ} (hδ : δ ≤ 1 / 4)
    (hb : ∀ᵐ ω ∂P, |Y ω| ≤ δ) :
    ∫ ω, Real.exp (2 * (Y ω - ∫ ω, Y ω ∂P)) ∂P
      ≤ Real.exp (2 * (1 + 2 * δ) * (∫ ω, Y ω ^ 2 ∂P - (∫ ω, Y ω ∂P) ^ 2)) := by
  set m := ∫ ω, Y ω ∂P with hmdef
  have hYi : Integrable Y P :=
    Integrable.of_bound hY.aestronglyMeasurable δ (hb.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hY2i : Integrable (fun ω => Y ω ^ 2) P :=
    Integrable.of_bound (hY.pow_const 2).aestronglyMeasurable (δ ^ 2) (hb.mono fun ω h => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  have hm : |m| ≤ δ := by
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := Y) (C := δ)
      (hb.mono fun ω h => by rwa [Real.norm_eq_abs])
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  have hpt : ∀ᵐ ω ∂P, Real.exp (2 * (Y ω - m))
      ≤ (1 - 2 * m + (2 + 4 * δ) * m ^ 2) + (2 - 2 * (2 + 4 * δ) * m) * Y ω
        + (2 + 4 * δ) * Y ω ^ 2 := by
    filter_upwards [hb] with ω hω
    have ht : |2 * (Y ω - m)| ≤ 4 * δ := by
      rw [abs_mul, abs_two]
      have := abs_sub (Y ω) m
      linarith
    have h := exp_le_add_mul_sq_of_abs_le ht hδ
    linarith
  have hL : Integrable (fun ω => (1 - 2 * m + (2 + 4 * δ) * m ^ 2)
      + (2 - 2 * (2 + 4 * δ) * m) * Y ω) P := (integrable_const _).add (hYi.const_mul _)
  have hQ : Integrable (fun ω => (2 + 4 * δ) * Y ω ^ 2) P := hY2i.const_mul _
  have hRi : Integrable (fun ω => (1 - 2 * m + (2 + 4 * δ) * m ^ 2)
      + (2 - 2 * (2 + 4 * δ) * m) * Y ω + (2 + 4 * δ) * Y ω ^ 2) P := hL.add hQ
  have hint := integral_mono_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le) hRi hpt
  have hC : Integrable (fun _ : Ω => 1 - 2 * m + (2 + 4 * δ) * m ^ 2) P := integrable_const _
  have hB : Integrable (fun ω => (2 - 2 * (2 + 4 * δ) * m) * Y ω) P := hYi.const_mul _
  rw [integral_add hL hQ, integral_add hC hB, integral_const, integral_const_mul,
    integral_const_mul, probReal_univ, one_smul, ← hmdef] at hint
  refine hint.trans ?_
  have := Real.add_one_le_exp (2 * (1 + 2 * δ) * (∫ ω, Y ω ^ 2 ∂P - m ^ 2))
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **L3: the centred walk's exponential moment under the one-point tilt**: for `k ≥ 20`, `σ ≥ 0`
and the first `M` blocks below the cutoff `y`, `e^{2Z_M}` is integrable and
`E'_h[e^{2Z_M}] ≤ e^{2(1 + 10⁻³⁰)∑_{m<M}V_m}`, `V_m = RMF.windowVarH`: a product over the prefix's
primes (`ProbabilityTheory.iIndepFun.mgf_sum`), each factor by
`RMF.integral_exp_two_mul_sub_integral_le` at `δ = (11/5)10⁻⁴⁰`. -/
theorem integral_exp_two_mul_windowZ_le (hX : IsRademacherPrimeValues X μ) {k M y : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) :
    Integrable (fun ω => Real.exp (2 * windowZ X μ y k σ h M ω))
        (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
      ∧ ∫ ω, Real.exp (2 * windowZ X μ y k σ h M ω)
          ∂(tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
        ≤ Real.exp (2 * (1 + 1 / 10 ^ 30) * ∑ i ∈ Finset.range M, windowVarH X μ y k σ h i) := by
  classical
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  set P := tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ
    with hPdef
  set T := (Finset.range M).biUnion (fun i => primeBlockSub (k : ℝ) i) with hTdef
  set w : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)) with hwdef
  set ξ : Nat.Primes → Ω → ℝ := fun p ω => localLogAdd (w p) (X (p : ℕ) ω) with hξdef
  set m : Nat.Primes → ℝ := fun p => ∫ ω, ξ p ω ∂P with hmdef
  set Y : Nat.Primes → Ω → ℝ := fun p ω => ξ p ω - m p with hYdef
  set δ : ℝ := 11 / 5 * (1 / 10 ^ 40) with hδdef
  have hdisj : (↑(Finset.range M) : Set ℕ).PairwiseDisjoint
      (fun i => primeBlockSub (k : ℝ) i) := fun a _ b _ hab =>
    pairwise_disjoint_primeBlockSub _ hab
  have hwT : ∀ p ∈ T, p ∈ primesBelowSub y ∧ ‖w p‖ ≤ 1 / 10 ^ 40 := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 hp
    have hk' : (20 : ℝ) ≤ (i : ℝ) + k := by
      have : (20 : ℝ) ≤ k := by exact_mod_cast hk
      linarith [Nat.cast_nonneg (α := ℝ) i]
    exact ⟨hy i (Finset.mem_range.1 hi) hpi,
      norm_cpow_le_of_mem_primeBlockSub hσ hk' (re_shiftLine σ h) hpi⟩
  have hξm : ∀ p, Measurable (ξ p) := fun p =>
    (measurable_localLogAdd (w p)).comp (hX.measurable (p : ℕ) p.2)
  have hbd : ∀ p ∈ T, ∀ᵐ ω ∂P, |ξ p ω| ≤ δ := by
    intro p hp
    have hnorm : ∀ᵐ ω ∂μ, ‖X (p : ℕ) ω‖ = 1 :=
      ((hX.hasLaw (p : ℕ) p.2).ae_iff (measurableSet_setOf.1
        (measurableSet_eq_fun measurable_norm measurable_const))).2 norm_eq_one_rademacherLaw
    filter_upwards [(tiltedMeasure_absolutelyContinuous _ y (shiftLine σ h) μ).ae_le hnorm]
      with ω hω
    exact (abs_localLogAdd_le_of_norm_le hω ((hwT p hp).2.trans (by norm_num))).trans
      (mul_le_mul_of_nonneg_left (hwT p hp).2 (by norm_num))
  have hZ : ∀ ω, windowZ X μ y k σ h M ω = ∑ p ∈ T, Y p ω := by
    intro ω
    have h1 : walk (halfBlock X k σ h) M ω = ∑ p ∈ T, ξ p ω := by
      rw [walk_apply, Finset.sum_biUnion hdisj]
      rfl
    have h2 : ∑ i ∈ Finset.range M, windowMeanH X μ y k σ h i = ∑ p ∈ T, m p := by
      rw [Finset.sum_biUnion hdisj]
      rfl
    rw [windowZ, h1, h2, ← Finset.sum_sub_distrib]
  have hindep : iIndepFun Y P :=
    (iIndepFun_localLogAdd_tiltedMeasure_rademacher hX y hs w).comp (fun p x => x - m p)
      (fun p => measurable_id.sub_const _)
  have hYm : ∀ p, Measurable (Y p) := fun p => (hξm p).sub_const _
  have hYe : ∀ p ω, Y p ω = ξ p ω - m p := fun p ω => rfl
  have hYi : ∀ p ∈ T, Integrable (fun ω => Real.exp (2 * Y p ω)) P := by
    intro p hp
    refine Integrable.of_bound ((hYm p).const_mul 2).exp.aestronglyMeasurable
      (Real.exp (2 * (δ + |m p|))) ?_
    filter_upwards [hbd p hp] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h2 := neg_le_abs (m p)
    have h3 := (abs_le.1 hω).2
    rw [hYe]
    linarith
  have hint : Integrable (fun ω => Real.exp (2 * ∑ p ∈ T, Y p ω)) P := by
    have h := hindep.integrable_exp_mul_sum (t := 2) hYm hYi
    simpa only [Finset.sum_apply] using h
  have hmgf : ∫ ω, Real.exp (2 * ∑ p ∈ T, Y p ω) ∂P
      = ∏ p ∈ T, ∫ ω, Real.exp (2 * Y p ω) ∂P := by
    have h := hindep.mgf_sum (t := 2) hYm T
    simpa only [mgf, Finset.sum_apply] using h
  have hfac : ∀ p ∈ T, ∫ ω, Real.exp (2 * Y p ω) ∂P
      ≤ Real.exp (2 * (1 + 2 * δ) * (∫ ω, ξ p ω ^ 2 ∂P - m p ^ 2)) := fun p hp =>
    integral_exp_two_mul_sub_integral_le (hξm p) (by norm_num [hδdef]) (hbd p hp)
  have hvar : ∑ p ∈ T, (∫ ω, ξ p ω ^ 2 ∂P - m p ^ 2)
      = ∑ i ∈ Finset.range M, windowVarH X μ y k σ h i := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hk' : (20 : ℝ) ≤ (i : ℝ) + k := by
      have : (20 : ℝ) ≤ k := by exact_mod_cast hk
      linarith [Nat.cast_nonneg (α := ℝ) i]
    rw [windowVarH, coe_blockMatchedVarAdd hX y hs (hy i (Finset.mem_range.1 hi))
      (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ h)))
      (fun p hp => (norm_cpow_le_of_mem_primeBlockSub hσ hk' (re_shiftLine σ h) hp).trans
        (by norm_num))]
  have hV0 : 0 ≤ ∑ i ∈ Finset.range M, windowVarH X μ y k σ h i :=
    Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
  simp only [hZ]
  refine ⟨hint, ?_⟩
  rw [hmgf]
  calc ∏ p ∈ T, ∫ ω, Real.exp (2 * Y p ω) ∂P
      ≤ ∏ p ∈ T, Real.exp (2 * (1 + 2 * δ) * (∫ ω, ξ p ω ^ 2 ∂P - m p ^ 2)) :=
        Finset.prod_le_prod (fun p _ => integral_nonneg fun ω => (Real.exp_pos _).le) hfac
    _ = Real.exp (2 * (1 + 2 * δ) * ∑ i ∈ Finset.range M, windowVarH X μ y k σ h i) := by
        rw [← Real.exp_sum, ← Finset.mul_sum, hvar]
    _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by norm_num [hδdef]) hV0)

/-- **The pointwise bound behind L3**: for `b, c ≥ 0`,
`e^{2z}(max(b - z, 0) + c)² ≤ (b + c)²e^{2z} + (b + c)e^{-1} + e^{-2}` (for `z < 0`:
`-2ze^{2z} ≤ e^{-1}` and `z²e^{2z} ≤ e^{-2}`). -/
lemma exp_mul_sq_le_short {z b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.exp (2 * z) * (max (b - z) 0 + c) ^ 2
      ≤ (b + c) ^ 2 * Real.exp (2 * z) + (b + c) * Real.exp (-1) + Real.exp (-2) := by
  have he := Real.exp_pos (2 * z)
  have e1 := Real.exp_pos (-1)
  have e2 := Real.exp_pos (-2)
  have hw : 0 ≤ b + c := by linarith
  rcases le_total b z with hbz | hzb
  · rw [max_eq_right (by linarith)]
    have h1 : c ^ 2 ≤ (b + c) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 he.le
    nlinarith
  · rw [max_eq_left (by linarith)]
    rcases le_total 0 z with hz | hz
    · have h1 : (b - z + c) ^ 2 ≤ (b + c) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h1 he.le
      nlinarith
    · have k1 : -(2 * z) * Real.exp (2 * z) ≤ Real.exp (-1) := by
        have h := Real.add_one_le_exp (-(2 * z) - 1)
        have e : Real.exp (-(2 * z) - 1) * Real.exp (2 * z) = Real.exp (-1) := by
          rw [← Real.exp_add]; congr 1; ring
        calc -(2 * z) * Real.exp (2 * z) = (-(2 * z) - 1 + 1) * Real.exp (2 * z) := by ring
          _ ≤ Real.exp (-(2 * z) - 1) * Real.exp (2 * z) := mul_le_mul_of_nonneg_right h he.le
          _ = Real.exp (-1) := e
      have k2 : z ^ 2 * Real.exp (2 * z) ≤ Real.exp (-2) := by
        have h := Real.add_one_le_exp (-z - 1)
        have hsq : z ^ 2 ≤ Real.exp (-z - 1) ^ 2 := by
          rw [show z ^ 2 = (-z) ^ 2 by ring]
          exact pow_le_pow_left₀ (by linarith) (by linarith) 2
        have e : Real.exp (-z - 1) ^ 2 * Real.exp (2 * z) = Real.exp (-2) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        calc z ^ 2 * Real.exp (2 * z) ≤ Real.exp (-z - 1) ^ 2 * Real.exp (2 * z) :=
              mul_le_mul_of_nonneg_right hsq he.le
          _ = Real.exp (-2) := e
      have expand : Real.exp (2 * z) * (b - z + c) ^ 2 = (b + c) ^ 2 * Real.exp (2 * z)
          + (b + c) * (-(2 * z) * Real.exp (2 * z)) + z ^ 2 * Real.exp (2 * z) := by ring
      rw [expand]
      have := mul_le_mul_of_nonneg_left k1 hw
      linarith

/-- **L3's short-prefix bound at variance `V`**:
`(b + c)²e^{2(1 + 10⁻³⁰)V} + (b + c)e^{-1} + e^{-2}`, `b = 3/2 + 10⁻¹⁵`. -/
noncomputable def hp2ShortPrefixBoundOf (V c : ℝ) : ℝ :=
  (3 / 2 + 1 / 10 ^ 15 + c) ^ 2 * Real.exp (2 * (1 + 1 / 10 ^ 30) * V)
    + (3 / 2 + 1 / 10 ^ 15 + c) * Real.exp (-1) + Real.exp (-2)

/-- **L3: the prefix term by the exponential moment**: for `k ≥ 20`, `σ ≥ 0`, the cutoff `y ≥ c_d`,
`c ≥ 0` and `∑_{m<d}V_m ≤ V`, `RMF.hp2ShortPrefixBoundOf V c` is a prefix bound
(`RMF.exp_mul_sq_le_short`, `RMF.integral_exp_two_mul_windowZ_le`). -/
theorem isHP2PrefixBound_short (hX : IsRademacherPrimeValues X μ) {k d y : ℕ} {σ h c V : ℝ}
    (hk : 20 ≤ k) (hσ : 0 ≤ σ) (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y) (hc : 0 ≤ c)
    (hV : ∑ i ∈ Finset.range d, windowVarH X μ y k σ h i ≤ V) :
    IsHP2PrefixBound X μ y k d σ h c (hp2ShortPrefixBoundOf V c) := by
  have hs : 0 < (shiftLine σ h).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure_rademacher hX y hs
  obtain ⟨hint, hmom⟩ := integral_exp_two_mul_windowZ_le hX (h := h) hk hσ
    (primeBlockSub_subset_of_cut_le hyd)
  have hb : (0 : ℝ) ≤ 3 / 2 + 1 / 10 ^ 15 := by norm_num
  have hbc : (0 : ℝ) ≤ 3 / 2 + 1 / 10 ^ 15 + c := by linarith
  unfold IsHP2PrefixBound hp2ShortPrefixBoundOf
  have hRi : Integrable (fun ω => (3 / 2 + 1 / 10 ^ 15 + c) ^ 2
      * Real.exp (2 * windowZ X μ y k σ h d ω)
      + ((3 / 2 + 1 / 10 ^ 15 + c) * Real.exp (-1) + Real.exp (-2)))
      (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ) :=
    (hint.const_mul _).add (integrable_const _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun ω =>
    Set.indicator_nonneg (fun ω _ => by positivity) ω) hRi (ae_of_all _ fun ω => ?_)).trans ?_
  · dsimp only
    by_cases hω : ω ∈ hp1Tube X μ y k d σ h
    · rw [Set.indicator_of_mem hω]
      have := exp_mul_sq_le_short (z := windowZ X μ y k σ h d ω) hb hc
      linarith
    · rw [Set.indicator_of_notMem hω]
      exact add_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
        (add_nonneg (mul_nonneg hbc (Real.exp_pos _).le) (Real.exp_pos _).le)
  · rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    have hexp := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hV
      (by norm_num : (0 : ℝ) ≤ 2 * (1 + 1 / 10 ^ 30)))
    have := mul_le_mul_of_nonneg_left (hmom.trans hexp) (sq_nonneg (3 / 2 + 1 / 10 ^ 15 + c))
    linarith

/-- **L3's variance at depth `M`**: `V_M = hp2PrefixExponentTel M/2 + 1.6·10⁻²⁰`
(`≤ 0.64274`, `0.90045` at `M = 1, 2`). -/
noncomputable def hp2ShortVar (M : ℕ) : ℝ := hp2PrefixExponentTel M / 2 + 1.6 / 10 ^ 20

/-- **L3: the prefix's variances**: for `k ≥ 20`, `h ∈ halfWindow k`, `σe^{k+M+3} ≤ 1/200` and the
first `M` blocks below the cutoff, `∑_{m<M}V_m ≤ hp2ShortVar M` (`V_m = (S_m + C_m(2h))/2` within
`e^{-m}/10²⁰`, `RMF.abs_blockMatchedVarAdd_height_sub_le_decay`; L2). -/
theorem sum_windowVarH_le_hp2ShortVar (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k M : ℕ}
    {σ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσM : σ * Real.exp ((k : ℝ) + ((M : ℝ) + 3)) ≤ 1 / 200)
    (hy : ∀ m, m < M → primeBlockSub k m ⊆ primesBelowSub y) :
    ∑ i ∈ Finset.range M, windowVarH X μ y k σ h i ≤ hp2ShortVar M := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hblk : ∀ i ∈ Finset.range M, windowVarH X μ y k σ h i
      ≤ (blockRpowSum k σ i + blockCosSum k σ (2 * h) i) / 2
        + Real.exp (-(i : ℝ)) / 10 ^ 20 := by
    intro i hi
    have hm : (20 : ℝ) ≤ (i : ℝ) + k := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have := (abs_le.1 (abs_blockMatchedVarAdd_height_sub_le_decay hX y (θ := k) (h := h) hσ
      (by positivity) hm (hy i (Finset.mem_range.1 hi)))).2
    unfold windowVarH
    linarith
  have hsum := Finset.sum_le_sum hblk
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsum
  have hP := hp2PrefixExponentTel_le hk hh hσ hσM
  have hE := sum_exp_neg_add_le 0 M
  simp only [add_zero] at hE
  have h1 : (∑ i ∈ Finset.range M, Real.exp (-(i : ℝ))) / 10 ^ 20 ≤ 1.59 / 10 ^ 20 :=
    div_le_div_of_nonneg_right hE (by positivity)
  unfold hp2ShortVar
  have h2 : (1.59 : ℝ) / 10 ^ 20 ≤ 1.6 / 10 ^ 20 := by norm_num
  linarith

/-- **L3's short-prefix bound at depth `M`**: `RMF.hp2ShortPrefixBoundOf (RMF.hp2ShortVar M) c`. -/
noncomputable def hp2ShortPrefixBound (M : ℕ) (c : ℝ) : ℝ :=
  hp2ShortPrefixBoundOf (hp2ShortVar M) c

/-- **L3: the short-prefix bound is a prefix bound**, in place of `RMF.hp2PrefixBound M c` at
`M = 1, 2`: for `k ≥ 20`, `h ∈ halfWindow k`, `σe^{k+d+3} ≤ 1/200`, the cutoff `y ≥ c_d` and
`c ≥ 0`. -/
theorem isHP2PrefixBound_hp2ShortPrefixBound (hX : IsRademacherPrimeValues X μ) {k d y : ℕ}
    {σ h c : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσd : σ * Real.exp ((k : ℝ) + ((d : ℝ) + 3)) ≤ 1 / 200)
    (hyd : ⌊blockScale k d⌋₊ + 1 ≤ y) (hc : 0 ≤ c) :
    IsHP2PrefixBound X μ y k d σ h c (hp2ShortPrefixBound d c) :=
  isHP2PrefixBound_short hX hk hσ hyd hc
    (sum_windowVarH_le_hp2ShortVar hX y hk hh hσ hσd (primeBlockSub_subset_of_cut_le hyd))

/-- Two prefix bounds give their minimum. -/
lemma IsHP2PrefixBound.min {y k d : ℕ} {σ h c B₁ B₂ : ℝ}
    (h₁ : IsHP2PrefixBound X μ y k d σ h c B₁) (h₂ : IsHP2PrefixBound X μ y k d σ h c B₂) :
    IsHP2PrefixBound X μ y k d σ h c (min B₁ B₂) :=
  le_min h₁ h₂

/-- `e^{1.2855} ≤ 3.6165` and `e^{1.80089} ≤ 6.0551`. -/
lemma exp_short_numerals :
    Real.exp 1.2855 ≤ 3.6165 ∧ Real.exp 1.80089 ≤ 6.0551 := by
  constructor <;> interval_decide (trust := kernel)

/-- **L3's short-prefix bounds at `M = 1, 2`**: with `w = 3/2 + 10⁻¹⁵ + c`,
`hp2ShortPrefixBound 1 c ≤ 3.6165w² + 0.36788w + 0.135336` and
`hp2ShortPrefixBound 2 c ≤ 6.0551w² + 0.36788w + 0.135336` (`2V₁ ≤ 1.2855`, `2V₂ ≤ 1.80089`),
against the `e^{2b}c² ≈ 20.09c²` of `RMF.hp2PrefixBound`. -/
theorem hp2ShortPrefixBound_one_two_le {c : ℝ} (hc : 0 ≤ c) :
    hp2ShortPrefixBound 1 c ≤ 3.6165 * (3 / 2 + 1 / 10 ^ 15 + c) ^ 2
        + 0.36788 * (3 / 2 + 1 / 10 ^ 15 + c) + 0.135336
      ∧ hp2ShortPrefixBound 2 c ≤ 6.0551 * (3 / 2 + 1 / 10 ^ 15 + c) ^ 2
        + 0.36788 * (3 / 2 + 1 / 10 ^ 15 + c) + 0.135336 := by
  obtain ⟨-, e2, e1⟩ := exp_neg_small_numerals
  obtain ⟨n1, n2⟩ := exp_short_numerals
  have hw : (0 : ℝ) ≤ 3 / 2 + 1 / 10 ^ 15 + c := by linarith
  have hU1 : hp2PrefixCosU 1 = 0.28546 := by simp [hp2PrefixCosU]
  have hU2 : hp2PrefixCosU 2 = -0.19913 := by simp [hp2PrefixCosU]
  have hV1 : 2 * (1 + 1 / 10 ^ 30) * hp2ShortVar 1 ≤ 1.2855 := by
    unfold hp2ShortVar hp2PrefixExponentTel
    rw [hU1]
    norm_num
  have hV2 : 2 * (1 + 1 / 10 ^ 30) * hp2ShortVar 2 ≤ 1.80089 := by
    unfold hp2ShortVar hp2PrefixExponentTel
    rw [hU2]
    norm_num
  have a1 := mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 hV1).trans n1)
    (sq_nonneg (3 / 2 + 1 / 10 ^ 15 + c))
  have a2 := mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 hV2).trans n2)
    (sq_nonneg (3 / 2 + 1 / 10 ^ 15 + c))
  have b1 := mul_le_mul_of_nonneg_left e1 hw
  unfold hp2ShortPrefixBound hp2ShortPrefixBoundOf
  constructor <;> linarith

end Short

/-! ### L4(a): the per-cell mass

On a cell `j` at depth `d` (`RMF.IsHP2UCell`, phase `ξ = d + log|h₁ - h₂| + k ∈ [-(j+1)/40, -j/40]`)
the difference frequency's sum from block `d` is `J(ξ, r - d + ξ) = J(ξ, 2) + J(2, r - d + ξ)` up
to `3.16·10⁻⁶ + 1/100`, with `J(ξ, 2) ≤ RMF.hp2CellMassD j` and `J(2, T) ≈ Φ(T) - Φ(2)`; the sum
frequency's by its phase `x = log(h₁ + h₂) + k ∈ [log 2 - 1, log 2]` per depth
(`RMF.hp2MassS`). -/

section CellMass

/-- `|Φ(T)| ≤ 1.03e^{-T}` for `T ≥ 2`. -/
lemma abs_cosExpTail_le_exp {T : ℝ} (hT : 2 ≤ T) : |cosExpTail T| ≤ 1.03 * Real.exp (-T) := by
  have h := abs_cosExpTail_le_of_ge hT le_rfl
  have h3 := exp_neg_small_numerals.1
  have h4 : Real.exp (-(2 * T)) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
  have he := Real.exp_pos (-T)
  have h5 : 1 + Real.exp (-(2 * T)) / 2 ≤ 1.03 := by linarith
  calc |cosExpTail T| ≤ Real.exp (-T) * (1 + Real.exp (-(2 * T)) / 2) := h
    _ ≤ Real.exp (-T) * 1.03 := mul_le_mul_of_nonneg_left h5 he.le
    _ = 1.03 * Real.exp (-T) := by ring

/-- The damping over blocks ending three before `r`: from `σe^{k+r} ≤ 1/200` and
`m₁ + j + 3 ≤ r`, `2σ(e^{m₁+j+k} - e^{m₁+k}) ≤ 0.0004979`. -/
lemma damping_le_of_add_three_le {k m₁ j r : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hr : m₁ + j + 3 ≤ r) :
    2 * σ * (Real.exp ((m₁ : ℝ) + j + k) - Real.exp ((m₁ : ℝ) + k)) ≤ 0.0004979 := by
  have h3 := exp_neg_small_numerals.1
  have hr' : (m₁ : ℝ) + j + 3 ≤ r := by exact_mod_cast hr
  have e : Real.exp ((m₁ : ℝ) + j + k) ≤ Real.exp ((k : ℝ) + r) * Real.exp (-3) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hB : σ * Real.exp ((m₁ : ℝ) + j + k) ≤ 0.04979 / 200 := by
    calc σ * Real.exp ((m₁ : ℝ) + j + k) ≤ σ * (Real.exp ((k : ℝ) + r) * Real.exp (-3)) :=
          mul_le_mul_of_nonneg_left e hσ
      _ = σ * Real.exp ((k : ℝ) + r) * Real.exp (-3) := by ring
      _ ≤ 1 / 200 * 0.04979 := mul_le_mul hσr h3 (Real.exp_pos _).le (by norm_num)
      _ = 0.04979 / 200 := by ring
  have := two_mul_sigma_damping_le hσ hB (Real.exp_pos ((m₁ : ℝ) + k)).le
  linarith

/-- The damping over blocks ending at `r`: from `σe^{k+r} ≤ 1/200` and `m₁ + j ≤ r`,
`2σ(e^{m₁+j+k} - e^{m₁+k}) ≤ 1/100`. -/
lemma damping_le_of_le {k m₁ j r : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hr : m₁ + j ≤ r) :
    2 * σ * (Real.exp ((m₁ : ℝ) + j + k) - Real.exp ((m₁ : ℝ) + k)) ≤ 2 * (1 / 200) := by
  refine two_mul_sigma_damping_le hσ (le_trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 ?_) hσ) hσr) (Real.exp_pos _).le
  have : (m₁ : ℝ) + j ≤ r := by exact_mod_cast hr
  linarith

/-- **L4(a): the difference frequency's mass on cell `j`**: for `k ≥ 20`, `σe^{k+r} ≤ 1/200` and a
pair in cell `j < 40` at depth `d`, `r ≥ d + 3`,
`∑_{i<r-d}C_{i+d}(h₁ - h₂) ≤ hp2CellMassD j - 0.0971 + 1.03e^{1-(r-d)}`
(`J(ξ, 2) ≤ hp2CellMassD j`, `Φ(2) ≥ 0.10912`, the damping `1/100`). -/
theorem sum_blockCosSum_diff_le_cell {k d r j : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hj : j < 40)
    (hcell : IsHP2UCell k d j h₁ h₂) (hr : d + 3 ≤ r) :
    ∑ i ∈ Finset.range (r - d), blockCosSum k σ (h₁ - h₂) (i + d)
      ≤ hp2CellMassD j - 0.0971 + 1.03 * Real.exp (1 - ((r - d : ℕ) : ℝ)) := by
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk (hcell.depth hj).2
  have hT := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := d) (j := r - d) hk hσ hD0 hD2)
  simp only [blockCosSum_abs] at hT
  have hdamp := damping_le_of_le (m₁ := d) (j := r - d) hσ hσr (by omega)
  set ξ := (d : ℝ) + (Real.log |h₁ - h₂| + k) with hξdef
  have hj' : (j : ℝ) + 1 ≤ 40 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hrd : (3 : ℝ) ≤ ((r - d : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ r - d by omega)
  have e2 : (d : ℝ) + ((r - d : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k) = ((r - d : ℕ) : ℝ) + ξ := by
    rw [hξdef]
    ring
  rw [e2] at hT
  have hξ0 : -1 ≤ ξ := by
    have : ((j : ℝ) + 1) / 40 ≤ 1 := by rw [div_le_one (by norm_num)]; exact hj'
    linarith
  have hsplit := cosExpInt_add ξ 2 (((r - d : ℕ) : ℝ) + ξ)
  have hM := hp2CellMassD_spec hj hξ₁ (by linarith [div_nonneg hj0 (by norm_num : (0 : ℝ) ≤ 40)])
  have hJ := abs_le.1 (abs_cosExpInt_two_sub_le (by linarith : (2 : ℝ) ≤ ((r - d : ℕ) : ℝ) + ξ))
  have hK := abs_le.1 (abs_cosExpTail_le_exp (by linarith : (2 : ℝ) ≤ ((r - d : ℕ) : ℝ) + ξ))
  have hE : Real.exp (-(((r - d : ℕ) : ℝ) + ξ)) ≤ Real.exp (1 - ((r - d : ℕ) : ℝ)) :=
    Real.exp_le_exp.2 (by linarith)
  have hΦ2 := cosExpAnti_two_cosExpTail_two_mem.2
  have h5 : (3.16 : ℝ) / 10 ^ 6 ≤ 0.0000032 := by norm_num
  linarith [hT.2]

/-- **L4(a): the sum frequency's mass per depth**: `-0.12543, 0.21102, 0.16262, 0.07796` for
`d = 0, 1, 2, 3` (the telescoped `J(d + x, r + x)` over the phases `x = log(h₁ + h₂) + k`, the
damping `1/100`, `Φ(2) ≥ 0.10912`), `e^{1-d} + 3.16·10⁻⁶` for `d ≥ 4`
(`RMF.abs_sum_blockCosSum_sum_le_floor`). -/
noncomputable def hp2MassS (d : ℕ) : ℝ :=
  if d = 0 then -0.12543 else if d = 1 then 0.21102 else if d = 2 then 0.16262
    else if d = 3 then 0.07796 else Real.exp (1 - d) + 3.16 / 10 ^ 6

/-- **L4(a): the sum frequency's mass**: for `k ≥ 20`, `h₁, h₂ ∈ halfWindow k`,
`σe^{k+r} ≤ 1/200` and `r ≥ d + 3`,
`∑_{i<r-d}C_{i+d}(h₁ + h₂) ≤ hp2MassS d + 0.52e^{1-(r-d)}`. -/
theorem sum_blockCosSum_sum_le_hp2MassS {k d r : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k)
    (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hr : d + 3 ≤ r) :
    ∑ i ∈ Finset.range (r - d), blockCosSum k σ (h₁ + h₂) (i + d)
      ≤ hp2MassS d + 0.52 * Real.exp (1 - ((r - d : ℕ) : ℝ)) := by
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ h₁ + h₂ := by linarith
  have hτ2 : h₁ + h₂ ≤ 2 * Real.exp (-(k : ℝ)) := by linarith
  have hE0 : 0 ≤ 0.52 * Real.exp (1 - ((r - d : ℕ) : ℝ)) := by positivity
  rcases le_or_gt 4 d with hd | hd
  · have h := (abs_le.1 (abs_sum_blockCosSum_sum_le_floor (j := r - d) (b := d) hk hσ hτ1
      hτ2)).2
    rw [show hp2MassS d = Real.exp (1 - d) + 3.16 / 10 ^ 6 by
      simp [hp2MassS, show d ≠ 0 by omega, show d ≠ 1 by omega, show d ≠ 2 by omega,
        show d ≠ 3 by omega]]
    linarith
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ0 : 0 < h₁ + h₂ := lt_of_lt_of_le (by positivity) hτ1
  have hτ20 : h₁ + h₂ ≤ 2 * Real.exp (-20) := by
    have := Real.exp_le_exp.2 (show -(k : ℝ) ≤ -20 by linarith)
    linarith
  obtain ⟨hx₁, hx₂⟩ := log_add_mem_of_window hτ1 hτ2
  have hT := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := d) (j := r - d) hk hσ hτ0 hτ20)
  have hdamp := damping_le_of_le (m₁ := d) (j := r - d) hσ hσr (by omega)
  set x := Real.log (h₁ + h₂) + k with hxdef
  have e2 : (d : ℝ) + ((r - d : ℕ) : ℝ) + x = (r : ℝ) + x := by
    push_cast [show d ≤ r by omega]
    ring
  rw [e2] at hT
  have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
  obtain ⟨l2l, l2u⟩ := log_two_numerals
  have hK := abs_le.1 (abs_cosExpTail_le_exp (by linarith : (2 : ℝ) ≤ (r : ℝ) + x))
  have hE : Real.exp (-((r : ℝ) + x)) ≤ Real.exp (1 - ((r - d : ℕ) : ℝ)) / 2 := by
    have h1 : Real.exp (-((r : ℝ) + x)) ≤ Real.exp (-((r : ℝ) + (Real.log 2 - 1))) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-((r : ℝ) + (Real.log 2 - 1))) = Real.exp (1 - r) / 2 := by
      rw [show -((r : ℝ) + (Real.log 2 - 1)) = (1 - r) + -Real.log 2 by ring, Real.exp_add,
        Real.exp_neg, Real.exp_log two_pos]
      ring
    have h3 : Real.exp (1 - (r : ℝ)) ≤ Real.exp (1 - ((r - d : ℕ) : ℝ)) := Real.exp_le_exp.2 (by
      push_cast [show d ≤ r by omega]
      linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    linarith
  have hΦ2 := cosExpAnti_two_cosExpTail_two_mem.2
  have h5 : (3.16 : ℝ) / 10 ^ 6 ≤ 0.0000032 := by norm_num
  have hr2 : (2 : ℝ) ≤ (r : ℝ) + x := by linarith
  interval_cases d
  · rw [show hp2MassS 0 = -0.12543 by simp [hp2MassS]]
    simp only [Nat.cast_zero, zero_add] at hT hdamp
    have hsplit := cosExpInt_add x 2 ((r : ℝ) + x)
    have hW := hp2Phase_zero_two hx₁ hx₂
    have hJ := abs_le.1 (abs_cosExpInt_two_sub_le hr2)
    linarith [hT.2]
  · rw [show hp2MassS 1 = 0.21102 by simp [hp2MassS]]
    simp only [Nat.cast_one] at hT hdamp
    have hsplit := cosExpInt_add (1 + x) 2 ((r : ℝ) + x)
    have hW := (hp2Phase_one_two hx₁ hx₂).2
    have hJ := abs_le.1 (abs_cosExpInt_two_sub_le hr2)
    linarith [hT.2]
  · rw [show hp2MassS 2 = 0.16262 by simp [hp2MassS]]
    simp only [Nat.cast_ofNat] at hT hdamp
    rcases le_total x 0 with hx0 | hx0
    · have hsplit := cosExpInt_add (2 + x) 2 ((r : ℝ) + x)
      have hW := (hp2Phase_two_two hx₁ hx0).2
      have hJ := abs_le.1 (abs_cosExpInt_two_sub_le hr2)
      linarith [hT.2]
    · have hJ := abs_le.1 (abs_cosExpInt_sub_tail_le (by linarith : 2 + x ≤ (r : ℝ) + x))
      have hK2 := abs_le.1 ((abs_cosExpTail_le_phase (v := 2 + x)).1 (by linarith))
      have he : 6 * Real.exp (-(4 * (2 + x))) ≤ 0.002013 :=
        le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num))
          six_mul_exp_neg_eight_le'
      linarith [hT.2]
  · rw [show hp2MassS 3 = 0.07796 by simp [hp2MassS]]
    simp only [Nat.cast_ofNat] at hT hdamp
    have hJ := abs_le.1 (abs_cosExpInt_sub_tail_le (by linarith : 3 + x ≤ (r : ℝ) + x))
    have hK3 := abs_le.1 ((abs_cosExpTail_le_phase (v := 3 + x)).2.1 (by linarith))
    have he : 6 * Real.exp (-(4 * (3 + x))) ≤ 0.000126 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num))
        six_mul_exp_neg_four_log_two_add_two_le
    linarith [hT.2]

/-- **L4(a): the pair-mass exponent on cell `j` at depth `d`**:
`2(hp2CellMassD j - 0.0971 + hp2MassS d + 1.55e^{1-(r-d)}) + 1.6·10⁻²⁰`. -/
noncomputable def hp2CellMassExp (d j r : ℕ) : ℝ :=
  2 * (hp2CellMassD j - 0.0971 + hp2MassS d + 1.55 * Real.exp (1 - ((r - d : ℕ) : ℝ)))
    + 1.6 / 10 ^ 20

/-- **L4(a): the pair mass on cell `j`**: for `k ≥ 20`, `h₁, h₂ ∈ halfWindow k`,
`σe^{k+r} ≤ 1/200`, a pair in cell `j < 40` at depth `d` and `r ≥ d + 3`, the mass sum over
`d ≤ m < r` (the hypothesis `hmass` of `RMF.integral_hp1Tube_inter_le_hp2PairBoundOf`) is at most
`hp2CellMassExp d j r`. -/
theorem hp2CellMass_le {k d r j : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hj : j < 40) (hcell : IsHP2UCell k d j h₁ h₂) (hr : d + 3 ≤ r) :
    ∑ m ∈ Finset.Ico d r, (2 * (blockCosSum k σ (h₁ - h₂) m + blockCosSum k σ (h₁ + h₂) m)
        + Real.exp (-(m : ℝ)) / 10 ^ 20) ≤ hp2CellMassExp d j r := by
  have hIco : ∑ m ∈ Finset.Ico d r, (2 * (blockCosSum k σ (h₁ - h₂) m
        + blockCosSum k σ (h₁ + h₂) m) + Real.exp (-(m : ℝ)) / 10 ^ 20)
      = ∑ i ∈ Finset.range (r - d), (2 * (blockCosSum k σ (h₁ - h₂) (i + d)
        + blockCosSum k σ (h₁ + h₂) (i + d)) + Real.exp (-((i + d : ℕ) : ℝ)) / 10 ^ 20) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm d i]
  rw [hIco, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
  have hD := sum_blockCosSum_diff_le_cell hk hσ hσr hj hcell hr
  have hS := sum_blockCosSum_sum_le_hp2MassS hk hh₁ hh₂ hσ hσr hr
  have hE := sum_exp_neg_add_le d (r - d)
  have h1 : (∑ i ∈ Finset.range (r - d), Real.exp (-((i + d : ℕ) : ℝ))) / 10 ^ 20
      ≤ 1.59 / 10 ^ 20 := div_le_div_of_nonneg_right hE (by positivity)
  have h2 : (1.59 : ℝ) / 10 ^ 20 ≤ 1.6 / 10 ^ 20 := by norm_num
  unfold hp2CellMassExp
  linarith

end CellMass

/-! ### L4(b): the per-cell push and post bound

The difference push from the post start `b = d + s` is `-J(s + ξ, T)` up to `3.16·10⁻⁶ + 1/100`
(`RMF.neg_sum_blockCosSum_diff_le_push`), at most `RMF.hp2CellPush0 j`, `…1`, `…2` on cell `j`;
the post bound `RMF.isHP2PostBound_of_numerals` takes it with the cell's `P, K_n, C₀, c_h`
(`RMF.hp2PostP4`, …, `RMF.hp2PostNumerals4_ok`, …). -/

section CellPost

/-- **L4(b): the telescoped push**: for `k ≥ 20`, `0 < |h₁ - h₂| ≤ 2e^{-20}`, `σe^{k+r} ≤ 1/200`
and `b + j' ≤ r`, a bound `-J(a, T) ≤ P` for every `T ≥ a`, `a = b + log|h₁ - h₂| + k`, gives
`-∑_{i<j'}C_{i+b}(h₁ - h₂) ≤ P + 0.01000316`. -/
lemma neg_sum_blockCosSum_diff_le_push {k b r j' : ℕ} {σ h₁ h₂ a P : ℝ} (hk : 20 ≤ k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200) (hD0 : 0 < |h₁ - h₂|)
    (hD2 : |h₁ - h₂| ≤ 2 * Real.exp (-20)) (hr : b + j' ≤ r)
    (ha : a = (b : ℝ) + (Real.log |h₁ - h₂| + k)) (hP : ∀ T, a ≤ T → -cosExpInt a T ≤ P) :
    -∑ i ∈ Finset.range j', blockCosSum k σ (h₁ - h₂) (i + b) ≤ P + 0.01000316 := by
  have hT := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := b) (j := j') hk hσ hD0 hD2)
  simp only [blockCosSum_abs] at hT
  rw [← ha] at hT
  have hj0 : (0 : ℝ) ≤ j' := Nat.cast_nonneg j'
  have hP' := hP ((b : ℝ) + j' + (Real.log |h₁ - h₂| + k)) (by rw [ha]; linarith)
  have hdamp := damping_le_of_le (m₁ := b) (j := j') hσ hσr hr
  have h5 : (3.16 : ℝ) / 10 ^ 6 ≤ 0.0000032 := by norm_num
  linarith [hT.1]

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- A post bound holds for any larger constant and shift (e.g. to raise a cell's `c_h` to the
`1.05` that `RMF.isHP2PrefixBound_hp2PrefixBound` needs). -/
lemma IsHP2PostBound.mono {y k d r : ℕ} {σ h₁ h₂ Cpost ch Cpost' ch' : ℝ}
    (h : IsHP2PostBound X μ y k d r σ h₁ h₂ Cpost ch) (hC : Cpost ≤ Cpost') (hch : ch ≤ ch')
    (hC0 : 0 ≤ Cpost) (hch0 : 0 ≤ ch) : IsHP2PostBound X μ y k d r σ h₁ h₂ Cpost' ch' := by
  intro z₁ z₂ hz₁ hz₂
  refine (h z₁ z₂ hz₁ hz₂).trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
  have a₁ := le_max_right (3 / 2 + 1 / 10 ^ 15 - z₁) 0
  have a₂ := le_max_right (3 / 2 + 1 / 10 ^ 15 - z₂) 0
  have m₁ := mul_le_mul hC (by linarith : max (3 / 2 + 1 / 10 ^ 15 - z₁) 0 + ch
    ≤ max (3 / 2 + 1 / 10 ^ 15 - z₁) 0 + ch') (by linarith) (by linarith)
  exact mul_le_mul m₁ (by linarith) (by linarith)
    (mul_nonneg (by linarith) (by linarith))

/-- **L4(b): the post bound on cell `j` at depth `d ≥ 4`** (post start `b = d`), with the cell's
push `RMF.hp2CellPush0 j`: `Cpost = hp2PostC04 j/√((0.495 - 0.5624/n₀)(0.495 - 1.2572/n₀))`,
`ch = hp2PostCh4 j`. -/
theorem isHP2PostBound_cell_deep (hX : IsRademacherPrimeValues X μ) {k d r y n₀ j : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hd : 4 ≤ d) (hj : j < 40)
    (hcell : IsHP2UCell k d j h₁ h₂) (hn₀ : 3 ≤ n₀) (hr : d + n₀ ≤ r) :
    IsHP2PostBound X μ y k d r σ h₁ h₂
      (hp2PostC04 j / √((0.495 - 0.5624 / n₀) * (0.495 - 1.2572 / n₀))) (hp2PostCh4 j) := by
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn₀0 : (0 : ℝ) < n₀ := by linarith
  have e3 := exp_neg_small_numerals.1
  have hpi := Real.pi_lt_d4
  have hb : hp2PostStart d = d := by simp [hp2PostStart, hd]
  have hed : Real.exp (1 - ((hp2PostStart d : ℕ) : ℝ)) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by
    rw [hb]
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  obtain ⟨hd1, hd2⟩ := hcell.depth hj
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk hd2
  obtain ⟨o1, o2, o3, o4⟩ := hp2PostNumerals4_ok hj
  refine isHP2PostBound_of_numerals hX hk hh₁ hh₂ hσ hσr hyr (s := 0) (by omega) hd1 hd2
    (Or.inl (by rw [hb]; exact hd)) hn₀ (by rw [hb]; exact hr)
    (VL := 0.4575) (vmax := 0.5375) (Dmax := 0.8101) (Smax := 0.0747) (DT := 2.428)
    (ST := 0.1188) (PD := hp2CellPush0 j + 0.01000316) (κ := 0.4425) (Kt := 1.274)
    (Vd := 0.0249) (P := hp2PostP4 j) (c := 0.919) (sq := 0.73315)
    (β₁ := 0.495 - 0.5624 / n₀) (β₂ := 0.495 - 1.2572 / n₀) (Kn := hp2PostKn4 j)
    (C₀ := hp2PostC04 j) (ch := hp2PostCh4 j)
    (fun m hm => ((varTier_bounds (by omega)).2.2 (by omega)).1)
    (fun m hm => ((varTier_bounds (by omega)).2.2 (by omega)).2)
    (fun i _ => (diffTier_le_max i).1) (fun m hm => (sumTier_le_max (by omega)).2.2 (by omega))
    (fun n => (sum_diffTier_le n).1) (fun n => by rw [hb]; exact (sum_sumTier_le n).2.2 d hd)
    (fun n j' hnr hj' => neg_sum_blockCosSum_diff_le_push hk hσ hσr hD0 hD2 (by omega)
      (by rw [hb]) fun T hT => hp2CellPush0_spec hj hξ₁ hξ₂ hT)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) ?_ ?_ (le_of_eq (by norm_num))
    (sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hn₀0.le) _) o2 o3 o4
  · have : (0.5624 : ℝ) / n₀ ≤ 0.5624 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith
  · have : (1.2572 : ℝ) / n₀ ≤ 1.2572 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith

/-- **L4(b): the post bound on cell `j` at depth `3`** (post start `b = 4`), with the cell's push
`RMF.hp2CellPush1 j`: `Cpost = hp2PostC03 j/√((0.495 - 0.5624/n₀)(0.495 - 0.818/n₀))`,
`ch = hp2PostCh3 j`. -/
theorem isHP2PostBound_cell_three (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40)
    (hcell : IsHP2UCell k 3 j h₁ h₂) (hn₀ : 3 ≤ n₀) (hr : 4 + n₀ ≤ r) :
    IsHP2PostBound X μ y k 3 r σ h₁ h₂
      (hp2PostC03 j / √((0.495 - 0.5624 / n₀) * (0.495 - 0.818 / n₀))) (hp2PostCh3 j) := by
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn₀0 : (0 : ℝ) < n₀ := by linarith
  have e3 := exp_neg_small_numerals.1
  have hpi := Real.pi_lt_d4
  have hb : hp2PostStart 3 = 4 := by decide
  have hed : Real.exp (1 - ((hp2PostStart 3 : ℕ) : ℝ)) = Real.exp (-3) := by
    rw [hb]
    norm_num
  obtain ⟨hd1, hd2⟩ := hcell.depth hj
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk hd2
  obtain ⟨o1, o2, o3, o4⟩ := hp2PostNumerals3_ok hj
  refine isHP2PostBound_of_numerals hX hk hh₁ hh₂ hσ hσr hyr (s := 1) (by rw [hb]) hd1 hd2
    (Or.inl (by rw [hb])) hn₀ (by rw [hb]; exact hr)
    (VL := 0.4575) (vmax := 0.5375) (Dmax := 0.7601) (Smax := 0.0747) (DT := 1.618)
    (ST := 0.1188) (PD := hp2CellPush1 j + 0.01000316) (κ := 0.4175) (Kt := 0.869)
    (Vd := 0.0249) (P := hp2PostP3 j) (c := 0.919) (sq := 0.73315)
    (β₁ := 0.495 - 0.5624 / n₀) (β₂ := 0.495 - 0.818 / n₀) (Kn := hp2PostKn3 j)
    (C₀ := hp2PostC03 j) (ch := hp2PostCh3 j)
    (fun m hm => ((varTier_bounds (by omega)).2.2 (by omega)).1)
    (fun m hm => ((varTier_bounds (by omega)).2.2 (by omega)).2)
    (fun i hi => (diffTier_le_max i).2.1 hi)
    (fun m hm => (sumTier_le_max (by omega)).2.2 (by omega))
    (fun n => (sum_diffTier_le n).2.1) (fun n => by rw [hb]; exact (sum_sumTier_le n).2.2 4 le_rfl)
    (fun n j' hnr hj' => neg_sum_blockCosSum_diff_le_push hk hσ hσr hD0 hD2 (by omega)
      (by rw [hb]; push_cast; ring) fun T hT => hp2CellPush1_spec hj hξ₁ hξ₂ hT)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hed]; linarith) (by rw [hed]; linarith)
    (by norm_num) (by nlinarith) (by norm_num) (by norm_num) ?_ ?_ (le_of_eq (by norm_num))
    (sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hn₀0.le) _) o2 o3 o4
  · have : (0.5624 : ℝ) / n₀ ≤ 0.5624 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith
  · have : (0.818 : ℝ) / n₀ ≤ 0.818 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith

/-- **L4(b): the post bound on cell `j` at depth `2`** (post start `b = 4`), with the cell's push
`RMF.hp2CellPush2 j`: `Cpost = hp2PostC02 j/√((0.495 - 0.5624/n₀)(0.495 - 0.2574/n₀))`,
`ch = hp2PostCh2 j`. -/
theorem isHP2PostBound_cell_two (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40)
    (hcell : IsHP2UCell k 2 j h₁ h₂) (hn₀ : 3 ≤ n₀) (hr : 4 + n₀ ≤ r) :
    IsHP2PostBound X μ y k 2 r σ h₁ h₂
      (hp2PostC02 j / √((0.495 - 0.5624 / n₀) * (0.495 - 0.2574 / n₀))) (hp2PostCh2 j) := by
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn₀0 : (0 : ℝ) < n₀ := by linarith
  have e3 := exp_neg_small_numerals.1
  have hpi := Real.pi_lt_d4
  have hb : hp2PostStart 2 = 4 := by decide
  have hed : Real.exp (1 - ((hp2PostStart 2 : ℕ) : ℝ)) = Real.exp (-3) := by
    rw [hb]
    norm_num
  obtain ⟨hd1, hd2⟩ := hcell.depth hj
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk hd2
  obtain ⟨o1, o2, o3, o4⟩ := hp2PostNumerals2_ok hj
  refine isHP2PostBound_of_numerals hX hk hh₁ hh₂ hσ hσr hyr (s := 2) (by rw [hb]) hd1 hd2
    (Or.inl (by rw [hb])) hn₀ (by rw [hb]; exact hr)
    (VL := 0.4575) (vmax := 0.5375) (Dmax := 0.3601) (Smax := 0.0747) (DT := 0.858)
    (ST := 0.1188) (PD := hp2CellPush2 j + 0.01000316) (κ := 0.2175) (Kt := 0.489)
    (Vd := 0.0249) (P := hp2PostP2 j) (c := 0.919) (sq := 0.73315)
    (β₁ := 0.495 - 0.5624 / n₀) (β₂ := 0.495 - 0.2574 / n₀) (Kn := hp2PostKn2 j)
    (C₀ := hp2PostC02 j) (ch := hp2PostCh2 j)
    (fun m hm => ((varTier_bounds (by omega)).2.2 (by omega)).1)
    (fun m hm => ((varTier_bounds (by omega)).2.2 (by omega)).2)
    (fun i hi => (diffTier_le_max i).2.2 hi)
    (fun m hm => (sumTier_le_max (by omega)).2.2 (by omega))
    (fun n => (sum_diffTier_le n).2.2) (fun n => by rw [hb]; exact (sum_sumTier_le n).2.2 4 le_rfl)
    (fun n j' hnr hj' => neg_sum_blockCosSum_diff_le_push hk hσ hσr hD0 hD2 (by omega)
      (by rw [hb]; push_cast; ring) fun T hT => hp2CellPush2_spec hj hξ₁ hξ₂ hT)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hed]; linarith) (by rw [hed]; linarith)
    (by norm_num) (by nlinarith) (by norm_num) (by norm_num) ?_ ?_ (le_of_eq (by norm_num))
    (sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hn₀0.le) _) o2 o3 o4
  · have : (0.5624 : ℝ) / n₀ ≤ 0.5624 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith
  · have : (0.2574 : ℝ) / n₀ ≤ 0.2574 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith

/-- **L4(b): the post bound on cell `j` at depth `1`** (post start `b = 3`), with the cell's push
`RMF.hp2CellPush2 j`: `Cpost = hp2PostC01 j/√((0.495 - 0.6408/n₀)(0.495 - 0.405/n₀))`,
`ch = hp2PostCh1 j`. -/
theorem isHP2PostBound_cell_one (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40)
    (hcell : IsHP2UCell k 1 j h₁ h₂) (hn₀ : 3 ≤ n₀) (hr : 3 + n₀ ≤ r) :
    IsHP2PostBound X μ y k 1 r σ h₁ h₂
      (hp2PostC01 j / √((0.495 - 0.6408 / n₀) * (0.495 - 0.405 / n₀))) (hp2PostCh1 j) := by
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn₀0 : (0 : ℝ) < n₀ := by linarith
  have e2 := exp_neg_small_numerals.2.1
  have hpi := Real.pi_lt_d4
  have hb : hp2PostStart 1 = 3 := by decide
  have hed : Real.exp (1 - ((hp2PostStart 1 : ℕ) : ℝ)) = Real.exp (-2) := by
    rw [hb]
    norm_num
  obtain ⟨hd1, hd2⟩ := hcell.depth hj
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk hd2
  have hcase : Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + ((3 : ℕ) : ℝ)) :=
    exp_one_le_of_depth (d := 1) hd1
  obtain ⟨o1, o2, o3, o4⟩ := hp2PostNumerals1_ok hj
  refine isHP2PostBound_of_numerals hX hk hh₁ hh₂ hσ hσr hyr (s := 2) (by rw [hb]) hd1 hd2
    (Or.inr ⟨by rw [hb]; omega, by rw [hb]; exact hcase⟩) hn₀ (by rw [hb]; exact hr)
    (VL := 0.4219) (vmax := 0.5731) (Dmax := 0.3601) (Smax := 0.1461) (DT := 0.858)
    (ST := 0.265) (PD := hp2CellPush2 j + 0.01000316) (κ := 0.2532) (Kt := 0.562)
    (Vd := 0.0677) (P := hp2PostP1 j) (c := 0.9489) (sq := 0.75704)
    (β₁ := 0.495 - 0.6408 / n₀) (β₂ := 0.495 - 0.405 / n₀) (Kn := hp2PostKn1 j)
    (C₀ := hp2PostC01 j) (ch := hp2PostCh1 j)
    (fun m hm => ((varTier_bounds (by omega)).2.1 (by omega)).1)
    (fun m hm => ((varTier_bounds (by omega)).2.1 (by omega)).2)
    (fun i hi => (diffTier_le_max i).2.2 hi)
    (fun m hm => (sumTier_le_max (by omega)).2.1 (by omega))
    (fun n => (sum_diffTier_le n).2.2) (fun n => by rw [hb]; exact (sum_sumTier_le n).2.1)
    (fun n j' hnr hj' => neg_sum_blockCosSum_diff_le_push hk hσ hσr hD0 hD2 (by omega)
      (by rw [hb]; push_cast; ring) fun T hT => hp2CellPush2_spec hj hξ₁ hξ₂ hT)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hed]; linarith) (by rw [hed]; linarith)
    (by norm_num) (by nlinarith) (by norm_num) (by norm_num) ?_ ?_ (le_of_eq (by norm_num))
    (sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hn₀0.le) _) o2 o3 o4
  · have : (0.6408 : ℝ) / n₀ ≤ 0.6408 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith
  · have : (0.405 : ℝ) / n₀ ≤ 0.405 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith

/-- **L4(b): the post bound on cell `j` at depth `0`** (post start `b = 2`), with the cell's push
`RMF.hp2CellPush2 j`: `Cpost = hp2PostC00 j/√((0.495 - 0.8391/n₀)(0.495 - 0.8427/n₀))`,
`ch = hp2PostCh0 j`. -/
theorem isHP2PostBound_cell_zero (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40)
    (hcell : IsHP2UCell k 0 j h₁ h₂) (hn₀ : 3 ≤ n₀) (hr : 2 + n₀ ≤ r) :
    IsHP2PostBound X μ y k 0 r σ h₁ h₂
      (hp2PostC00 j / √((0.495 - 0.8391 / n₀) * (0.495 - 0.8427 / n₀))) (hp2PostCh0 j) := by
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn₀0 : (0 : ℝ) < n₀ := by linarith
  have e1 := exp_neg_small_numerals.2.2
  have hpi := Real.pi_lt_d4
  have hb : hp2PostStart 0 = 2 := by decide
  have hed : Real.exp (1 - ((hp2PostStart 0 : ℕ) : ℝ)) = Real.exp (-1) := by
    rw [hb]
    norm_num
  obtain ⟨hd1, hd2⟩ := hcell.depth hj
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk hd2
  have hcase : Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + ((2 : ℕ) : ℝ)) :=
    exp_one_le_of_depth (d := 0) hd1
  obtain ⟨o1, o2, o3, o4⟩ := hp2PostNumerals0_ok hj
  refine isHP2PostBound_of_numerals hX hk hh₁ hh₂ hσ hσr hyr (s := 2) (by rw [hb]) hd1 hd2
    (Or.inr ⟨by rw [hb], by rw [hb]; exact hcase⟩) hn₀ (by rw [hb]; exact hr)
    (VL := 0.3649) (vmax := 0.6551) (Dmax := 0.3601) (Smax := 0.3101) (DT := 0.858)
    (ST := 0.575) (PD := hp2CellPush2 j + 0.01000316) (κ := 0.3352) (Kt := 0.717)
    (Vd := 0.184) (P := hp2PostP0 j) (c := 1.0145) (sq := 0.80939)
    (β₁ := 0.495 - 0.8391 / n₀) (β₂ := 0.495 - 0.8427 / n₀) (Kn := hp2PostKn0 j)
    (C₀ := hp2PostC00 j) (ch := hp2PostCh0 j)
    (fun m hm => ((varTier_bounds (by omega)).1).1)
    (fun m hm => ((varTier_bounds (by omega)).1).2)
    (fun i hi => (diffTier_le_max i).2.2 hi) (fun m hm => (sumTier_le_max (by omega)).1)
    (fun n => (sum_diffTier_le n).2.2) (fun n => by rw [hb]; exact (sum_sumTier_le n).1)
    (fun n j' hnr hj' => neg_sum_blockCosSum_diff_le_push hk hσ hσr hD0 hD2 (by omega)
      (by rw [hb]; push_cast; ring) fun T hT => hp2CellPush2_spec hj hξ₁ hξ₂ hT)
    (by norm_num) (by norm_num) (by norm_num) (by rw [hed]; linarith) (by rw [hed]; linarith)
    (by norm_num) (by nlinarith) (by norm_num) (by norm_num) ?_ ?_ (le_of_eq (by norm_num))
    (sub_le_sub_left (div_le_div_of_nonneg_right (by norm_num) hn₀0.le) _) o2 o3 o4
  · have : (0.8391 : ℝ) / n₀ ≤ 0.8391 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith
  · have : (0.8427 : ℝ) / n₀ ≤ 0.8427 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn₀'
    linarith

end CellPost

/-! ### L4(c): the per-cell bridge

For `d ≤ 3` the bridge blocks `d ≤ m < d + L` (`L = 2, 2, 2, 1`) carry the difference frequency's
`J(ξ, L + ξ)` on the cell (`RMF.hp2CellBridge2Lo` …) and the sum and doubled frequencies'
`J(d + x, d + L + x)` over the phases (`RMF.hp2Phase_two`, `RMF.hp2Phase_bridge_one` …); with
`RMF.bridge_moment_le_of_cos` the bridge's second moment is at most `hp2BridgeX{d} j²`
(`RMF.hp2BridgeNumerals0_ok` …). -/

section CellBridge

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **L4(c): the bridge's second moment from ranges of partial integrals**: for a pair at
`0 < |h₁ - h₂| ≤ 2e^{-20}`, `h₁, h₂ ∈ halfWindow k`, `k ≥ 20`, with post start
`hp2PostStart d = d + L`, `σe^{k+r} ≤ 1/200`, `r ≥ d + L + 3` and the cutoff `y ≥ c_r`: the range
`[lo, hi]` of `J(ξ, L + ξ)`, `ξ = d + log|h₁ - h₂| + k`, and `[Slo, Shi]` of `J(d + x, d + L + x)`
over the phases `x ∈ [log 2 - 1, log 2]` bound the bridge's second moment at `h ∈ {h₁, h₂}` by
`V + 1.6·10⁻²⁰ + (M + 3.2·10⁻²⁰)²` for `V ≥ (L(1 + 1/150000) + Shi + 0.000502)/2` and
`M ≥ -(lo + Slo) + 0.001004, hi + Shi + 0.001004`. -/
theorem bridge_moment_le_of_cell (hX : IsRademacherPrimeValues X μ) {k d L r y : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hbL : hp2PostStart d = d + L) (hr : d + L + 3 ≤ r)
    (hhh : h = h₁ ∨ h = h₂) (hD0 : 0 < |h₁ - h₂|) (hD2 : |h₁ - h₂| ≤ 2 * Real.exp (-20))
    {lo hi Slo Shi V M : ℝ}
    (hD : lo ≤ cosExpInt ((d : ℝ) + (Real.log |h₁ - h₂| + k))
        ((d : ℝ) + L + (Real.log |h₁ - h₂| + k))
      ∧ cosExpInt ((d : ℝ) + (Real.log |h₁ - h₂| + k)) ((d : ℝ) + L + (Real.log |h₁ - h₂| + k))
        ≤ hi)
    (hS : ∀ x, Real.log 2 - 1 ≤ x → x ≤ Real.log 2 →
      Slo ≤ cosExpInt ((d : ℝ) + x) ((d : ℝ) + L + x)
        ∧ cosExpInt ((d : ℝ) + x) ((d : ℝ) + L + x) ≤ Shi)
    (hV : ((L : ℝ) * (1 + 1 / 150000) + Shi + 0.000502) / 2 ≤ V)
    (hM₁ : -M ≤ lo + Slo - 2 * 0.000502) (hM₂ : hi + Shi + 2 * (0.000502 : ℝ) ≤ M) :
    ∑ i ∈ Finset.range (hp2PostStart d - d), pairVarH X μ y k σ h₁ h₂ h (i + d)
        + (∑ i ∈ Finset.range (hp2PostStart d - d),
          (pairMeanH X μ y k σ h₁ h₂ h (i + d) - windowMeanH X μ y k σ h (i + d))) ^ 2
      ≤ V + 1.6 / 10 ^ 20 + (M + 3.2 / 10 ^ 20) ^ 2 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : hp2PostStart d - d = L := by omega
  have hh : h ∈ halfWindow k := by rcases hhh with rfl | rfl <;> assumption
  have hy : ∀ i, i < hp2PostStart d - d → primeBlockSub k (i + d) ⊆ primesBelowSub y :=
    fun i _ => primeBlockSub_subset_of_cut_le hyr (i + d) (by omega)
  have hdamp := damping_le_of_add_three_le (m₁ := d) (j := L) hσ hσr hr
  have h5 : (3.16 : ℝ) / 10 ^ 6 + 0.0004979 ≤ 0.000502 := by norm_num
  have h20 : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
  -- the difference frequency
  have hTD := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := d) (j := L) hk hσ hD0 hD2)
  simp only [blockCosSum_abs] at hTD
  -- the sum frequency
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ h₁ + h₂ := by linarith
  have hτ2 : h₁ + h₂ ≤ 2 * Real.exp (-(k : ℝ)) := by linarith
  have hτ0 : 0 < h₁ + h₂ := lt_of_lt_of_le (by positivity) hτ1
  have hTS := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := d) (j := L) hk hσ hτ0
    (by linarith))
  obtain ⟨hx₁, hx₂⟩ := log_add_mem_of_window hτ1 hτ2
  have hS1 := hS _ hx₁ hx₂
  -- the doubled frequency
  obtain ⟨h0, -, -⟩ := log_add_mem_of_mem_halfWindow hh
  obtain ⟨hy₁, hy₂⟩ := log_two_mul_add_mem_of_mem_halfWindow hh
  have hT2 := abs_le.1 (abs_sum_blockCosSum_sub_cosExpInt (m₁ := d) (j := L) (τ := 2 * h) hk hσ
    (by positivity) (by linarith [hh.2]))
  have hS2 := hS _ hy₁ hy₂
  -- the Mertens sums
  have hR : ∑ i ∈ Finset.range L, blockRpowSum k σ (i + d) ≤ L * (1 + 1 / 150000) := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.range L) =>
      blockRpowSum_le (θ := k) (m := i + d) hσ (by linarith [Nat.cast_nonneg (α := ℝ) (i + d)])
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    linarith
  refine bridge_moment_le_of_cos hX hk hσ hhh hy (V := V) (M := M) ?_ ?_
  · rw [hL, ← Finset.sum_div, Finset.sum_add_distrib]
    linarith [hT2.2, hS2.2]
  · rw [hL, Finset.sum_add_distrib, abs_le]
    constructor <;> linarith [hTD.1, hTD.2, hTS.1, hTS.2, hD.1, hD.2, hS1.1, hS1.2]

/-- **L4(c): the bridge on cell `j` at depth `0`** (blocks `0, 1`): for `h ∈ {h₁, h₂}` the
bridge's second moment under the two-fold tilt is at most `hp2BridgeX0 j²`. -/
theorem hp2CellBridge_zero_le (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40) (hcell : IsHP2UCell k 0 j h₁ h₂)
    (hn₀ : 3 ≤ n₀) (hr : hp2PostStart 0 + n₀ ≤ r) (hhh : h = h₁ ∨ h = h₂) :
    ∑ i ∈ Finset.range (hp2PostStart 0 - 0), pairVarH X μ y k σ h₁ h₂ h (i + 0)
        + (∑ i ∈ Finset.range (hp2PostStart 0 - 0),
          (pairMeanH X μ y k σ h₁ h₂ h (i + 0) - windowMeanH X μ y k σ h (i + 0))) ^ 2
      ≤ hp2BridgeX0 j ^ 2 := by
  have hb : hp2PostStart 0 = 0 + 2 := by decide
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk (hcell.depth hj).2
  obtain ⟨o1, o2, o3⟩ := hp2BridgeNumerals0_ok hj
  have hD := hp2CellBridge2_spec hj hξ₁ hξ₂
  have e : ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)
      = 2 + (((0 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)) := by push_cast; ring
  refine (bridge_moment_le_of_cell hX hk hh₁ hh₂ hσ hσr hyr hb (by omega) hhh hD0 hD2
    (lo := hp2CellBridge2Lo j) (hi := hp2CellBridge2Hi j) (Slo := -0.5631) (Shi := -0.19964)
    (V := 0.90044) (M := hp2BridgeM0 j) (by rw [e]; exact hD) (fun x hx₁ hx₂ => ?_)
    (by norm_num) o1 o2).trans o3
  have e' : ((0 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + x = 2 + x := by push_cast; ring
  have e'' : ((0 : ℕ) : ℝ) + x = x := by push_cast; ring
  rw [e', e'']
  exact hp2Phase_two hx₁ hx₂

/-- **L4(c): the bridge on cell `j` at depth `1`** (blocks `1, 2`): for `h ∈ {h₁, h₂}` the
bridge's second moment under the two-fold tilt is at most `hp2BridgeX1 j²`. -/
theorem hp2CellBridge_one_le (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40) (hcell : IsHP2UCell k 1 j h₁ h₂)
    (hn₀ : 3 ≤ n₀) (hr : hp2PostStart 1 + n₀ ≤ r) (hhh : h = h₁ ∨ h = h₂) :
    ∑ i ∈ Finset.range (hp2PostStart 1 - 1), pairVarH X μ y k σ h₁ h₂ h (i + 1)
        + (∑ i ∈ Finset.range (hp2PostStart 1 - 1),
          (pairMeanH X μ y k σ h₁ h₂ h (i + 1) - windowMeanH X μ y k σ h (i + 1))) ^ 2
      ≤ hp2BridgeX1 j ^ 2 := by
  have hb : hp2PostStart 1 = 1 + 2 := by decide
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk (hcell.depth hj).2
  obtain ⟨o1, o2, o3⟩ := hp2BridgeNumerals1_ok hj
  have hD := hp2CellBridge2_spec hj hξ₁ hξ₂
  have e : ((1 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)
      = 2 + (((1 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)) := by push_cast; ring
  refine (bridge_moment_le_of_cell hX hk hh₁ hh₂ hσ hσr hyr hb (by omega) hhh hD0 hD2
    (lo := hp2CellBridge2Lo j) (hi := hp2CellBridge2Hi j) (Slo := -0.49246) (Shi := 0.26884)
    (V := 1.13468) (M := hp2BridgeM1 j) (by rw [e]; exact hD) (fun x hx₁ hx₂ => ?_)
    (by norm_num) o1 o2).trans o3
  have e' : ((1 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + x = 3 + x := by push_cast; ring
  have e'' : ((1 : ℕ) : ℝ) + x = 1 + x := by push_cast; ring
  rw [e', e'']
  exact hp2Phase_bridge_one hx₁ hx₂

/-- **L4(c): the bridge on cell `j` at depth `2`** (blocks `2, 3`): for `h ∈ {h₁, h₂}` the
bridge's second moment under the two-fold tilt is at most `hp2BridgeX2 j²`. -/
theorem hp2CellBridge_two_le (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40) (hcell : IsHP2UCell k 2 j h₁ h₂)
    (hn₀ : 3 ≤ n₀) (hr : hp2PostStart 2 + n₀ ≤ r) (hhh : h = h₁ ∨ h = h₂) :
    ∑ i ∈ Finset.range (hp2PostStart 2 - 2), pairVarH X μ y k σ h₁ h₂ h (i + 2)
        + (∑ i ∈ Finset.range (hp2PostStart 2 - 2),
          (pairMeanH X μ y k σ h₁ h₂ h (i + 2) - windowMeanH X μ y k σ h (i + 2))) ^ 2
      ≤ hp2BridgeX2 j ^ 2 := by
  have hb : hp2PostStart 2 = 2 + 2 := by decide
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk (hcell.depth hj).2
  obtain ⟨o1, o2, o3⟩ := hp2BridgeNumerals2_ok hj
  have hD := hp2CellBridge2_spec hj hξ₁ hξ₂
  have e : ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)
      = 2 + (((2 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)) := by push_cast; ring
  refine (bridge_moment_le_of_cell hX hk hh₁ hh₂ hσ hσr hyr hb (by omega) hhh hD0 hD2
    (lo := hp2CellBridge2Lo j) (hi := hp2CellBridge2Hi j) (Slo := -0.1635) (Shi := 0.17752)
    (V := 1.08902) (M := hp2BridgeM2 j) (by rw [e]; exact hD) (fun x hx₁ _ => ?_)
    (by norm_num) o1 o2).trans o3
  have e' : ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + x = 4 + x := by push_cast; ring
  have e'' : ((2 : ℕ) : ℝ) + x = 2 + x := by push_cast; ring
  rw [e', e'']
  exact hp2Phase_bridge_two hx₁

/-- **L4(c): the bridge on cell `j` at depth `3`** (block `3`): for `h ∈ {h₁, h₂}` the bridge's
second moment under the two-fold tilt is at most `hp2BridgeX3 j²`. -/
theorem hp2CellBridge_three_le (hX : IsRademacherPrimeValues X μ) {k r y n₀ j : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hj : j < 40) (hcell : IsHP2UCell k 3 j h₁ h₂)
    (hn₀ : 3 ≤ n₀) (hr : hp2PostStart 3 + n₀ ≤ r) (hhh : h = h₁ ∨ h = h₂) :
    ∑ i ∈ Finset.range (hp2PostStart 3 - 3), pairVarH X μ y k σ h₁ h₂ h (i + 3)
        + (∑ i ∈ Finset.range (hp2PostStart 3 - 3),
          (pairMeanH X μ y k σ h₁ h₂ h (i + 3) - windowMeanH X μ y k σ h (i + 3))) ^ 2
      ≤ hp2BridgeX3 j ^ 2 := by
  have hb : hp2PostStart 3 = 3 + 1 := by decide
  obtain ⟨hD0, hξ₁, hξ₂⟩ := hcell.xi_mem
  have hD2 := abs_le_two_exp_neg_twenty_of_depth hk (hcell.depth hj).2
  obtain ⟨o1, o2, o3⟩ := hp2BridgeNumerals3_ok hj
  have hD := hp2CellBridge1_spec hj hξ₁ hξ₂
  have e : ((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)
      = 1 + (((3 : ℕ) : ℝ) + (Real.log |h₁ - h₂| + k)) := by push_cast; ring
  refine (bridge_moment_le_of_cell hX hk hh₁ hh₂ hσ hσr hyr hb (by omega) hhh hD0 hD2
    (lo := hp2CellBridge1Lo j) (hi := hp2CellBridge1Hi j) (Slo := -0.09286) (Shi := 0.09286)
    (V := 0.54669) (M := hp2BridgeM3 j) (by rw [e]; exact hD) (fun x hx₁ _ => ?_)
    (by norm_num) o1 o2).trans o3
  have e' : ((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) + x = 4 + x := by push_cast; ring
  have e'' : ((3 : ℕ) : ℝ) + x = 3 + x := by push_cast; ring
  rw [e', e'']
  exact hp2Phase_bridge_three hx₁

end CellBridge

end RMF
