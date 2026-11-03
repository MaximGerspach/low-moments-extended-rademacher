/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Chaining
import RMF.EulerProduct.JointLaplaceExplicit
import RMF.EulerProduct.JointLaplaceSharp

/-!
# Hamdan's Lemma B.2 with a sharp constant

`RMF.IsSteinhausRMF.exists_measure_exists_gt_le` proves Lemma B.2 with one parameter `Λ` bounding
both `V/A` and the window `rP`, the chain cut at `q₀ ≈ 24Λ²`, and the local constants summed over
every prime.  Here:

* the Laplace errors are summed over `p ≥ y₀` only, and are at most `1` once
  `y₀ ≥ RMF.chainSharpThreshold σ₀ Λ₁` (`RMF/EulerProduct/JointLaplaceSharp.lean`);
* `V ≤ Λ₁A` and `rP ≤ Λ₂` are separate, and `Λ₂ ≤ 1/288` makes every level `q ≥ 1` of the chain
  summable, so there is no bracket regime below a threshold;
* the cross term `λ₁V₂/2` is kept (it is `≤ Λ₁ q/8`) rather than absorbed, which is what forces
  `q₀ ≈ 24Λ²` in `RMF.IsSteinhausRMF.exists_measure_exists_gt_le`.

The constant is `RMF.chainSharpConst Λ₁ Λ₂ = e^{1+2Λ₁} + e^{Λ₁} + e·8e^{2Λ'}e^{(2Λ')²·48Λ₂}/(1 -
e^{-1/(192Λ₂)})`, `Λ' = 17Λ₁/16`.
-/

open Finset MeasureTheory

namespace RMF

/-! ### One link of the chain, and the base point, above a threshold -/

/-- **One link of the chain above a threshold**: `RMF.IsSteinhausRMF.exists_measure_link_le` with
its constant replaced by the tail `pairTailConst σ₀ Λ · y₀^{-3(σ₁-1/3)/2}`,
`σ₁ = (σ₀+1/3)/2`. -/
theorem IsSteinhausRMF.measure_link_le_tail {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) {l₁ σ V₁ V₂ D h₁ h₂ : ℝ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ)
    {E : Set Ω} (hl₁ : 0 ≤ l₁) (hl₁Λ : l₁ ≤ Λ) (hσ : σ₀ ≤ σ) (hD : |h₁ - h₂| ≤ D)
    (hV₂ : 0 ≤ V₂) (hD0 : 0 < D)
    (hP₁ : 0 < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
    (hV₂P : V₂ / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ)
    (hE : MeasurableSet E)
    (hE₁ : ∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ 0) ω‖)
    (hE₂ : ∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₁) ω‖
        - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₂) ω‖) :
    μ.real E ≤ Real.exp (l₁ ^ 2 / 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
      - l₁ * V₁ + l₁ * V₂ / 2
      - V₂ ^ 2 / (2 * (D * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p))
      + pairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))) := by
  haveI := hf.isProbabilityMeasure
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ,
      P = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  rw [← hPdef] at hP₁ hV₂P
  rw [← hAdef, ← hPdef]
  set T := pairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) with hTdef
  have hB : (0 : ℝ) < D * P := by positivity
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂ : ℝ, l₂ = V₂ / (D * P) := ⟨_, rfl⟩
  have hl₂ : (0 : ℝ) ≤ l₂ := by rw [hl₂def]; positivity
  have hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ := by
    have h1 : l₂ * |h₁ - h₂| ≤ l₂ * D := mul_le_mul_of_nonneg_left hD hl₂
    have h2 : l₂ * D = V₂ / P := by rw [hl₂def]; field_simp
    linarith [h2 ▸ h1]
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissa σ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissa_re]
    linarith
  have hq : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      |pairWeight l₁ l₂ a| ≤ l₁ / 2 + l₂ / 2 := fun a _ => abs_pairWeight_le hl₁ hl₂ a
  have hIpos := hf.integral_prod_norm_pair_pos hσ₀ l₁ l₂ σ h₁ h₂ y₀ y hl₁ hl₂ hσ
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow y₀ y Finset.univ hre] at hIpos
  have htail := pair_prime_sum_tail_le hσ₀ hΛ hy₀ y hl₁ hl₂ hσ hl₁Λ hl₂Λ
    (h₁ := h₁) (h₂ := h₂)
  rw [← hTdef] at htail
  have hmain := sum_norm_sum_pairWeight_cpow_le (σ := σ) (h₁ := h₁) (h₂ := h₂) hl₁ hl₂ y₀ y
  rw [← hAdef, ← hPdef] at hmain
  have hlog := (abs_le.1 htail).2
  have h := hf.measure_le_exp_of_log_le hq (by positivity) hre hIpos
    (B := l₁ ^ 2 / 4 * A + (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂| * P + T)
    (W := l₁ * V₁ + l₂ * V₂) (by linarith) hE (fun ω hω => by
      rw [sum_two_mul_pairWeight_mul]
      have hA' : l₁ * V₁
          ≤ l₁ * Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ 0) ω‖ := by
        rw [pairAbscissa_zero_eq σ h₁ h₂]
        exact mul_le_mul_of_nonneg_left (hE₁ ω hω) hl₁
      have hB' : l₂ * V₂
          ≤ l₂ * (Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ 1) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (pairAbscissa σ h₁ h₂ 2) ω‖) := by
        rw [pairAbscissa_one_eq σ h₁ h₂, pairAbscissa_two_eq σ h₁ h₂]
        exact mul_le_mul_of_nonneg_left (hE₂ ω hω) hl₂
      linarith)
  refine le_trans h (Real.exp_le_exp.2 ?_)
  have hcross : (l₁ * l₂ + l₂ ^ 2) / 2 * |h₁ - h₂| * P ≤ (l₁ * l₂ + l₂ ^ 2) / 2 * (D * P) := by
    have hnn : (0 : ℝ) ≤ (l₁ * l₂ + l₂ ^ 2) / 2 := by positivity
    have h1 : |h₁ - h₂| * P ≤ D * P := mul_le_mul_of_nonneg_right hD hP₁.le
    nlinarith
  have hexpand : (l₁ * l₂ + l₂ ^ 2) / 2 * (D * P) = l₁ * V₂ / 2 + V₂ ^ 2 / (2 * (D * P)) := by
    rw [hl₂def]
    field_simp
  have hl₂V : l₂ * V₂ = V₂ ^ 2 / (D * P) := by
    rw [hl₂def]
    field_simp
  have hsplit : V₂ ^ 2 / (D * P) = 2 * (V₂ ^ 2 / (2 * (D * P))) := by
    field_simp
  linarith [hexpand ▸ hcross]

/-- The base-point constant of the sharp chain, `e^{1+2Λ₁} + e^{Λ₁}`. -/
noncomputable def chainSharpBase (Λ₁ : ℝ) : ℝ := Real.exp (1 + 2 * Λ₁) + Real.exp Λ₁

/-- **The base point above a threshold.**  `P(E) ≤ (e^{1+2Λ₁} + e^{Λ₁}) e^{-V²/A}` on any event
where `log‖F(s)‖ ≥ V - 1`, for `0 ≤ V ≤ Λ₁A`, once the one-point tail error is at most `1`. -/
theorem IsSteinhausRMF.measure_base_le_tail {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {σ₀ Λ₁ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 0 ≤ Λ₁) {σ V : ℝ} {s : ℂ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ)
    (hT : multiTailConst Λ₁ σ₀ 1 * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2)) ≤ 1) {E : Set Ω}
    (hs : s.re = σ) (hσ : σ₀ ≤ σ) (hV : 0 ≤ V)
    (hA : 0 < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hVΛ : V ≤ Λ₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) (hE : MeasurableSet E)
    (hEV : ∀ ω ∈ E, V - 1 ≤ Real.log ‖randomEulerProductIco f y₀ y s ω‖) :
    μ.real E
      ≤ chainSharpBase Λ₁ * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  haveI := hf.isProbabilityMeasure
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  rw [← hAdef] at hA hVΛ ⊢
  have hexp0 : (0 : ℝ) < Real.exp (-(V ^ 2 / A)) := Real.exp_pos _
  have hB1 : (0 : ℝ) < Real.exp (1 + 2 * Λ₁) := Real.exp_pos _
  have hB2 : (0 : ℝ) < Real.exp Λ₁ := Real.exp_pos _
  rw [chainSharpBase]
  rcases le_or_gt 0 (V - 1) with hpos | hneg
  · have hkey := sq_div_sub_lower hA zero_le_one hVΛ
    have h := hf.measure_ge_le_gaussian_tail hσ₀ hΛ₁ hy₀ y hpos hs hσ (hAdef ▸ hA)
      (by rw [← hAdef]; linarith) hE hEV
    rw [← hAdef] at h
    refine le_trans h ?_
    have hstep : Real.exp (multiTailConst Λ₁ σ₀ 1 * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2))
        - (V - 1) ^ 2 / A) ≤ Real.exp (1 + 2 * Λ₁) * Real.exp (-(V ^ 2 / A)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    nlinarith
  · have hVA : V ^ 2 / A ≤ Λ₁ := by
      rw [div_le_iff₀ hA]
      nlinarith
    have hone : μ.real E ≤ 1 := by
      have h := measureReal_mono (μ := μ) (Set.subset_univ E) (measure_ne_top μ _)
      rwa [probReal_univ] at h
    have hstep : (1 : ℝ) ≤ Real.exp Λ₁ * Real.exp (-(V ^ 2 / A)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    nlinarith

/-! ### The constants -/

/-- **The threshold on the first prime**: past it both Laplace tails are at most `1`. -/
noncomputable def chainSharpThreshold (σ₀ Λ₁ : ℝ) : ℝ :=
  max 2 (max (multiTailConst Λ₁ σ₀ 1 ^ (3 * ((σ₀ - 1 / 3) / 2))⁻¹)
    (pairTailConst σ₀ (2 * Λ₁) ^ (3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))⁻¹))

lemma multiTail_le_one_of_chainSharpThreshold_le {σ₀ Λ₁ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 0 ≤ Λ₁)
    {y₀ : ℕ} (hy₀ : chainSharpThreshold σ₀ Λ₁ ≤ y₀) :
    multiTailConst Λ₁ σ₀ 1 * (y₀ : ℝ) ^ (-3 * ((σ₀ - 1 / 3) / 2)) ≤ 1 := by
  have hC : 0 ≤ multiTailConst Λ₁ σ₀ 1 := by
    simpa using multiTailConst_nonneg ({0} : Finset ℕ) hΛ₁ hσ₀
  have h := mul_rpow_neg_le_one_of_le hC (by linarith : (0 : ℝ) < 3 * ((σ₀ - 1 / 3) / 2))
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy₀)
  rwa [show -(3 * ((σ₀ - 1 / 3) / 2)) = -3 * ((σ₀ - 1 / 3) / 2) by ring] at h

lemma pairTail_le_one_of_chainSharpThreshold_le {σ₀ Λ₁ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 0 ≤ Λ₁)
    {y₀ : ℕ} (hy₀ : chainSharpThreshold σ₀ Λ₁ ≤ y₀) :
    pairTailConst σ₀ (2 * Λ₁) * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) ≤ 1 := by
  have hC : 0 ≤ pairTailConst σ₀ (2 * Λ₁) := pairTailConst_nonneg hσ₀ (by linarith)
  have h := mul_rpow_neg_le_one_of_le hC
    (by linarith : (0 : ℝ) < 3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy₀)
  rwa [show -(3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) = -3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2) by
    ring] at h

lemma two_le_chainSharpThreshold (σ₀ Λ₁ : ℝ) : 2 ≤ chainSharpThreshold σ₀ Λ₁ := le_max_left _ _

/-- The chaining sum of the sharp chain, `8e^{2Λ'}·e^{(2Λ')²/(2c)}/(1 - e^{-c/2})` with
`Λ' = 17Λ₁/16` and `c = 1/(96Λ₂)`. -/
noncomputable def chainSharpSum (Λ₁ Λ₂ : ℝ) : ℝ :=
  8 * Real.exp (2 * (17 * Λ₁ / 16))
    * (Real.exp ((2 * (17 * Λ₁ / 16)) ^ 2 / (2 * (1 / (96 * Λ₂))))
      * (1 - Real.exp (-(1 / (96 * Λ₂) / 2)))⁻¹)

/-- **The constant of the sharp Lemma B.2**, `chainSharpBase Λ₁ + e·chainSharpSum Λ₁ Λ₂`. -/
noncomputable def chainSharpConst (Λ₁ Λ₂ : ℝ) : ℝ :=
  chainSharpBase Λ₁ + Real.exp 1 * chainSharpSum Λ₁ Λ₂

lemma chainSharpSum_pos {Λ₁ Λ₂ : ℝ} (hΛ₂ : 0 < Λ₂) : 0 < chainSharpSum Λ₁ Λ₂ := by
  have h1 : Real.exp (-(1 / (96 * Λ₂) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < 1 / (96 * Λ₂) / 2 := by positivity
    linarith
  have h2 : (0 : ℝ) < 1 - Real.exp (-(1 / (96 * Λ₂) / 2)) := by linarith
  rw [chainSharpSum]
  positivity

lemma chainSharpConst_pos {Λ₁ Λ₂ : ℝ} (hΛ₂ : 0 < Λ₂) : 0 < chainSharpConst Λ₁ Λ₂ := by
  have := chainSharpSum_pos (Λ₁ := Λ₁) hΛ₂
  rw [chainSharpConst, chainSharpBase]
  positivity

/-! ### Lemma B.2 -/

set_option maxHeartbeats 400000 in
-- the assembly of the chain: the same size as `RMF.IsSteinhausRMF.exists_measure_exists_gt_le`
/-- **Hamdan's Lemma B.2, sharp.**  For `σ₀ ≤ σ`, `0 ≤ V ≤ Λ₁A`, `1 ≤ A`, `rP ≤ Λ₂ ≤ 1/288` and
`y₀ ≥ chainSharpThreshold σ₀ Λ₁`:

`P(∃h ∈ [0,r) : log‖F(σ+ih)‖ > V) ≤ chainSharpConst Λ₁ Λ₂ · exp(-V²/A)`,

with `A = ∑_{y₀ ≤ p < y} p^{-2σ}` and `P = ∑_{y₀ ≤ p < y} p^{-2σ} log p`. -/
theorem IsSteinhausRMF.measure_exists_gt_le_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {σ₀ Λ₁ Λ₂ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 1 ≤ Λ₁) (hΛ₂ : 0 < Λ₂) (hΛ₂288 : 288 * Λ₂ ≤ 1)
    {σ V r : ℝ} {y₀ : ℕ} (hy₀ : chainSharpThreshold σ₀ Λ₁ ≤ y₀) (y : ℕ) (hσ : σ₀ ≤ σ)
    (hr : 0 < r) (hV : 0 ≤ V)
    (hA1 : 1 ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hVΛ : V ≤ Λ₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hrP : r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico 0 r,
        V < Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
      ≤ chainSharpConst Λ₁ Λ₂
        * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  have hΛ₁0 : (0 : ℝ) < Λ₁ := by linarith
  have hy₀2 : (2 : ℝ) ≤ (y₀ : ℝ) := le_trans (two_le_chainSharpThreshold σ₀ Λ₁) hy₀
  have hy₀1 : 1 ≤ y₀ := by exact_mod_cast (show (1 : ℝ) ≤ (y₀ : ℝ) by linarith)
  have hTm := multiTail_le_one_of_chainSharpThreshold_le hσ₀ hΛ₁0.le hy₀
  have hTp := pairTail_le_one_of_chainSharpThreshold_le hσ₀ hΛ₁0.le hy₀
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (96 * Λ₂) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hc3 : (3 : ℝ) ≤ c := by
    rw [hcdef, le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨Λ', hΛ'def⟩ : ∃ Λ' : ℝ, Λ' = 17 * Λ₁ / 16 := ⟨_, rfl⟩
  obtain ⟨Csum, hCsumdef⟩ : ∃ Csum : ℝ, Csum = 8 * Real.exp (2 * Λ')
      * (Real.exp ((2 * Λ') ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹) := ⟨_, rfl⟩
  have hW : chainSharpConst Λ₁ Λ₂ = chainSharpBase Λ₁ + Real.exp 1 * Csum := by
    unfold chainSharpConst chainSharpSum
    rw [show (1 : ℝ) / (96 * Λ₂) = c from hcdef.symm, ← hΛ'def, ← hCsumdef]
  rw [hW]
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hf.isProbabilityMeasure
  have hA : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := by linarith
  have hP : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
    have h := log_two_mul_sum_le_sum_mul_log σ y₀ y
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- the unimodularity set, on which the walk *is* the Euler product's logarithm
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    have hrw : {ω : Ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1}
        = ⋂ p ∈ primesIco y₀ y, {ω : Ω | ‖X p ω‖ ≤ 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hGdef, hrw]
    exact (primesIco y₀ y).measurableSet_biInter fun p hp =>
      measurableSet_le ((hX.measurable p (prime_of_mem_primesIco hp)).norm)
        measurable_const
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → Ω → ℝ, S = fun t ω =>
      ∑ p ∈ primesIco y₀ y, localLog ((p : ℂ) ^ (-(heightLine σ t))) (X p ω) := ⟨_, rfl⟩
  have hSmeas : ∀ t : ℝ, Measurable (S t) := by
    intro t
    simp only [hSdef]
    exact Finset.measurable_sum _ fun p hp =>
      (measurable_localLog _).comp (hX.measurable p (prime_of_mem_primesIco hp))
  have hSeq : ∀ (t : ℝ) (ω : Ω), ω ∈ G →
      S t ω = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
        (heightLine σ t) ω‖ := by
    intro t ω hω
    rw [hGdef] at hω
    simp only [hSdef]
    exact (log_norm_randomEulerProductIco_eq (by rw [re_heightLine]; exact hσ0) hω).symm
  -- the Lipschitz bound, and the level at which the chain is cut
  obtain ⟨Lip, hLipdef⟩ : ∃ Lip : ℝ, Lip = (1 - (2 : ℝ) ^ (-σ))⁻¹
      * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) * Real.log p := ⟨_, rfl⟩
  have hθ : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hLip0 : (0 : ℝ) ≤ Lip := by
    have h1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by linarith
    have h2 : (0 : ℝ) ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) * Real.log p := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpp := prime_of_mem_primesIco hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
      have hl := Real.log_nonneg hp1
      have hr0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
      positivity
    rw [hLipdef]
    positivity
  have hLip : ∀ ω ∈ G, ∀ u v : ℝ, |S u ω - S v ω| ≤ Lip * |u - v| := by
    intro ω hω u v
    rw [hGdef] at hω
    have h := abs_sum_localLog_sub_le (B := primesIco y₀ y)
      (fun p hp => prime_of_mem_primesIco hp) hω
      (re_heightLine σ u) (re_heightLine σ v) hσ0
    rw [im_heightLine, im_heightLine] at h
    simp only [hSdef]
    rw [hLipdef]
    exact h
  obtain ⟨L, hL⟩ := exists_level_le (Lip := Lip) hr (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌈V⌉₊ + 2 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; omega
  have hQge : V + 2 ≤ (Q : ℝ) := by
    rw [hQdef]
    push_cast
    have := Nat.le_ceil V
    linarith
  -- the target, moved onto the unimodularity set and expressed through the walk
  have htarget : μ.real {ω | ∃ h ∈ Set.Ico 0 r,
      V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
        (heightLine σ h) ω‖} = μ.real (G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω}) := by
    have hset : G ∩ {ω | ∃ h ∈ Set.Ico 0 r,
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖} = G ∩ {ω | ∃ h ∈ Set.Ico 0 r, V < S h ω} := by
      ext ω
      constructor
      · rintro ⟨hωG, h, hh, hlt⟩
        exact ⟨hωG, h, hh, by rw [hSeq h ω hωG]; exact hlt⟩
      · rintro ⟨hωG, h, hh, hlt⟩
        exact ⟨hωG, h, hh, by rw [← hSeq h ω hωG]; exact hlt⟩
    unfold MeasureTheory.Measure.real
    rw [measure_eq_measure_inter_of_compl_null hGnull, hset]
  rw [htarget]
  refine le_trans (measureReal_inter_exists_gt_le (μ := μ) (S := S) (G := G) (V := V)
    hr hQ1 hLip0 hLip hL) ?_
  -- the base point of the whole event
  have hbase0 : μ.real (G ∩ {ω | V - 1 < S 0 ω})
      ≤ chainSharpBase Λ₁ * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
    refine hf.measure_base_le_tail hσ₀ hΛ₁0.le hy₀1 y hTm (re_heightLine σ 0) hσ hV hA hVΛ
      (hGmeas.inter (measurableSet_lt measurable_const (hSmeas 0))) ?_
    rintro ω ⟨hωG, hlt⟩
    simp only [Set.mem_setOf_eq] at hlt
    rw [← hSeq 0 ω hωG]
    linarith
  -- abbreviations for the two prime sums
  obtain ⟨AA, hAAdef⟩ : ∃ AA : ℝ, AA = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨PP, hPPdef⟩ : ∃ PP : ℝ,
      PP = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  have hPlow : Real.log 2 * AA ≤ PP := by
    rw [hAAdef, hPPdef]
    exact log_two_mul_sum_le_sum_mul_log σ y₀ y
  rw [← hAAdef] at hA hA1 hVΛ hbase0 ⊢
  rw [← hPPdef] at hP hrP
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hVA : V ^ 2 / AA ≤ Λ₁ * V := by
    rw [div_le_iff₀ hA]
    nlinarith
  have hQupper : (Q : ℝ) ≤ V + 3 := by
    rw [hQdef]
    push_cast
    have := Nat.ceil_lt_add_one hV
    linarith
  -- one link of the chain, at every level
  have hterm : ∀ q ℓ i : ℕ, 1 ≤ q → q ≤ Q → ∀ E : Set Ω, MeasurableSet E → E ⊆ G →
      (∀ ω ∈ E, q < Q → V - q - 1 < S 0 ω) →
      (∀ ω ∈ E, (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
        ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
          - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω) →
      μ.real E ≤ Real.exp 1
        * Real.exp (-(V ^ 2 / AA) + 2 * Λ' * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro q ℓ i hq1 hqQ' E hEmeas hEG hE1 hE2
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ'
    have hp4 : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
    have hgap : |(i : ℝ) * (r / 4 ^ (ℓ + 1)) - ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))|
        ≤ 3 * r / 4 ^ (ℓ + 1) := by
      have hdm : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
      have hcast : (i : ℝ) - ((4 * (i / 4) : ℕ) : ℝ) = ((i % 4 : ℕ) : ℝ) := by
        have h := congrArg (fun n : ℕ => (n : ℝ)) hdm
        push_cast at h ⊢
        linarith
      have hmod3 : ((i % 4 : ℕ) : ℝ) ≤ 3 := by
        have h : i % 4 ≤ 3 := by omega
        exact_mod_cast h
      have hr4 : (0 : ℝ) < r / 4 ^ (ℓ + 1) := by positivity
      rw [← sub_mul, hcast, abs_of_nonneg (by positivity),
        show 3 * r / 4 ^ (ℓ + 1) = 3 * (r / 4 ^ (ℓ + 1)) by ring]
      exact mul_le_mul_of_nonneg_right hmod3 hr4.le
    have hD0 : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) := by positivity
    have hw1 : ((3 : ℝ) / 4) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hV2ge : (0 : ℝ) ≤ (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) := by positivity
    have hV2small : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) ≤ (q : ℝ) / 8 := by
      linarith [mul_le_mul_of_nonneg_left hw1 hq0R]
    have hV2P : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) / PP ≤ 2 * Λ₁ := by
      rw [div_le_iff₀ hP]
      have h1 : (Q : ℝ) ≤ 4 * Λ₁ * AA := by
        have hz := mul_le_mul_of_nonneg_left hA1 (by linarith : (0 : ℝ) ≤ 3 * Λ₁)
        linarith only [hQupper, hVΛ, hz, hΛ₁]
      have h2 : 2 * Λ₁ * (Real.log 2 * AA) ≤ 2 * Λ₁ * PP :=
        mul_le_mul_of_nonneg_left hPlow (by linarith)
      have h3 : 4 * Λ₁ * AA / 8 ≤ 2 * Λ₁ * (Real.log 2 * AA) := by
        have hΛA : (0 : ℝ) ≤ Λ₁ * AA := by positivity
        have hz := mul_le_mul_of_nonneg_left hlog2.le
          (show (0 : ℝ) ≤ 2 * Λ₁ * AA by positivity)
        linarith only [hz, hΛA]
      linarith only [hV2small, hqQR, h1, h2, h3]
    have hnum := two_mul_le_sq_div_two_mul hr hP hΛ₂ hrP q ℓ
    have hcnum : c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ
        ≤ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2 / (2 * (3 * r / 4 ^ (ℓ + 1) * PP)) := by
      have hc2 : c = 2 * (1 / (192 * Λ₂)) := by
        rw [hcdef]
        field_simp
        ring
      rw [hc2]
      exact hnum
    have hΛ'q : 2 * Λ₁ * ((q : ℝ) + 1) + Λ₁ * ((q : ℝ) / 8) ≤ 2 * Λ' * ((q : ℝ) + 1) := by
      rw [hΛ'def]
      linarith only [hΛ₁0]
    rcases le_or_gt 0 (V - (q : ℝ) - 1) with hpos | hneg
    · have hqQ : q < Q := by
        have h1 : (q : ℝ) < (Q : ℝ) := by linarith
        exact_mod_cast h1
      have hl1 : (0 : ℝ) ≤ 2 * (V - (q : ℝ) - 1) / AA := by positivity
      have hl1two : 2 * (V - (q : ℝ) - 1) / AA ≤ 2 * Λ₁ := by
        rw [div_le_iff₀ hA]
        linarith only [hVΛ, hq0R]
      have hshift := sq_div_sub_lower (A := AA) (V := V) (u := (q : ℝ) + 1) (Λ := Λ₁)
        hA (by positivity) hVΛ
      have hsq : (2 * (V - (q : ℝ) - 1) / AA) ^ 2 / 4 * AA
          - 2 * (V - (q : ℝ) - 1) / AA * (V - (q : ℝ) - 1)
          = -((V - ((q : ℝ) + 1)) ^ 2 / AA) := by
        field_simp
        ring
      have hcrossV : 2 * (V - (q : ℝ) - 1) / AA * ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) / 2
          ≤ Λ₁ * ((q : ℝ) / 8) := by
        have hhalf : (V - (q : ℝ) - 1) / AA ≤ Λ₁ := by
          rw [div_le_iff₀ hA]
          linarith only [hVΛ, hq0R]
        have hhalf0 : 0 ≤ (V - (q : ℝ) - 1) / AA := by positivity
        have hre : 2 * (V - (q : ℝ) - 1) / AA * ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) / 2
            = (V - (q : ℝ) - 1) / AA * ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) := by ring
        rw [hre]
        exact mul_le_mul hhalf hV2small hV2ge hΛ₁0.le
      have h := hf.measure_link_le_tail hσ₀ (by linarith : (0 : ℝ) ≤ 2 * Λ₁) hy₀1 y
        (l₁ := 2 * (V - (q : ℝ) - 1) / AA) (V₁ := V - (q : ℝ) - 1)
        (V₂ := (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) (D := 3 * r / 4 ^ (ℓ + 1))
        (h₁ := (i : ℝ) * (r / 4 ^ (ℓ + 1))) (h₂ := ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)))
        hl1 hl1two hσ hgap hV2ge hD0 (hPPdef ▸ hP) (hPPdef ▸ hV2P) hEmeas
        (fun ω hω => by
          rw [← hSeq 0 ω (hEG hω)]
          exact le_of_lt (hE1 ω hω hqQ))
        (fun ω hω => by
          rw [← hSeq _ ω (hEG hω), ← hSeq _ ω (hEG hω)]
          exact hE2 ω hω)
      rw [← hAAdef, ← hPPdef] at h
      refine le_trans h ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith only [hsq, hshift, hcrossV, hcnum, hΛ'q, hTp]
    · obtain ⟨V₁, hV₁def⟩ : ∃ V₁ : ℝ, V₁ = -∑ p ∈ primesIco y₀ y,
          Real.log (1 + ((p : ℕ) : ℝ) ^ (-(heightLine σ 0).re)) := ⟨_, rfl⟩
      have hE1' : ∀ ω ∈ E, V₁
            ≤ Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
              (heightLine σ 0) ω‖ := by
        intro ω hω
        have hωG : ω ∈ G := hEG hω
        rw [hGdef] at hωG
        rw [hV₁def]
        exact le_log_norm_randomEulerProductIco (by rw [re_heightLine]; exact hσ0) hωG
      have hΛq : (0 : ℝ) ≤ Λ₁ * ((q : ℝ) + 1) := by positivity
      have hΛV : Λ₁ * V ≤ Λ₁ * ((q : ℝ) + 1) := by
        have hz := mul_pos hΛ₁0 (show (0 : ℝ) < (q : ℝ) + 1 - V by linarith only [hneg])
        linarith only [hz]
      have hΛ'Λ : Λ₁ * ((q : ℝ) + 1) ≤ 2 * Λ' * ((q : ℝ) + 1) := by
        have hΛq0 := mul_nonneg hΛ₁0.le hq0R
        rw [hΛ'def]
        linarith only [hΛq0, hΛ₁0]
      have h := hf.measure_link_le_tail hσ₀ (by linarith : (0 : ℝ) ≤ 2 * Λ₁) hy₀1 y
        (l₁ := 0) (V₁ := V₁)
        (V₂ := (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) (D := 3 * r / 4 ^ (ℓ + 1))
        (h₁ := (i : ℝ) * (r / 4 ^ (ℓ + 1))) (h₂ := ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)))
        le_rfl (by linarith) hσ hgap hV2ge hD0 (hPPdef ▸ hP) (hPPdef ▸ hV2P) hEmeas hE1'
        (fun ω hω => by
          rw [← hSeq _ ω (hEG hω), ← hSeq _ ω (hEG hω)]
          exact hE2 ω hω)
      rw [← hAAdef, ← hPPdef] at h
      refine le_trans h ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith only [hcnum, hVA, hΛV, hΛq, hΛ'Λ, hTp]
  -- every level of the chain
  have hbig : ∀ q ∈ Finset.Icc 1 Q,
      μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Real.exp 1 * ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1)
          * Real.exp (-(V ^ 2 / AA) + 2 * Λ' * ((q : ℝ) + 1)
            - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
    have hqQ' : q ≤ Q := (Finset.mem_Icc.1 hq).2
    have hbrmeas : MeasurableSet
        {ω : Ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q} := by
      by_cases hqQ : q < Q
      · have hrw : {ω : Ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
            = {ω : Ω | V - q - 1 < S 0 ω} ∩ {ω : Ω | S 0 ω ≤ V - q} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
          exact ⟨fun h => ⟨h.1 hqQ, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩
        rw [hrw]
        exact (measurableSet_lt measurable_const (hSmeas 0)).inter
          (measurableSet_le (hSmeas 0) measurable_const)
      · have hrw : {ω : Ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
            = {ω : Ω | S 0 ω ≤ V - q} := by
          ext ω
          simp only [Set.mem_setOf_eq]
          exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hqQ, h⟩⟩
        rw [hrw]
        exact measurableSet_le (hSmeas 0) measurable_const
    rw [Finset.mul_sum]
    refine le_trans (measureReal_biUnion_finset_le _ _) (Finset.sum_le_sum fun ℓ _ => ?_)
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    have hb : ∀ i ∈ Finset.range (4 ^ (ℓ + 1)),
        μ.real (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})
        ≤ Real.exp 1 * Real.exp (-(V ^ 2 / AA) + 2 * Λ' * ((q : ℝ) + 1)
            - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
      intro i _
      refine hterm q ℓ i hq1 hqQ' _
        ((hGmeas.inter hbrmeas).inter
          (measurableSet_le measurable_const ((hSmeas _).sub (hSmeas _))))
        (fun ω hω => hω.1.1) (fun ω hω hlt => hω.1.2.1 hlt) (fun ω hω => hω.2)
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_of_eq (by ring)
  have hsum := Finset.sum_le_sum hbig
  rw [← Finset.mul_sum] at hsum
  have hT : ∀ q ∈ Finset.Icc 1 Q, 3 ≤ c * (q : ℝ) ^ 2 := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hq).1
    have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hq1
    calc (3 : ℝ) ≤ c := hc3
      _ = c * 1 := (mul_one c).symm
      _ ≤ c * (q : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hq2 hc.le
  have hchain := sum_chaining_le (W := V ^ 2 / AA) (Λ := Λ') (c := c) hc (Finset.Icc 1 Q) hT L
  rw [← hCsumdef] at hchain
  have hfin := mul_le_mul_of_nonneg_left hchain (Real.exp_pos 1).le
  have hbase1 : chainSharpBase Λ₁ * Real.exp (-(V ^ 2 / AA))
      + Real.exp 1 * (Csum * Real.exp (-(V ^ 2 / AA)))
      = (chainSharpBase Λ₁ + Real.exp 1 * Csum) * Real.exp (-(V ^ 2 / AA)) := by ring
  linarith only [hbase0, hsum, hfin, hbase1]

/-- **The sharp Lemma B.2 on any interval** `[h₀, h₀ + r)`: rotate the values by `p^{-ih₀}`. -/
theorem IsSteinhausRMF.measure_exists_gt_le_shift_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {σ₀ Λ₁ Λ₂ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 1 ≤ Λ₁) (hΛ₂ : 0 < Λ₂) (hΛ₂288 : 288 * Λ₂ ≤ 1)
    {σ V r h₀ : ℝ} {y₀ : ℕ} (hy₀ : chainSharpThreshold σ₀ Λ₁ ≤ y₀) (y : ℕ) (hσ : σ₀ ≤ σ)
    (hr : 0 < r) (hV : 0 ≤ V)
    (hA1 : 1 ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hVΛ : V ≤ Λ₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hrP : r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
      ≤ chainSharpConst Λ₁ Λ₂
        * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hX' := hX.mul_unimodular (c := fun p : ℕ => (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)))
    (fun p hp => norm_cpow_neg_mul_I hp h₀)
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hset : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖}
      = G ∩ {ω | ∃ u ∈ Set.Ico (0 : ℝ) r,
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
          (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * X p ω) y₀ y (heightLine σ u) ω‖} := by
    ext ω
    constructor
    · rintro ⟨hωG, h, hh, hlt⟩
      have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
      refine ⟨hωG, h - h₀, ?_, ?_⟩
      · simp only [Set.mem_Ico] at hh ⊢
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      · rw [log_norm_randomEulerProductIco_rotate hσ0 hωu, show h₀ + (h - h₀) = h from by ring]
        exact hlt
    · rintro ⟨hωG, u, hu, hlt⟩
      have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
      refine ⟨hωG, h₀ + u, ?_, ?_⟩
      · simp only [Set.mem_Ico] at hu ⊢
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · rw [← log_norm_randomEulerProductIco_rotate hσ0 hωu]
        exact hlt
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖}
      = μ.real {ω | ∃ u ∈ Set.Ico (0 : ℝ) r,
          V < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (p : ℂ) ^ (-((h₀ : ℂ) * Complex.I)) * X p ω) y₀ y (heightLine σ u) ω‖} := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _, hset,
          ← measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ chainSharpConst Λ₁ Λ₂ * Real.exp (-(V ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) :=
        hX'.isSteinhausRMF.measure_exists_gt_le_sharp hσ₀ hΛ₁ hΛ₂ hΛ₂288 hy₀ y hσ hr hV hA1
          hVΛ hrP

/-- **The sharp Lemma B.2 for the lower tail**, on any interval: the event
`W + 4A < -log‖F(σ+ih)‖` for some `h ∈ [h₀, h₀ + r)`. -/
theorem IsSteinhausRMF.measure_exists_lt_le_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ)
    {σ₀ Λ₁ Λ₂ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 1 ≤ Λ₁) (hΛ₂ : 0 < Λ₂) (hΛ₂288 : 288 * Λ₂ ≤ 1)
    {σ W r h₀ : ℝ} {y₀ : ℕ} (hy₀ : chainSharpThreshold σ₀ Λ₁ ≤ y₀) (y : ℕ) (hσ : σ₀ ≤ σ)
    (hr : 0 < r) (hW : 0 ≤ W)
    (hA1 : 1 ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hWΛ : W ≤ Λ₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hrP : r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
      ≤ chainSharpConst Λ₁ Λ₂
        * Real.exp (-(W ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hσ13 : (1 : ℝ) / 3 ≤ σ := by linarith
  have hX' := hX.mul_unimodular (c := fun _ : ℕ => (-1 : ℂ))
    (fun _ _ => by rw [norm_neg, norm_one])
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hsub : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      ⊆ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} := by
    rintro ω ⟨hωG, h, hh, hlt⟩
    have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
    have hre : (heightLine σ h).re = σ := re_heightLine σ h
    have hrefl := neg_log_norm_randomEulerProductIco_le (X := X) (y := y)
      (s := heightLine σ h) (by rw [hre]; exact hσ13) hωu
    rw [hre] at hrefl
    exact ⟨h, hh, by linarith⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      = μ.real (G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            < -Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y
              (heightLine σ h) ω‖}) := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ chainSharpConst Λ₁ Λ₂ * Real.exp (-(W ^ 2 / ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))) :=
        hX'.isSteinhausRMF.measure_exists_gt_le_shift_sharp hσ₀ hΛ₁ hΛ₂ hΛ₂288 hy₀ y hσ hr hW
          hA1 hWΛ hrP

end RMF
