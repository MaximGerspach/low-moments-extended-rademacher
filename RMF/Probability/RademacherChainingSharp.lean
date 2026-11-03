/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherChaining
import RMF.EulerProduct.RademacherJointLaplaceSharp

/-!
# Lemma B.2 for the Rademacher RMF, with a sharp constant

The Rademacher twin of `RMF/Probability/ChainingSharp.lean`.
`RMF.IsRademacherRMF.exists_measure_exists_gt_le` proves
`P(∃h ∈ [h₀, h₀+r) : log‖F(σ+ih)‖ > V) ≤ C·exp(A - 2V)` with an existential
`C ≥ q₀e^{2(q₀+1)}`, `q₀ = ⌈48Λ² + 48Λ⌉`, in its one parameter `Λ`.  Here:

* the pair Laplace errors are summed over `p ≥ y₀` and are at most `1` past
  `RMF.radChainThreshold σ₀ Λ₁` (`RMF.rad_pair_prime_sum_tail_le_at`);
* `V ≤ Λ₁A` (only for the Laplace range of the links) and `rP ≤ Λ₂ ≤ 1/576` are separate; every
  level `q ≥ 1` of the chain is summed, with no bracket below a threshold;
* the links keep their linear terms (`3V₂/2 ≤ 3q/16`), so the chain's slope is `35/16` and its
  decay `V₂²/(4B) ≥ q²(9/4)^ℓ/(192Λ₂)`.

The base point is exact: the tilt is `2` and `E‖F‖² = ∏(1 + p^{-2σ}) ≤ e^A`
(`RMF.IsRademacherRMF.measure_ge_le_second_moment`), so no one-point threshold is needed, unlike
`RMF.chainSharpThreshold`.  The constant is `RMF.radChainConst Λ₂ = e² + e·radChainSum Λ₂`.
-/

open Finset MeasureTheory

namespace RMF

/-! ### The links above a threshold -/

/-- **One link of the chain at the second-moment tilt, above a threshold**:
`RMF.IsRademacherRMF.exists_measure_link_le_two` with the pair constant replaced by the tail
`radPairTailConst σ₀ Λ · y₀^{-3(σ₁-1/3)/2}`. -/
theorem IsRademacherRMF.measure_link_le_two_tail {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 2 ≤ Λ) {σ V₁ V₂ D h₀ h₁ h₂ : ℝ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ)
    {E : Set Ω} (hσ : σ₀ ≤ σ) (hD : |h₁ - h₂| ≤ D) (hV₂ : 0 ≤ V₂) (hD0 : 0 < D)
    (hP₁ : 0 < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
    (hV₂P : V₂ / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ)
    (hE : MeasurableSet E)
    (hE₁ : ∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖)
    (hE₂ : ∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₁) ω‖
        - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₂) ω‖) :
    μ.real E ≤ Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
      - 2 * V₁ + 3 * V₂ / 2
      - V₂ ^ 2 / (4 * (D * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p))
      + radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))) := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨Pr, hPdef⟩ : ∃ Pr : ℝ,
      Pr = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  rw [← hPdef] at hP₁ hV₂P
  rw [← hAdef, ← hPdef]
  set T := radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))
    with hTdef
  have hB : (0 : ℝ) < D * Pr := by positivity
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂ : ℝ, l₂ = V₂ / (2 * (D * Pr)) := ⟨_, rfl⟩
  have hl₂ : (0 : ℝ) ≤ l₂ := by rw [hl₂def]; positivity
  have hl₂D : l₂ * D = V₂ / (2 * Pr) := by
    rw [hl₂def]
    field_simp
  have hV₂half : V₂ / (2 * Pr) ≤ Λ := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Pr)]
    rw [div_le_iff₀ hP₁] at hV₂P
    linarith
  have hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ := by
    have h1 : l₂ * |h₁ - h₂| ≤ l₂ * D := mul_le_mul_of_nonneg_left hD hl₂
    rw [hl₂D] at h1
    linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have htail := rad_pair_prime_sum_tail_le_at hσ₀ (by linarith) (h₀ := h₀) hy₀ y
    (by norm_num : (0 : ℝ) ≤ 2) hl₂ hσ hΛ hl₂Λ
  rw [← hTdef] at htail
  have hmain := sum_pair_main_term_pairAbscissaAt_two_le (l₂ := l₂) (σ := σ) (h₀ := h₀)
    (h₁ := h₁) (h₂ := h₂) hl₂ y₀ y
  rw [← hAdef, ← hPdef] at hmain
  have hlog : Real.log (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
      ^ (2 * pairWeight 2 l₂ a) ∂μ) ≤ A + (3 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr + T := by
    rw [hf.integral_prod_norm_randomEulerProductIco_rpow_pair_at y₀ y 2 l₂ σ h₀ h₁ h₂ hσ0]
    linarith [(abs_le.1 htail).2]
  have h := hf.measure_le_exp_pair_at_of_log_le hσ₀ (by norm_num : (0 : ℝ) ≤ 2) hl₂ hσ hlog hE
    (W := 2 * V₁ + l₂ * V₂) (fun ω hω => by
      rw [pairAbscissaAt_zero_heightLine, pairAbscissaAt_one_heightLine,
        pairAbscissaAt_two_heightLine]
      have hA' := mul_le_mul_of_nonneg_left (hE₁ ω hω) (by norm_num : (0 : ℝ) ≤ 2)
      have hB' := mul_le_mul_of_nonneg_left (hE₂ ω hω) hl₂
      linarith)
  refine le_trans h (Real.exp_le_exp.2 ?_)
  have hnn : (0 : ℝ) ≤ 3 * l₂ + l₂ ^ 2 := by nlinarith [sq_nonneg l₂]
  have hcross : (3 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr ≤ (3 * l₂ + l₂ ^ 2) * (D * Pr) := by
    have h1 : |h₁ - h₂| * Pr ≤ D * Pr := mul_le_mul_of_nonneg_right hD hP₁.le
    nlinarith
  have hid := link_exponent_two_eq (V₂ := V₂) (B := D * Pr) (ne_of_gt hB)
  rw [← hl₂def] at hid
  linarith

/-- The link exponent at zero tilt and `l₂ = V₂/(2B)`: `(2l₂ + l₂²)B - l₂V₂ = V₂ - V₂²/(4B)`. -/
lemma link_exponent_zero_eq {V₂ B : ℝ} (hB : B ≠ 0) :
    (2 * (V₂ / (2 * B)) + (V₂ / (2 * B)) ^ 2) * B - V₂ / (2 * B) * V₂
      = V₂ - V₂ ^ 2 / (4 * B) := by
  field_simp
  ring

/-- **One link of the chain at zero tilt, above a threshold**: the increment alone,
`μ(E) ≤ exp(V₂ - V₂²/(4DP) + T)`.  `RMF.IsRademacherRMF.exists_measure_link_le` at `l₁ = 0`,
with the tail in place of the pair constant; no bound on the base is needed. -/
theorem IsRademacherRMF.measure_link_le_zero_tail {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) {σ V₂ D h₀ h₁ h₂ : ℝ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (y : ℕ)
    {E : Set Ω} (hσ : σ₀ ≤ σ) (hD : |h₁ - h₂| ≤ D) (hV₂ : 0 ≤ V₂) (hD0 : 0 < D)
    (hP₁ : 0 < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
    (hV₂P : V₂ / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ)
    (hE : MeasurableSet E)
    (hE₂ : ∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₁) ω‖
        - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₂) ω‖) :
    μ.real E ≤ Real.exp (V₂
      - V₂ ^ 2 / (4 * (D * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p))
      + radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))) := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨Pr, hPdef⟩ : ∃ Pr : ℝ,
      Pr = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  rw [← hPdef] at hP₁ hV₂P
  rw [← hPdef]
  set T := radPairTailConst σ₀ Λ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))
    with hTdef
  have hB : (0 : ℝ) < D * Pr := by positivity
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂ : ℝ, l₂ = V₂ / (2 * (D * Pr)) := ⟨_, rfl⟩
  have hl₂ : (0 : ℝ) ≤ l₂ := by rw [hl₂def]; positivity
  have hl₂D : l₂ * D = V₂ / (2 * Pr) := by
    rw [hl₂def]
    field_simp
  have hV₂half : V₂ / (2 * Pr) ≤ Λ := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Pr)]
    rw [div_le_iff₀ hP₁] at hV₂P
    linarith
  have hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ := by
    have h1 : l₂ * |h₁ - h₂| ≤ l₂ * D := mul_le_mul_of_nonneg_left hD hl₂
    rw [hl₂D] at h1
    linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have htail := rad_pair_prime_sum_tail_le_at hσ₀ hΛ (h₀ := h₀) hy₀ y le_rfl hl₂ hσ hΛ hl₂Λ
  rw [← hTdef] at htail
  have hmain := sum_pair_main_term_pairAbscissaAt_le (l₁ := 0) (l₂ := l₂) (σ := σ) (h₀ := h₀)
    (h₁ := h₁) (h₂ := h₂) le_rfl hl₂ y₀ y
  rw [← hAdef, ← hPdef] at hmain
  have hlog : Real.log (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
      ^ (2 * pairWeight 0 l₂ a) ∂μ) ≤ (2 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr + T := by
    rw [hf.integral_prod_norm_randomEulerProductIco_rpow_pair_at y₀ y 0 l₂ σ h₀ h₁ h₂ hσ0]
    have hz : ((0 : ℝ) ^ 2 / 2 + 0 / 2) * A + (2 * l₂ + 0 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr
        = (2 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr := by ring
    linarith [(abs_le.1 htail).2]
  have h := hf.measure_le_exp_pair_at_of_log_le hσ₀ le_rfl hl₂ hσ hlog hE
    (W := l₂ * V₂) (fun ω hω => by
      rw [pairAbscissaAt_one_heightLine, pairAbscissaAt_two_heightLine]
      have hB' := mul_le_mul_of_nonneg_left (hE₂ ω hω) hl₂
      linarith)
  refine le_trans h (Real.exp_le_exp.2 ?_)
  have hnn : (0 : ℝ) ≤ 2 * l₂ + l₂ ^ 2 := by nlinarith [sq_nonneg l₂]
  have hcross : (2 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr ≤ (2 * l₂ + l₂ ^ 2) * (D * Pr) := by
    have h1 : |h₁ - h₂| * Pr ≤ D * Pr := mul_le_mul_of_nonneg_right hD hP₁.le
    nlinarith
  have hid := link_exponent_zero_eq (V₂ := V₂) (B := D * Pr) (ne_of_gt hB)
  rw [← hl₂def] at hid
  linarith

/-! ### The constants -/

/-- **The threshold on the first prime**: past it the pair tail
`radPairTailConst σ₀ Λ₁ · y₀^{-3(σ₁-1/3)/2}` is at most `1`. -/
noncomputable def radChainThreshold (σ₀ Λ₁ : ℝ) : ℝ :=
  max 2 (radPairTailConst σ₀ Λ₁ ^ (3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))⁻¹)

lemma radPairTail_le_one_of_radChainThreshold_le {σ₀ Λ₁ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 0 ≤ Λ₁)
    {y₀ : ℕ} (hy₀ : radChainThreshold σ₀ Λ₁ ≤ y₀) :
    radPairTailConst σ₀ Λ₁ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) ≤ 1 := by
  have hC : 0 ≤ radPairTailConst σ₀ Λ₁ := radPairTailConst_nonneg hσ₀ hΛ₁
  have h := mul_rpow_neg_le_one_of_le hC
    (by linarith : (0 : ℝ) < 3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))
    (le_trans (le_max_right _ _) hy₀)
  rwa [show -(3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2)) = -3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2) by
    ring] at h

lemma two_le_radChainThreshold (σ₀ Λ₁ : ℝ) : 2 ≤ radChainThreshold σ₀ Λ₁ := le_max_left _ _

/-- The chaining sum of the sharp Rademacher chain, `8e^{2Λ'}·e^{(2Λ')²/(2c)}/(1 - e^{-c/2})`
with slope `Λ' = 35/32` and decay `c = 1/(192Λ₂)`. -/
noncomputable def radChainSum (Λ₂ : ℝ) : ℝ :=
  8 * Real.exp (2 * (35 / 32))
    * (Real.exp ((2 * (35 / 32)) ^ 2 / (2 * (1 / (192 * Λ₂))))
      * (1 - Real.exp (-(1 / (192 * Λ₂) / 2)))⁻¹)

/-- **The constant of the sharp Rademacher Lemma B.2**, `e² + e·radChainSum Λ₂`: `e²` the base
point, `e` the pair tail. -/
noncomputable def radChainConst (Λ₂ : ℝ) : ℝ :=
  Real.exp 2 + Real.exp 1 * radChainSum Λ₂

lemma radChainSum_pos {Λ₂ : ℝ} (hΛ₂ : 0 < Λ₂) : 0 < radChainSum Λ₂ := by
  have h1 : Real.exp (-(1 / (192 * Λ₂) / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < 1 / (192 * Λ₂) / 2 := by positivity
    linarith
  have h2 : (0 : ℝ) < 1 - Real.exp (-(1 / (192 * Λ₂) / 2)) := by linarith
  rw [radChainSum]
  positivity

lemma radChainConst_pos {Λ₂ : ℝ} (hΛ₂ : 0 < Λ₂) : 0 < radChainConst Λ₂ := by
  have := radChainSum_pos hΛ₂
  rw [radChainConst]
  positivity

/-! ### Lemma B.2 -/

set_option maxHeartbeats 800000 in
-- the assembly of the chain: the same size as `RMF.IsSteinhausRMF.measure_exists_gt_le_sharp`
/-- **Hamdan's Lemma B.2 for the Rademacher RMF, sharp.**  For `σ₀ ≤ σ`, `0 ≤ V ≤ Λ₁A`, `1 ≤ A`,
`rP ≤ Λ₂ ≤ 1/576` and `y₀ ≥ radChainThreshold σ₀ Λ₁`, `Λ₁ ≥ 2`:

`P(∃h ∈ [h₀, h₀+r) : log‖F(σ+ih)‖ > V) ≤ radChainConst Λ₂ · exp(A - 2V)`,

with `A = ∑_{y₀ ≤ p < y} p^{-2σ}` and `P = ∑_{y₀ ≤ p < y} p^{-2σ} log p`.  The base point is the
exact second moment (`e²`); every level `q ≥ 1` of the chain is a link at tilt `2` (when
`q + 1 ≤ V`) or `0`, each costing `e·exp(A - 2V + (35/16)(q+1) - q²(9/4)^ℓ/(192Λ₂))`. -/
theorem IsRademacherRMF.measure_exists_gt_le_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    {σ₀ Λ₁ Λ₂ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 2 ≤ Λ₁) (hΛ₂ : 0 < Λ₂) (hΛ₂576 : 576 * Λ₂ ≤ 1)
    {σ V r h₀ : ℝ} {y₀ : ℕ} (hy₀ : radChainThreshold σ₀ Λ₁ ≤ y₀) (y : ℕ) (hσ : σ₀ ≤ σ)
    (hr : 0 < r) (hV : 0 ≤ V)
    (hA1 : 1 ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hVΛ : V ≤ Λ₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hrP : r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
      ≤ radChainConst Λ₂ * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * V) := by
  have hΛ₁0 : (0 : ℝ) < Λ₁ := by linarith
  have hy₀2 : (2 : ℝ) ≤ (y₀ : ℝ) := le_trans (two_le_radChainThreshold σ₀ Λ₁) hy₀
  have hy₀1 : 1 ≤ y₀ := by exact_mod_cast (show (1 : ℝ) ≤ (y₀ : ℝ) by linarith)
  have hTp := radPairTail_le_one_of_radChainThreshold_le hσ₀ hΛ₁0.le hy₀
  set T := radPairTailConst σ₀ Λ₁ * (y₀ : ℝ) ^ (-3 * (((σ₀ + 1 / 3) / 2 - 1 / 3) / 2))
    with hTdef
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (192 * Λ₂) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hc3 : (3 : ℝ) ≤ c := by
    rw [hcdef, le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨Λ', hΛ'def⟩ : ∃ Λ' : ℝ, Λ' = 35 / 32 := ⟨_, rfl⟩
  obtain ⟨Csum, hCsumdef⟩ : ∃ Csum : ℝ, Csum = 8 * Real.exp (2 * Λ')
      * (Real.exp ((2 * Λ') ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹) := ⟨_, rfl⟩
  have hW : radChainConst Λ₂ = Real.exp 2 + Real.exp 1 * Csum := by
    unfold radChainConst radChainSum
    rw [show (1 : ℝ) / (192 * Λ₂) = c from hcdef.symm, show (35 : ℝ) / 32 = Λ' from
      hΛ'def.symm, ← hCsumdef]
  rw [hW]
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  haveI := hX.isProbabilityMeasure
  have hA : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := by linarith
  have hP : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
    have h := log_two_mul_sum_le_sum_mul_log σ y₀ y
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith only [h, hl2, hA]
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hre0 : (0 : ℝ) < (heightLine σ h₀).re := by rw [re_heightLine]; exact hσ0
  -- the unimodularity set
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    have hrw : {ω : Ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1}
        = ⋂ p ∈ primesIco y₀ y, {ω : Ω | ‖X p ω‖ ≤ 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hGdef, hrw]
    exact (primesIco y₀ y).measurableSet_biInter fun p hp =>
      measurableSet_le ((hX.measurable p (prime_of_mem_primesIco hp)).norm) measurable_const
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  -- the walk, based at `h₀`
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → Ω → ℝ, S = fun t ω =>
    ∑ p ∈ primesIco y₀ y, localLogAdd ((p : ℂ) ^ (-(heightLine σ (h₀ + t)))) (X p ω) := ⟨_, rfl⟩
  have hSmeas : ∀ t : ℝ, Measurable (S t) := by
    intro t
    simp only [hSdef]
    exact Finset.measurable_sum _ fun p hp =>
      (measurable_localLogAdd _).comp (hX.measurable p (prime_of_mem_primesIco hp))
  have hSeq : ∀ (t : ℝ) (ω : Ω), ω ∈ G →
      S t ω = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (heightLine σ (h₀ + t)) ω‖ := by
    intro t ω hω
    rw [hGdef] at hω
    simp only [hSdef]
    exact (log_norm_randomEulerProductIco_sqfree_eq
      (by rw [re_heightLine]; exact hσ0) hω).symm
  -- the Lipschitz bound and the level at which the chain is cut
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
    have h := abs_sum_localLogAdd_sub_le (B := primesIco y₀ y)
      (fun p hp => prime_of_mem_primesIco hp) hω
      (re_heightLine σ (h₀ + u)) (re_heightLine σ (h₀ + v)) hσ0
    rw [im_heightLine, im_heightLine, show h₀ + u - (h₀ + v) = u - v from by ring] at h
    simp only [hSdef]
    rw [hLipdef]
    exact h
  obtain ⟨L, hL⟩ := exists_level_le (Lip := Lip) hr (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌈V⌉₊ + 2 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; omega
  have hQupper : (Q : ℝ) ≤ V + 3 := by
    rw [hQdef]
    push_cast
    have := Nat.ceil_lt_add_one hV
    linarith
  have hQge : V + 2 ≤ (Q : ℝ) := by
    rw [hQdef]
    push_cast
    have := Nat.le_ceil V
    linarith
  -- the target, moved onto the unimodularity set and reindexed by `h = h₀ + t`
  have htarget : μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
      V < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (heightLine σ h) ω‖} = μ.real (G ∩ {ω | ∃ t ∈ Set.Ico 0 r, V < S t ω}) := by
    have hset : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖} = G ∩ {ω | ∃ t ∈ Set.Ico 0 r, V < S t ω} := by
      ext ω
      constructor
      · rintro ⟨hωG, h, hh, hlt⟩
        simp only [Set.mem_Ico] at hh
        refine ⟨hωG, h - h₀, ?_, ?_⟩
        · simp only [Set.mem_Ico]
          constructor <;> linarith [hh.1, hh.2]
        · rw [hSeq (h - h₀) ω hωG, show h₀ + (h - h₀) = h from by ring]
          exact hlt
      · rintro ⟨hωG, t, ht, hlt⟩
        simp only [Set.mem_Ico] at ht
        refine ⟨hωG, h₀ + t, ?_, ?_⟩
        · simp only [Set.mem_Ico]
          constructor <;> linarith [ht.1, ht.2]
        · rw [← hSeq t ω hωG]
          exact hlt
    unfold MeasureTheory.Measure.real
    rw [measure_eq_measure_inter_of_compl_null hGnull, hset]
  rw [htarget]
  refine le_trans (measureReal_inter_exists_gt_le (μ := μ) (S := S) (G := G) (V := V)
    hr hQ1 hLip0 hLip hL) ?_
  -- the base point
  have hbase0 : μ.real (G ∩ {ω | V - 1 < S 0 ω})
      ≤ Real.exp 2 * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * V) := by
    have h := hf.measure_ge_le_second_moment (V := V - 1) (s := heightLine σ h₀)
      (y₀ := y₀) (y₁ := y) (hGmeas.inter (measurableSet_lt measurable_const (hSmeas 0)))
      (fun ω hω => norm_randomEulerProductIco_sqfree_pos hre0 (by
        have := hω.1
        rwa [hGdef] at this))
      (fun ω hω => by
        have h0 := hSeq 0 ω hω.1
        rw [add_zero] at h0
        rw [← h0]
        exact le_of_lt hω.2)
    refine le_trans h (le_of_eq ?_)
    rw [← Real.exp_add]
    simp only [re_heightLine]
    ring_nf
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
  -- one link of the chain, at every level
  have hterm : ∀ q ℓ i : ℕ, 1 ≤ q → q ≤ Q → ∀ E : Set Ω, MeasurableSet E → E ⊆ G →
      (∀ ω ∈ E, q < Q → V - q - 1 < S 0 ω) →
      (∀ ω ∈ E, (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
        ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
          - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω) →
      μ.real E ≤ Real.exp 1
        * Real.exp (-(2 * V - AA) + 2 * Λ' * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro q ℓ i hq1 hqQ' E hEmeas hEG hE1 hE2
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ'
    have hp4 : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
    have hgap : |(h₀ + (i : ℝ) * (r / 4 ^ (ℓ + 1)))
        - (h₀ + ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)))| ≤ 3 * r / 4 ^ (ℓ + 1) := by
      have hdm : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
      have hcast : (i : ℝ) - ((4 * (i / 4) : ℕ) : ℝ) = ((i % 4 : ℕ) : ℝ) := by
        have h := congrArg (fun n : ℕ => (n : ℝ)) hdm
        push_cast at h ⊢
        linarith
      have hmod3 : ((i % 4 : ℕ) : ℝ) ≤ 3 := by
        have h : i % 4 ≤ 3 := by omega
        exact_mod_cast h
      have hr4 : (0 : ℝ) < r / 4 ^ (ℓ + 1) := by positivity
      rw [show h₀ + (i : ℝ) * (r / 4 ^ (ℓ + 1)) - (h₀ + ((4 * (i / 4) : ℕ) : ℝ)
          * (r / 4 ^ (ℓ + 1))) = ((i : ℝ) - ((4 * (i / 4) : ℕ) : ℝ)) * (r / 4 ^ (ℓ + 1)) by ring,
        hcast, abs_of_nonneg (by positivity),
        show 3 * r / 4 ^ (ℓ + 1) = 3 * (r / 4 ^ (ℓ + 1)) by ring]
      exact mul_le_mul_of_nonneg_right hmod3 hr4.le
    have hD0 : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) := by positivity
    have hw1 : ((3 : ℝ) / 4) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hV2ge : (0 : ℝ) ≤ (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) := by positivity
    have hV2small : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) ≤ (q : ℝ) / 8 := by
      linarith [mul_le_mul_of_nonneg_left hw1 hq0R]
    -- the links' Laplace range: `V₂/PP ≤ Λ₁`
    have hV2P : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) / PP ≤ Λ₁ := by
      rw [div_le_iff₀ hP]
      have hΛA : 2 ≤ Λ₁ * AA := by nlinarith only [hΛ₁, hA1]
      have h1 : Λ₁ * (Real.log 2 * AA) ≤ Λ₁ * PP := mul_le_mul_of_nonneg_left hPlow hΛ₁0.le
      have h2 : 0.6931471803 * (Λ₁ * AA) ≤ Λ₁ * (Real.log 2 * AA) := by
        have := mul_le_mul_of_nonneg_right hlog2.le (show (0 : ℝ) ≤ Λ₁ * AA by linarith)
        linarith only [this]
      linarith only [hV2small, hqQR, hQupper, hVΛ, h1, h2, hΛA]
    -- the decay
    have hnum := two_mul_le_sq_div_two_mul hr hP hΛ₂ hrP q ℓ
    have hcnum : c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ
        ≤ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2 / (4 * (3 * r / 4 ^ (ℓ + 1) * PP)) := by
      have hB : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) * PP := by positivity
      have e1 : ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2 / (4 * (3 * r / 4 ^ (ℓ + 1) * PP))
          = ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
            / (2 * (3 * r / 4 ^ (ℓ + 1) * PP)) / 2 := by
        field_simp
        ring
      have e2 : c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ
          = 2 * (1 / (192 * Λ₂)) * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ / 2 := by
        rw [hcdef]
        ring
      rw [e1, e2]
      linarith
    have hslope : 2 * ((q : ℝ) + 1) + 3 * ((q : ℝ) / 8) / 2 ≤ 2 * Λ' * ((q : ℝ) + 1) := by
      rw [hΛ'def]
      linarith
    rcases le_or_gt ((q : ℝ) + 1) V with hpos | hneg
    · have hqQ : q < Q := by
        have h1 : (q : ℝ) < (Q : ℝ) := by linarith
        exact_mod_cast h1
      have h := hf.measure_link_le_two_tail hσ₀ hΛ₁ hy₀1 y (V₁ := V - (q : ℝ) - 1)
        (V₂ := (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) (D := 3 * r / 4 ^ (ℓ + 1))
        (h₀ := h₀) (h₁ := h₀ + (i : ℝ) * (r / 4 ^ (ℓ + 1)))
        (h₂ := h₀ + ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)))
        hσ hgap hV2ge hD0 (hPPdef ▸ hP) (hPPdef ▸ hV2P) hEmeas
        (fun ω hω => by
          have h0 := hSeq 0 ω (hEG hω)
          rw [add_zero] at h0
          rw [← h0]
          exact le_of_lt (hE1 ω hω hqQ))
        (fun ω hω => by
          rw [← hSeq _ ω (hEG hω), ← hSeq _ ω (hEG hω)]
          exact hE2 ω hω)
      rw [← hAAdef, ← hPPdef, ← hTdef] at h
      refine le_trans h ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hlin : 3 * ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) / 2 ≤ 3 * ((q : ℝ) / 8) / 2 := by
        linarith only [hV2small]
      linarith only [hcnum, hslope, hlin, hTp]
    · have h := hf.measure_link_le_zero_tail hσ₀ hΛ₁0.le hy₀1 y
        (V₂ := (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) (D := 3 * r / 4 ^ (ℓ + 1))
        (h₀ := h₀) (h₁ := h₀ + (i : ℝ) * (r / 4 ^ (ℓ + 1)))
        (h₂ := h₀ + ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1)))
        hσ hgap hV2ge hD0 (hPPdef ▸ hP) (hPPdef ▸ hV2P) hEmeas
        (fun ω hω => by
          rw [← hSeq _ ω (hEG hω), ← hSeq _ ω (hEG hω)]
          exact hE2 ω hω)
      rw [← hPPdef, ← hTdef] at h
      refine le_trans h ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hsl0 : (q : ℝ) / 8 ≤ AA - 2 * V + 2 * Λ' * ((q : ℝ) + 1) := by
        rw [hΛ'def]
        linarith only [hneg, hA1, hq0R]
      linarith only [hcnum, hsl0, hV2small, hTp]
  -- every level of the chain
  have hbig : ∀ q ∈ Finset.Icc 1 Q,
      μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - q - 1 < S 0 ω) ∧ S 0 ω ≤ V - q}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Real.exp 1 * ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1)
          * Real.exp (-(2 * V - AA) + 2 * Λ' * ((q : ℝ) + 1)
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
        ≤ Real.exp 1 * Real.exp (-(2 * V - AA) + 2 * Λ' * ((q : ℝ) + 1)
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
  have hchain := sum_chaining_le (W := 2 * V - AA) (Λ := Λ') (c := c) hc (Finset.Icc 1 Q) hT L
  rw [← hCsumdef] at hchain
  have hfin := mul_le_mul_of_nonneg_left hchain (Real.exp_pos 1).le
  have hEeq : Real.exp (-(2 * V - AA)) = Real.exp (AA - 2 * V) := by
    congr 1
    ring
  rw [hEeq] at hfin
  have hbase1 : Real.exp 2 * Real.exp (AA - 2 * V)
      + Real.exp 1 * (Csum * Real.exp (AA - 2 * V))
      = (Real.exp 2 + Real.exp 1 * Csum) * Real.exp (AA - 2 * V) := by ring
  linarith only [hbase0, hsum, hfin, hbase1]

/-- **Lemma B.2's lower tail for the Rademacher RMF, sharp.**
`P(∃h ∈ [h₀, h₀+r) : W + 4A < -log‖F(σ+ih)‖) ≤ radChainConst Λ₂ · exp(A - 2W)`: the reflection
`X ↦ -X` (`RMF.IsRademacherPrimeValues.neg`) and `RMF.neg_log_norm_randomEulerProductIco_sqfree_le`,
as in `RMF.IsRademacherRMF.exists_measure_exists_lt_le`. -/
theorem IsRademacherRMF.measure_exists_lt_le_sharp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    {σ₀ Λ₁ Λ₂ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ₁ : 2 ≤ Λ₁) (hΛ₂ : 0 < Λ₂) (hΛ₂576 : 576 * Λ₂ ≤ 1)
    {σ W r h₀ : ℝ} {y₀ : ℕ} (hy₀ : radChainThreshold σ₀ Λ₁ ≤ y₀) (y : ℕ) (hσ : σ₀ ≤ σ)
    (hr : 0 < r) (hW : 0 ≤ W)
    (hA1 : 1 ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hWΛ : W ≤ Λ₁ * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (hrP : r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ₂) :
    μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
      ≤ radChainConst Λ₂ * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * W) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hσ13 : (1 : ℝ) / 3 ≤ σ := by linarith
  have hX' := hX.neg
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hsub : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      ⊆ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} := by
    rintro ω ⟨hωG, h, hh, hlt⟩
    have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
    have hre : (heightLine σ h).re = σ := re_heightLine σ h
    have hrefl := neg_log_norm_randomEulerProductIco_sqfree_le (X := X) (y := y)
      (s := heightLine σ h) (by rw [hre]; exact hσ13) hωu
    rw [hre] at hrefl
    exact ⟨h, hh, by linarith⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      = μ.real (G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            < -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              y₀ y (heightLine σ h) ω‖}) := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ radChainConst Λ₂ * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * W) :=
        hX'.isRademacherRMF.measure_exists_gt_le_sharp hσ₀ hΛ₁ hΛ₂ hΛ₂576 hy₀ y hσ hr hW hA1 hWΛ
          hrP

end RMF
