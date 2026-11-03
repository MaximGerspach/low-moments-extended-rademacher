/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.JointLaplace
import RMF.EulerProduct.LogExpansionExplicit

/-!
# The joint Laplace transform with its constants named

The explicit twins of the constant-carrying statements of `RMF/EulerProduct/JointLaplace.lean`
that Harper's theorem uses.  Every constant is a closed form:

* `RMF.localPairConst θ₀`: the pair expansion after logarithms, from `RMF.localPairFine`,
  `RMF.localPairScale` and `RMF.localPairTail`;
* `RMF.localMultiConst Q n`, `RMF.localMultiLogConst Q θ n`: the multi-weight expansion, before and
  after logarithms, for `n` weights bounded by `Q`.
-/

open Finset MeasureTheory ProbabilityTheory

namespace RMF

variable {ι : Type*}

/-! ### The multi-weight expansion -/

/-- **The multi-weight expansion's constant**: `C_fine + M/d³ + 1` with `K = Qn`,
`d = 1/(4(K+1))`, `C_fine = 64K³ + 48eK + K²/20` and `M = e^{K/2} + 1 + K²/25`. -/
noncomputable def localMultiConst (Q : ℝ) (n : ℕ) : ℝ :=
  64 * (Q * n) ^ 3 + 48 * Real.exp 1 * (Q * n) + (Q * n) ^ 2 / 20
    + (Real.exp (Q * n / 2) + (1 + (Q * n) ^ 2 / 25)) / (1 / (4 * (Q * n + 1))) ^ 3 + 1

/-- **`RMF.exists_local_multi_expansion_steinhausLaw` at its constant**
`RMF.localMultiConst Q A.card`. -/
theorem exists_local_multi_expansion_steinhausLaw_explicit (A : Finset ι) {Q : ℝ} (hQ0 : 0 ≤ Q) :
    localMultiConst Q A.card > 0 ∧ ∀ (q : ι → ℝ) (w : ι → ℂ) (t : ℝ),
      (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, ‖w a‖ ≤ t) → 0 ≤ t → t ≤ 1 / 5 →
        |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
            - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)| ≤ (localMultiConst Q A.card) * t ^ 3 := by
  have hK0 : (0 : ℝ) ≤ Q * A.card := mul_nonneg hQ0 (Nat.cast_nonneg _)
  set K : ℝ := Q * A.card with hKdef
  set d : ℝ := 1 / (4 * (K + 1)) with hddef
  have hd : 0 < d := by rw [hddef]; positivity
  set Cfine : ℝ := 64 * K ^ 3 + 48 * Real.exp 1 * K + K ^ 2 / 20 with hCfine
  set M : ℝ := Real.exp (K / 2) + (1 + K ^ 2 / 25) with hMdef
  have hCfine0 : 0 ≤ Cfine := by rw [hCfine]; positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hW : localMultiConst Q A.card = Cfine + M / d ^ 3 + 1 := by
    unfold localMultiConst
    rw [hCfine, hMdef, hddef, hKdef]
  rw [hW]
  refine ⟨by positivity, ?_⟩
  intro q w t hq hw ht0 ht
  have hfine : t ≤ d →
      |(∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
        - (1 + ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)| ≤ Cfine * t ^ 3 := by
    intro htd
    have hsmall : 4 * (Q * A.card) * t ≤ 1 := by
      have h1 : t ≤ 1 / (4 * (K + 1)) := by rwa [← hddef]
      have h2 : (0 : ℝ) < 4 * (K + 1) := by linarith
      rw [le_div_iff₀ h2] at h1
      nlinarith
    exact abs_integral_prod_localIntegrand_sub_le hq hw hQ0 ht0 ht hsmall
  have hcrude := abs_integral_prod_localIntegrand_sub_le_crude hq hw hQ0 ht
  have hcube := le_mul_cube_of_two_regime hd ht0 hM0 hCfine0 hfine hcrude
  nlinarith [pow_nonneg ht0 3]

/-- **The multi-weight expansion after logarithms**: `RMF.logSubPolyConst` at
`C₀ = localMultiConst Q n`, `K = (Qn)²` and `M₀ = 2Qn·log(1/(1-θ))`. -/
noncomputable def localMultiLogConst (Q θ : ℝ) (n : ℕ) : ℝ :=
  logSubPolyConst (localMultiConst Q n) ((Q * n) ^ 2) (2 * (Q * n) * Real.log ((1 - θ)⁻¹))

/-- **`RMF.exists_abs_log_local_multi_le` at its constant** `RMF.localMultiLogConst Q θ A.card`. -/
theorem exists_abs_log_local_multi_le_explicit (A : Finset ι) {Q θ : ℝ} (hQ0 : 0 ≤ Q) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) :
    localMultiLogConst Q θ A.card > 0 ∧ ∀ (q : ι → ℝ) (w : ι → ℂ) (t : ℝ),
      (∀ a ∈ A, |q a| ≤ Q) → (∀ a ∈ A, ‖w a‖ ≤ t) → 0 ≤ t → t ≤ θ →
        |Real.log (∫ z, ∏ a ∈ A, ‖(1 - z * w a)⁻¹‖ ^ (2 * q a) ∂steinhausLaw)
            - ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2| ≤ (localMultiLogConst Q θ A.card) * t ^ 3 := by
  have hK0 : (0 : ℝ) ≤ Q * A.card := mul_nonneg hQ0 (Nat.cast_nonneg _)
  have hL0 : (0 : ℝ) ≤ Real.log ((1 - θ)⁻¹) :=
    Real.log_nonneg (one_le_inv_iff₀.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨hC₀, hexp⟩ := exists_local_multi_expansion_steinhausLaw_explicit A hQ0
  set C₀ := localMultiConst Q A.card with hC₀_expl
  obtain ⟨hC, hbound⟩ := exists_abs_log_sub_poly_le_explicit (C₀ := C₀)
    (K := (Q * A.card) ^ 2) (M₀ := 2 * (Q * A.card) * Real.log ((1 - θ)⁻¹))
    hC₀.le (by positivity) (by positivity)
  set C := logSubPolyConst C₀ ((Q * A.card) ^ 2)
    (2 * (Q * A.card) * Real.log ((1 - θ)⁻¹)) with hC_expl
  have hW : localMultiLogConst Q θ A.card = C := rfl
  rw [hW]
  refine ⟨hC, ?_⟩
  intro q w t hq hw ht0 ht
  refine hbound _ _ t ht0 (by linarith)
    (fun h5 => hexp q w t hq hw ht0 h5) ?_
    (abs_log_integral_prod_localIntegrand_le hq (fun a ha => le_trans (hw a ha) ht) hθ)
  -- the polynomial part is `O(t²)`
  have hu0 : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a‖ := norm_nonneg _
  have h1 := norm_sum_smul_le hq hw
  have hsq : ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 ≤ ((Q * A.card) * t) ^ 2 :=
    pow_le_pow_left₀ hu0 h1 2
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2)]
  nlinarith

/-! ### The pair expansion -/

/-- The pair expansion's fine-regime constant, `4e/(1-θ₀) + 65`. -/
noncomputable def localPairFine (θ₀ : ℝ) : ℝ := 4 * Real.exp 1 / (1 - θ₀) + 65

/-- The pair expansion's switching scale, `min{(1-θ₀)/8, 1/(4(C_f+1))}`. -/
noncomputable def localPairScale (θ₀ : ℝ) : ℝ :=
  min ((1 - θ₀) / 8) (1 / (4 * (localPairFine θ₀ + 1)))

/-- The pair expansion's crude-regime constant, `2/((1-θ₀)d₀²) + 1/d₀`. -/
noncomputable def localPairTail (θ₀ : ℝ) : ℝ :=
  2 / ((1 - θ₀) * localPairScale θ₀ ^ 2) + 1 / localPairScale θ₀

/-- **The pair expansion's constant**, `2(1+C_f)² + C_f + C_tail`. -/
noncomputable def localPairConst (θ₀ : ℝ) : ℝ :=
  2 * (1 + localPairFine θ₀) ^ 2 + localPairFine θ₀ + localPairTail θ₀

set_option maxHeartbeats 400000 in
-- the proof exceeds the default `maxHeartbeats`
/-- **`RMF.exists_abs_log_local_pair_le` at its constant** `RMF.localPairConst θ₀`. -/
theorem exists_abs_log_local_pair_le_explicit {θ₀ : ℝ} (hθ₀0 : 0 ≤ θ₀) (hθ₀ : θ₀ < 1) :
    localPairConst θ₀ > 0 ∧ ∀ (l₁ l₂ t d : ℝ) (w : Fin 3 → ℂ), 0 ≤ l₁ → 0 ≤ l₂ → 0 ≤ d → 0 ≤ t →
        t ≤ θ₀ →
      (∀ a, ‖w a‖ ≤ t) → ‖w 1 - w 2‖ ≤ t * d →
        |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
            - ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2|
          ≤ (localPairConst θ₀) * ((1 + (l₁ / 2 + l₂ / 2 * d)) * t) ^ 3 := by
  have h1θ₀ : (0 : ℝ) < 1 - θ₀ := by linarith
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = 4 * Real.exp 1 / (1 - θ₀) + 65 := ⟨_, rfl⟩
  have hCf0 : (0 : ℝ) < Cf := by rw [hCfdef]; positivity
  obtain ⟨d₀, hd₀def⟩ : ∃ d₀ : ℝ, d₀ = min ((1 - θ₀) / 8) (1 / (4 * (Cf + 1))) := ⟨_, rfl⟩
  have hd₀0 : (0 : ℝ) < d₀ := by
    rw [hd₀def]
    exact lt_min (by positivity) (by positivity)
  have hd₀8 : d₀ ≤ (1 - θ₀) / 8 := by rw [hd₀def]; exact min_le_left _ _
  have hd₀le : d₀ ≤ 1 / 8 := le_trans hd₀8 (by linarith)
  have hCd₀ : Cf * d₀ ≤ 1 / 4 := by
    have hd₀C : d₀ ≤ 1 / (4 * (Cf + 1)) := by rw [hd₀def]; exact min_le_right _ _
    have h1 : Cf * d₀ ≤ Cf * (1 / (4 * (Cf + 1))) :=
      mul_le_mul_of_nonneg_left hd₀C hCf0.le
    have h2 : Cf * (1 / (4 * (Cf + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  obtain ⟨Ctail, hCtail⟩ : ∃ Ctail : ℝ, Ctail = 2 / ((1 - θ₀) * d₀ ^ 2) + 1 / d₀ := ⟨_, rfl⟩
  have hCtail0 : (0 : ℝ) ≤ Ctail := by rw [hCtail]; positivity
  have hW : localPairConst θ₀ = 2 * (1 + Cf) ^ 2 + Cf + Ctail := by
    unfold localPairConst localPairTail localPairScale localPairFine
    rw [hCtail, hd₀def, hCfdef]
  rw [hW]
  refine ⟨by positivity, ?_⟩
  intro l₁ l₂ t d w hl₁ hl₂ hd0 ht0 htθ hw h12
  have ht1 : t < 1 := lt_of_le_of_lt htθ hθ₀
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hfine0 :=
    abs_integral_prod_localIntegrand_sub_pair_le hl₁ hl₂ hd0 ht0 htθ hθ₀ hw h12
  have hcrude0 : |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂steinhausLaw)| ≤ 2 * (l₁ / 2 + l₂ / 2 * d) * (t / (1 - t)) :=
    abs_log_integral_prod_localIntegrand_le_of_bound
      (fun a _ => lt_of_le_of_lt (hw a) ht1) fun _ hz =>
      abs_logExponent_pairWeight_le hz hl₁ hl₂ ht1 (hw 0) (hw 1) (hw 2) h12
  have hm1' : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ≤ (l₁ / 2 + l₂ / 2 * d) * t := by
    simpa using norm_sum_pairWeight_pow_le hl₁ hl₂ (hw 0) (hw 1) (hw 2) h12 (k := 1) le_rfl
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = l₁ / 2 + l₂ / 2 * d := ⟨_, rfl⟩
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  rw [← hMdef] at hfine0 hcrude0 hm1' ⊢
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (1 + M) * t := ⟨_, rfl⟩
  rw [← hxdef] at hfine0 ⊢
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
  have hx20 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have hx30 : (0 : ℝ) ≤ x ^ 3 := by positivity
  have hMtx : M * t ≤ x := by rw [hxdef]; nlinarith
  have hm1x : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ≤ x := le_trans hm1' hMtx
  have hPx : |‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2| ≤ 1 * x ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (∑ a, (pairWeight l₁ l₂ a : ℂ) * w a)]
  have hP2 : ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2 ≤ 1 * x ^ 2 := (abs_le.1 hPx).2
  have hP0 : (0 : ℝ) ≤ ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2 := by positivity
  have hcrudex : |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a)
      ∂steinhausLaw)| ≤ 2 * x / (1 - θ₀) := by
    refine le_trans hcrude0 ?_
    have hfrac : t / (1 - t) ≤ t / (1 - θ₀) := by
      rw [div_le_div_iff₀ h1t h1θ₀]
      exact mul_le_mul_of_nonneg_left (by linarith) ht0
    have h1 : 2 * M * (t / (1 - t)) ≤ 2 * M * (t / (1 - θ₀)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    have h2 : 2 * M * (t / (1 - θ₀)) ≤ 2 * x / (1 - θ₀) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right h1θ₀]
      linarith
    linarith
  rcases le_or_gt x d₀ with hfine | hbig
  · -- the fine regime: `x ≤ d₀` makes the combination small
    have hIP : |(∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
        - (1 + ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2)| ≤ Cf * x ^ 3 := by
      rw [hCfdef]
      exact hfine0 (le_trans hfine hd₀8)
    have hhalf : |(∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
        - 1| ≤ 1 / 2 := by
      have h3 : Cf * x ^ 3 ≤ Cf * d₀ * x ^ 2 := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfine hx20) hCf0.le
        calc Cf * x ^ 3 = Cf * (x * x ^ 2) := by ring
          _ ≤ Cf * (d₀ * x ^ 2) := h
          _ = Cf * d₀ * x ^ 2 := by ring
      have h4 : Cf * d₀ * x ^ 2 ≤ 1 / 4 * x ^ 2 := mul_le_mul_of_nonneg_right hCd₀ hx20
      have h5 : x ^ 2 ≤ 1 / 64 := by nlinarith [le_trans hfine hd₀le]
      have h1 := abs_le.1 hIP
      rw [abs_le]
      constructor <;> linarith only [h1.1, h1.2, hP2, hP0, h3, h4, h5]
    have h := abs_log_sub_poly_le hx0
      (by linarith [le_trans hfine hd₀le]) hCf0.le hIP hPx hhalf
    calc |Real.log (∫ z, ∏ a, ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw)
          - ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2|
        ≤ (2 * (1 + Cf) ^ 2 + Cf) * x ^ 3 := h
      _ ≤ (2 * (1 + Cf) ^ 2 + Cf + Ctail) * x ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) hx30
  · -- the crude regime: `x > d₀`, so `x³` dominates both `x` and `x²`
    have hA : 2 * x / (1 - θ₀) ≤ 2 / ((1 - θ₀) * d₀ ^ 2) * x ^ 3 := by
      have hxx : d₀ ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hd₀0.le hbig.le 2
      rw [div_mul_eq_mul_div, div_le_div_iff₀ h1θ₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hxx
        (by positivity : (0 : ℝ) ≤ 2 * x * (1 - θ₀))]
    have hB : 1 * x ^ 2 ≤ 1 / d₀ * x ^ 3 := by
      rw [one_mul, div_mul_eq_mul_div, le_div_iff₀ hd₀0]
      nlinarith [sq_nonneg x, hbig.le]
    have hsplit := abs_sub (Real.log (∫ z, ∏ a,
        ‖(1 - z * w a)⁻¹‖ ^ (2 * pairWeight l₁ l₂ a) ∂steinhausLaw))
      (‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2)
    have habsP : |‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2|
        = ‖∑ a, (pairWeight l₁ l₂ a : ℂ) * w a‖ ^ 2 := abs_of_nonneg (by positivity)
    have hfin : (2 / ((1 - θ₀) * d₀ ^ 2) + 1 / d₀) * x ^ 3
        ≤ (2 * (1 + Cf) ^ 2 + Cf + Ctail) * x ^ 3 := by
      rw [← hCtail]
      exact mul_le_mul_of_nonneg_right
        (by linarith only [sq_nonneg (1 + Cf), hCf0.le]) hx30
    rw [habsP] at hsplit
    linarith only [hsplit, hcrudex, hP2, hA, hB, hfin]

end RMF
