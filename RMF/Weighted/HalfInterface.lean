/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfSmallPrimes
import RMF.Weighted.HalfFirstMoment
import RMF.Weighted.HalfDecomposition
import RMF.Weighted.HalfReduction

/-!
# The `q = ½` lower bound: the end result

`RMF.exists_integral_weightedRademacherSum_asymp_half`: `E|∑_{n≤x} f(n)/√n| ≍ (log log x)^{3/4}`,
the `q = ½` case of Theorem 1.2 of the paper for the weighted sum.  The small-prime statements
(C2) `RMF.integral_halfTwist_pair_le` and (C3) `RMF.le_setIntegral_halfLadder_twist` are in
`RMF/Weighted/HalfSmallPrimes.lean`, in the objects of `RMF/Weighted/HalfEvents.lean`; the
barriered second moment (Proposition 6.4 of the paper) is in `RMF/Weighted/HalfSecondMoment.lean`,
the first moment (Proposition 6.3) in `RMF/Weighted/HalfFirstMoment.lean`, the decomposition in
`RMF/Weighted/HalfDecomposition.lean`.

## How they fit

Write `F_{(a,b]}` for the Euler product over the primes with `a < log log p ≤ b`, `σ = 2V/log x`,
`J = ∫_ℝ |F(½+σ+ih)/(σ+ih)|² dh`, `t = ⌊log(1/σ)⌋ - 4` (so `e^{-5} < σe^t ≤ e^{-4}`), and fix the
barrier's constants `(j₀, C₁, a, B)` from the first moment.  For `k ∈ K = [k₀+2, ⌊t/2⌋]` let

`W_k = e^{2k}(log x)^{-1} ∫_{h ∈ halfWindow k} 1_{L(k,h)} R(h) |F_{(k,x]}(½+σ+ih)|² dh`,
`R(h) = |F_{(k₀,k]}(½+σ+ih)|² / F_{(k₀,k]}(½+σ)²`.

The decomposition proves, pointwise, `(J/log x)^{1/2} ≥ c(k₀) ∑_{k ∈ K} 1_{E(k)} F_{(k₀,k]}(½+σ)
W_k^{1/2}`, from `|σ+ih|^{-2} ≥ e^{2k}/2` on the window, the deterministic lower bound on the
primes up to `exp(e^{k₀})`, and the disjointness of the `E(k) = E_≤(k) ∩ E_>(k)`.  Then, per `k`,
Hölder backwards with the weight `F_{(k₀,k]}(½+σ)` (which needs no normalisation):

`E[1_{E(k)} F W_k^{1/2}] ≥ E[1_{E(k)} F W_k]^{3/2} / E[F W_k²]^{1/2}`.

Independence of the primes below and above `exp(e^k)` factorises both moments:
* numerator: `∫_h E[1_{E_≤(k)} |F_{(k₀,k]}(σ+ih)|²/F_{(k₀,k]}(σ)] · E[1_{E_>(k)} 1_{L(k,h)}
  |F_{(k,x]}(σ+ih)|²] dh ≥ c₃ · c₄ e^{t-k}/√(t-k) · |window|` by (C3) and the first moment;
* denominator: `∬ E[F_{(k₀,k]}(σ) R(h₁) R(h₂)] · E[1_{L(k,h₁)} 1_{L(k,h₂)} |F_{(k,x]}(h₁)|²
  |F_{(k,x]}(h₂)|²] ≤ C₂ · C₃ e^{2t-4k}/(t-k)` by (C2) and the second moment.

So `E[1_{E(k)} F W_k^{1/2}] ≫ (e^t/log x)^{1/2} (t-k)^{-1/4} ≍ V^{-1/2}(t-k)^{-1/4}`, and summing
over `K` gives `≫ V^{-1/2} (log log x)^{3/4}` (`RMF.exists_le_integral_sqrt_lineDiv_half`), the
main term of the lower reduction `RMF.exists_le_integral_norm_weightedRademacherSum_half_line`.
With `V` a large constant that is the lower bound of the end result.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The decomposition, and the end result -/

/-- `e^{V/2} ≥ V` for `V ≥ 0`: `e^{V/2} = (e^{V/4})² ≥ (1 + V/4)² ≥ V`. -/
lemma le_exp_half (V : ℝ) (hV : 0 ≤ V) : V ≤ Real.exp (V / 2) := by
  have h1 : 1 + V / 4 ≤ Real.exp (V / 4) := by linarith [Real.add_one_le_exp (V / 4)]
  have h2 : Real.exp (V / 2) = Real.exp (V / 4) * Real.exp (V / 4) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h2]
  nlinarith [mul_le_mul h1 h1 (by linarith) (Real.exp_pos _).le, sq_nonneg (V / 4 - 1)]

/-- **The choice of `V`**: `C e^{-V/2} ≤ d V^{-1/2}` once `V ≥ 1` and `V ≥ (C/d)²`, since
`e^{V/2} ≥ V` makes `C e^{-V/2} ≤ C/V = (C V^{-1/2}) V^{-1/2}`. -/
lemma mul_exp_neg_half_le_of_sq_le {C d V : ℝ} (hC : 0 ≤ C) (hd : 0 < d) (hV : 1 ≤ V)
    (hVd : (C / d) ^ 2 ≤ V) : C * Real.exp (-(V / 2)) ≤ d * V ^ (-(1 / 2 : ℝ)) := by
  have hV0 : 0 < V := by linarith
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hrpow : V ^ (-(1 / 2 : ℝ)) = (Real.sqrt V)⁻¹ := by
    rw [Real.rpow_neg hV0.le, ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt V * Real.sqrt V = V := Real.mul_self_sqrt hV0.le
  -- `C/d ≤ √V`, i.e. `C ≤ d √V`
  have hCd : C / d ≤ Real.sqrt V := by
    rw [show C / d = Real.sqrt ((C / d) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hVd
  have hC' : C ≤ d * Real.sqrt V := by
    rw [div_le_iff₀ hd] at hCd
    linarith
  -- `C e^{-V/2} ≤ C/V = (C/√V)·(√V)⁻¹ ≤ d (√V)⁻¹`
  have he : C * Real.exp (-(V / 2)) ≤ C / V := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hC hV0 (le_exp_half V hV0.le)
  have hCV : C / Real.sqrt V * (Real.sqrt V)⁻¹ = C / V := by
    rw [← div_eq_mul_inv, div_div, hsq]
  rw [hrpow]
  refine le_trans he ?_
  rw [← hCV]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hs0).2 hC') (inv_nonneg.2 hs0.le)

/-- The arithmetic of the assembly: from the reduction `c₁PQ - C₁eL ≤ E`, the main term
`c₂vL ≤ PQ` and the choice `C₁e ≤ dv` with `c₁c₂ = 2d`, `dvL ≤ E`. -/
lemma half_final_arith {E P Q L c₁ c₂ C₁ d e v : ℝ} (hc₁ : 0 ≤ c₁) (hL : 0 ≤ L)
    (hd : c₁ * c₂ = 2 * d) (h1 : c₁ * P * Q - C₁ * e * L ≤ E) (h2 : c₂ * v * L ≤ P * Q)
    (h3 : C₁ * e ≤ d * v) : d * v * L ≤ E := by
  have h4 := mul_le_mul_of_nonneg_left h2 hc₁
  have h5 := mul_le_mul_of_nonneg_right h3 hL
  have e1 : c₁ * (c₂ * v * L) = 2 * (d * v * L) := by linear_combination (v * L) * hd
  have e2 : c₁ * (P * Q) = c₁ * P * Q := by ring
  linarith

/-- **The order of magnitude of `E|S(x)|`**: `c(log log x)^{3/4} ≤ E|∑_{n≤x} f(n)/√n|
≤ C(log log x)^{3/4}` for `x ≥ x₀`, the `q = ½` case of Theorem 1.2 of the paper for the weighted
sum.

The upper bound is `RMF.exists_const_integral_rpow_weightedRademacherSum_le_smallQ` at `q = ½`
with `Λ(1+√Λ/2)^{-1/2} ≤ 2Λ^{3/4}`.  The lower bound is the lower reduction
(`RMF.exists_le_integral_norm_weightedRademacherSum_half_line`) with its main term bounded below by
the decomposition (`RMF.exists_le_integral_sqrt_lineDiv_half`), at the constant
`V = max(1, (C₁/d)²)` of `RMF.mul_exp_neg_half_le_of_sq_le`. -/
theorem exists_integral_weightedRademacherSum_asymp_half :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
        c * Real.log (Real.log x) ^ (3 / 4 : ℝ)
            ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
          ∧ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ
            ≤ C * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hred⟩ :=
    exists_le_integral_norm_weightedRademacherSum_half_line (Ω := Ω)
  obtain ⟨c₂, hc₂, hmain⟩ := exists_le_integral_sqrt_lineDiv_half (Ω := Ω)
  obtain ⟨Cu, xu, hCu, hup⟩ := exists_const_integral_rpow_weightedRademacherSum_le_smallQ (Ω := Ω)
  have hd0 : 0 < c₁ * c₂ / 2 := by positivity
  have hV1 : (1 : ℝ) ≤ max 1 ((C₁ / (c₁ * c₂ / 2)) ^ 2) := le_max_left _ _
  obtain ⟨x₁, hx₁⟩ := hred _ hV1
  obtain ⟨x₂, hx₂⟩ := hmain _ hV1
  have hVpos : 0 < (max 1 ((C₁ / (c₁ * c₂ / 2)) ^ 2)) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  refine ⟨c₁ * c₂ / 2 * (max 1 ((C₁ / (c₁ * c₂ / 2)) ^ 2)) ^ (-(1 / 2 : ℝ)), 2 * Cu,
    max (max x₁ x₂) (max xu (Real.exp (Real.exp 1))), by positivity, by positivity,
    fun X μ hX x hx => ?_⟩
  -- `log log x ≥ 1`
  have hxe : Real.exp (Real.exp 1) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hΛ1 : 1 ≤ Real.log (Real.log x) := by
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
    have h1 : Real.exp 1 ≤ Real.log x := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) hxe
    have h2 : Real.log (Real.exp 1) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hL0 : 0 ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  refine ⟨?_, ?_⟩
  · exact half_final_arith hc₁.le hL0 (by ring)
      (hx₁ X μ hX x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx))
      (hx₂ X μ hX x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx))
      (mul_exp_neg_half_le_of_sq_le hC₁.le hd0 hV1 (le_max_right _ _))
  · have h := hup X μ hX x (1 / 2) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
      (by norm_num) le_rfl
    have hS : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * (1 / 2 : ℝ)) ∂μ)
        = ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
      simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    rw [hS] at h
    have hT := mul_one_add_half_sqrt_rpow_le hΛ1
    nlinarith [mul_le_mul_of_nonneg_left hT hCu.le]

end RMF
