/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LowerFixedQ

/-!
# The weighted sum at `q = ½`: the reduction

The first step of the lower bound `E|S(x)| ≫ (log log x)^{3/4}`, `S(x) = ∑_{n≤x} f(n)/√n` (the
`q = ½` case of Theorem 1.2 of the paper): Gerspach's Proposition 6 (arXiv:1909.10224) at
`α = 1` with the weight `|σ+it|^{-2}` kept
(`RMF.exists_le_integral_rpow_weightedRademacherSum_euler_full`, over the whole line and with one
Euler product over the primes up to `x`), at `q = ½`, with the subtracted term bounded:

`c (log x)^{-1/2} E[(∫_ℝ |F(½+2V/log x+it)|²/|2V/log x+it|² dt)^{1/2}]`
`  - C e^{-V/2} (log log x)^{3/4} ≤ E|S(x)|`

(`RMF.exists_le_integral_norm_weightedRademacherSum_half_line`), with `c, C` independent of `V`
and `x`, and the threshold on `x` depending on `V`.  The main term is `≫ V^{-1/2}(log log x)^{3/4}`
by `RMF.exists_le_integral_sqrt_lineDiv_half`; then `V` a large constant absorbs the subtracted
term.

## The subtracted term

`∫_ℝ |F(½+σ+it)/(σ+it)|² dt` decreases in `σ` (`RMF.integral_lineDiv_le_of_le`), so at
`σ = V/log x ≥ 1/log x` it is at most its value at `1/log x`.  There the upper bound machinery's
own target, `RMF.exists_const_integral_rpow_lineDiv_le_target_rademacher`, holds on the whole
range `0 < q ≤ ½`, and it applies at `y = ⌊x⌋` with the parameters of
`RMF.eventually_exists_mesoParams_floor`.  At `q = ½` its target `Λ(1+(1-q)√Λ)^{-q}` is at most
`2Λ^{3/4}`, `Λ = log log x`: every scale contributes, which is why the exponent is `3/4`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`Z` at `y = ⌊x⌋` and `σ = 1/log x`, against the non-sharp target, on `0 < q ≤ ½`.**
`E[((log ⌊x⌋)^{-1} ∫_ℝ |F(½+σ+it)|²/|σ+it|² dt)^q] ≤ C Λ(1+(1-q)√Λ)^{-q}`, `Λ = log log x`.
`RMF.exists_const_integral_rpow_lineDiv_le_target_rademacher` read at `y = ⌊x⌋`; its one extra
condition, `(σ log y)⁻¹ ≤ J^{3/2}`, follows from `(σ log y)⁻¹ ≤ 8Λ`, `J ≥ Λ/2` and `Λ ≥ 512`.  The
twin of `RMF.exists_const_integral_rpow_lineDiv_floor_le`, which is sharp but excludes `q = ½`. -/
theorem exists_const_integral_rpow_lineDiv_floor_le_target :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x q : ℝ, x₀ ≤ x → 0 < q → q ≤ 1 / 2 →
          (∫ ω, ((Real.log (⌊x⌋₊ : ℝ))⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                  ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
                / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
            ≤ C * (Real.log (Real.log x)
                * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)) := by
  obtain ⟨yb, K, hK, HT⟩ := exists_const_integral_rpow_lineDiv_le_target_rademacher (Ω := Ω)
  obtain ⟨x₂, hev⟩ := Filter.eventually_atTop.1
    ((eventually_exists_mesoParams_floor 0).and (Filter.eventually_ge_atTop (yb + 1)))
  refine ⟨4 * K, x₂, by positivity, fun X μ hX x q hx hq0 hq2 => ?_⟩
  obtain ⟨⟨J, M, hy2, hσ0, hσy, hJ1, hJle, hJw, hM1, hM, hJlo, hJhi, hLLhalf, h8S, -, -, hΛ⟩,
    hxb⟩ := hev x hx
  have hyb : yb ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  -- `log ⌊x⌋ ≥ 1`, since `log log ⌊x⌋ ≥ Λ/2 > 0`
  have hlogy1 : 1 ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    by_contra h
    have hlt : Real.log ((⌊x⌋₊ : ℕ) : ℝ) < 1 := not_le.mp h
    have hlogy0 : 0 ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ ⌊x⌋₊ by omega))
    have := Real.log_nonpos hlogy0 hlt.le
    linarith
  -- `(σ log y)⁻¹ ≤ 8Λ ≤ J^{3/2}`
  have hσJ : (1 / Real.log x * Real.log ((⌊x⌋₊ : ℕ) : ℝ))⁻¹ ≤ (J : ℝ) ^ (3 / 2 : ℝ) := by
    have hJ256 : (256 : ℝ) ≤ (J : ℝ) := by linarith
    have hJ0 : (0 : ℝ) < (J : ℝ) := by linarith
    have h32 : (J : ℝ) ^ (3 / 2 : ℝ) = (J : ℝ) * Real.sqrt J := by
      have h : (J : ℝ) ^ (1 : ℝ) * (J : ℝ) ^ (1 / 2 : ℝ) = (J : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add hJ0]
        norm_num
      rw [← h, Real.rpow_one, Real.sqrt_eq_rpow]
    have hsJ : (16 : ℝ) ≤ Real.sqrt J := by
      rw [show (16 : ℝ) = Real.sqrt 256 by
        rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hJ256
    rw [h32]
    nlinarith [h8S, hJlo, hsJ, hJ0]
  have hZ := HT X μ hX (1 / Real.log x) q ⌊x⌋₊ J M hyb hy2 hlogy1 hσ0 hσy hq0 hq2 hJ1 hJle hJw
    hM1 hM hσJ
  refine le_trans hZ ?_
  have h := target_le_of_bounds (J := J) (Λ := Real.log (Real.log x)) (by linarith) hq0.le
    (by linarith) hJlo hJhi
  nlinarith [h, hK.le]

/-- At `q = ½` the target is `≪ Λ^{3/4}`: `Λ(1+√Λ/2)^{-1/2} ≤ 2Λ^{3/4}` for `Λ ≥ 1`. -/
lemma mul_one_add_half_sqrt_rpow_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    Λ * (1 + (1 - 1 / 2) * Real.sqrt Λ) ^ (-(1 / 2 : ℝ)) ≤ 2 * Λ ^ (3 / 4 : ℝ) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hb : (1 + (1 - 1 / 2) * Real.sqrt Λ) ^ (-(1 / 2 : ℝ)) ≤ 2 * Λ ^ (-((1 / 2 : ℝ) / 2)) :=
    rpow_neg_le_of_sqrt_le hΛ (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith [Real.sqrt_nonneg Λ])
  have hsplit : Λ * Λ ^ (-((1 / 2 : ℝ) / 2)) = Λ ^ (3 / 4 : ℝ) := by
    have he : (1 : ℝ) + -((1 / 2 : ℝ) / 2) = 3 / 4 := by norm_num
    rw [← he, Real.rpow_add hΛ0, Real.rpow_one]
  calc Λ * (1 + (1 - 1 / 2) * Real.sqrt Λ) ^ (-(1 / 2 : ℝ))
      ≤ Λ * (2 * Λ ^ (-((1 / 2 : ℝ) / 2))) := mul_le_mul_of_nonneg_left hb hΛ0.le
    _ = 2 * (Λ * Λ ^ (-((1 / 2 : ℝ) / 2))) := by ring
    _ = 2 * Λ ^ (3 / 4 : ℝ) := by rw [hsplit]

/-- The arithmetic of the `q = ½` reduction: the subtracted term, pulled through
`E[J₂^{1/2}] ≤ L^{1/2} E[Z^{1/2}]` and `E[Z^{1/2}] ≤ 2KΛ^{3/4}`, and the error term, against
`L^{-1/2} ≤ e^{-V/2}Λ^{3/4}`. -/
lemma half_reduction_arith {ES EJ₁ EJ₂ EZ L Λ V c₀ C₀ K : ℝ} (hL : 0 < L) (hC₀ : 0 ≤ C₀)
    (hred : c₀ * L ^ (-(1 / 2 : ℝ)) * EJ₁ - C₀ * Real.exp (-(V / 2)) * L ^ (-(1 / 2 : ℝ)) * EJ₂
        - C₀ * L ^ (-(1 / 2 : ℝ)) ≤ ES)
    (hJ₂ : EJ₂ ≤ L ^ (1 / 2 : ℝ) * EZ) (hZ : EZ ≤ K * (2 * Λ ^ (3 / 4 : ℝ)))
    (herr : L ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-(V / 2)) * Λ ^ (3 / 4 : ℝ)) :
    c₀ * L ^ (-(1 / 2 : ℝ)) * EJ₁ - C₀ * (2 * K + 1) * Real.exp (-(V / 2)) * Λ ^ (3 / 4 : ℝ)
      ≤ ES := by
  have hLL : L ^ (-(1 / 2 : ℝ)) * L ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hL]
    norm_num
  have hcoef : 0 ≤ C₀ * Real.exp (-(V / 2)) * L ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg hC₀ (Real.exp_pos _).le) (Real.rpow_nonneg hL.le _)
  have h1 := mul_le_mul_of_nonneg_left hJ₂ hcoef
  have e1 : C₀ * Real.exp (-(V / 2)) * L ^ (-(1 / 2 : ℝ)) * (L ^ (1 / 2 : ℝ) * EZ)
      = C₀ * Real.exp (-(V / 2)) * EZ := by
    rw [show C₀ * Real.exp (-(V / 2)) * L ^ (-(1 / 2 : ℝ)) * (L ^ (1 / 2 : ℝ) * EZ)
        = C₀ * Real.exp (-(V / 2)) * (L ^ (-(1 / 2 : ℝ)) * L ^ (1 / 2 : ℝ)) * EZ by ring, hLL,
      mul_one]
  have hce : 0 ≤ C₀ * Real.exp (-(V / 2)) := mul_nonneg hC₀ (Real.exp_pos _).le
  have h2 := mul_le_mul_of_nonneg_left hZ hce
  have h3 := mul_le_mul_of_nonneg_left herr hC₀
  nlinarith [h1, e1, h2, h3]

/-- **The reduction at `q = ½`, with the subtracted term bounded.**  For `V ≥ 1` and `x ≥ x₀(V)`,
`c(log x)^{-1/2}E[(∫_ℝ |F(½+σ+it)/(σ+it)|² dt)^{1/2}] - Ce^{-V/2}(log log x)^{3/4} ≤ E|S(x)|`
at `σ = 2V/log x`, `F` over the primes up to `x`, with `c, C > 0` independent of `V` and `x`.  So
a bound `≫ V^{-1/2}(log log x)^{3/4}` on the main term absorbs the subtracted one once `V` is a
large constant.  The reduction's own error `C(log x)^{-1/2}` is absorbed once `log x ≥ e^V`. -/
theorem exists_le_integral_norm_weightedRademacherSum_half_line :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ V : ℝ, 1 ≤ V → ∃ x₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ → ∀ x : ℝ, x₀ ≤ x →
        c * Real.log x ^ (-(1 / 2 : ℝ)) * (∫ ω, (∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                ((1 / 2 : ℂ) + ((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
              / (((2 * V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ (1 / 2 : ℝ) ∂μ)
          - C * Real.exp (-(V / 2)) * Real.log (Real.log x) ^ (3 / 4 : ℝ)
        ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
  obtain ⟨c₀, C₀, x₁, hc₀, hC₀, hred⟩ :=
    exists_le_integral_rpow_weightedRademacherSum_euler_full (Ω := Ω)
  obtain ⟨K, x₂, hK, hup⟩ := exists_const_integral_rpow_lineDiv_floor_le_target (Ω := Ω)
  refine ⟨c₀, C₀ * (2 * K + 1), hc₀, by positivity, fun V hV => ?_⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (max (max x₁ x₂) 2)).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop (max (3 * V + 3) (Real.exp V))).and
        ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1)))
  refine ⟨x₀, fun X μ hX x hx => ?_⟩
  obtain ⟨hxm, hLm, hΛ1⟩ := hx₀ x hx
  have hΛ1' : (1 : ℝ) ≤ Real.log (Real.log x) := hΛ1
  haveI := hX.isProbabilityMeasure
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxm
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxm
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hxm
  have hlogV : 3 * V + 3 ≤ Real.log x := le_trans (le_max_left _ _) hLm
  have hLe : Real.exp V ≤ Real.log x := le_trans (le_max_right _ _) hLm
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos V) hLe
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hL'0 : 0 < Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hL'L : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
  -- the reduction, at `q = ½`
  have h1 := hred X μ hX V x (1 / 2) (by linarith) hx₁ hlogV (by norm_num) le_rfl
  rw [show -(V * (1 / 2 : ℝ)) = -(V / 2) by ring] at h1
  have hS : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * (1 / 2 : ℝ)) ∂μ)
      = ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ := by
    simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  rw [hS] at h1
  -- the subtracted term: down to `σ = 1/log x`, then the upper-bound machinery
  have h4 := integral_rpow_lineDiv_le_of_le hX hy2 (σ₁ := 1 / Real.log x)
    (σ₂ := V / Real.log x) (by positivity) (div_le_div_of_nonneg_right hV hL0.le)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h6 := integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
    (J := fun ω => ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
        / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
    hL'0 hL'L (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun ω => integral_nonneg fun t => sq_nonneg _)
  have h5 := hup X μ hX x (1 / 2) hx₂ (by norm_num) le_rfl
  have hT := mul_one_add_half_sqrt_rpow_le hΛ1'
  have hZ := le_trans h5 (mul_le_mul_of_nonneg_left hT hK.le)
  -- the error term: `(log x)^{-1/2} ≤ e^{-V/2} ≤ e^{-V/2}Λ^{3/4}`
  have herr : Real.log x ^ (-(1 / 2 : ℝ))
      ≤ Real.exp (-(V / 2)) * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
    have he : Real.log x ^ (-(1 / 2 : ℝ)) ≤ Real.exp V ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos V) hLe (by norm_num)
    have he' : Real.exp V ^ (-(1 / 2 : ℝ)) = Real.exp (-(V / 2)) := by
      rw [← Real.exp_mul]
      ring_nf
    have hΛ34 : (1 : ℝ) ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) :=
      Real.one_le_rpow hΛ1' (by norm_num)
    rw [he'] at he
    nlinarith [Real.exp_pos (-(V / 2))]
  exact half_reduction_arith hL0 hC₀.le h1 (le_trans h4 h6) hZ herr

end RMF
