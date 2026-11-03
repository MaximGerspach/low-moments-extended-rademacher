/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BandTailAssembly

/-!
# The truncation bound

For `½ < q ≤ 1`, `1 ≤ y < z ≤ x`, `κ = log z/log y ≥ e` (`κ = log z` if `y = 1`) and
`V = log x/log z ≥ C₀ log κ` with `C₀ = 2`,

`E|𝒯_{y,z}(x)|^{2q} ≪ κ^{q(2q-1)}·b(min{1/(2q-1), log κ})`,

for the bands `y ≥ 2` (`RMF.exists_const_integral_rpow_norm_blockTruncationTail_le`) and for the
bottom band `y = 1` (`RMF.exists_const_integral_rpow_norm_truncationTail_le`).  Both come from one
bound for any atom bound `E|T(w)|² ≤ M·w^{-1/log z}`,
`RMF.exists_integral_rpow_norm_blockTruncationTail_le_of_atom`: the conditioning
(`RMF.integral_rpow_norm_blockTruncationTail_le`), the atom `E|T(x)|^{2q} ≤ 1 + M·e^{-V}` by
Jensen, and the rough sum (`RMF.exists_integral_rpow_sum_blockTailTerm_le`).  The band tail's atom
is `M = e^{45}κ` (`M = e^{18}·log z` on the bottom band), `κ·e^{-V}(V+1)² ≤ 18` for
`V ≥ 2 log κ` (`RMF.mul_exp_neg_mul_add_one_sq_le`), and the line functional is bounded by
`RMF.exists_const_integral_rpow_lineDiv_band_le_rademacher`.  The smoothing is at `η = 1/V`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The arithmetic of `C₀ = 2`.**  For `κ > 0` and `V ≥ max(0, 2 log κ)`: `κ·e^{-V}·(V+1)² ≤ 18`,
since `κ ≤ e^{V/2}` and `(V+1)² ≤ 18·e^{V/2}` (`1 + u + u²/2 ≤ e^u` at `u = V/2`). -/
lemma mul_exp_neg_mul_add_one_sq_le {κ V : ℝ} (hκ : 0 < κ) (hV0 : 0 ≤ V)
    (hV : 2 * Real.log κ ≤ V) : κ * Real.exp (-V) * (V + 1) ^ 2 ≤ 18 := by
  have h1 : κ * Real.exp (-V) ≤ Real.exp (-(V / 2)) := by
    rw [← Real.exp_log hκ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h2 : (V + 1) ^ 2 ≤ 18 * Real.exp (V / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ V / 2 by linarith)
    nlinarith [sq_nonneg V]
  have h3 : Real.exp (-(V / 2)) * Real.exp (V / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc κ * Real.exp (-V) * (V + 1) ^ 2 ≤ Real.exp (-(V / 2)) * (18 * Real.exp (V / 2)) :=
        mul_le_mul h1 h2 (sq_nonneg _) (Real.exp_pos _).le
    _ = 18 := by rw [mul_left_comm, h3, mul_one]

/-- **The truncation bound from an atom bound.**  For `0 ≤ q ≤ 1`, `3 ≤ z ≤ x`, `y ≤ z`,
`2c·log z = 1` and `E|T(w)|² ≤ M·w^{-1/log z}` for every `w > 0`, with `V = log x/log z`,
`E|𝒯_{y,z}(x)|^{2q} ≤ K·(E[Z^q] + 1 + M·e^{-V}(V+1)²)`,
`Z = (log z)⁻¹∫_ℝ‖F_{y,z}(½-c+it)/(c+it)‖²dt`; `K` is independent of `X`, `μ`, `q`, `M`, `c`,
`x`, `y`, `z` (`Ω` is fixed).  The conditioning leaves the atom,
`E|T(x)|^{2q} ≤ (E|T(x)|²)^q ≤ 1 + M·e^{-V}` by Jensen, and the rough sum
(`RMF.exists_integral_rpow_sum_blockTailTerm_le`). -/
theorem exists_integral_rpow_norm_blockTruncationTail_le_of_atom :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (q M c x : ℝ) (y z : ℕ), 0 ≤ q → q ≤ 1 → 0 ≤ M → 3 ≤ z → y ≤ z → (z : ℝ) ≤ x →
        2 * c * Real.log z = 1 →
        (∀ w : ℝ, 0 < w →
          (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
            ≤ M * w ^ (-(Real.log z)⁻¹)) →
        (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
            ^ (2 * q) ∂μ)
          ≤ K * ((∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                      (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                    / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
              + 1 + M * Real.exp (-(Real.log x / Real.log z))
                  * (Real.log x / Real.log z + 1) ^ 2) := by
  obtain ⟨K, hK, hN9c⟩ := exists_integral_rpow_sum_blockTailTerm_le
  refine ⟨K + 1, by linarith, ?_⟩
  intro X μ hX q M c x y z hq0 hq1 hM hz hyz hzx hc hatom
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  -- the conditioning
  have hcond := integral_rpow_norm_blockTruncationTail_le hX hyz hx1 hq0 hq1
  -- the atom, by Jensen
  have hxV : x ^ (-(Real.log z)⁻¹) = Real.exp (-(Real.log x / Real.log z)) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hatomq : (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ) ≤ 1 + M * Real.exp (-(Real.log x / Real.log z)) := by
    have hmeas : Measurable fun ω =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2 :=
      ((measurable_smoothAlgebra_blockTailSum y z x).mono (smoothAlgebra_le hX z)
        le_rfl).norm.pow_const 2
    have hint : Integrable (fun ω =>
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2) μ := by
      refine (memLp_top_of_bound hmeas.aestronglyMeasurable ((primorial z : ℝ) ^ 2)
        ?_).integrable le_top
      filter_upwards [ae_norm_blockTailSum_le hRa y z x] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hω 2
    have hB : (∫ ω,
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2 ∂μ)
        ≤ M * Real.exp (-(Real.log x / Real.log z)) := by
      rw [← hxV]
      exact hatom x hx0
    have hpow : ∀ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
          ^ (2 * q)
        = (‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖ ^ 2) ^ q := by
      intro ω
      rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
    simp_rw [hpow]
    refine le_trans (integral_rpow_le_rpow_of_integral_le hq0 hq1
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint hB) ?_
    exact rpow_le_one_add (mul_nonneg hM (Real.exp_pos _).le) hq0 hq1
  -- the rough sum
  have hS := hN9c Ω X μ hX q M c x y z hq0 hq1 hM hz hzx hc hatom
    (({r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}).erase 1)
    (fun r hr => ((Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).2).1)
    (fun r hr => by
      have h1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).1
      have h2 := Finset.ne_of_mem_erase hr
      omega)
    (fun r hr => by
      have h := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).2
      exact le_trans (Nat.cast_le.2 h) (Nat.floor_le hx0.le))
  -- assemble
  have hV0 : 0 ≤ Real.log x / Real.log z := div_nonneg (Real.log_nonneg hx1) hlogz.le
  have hMe0 : 0 ≤ M * Real.exp (-(Real.log x / Real.log z)) := mul_nonneg hM (Real.exp_pos _).le
  have hMV : M * Real.exp (-(Real.log x / Real.log z))
      ≤ M * Real.exp (-(Real.log x / Real.log z)) * (Real.log x / Real.log z + 1) ^ 2 :=
    le_mul_of_one_le_right hMe0 (by nlinarith [hV0])
  have hIZ0 : 0 ≤ ∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 hlogz.le) (integral_nonneg fun t => sq_nonneg _)) q
  linarith

/-- **The truncation bound for a band**, for `½ < q ≤ 1` and `C₀ = 2`: a constant
`C`, independent of `q`, `y`, `z`, `x`, `X` and `μ`, such that for `y ≥ 2`, `κ = log z/log y ≥ e`,
`z ≤ x` and `V = log x/log z ≥ 2 log κ`,

`E|𝒯_{y,z}(x)|^{2q} ≤ C·κ^{q(2q-1)}·b(min{1/(2q-1), log κ})`.

`RMF.exists_integral_rpow_norm_blockTruncationTail_le_of_atom` at the atom `M = e^{45}κ`
(`RMF.integral_normSq_blockTailSum_le`) and `c = 1/(2 log z)`; the band's line integral
(`RMF.exists_const_integral_rpow_lineDiv_band_le_rademacher`) for `E[Z^q]`;
`M·e^{-V}(V+1)² ≤ 18e^{45}` (`RMF.mul_exp_neg_mul_add_one_sq_le`); and the right side is at least
`½` (`RMF.half_le_rpow_mul_ballotFactor`).  `κ ≥ e` and `y ≥ 2` give `z ≥ 4`. -/
theorem exists_const_integral_rpow_norm_blockTruncationTail_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (q : ℝ) (y z : ℕ) (x : ℝ), 1 / 2 < q → q ≤ 1 → 2 ≤ y →
        Real.exp 1 ≤ Real.log z / Real.log y → (z : ℝ) ≤ x →
        2 * Real.log (Real.log z / Real.log y) ≤ Real.log x / Real.log z →
        (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * ((Real.log z / Real.log y) ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y)))) := by
  obtain ⟨K, hK, hcore⟩ := exists_integral_rpow_norm_blockTruncationTail_le_of_atom (Ω := Ω)
  obtain ⟨CB, hCB, hB⟩ := exists_const_integral_rpow_lineDiv_band_le_rademacher (Ω := Ω)
  refine ⟨2 * K * (1 + 18 * Real.exp 45) + K * CB, by positivity, ?_⟩
  intro X μ hX q y z x hq2 hq1 hy hκ hzx hV
  have hq0 : 0 ≤ q := by linarith
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  -- `log z ≥ e·log y ≥ 2 log 2 = log 4`, so `z ≥ 4`, and `y ≤ z`
  have hlogz : Real.exp 1 * Real.log y ≤ Real.log z := (le_div_iff₀ hlogy).1 hκ
  have hlog2 : Real.log 2 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) hy2
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 ≤ Real.log (z : ℝ) := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h := mul_le_mul he2 hlog2 hl2.le (by linarith)
    linarith
  have hlogz0 : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog4
  have hz0 : (0 : ℝ) < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogz0
      exact absurd hlogz0 (lt_irrefl 0)
    · exact_mod_cast h
  have hz4 : (4 : ℝ) ≤ z := (Real.log_le_log_iff (by norm_num) hz0).1 hlog4
  have hz3 : 3 ≤ z := by exact_mod_cast (show (3 : ℝ) ≤ z by linarith)
  have hyz : y ≤ z := by
    have h := mul_le_mul_of_nonneg_right he2 hlogy.le
    have h1 : Real.log (y : ℝ) ≤ Real.log z := by linarith
    exact_mod_cast (Real.log_le_log_iff (by linarith) hz0).1 h1
  -- `κ` and `c`
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.log z / Real.log y := ⟨_, rfl⟩
  rw [← hκdef] at hκ hV ⊢
  have hκ0 : 0 < κ := lt_of_lt_of_le (Real.exp_pos 1) hκ
  have hlogκ : 1 ≤ Real.log κ := by
    have h := Real.log_le_log (Real.exp_pos 1) hκ
    rwa [Real.log_exp] at h
  have hV0 : 0 ≤ Real.log x / Real.log z := by linarith
  have hc : 2 * (1 / (2 * Real.log z)) * Real.log z = 1 := by
    field_simp
  -- the core bound at the band tail's atom, and the band's line integral
  have h1 := hcore X μ hX q (Real.exp 45 * κ) (1 / (2 * Real.log z)) x y z hq0 hq1
    (mul_nonneg (Real.exp_pos 45).le hκ0.le) hz3 hyz hzx hc
    (fun w hw => by rw [hκdef]; exact integral_normSq_blockTailSum_le hX hy hyz hw)
  have h2 := hB X μ hX q (1 / (2 * Real.log z)) y z hq2 hq1 hy (by rw [← hκdef]; exact hκ) hc
  rw [← hκdef] at h2
  have h3 : Real.exp 45 * κ * Real.exp (-(Real.log x / Real.log z))
      * (Real.log x / Real.log z + 1) ^ 2 ≤ 18 * Real.exp 45 := by
    have h := mul_exp_neg_mul_add_one_sq_le hκ0 hV0 hV
    calc Real.exp 45 * κ * Real.exp (-(Real.log x / Real.log z))
          * (Real.log x / Real.log z + 1) ^ 2
        = Real.exp 45 * (κ * Real.exp (-(Real.log x / Real.log z))
          * (Real.log x / Real.log z + 1) ^ 2) := by ring
      _ ≤ Real.exp 45 * 18 := mul_le_mul_of_nonneg_left h (Real.exp_pos 45).le
      _ = 18 * Real.exp 45 := by ring
  have hR := half_le_rpow_mul_ballotFactor hq2 hq1 hκ
  have e1 := mul_le_mul_of_nonneg_left h2 hK.le
  have e2 := mul_le_mul_of_nonneg_left h3 hK.le
  have e3 := mul_le_mul_of_nonneg_left hR
    (show (0 : ℝ) ≤ 2 * K * (1 + 18 * Real.exp 45) by positivity)
  linarith

/-- **The truncation bound for the bottom band** `y = 1`, for `½ < q ≤ 1` and
`C₀ = 2`: a constant `C`, independent of `q`, `z`, `x`, `X` and `μ`, such that for
`κ = log z ≥ e`, `z ≤ x` and `V = log x/log z ≥ 2 log log z`,

`E|𝒯_z(x)|^{2q} ≤ C·(log z)^{q(2q-1)}·b(min{1/(2q-1), log log z})`.

The band `(0, z]` of `RMF.exists_integral_rpow_norm_blockTruncationTail_le_of_atom`
(`RMF.blockTruncationTail_zero`), at the atom `M = e^{18}·log z`
(`RMF.integral_normSq_blockTailSum_zero_le`), with the line integral of the bottom band
(`RMF.exists_const_integral_rpow_lineDiv_primesBelow_le_rademacher`), the product over the primes
up to `z` being the band's (`RMF.randomEulerProductIco_one`). -/
theorem exists_const_integral_rpow_norm_truncationTail_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (q : ℝ) (z : ℕ) (x : ℝ), 1 / 2 < q → q ≤ 1 → Real.exp 1 ≤ Real.log z → (z : ℝ) ≤ x →
        2 * Real.log (Real.log z) ≤ Real.log x / Real.log z →
        (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) z x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * ((Real.log z) ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z)))) := by
  obtain ⟨K, hK, hcore⟩ := exists_integral_rpow_norm_blockTruncationTail_le_of_atom (Ω := Ω)
  obtain ⟨CB, hCB, hB⟩ := exists_const_integral_rpow_lineDiv_primesBelow_le_rademacher (Ω := Ω)
  refine ⟨2 * K * (1 + 18 * Real.exp 18) + K * CB, by positivity, ?_⟩
  intro X μ hX q z x hq2 hq1 hκ hzx hV
  have hq0 : 0 ≤ q := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hlogz0 : 0 < Real.log (z : ℝ) := by linarith [Real.exp_pos 1]
  have hz0 : (0 : ℝ) < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogz0
      exact absurd hlogz0 (lt_irrefl 0)
    · exact_mod_cast h
  have hz3 : 3 ≤ z := by
    have h3 : Real.log 3 ≤ Real.log (z : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    exact_mod_cast (Real.log_le_log_iff (by norm_num) hz0).1 h3
  have hz2 : 2 ≤ z := by omega
  have hV0 : 0 ≤ Real.log x / Real.log z := by
    have h := Real.log_le_log (Real.exp_pos 1) hκ
    rw [Real.log_exp] at h
    linarith
  have hc : 2 * (1 / (2 * Real.log z)) * Real.log z = 1 := by
    field_simp
  -- the core bound at the band `(0, z]`, whose truncation error is `truncationTail`
  have h1 := hcore X μ hX q (Real.exp 18 * Real.log z) (1 / (2 * Real.log z)) x 0 z hq0 hq1
    (mul_nonneg (Real.exp_pos 18).le hlogz0.le) hz3 (Nat.zero_le z) hzx hc
    (fun w hw => integral_normSq_blockTailSum_zero_le hX hz2 hw)
  simp only [blockTruncationTail_zero, zero_add, randomEulerProductIco_one] at h1
  have h2 := hB X μ hX q (1 / (2 * Real.log z)) z hq2 hq1 hκ hc
  have h3 : Real.exp 18 * Real.log z * Real.exp (-(Real.log x / Real.log z))
      * (Real.log x / Real.log z + 1) ^ 2 ≤ 18 * Real.exp 18 := by
    have h := mul_exp_neg_mul_add_one_sq_le hlogz0 hV0 hV
    calc Real.exp 18 * Real.log z * Real.exp (-(Real.log x / Real.log z))
          * (Real.log x / Real.log z + 1) ^ 2
        = Real.exp 18 * (Real.log z * Real.exp (-(Real.log x / Real.log z))
          * (Real.log x / Real.log z + 1) ^ 2) := by ring
      _ ≤ Real.exp 18 * 18 := mul_le_mul_of_nonneg_left h (Real.exp_pos 18).le
      _ = 18 * Real.exp 18 := by ring
  have hR := half_le_rpow_mul_ballotFactor hq2 hq1 hκ
  have e1 := mul_le_mul_of_nonneg_left h2 hK.le
  have e2 := mul_le_mul_of_nonneg_left h3 hK.le
  have e3 := mul_le_mul_of_nonneg_left hR
    (show (0 : ℝ) ≤ 2 * K * (1 + 18 * Real.exp 18) by positivity)
  linarith

end RMF
