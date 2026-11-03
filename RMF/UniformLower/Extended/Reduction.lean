/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Extended.Discrepancy
import RMF.Weighted.ExtendedLowerParseval

/-!
# The extended sum's explicit lower bound: the reduction

The reduction for `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)` with the weighted sum's constants
(`RMF.le_integral_rpow_weightedRademacherSum_euler_full_of_windowCovering`).  With
`J_Y(σ) = ∫_ℝ |F^e(½+σ+it)/(½+σ+it)|² dt` (`RMF.lineDivSq`, `F^e` over the primes up to `x`),
for `x ≥ e^{300}` with the window covering, `log x ≥ 3V + 3` and `0 < q ≤ ½`,

`cRed(q)(log x)^{-q}E[J_Y(2V/log x)^q] - cJ(q)e^{-Vq}(log x)^{-q}E[J_Y(V/log x)^q]`
`  - cErrD(q)(log x)^{-q} ≤ E|Y(x)|^{2q}`

(`RMF.le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering`).  The chain is the
weighted one on the unnormalised sum `∑_{n≤x} X^e(n)`, divided by `x^q` at the end:

* symmetrisation and Khintchine, `RMF.khintchine_rough_extended` (`q ≤ ½`), with the weighted
  sum's factor `3^{-(1-q)}2^{-(1-2q)}`;
* L4, L5 and L8 from `RMF.IsWindowCovering`, pointwise and for any arithmetic function
  (`RMF.sum_normSq_ge_of_windowCovering`), and L9 with `E[D] ≤ 2x`
  (`RMF.integral_sum_discrepancy_le_sqrt_extended`):
  `(x/(8 log x))^qE[M^q] - (2x/log x)^q ≤ E[(∑_p |∑_{m≤x/p} X^e(m)|²)^q]`
  (`RMF.meanSquare_le_sum_extended_of_windowCovering`),
  `M = ∫_1^{√x/(1+1/log x)} |∑_{n≤z} X^e(n)|² dz/z²`;
* Parseval on the full line, `(2π)⁻¹J_Y(2V/log x) - π⁻¹e^{-V}J_Y(V/log x) ≤ M`
  (`RMF.extendedMeanSquare_ge_line_full`: `RMF.extendedMeanSquare_ge_line` before its cut to
  `|t| < 1`).

Divided by `x^q`, `∑_p |∑_{m≤x/p} X^e(m)|²/x = ∑_p p⁻¹|Y(x/p)|²`, and the weighted arithmetic
`RMF.reduction_arith_explicit'` applies verbatim (`RMF.reduction_arith_extended`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Steps L4, L5 and L8 from the window covering -/

omit [MeasurableSpace Ω] in
/-- **Steps L4, L5 and L8 with the window covering supplied, unnormalised**: for any arithmetic
function `g`, `x ≥ 4` with `RMF.IsWindowCovering x` and `S` a set of primes up to `x` containing
those of `(√x, x]`,
`(x/(8 log x))∫_1^{√x/(1+1/log x)} |∑_{n≤z} g(n)|² dz/z² - D/log x ≤ ∑_{p∈S} |∑_{m≤x/p} g(m)|²`,
`D` the smoothing discrepancy.  The unnormalised twin of
`RMF.sum_normSq_ge_weighted_of_windowCovering`; `RMF.sum_normSq_ge` has an existential `x₀`. -/
theorem sum_normSq_ge_of_windowCovering (g : Ω → ArithmeticFunction ℂ) (ω : Ω) {x : ℝ}
    (hx : 4 ≤ x) (hwin : IsWindowCovering x) (S : Finset ℕ) (hSp : ∀ p ∈ S, Nat.Prime p)
    (hSx : ∀ p ∈ S, (p : ℝ) ≤ x)
    (hS : ∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) :
    x / (8 * Real.log x) * (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
          ‖randomSum g z ω‖ ^ 2 / z ^ 2)
        - (∑ p ∈ S, Real.log p * (Real.log x / p *
            ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
              discrepancy g x p ω t)) / Real.log x
      ≤ ∑ p ∈ S, ‖randomSum g (x / p) ω‖ ^ 2 := by
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  -- L4: `log p ≤ log x`
  have hL4 : ∑ p ∈ S, Real.log p * ‖randomSum g (x / p) ω‖ ^ 2
      ≤ Real.log x * ∑ p ∈ S, ‖randomSum g (x / p) ω‖ ^ 2 :=
    sum_log_mul_le_log_mul_sum (x := x) (by linarith) hSx
      (v := fun p => ‖randomSum g (x / p) ω‖ ^ 2) fun p => by positivity
  -- L5: smoothing, prime by prime, weighted by `log p`
  have hL5 := sum_log_smoothing_bound (f := g) (X := Real.log x) hx0.le hlog0 hSp ω
  -- L8: the covering
  have hcover := hwin (fun t => ‖randomSum g (x / t) ω‖ ^ 2) (fun t => by positivity)
    (fun c d hc => integrableOn_normSq_randomSum_div g hx0.le hc ω) S hSp hS
  -- the substitution `z = x/t`
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have ha0 : (0 : ℝ) < Real.sqrt x * (1 + 1 / Real.log x) := by positivity
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hax : Real.sqrt x * (1 + 1 / Real.log x) ≤ x := by nlinarith
  have h1 : x / x = 1 := div_self hx0.ne'
  have h2 : x / (Real.sqrt x * (1 + 1 / Real.log x)) = Real.sqrt x / (1 + 1 / Real.log x) := by
    field_simp
    nlinarith
  have hsubst : (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2)
      = x * ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
          ‖randomSum g z ω‖ ^ 2 / z ^ 2 := by
    have h := setIntegral_comp_div hx0 ha0 hax (fun z => ‖randomSum g z ω‖ ^ 2)
    rw [h1, h2] at h
    exact h
  rw [hsubst] at hcover
  -- the atoms: `field_simp` must not reach inside the integrals
  set M : ℝ := ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
    ‖randomSum g z ω‖ ^ 2 / z ^ 2 with hMdef
  set Dsum : ℝ := ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t) with hDdef
  set Wsum : ℝ := ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2) with hWdef
  set A : ℝ := ∑ p ∈ S, ‖randomSum g (x / p) ω‖ ^ 2 with hAdef
  -- `xM/8 ≤ W/4 ≤ ∑ log p·|…|² + D ≤ log x·A + D`
  have hkey : x * M / 8 - Dsum ≤ A * Real.log x := by linarith
  have e : x / (8 * Real.log x) * M - Dsum / Real.log x = (x * M / 8 - Dsum) / Real.log x := by
    field_simp
  rw [e, div_le_iff₀ hlog0]
  exact hkey

/-! ### Step L9: the `q`-th moment -/

/-- **L9 for the extended sum with the window covering supplied**: for `x ≥ e^{300}` with
`RMF.IsWindowCovering x`, `0 ≤ q ≤ 1` and `S` the primes of `(√x, x]`,
`(x/(8 log x))^qE[M^q] - (2x/log x)^q ≤ E[(∑_{p∈S} |∑_{m≤x/p} X^e(m)|²)^q]`,
`M = ∫_1^{√x/(1+1/log x)} |∑_{n≤z} X^e(n)|² dz/z²`: `RMF.sum_normSq_ge_of_windowCovering` and
`E[D] ≤ 2x` (`RMF.integral_sum_discrepancy_le_sqrt_extended`).  The twin of
`RMF.meanSquare_le_sum_weighted_of_windowCovering`; `RMF.meanSquare_le_sum_extended` has an
existential `x₀` and `40x`. -/
theorem meanSquare_le_sum_extended_of_windowCovering {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp 300 ≤ x)
    (hwin : IsWindowCovering x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ℕ)
    (hSp : ∀ p ∈ S, Nat.Prime p) (hSs : ∀ p ∈ S, Real.sqrt x < p) (hSx : ∀ p ∈ S, (p : ℝ) ≤ x)
    (hS : ∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) :
    (x / (8 * Real.log x)) ^ q
          * ∫ ω, (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
              ‖randomSum (fun ω => compMultExtension fun r => X r ω) z ω‖ ^ 2 / z ^ 2) ^ q ∂μ
        - (2 * x / Real.log x) ^ q
      ≤ ∫ ω, (∑ p ∈ S, ‖randomSum (fun ω => compMultExtension fun r => X r ω)
          (x / p) ω‖ ^ 2) ^ q ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (300 : ℝ)]) hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun r => X r ω with hgdef
  have hmeas : ∀ n : ℕ, Measurable fun ω => g ω n := fun n => hX.measurable_compMultExtension n
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖g ω n‖ ≤ 1 := fun n =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  have hSsub : S ⊆ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊ := fun p hp =>
    mem_largePrimeSet.2 ⟨⟨(Nat.floor_lt (Real.sqrt_nonneg x)).2 (hSs p hp),
      Nat.le_floor (hSx p hp)⟩, hSp p hp⟩
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  set M : Ω → ℝ := fun ω => ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z ^ 2 with hMdef
  set D : Ω → ℝ := fun ω => ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t) with hDdef
  set A : Ω → ℝ := fun ω => ∑ p ∈ S, ‖randomSum g (x / p) ω‖ ^ 2 with hAdef
  -- the pointwise inequality
  have hpt0 : ∀ ω, x / (8 * Real.log x) * M ω - D ω / Real.log x ≤ A ω := fun ω =>
    sum_normSq_ge_of_windowCovering g ω hx4 hwin S hSp hSx hS
  -- nonnegativity
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun z _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    refine Finset.sum_nonneg fun p _ => mul_nonneg (Real.log_natCast_nonneg p) ?_
    refine mul_nonneg (by positivity) ?_
    exact setIntegral_nonneg measurableSet_Ioc fun t _ => discrepancy_nonneg g x p ω t
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Finset.sum_nonneg fun p _ => by positivity
  have hP0 : ∀ ω, 0 ≤ x / (8 * Real.log x) * M ω := fun ω => mul_nonneg (by positivity) (hM0 ω)
  have hR0 : ∀ ω, 0 ≤ D ω / Real.log x := fun ω => div_nonneg (hD0 ω) hlog0.le
  -- integrability
  have hMi : Integrable M μ :=
    (integrable_meanSquare_prod_of hmeas hbd (c := 1) (d := w) le_rfl).integral_prod_left
  have hDi : Integrable D μ := integrable_extendedDiscrepancySum hX hx0.le hSp
  have hAi : Integrable A μ :=
    integrable_finsetSum _ fun p _ => integrable_normSq_randomSum_of hmeas hbd (x / p)
  have hPi : Integrable (fun ω => x / (8 * Real.log x) * M ω) μ := hMi.const_mul _
  have hRi : Integrable (fun ω => D ω / Real.log x) μ := hDi.div_const _
  have hPq := integrable_rpow_of_integrable hPi (Filter.Eventually.of_forall hP0) hq0 hq1
  have hRq := integrable_rpow_of_integrable hRi (Filter.Eventually.of_forall hR0) hq0 hq1
  have hAq := integrable_rpow_of_integrable hAi (Filter.Eventually.of_forall hA0) hq0 hq1
  -- the pointwise inequality, at the `q`-th power
  have hpt : ∀ ω, (x / (8 * Real.log x) * M ω) ^ q - (D ω / Real.log x) ^ q ≤ A ω ^ q :=
    fun ω => rpow_sub_rpow_le_of_sub_le (hP0 ω) (hR0 ω) (hA0 ω) (hpt0 ω) hq0 hq1
  have hmain : (∫ ω, (x / (8 * Real.log x) * M ω) ^ q ∂μ) - ∫ ω, (D ω / Real.log x) ^ q ∂μ
      ≤ ∫ ω, A ω ^ q ∂μ := by
    rw [← integral_sub hPq hRq]
    exact integral_mono (hPq.sub hRq) hAq hpt
  -- the two evaluations
  have hPval : (∫ ω, (x / (8 * Real.log x) * M ω) ^ q ∂μ)
      = (x / (8 * Real.log x)) ^ q * ∫ ω, M ω ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow (by positivity) (hM0 ω))
  have hRval : (∫ ω, (D ω / Real.log x) ^ q ∂μ) ≤ (2 * x / Real.log x) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hR0 ω)) hRi hRq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hR0) ?_ hq0
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_sum_discrepancy_le_sqrt_extended hX hx hSsub)
      hlog0.le
  rw [hPval] at hmain
  linarith

/-! ### Parseval on the full line -/

/-- **Parseval for the extended mean square on the full line.**  For Rademacher `X`, `V > 0`,
`x ≥ 4` and `log x ≥ 3V + 3`, almost surely
`(2π)⁻¹J_Y(2V/log x) - π⁻¹e^{-V}J_Y(V/log x) ≤ ∫_1^{√x/(1+1/log x)} |∑_{n≤z} X^e(n)|² dz/z²`,
`J_Y(σ) = ∫_ℝ |F^e(½+σ+it)/(½+σ+it)|² dt`: `RMF.extendedMeanSquare_ge_line` before its cut to
`|t| < 1`, the twin of `RMF.weightedMeanSquare_ge_line_full`. -/
theorem extendedMeanSquare_ge_line_full {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V : ℝ} (hV : 0 < V)
    (hx : 3 * V + 3 ≤ Real.log x) (hx4 : 4 ≤ x) :
    ∀ᵐ ω ∂μ, (2 * Real.pi)⁻¹
          * (∫ t : ℝ, lineDivSq (1 / 2 + 2 * V / Real.log x) X (⌊x⌋₊ + 1) ω t)
        - Real.pi⁻¹ * Real.exp (-V)
          * (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t)
      ≤ ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
          ‖randomSum (fun ω => compMultExtension fun p => X p ω) z ω‖ ^ 2 / z ^ 2 := by
  obtain ⟨hx0, hlog, -, -, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hV0 : 0 ≤ V / Real.log x := by positivity
  have hσ₁h : (1 : ℝ) / 2 ≤ 1 / 2 + 2 * V / Real.log x := by
    have : 0 ≤ 2 * V / Real.log x := by positivity
    linarith
  have hσ₂h : (1 : ℝ) / 2 ≤ 1 / 2 + V / Real.log x := by linarith
  have hσ₂₁ : 1 / 2 + V / Real.log x ≤ 1 / 2 + 2 * V / Real.log x := by
    have : V / Real.log x ≤ 2 * V / Real.log x :=
      div_le_div_of_nonneg_right (by linarith) hlog0.le
    linarith
  set g : Ω → ArithmeticFunction ℂ := fun ω => compMultExtension fun p => X p ω with hgdef
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖g ω n‖ ≤ 1 := fun n =>
    hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  filter_upwards [smoothTailIntegral_eq_lineDivSq_extended hX ⌊x⌋₊ hσ₁h,
    smoothTailIntegral_eq_lineDivSq_extended hX ⌊x⌋₊ hσ₂h,
    integrableOn_smoothTail_of hbd ⌊x⌋₊ hσ₁h, integrableOn_smoothTail_of hbd ⌊x⌋₊ hσ₂h]
    with ω hP₁ hP₂ hI₁ hI₂
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  have hw1 : 1 ≤ w := one_le_sqrt_div hx4
  have hwsq : w ≤ Real.sqrt x := div_le_self (Real.sqrt_nonneg x) hr1
  -- the cut
  have hsplit := setIntegral_Ioi_le_Ioc_add_mul (A := fun u => smoothPartial g ⌊x⌋₊ u ω)
    (fun u hu => smoothPartial_eq_zero hu ω) hw1 hσ₂₁ hI₁ hI₂
  rw [smoothTailIntegral] at hP₁ hP₂
  rw [hP₁, hP₂] at hsplit
  -- on `(1, w]` the shifted smooth-tail integrand is below the mean-square integrand
  have hb : (∫ u in Set.Ioc 1 w,
        ‖smoothPartial g ⌊x⌋₊ u ω‖ ^ 2 / u ^ (1 + 2 * (1 / 2 + 2 * V / Real.log x)))
      ≤ ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z ^ 2 :=
    setIntegral_mono_on
      (hI₁.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi zero_le_one)))
      (integrableOn_meanSquare_integrand g le_rfl ω) measurableSet_Ioc fun z hz =>
        smoothTail_integrand_le (by linarith) hσ₁h hz.1.le (le_trans hz.2 hwsq) ω
  -- the damping factor
  have hd : w ^ (-(2 * ((1 / 2 + 2 * V / Real.log x) - (1 / 2 + V / Real.log x))))
      ≤ 2 * Real.exp (-V) := by
    have he : (1 / 2 + 2 * V / Real.log x) - (1 / 2 + V / Real.log x)
        = 2 * V / Real.log x - V / Real.log x := by ring
    rw [he]
    exact rpow_neg_sqrt_div_le hV hx0 hx
  have hJ₂ : 0 ≤ ∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t :=
    integral_nonneg fun t => by unfold lineDivSq; positivity
  exact parseval_assembly_full hb hsplit hd hJ₂

/-! ### The reduction -/

/-- **The reduction's arithmetic for the extended sum**: from Khintchine
`3^{-(1-q)}ER ≤ 2^{1-2q}x^qES`, L9 `(x/(8L))^qEM - (2x/L)^q ≤ ER` and Parseval
`(2π)^{-q}EW - (π⁻¹e^{-V})^qEJ ≤ EM`, for `x, L > 0` and `q ≤ ½`,
`cRed·L^{-q}EW - cJ·e^{-Vq}L^{-q}EJ - cErrD·L^{-q} ≤ ES`: divided by `x^q`, these are the
hypotheses of `RMF.reduction_arith_explicit'`. -/
lemma reduction_arith_extended {ES ER EM EW EJ x L V q : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hq12 : q ≤ 1 / 2)
    (hkh : (3 : ℝ) ^ (-(1 - q)) * ER ≤ 2 ^ (1 - 2 * q) * (x ^ q * ES))
    (h9 : (x / (8 * L)) ^ q * EM - (2 * x / L) ^ q ≤ ER)
    (hPar : (2 * Real.pi)⁻¹ ^ q * EW - (Real.pi⁻¹ * Real.exp (-V)) ^ q * EJ ≤ EM) :
    cRed q * L ^ (-q) * EW - cJ q * Real.exp (-(V * q)) * L ^ (-q) * EJ - cErrD q * L ^ (-q)
      ≤ ES := by
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx q
  have h20 : (0 : ℝ) < 2 ^ (1 - 2 * q) := Real.rpow_pos_of_pos two_pos _
  refine reduction_arith_explicit' (ER := ER / x ^ q) hL ?_ ?_ hPar
  · -- Khintchine, divided by `2^{1-2q}x^q`
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * q),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 - 2 * q)]
    have e : (3 : ℝ) ^ (-(1 - q)) * (2 ^ (1 - 2 * q))⁻¹ * (ER / x ^ q)
        = (3 ^ (-(1 - q)) * ER) / (2 ^ (1 - 2 * q) * x ^ q) := by
      field_simp
    rw [e, div_le_iff₀ (mul_pos h20 hxq)]
    calc (3 : ℝ) ^ (-(1 - q)) * ER ≤ 2 ^ (1 - 2 * q) * (x ^ q * ES) := hkh
      _ = ES * (2 ^ (1 - 2 * q) * x ^ q) := by ring
  · -- L9, divided by `x^q`
    have h8 : (x / (8 * L)) ^ q = x ^ q * (8 * L)⁻¹ ^ q := by
      rw [div_eq_mul_inv, Real.mul_rpow hx.le (inv_nonneg.2 (by positivity))]
    have h2 : (2 * x / L) ^ q = x ^ q * (2 / L) ^ q := by
      rw [show 2 * x / L = x * (2 / L) by ring, Real.mul_rpow hx.le (by positivity)]
    rw [le_div_iff₀ hxq]
    have e : ((8 * L)⁻¹ ^ q * EM - (2 / L) ^ q) * x ^ q
        = (x / (8 * L)) ^ q * EM - (2 * x / L) ^ q := by
      rw [h8, h2]
      ring
    rw [e]
    exact h9

/-- **The reduction for the extended sum, with the window covering supplied.**  For a Rademacher
family, `V > 0`, `x ≥ e^{300}` with `RMF.IsWindowCovering x` (produced by
`RMF.isWindowCovering_of_classical` for `x ≥ exp(2·10²⁰ + 2)`), `log x ≥ 3V + 3` and
`0 < q ≤ ½`, with `J_Y(σ) = ∫_ℝ lineDivSq (½ + σ) X (⌊x⌋ + 1) ω t dt`:

`cRed(q)(log x)^{-q}E[J_Y(2V/log x)^q] - cJ(q)e^{-Vq}(log x)^{-q}E[J_Y(V/log x)^q]`
`  - cErrD(q)(log x)^{-q} ≤ E|Y(x)|^{2q}`.

The twin of `RMF.le_integral_rpow_weightedRademacherSum_euler_full_of_windowCovering`, with the
same constants. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_of_windowCovering {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {V x q : ℝ} (hV : 0 < V)
    (hx : Real.exp 300 ≤ x) (hwin : IsWindowCovering x) (hlogV : 3 * V + 3 ≤ Real.log x)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) :
    cRed q * (Real.log x ^ (-q) * ∫ ω, (∫ t : ℝ,
        lineDivSq (1 / 2 + 2 * V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
      - cJ q * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
          lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
      - cErrD q * Real.log x ^ (-q)
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := le_trans (by linarith [Real.add_one_le_exp (300 : ℝ)]) hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hL0 : 0 < Real.log x := by linarith
  have hσ₂h : (1 : ℝ) / 2 ≤ 1 / 2 + V / Real.log x := by
    have : 0 ≤ V / Real.log x := div_nonneg hV.le hL0.le
    linarith
  -- symmetrisation and Khintchine, on the primes of `(√x, x]`
  obtain ⟨hSp, hSx, hScov⟩ := primesIoc_sqrt_spec hx0.le
  have hSs : ∀ p ∈ largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊, Real.sqrt x < p := fun p hp =>
    (Nat.floor_lt (Real.sqrt_nonneg x)).1 (mem_largePrimeSet.1 hp).1.1
  have hkh := khintchine_rough_extended hX (by linarith) (floor_lt_floor_sqrt_add_one_sq hx0.le)
    hq0 (by linarith)
  -- L4–L9
  have h9 := meanSquare_le_sum_extended_of_windowCovering hX hx hwin hq0.le (by linarith)
    (largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) hSp hSs hSx hScov
  -- Parseval, at the `q`-th power
  have hMi : Integrable (fun ω => ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
      ‖randomSum (fun ω => compMultExtension fun p => X p ω) z ω‖ ^ 2 / z ^ 2) μ :=
    (integrable_meanSquare_prod_of (fun n => hX.measurable_compMultExtension n)
      (fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n)
      le_rfl).integral_prod_left
  have hM0 : ∀ ω, 0 ≤ ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
      ‖randomSum (fun ω => compMultExtension fun p => X p ω) z ω‖ ^ 2 / z ^ 2 := fun ω =>
    setIntegral_nonneg measurableSet_Ioc fun z _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hPar := integral_rpow_sub_le_of_ae (extendedMeanSquare_ge_line_full hX hV hlogV hx4)
    (by positivity) (by positivity) hq0.le (by linarith)
    (fun ω => integral_nonneg fun t => by unfold lineDivSq; positivity)
    (fun ω => integral_nonneg fun t => by unfold lineDivSq; positivity)
    hM0 (integrable_lineDivSq_rpow_extended hX (⌊x⌋₊ + 1) hσ₂h hq0.le)
    (integrable_rpow_of_integrable hMi (Filter.Eventually.of_forall hM0) hq0.le (by linarith))
  -- the unnormalised moment is `x^q E|Y|^{2q}`
  have hscale : (∫ ω, ‖randomSum (fun ω => compMultExtension fun r => X r ω) x ω‖ ^ (2 * q) ∂μ)
      = x ^ q * ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hs : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hx0).ne'
    have e : randomSum (fun ω => compMultExtension fun r => X r ω) x ω
        = normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω * (Real.sqrt x : ℂ) := by
      rw [normalisedSum, div_mul_cancel₀ _ hs]
    simp only
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.mul_rpow (norm_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hx0.le, show 1 / 2 * (2 * q) = q by ring, mul_comm]
  rw [hscale] at hkh
  have h := reduction_arith_extended hx0 hL0 hq1 hkh h9 hPar
  calc _ = _ := by ring
    _ ≤ _ := h

end RMF
