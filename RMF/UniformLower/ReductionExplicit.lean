/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.Reduction
import RMF.UniformLower.PerScale
import RMF.Reduction.LowerReductionExplicit

/-!
# The lower reduction, explicit and exact in `q`

Gerspach's Proposition 6 at `α = 1` (`RMF.exists_le_integral_rpow_weightedRademacherSum_of_parseval`
for `0 < q ≤ ½`) with nothing existential, for every `0 < q ≤ 1`:

`cRed(q)(log x)^{-q}E[W^q] - cJ(q)e^{-Vq}(log x)^{-q}E[J(V/log x)^q] - cErr(q)(log x)^{-q}`
`  ≤ E|S(x)|^{2q}`

for `x ≥ RMF.windowThreshold`, `log x ≥ 3V + 3` and every `W ≥ 0` that Parseval bounds with the
factor `(2π)⁻¹` (`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`).  With
Khintchine's factor on both sides of `½`, `k(q) = 3^{-(1-q)}2^{-max(1-2q, 0)}`:
`cRed = k(16π)^{-q}`, `cJ = k(8π)^{-q}`, `cErr = k·16^q`.

* **The threshold.**  The window weight of steps L4–L9 (`RMF.sum_normSq_ge_weighted`,
  `RMF.meanSquare_le_sum_weighted`) holds from the explicit `RMF.windowThreshold` on, through
  `RMF.half_setIntegral_le_window_sumOf_explicit`.
* **The constants** are the exact product of the chain's factors — Khintchine's, L9's
  `(8 log x)^{-q}` and `16^q`, Parseval's `(2π)^{-q}` and `π^{-q}e^{-Vq}`.
* **The canonical main term** `W = J(2V/log x)` (`RMF.weightedMeanSquare_ge_line_full`, no
  halving) is written through `RMF.shiftLine`, as
  `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_numeral` delivers it.

Also the floor for tiny `q`, `2^{-(1-2q)}3^{-(1-q)}(0.49/log x)^q ≤ E|S(x)|^{2q}`, from the primes
of `(x/2, x]`, at which `S(x/p) = 1`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Steps L4–L9 at the window threshold -/

omit [MeasurableSpace Ω] in
/-- **`RMF.sum_normSq_ge_weighted` at its threshold** `RMF.windowThreshold`: steps L4, L5 and L8
for the weighted sum, pointwise, the covering by `RMF.half_setIntegral_le_window_sumOf_explicit`. -/
theorem sum_normSq_ge_weighted_explicit :
    ∀ (g : Ω → ArithmeticFunction ℂ) (ω : Ω) (x : ℝ), windowThreshold ≤ x →
      ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
        (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
        (8 * Real.log x)⁻¹ * (∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
              ‖randomSum g z ω‖ ^ 2 / z)
            - (∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
                ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
                  discrepancy g x p ω t))) / Real.log x
          ≤ ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 := by
  have hL8 := half_setIntegral_le_window_sumOf_explicit
  intro g ω x hx S hSp hSx hS
  have hx4 : (4 : ℝ) ≤ x := le_trans four_le_windowThreshold hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hr0 : (0 : ℝ) < 1 + 1 / Real.log x := by linarith
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hSp p hp).pos
  have hp1 : ∀ p ∈ S, (1 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hSp p hp).one_lt.le
  -- the four sums
  set V : ℝ := ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 with hVdef
  set L : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) with hLdef
  set Wsum : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2)) with hWdef
  set Dsum : ℝ := ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t)) with hDdef
  set Gsum : ℝ := ∑ p ∈ S, Real.log p * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
      ‖randomSum g (x / t) ω‖ ^ 2 / |t|) with hGdef
  set M : ℝ := ∫ z in Set.Ioc 1 (Real.sqrt x / (1 + 1 / Real.log x)),
    ‖randomSum g z ω‖ ^ 2 / z with hMdef
  -- L4: `log p ≤ log x`
  have hL4 : L ≤ Real.log x * V :=
    sum_log_mul_le_log_mul_sum (x := x) (by linarith) hSx
      (v := fun p => (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) fun p => by positivity
  -- L5: smoothing, prime by prime, weighted by `log p / p`
  have hL5 : 1 / 4 * Wsum - Dsum ≤ L := by
    have hstep : ∀ p ∈ S, 1 / 4 * (Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
            ‖randomSum g (x / t) ω‖ ^ 2)))
        - Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
          ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t))
        ≤ Real.log p * ((p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2) := by
      intro p hp
      have hb := smoothing_bound (f := g) hx0.le hlog0 (hpos p hp) ω
      have hw : (0 : ℝ) ≤ Real.log p * (p : ℝ)⁻¹ :=
        mul_nonneg (Real.log_natCast_nonneg p) (inv_nonneg.2 (hpos p hp).le)
      have := mul_le_mul_of_nonneg_left hb hw
      linarith [this]
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    exact hsum
  -- L8: the extra `1/p` against `1/t`, then the covering
  have hGW : Gsum ≤ Wsum := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp0 := hpos p hp
    have hIG := integrableOn_normSq_randomSum_div_abs g hx0.le (c := (p : ℝ))
      (d := (p : ℝ) * (1 + 1 / Real.log x)) (hp1 p hp) ω
    have hIA := (integrableOn_normSq_randomSum_div g hx0.le (c := (p : ℝ))
      (d := (p : ℝ) * (1 + 1 / Real.log x)) (hp1 p hp) ω).const_mul ((p : ℝ)⁻¹)
    have hmono : (∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
        ≤ ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          (p : ℝ)⁻¹ * ‖randomSum g (x / t) ω‖ ^ 2 := by
      refine setIntegral_mono_on hIG hIA measurableSet_Ioc fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans hp0 ht.1
      rw [abs_of_pos ht0, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hp0 ht.1.le) (by positivity)
    rw [integral_const_mul] at hmono
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have hcoef : (0 : ℝ) ≤ Real.log x / p := by positivity
    calc Real.log p * (Real.log x / p * ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)),
          ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
        ≤ Real.log p * (Real.log x / p * ((p : ℝ)⁻¹ * ∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)), ‖randomSum g (x / t) ω‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hcoef) hlp
      _ = Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p * ∫ t in Set.Ioc (p : ℝ)
          ((p : ℝ) * (1 + 1 / Real.log x)), ‖randomSum g (x / t) ω‖ ^ 2)) := by ring
  have hcover := hL8 x hx (fun t => ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
    (fun t => by positivity)
    (fun c d hc => integrableOn_normSq_randomSum_div_abs g hx0.le hc ω) S hSp hS
  -- the substitution
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have ha0 : (0 : ℝ) < Real.sqrt x * (1 + 1 / Real.log x) := by positivity
  have hax : Real.sqrt x * (1 + 1 / Real.log x) ≤ x := by
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith
  have hxa : x / (Real.sqrt x * (1 + 1 / Real.log x)) = Real.sqrt x / (1 + 1 / Real.log x) := by
    have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    field_simp
    nlinarith
  have habs : (∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2 / |t|)
      = ∫ t in Set.Ioc (Real.sqrt x * (1 + 1 / Real.log x)) x,
        ‖randomSum g (x / t) ω‖ ^ 2 / t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [abs_of_pos (lt_trans ha0 ht.1)]
  have hsub := setIntegral_div_eq_dz_div_z g hx0 ha0 hax ω
  rw [hxa] at hsub
  rw [habs, hsub] at hcover
  -- assemble: `M/8 ≤ Gsum/4 ≤ Wsum/4 ≤ L + Dsum ≤ log x · V + Dsum`
  have hkey : M / 8 - Dsum ≤ Real.log x * V := by linarith
  rw [show (8 * Real.log x)⁻¹ * M - Dsum / Real.log x = (M / 8 - Dsum) / Real.log x by
    field_simp]
  rw [div_le_iff₀ hlog0]
  linarith

/-- **`RMF.meanSquare_le_sum_weighted` at its threshold** `RMF.windowThreshold`: steps L4–L9 for
the weighted sum, `(8 log x)^{-q}E[weightedMeanSquare^q] - (16/log x)^q
≤ E[(∑_{p∈S} p^{-1}|S(x/p)|²)^q]` for `0 ≤ q ≤ 1`. -/
theorem meanSquare_le_sum_weighted_explicit :
    ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ x q : ℝ, windowThreshold ≤ x → 0 ≤ q → q ≤ 1 →
        ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, (p : ℝ) ≤ x) →
          (∀ p : ℕ, p.Prime → Real.sqrt x < p → (p : ℝ) ≤ x → p ∈ S) →
          (8 * Real.log x)⁻¹ ^ q
                * ∫ ω, weightedMeanSquare (fun ω => squarefreeExtension fun r => X r ω) x ω
                    ^ q ∂μ
              - (16 / Real.log x) ^ q
            ≤ ∫ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum
                (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2) ^ q ∂μ := by
  have hchain := sum_normSq_ge_weighted_explicit (Ω := Ω)
  intro X μ hX x q hx hq0 hq1 S hSp hSx hS
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := le_trans four_le_windowThreshold hx
  obtain ⟨hx0, hlog, hsq, hr2, hr1⟩ := log_scale_facts hx4
  have hlog0 : (0 : ℝ) < Real.log x := by linarith
  have hxe : Real.exp 1 ≤ x := by nlinarith [Real.exp_one_lt_d9]
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun r => X r ω with hfdef
  set g : Ω → ArithmeticFunction ℂ := fun ω => weightedExt fun r => X r ω with hgdef
  have hg : IsBoundedRMF g μ := isBoundedRMF_weightedExt hX
  have hSsub : S ⊆ {p ∈ Finset.Ioc 0 ⌊x⌋₊ | p.Prime} := fun p hp =>
    Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(hSp p hp).pos, Nat.le_floor (hSx p hp)⟩, hSp p hp⟩
  -- the three quantities, in terms of `g`
  set w : ℝ := Real.sqrt x / (1 + 1 / Real.log x) with hwdef
  set Mg : Ω → ℝ := fun ω => ∫ z in Set.Ioc 1 w, ‖randomSum g z ω‖ ^ 2 / z with hMgdef
  set D : Ω → ℝ := fun ω => ∑ p ∈ S, Real.log p * ((p : ℝ)⁻¹ * (Real.log x / p *
    ∫ t in Set.Ioc (p : ℝ) ((p : ℝ) * (1 + 1 / Real.log x)), discrepancy g x p ω t))
    with hDdef
  set A : Ω → ℝ := fun ω => ∑ p ∈ S, (p : ℝ)⁻¹ * ‖randomSum g (x / p) ω‖ ^ 2 with hAdef
  have hMeq : ∀ ω, weightedMeanSquare f x ω = Mg ω := by
    intro ω
    simp only [weightedMeanSquare, hMgdef, hfdef, hgdef, hwdef, weightedRademacherSum_eq_randomSum]
  have hAeq : ∀ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) = A ω := by
    intro ω
    simp only [hAdef, hfdef, hgdef, weightedRademacherSum_eq_randomSum]
  -- nonnegativity
  have hM0 : ∀ ω, 0 ≤ Mg ω := fun ω => by
    rw [← hMeq]
    exact weightedMeanSquare_nonneg f x ω
  have hD0 : ∀ ω, 0 ≤ D ω := by
    intro ω
    refine Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_natCast_nonneg p) ?_
    refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (mul_nonneg (by positivity) ?_)
    exact setIntegral_nonneg measurableSet_Ioc fun t _ => discrepancy_nonneg g x p ω t
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Finset.sum_nonneg fun p _ => by positivity
  have hP0 : ∀ ω, 0 ≤ (8 * Real.log x)⁻¹ * Mg ω := fun ω =>
    mul_nonneg (by positivity) (hM0 ω)
  have hR0 : ∀ ω, 0 ≤ D ω / Real.log x := fun ω => div_nonneg (hD0 ω) hlog0.le
  -- integrability
  have hMi : Integrable Mg μ := (integrable_weightedMeanSquare_prod hX w).integral_prod_left
  have hDi : Integrable D μ := integrable_weightedDiscrepancySum hX hx0.le hSp
  have hAi : Integrable A μ :=
    integrable_finsetSum _ fun p _ => (integrable_normSq_randomSum hg (x / p)).const_mul _
  have hPi : Integrable (fun ω => (8 * Real.log x)⁻¹ * Mg ω) μ := hMi.const_mul _
  have hRi : Integrable (fun ω => D ω / Real.log x) μ := hDi.div_const _
  have hPq := integrable_rpow_of_integrable hPi (Filter.Eventually.of_forall hP0) hq0 hq1
  have hRq := integrable_rpow_of_integrable hRi (Filter.Eventually.of_forall hR0) hq0 hq1
  have hAq := integrable_rpow_of_integrable hAi (Filter.Eventually.of_forall hA0) hq0 hq1
  -- the pointwise inequality, at the `q`-th power
  have hpt : ∀ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q - (D ω / Real.log x) ^ q ≤ A ω ^ q :=
    fun ω => rpow_sub_rpow_le_of_sub_le (hP0 ω) (hR0 ω) (hA0 ω)
      (hchain g ω x hx S hSp hSx hS) hq0 hq1
  have hmain : (∫ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q ∂μ) - ∫ ω, (D ω / Real.log x) ^ q ∂μ
      ≤ ∫ ω, A ω ^ q ∂μ := by
    rw [← integral_sub hPq hRq]
    exact integral_mono (hPq.sub hRq) hAq hpt
  -- the two evaluations
  have hPval : (∫ ω, ((8 * Real.log x)⁻¹ * Mg ω) ^ q ∂μ)
      = (8 * Real.log x)⁻¹ ^ q * ∫ ω, Mg ω ^ q ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      Real.mul_rpow (by positivity) (hM0 ω))
  have hRval : (∫ ω, (D ω / Real.log x) ^ q ∂μ) ≤ (16 / Real.log x) ^ q := by
    refine le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall fun ω => Set.mem_Ici.2 (hR0 ω)) hRi hRq) ?_
    refine Real.rpow_le_rpow (integral_nonneg hR0) ?_ hq0
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_sum_discrepancy_le_weighted hX hxe hSsub)
      hlog0.le
  -- back to the weighted sums
  have hL : (∫ ω, weightedMeanSquare f x ω ^ q ∂μ) = ∫ ω, Mg ω ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hMeq ω])
  have hR : (∫ ω, (∑ p ∈ S, (p : ℝ)⁻¹ * ‖weightedRademacherSum f (x / p) ω‖ ^ 2) ^ q ∂μ)
      = ∫ ω, A ω ^ q ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hAeq ω])
  rw [hL, hR]
  rw [hPval] at hmain
  linarith

/-! ### Khintchine on both sides of `½` -/

/-- **Steps L1–L3 for the weighted sum, `0 < q ≤ 1`.**  For `⌊x⌋ < (y+1)²`,
`3^{-(1-q)}2^{-max(1-2q, 0)}·E[(∑_{y<p≤x} p^{-1}|S(x/p)|²)^q] ≤ E|S(x)|^{2q}`:
`RMF.khintchine_rough_weighted` for `q ≤ ½`, `RMF.khintchine_rough_weighted_of_half_le` above. -/
theorem khintchine_rough_weighted_of_le_one {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {x : ℝ} {y : ℕ} (hx : 1 ≤ x)
    (hxy : ⌊x⌋₊ < (y + 1) ^ 2) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0)
        * ∫ ω, (∑ p ∈ largePrimeSet y ⌊x⌋₊, (p : ℝ)⁻¹
          * ‖weightedRademacherSum (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2)
            ^ q ∂μ
      ≤ ∫ ω, ‖weightedRademacherSum
          (fun ω => squarefreeExtension fun r => X r ω) x ω‖ ^ (2 * q) ∂μ := by
  rcases le_or_gt q (1 / 2) with hq12 | hq12
  · have hkh := khintchine_rough_weighted hX hx hxy hq0 (by linarith)
    rw [max_eq_left (by linarith)]
    have h2 : (2 : ℝ) ^ (-(1 - 2 * q)) * 2 ^ (1 - 2 * q) = 1 := by
      rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
    have h20 : (0 : ℝ) ≤ 2 ^ (-(1 - 2 * q)) := Real.rpow_nonneg zero_le_two _
    have hmul := mul_le_mul_of_nonneg_left hkh h20
    rw [← mul_assoc ((2 : ℝ) ^ (-(1 - 2 * q))) ((2 : ℝ) ^ (1 - 2 * q)), h2, one_mul] at hmul
    linarith
  · have hkh := khintchine_rough_weighted_of_half_le hX hx hxy (by linarith) hq1
    rw [max_eq_right (by linarith), neg_zero, Real.rpow_zero, mul_one]
    exact hkh

/-! ### The constants -/

/-- **The main-term constant** `3^{-(1-q)}2^{-max(1-2q, 0)}(16π)^{-q}` of the reduction
(`≈ 0.0814` at `q = ½`). -/
noncomputable def cRed (q : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * (16 * Real.pi) ^ (-q)

/-- **The subtracted-term constant** `3^{-(1-q)}2^{-max(1-2q, 0)}(8π)^{-q}` of the reduction. -/
noncomputable def cJ (q : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * (8 * Real.pi) ^ (-q)

/-- **The error constant** `3^{-(1-q)}2^{-max(1-2q, 0)}16^q` of the reduction. -/
noncomputable def cErr (q : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * (16 : ℝ) ^ q

lemma cRed_pos (q : ℝ) : 0 < cRed q := by
  unfold cRed
  positivity

lemma cJ_pos (q : ℝ) : 0 < cJ q := by
  unfold cJ
  positivity

lemma cErr_pos (q : ℝ) : 0 < cErr q := by
  unfold cErr
  positivity

/-! ### The reduction -/

/-- **The arithmetic of the reduction, exact.**  From Khintchine `3^{-(1-q)}2^{-max(1-2q, 0)}ER
≤ ES`, L9 `(8L)^{-q}EM - (16/L)^q ≤ ER` and Parseval `(2π)^{-q}EW - (π⁻¹e^{-V})^qEJ ≤ EM`:
`cRed·L^{-q}EW - cJ·e^{-Vq}L^{-q}EJ - cErr·L^{-q} ≤ ES`, every factor kept. -/
lemma reduction_arith_explicit {ES ER EM EW EJ L V q : ℝ} (hL : 0 < L)
    (hkh : (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) * ER ≤ ES)
    (h9 : (8 * L)⁻¹ ^ q * EM - (16 / L) ^ q ≤ ER)
    (hPar : (2 * Real.pi)⁻¹ ^ q * EW - (Real.pi⁻¹ * Real.exp (-V)) ^ q * EJ ≤ EM) :
    cRed q * L ^ (-q) * EW - cJ q * Real.exp (-(V * q)) * L ^ (-q) * EJ - cErr q * L ^ (-q)
      ≤ ES := by
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hLq : L⁻¹ ^ q = L ^ (-q) := by rw [Real.inv_rpow hL.le, ← Real.rpow_neg hL.le]
  have h8 : (8 * L)⁻¹ ^ q = (8 : ℝ)⁻¹ ^ q * L ^ (-q) := by
    rw [mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hL.le), hLq]
  have h16 : (16 / L) ^ q = (16 : ℝ) ^ q * L ^ (-q) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hL.le), hLq]
  have hpe : (Real.pi⁻¹ * Real.exp (-V)) ^ q = Real.pi⁻¹ ^ q * Real.exp (-(V * q)) := by
    rw [Real.mul_rpow (inv_nonneg.2 hπ0.le) (Real.exp_pos _).le, ← Real.exp_mul, neg_mul]
  have hred : (16 * Real.pi) ^ (-q) = (8 : ℝ)⁻¹ ^ q * (2 * Real.pi)⁻¹ ^ q := by
    rw [← Real.mul_rpow (by norm_num) (inv_nonneg.2 (by positivity)), ← mul_inv,
      show (8 : ℝ) * (2 * Real.pi) = 16 * Real.pi by ring,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 16 * Real.pi),
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ 16 * Real.pi)]
  have hJ : (8 * Real.pi) ^ (-q) = (8 : ℝ)⁻¹ ^ q * Real.pi⁻¹ ^ q := by
    rw [← Real.mul_rpow (by norm_num) (inv_nonneg.2 hπ0.le), ← mul_inv,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 8 * Real.pi),
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ 8 * Real.pi)]
  rw [h8, h16] at h9
  rw [hpe] at hPar
  have hk0 : 0 ≤ (3 : ℝ) ^ (-(1 - q)) * (2 : ℝ) ^ (-max (1 - 2 * q) 0) := by positivity
  have hA0 : 0 ≤ (8 : ℝ)⁻¹ ^ q * L ^ (-q) := by positivity
  have p1 := mul_le_mul_of_nonneg_left hPar hA0
  have p2 : (8 : ℝ)⁻¹ ^ q * L ^ (-q)
        * ((2 * Real.pi)⁻¹ ^ q * EW - Real.pi⁻¹ ^ q * Real.exp (-(V * q)) * EJ)
      - (16 : ℝ) ^ q * L ^ (-q) ≤ ER := by linarith
  have p3 := mul_le_mul_of_nonneg_left p2 hk0
  unfold cRed cJ cErr
  rw [hred, hJ]
  linarith

/-- **Gerspach's Proposition 6 at `α = 1`, explicit and exact in `q`, for any main term the
Parseval step bounds.**  For a Rademacher family, `V > 0`, `x ≥ RMF.windowThreshold` with
`log x ≥ 3V + 3`, `0 < q ≤ 1`, and every nonnegative `W` with, almost surely,
`(2π)⁻¹W - π⁻¹e^{-V}J(V/log x) ≤ M` (`J(σ) = ∫_ℝ |F(½+σ+it)/(σ+it)|² dt`, `F` over the primes
up to `x`, `M = RMF.weightedMeanSquare`; `RMF.weightedMeanSquare_ge_line_full` supplies it at
`W = J(2V/log x)`):

`cRed(q)(log x)^{-q}E[W^q] - cJ(q)e^{-Vq}(log x)^{-q}E[J(V/log x)^q] - cErr(q)(log x)^{-q}`
`  ≤ E|S(x)|^{2q}`.

No measurability of `W` is asked (`RMF.integral_rpow_sub_le_of_ae`). -/
theorem le_integral_rpow_weightedRademacherSum_of_parseval_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {V x q : ℝ} (hV : 0 < V)
    (hx : windowThreshold ≤ x) (hlogV : 3 * V + 3 ≤ Real.log x) (hq0 : 0 < q) (hq1 : q ≤ 1)
    {W : Ω → ℝ} (hW0 : ∀ ω, 0 ≤ W ω)
    (hae : ∀ᵐ ω ∂μ, (2 * Real.pi)⁻¹ * W ω - Real.pi⁻¹ * Real.exp (-V) * (∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      ≤ weightedMeanSquare (fun ω => squarefreeExtension fun p => X p ω) x ω) :
    cRed q * Real.log x ^ (-q) * (∫ ω, W ω ^ q ∂μ)
      - cJ q * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      - cErr q * Real.log x ^ (-q)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := le_trans four_le_windowThreshold hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  have hσ₂0 : 0 < V / Real.log x := div_pos hV (by linarith)
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ x))
  -- steps L1–L3 and L4–L9, on the primes of `(√x, x]`
  obtain ⟨hSp, hSx, hScov⟩ := primesIoc_sqrt_spec hx0.le
  have hkh := khintchine_rough_weighted_of_le_one hX (by linarith)
    (floor_lt_floor_sqrt_add_one_sq hx0.le) hq0 hq1
  have h9 := meanSquare_le_sum_weighted_explicit X μ hX x q hx hq0.le hq1
    (largePrimeSet ⌊Real.sqrt x⌋₊ ⌊x⌋₊) hSp hSx hScov
  -- Parseval, at the `q`-th power
  have hPar := integral_rpow_sub_le_of_ae hae (by positivity) (by positivity) hq0.le hq1 hW0
    (fun ω => integral_nonneg fun t => sq_nonneg _)
    (fun ω => weightedMeanSquare_nonneg _ x ω)
    (integrable_rpow_eulerProductLine_of_two_le hX hy2 hσ₂0 hq0.le)
    (integrable_rpow_of_integrable (integrable_weightedMeanSquare hX x)
      (Filter.Eventually.of_forall fun ω => weightedMeanSquare_nonneg _ x ω) hq0.le hq1)
  exact reduction_arith_explicit (by linarith) hkh h9 hPar

omit [MeasurableSpace Ω] in
/-- **The bridge to the main term**: the reduction's line integral
`∫_ℝ |F(½+σ+it)/(σ+it)|² dt` is the one of `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_numeral`,
written through `RMF.shiftLine σ t = ½ + σ + it`. -/
lemma integral_lineDiv_eq_shiftLine (X : ℕ → Ω → ℂ) (N : ℕ) (σ : ℝ) (ω : Ω) :
    (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = ∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2 := by
  simp only [shiftLine_eq_half_add]

/-- **The reduction at the canonical main term** `W = J(2V/log x)`: for a Rademacher family,
`V > 0`, `x ≥ RMF.windowThreshold` with `log x ≥ 3V + 3` and `0 < q ≤ 1`, at `σ = 2V/log x`,

`cRed(q)·((log x)^{-q}E[(∫_ℝ |F(shiftLine σ u)/(σ+iu)|² du)^q])`
`  - cJ(q)e^{-Vq}(log x)^{-q}E[J(V/log x)^q] - cErr(q)(log x)^{-q} ≤ E|S(x)|^{2q}`,

`F` over the primes up to `x` (`y = ⌊x⌋ + 1`).  The first bracket is the right side of
`RMF.le_rpow_mul_integral_rpow_integral_lineDiv_numeral` at `L = log x`, `y = ⌊x⌋ + 1` and this
`σ` (its `V` is `σL = 2V`).  Parseval's hypothesis is `RMF.weightedMeanSquare_ge_line_full`, with
`(2π)⁻¹`. -/
theorem le_integral_rpow_weightedRademacherSum_euler_full_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {V x q : ℝ} (hV : 0 < V)
    (hx : windowThreshold ≤ x) (hlogV : 3 * V + 3 ≤ Real.log x) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    cRed q * (Real.log x ^ (-q) * ∫ ω, (∫ u : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            (shiftLine (2 * V / Real.log x) u) ω
          / (((2 * V / Real.log x : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      - cJ q * Real.exp (-(V * q)) * Real.log x ^ (-q) * (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      - cErr q * Real.log x ^ (-q)
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  have hx4 : (4 : ℝ) ≤ x := le_trans four_le_windowThreshold hx
  have h := le_integral_rpow_weightedRademacherSum_of_parseval_explicit hX hV hx hlogV hq0 hq1
    (fun ω => integral_nonneg fun t => sq_nonneg _)
    (Filter.Eventually.of_forall fun ω => weightedMeanSquare_ge_line_full hV hlogV hx4 ω)
  simp only [← integral_lineDiv_eq_shiftLine]
  rw [← mul_assoc]
  exact h

/-! ### The floor for tiny `q` -/

omit [MeasurableSpace Ω] in
/-- `S(z) = 1` for `1 ≤ z < 2`: only `n = 1` is in range, and `f(1) = 1`. -/
lemma weightedRademacherSum_eq_one_of_lt_two (X : ℕ → Ω → ℂ) {z : ℝ} (h1 : 1 ≤ z)
    (h2 : z < 2) (ω : Ω) :
    weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z ω = 1 := by
  have hfl : ⌊z⌋₊ = 1 :=
    (Nat.floor_eq_iff (by linarith)).2 ⟨by exact_mod_cast h1, by push_cast; linarith⟩
  simp [weightedRademacherSum, hfl]

/-- The arithmetic of the floor's prime sum: for `L ≥ 200 + 80C` and `log(x/2) ≥ L/2`, the errors
`Cx/L² + C(x/2)/log²(x/2)` of `RMF.theta_sub_theta_ge` are at most `3x/16000`. -/
lemma theta_half_arith {C L l₂ x θ : ℝ} (hC0 : 0 ≤ C) (hL : 200 + 80 * C ≤ L) (hl₂ : L / 2 ≤ l₂)
    (hx0 : 0 < x) (hθ : x - x / 2 - (C * x / L ^ 2 + C * (x / 2) / l₂ ^ 2) ≤ θ) :
    49 / 100 * x ≤ θ := by
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < l₂ := by linarith
  have hL2 : 16000 * C ≤ L ^ 2 := by
    nlinarith [mul_le_mul hL hL (by positivity) hL0.le]
  have hl2 : L ^ 2 / 4 ≤ l₂ ^ 2 := by
    nlinarith [mul_le_mul hl₂ hl₂ (by positivity) hl0.le]
  have hE1 : C * x / L ^ 2 ≤ x / 16000 := by
    rw [div_le_div_iff₀ (pow_pos hL0 2) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hL2 hx0.le]
  have hE2 : C * (x / 2) / l₂ ^ 2 ≤ x / 8000 := by
    rw [div_le_div_iff₀ (pow_pos hl0 2) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hl2 hx0.le, mul_le_mul_of_nonneg_left hL2 hx0.le]
  linarith

/-- **The primes of `(x/2, x]`**: `∑_{x/2<p≤x} 1/p ≥ 0.49/log x` for `x ≥ RMF.windowThreshold`.
`1/p ≥ log p/(x log x)` there, and `θ(x) - θ(x/2) ≥ 0.49x` by `RMF.theta_sub_theta_ge` with the
effective `RMF.abs_theta_sub_le_pntAll`, whose errors are small at `log x ≥ 200 + 80C`. -/
lemma le_sum_inv_largePrimeSet_half {x : ℝ} (hx : windowThreshold ≤ x) :
    49 / (100 * Real.log x) ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := by
  have hx4 : (4 : ℝ) ≤ x := le_trans four_le_windowThreshold hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hxe : Real.exp (200 + 80 * pntAllConst) ≤ x := le_trans (le_max_left _ _) hx
  have hL : 200 + 80 * pntAllConst ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hL0 : 0 < Real.log x := by linarith [pntAllConst_nonneg]
  have hl₂ : Real.log x / 2 ≤ Real.log (x / 2) := by
    rw [Real.log_div hx0.ne' two_ne_zero]
    have := Real.log_two_lt_d9
    linarith [pntAllConst_nonneg]
  have hθ := theta_sub_theta_ge abs_theta_sub_le_pntAll (s := x / 2) (t := x) (by linarith)
    (by linarith)
  have hθ' := theta_half_arith pntAllConst_nonneg hL hl₂ hx0 hθ
  rw [theta_sub_theta_eq (Nat.floor_mono (by linarith))] at hθ'
  have hterm : ∀ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊,
      Real.log p / (x * Real.log x) ≤ (p : ℝ)⁻¹ := by
    intro p hp
    obtain ⟨⟨-, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpxR : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hpx) (Nat.floor_le hx0.le)
    have hlogp : Real.log p ≤ Real.log x := Real.log_le_log hp0 hpxR
    have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [div_le_iff₀ (mul_pos hx0 hL0)]
    have h1 : (1 : ℝ) ≤ (p : ℝ)⁻¹ * x := by
      rw [inv_mul_eq_div, one_le_div hp0]
      exact hpxR
    nlinarith [mul_le_mul h1 hlogp hlogp0 (zero_le_one.trans h1)]
  calc 49 / (100 * Real.log x) = 49 / 100 * x / (x * Real.log x) := by
        field_simp
    _ ≤ (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p) / (x * Real.log x) :=
        div_le_div_of_nonneg_right hθ' (mul_pos hx0 hL0).le
    _ = ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p / (x * Real.log x) := Finset.sum_div _ _ _
    _ ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := Finset.sum_le_sum hterm

/-- **The floor for tiny `q`**: for a Rademacher family, `0 < q ≤ ½` and `x ≥ RMF.windowThreshold`,
`2^{-(1-2q)}3^{-(1-q)}(0.49/log x)^q ≤ E|S(x)|^{2q}`.  Khintchine (`RMF.khintchine_rough_weighted`)
at `y = ⌊x/2⌋`: every prime `p` of `(x/2, x]` has `S(x/p) = 1`, so the prime sum is the constant
`∑_{x/2<p≤x} 1/p ≥ 0.49/log x` (`RMF.le_sum_inv_largePrimeSet_half`). -/
theorem le_integral_rpow_weightedRademacherSum_floor_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : windowThreshold ≤ x) (hq0 : 0 < q)
    (hq12 : q ≤ 1 / 2) :
    (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (49 / (100 * Real.log x)) ^ q
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx4 : (4 : ℝ) ≤ x := le_trans four_le_windowThreshold hx
  obtain ⟨hx0, hlog, -, -, -⟩ := log_scale_facts hx4
  -- Khintchine at `y = ⌊x/2⌋`
  have hxy : ⌊x⌋₊ < (⌊x / 2⌋₊ + 1) ^ 2 := by
    have hs : x / 2 < (⌊x / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : x < ((⌊x / 2⌋₊ : ℝ) + 1) ^ 2 := by nlinarith
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hcast : (⌊x⌋₊ : ℝ) < (((⌊x / 2⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hkh := khintchine_rough_weighted hX (by linarith) hxy hq0 (by linarith)
  -- the prime sum is deterministic
  have hS1 : ∀ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, ∀ ω,
      weightedRademacherSum (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω = 1 := by
    intro p hp ω
    obtain ⟨⟨hyp, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpxR : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hpx) (Nat.floor_le hx0.le)
    have hhalf : x / 2 < p := by
      have h1 : (⌊x / 2⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hyp
      have h2 := Nat.lt_floor_add_one (x / 2)
      linarith
    refine weightedRademacherSum_eq_one_of_lt_two X ?_ ?_ ω
    · rw [le_div_iff₀ hp0]
      linarith
    · rw [div_lt_iff₀ hp0]
      linarith
  have hconst : ∀ ω, (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ * ‖weightedRademacherSum
      (fun ω => squarefreeExtension fun r => X r ω) (x / p) ω‖ ^ 2)
      = ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ := fun ω =>
    Finset.sum_congr rfl fun p hp => by rw [hS1 p hp ω, norm_one, one_pow, mul_one]
  simp only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul] at hkh
  -- the constant, bounded below
  have hL0 : 0 < Real.log x := by linarith
  have hmono : (49 / (100 * Real.log x)) ^ q
      ≤ (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹) ^ q :=
    Real.rpow_le_rpow (div_pos (by norm_num) (mul_pos (by norm_num) hL0)).le
      (le_sum_inv_largePrimeSet_half hx) hq0.le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - q)) := Real.rpow_nonneg (by norm_num) _
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 - 2 * q)) := Real.rpow_nonneg (by norm_num) _
  have h2 : (2 : ℝ) ^ (-(1 - 2 * q)) * 2 ^ (1 - 2 * q) = 1 := by
    rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
  have p1 := le_trans (mul_le_mul_of_nonneg_left hmono h3) hkh
  have p2 := mul_le_mul_of_nonneg_left p1 h20
  rw [← mul_assoc ((2 : ℝ) ^ (-(1 - 2 * q))) ((2 : ℝ) ^ (1 - 2 * q)), h2, one_mul] at p2
  linarith

end RMF
