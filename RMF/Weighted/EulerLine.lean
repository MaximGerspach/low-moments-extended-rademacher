/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Principal

/-!
# The Euler-product line integral is a.e. bounded

The right-hand side of the small-`q` reduction to a random Euler product
(`RMF.exists_integral_rpow_weightedRademacherSum_le`) contains `∫ ω, Z(ω)^q ∂μ` with

`Z(ω) = (log y)⁻¹ ∫_ℝ ‖F_y(½+σ+it)/(σ+it)‖² dt`.

If `Z^q` were not integrable, Lean's convention would make that integral `0` and the right-hand
side would collapse — so this is load-bearing, not bookkeeping.

`Z` is a.e. bounded.  By Parseval (`RMF.integral_normSq_smoothWeightedSum_eq_line`) the
`t`-integral is a `u`-integral of `‖A_y(u)‖²·u^(-1-2σ)`; the smooth sum vanishes below `1`
(`RMF.smoothWeightedSum_eq_zero_of_lt_one`); and `∫_1^∞ u^(-1-2σ) du = 1/(2σ)`.

The bound on `A_y` has to be **uniform in `u`**, which is what `RMF.norm_smoothWeightedSum_le_sum`
cannot give — its majorant is the sum over `Icc 1 ⌊v⌋₊`, and there is no `v` dominating the whole
half-line.  What supplies it instead is `RMF.smoothWeightedSum_eq_randomEulerProduct`: past
`primorial y` the smooth sum has stopped moving and equals `F_y(½)`, so
`RMF.norm_smoothWeightedSum_le_of_bound` at the truncation point `primorial y` bounds every value.

Passing through the `u`-integral also settles measurability in `ω`, which the `t`-integral does
not give directly: `A_y(u)` depends on `u` only through `⌊u⌋₊`, so `(ω, u) ↦ A_y(u)(ω)` is
jointly measurable by `measurable_from_prod_countable_left`, and
`MeasureTheory.StronglyMeasurable.integral_prod_right'` then integrates `u` out.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`Z^q` is integrable**, for `σ > 0` and `q ≥ 0`.  `Z` is a.e. at most
`(log y)⁻¹·2π·(primorial y)²/(2σ)`: by Parseval its `t`-integral is a `u`-integral of
`‖A_y(u)‖²u^(-1-2σ)`, where `A_y(u)` vanishes below `1` and is a sum of at most `primorial y` terms
of modulus at most one (past `primorial y` it is constant, equal to `F_y(½)`), and the remaining
`u`-integral is `∫_1^∞ u^(-1-2σ) du = 1/(2σ)`. -/
theorem integrable_rpow_eulerProductLine {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) ^ q) μ := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  -- everything stated at the raw `squarefreeExtension` shape is fetched before `set` folds it
  have hpars := fun ω : Ω => integral_normSq_smoothWeightedSum_eq_line (X := X) y hσ ω
  have hIint := fun ω : Ω => integrableOn_normSq_smoothWeightedSum (X := X) y hσ ω
  have hEuler := fun (N : ℝ) (hN : (primorial y : ℝ) ≤ N) (ω : Ω) =>
    smoothWeightedSum_eq_randomEulerProduct (X := X) y hN ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω
  -- Step 1: Parseval turns the `t`-integral into the `u`-integral
  have hpi2 : (2 * Real.pi) ≠ 0 := by positivity
  have hrw : ∀ ω : Ω,
      ((Real.log y)⁻¹ * ∫ t : ℝ, ‖randomEulerProduct f (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        = (Real.log y)⁻¹ * (2 * Real.pi)
            * ∫ u in Set.Ioi (0 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
    intro ω
    rw [hpars ω, mul_assoc, mul_inv_cancel_left₀ hpi2]
  simp only [hrw]
  -- Step 2: the `u`-integral is measurable in `ω`, since `A_y(u)` sees `u` only through `⌊u⌋₊`
  have hstep : Measurable fun z : Ω × ℕ => smoothWeightedSum f y (z.2 : ℝ) z.1 :=
    measurable_from_prod_countable_left fun n => measurable_smoothWeightedSum hRa y (n : ℝ)
  have hA : Measurable fun z : Ω × ℝ => smoothWeightedSum f y z.2 z.1 := by
    have hcomp : (fun z : Ω × ℝ => smoothWeightedSum f y z.2 z.1)
        = (fun z : Ω × ℕ => smoothWeightedSum f y (z.2 : ℝ) z.1)
          ∘ fun z : Ω × ℝ => (z.1, ⌊z.2⌋₊) := by
      funext z
      simp only [Function.comp_apply, smoothWeightedSum, Nat.floor_natCast]
    rw [hcomp]
    exact hstep.comp (measurable_fst.prodMk (Nat.measurable_floor.comp measurable_snd))
  have hjm : Measurable fun z : Ω × ℝ =>
      ‖smoothWeightedSum f y z.2 z.1‖ ^ 2 / z.2 ^ (1 + 2 * σ) := by
    have hden : Measurable fun z : Ω × ℝ => z.2 ^ (1 + 2 * σ) :=
      (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + 2 * σ)).measurable.comp
        measurable_snd
    exact (hA.norm.pow_const 2).div hden
  have hsm : StronglyMeasurable fun ω : Ω =>
      ∫ u in Set.Ioi (0 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
    hjm.stronglyMeasurable.integral_prod_right'
  have hmq : Measurable fun ω : Ω => ((Real.log y)⁻¹ * (2 * Real.pi)
      * ∫ u in Set.Ioi (0 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ)) ^ q :=
    (Real.continuous_rpow_const hq0).measurable.comp (measurable_const.mul hsm.measurable)
  -- Step 3: `A_y` is bounded by `primorial y`, uniformly in `u`
  have hbnd : ∀ᵐ ω ∂μ, ∀ u : ℝ, ‖smoothWeightedSum f y u ω‖ ≤ (primorial y : ℝ) := by
    filter_upwards [MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n] with ω hb u
    rcases lt_or_ge (primorial y : ℝ) u with hgt | hle
    · rw [hEuler u hgt.le ω, ← hEuler ((primorial y : ℕ) : ℝ) le_rfl ω]
      refine le_trans (norm_smoothWeightedSum_le_of_bound hb y _) ?_
      rw [Nat.floor_natCast]
    · refine le_trans (norm_smoothWeightedSum_le_of_bound hb y u) ?_
      have hfl : ⌊u⌋₊ ≤ ⌊((primorial y : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hle
      rw [Nat.floor_natCast] at hfl
      exact_mod_cast hfl
  -- Step 4: the `u`-integral is at most `(primorial y)²/(2σ)`
  have hIbd : ∀ᵐ ω ∂μ,
      (∫ u in Set.Ioi (0 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        ≤ (primorial y : ℝ) ^ 2 / (2 * σ) := by
    filter_upwards [hbnd] with ω hω
    have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi zero_le_one
    have hsub' : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun u hu => hu.1
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
      Set.disjoint_left.2 fun u hu hu' => absurd hu.2 (not_le.2 hu')
    have hsplit : (∫ u in Set.Ioi (0 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        = (∫ u in Set.Ioc (0 : ℝ) 1, ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
          + ∫ u in Set.Ioi (1 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
      exact setIntegral_union hdisj measurableSet_Ioi ((hIint ω).mono_set hsub')
        ((hIint ω).mono_set hsub)
    have hlow : (∫ u in Set.Ioc (0 : ℝ) 1, ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        = 0 := by
      have h1 : (∫ u in Set.Ioc (0 : ℝ) 1, ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
          = ∫ u in Set.Ioo (0 : ℝ) 1, ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
        (setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1))).symm
      have h2 : Set.EqOn (fun u : ℝ => ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
          (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
        intro u hu
        change ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) = 0
        rw [smoothWeightedSum_eq_zero_of_lt_one f y hu.2 ω]
        simp
      rw [h1, setIntegral_congr_fun measurableSet_Ioo h2]
      simp
    have hmaj : IntegrableOn
        (fun u : ℝ => (primorial y : ℝ) ^ 2 * u ^ (-(1 + 2 * σ))) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    have hcmp : (∫ u in Set.Ioi (1 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))
        ≤ ∫ u in Set.Ioi (1 : ℝ), (primorial y : ℝ) ^ 2 * u ^ (-(1 + 2 * σ)) := by
      refine setIntegral_mono_on ((hIint ω).mono_set hsub) hmaj measurableSet_Ioi fun u hu => ?_
      have hu0 : (0 : ℝ) < u := lt_trans one_pos (Set.mem_Ioi.1 hu)
      have hnum : ‖smoothWeightedSum f y u ω‖ ^ 2 ≤ (primorial y : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hω u) 2
      rw [Real.rpow_neg hu0.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hu0.le _)
    have hval : (∫ u in Set.Ioi (1 : ℝ), (primorial y : ℝ) ^ 2 * u ^ (-(1 + 2 * σ)))
        = (primorial y : ℝ) ^ 2 / (2 * σ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
        show -(1 + 2 * σ) + 1 = -(2 * σ) by ring, neg_div_neg_eq, mul_one_div]
    rw [hsplit, hlow, zero_add]
    exact le_trans hcmp (le_of_eq hval)
  -- Step 5: bounded and measurable, hence in `L^∞`, hence integrable
  have hc0 : (0 : ℝ) ≤ (Real.log y)⁻¹ * (2 * Real.pi) :=
    mul_nonneg (inv_nonneg.2 (Real.log_natCast_nonneg y)) (by positivity)
  refine (memLp_top_of_bound hmq.aestronglyMeasurable
    (((Real.log y)⁻¹ * (2 * Real.pi) * ((primorial y : ℝ) ^ 2 / (2 * σ))) ^ q) ?_).integrable
    le_top
  filter_upwards [hIbd] with ω hω
  have h0 : (0 : ℝ) ≤ ∫ u in Set.Ioi (0 : ℝ),
      ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Set.mem_Ioi.1 hu).le _)
  have hprod : (0 : ℝ) ≤ (Real.log y)⁻¹ * (2 * Real.pi)
      * ∫ u in Set.Ioi (0 : ℝ), ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) :=
    mul_nonneg hc0 h0
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hprod q)]
  exact Real.rpow_le_rpow hprod (mul_le_mul_of_nonneg_left hω hc0) hq0

end RMF
