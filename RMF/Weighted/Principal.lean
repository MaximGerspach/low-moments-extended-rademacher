/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Conditional
import RMF.Weighted.Sieve

/-!
# Assembly, part 2: the principal term becomes the Euler-product line integral

`RMF.sum_weightedRoughTerm_le_setIntegral` leaves `(2/η)·∫_T ‖A_y(x/t)‖²·b(t) dt` with `b` the
sieve bound of `RMF.exists_sum_inv_sq_indicator_le_sqrt`.  Its leading part is
`≍ η/log y · ∫ ‖A_y(x/t)‖² dt/t`, and the `η` cancels the `2/η`.  The change of variable
`t ↦ x/t` (`RMF.integral_comp_div_div`) and Parseval
(`RMF.integral_normSq_smoothWeightedSum_eq_line`) then turn it into `Z`.

The merge of the sieve's two halves on `t ≥ y` and the change of variable hold for any
nonnegative function (`RMF.setIntegral_mul_sieveShape_le`); the band tail of the truncation bound
(`RMF/Weighted/BandTailSmoothing.lean`) reuses them.

## The two constants are different, and the second one is `e²`

Writing `η = 1/√y`, the sieve bound splits as

`b(t) = C(1+η)η/(t·log y) + C(1+η)²/(t²·log y)`,

and on `t ≥ y` the second term is at most `(1+η)/(yη)` times the first, i.e. `(1+η)η` times the
first, because `ηy = √y = 1/η`.  So the whole term is at most

`(2/η)·C·(1+η)²·(η/(1+η) + 1/y)/log y · ∫_T ‖A_y(x/t)‖² dt/t`,

whose prefactor is `C·(2(1+η) + 2η(1+η)²)/log y` — bounded, and **that is what the choice
`η = 1/√y` buys**: the `1/η = √y` in the second term is exactly cancelled by the `1/y`.

What does **not** happen is the constant staying the same.  The change of variable turns
`∫_T ‖A_y(x/t)‖² dt/t` into `∫_{1/(1+η)}^{x/y} ‖A_y(w)‖² dw/w`, and passing from `dw/w` to
`dw/w^{1+2σ}` costs `e²` (this is where `σ·log(x/y) ≤ 1` enters); Parseval then supplies a
`(2π)⁻¹`.  The surviving constant is `(2(1+η) + 2η(1+η)²)·e²/(2π)`, which for `η ≤ 1/2` is at
most `e²` but is **never below `e²/π ≈ 2.35`**.  So the sieve constant `C` cannot be reused on
the right: it is carried through unchanged (hence universally quantified) and the loss is the
separate absolute constant `e²`.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- `A_y(u) = 0` for `u < 1`: the summation range `Icc 1 ⌊u⌋₊` is empty.

This is what lets the change of variable land on `(1/(1+η), x/y)` — an interval reaching below
`1` — without any extra term. -/
lemma smoothWeightedSum_eq_zero_of_lt_one (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {u : ℝ}
    (hu : u < 1) (ω : Ω) : smoothWeightedSum f y u ω = 0 := by
  rw [smoothWeightedSum, Nat.floor_eq_zero.2 hu]
  simp

omit [MeasurableSpace Ω] in
/-- A crude bound on `A_y(u)` by the full weighted mass up to `v ≥ u`.

Unlike `RMF.norm_smoothWeightedSum_le_of_bound` this asks nothing of `f`, so it is available at
every `ω`; it is used only to see that the integrands below are bounded on a compact range. -/
lemma norm_smoothWeightedSum_le_sum (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {u v : ℝ}
    (huv : u ≤ v) (ω : Ω) :
    ‖smoothWeightedSum f y u ω‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊v⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro k hk
    have hk' := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
    exact Finset.mem_Icc.2 ⟨hk'.1, le_trans hk'.2 (Nat.floor_le_floor huv)⟩
  · exact fun k _ _ => norm_nonneg _

omit [MeasurableSpace Ω] in
/-- **Parseval's integrand is integrable.**  The companion of
`RMF.integral_normSq_smoothWeightedSum_eq_line`, which as an equation between integrals could
hold vacuously; it is `RMF.integrableOn_normSq_partialSum` at the same coefficients, whose
summability is free because they are supported on the finitely many squarefree `y`-smooth
numbers. -/
theorem integrableOn_normSq_smoothWeightedSum {X : ℕ → Ω → ℂ} (y : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (ω : Ω) :
    IntegrableOn (fun u : ℝ =>
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y u ω‖ ^ 2
          / u ^ (1 + 2 * σ)) (Set.Ioi (0 : ℝ)) := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set a : ℕ → ℂ := fun n => smoothCoeff f y ω n / (Real.sqrt n : ℂ) with hadef
  have hpart : ∀ u : ℝ, ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n = smoothWeightedSum f y u ω := by
    intro u
    rw [smoothWeightedSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hadef, smoothCoeff]
    by_cases h : n ∈ Nat.smoothNumbers (y + 1)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_div]
  have hsupp : ∀ n ∉ Finset.Icc 1 (primorial y), a n = 0 := by
    intro n hn
    simp only [hadef, smoothCoeff]
    by_cases hsm : n ∈ Nat.smoothNumbers (y + 1)
    · rw [if_pos hsm]
      have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsm
      have hsf : ¬ Squarefree n := by
        intro hsf
        have hp0 : 0 < primorial y := by
          rw [primorial]
          exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
        exact hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0,
          Nat.le_of_dvd hp0 (dvd_primorial_of_squarefree_of_mem_smoothNumbers hsf hsm)⟩)
      rw [hfdef]
      simp [squarefreeExtension_apply_of_not_squarefree _ hsf]
    · rw [if_neg hsm, zero_div]
  have hsum : Summable (coeffWeight σ a) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 (primorial y)) fun n hn => ?_
    rw [coeffWeight, hsupp n hn, norm_zero, zero_div]
  have key := integrableOn_normSq_partialSum σ a hσ hsum
  simp_rw [hpart] at key
  exact key

/-- `v/w ≤ e²·v/w^{1+s}` whenever `w^s ≤ e²`: the pointwise step from `dw/w` to `dw/w^{1+s}`,
stated so that it can also be used below `w = 1`. -/
lemma div_le_exp_two_mul_div_rpow {v w s : ℝ} (hv : 0 ≤ v) (hw : 0 < w)
    (hs : w ^ s ≤ Real.exp 2) : v / w ≤ Real.exp 2 * (v / w ^ (1 + s)) := by
  have hws : (0 : ℝ) < w ^ s := Real.rpow_pos_of_pos hw s
  have hsplit : w ^ (1 + s) = w * w ^ s := by rw [Real.rpow_add hw, Real.rpow_one]
  rw [hsplit, mul_div_assoc', div_le_div_iff₀ hw (mul_pos hw hws)]
  linarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hv hw.le)]

/-- **The numerical content of the choice `η = 1/√y`.**  With `η = 1/√y` the combined weight
`2(1+η)²(η/(1+η) + 1/y)/η` equals `2(1+η) + 2η(1+η)²`, which for `y ≥ 4` is at most `21/4 < 2π`.

The `1/y` is the second, `1/t²`, half of the sieve bound; that it survives division by `η` is
exactly the cancellation `1/(ηy) = 1/√y = η`. -/
lemma two_mul_sieve_shape_div_le {y : ℝ} (hy : 4 ≤ y) :
    2 * ((1 + 1 / Real.sqrt y) ^ 2 * ((1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1 / y)) /
        (1 / Real.sqrt y) ≤ 2 * Real.pi := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hs2 : (2 : ℝ) ≤ Real.sqrt y := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy
  have hysq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  have hinv : 1 / Real.sqrt y ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) < 1 / Real.sqrt y := by
    exact one_div_pos.2 hs0
  have h1η : (0 : ℝ) < 1 + 1 / Real.sqrt y := by linarith
  have hval : 2 * ((1 + 1 / Real.sqrt y) ^ 2 * ((1 / Real.sqrt y) / (1 + 1 / Real.sqrt y)
        + 1 / y)) / (1 / Real.sqrt y)
      = 2 * (1 + 1 / Real.sqrt y) + 2 * (1 + 1 / Real.sqrt y) ^ 2 / Real.sqrt y := by
    rw [show (1 : ℝ) / y = 1 / Real.sqrt y ^ 2 by rw [hysq]]
    field_simp
  rw [hval]
  have hsq : (1 + 1 / Real.sqrt y) ^ 2 ≤ 9 / 4 := by nlinarith
  have h2 : 2 * (1 + 1 / Real.sqrt y) ^ 2 / Real.sqrt y ≤ 9 / 4 := by
    rw [div_le_iff₀ hs0]
    nlinarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith

/-- **The principal term's first two steps, for any nonnegative function.**  On `t ≥ a` the two
halves of the sieve bound `C(1+η)²(tη/(1+η)+1)/(t²L)` merge into a single `dt/t`, the second
half's `1/t` bounded by `1/a`; the change of variable `t ↦ x/t` (`RMF.integral_comp_div_div`)
then carries `dt/t` on `[a, b]` to `dw/w` on `(x/b, x/a)`.  The head's
`RMF.setIntegral_normSq_mul_sieve_le` uses it at `g = ‖A_y‖²`, `a = y`; the band tail of the
truncation bound at `a = R`. -/
theorem setIntegral_mul_sieveShape_le (g : ℝ → ℝ) {x a b η C L : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hab : a ≤ b) (hη : 0 < η) (hC : 0 ≤ C) (hL : 0 < L) (hg : ∀ w, 0 ≤ g w)
    (hint : IntegrableOn (fun t => g (x / t) / t) (Set.Icc a b)) :
    (∫ t in Set.Icc a b, g (x / t) * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L)))
      ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / a)) / L
          * ∫ w in Set.Ioo (x / b) (x / a), g w / w := by
  have hpt : ∀ t ∈ Set.Icc a b,
      g (x / t) * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L))
        ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / a)) / L * (g (x / t) / t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
    have hA : (1 + η) ^ 2 * t ≤ (1 + η) ^ 2 * t ^ 2 / a := by
      rw [le_div_iff₀ ha]
      have h1 : t * a ≤ t * t := mul_le_mul_of_nonneg_left ht.1 ht0.le
      have h2 : (0 : ℝ) ≤ (1 + η) ^ 2 := sq_nonneg _
      nlinarith
    have hshrink : (1 + η) ^ 2 * (t * η / (1 + η) + 1) / t ^ 2
        ≤ (1 + η) ^ 2 * (η / (1 + η) + 1 / a) / t := by
      rw [div_le_div_iff₀ (pow_pos ht0 2) ht0,
        show (1 + η) ^ 2 * (t * η / (1 + η) + 1) * t
          = (1 + η) ^ 2 * (η / (1 + η)) * t ^ 2 + (1 + η) ^ 2 * t by ring,
        show (1 + η) ^ 2 * (η / (1 + η) + 1 / a) * t ^ 2
          = (1 + η) ^ 2 * (η / (1 + η)) * t ^ 2 + (1 + η) ^ 2 * t ^ 2 / a by ring]
      linarith
    have hc : (0 : ℝ) ≤ g (x / t) * (C / L) := mul_nonneg (hg _) (div_nonneg hC hL.le)
    calc g (x / t) * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L))
        = g (x / t) * (C / L) * ((1 + η) ^ 2 * (t * η / (1 + η) + 1) / t ^ 2) := by ring
      _ ≤ g (x / t) * (C / L) * ((1 + η) ^ 2 * (η / (1 + η) + 1 / a) / t) :=
          mul_le_mul_of_nonneg_left hshrink hc
      _ = C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / a)) / L * (g (x / t) / t) := by ring
  have hstep : (∫ t in Set.Icc a b,
        g (x / t) * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * L)))
      ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / a)) / L
          * ∫ t in Set.Icc a b, g (x / t) / t := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hint.const_mul _) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
      have hnum : (0 : ℝ) ≤ C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) :=
        mul_nonneg (mul_nonneg hC (sq_nonneg _)) (by positivity)
      exact mul_nonneg (hg _) (div_nonneg hnum (mul_nonneg (sq_nonneg _) hL.le))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hpt t ht
  have hchange : (∫ t in Set.Icc a b, g (x / t) / t)
      = ∫ w in Set.Ioo (x / b) (x / a), g w / w := by
    rw [← MeasureTheory.Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))]
    exact integral_comp_div_div hx ha hab g
  rwa [hchange] at hstep

omit [MeasurableSpace Ω] in
/-- **Assembly part 2, at one `ω` and an abstract window width.**
`(2/η)·∫_{[y, x(1+η)]} ‖A_y(x/t)‖²·b(t) dt ≤ e²·C·(log y)⁻¹·∫_ℝ ‖F_y(½+σ+it)/(σ+it)‖² dt`,
with `b` the sieve bound.  `η` is abstract and enters only through `hshape`, the one place the
choice `η = 1/√y` is used; `RMF.two_mul_sieve_shape_div_le` discharges it.  No hypothesis is placed
on `X`: the sum `A_y` is finite for every `ω`, and both the crude bound
`RMF.norm_smoothWeightedSum_le_sum` and Parseval hold unconditionally. -/
theorem setIntegral_normSq_mul_sieve_le {X : ℕ → Ω → ℂ} (y : ℕ) {σ x η C : ℝ}
    (hy : (0 : ℝ) < y) (hyx : (y : ℝ) ≤ x) (hσ : 0 < σ) (hσlog : σ * Real.log (x / y) ≤ 1)
    (hη : 0 < η) (hC : 0 < C) (hlogy : 0 < Real.log y)
    (hshape : 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / η ≤ 2 * Real.pi) (ω : Ω) :
    (2 / η) * (∫ t in Set.Icc ((y : ℝ)) (x * (1 + η)),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ Real.exp 2 * C * ((Real.log y)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hpars := integral_normSq_smoothWeightedSum_eq_line (X := X) y hσ ω
  have hIint := integrableOn_normSq_smoothWeightedSum (X := X) y hσ ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set P : ℝ := ∫ t : ℝ, ‖randomEulerProduct f (y + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 with hPdef
  -- elementary positivity
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hy hyx
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hb : (y : ℝ) ≤ x * (1 + η) := le_trans hyx (le_mul_of_one_le_right hx0.le (by linarith))
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  -- the crude bound on `A_y` over the range of integration
  have hgb : ∀ t ∈ Set.Icc ((y : ℝ)) (x * (1 + η)),
      ‖smoothWeightedSum f y (x / t) ω‖
        ≤ ∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖ :=
    fun t ht =>
      norm_smoothWeightedSum_le_sum f y (div_le_div_of_nonneg_left hx0.le hy ht.1) ω
  have hmeas : Measurable fun t : ℝ => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothWeightedSum f y (x / t) ω :=
      (measurable_smoothWeightedSum_truncation f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  have hint1 : IntegrableOn (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 / t)
      (Set.Icc ((y : ℝ)) (x * (1 + η))) volume := by
    refine Measure.integrableOn_of_bounded
      (M := (∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖) ^ 2 / (y : ℝ))
      measure_Icc_lt_top.ne (hmeas.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hy ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ht0.le)]
    calc ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 / t
        ≤ (∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖) ^ 2 / t := by
          gcongr
          exact hgb t ht
      _ ≤ (∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖) ^ 2 / (y : ℝ) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hy ht.1
  -- Steps 1-2: the sieve's two halves merge on `t ≥ y`, and `t ↦ x/t` preserves `dt/t`
  have hstep12 : (∫ t in Set.Icc ((y : ℝ)) (x * (1 + η)),
        ‖smoothWeightedSum f y (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
              ‖smoothWeightedSum f y w ω‖ ^ 2 / w :=
    setIntegral_mul_sieveShape_le (fun u => ‖smoothWeightedSum f y u ω‖ ^ 2) hx0 hy hb hη
      hC.le hlogy (fun _ => sq_nonneg _) hint1
  -- Step 3: `dw/w ≤ e² dw/w^{1+2σ}`, the only use of `σ·log(x/y) ≤ 1`
  have hlow : (0 : ℝ) < x / (x * (1 + η)) := div_pos hx0 (mul_pos hx0 h1η)
  have hsub : Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)) ⊆ Set.Ioi (0 : ℝ) :=
    fun w hw => lt_trans hlow hw.1
  have hcmp : ∀ w ∈ Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
      ‖smoothWeightedSum f y w ω‖ ^ 2 / w
        ≤ Real.exp 2 * (‖smoothWeightedSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := lt_trans hlow hw.1
    rcases lt_or_ge w 1 with hlt | hge
    · rw [smoothWeightedSum_eq_zero_of_lt_one f y hlt ω]
      simp
    · refine div_le_exp_two_mul_div_rpow (sq_nonneg _) hw0 ?_
      rw [Real.rpow_def_of_pos hw0]
      refine Real.exp_le_exp.2 ?_
      have hlogw : Real.log w ≤ Real.log (x / (y : ℝ)) := Real.log_le_log hw0 hw.2.le
      have hσ2 : (0 : ℝ) ≤ 2 * σ := by linarith
      have h1 : Real.log w * (2 * σ) ≤ Real.log (x / (y : ℝ)) * (2 * σ) :=
        mul_le_mul_of_nonneg_right hlogw hσ2
      have h2 : Real.log (x / (y : ℝ)) * (2 * σ) = 2 * (σ * Real.log (x / (y : ℝ))) := by ring
      linarith
  have hstep3 : (∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
        ‖smoothWeightedSum f y w ω‖ ^ 2 / w)
      ≤ Real.exp 2 * ∫ u in Set.Ioi (0 : ℝ),
          ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
    calc (∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
            ‖smoothWeightedSum f y w ω‖ ^ 2 / w)
        ≤ ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
            Real.exp 2 * (‖smoothWeightedSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
          refine integral_mono_of_nonneg ?_ ((hIint.mono_set hsub).const_mul _) ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact div_nonneg (sq_nonneg _) (lt_trans hlow hw.1).le
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact hcmp w hw
      _ = Real.exp 2 * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
            ‖smoothWeightedSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ) := integral_const_mul _ _
      _ ≤ Real.exp 2 * ∫ u in Set.Ioi (0 : ℝ),
            ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 2).le
          refine setIntegral_mono_set hIint ?_ (Filter.Eventually.of_forall fun w hw => hsub hw)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hu) _)
  -- the constant that survives
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hcoef : 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / η * (2 * Real.pi)⁻¹ ≤ 1 := by
    calc 2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / η * (2 * Real.pi)⁻¹
        ≤ 2 * Real.pi * (2 * Real.pi)⁻¹ :=
          mul_le_mul_of_nonneg_right hshape (inv_nonneg.2 hpi0.le)
      _ = 1 := mul_inv_cancel₀ hpi0.ne'
  have hRHS0 : (0 : ℝ) ≤ Real.exp 2 * C * ((Real.log y)⁻¹ * P) :=
    mul_nonneg (mul_nonneg (Real.exp_pos 2).le hC.le)
      (mul_nonneg (inv_nonneg.2 hlogy.le) hP0)
  calc (2 / η) * (∫ t in Set.Icc ((y : ℝ)) (x * (1 + η)),
          ‖smoothWeightedSum f y (x / t) ω‖ ^ 2
            * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ (2 / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
              ‖smoothWeightedSum f y w ω‖ ^ 2 / w) :=
        mul_le_mul_of_nonneg_left hstep12 (by positivity)
    _ ≤ (2 / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y
          * (Real.exp 2 * ∫ u in Set.Ioi (0 : ℝ),
              ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 ?_) (by positivity)
        exact div_nonneg (mul_nonneg hC.le (mul_nonneg (sq_nonneg _)
          (by positivity))) hlogy.le
    _ = (2 * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / η * (2 * Real.pi)⁻¹)
          * (Real.exp 2 * C * ((Real.log y)⁻¹ * P)) := by rw [hpars]; ring
    _ ≤ 1 * (Real.exp 2 * C * ((Real.log y)⁻¹ * P)) :=
        mul_le_mul_of_nonneg_right hcoef hRHS0
    _ = Real.exp 2 * C * ((Real.log y)⁻¹ * P) := one_mul _

/-- **Assembly part 2.**  The principal term of the smoothing is at most `e²` times the sieve
constant times `Z(ω) = (log y)⁻¹ ∫_ℝ ‖F_y(½+σ+it)/(σ+it)‖² dt`.  The sieve constant `C` is
**universally quantified**: it is whatever `RMF.exists_sum_inv_sq_indicator_le_sqrt` delivers and
passes through unchanged, and the absolute loss `e²`, from `dw/w` versus `dw/w^{1+2σ}`, is a
*separate* constant; with one `C` on both sides it would cancel, and the resulting inequality
with constant `1` is false. -/
theorem exists_setIntegral_normSq_mul_sieve_le :
    ∃ K y₀ : ℝ, 0 < K ∧ 0 < y₀ ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      ∀ C : ℝ, 0 < C → ∀ (y : ℕ) (σ x : ℝ), 2 ≤ y → y₀ ≤ (y : ℝ) → (y : ℝ) ≤ x → 0 < σ →
        σ * Real.log (x / y) ≤ 1 →
      ∀ᵐ ω ∂μ, (2 / (1 / Real.sqrt y)) * (∫ t in Set.Icc ((y : ℝ)) (x * (1 + 1 / Real.sqrt y)),
            ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2
              * (C * (1 + 1 / Real.sqrt y) ^ 2 * (t * (1 / Real.sqrt y) / (1 + 1 / Real.sqrt y) + 1)
                  / (t ^ 2 * Real.log y)))
        ≤ K * C * ((Real.log y)⁻¹ * ∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  refine ⟨Real.exp 2, 4, Real.exp_pos 2, by norm_num, ?_⟩
  intro Ω' _ X μ C hC y σ x _hy2 hy0 hyx hσ hσlog
  refine Filter.Eventually.of_forall fun ω => ?_
  have hy : (0 : ℝ) < (y : ℝ) := by linarith
  have hη : (0 : ℝ) < 1 / Real.sqrt y := one_div_pos.2 (Real.sqrt_pos.2 hy)
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  exact setIntegral_normSq_mul_sieve_le y hy hyx hσ hσlog hη hC hlogy
    (two_mul_sieve_shape_div_le hy0) ω

end RMF
