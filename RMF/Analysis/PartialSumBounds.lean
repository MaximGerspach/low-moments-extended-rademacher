/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.FourierTransform
import RMF.Analysis.FourierPlancherel
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Partial sums of a Dirichlet-series coefficient sequence

Throughout, `a : ℕ → ℂ` is a coefficient sequence, `σ > 0` an abscissa, and
`A(u) = ∑_{1 ≤ n ≤ u} aₙ` the summatory function.  The standing hypothesis is
`S := ∑ ‖aₙ‖/n^σ < ∞`.

That hypothesis is exactly what Parseval for Dirichlet series (Montgomery–Vaughan (5.26)) needs,
and the reason is this file: writing `bₙ = ‖aₙ‖/n^σ`, Cauchy–Schwarz in the form

`‖A(u)‖² ≤ (∑_{n ≤ u} bₙ) · (∑_{n ≤ u} bₙ n^{2σ}) ≤ S · ∑_{n ≤ u} bₙ n^{2σ}`

converts the hypothesis into a bound on `∫₀^∞ ‖A(u)‖²/u^{1+2σ} du`, after which
`∫_n^∞ bₙ n^{2σ}/u^{1+2σ} du = bₙ/(2σ)` gives `∫₀^∞ ‖A(u)‖²/u^{1+2σ} du ≤ S²/(2σ)`.

The crude bound `‖A(u)‖ ≤ u^σ ∑_{n ≤ u} bₙ ≤ S u^σ` is *not* enough: it gives
`‖A(u)‖²/u^{1+2σ} ≤ S²/u`, which is not integrable at infinity.  Splitting the weight unevenly
between the two Cauchy–Schwarz factors is what makes the integral converge.

## The shift

Everything is stated for a general `σ > 0` rather than only for `σ = 1/2`.  The upper-bound
half of Harper's theorem uses only the critical line, and the `_half` specialisation
at the end is the `σ = 1/2` specialisation it consumes; the *lower* bound needs the same identity
at `σ = 1/2 + 4V/log x`, off the critical line, which is why the abscissa is carried throughout.
-/

open MeasureTheory

open scoped ENNReal FourierTransform

namespace RMF

variable (σ : ℝ) (a : ℕ → ℂ)

/-- `bₙ = ‖aₙ‖/n^σ`, the weight in which the hypothesis of Parseval is stated. -/
noncomputable def coeffWeight (n : ℕ) : ℝ := ‖a n‖ / (n : ℝ) ^ σ

lemma coeffWeight_nonneg (n : ℕ) : 0 ≤ coeffWeight σ a n := by
  unfold coeffWeight
  positivity

/-- The `σ`-power of a positive natural, squared. -/
lemma rpow_sq_eq {n : ℕ} (hn : 1 ≤ n) : ((n : ℝ) ^ σ) ^ 2 = (n : ℝ) ^ (2 * σ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_natCast ((n : ℝ) ^ σ) 2, ← Real.rpow_mul hn0.le]
  norm_num
  rw [mul_comm]

/-- Each `‖aₙ‖` is the geometric mean of the two Cauchy–Schwarz weights. -/
lemma sqrt_coeffWeight_mul_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (coeffWeight σ a n) * Real.sqrt (coeffWeight σ a n * (n : ℝ) ^ (2 * σ))
      = ‖a n‖ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos hn0 σ).ne'
  rw [← Real.sqrt_mul (coeffWeight_nonneg σ a n)]
  have hval : coeffWeight σ a n * (coeffWeight σ a n * (n : ℝ) ^ (2 * σ)) = ‖a n‖ ^ 2 := by
    rw [← rpow_sq_eq σ hn]
    unfold coeffWeight
    field_simp
  rw [hval, Real.sqrt_sq (norm_nonneg _)]

/-- **The Cauchy–Schwarz bound on a partial sum.**  Splitting `‖aₙ‖ = √bₙ · √(bₙ n^{2σ})` and
applying Cauchy–Schwarz keeps one factor bounded by `S` while the other carries the `n^{2σ}`,
which is what makes the resulting integral converge. -/
lemma norm_sum_Icc_sq_le (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, a n‖ ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n)
        * ∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n * (n : ℝ) ^ (2 * σ) := by
  have hnn : ∀ n : ℕ, 0 ≤ coeffWeight σ a n * (n : ℝ) ^ (2 * σ) := fun n =>
    mul_nonneg (coeffWeight_nonneg σ a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsum : ∑ n ∈ Finset.Icc 1 N, ‖a n‖
      ≤ Real.sqrt (∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n)
        * Real.sqrt (∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n * (n : ℝ) ^ (2 * σ)) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n hn => ?_))
      (Real.sum_sqrt_mul_sqrt_le _ (coeffWeight_nonneg σ a) hnn)
    exact (sqrt_coeffWeight_mul_sqrt σ a n (Finset.mem_Icc.1 hn).1).symm
  calc ‖∑ n ∈ Finset.Icc 1 N, a n‖ ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Real.sqrt (∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n * (n : ℝ) ^ (2 * σ))) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hsum 2
    _ = (∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n)
          * ∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n * (n : ℝ) ^ (2 * σ) := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun n _ => coeffWeight_nonneg σ a n),
          Real.sq_sqrt (Finset.sum_nonneg fun n _ => hnn n)]

/-- The first Cauchy–Schwarz factor is bounded by the whole sum. -/
lemma sum_coeffWeight_le_tsum (ha : Summable (coeffWeight σ a)) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n ≤ ∑' n, coeffWeight σ a n :=
  ha.sum_le_tsum _ (fun n _ => coeffWeight_nonneg σ a n)

/-- **The partial sum against the tail-uniform bound.**  `‖A(N)‖² ≤ S · ∑_{n ≤ N} bₙ n^{2σ}`, with
`S = ∑ bₙ` independent of `N`; only the second factor grows with `N`, and it grows slowly enough
that the domination below converges. -/
lemma norm_sum_Icc_sq_le_tsum_mul (ha : Summable (coeffWeight σ a)) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, a n‖ ^ 2
      ≤ (∑' n, coeffWeight σ a n) * ∑ n ∈ Finset.Icc 1 N, coeffWeight σ a n * (n : ℝ) ^ (2 * σ) :=
  le_trans (norm_sum_Icc_sq_le σ a N)
    (mul_le_mul_of_nonneg_right (sum_coeffWeight_le_tsum σ a ha N)
      (Finset.sum_nonneg fun n _ =>
        mul_nonneg (coeffWeight_nonneg σ a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)))

/-! ### The tail integrals

`∫_c^∞ k/u^{1+ρ} du = k c^{-ρ}/ρ` for `ρ > 0`, in both the Bochner and the `ℝ≥0∞` form.  Used at
`ρ = 2σ` for the `L²` bound and at `ρ = σ` for the `L¹` bound. -/

lemma integrableOn_div_rpow {ρ : ℝ} (hρ : 0 < ρ) {k : ℝ} {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => k / u ^ (1 + ρ)) (Set.Ioi c) := by
  refine IntegrableOn.congr_fun
    ((integrableOn_Ioi_rpow_of_lt (a := -(1 + ρ)) (by linarith) hc).const_mul k)
    (fun u hu => ?_) measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := lt_trans hc (Set.mem_Ioi.1 hu)
  rw [Real.rpow_neg hu0.le]
  ring

lemma integral_div_rpow {ρ : ℝ} (hρ : 0 < ρ) {k : ℝ} {c : ℝ} (hc : 0 < c) :
    ∫ u in Set.Ioi c, k / u ^ (1 + ρ) = k * c ^ (-ρ) / ρ := by
  have hcongr : ∀ u ∈ Set.Ioi c, k / u ^ (1 + ρ) = k * u ^ (-(1 + ρ) : ℝ) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans hc (Set.mem_Ioi.1 hu)
    rw [Real.rpow_neg hu0.le]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hc, show -(1 + ρ) + 1 = -ρ by ring]
  field_simp

lemma lintegral_ofReal_div_rpow {ρ : ℝ} (hρ : 0 < ρ) {k : ℝ} (hk : 0 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∫⁻ u in Set.Ioi c, ENNReal.ofReal (k / u ^ (1 + ρ))
      = ENNReal.ofReal (k * c ^ (-ρ) / ρ) := by
  rw [← integral_div_rpow hρ (k := k) hc]
  refine (ofReal_integral_eq_lintegral_ofReal (integrableOn_div_rpow hρ hc) ?_).symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact div_nonneg hk (Real.rpow_nonneg (lt_trans hc hu).le _)

/-! ### The `L²` bound

`∫₀^∞ ‖A(u)‖²/u^{1+2σ} du ≤ S²/(2σ)`.  The domination is by the family
`Fₙ(u) = S bₙ n^{2σ}/u^{1+2σ} · 1_{u ≥ n}`, whose total integral is `∑ₙ S bₙ/(2σ) = S²/(2σ)`.
Since the integrand vanishes for `u ≤ 0` (the sum is empty there), the argument runs over all of
`ℝ`, which avoids restricting the measure twice. -/

theorem lintegral_normSq_partialSum_le (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ))
      ≤ ENNReal.ofReal ((∑' n, coeffWeight σ a n) ^ 2 / (2 * σ)) := by
  have hσ2 : (0 : ℝ) < 2 * σ := by linarith
  have hS0 : 0 ≤ ∑' n, coeffWeight σ a n := tsum_nonneg (coeffWeight_nonneg σ a)
  set S : ℝ := ∑' n, coeffWeight σ a n with hSdef
  set F : ℕ → ℝ → ℝ≥0∞ := fun n u => Set.indicator (Set.Ici (n : ℝ))
    (fun u => ENNReal.ofReal (S * (coeffWeight σ a n * (n : ℝ) ^ (2 * σ)) / u ^ (1 + 2 * σ))) u
    with hFdef
  have hnn : ∀ n : ℕ, 0 ≤ S * (coeffWeight σ a n * (n : ℝ) ^ (2 * σ)) := fun n =>
    mul_nonneg hS0 (mul_nonneg (coeffWeight_nonneg σ a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hmeas : ∀ n, AEMeasurable (F n) (volume : Measure ℝ) := fun n =>
    (Measurable.indicator (ENNReal.measurable_ofReal.comp (by fun_prop))
      measurableSet_Ici).aemeasurable
  -- each term integrates to `S bₙ/(2σ)`
  have hval : ∀ n : ℕ, ∫⁻ u, F n u = ENNReal.ofReal (S * coeffWeight σ a n / (2 * σ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hFdef, coeffWeight, Real.zero_rpow hσ.ne']
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnne : ((n : ℝ) ^ (2 * σ)) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
      simp only [hFdef]
      rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm,
        lintegral_ofReal_div_rpow hσ2 (hnn n) hn0]
      congr 1
      rw [Real.rpow_neg hn0.le]
      field_simp
  -- pointwise domination, valid on all of `ℝ`
  have hdom : ∀ u : ℝ,
      ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ)) ≤ ∑' n, F n u := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      simp [hfl]
    · have hsupp : ∀ n ∉ Finset.range (⌊u⌋₊ + 1), F n u = 0 := by
        intro n hn
        rw [Finset.mem_range] at hn
        push Not at hn
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_Ici, not_le]
        have hlt : (⌊u⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
        linarith [Nat.lt_floor_add_one u]
      have hmem : ∀ n ∈ Finset.range (⌊u⌋₊ + 1),
          F n u = ENNReal.ofReal
            (S * (coeffWeight σ a n * (n : ℝ) ^ (2 * σ)) / u ^ (1 + 2 * σ)) := by
        intro n hn
        rw [Finset.mem_range] at hn
        refine Set.indicator_of_mem ?_ _
        exact Set.mem_Ici.2 ((Nat.le_floor_iff hu.le).1 (by omega))
      have hsplit : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, coeffWeight σ a n * (n : ℝ) ^ (2 * σ)
          = ∑ n ∈ Finset.range (⌊u⌋₊ + 1), coeffWeight σ a n * (n : ℝ) ^ (2 * σ) := by
        refine Finset.sum_subset (fun n hn => ?_) (fun n hnt hns => ?_)
        · rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega
        · rw [Finset.mem_range] at hnt
          simp only [Finset.mem_Icc, not_and, not_le] at hns
          have hz : n = 0 := by by_contra h; exact absurd (hns (by omega)) (by omega)
          simp [hz, coeffWeight, Real.zero_rpow hσ.ne']
      rw [tsum_eq_sum hsupp, Finset.sum_congr rfl hmem,
        ← ENNReal.ofReal_sum_of_nonneg
          (fun n _ => div_nonneg (hnn n) (Real.rpow_nonneg hu.le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Finset.sum_div, ← Finset.mul_sum, ← hsplit]
      exact div_le_div_of_nonneg_right (norm_sum_Icc_sq_le_tsum_mul σ a ha ⌊u⌋₊)
        (Real.rpow_nonneg hu.le _)
  calc ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ))
      ≤ ∫⁻ u, ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ)) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ u, ∑' n, F n u := lintegral_mono hdom
    _ = ∑' n, ∫⁻ u, F n u := lintegral_tsum hmeas
    _ = ∑' n, ENNReal.ofReal (S * coeffWeight σ a n / (2 * σ)) := by simp_rw [hval]
    _ = ENNReal.ofReal (∑' n, S * coeffWeight σ a n / (2 * σ)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => div_nonneg (mul_nonneg hS0 (coeffWeight_nonneg σ a n)) hσ2.le)
          (((ha.mul_left S).div_const (2 * σ)))).symm
    _ = ENNReal.ofReal (S ^ 2 / (2 * σ)) := by
        simp_rw [div_eq_mul_inv, tsum_mul_right, tsum_mul_left, ← hSdef, sq]

/-! ### The two conclusions Parseval consumes -/

lemma measurable_normSq_partialSum :
    Measurable fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ) := by
  refine Measurable.div ?_ (by fun_prop)
  exact ((measurable_from_top (f := fun N : ℕ => ‖∑ n ∈ Finset.Icc 1 N, a n‖ ^ 2)).comp
    Nat.measurable_floor)

lemma nonneg_normSq_partialSum {u : ℝ} (hu : 0 < u) :
    0 ≤ ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ) :=
  div_nonneg (sq_nonneg _) (Real.rpow_nonneg hu.le _)

/-- **The integrand of Parseval is integrable.**  In Lean an integral of a non-integrable function
is `0`, so an equation between two integrals can hold vacuously; this is what stops
`RMF.integral_normSq_partialSum_eq_line` from being weaker than it looks. -/
theorem integrableOn_normSq_partialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ))
      (Set.Ioi (0 : ℝ)) := by
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact nonneg_normSq_partialSum σ a hu
  refine ⟨(measurable_normSq_partialSum σ a).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hae]
  exact lt_of_le_of_lt (lintegral_normSq_partialSum_le σ a hσ ha) ENNReal.ofReal_lt_top

/-! ### The `L¹` bound

`∫₀^∞ ‖A(u)‖ u^{-1-σ} du ≤ S/σ`.  Same domination as for `L²`, but with the *whole* weight on the
`n`-side: `‖aₙ‖ = bₙ n^σ` and `∫_n^∞ u^{-1-σ} du = n^{-σ}/σ`, so the two `n^σ` cancel and the sum
is `S/σ`.  This is what puts `v ↦ A(eᵛ)e^{-σv}` in `L¹`, which `RMF.coeFn_fourier_toLp` needs
alongside the `L²` bound. -/

lemma norm_eq_coeffWeight_mul_rpow {n : ℕ} (hn : 1 ≤ n) :
    coeffWeight σ a n * (n : ℝ) ^ σ = ‖a n‖ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos hn0 σ).ne'
  unfold coeffWeight
  field_simp

theorem lintegral_norm_partialSum_le (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ))
      ≤ ENNReal.ofReal ((∑' n, coeffWeight σ a n) / σ) := by
  have hS0 : 0 ≤ ∑' n, coeffWeight σ a n := tsum_nonneg (coeffWeight_nonneg σ a)
  set G : ℕ → ℝ → ℝ≥0∞ := fun n u => Set.indicator (Set.Ici (n : ℝ))
    (fun u => ENNReal.ofReal (coeffWeight σ a n * (n : ℝ) ^ σ / u ^ (1 + σ))) u with hGdef
  have hnn : ∀ n : ℕ, 0 ≤ coeffWeight σ a n * (n : ℝ) ^ σ := fun n =>
    mul_nonneg (coeffWeight_nonneg σ a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hmeas : ∀ n, AEMeasurable (G n) (volume : Measure ℝ) := fun n =>
    (Measurable.indicator (ENNReal.measurable_ofReal.comp (by fun_prop))
      measurableSet_Ici).aemeasurable
  have hval : ∀ n : ℕ, ∫⁻ u, G n u = ENNReal.ofReal (coeffWeight σ a n / σ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hGdef, coeffWeight, Real.zero_rpow hσ.ne']
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnne : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos hn0 σ).ne'
      simp only [hGdef]
      rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm,
        lintegral_ofReal_div_rpow hσ (hnn n) hn0]
      congr 1
      rw [Real.rpow_neg hn0.le]
      field_simp
  have hdom : ∀ u : ℝ,
      ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ)) ≤ ∑' n, G n u := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      simp [hfl]
    · have hsupp : ∀ n ∉ Finset.range (⌊u⌋₊ + 1), G n u = 0 := by
        intro n hn
        rw [Finset.mem_range] at hn
        push Not at hn
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_Ici, not_le]
        have hlt : (⌊u⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
        linarith [Nat.lt_floor_add_one u]
      have hmem : ∀ n ∈ Finset.range (⌊u⌋₊ + 1),
          G n u = ENNReal.ofReal (coeffWeight σ a n * (n : ℝ) ^ σ / u ^ (1 + σ)) := by
        intro n hn
        rw [Finset.mem_range] at hn
        refine Set.indicator_of_mem ?_ _
        exact Set.mem_Ici.2 ((Nat.le_floor_iff hu.le).1 (by omega))
      have hsplit : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, coeffWeight σ a n * (n : ℝ) ^ σ
          = ∑ n ∈ Finset.range (⌊u⌋₊ + 1), coeffWeight σ a n * (n : ℝ) ^ σ := by
        refine Finset.sum_subset (fun n hn => ?_) (fun n hnt hns => ?_)
        · rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega
        · rw [Finset.mem_range] at hnt
          simp only [Finset.mem_Icc, not_and, not_le] at hns
          have hz : n = 0 := by by_contra h; exact absurd (hns (by omega)) (by omega)
          simp [hz, coeffWeight, Real.zero_rpow hσ.ne']
      rw [tsum_eq_sum hsupp, Finset.sum_congr rfl hmem,
        ← ENNReal.ofReal_sum_of_nonneg
          (fun n _ => div_nonneg (hnn n) (Real.rpow_nonneg hu.le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Finset.sum_div, ← hsplit]
      refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hu.le _)
      refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun n hn => ?_))
      exact (norm_eq_coeffWeight_mul_rpow σ a (Finset.mem_Icc.1 hn).1).symm
  calc ∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ))
      ≤ ∫⁻ u, ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ)) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ u, ∑' n, G n u := lintegral_mono hdom
    _ = ∑' n, ∫⁻ u, G n u := lintegral_tsum hmeas
    _ = ∑' n, ENNReal.ofReal (coeffWeight σ a n / σ) := by simp_rw [hval]
    _ = ENNReal.ofReal (∑' n, coeffWeight σ a n / σ) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => div_nonneg (coeffWeight_nonneg σ a n) hσ.le) (ha.div_const σ)).symm
    _ = ENNReal.ofReal ((∑' n, coeffWeight σ a n) / σ) := by
        simp_rw [div_eq_mul_inv, tsum_mul_right]

lemma measurable_norm_partialSum :
    Measurable fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ) := by
  refine Measurable.div ?_ (by fun_prop)
  exact (measurable_from_top (f := fun N : ℕ => ‖∑ n ∈ Finset.Icc 1 N, a n‖)).comp
    Nat.measurable_floor

lemma nonneg_norm_partialSum {u : ℝ} (hu : 0 < u) :
    0 ≤ ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ) :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg hu.le _)

/-- **The integrand is integrable on `(0,∞)`.**  Together with
`RMF.integrableOn_normSq_partialSum` this says `v ↦ A(eᵛ)e^{-σv}` lies in `L¹ ∩ L²`, which is
what `RMF.coeFn_fourier_toLp` asks of it. -/
theorem integrableOn_norm_partialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ))
      (Set.Ioi (0 : ℝ)) := by
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact nonneg_norm_partialSum σ a hu
  refine ⟨(measurable_norm_partialSum σ a).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hae]
  exact lt_of_le_of_lt (lintegral_norm_partialSum_le σ a hσ ha) ENNReal.ofReal_lt_top

/-! ### The Mellin representation

`∫₀^∞ A(u) u^{-s-1} du = D(s)/s` on the line `Re s = σ`, where `D(s) = ∑ aₙ n^{-s}`.

This is the identity Parseval's right-hand side needs, and it is the *same* interchange as the
`L¹` bound rather than an Abel summation: `A(u) = ∑ₙ aₙ 1_{u≥n}` and `∫_n^∞ u^{-s-1} du = n^{-s}/s`,
so the sum telescopes into `D(s)/s` directly.  The dominating series is `∑ₙ bₙ/σ = S/σ`, i.e.
exactly the `L¹` bound, which is why the hypothesis is the same one. -/

/-- The `n`-th piece of `A(u) u^{-s-1}`: `aₙ u^{-s-1}` for `u ≥ n`, and `0` otherwise.  The `n = 0`
case is excluded by hand, since `A` sums from `1`. -/
noncomputable def mellinTerm (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  if n = 0 then 0 else Set.indicator (Set.Ici (n : ℝ)) (fun u => a n * (u : ℂ) ^ (-s - 1)) u

/-- `∫_c^∞ u^{-s-1} du = c^{-s}/s` for `Re s > 0`. -/
lemma integral_Ioi_cpow_neg_sub_one {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    ∫ u in Set.Ioi c, (u : ℂ) ^ (-s - 1) = (c : ℂ) ^ (-s) / s := by
  have hre : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [integral_Ioi_cpow_of_lt hre hc, show -s - 1 + 1 = -s by ring, neg_div_neg_eq]

/-- Each piece integrates to the corresponding term of `D(s)/s`. -/
lemma integral_mellinTerm {s : ℂ} (hs : 0 < s.re) (hs0 : s ≠ 0) (n : ℕ) :
    ∫ u in Set.Ioi (0 : ℝ), mellinTerm a s n u = a n / (n : ℂ) ^ s / s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mellinTerm, Complex.zero_cpow hs0]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsub : Set.Ioi (0 : ℝ) ∩ Set.Ici (n : ℝ) = Set.Ici (n : ℝ) :=
      Set.inter_eq_right.2 (fun u hu => lt_of_lt_of_le hn0 (Set.mem_Ici.1 hu))
    simp only [mellinTerm, if_neg hn.ne']
    rw [setIntegral_indicator measurableSet_Ici, hsub,
      setIntegral_congr_set Ioi_ae_eq_Ici.symm, integral_const_mul,
      integral_Ioi_cpow_neg_sub_one hs hn0, Complex.cpow_neg, Complex.ofReal_natCast]
    field_simp

/-- The pieces are dominated by the `L¹` weights, term by term. -/
lemma lintegral_enorm_mellinTerm (hσ : 0 < σ) {s : ℂ} (hs : s.re = σ) (n : ℕ) :
    ∫⁻ u in Set.Ioi (0 : ℝ), ‖mellinTerm a s n u‖ₑ
      = ENNReal.ofReal (coeffWeight σ a n / σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mellinTerm, coeffWeight, Real.zero_rpow hσ.ne']
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnne : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos hn0 σ).ne'
    have hsub : Set.Ici (n : ℝ) ∩ Set.Ioi (0 : ℝ) = Set.Ici (n : ℝ) :=
      Set.inter_eq_left.2 (fun u hu => lt_of_lt_of_le hn0 (Set.mem_Ici.1 hu))
    have hpt : ∀ u ∈ Set.Ici (n : ℝ),
        ‖a n * (u : ℂ) ^ (-s - 1)‖ₑ = ENNReal.ofReal (‖a n‖ / u ^ (1 + σ)) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hn0 (Set.mem_Ici.1 hu)
      rw [← ofReal_norm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
        show (-s - 1).re = -(1 + σ) by
          simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, hs]; ring,
        Real.rpow_neg hu0.le]
      ring_nf
    have henorm : (fun u : ℝ =>
        ‖Set.indicator (Set.Ici (n : ℝ)) (fun u => a n * (u : ℂ) ^ (-s - 1)) u‖ₑ)
        = Set.indicator (Set.Ici (n : ℝ)) (fun u => ‖a n * (u : ℂ) ^ (-s - 1)‖ₑ) :=
      (Set.indicator_comp_of_zero (g := fun z : ℂ => ‖z‖ₑ) (by simp)).symm
    simp only [mellinTerm, if_neg hn.ne']
    rw [henorm, lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hsub,
      setLIntegral_congr_fun measurableSet_Ici hpt, setLIntegral_congr Ioi_ae_eq_Ici.symm,
      lintegral_ofReal_div_rpow hσ (norm_nonneg _) hn0]
    congr 1
    rw [Real.rpow_neg hn0.le]
    unfold coeffWeight
    field_simp

lemma measurable_mellinTerm (s : ℂ) (n : ℕ) : Measurable (mellinTerm a s n) := by
  unfold mellinTerm
  split
  · exact measurable_const
  · exact Measurable.indicator (by fun_prop) measurableSet_Ici

/-- **The Mellin representation.**  `∫₀^∞ A(u) u^{-s-1} du = D(s)/s` on `Re s = σ`.

The interchange is legitimate because the dominating series is `∑ₙ bₙ/σ = S/σ`, which is the
`L¹` bound; no analytic continuation and no conditional convergence appear anywhere. -/
theorem integral_partialSum_cpow (hσ : 0 < σ) (ha : Summable (coeffWeight σ a))
    {s : ℂ} (hs : s.re = σ) :
    ∫ u in Set.Ioi (0 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) * (u : ℂ) ^ (-s - 1)
      = (∑' n : ℕ, a n / (n : ℂ) ^ s) / s := by
  have hsre : 0 < s.re := by rw [hs]; exact hσ
  have hs0 : s ≠ 0 := fun h => by simp [h] at hsre
  -- the integrand is the sum of the pieces
  have hptwise : ∀ u ∈ Set.Ioi (0 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) * (u : ℂ) ^ (-s - 1)
        = ∑' n, mellinTerm a s n u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hsupp : ∀ n ∉ Finset.Icc 1 ⌊u⌋₊, mellinTerm a s n u = 0 := by
      intro n hn
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      unfold mellinTerm
      split
      · rfl
      · rename_i hne
        refine Set.indicator_of_notMem ?_ _
        simp only [Set.mem_Ici, not_le]
        have hlt : ⌊u⌋₊ < n := hn (Nat.one_le_iff_ne_zero.2 hne)
        have hc : (⌊u⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
        linarith [Nat.lt_floor_add_one u]
    have hmem : ∀ n ∈ Finset.Icc 1 ⌊u⌋₊, mellinTerm a s n u = a n * (u : ℂ) ^ (-s - 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      unfold mellinTerm
      rw [if_neg (by omega)]
      exact Set.indicator_of_mem (Set.mem_Ici.2 ((Nat.le_floor_iff hu0.le).1 hn.2)) _
    rw [tsum_eq_sum hsupp, Finset.sum_congr rfl hmem, ← Finset.sum_mul]
  -- the interchange is dominated by the `L¹` bound
  have hfin : ∑' n, ∫⁻ u in Set.Ioi (0 : ℝ), ‖mellinTerm a s n u‖ₑ ≠ ∞ := by
    simp_rw [lintegral_enorm_mellinTerm σ a hσ hs]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => div_nonneg (coeffWeight_nonneg σ a n) hσ.le) (ha.div_const σ)]
    exact ENNReal.ofReal_ne_top
  rw [setIntegral_congr_fun measurableSet_Ioi hptwise,
    integral_tsum (fun n => (measurable_mellinTerm a s n).aestronglyMeasurable) hfin]
  simp_rw [integral_mellinTerm a hsre hs0]
  exact tsum_div_const

/-! ### The logarithmic change of variables

`u = eᵛ` turns `∫₀^∞ · du` into `∫_ℝ eᵛ · dv`, and carries `A(u)u^{-σ}` to `g(v) = A(eᵛ)e^{-σv}`.
Both bounds transfer verbatim, and `g` is the function Plancherel is applied to. -/

lemma image_exp_univ : Real.exp '' Set.univ = Set.Ioi (0 : ℝ) := by
  rw [Set.image_univ, Real.range_exp]

lemma exp_rpow (v c : ℝ) : Real.exp v ^ c = Real.exp (v * c) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]

lemma integral_Ioi_eq_integral_exp (φ : ℝ → ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), φ u = ∫ v : ℝ, Real.exp v * φ (Real.exp v) := by
  rw [← image_exp_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul, Measure.restrict_univ]

lemma integrableOn_Ioi_iff_integrable_exp (φ : ℝ → ℝ) :
    IntegrableOn φ (Set.Ioi (0 : ℝ)) ↔ Integrable fun v : ℝ => Real.exp v * φ (Real.exp v) := by
  rw [← image_exp_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul, IntegrableOn, Measure.restrict_univ]

/-- `g(v) = A(eᵛ) e^{-σv}`, the function whose Fourier transform is `D(s)/s`. -/
noncomputable def logPartialSum (v : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n) * (Real.exp (-σ * v) : ℂ)

lemma norm_logPartialSum (v : ℝ) :
    ‖logPartialSum σ a v‖
      = Real.exp (-σ * v) * ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ := by
  rw [logPartialSum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

lemma measurable_logPartialSum : Measurable (logPartialSum σ a) := by
  unfold logPartialSum
  refine Measurable.mul ?_ (by fun_prop)
  exact ((measurable_from_top (f := fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n))).comp
    (Nat.measurable_floor.comp Real.measurable_exp))

lemma exp_mul_norm_eq (v : ℝ) :
    Real.exp v * (‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ / Real.exp v ^ (1 + σ))
      = ‖logPartialSum σ a v‖ := by
  have h : Real.exp v / Real.exp (v * (1 + σ)) = Real.exp (-σ * v) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [norm_logPartialSum, exp_rpow]
  calc Real.exp v * (‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ / Real.exp (v * (1 + σ)))
      = (Real.exp v / Real.exp (v * (1 + σ)))
          * ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ := by ring
    _ = Real.exp (-σ * v) * ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ := by rw [h]

lemma exp_mul_normSq_eq (v : ℝ) :
    Real.exp v * (‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ ^ 2 / Real.exp v ^ (1 + 2 * σ))
      = ‖logPartialSum σ a v‖ ^ 2 := by
  have h : Real.exp v / Real.exp (v * (1 + 2 * σ)) = Real.exp (-σ * v) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [norm_logPartialSum, exp_rpow]
  calc Real.exp v * (‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ ^ 2 / Real.exp (v * (1 + 2 * σ)))
      = (Real.exp v / Real.exp (v * (1 + 2 * σ)))
          * ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖ ^ 2 := by ring
    _ = (Real.exp (-σ * v) * ‖∑ n ∈ Finset.Icc 1 ⌊Real.exp v⌋₊, a n‖) ^ 2 := by
        rw [h]; ring

lemma integral_normSq_logPartialSum :
    ∫ v : ℝ, ‖logPartialSum σ a v‖ ^ 2
      = ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ) := by
  rw [integral_Ioi_eq_integral_exp]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun v => (exp_mul_normSq_eq σ a v).symm)

lemma integrable_logPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    Integrable (logPartialSum σ a) :=
  (integrable_norm_iff (measurable_logPartialSum σ a).aestronglyMeasurable).1
    (((integrableOn_Ioi_iff_integrable_exp
      (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ / u ^ (1 + σ))).1
        (integrableOn_norm_partialSum σ a hσ ha)).congr
      (Filter.Eventually.of_forall (exp_mul_norm_eq σ a)))

lemma memLp_two_logPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    MemLp (logPartialSum σ a) 2 :=
  (memLp_two_iff_integrable_sq_norm
    (measurable_logPartialSum σ a).aestronglyMeasurable).2
    (((integrableOn_Ioi_iff_integrable_exp
      (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ))).1
        (integrableOn_normSq_partialSum σ a hσ ha)).congr
      (Filter.Eventually.of_forall (exp_mul_normSq_eq σ a)))

/-! ### The Fourier transform of `g`

`𝓕g(ξ) = D(s)/s` with `s = σ + 2πiξ`.  Rather than route through `mellin_eq_fourier` and then
undo a reflection, the substitution `u = eᵛ` is applied to the Fourier integral directly: the
Jacobian `eᵛ`, the `e^{-σv}` inside `g`, and the character `e^{-2πivξ}` combine into exactly
`u^{-s-1}`. -/

lemma integral_Ioi_eq_integral_exp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → F) :
    ∫ u in Set.Ioi (0 : ℝ), φ u = ∫ v : ℝ, Real.exp v • φ (Real.exp v) := by
  rw [← image_exp_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [abs_of_pos (Real.exp_pos _), Measure.restrict_univ]

theorem fourier_logPartialSum (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) (ξ : ℝ) :
    𝓕 (logPartialSum σ a) ξ
      = (∑' n : ℕ, a n / (n : ℂ) ^ ((σ : ℂ) + 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I))
        / ((σ : ℂ) + 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I) := by
  set s : ℂ := (σ : ℂ) + 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I with hsdef
  have hs : s.re = σ := by simp [hsdef]
  rw [← integral_partialSum_cpow σ a hσ ha hs, integral_Ioi_eq_integral_exp_smul, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hpos : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hne : ((Real.exp v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have hlog : Complex.log ((Real.exp v : ℝ) : ℂ) = (v : ℂ) := by
    rw [← Complex.ofReal_log hpos.le, Real.log_exp]
  simp only [logPartialSum]
  have hinner : (inner ℝ v ξ : ℝ) = v * ξ := Real.inner_apply v ξ
  rw [Complex.cpow_def_of_ne_zero hne, hlog, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_exp, Complex.ofReal_exp, hinner]
  simp only [show ∀ z w x : ℂ, Complex.exp z * (w * Complex.exp x) = w * Complex.exp (z + x)
    from fun z w x => by rw [Complex.exp_add]; ring]
  congr 1
  simp only [hsdef]
  push_cast
  ring_nf

/-! ### Parseval for Dirichlet series

Everything above assembles into Montgomery–Vaughan (5.26).  The chain is

    ∫₀^∞ ‖A(u)‖²/u^{1+2σ} du = ∫_ℝ ‖g‖² = ∫_ℝ ‖𝓕g‖² = (2π)⁻¹ ∫_ℝ ‖D(σ+it)/(σ+it)‖² dt,

with the equalities supplied by `integral_normSq_logPartialSum` (change of variables),
`RMF.integral_normSq_fourier` (Plancherel), and `fourier_logPartialSum` together with the
rescaling `t = 2πξ`.  The `(2π)⁻¹`, which the literature absorbs into `≪`, is that rescaling's
Jacobian. -/

theorem integral_normSq_partialSum_eq_line (hσ : 0 < σ) (ha : Summable (coeffWeight σ a)) :
    ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * σ)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖(∑' n : ℕ, a n / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hkey : ∀ t : ℝ,
      ‖(∑' n : ℕ, a n / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = ‖𝓕 (logPartialSum σ a) ((2 * Real.pi)⁻¹ * t)‖ ^ 2 := by
    intro t
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have harg : ((σ : ℂ) + 2 * (Real.pi : ℂ) * ((((2 * Real.pi)⁻¹ * t : ℝ)) : ℂ) * Complex.I)
        = (σ : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [fourier_logPartialSum σ a hσ ha, harg]
  rw [← integral_normSq_logPartialSum σ a,
    ← integral_normSq_fourier (integrable_logPartialSum σ a hσ ha)
      (memLp_two_logPartialSum σ a hσ ha)]
  simp_rw [hkey]
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun ξ => ‖𝓕 (logPartialSum σ a) ξ‖ ^ 2) (2 * Real.pi)⁻¹, inv_inv,
    abs_of_pos hpi, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

/-! ### The critical line

The `σ = 1/2` specialisation, in the shape `RMF/Reduction/Suppliers.lean` consumes: the weight is
`‖aₙ‖/√n` and the integrand's denominator is the natural-power `u²`. -/

lemma coeffWeight_half (n : ℕ) : coeffWeight (1 / 2) a n = ‖a n‖ / Real.sqrt n := by
  rw [coeffWeight, Real.sqrt_eq_rpow]

theorem integrableOn_normSq_partialSum_half
    (ha : Summable fun n : ℕ => ‖a n‖ / Real.sqrt n) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hσ : (0 : ℝ) < 1 / 2 := by norm_num
  have hw : coeffWeight (1 / 2) a = fun n : ℕ => ‖a n‖ / Real.sqrt n :=
    funext (coeffWeight_half a)
  have haw : Summable (coeffWeight (1 / 2) a) := by rw [hw]; exact ha
  refine (integrableOn_normSq_partialSum (1 / 2) a hσ haw).congr_fun
    (fun u hu => ?_) measurableSet_Ioi
  simp only [show (1 : ℝ) + 2 * (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

theorem integral_normSq_partialSum_eq_line_half
    (ha : Summable fun n : ℕ => ‖a n‖ / Real.sqrt n) :
    ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖(∑' n : ℕ, a n / (n : ℂ) ^ (1 / 2 + (t : ℂ) * Complex.I))
            / (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hσ : (0 : ℝ) < 1 / 2 := by norm_num
  have hw : coeffWeight (1 / 2) a = fun n : ℕ => ‖a n‖ / Real.sqrt n :=
    funext (coeffWeight_half a)
  have haw : Summable (coeffWeight (1 / 2) a) := by rw [hw]; exact ha
  have hkey := integral_normSq_partialSum_eq_line (1 / 2) a hσ haw
  have hL : ∫ u in Set.Ioi (0 : ℝ),
        ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ (1 + 2 * (1 / 2 : ℝ))
      = ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n‖ ^ 2 / u ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [show (1 : ℝ) + 2 * (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← hL, hkey]
  norm_num

end RMF
