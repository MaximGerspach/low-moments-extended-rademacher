/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.PartialSumBounds

/-!
# Parseval for the tail of a Dirichlet polynomial

The tail Plancherel step of the truncation bound.  For a coefficient sequence supported on
`1 ≤ n ≤ N`, `c > 0`, and the tail `T(u) = ∑_{u < n ≤ N} aₙ`,

`∫₀^∞ ‖T(u)‖² u^{2c-1} du = (2π)⁻¹ ∫_ℝ ‖(∑_{n ≤ N} aₙ n^{c+it})/(c+it)‖² dt`,

`RMF.integral_normSq_tailSum_eq_line`.  At `aₙ = X(n)n^{-1/2}` the numerator is `F(½ − c − it)`, so
this is the identity at the **left** shift `½ − c`.

## Against the head identity

`RMF.integral_normSq_partialSum_eq_line` is the same statement for the head `A(u) = ∑_{n ≤ u} aₙ`
at `u^{-1-2σ}`, and the proof has the same three steps: the Mellin transform
(`∫₀^∞ T(u)u^{s-1}du = ∑ aₙn^s/s`, since each `aₙ1_{u<n}` integrates to `aₙn^s/s`), the change of
variables `u = eᵛ` carrying `T(u)u^c` to `g(v) = T(eᵛ)e^{cv}`, and Plancherel for `g`.

Finite support removes everything else.  The head needs a Cauchy–Schwarz splitting to make
`‖A(u)‖²u^{-1-2σ}` integrable at infinity and a dominated `tsum` interchange for its Mellin
transform; here the tail is zero beyond `N`, bounded by `∑‖aₙ‖` below it, and the Mellin transform
is a finite sum of integrals of `u^{s-1}` over `(0, n)`.
-/

open MeasureTheory

open scoped FourierTransform

namespace RMF

variable (c : ℝ) (N : ℕ) (a : ℕ → ℂ)

/-! ### The tail as a function of a real cut -/

/-- For `u ≥ 0`, the tail `∑_{⌊u⌋ < n ≤ N} aₙ` is `∑_{1 ≤ n ≤ N} aₙ·1_{u < n}`. -/
lemma sum_Ioc_floor_eq_sum_ite {u : ℝ} (hu : 0 ≤ u) :
    ∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n = ∑ n ∈ Finset.Icc 1 N, if u < n then a n else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, h2⟩, (Nat.floor_lt hu).1 h1⟩
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨(Nat.floor_lt hu).2 h3, h2⟩

/-- The tail is bounded by the total mass of the coefficients. -/
lemma norm_sum_Ioc_floor_le (u : ℝ) :
    ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
  refine le_trans (norm_sum_le _ _)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _)
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_Icc]
  omega

/-- The tail vanishes from `N` on. -/
lemma sum_Ioc_floor_eq_zero {u : ℝ} (hu : (N : ℝ) ≤ u) : ∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n = 0 := by
  have hN : N ≤ ⌊u⌋₊ := Nat.le_floor hu
  rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]

lemma measurable_sum_Ioc_floor : Measurable fun u : ℝ => ∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n :=
  (measurable_from_top (f := fun M : ℕ => ∑ n ∈ Finset.Ioc M N, a n)).comp Nat.measurable_floor

/-- **The tail against a power is integrable on `(0,∞)`**, for `r > -1` and `k ≥ 1`: it vanishes
beyond `N`, and on `(0, N]` it is at most `(∑‖aₙ‖)^k·u^r`. -/
lemma integrableOn_norm_tail_mul_rpow {r : ℝ} (hr : -1 < r) {k : ℕ} (hk : k ≠ 0) :
    IntegrableOn (fun u : ℝ => ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ^ k * u ^ r) (Set.Ioi 0) := by
  have hmeas : Measurable fun u : ℝ => ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ^ k * u ^ r :=
    ((measurable_sum_Ioc_floor N a).norm.pow_const k).mul (measurable_id.pow_const r)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (Nat.cast_nonneg N)]
  refine IntegrableOn.union ?_ ?_
  · have hdom : IntegrableOn (fun u : ℝ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ k * u ^ r)
        (Set.Ioc 0 N) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg N)).1
        ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul _)
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have hur : 0 ≤ u ^ r := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) hur)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_Ioc_floor_le N a u) k) hur
  · refine (integrableOn_zero).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only
    rw [sum_Ioc_floor_eq_zero N a (le_of_lt hu), norm_zero, zero_pow hk, zero_mul]

/-! ### The Mellin transform of the tail

`∫₀^∞ T(u)u^{s-1}du = ∑_{n ≤ N} aₙ n^s/s` for `Re s > 0`: `T(u) = ∑ₙ aₙ1_{u<n}` and
`∫₀ⁿ u^{s-1}du = n^s/s`.  A finite sum, so the interchange is `MeasureTheory.integral_finsetSum`. -/

/-- **The Mellin transform of the tail.** -/
theorem integral_tailSum_cpow {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Set.Ioi (0 : ℝ), (∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n) * (u : ℂ) ^ (s - 1)
      = (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ s) / s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hre : -1 < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  -- pointwise, the integrand is a finite sum of truncated powers
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ), (∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n) * (u : ℂ) ^ (s - 1)
      = ∑ n ∈ Finset.Icc 1 N,
          Set.indicator (Set.Iio (n : ℝ)) (fun u => a n * (u : ℂ) ^ (s - 1)) u := by
    intro u hu
    rw [sum_Ioc_floor_eq_sum_ite N a (le_of_lt hu), Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : u < n
    · rw [if_pos h, Set.indicator_of_mem (Set.mem_Iio.2 h)]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem (by simpa using h)]
  -- each piece is integrable on `(0,∞)`: it is `aₙu^{s-1}` on `(0,n)`
  have hint : ∀ n ∈ Finset.Icc 1 N, Integrable
      (fun u : ℝ => Set.indicator (Set.Iio (n : ℝ)) (fun u => a n * (u : ℂ) ^ (s - 1)) u)
      (volume.restrict (Set.Ioi 0)) := by
    intro n _
    rw [integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
    have hIoc : IntegrableOn (fun u : ℝ => a n * (u : ℂ) ^ (s - 1)) (Set.Ioc 0 n) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).1
        ((intervalIntegral.intervalIntegrable_cpow' hre).const_mul _)
    exact hIoc.mono_set Set.Ioo_subset_Ioc_self
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ hint, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  -- `∫₀ⁿ aₙ u^{s-1} du = aₙ n^s/s`
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hn0,
    integral_cpow (Or.inl hre), sub_add_cancel, Complex.ofReal_zero, Complex.zero_cpow hs0,
    sub_zero, Complex.ofReal_natCast, mul_div_assoc]

/-! ### The logarithmic change of variables -/

/-- `g(v) = T(eᵛ)·e^{cv}`, the function whose Fourier transform is the tail's Mellin transform. -/
noncomputable def logTailSum (v : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n) * (Real.exp (c * v) : ℂ)

lemma norm_logTailSum (v : ℝ) :
    ‖logTailSum c N a v‖ = Real.exp (c * v) * ‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ := by
  rw [logTailSum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

lemma measurable_logTailSum : Measurable (logTailSum c N a) := by
  unfold logTailSum
  exact ((measurable_sum_Ioc_floor N a).comp Real.measurable_exp).mul (by fun_prop)

lemma exp_mul_norm_eq_logTailSum (v : ℝ) :
    Real.exp v * (‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ ^ 1 * Real.exp v ^ (c - 1))
      = ‖logTailSum c N a v‖ := by
  rw [norm_logTailSum, exp_rpow, pow_one]
  have h : Real.exp v * Real.exp (v * (c - 1)) = Real.exp (c * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp v * (‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ * Real.exp (v * (c - 1)))
      = (Real.exp v * Real.exp (v * (c - 1))) * ‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ := by
        ring
    _ = Real.exp (c * v) * ‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ := by rw [h]

lemma exp_mul_normSq_eq_logTailSum (v : ℝ) :
    Real.exp v * (‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ ^ 2 * Real.exp v ^ (2 * c - 1))
      = ‖logTailSum c N a v‖ ^ 2 := by
  rw [norm_logTailSum, exp_rpow]
  have h : Real.exp v * Real.exp (v * (2 * c - 1)) = Real.exp (c * v) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc Real.exp v * (‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ ^ 2 * Real.exp (v * (2 * c - 1)))
      = (Real.exp v * Real.exp (v * (2 * c - 1)))
          * ‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖ ^ 2 := by ring
    _ = (Real.exp (c * v) * ‖∑ n ∈ Finset.Ioc ⌊Real.exp v⌋₊ N, a n‖) ^ 2 := by
        rw [h]
        ring

lemma integral_normSq_logTailSum :
    ∫ v : ℝ, ‖logTailSum c N a v‖ ^ 2
      = ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ^ 2 * u ^ (2 * c - 1) := by
  rw [integral_Ioi_eq_integral_exp]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun v => (exp_mul_normSq_eq_logTailSum c N a v).symm)

lemma integrable_logTailSum (hc : 0 < c) : Integrable (logTailSum c N a) :=
  (integrable_norm_iff (measurable_logTailSum c N a).aestronglyMeasurable).1
    (((integrableOn_Ioi_iff_integrable_exp
      (fun u : ℝ => ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ^ 1 * u ^ (c - 1))).1
        (integrableOn_norm_tail_mul_rpow N a (by linarith) one_ne_zero)).congr
      (Filter.Eventually.of_forall (exp_mul_norm_eq_logTailSum c N a)))

lemma memLp_two_logTailSum (hc : 0 < c) : MemLp (logTailSum c N a) 2 :=
  (memLp_two_iff_integrable_sq_norm (measurable_logTailSum c N a).aestronglyMeasurable).2
    (((integrableOn_Ioi_iff_integrable_exp
      (fun u : ℝ => ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ^ 2 * u ^ (2 * c - 1))).1
        (integrableOn_norm_tail_mul_rpow N a (by linarith) two_ne_zero)).congr
      (Filter.Eventually.of_forall (exp_mul_normSq_eq_logTailSum c N a)))

/-! ### The Fourier transform of `g`

`𝓕g(ξ) = ∑ aₙn^s/s` with `s = c − 2πiξ`: the Jacobian `eᵛ`, the `e^{cv}` inside `g` and the
character `e^{-2πivξ}` combine into exactly `u^{s-1}`, as in `RMF.fourier_logPartialSum`. -/

theorem fourier_logTailSum (hc : 0 < c) (ξ : ℝ) :
    𝓕 (logTailSum c N a) ξ
      = (∑ n ∈ Finset.Icc 1 N,
          a n * (n : ℂ) ^ ((c : ℂ) - 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I))
        / ((c : ℂ) - 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I) := by
  set s : ℂ := (c : ℂ) - 2 * (Real.pi : ℂ) * (ξ : ℂ) * Complex.I with hsdef
  have hs : 0 < s.re := by simp [hsdef, hc]
  rw [← integral_tailSum_cpow N a hs, integral_Ioi_eq_integral_exp_smul, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hpos : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hne : ((Real.exp v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have hlog : Complex.log ((Real.exp v : ℝ) : ℂ) = (v : ℂ) := by
    rw [← Complex.ofReal_log hpos.le, Real.log_exp]
  simp only [logTailSum]
  have hinner : (inner ℝ v ξ : ℝ) = v * ξ := Real.inner_apply v ξ
  rw [Complex.cpow_def_of_ne_zero hne, hlog, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_exp, Complex.ofReal_exp, hinner]
  simp only [show ∀ z w x : ℂ, Complex.exp z * (w * Complex.exp x) = w * Complex.exp (z + x)
    from fun z w x => by rw [Complex.exp_add]; ring]
  congr 1
  simp only [hsdef]
  push_cast
  ring_nf

/-! ### Parseval for the tail -/

/-- **Parseval for the tail of a Dirichlet polynomial.**  For `c > 0`,

`∫₀^∞ ‖∑_{u<n≤N} aₙ‖² u^{2c-1} du = (2π)⁻¹ ∫_ℝ ‖(∑_{n≤N} aₙ n^{c+it})/(c+it)‖² dt`.

At `aₙ = X(n)n^{-1/2}` the numerator is the Euler product at the left shift `½ − c − it`. -/
theorem integral_normSq_tailSum_eq_line (hc : 0 < c) :
    ∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ N, a n‖ ^ 2 * u ^ (2 * c - 1)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖(∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I))
            / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hkey : ∀ t : ℝ,
      ‖(∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I))
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = ‖𝓕 (logTailSum c N a) (-(2 * Real.pi)⁻¹ * t)‖ ^ 2 := by
    intro t
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have harg : ((c : ℂ) - 2 * (Real.pi : ℂ) * (((-(2 * Real.pi)⁻¹ * t : ℝ)) : ℂ) * Complex.I)
        = (c : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      field_simp
      ring
    rw [fourier_logTailSum c N a hc, harg]
  rw [← integral_normSq_logTailSum c N a,
    ← integral_normSq_fourier (integrable_logTailSum c N a hc) (memLp_two_logTailSum c N a hc)]
  simp_rw [hkey]
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun ξ => ‖𝓕 (logTailSum c N a) ξ‖ ^ 2) (-(2 * Real.pi)⁻¹), inv_neg, inv_inv, abs_neg,
    abs_of_pos hpi, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

end RMF
