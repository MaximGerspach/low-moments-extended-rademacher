/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.PerronKernel
import RMF.Weighted.WeightedExtended.Reduction

/-!
# The weighted extended sum: Perron's formula for the Riesz mean

The second step of the proof of Proposition 1.5 of the paper.  The Riesz mean
`A(x) = ∑_{m≤x} X(m)m^{-1/2} log(x/m)` of `RMF/Weighted/WeightedExtended/Reduction.lean` is a line
integral of the Euler product `F(s) = ∏_{p≤x}(1 + X(p)p^{-s})`: for every `ω`, `x > 0` and `σ > 0`
(`RMF.logWeightedSum_eq_integral_eulerProduct`),

`A(x) = (1/2π) ∫_ℝ F(½+σ+it) x^{σ+it}/(σ+it)² dt`.

`F` is a Dirichlet polynomial here (`RMF.randomEulerProduct_sqfree_eq_sum`), so the interchange of
sum and integral is finite, and each term is the Perron kernel `RMF.perron_kernel_sq`.  At
`σ = 1/log x`, where `x^σ = e`, this gives the pathwise bound (`RMF.norm_logWeightedSum_le`)

`|A(x)| ≤ (e/2π) ∫_ℝ (σ² + t²)⁻¹ |F(½+σ+it)| dt`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Perron's formula for a Dirichlet polynomial -/

/-- `x^z · a^{-z} = (a/x)^{-z}` for `x, a > 0`. -/
lemma cpow_mul_cpow_neg_eq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) (z : ℂ) :
    (x : ℂ) ^ z * (a : ℂ) ^ (-z) = ((a / x : ℝ) : ℂ) ^ (-z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 ha.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (div_pos ha hx).ne'),
    ← Complex.exp_add, ← Complex.ofReal_log hx.le, ← Complex.ofReal_log ha.le,
    ← Complex.ofReal_log (div_pos ha hx).le, Real.log_div ha.ne' hx.ne', Complex.ofReal_sub]
  ring_nf

/-- **Perron's formula for a Dirichlet polynomial.**  For a finite set `S` of positive integers,
`σ, x > 0`:  `(1/2π) ∫_ℝ (∑_{n∈S} cₙ n^{-(½+σ+it)}) x^{σ+it}/(σ+it)² dt
= ∑_{n∈S} cₙ n^{-1/2} max(log(x/n), 0)`, term by term from `RMF.perron_kernel_sq` at `u = n/x`. -/
theorem perron_dirichletPolynomial {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℂ) {σ x : ℝ}
    (hσ : 0 < σ) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (∑ n ∈ S, c n / (n : ℂ) ^ shiftLine σ t)
        * (x : ℂ) ^ ((σ : ℂ) + t * Complex.I) / ((σ : ℂ) + t * Complex.I) ^ 2
      = ∑ n ∈ S, c n / (Real.sqrt n : ℂ) * ((max (Real.log (x / n)) 0 : ℝ) : ℂ) := by
  have hsl : ∀ t : ℝ, shiftLine σ t = (1 / 2 : ℂ) + ((σ : ℂ) + t * Complex.I) := fun t => by
    rw [shiftLine]
    push_cast
    ring
  have hsqrt : ∀ n : ℕ, (n : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt n : ℝ) : ℂ) := fun n => by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_num
  -- each term, pointwise in `t`
  have hpt : ∀ t : ℝ, (∑ n ∈ S, c n / (n : ℂ) ^ shiftLine σ t)
        * (x : ℂ) ^ ((σ : ℂ) + t * Complex.I) / ((σ : ℂ) + t * Complex.I) ^ 2
      = ∑ n ∈ S, c n / (Real.sqrt n : ℂ) * ((((n : ℝ) / x : ℝ) : ℂ)
          ^ (-((σ : ℂ) + t * Complex.I)) / ((σ : ℂ) + t * Complex.I) ^ 2) := by
    intro t
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hS n hn).ne'
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hS n hn
    rw [← cpow_mul_cpow_neg_eq hx hn0' ((σ : ℂ) + t * Complex.I), hsl t,
      Complex.cpow_add _ _ hn0, hsqrt, Complex.cpow_neg]
    push_cast
    ring
  simp_rw [hpt]
  have hint : ∀ n ∈ S, Integrable (fun t : ℝ => c n / (Real.sqrt n : ℂ) * ((((n : ℝ) / x : ℝ) : ℂ)
      ^ (-((σ : ℂ) + t * Complex.I)) / ((σ : ℂ) + t * Complex.I) ^ 2)) := fun n hn =>
    (integrable_cpow_neg_div_sq_vertical hσ.ne'
      (div_pos (by exact_mod_cast hS n hn) hx)).const_mul _
  rw [integral_finsetSum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hS n hn
  rw [integral_const_mul, mul_left_comm, perron_kernel_sq hσ (div_pos hn0' hx), ← Real.log_inv,
    inv_div]

/-! ### The Euler product as a Dirichlet polynomial -/

omit [MeasurableSpace Ω] in
/-- **The Euler product is a Dirichlet polynomial.**  For every `ω` and `s`, and `M ≥ primorial y`,
`F_{y+1}(s) = ∑_{1≤n≤M} aₙ n^{-s}` with `aₙ = RMF.smoothCoeff`: `F_{y+1}` is the Dirichlet series
of the `aₙ` (`RMF.dirichletSeries_smoothCoeff_eq_sqfree`), and `aₙ ≠ 0` only at squarefree
`y`-smooth `n`, which divide `primorial y`
(`RMF.dvd_primorial_of_squarefree_of_mem_smoothNumbers`). -/
lemma randomEulerProduct_sqfree_eq_sum {X : ℕ → Ω → ℂ} (y : ℕ) {M : ℕ} (hM : primorial y ≤ M)
    (ω : Ω) (s : ℂ) :
    randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) s ω
      = ∑ n ∈ Finset.Icc 1 M,
          smoothCoeff (fun ω => squarefreeExtension fun p => X p ω) y ω n / (n : ℂ) ^ s := by
  rw [← dirichletSeries_smoothCoeff_eq_sqfree y ω s, dirichletSeries]
  refine tsum_eq_sum fun n hn => ?_
  by_cases hsm : n ∈ Nat.smoothNumbers (y + 1)
  · have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsm
    have hsf : ¬ Squarefree n := by
      intro hsf
      refine hn (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hn0, ?_⟩)
      exact (Nat.le_of_dvd (primorial_pos y)
        (dvd_primorial_of_squarefree_of_mem_smoothNumbers hsf hsm)).trans hM
    rw [smoothCoeff, if_pos hsm, squarefreeExtension_apply_of_not_squarefree _ hsf, zero_div]
  · rw [smoothCoeff, if_neg hsm, zero_div]

omit [MeasurableSpace Ω] in
/-- **Perron's formula for the Riesz mean.**  For every `ω`, `x > 0` and `σ > 0`,
`A(x) = (1/2π) ∫_ℝ F_{⌊x⌋+1}(½+σ+it) x^{σ+it}/(σ+it)² dt`: `F` is a Dirichlet polynomial
(`RMF.randomEulerProduct_sqfree_eq_sum`), and the terms `n > x` vanish in
`RMF.perron_dirichletPolynomial`. -/
theorem logWeightedSum_eq_integral_eulerProduct {X : ℕ → Ω → ℂ} (ω : Ω) {x σ : ℝ} (hx : 0 < x)
    (hσ : 0 < σ) :
    logWeightedSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine σ t) ω
            * (x : ℂ) ^ ((σ : ℂ) + t * Complex.I) / ((σ : ℂ) + t * Complex.I) ^ 2 := by
  set N := ⌊x⌋₊
  have hM : primorial N ≤ N + primorial N := Nat.le_add_left _ _
  simp_rw [randomEulerProduct_sqfree_eq_sum N hM ω]
  rw [perron_dirichletPolynomial (fun n hn => (Finset.mem_Icc.1 hn).1) _ hσ hx, logWeightedSum]
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 (N + primorial N) :=
    Finset.Icc_subset_Icc le_rfl (Nat.le_add_right _ _)
  rw [← Finset.sum_subset hsub fun n hn hnN => ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hnN).trans (Nat.floor_le hx.le)
    have hsm : n ∈ Nat.smoothNumbers (N + 1) := Nat.mem_smoothNumbers_of_lt hn1 (by omega)
    rw [smoothCoeff, if_pos hsm,
      max_eq_left (Real.log_nonneg ((one_le_div hn0).2 hnx))]
  · obtain ⟨hn1, -⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hNn : N + 1 ≤ n := by
      by_contra h
      exact hnN (Finset.mem_Icc.2 ⟨hn1, by omega⟩)
    have hxn : x < n := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hNn)
    rw [max_eq_right (Real.log_nonpos (div_pos hx hn0).le ((div_le_one hn0).2 hxn.le)),
      Complex.ofReal_zero, mul_zero]

/-! ### The pathwise bound -/

omit [MeasurableSpace Ω] in
/-- **The pathwise bound for the Riesz mean.**  For every `ω` and `x > 1`, with `σ = 1/log x`,
`|A(x)| ≤ (e/2π) ∫_ℝ (σ² + t²)⁻¹ |F_{⌊x⌋+1}(½+σ+it)| dt`: Perron's formula
(`RMF.logWeightedSum_eq_integral_eulerProduct`) and `|x^{σ+it}| = x^σ = e`. -/
theorem norm_logWeightedSum_le {X : ℕ → Ω → ℂ} (ω : Ω) {x : ℝ} (hx : 1 < x) :
    ‖logWeightedSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ≤ Real.exp 1 / (2 * Real.pi) * ∫ t : ℝ, ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine (Real.log x)⁻¹ t) ω‖ := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hσ : 0 < (Real.log x)⁻¹ := inv_pos.2 hlog
  have hxσ : x ^ (Real.log x)⁻¹ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx0, mul_inv_cancel₀ hlog.ne']
  have hpt : ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          (shiftLine (Real.log x)⁻¹ t) ω
        * (x : ℂ) ^ ((((Real.log x)⁻¹ : ℝ) : ℂ) + t * Complex.I)
        / ((((Real.log x)⁻¹ : ℝ) : ℂ) + t * Complex.I) ^ 2‖
      = Real.exp 1 * (((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine (Real.log x)⁻¹ t) ω‖) := by
    intro t
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, norm_pow, Complex.sq_norm,
      Complex.normSq_add_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hxσ, div_eq_mul_inv]
    ring
  have h2π : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [logWeightedSum_eq_integral_eulerProduct ω hx0 hσ, norm_mul, h2π]
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ,
          randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine (Real.log x)⁻¹ t) ω
            * (x : ℂ) ^ ((((Real.log x)⁻¹ : ℝ) : ℂ) + t * Complex.I)
            / ((((Real.log x)⁻¹ : ℝ) : ℂ) + t * Complex.I) ^ 2‖
      ≤ 1 / (2 * Real.pi) * ∫ t : ℝ, Real.exp 1 * (((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine (Real.log x)⁻¹ t) ω‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = Real.exp 1 / (2 * Real.pi) * ∫ t : ℝ, ((Real.log x)⁻¹ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              (shiftLine (Real.log x)⁻¹ t) ω‖ := by
        rw [integral_const_mul]
        ring

end RMF
