/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.EulerProduct.Defs

/-!
# Moments of random Euler products

Every moment of a random Euler product factors over the primes, because the product is over
independent factors:

`E ‖F_y(s)‖ ^ r = ∏_{p < y} E ‖local factor at p‖ ^ r`

(`RMF.IsIIDPrimeValues.integral_prod`).  The situation is unusually clean: since
`‖X p · p ^ (-s)‖ ≤ p ^ (-s.re) < 1`, each local factor is bounded above *and* bounded away
from zero, so no integrability side conditions arise.

This file computes the local second moments and assembles them.  The Rademacher case needs only
that the law is centred with unit second moment (`RMF.integral_norm_one_add_mul_sq_of_centered`).
The Steinhaus case needs the geometric expansion of `(1 - X z)⁻¹` together with the orthogonality
of the characters, and is treated separately.

For a general exponent `2 q` the local integral is not computable in closed form, and one expands
it instead:

`E ‖(1 - z w)⁻¹‖ ^ (2 q) = 1 + q ^ 2 ‖w‖ ^ 2 + O_Q(‖w‖ ^ 3)`   (`|q| ≤ Q`, `‖w‖ ≤ 1/5`).

The last sections supply its ingredients; the expansion itself, at several weights at once, is
`RMF.exists_local_multi_expansion_steinhausLaw`.  The constant is uniform over the bounded range
`[-Q, Q]` of exponents, which is what lets the expansion be summed over the primes afterwards.
The coefficient `q ^ 2` (rather than `q`) is the source of the exponent in Harper's theorem, and is
invisible to Jensen's inequality applied to the second moment.

The middle section collects what every general-exponent statement needs: on the circle the
local integrand is bounded above and away from zero, so it is integrable and the local
moment is positive.

The second moment of a real part is proved in its polarized form
`E Re(z w₁) · Re(z w₂) = Re (w₁ conj w₂) / 2` (`RMF.integral_re_mul_mul_re_steinhausLaw`),
of which the diagonal `w₁ = w₂` is what the one-point expansion uses.  The off-diagonal case
is the cross term of a joint moment at two points: for `w_j = p ^ (-σ - i t_j)`,
`Re (w₁ conj w₂) = p ^ (-2 σ) cos ((t₁ - t₂) log p)`.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Local second moments -/

/-- **The local second moment for any centred law of unit second moment**: `E ‖1 + X w‖²
= 1 + ‖w‖²`, since `‖1 + u‖² = 1 + 2 Re u + ‖u‖²` leaves only `E X` and `E ‖X‖²`.  The general
form covers laws rotated by a unimodular constant, which `RMF.IsIIDPrimeValues` cannot express:
Harper's Rademacher periodisation `p ↦ f(p) p^{-iN}` turns each prime by its own angle, so its
values are independent but not identically distributed. -/
lemma integral_norm_one_add_mul_sq_of_centered {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hid : Integrable (fun z : ℂ => z) ν) (hsq : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hcent : (∫ z, z ∂ν) = 0) (hvar : (∫ z, ‖z‖ ^ 2 ∂ν) = 1) (w : ℂ) :
    (∫ z, ‖1 + z * w‖ ^ 2 ∂ν) = 1 + ‖w‖ ^ 2 := by
  have hexp : ∀ z : ℂ, ‖1 + z * w‖ ^ 2 = 1 + 2 * (z * w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    intro z
    have h2 : ‖z‖ ^ 2 * ‖w‖ ^ 2 = Complex.normSq z * Complex.normSq w := by
      rw [Complex.sq_norm, Complex.sq_norm]
    rw [Complex.sq_norm, h2, ← Complex.normSq_mul, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hre : Integrable (fun z : ℂ => (z * w).re) ν := (hid.mul_const w).re
  have hcross : (∫ z, (z * w).re ∂ν) = 0 := by
    have h : (∫ z, (z * w).re ∂ν) = (∫ z, z * w ∂ν).re := integral_re (hid.mul_const w)
    rw [h, integral_mul_const, hcent]
    simp
  have hi1 : Integrable (fun z : ℂ => 1 + 2 * (z * w).re) ν :=
    (integrable_const (1 : ℝ)).add (hre.const_mul 2)
  have hi2 : Integrable (fun z : ℂ => ‖z‖ ^ 2 * ‖w‖ ^ 2) ν := hsq.mul_const _
  calc (∫ z, ‖1 + z * w‖ ^ 2 ∂ν)
      = ∫ z, (1 + 2 * (z * w).re + ‖z‖ ^ 2 * ‖w‖ ^ 2) ∂ν := by simp_rw [hexp]
    _ = (∫ z, (1 + 2 * (z * w).re) ∂ν) + ∫ z, ‖z‖ ^ 2 * ‖w‖ ^ 2 ∂ν := integral_add hi1 hi2
    _ = ((∫ _z : ℂ, (1 : ℝ) ∂ν) + ∫ z, 2 * (z * w).re ∂ν)
          + ∫ z, ‖z‖ ^ 2 * ‖w‖ ^ 2 ∂ν := by
        rw [integral_add (integrable_const (1 : ℝ)) (hre.const_mul 2)]
    _ = 1 + ‖w‖ ^ 2 := by
        rw [integral_const_mul, hcross, integral_mul_const, hvar, integral_const]
        simp

/-- Every function is integrable against the two-point law. -/
lemma integrable_rademacherLaw {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) : Integrable f rademacherLaw := by
  rw [rademacherLaw]
  refine (integrable_smul_measure (by simp) (by simp)).2 ?_
  exact integrable_add_measure.2 ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩

/-- **The Rademacher law is centred.** -/
lemma integral_id_rademacherLaw : (∫ z, z ∂rademacherLaw) = 0 := by
  rw [rademacherLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp

/-- **The Rademacher law has unit second moment**, since `‖±1‖ = 1`. -/
lemma integral_norm_sq_rademacherLaw : (∫ z, ‖z‖ ^ 2 ∂rademacherLaw) = 1 := by
  rw [rademacherLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp
  norm_num

/-- **The local second moment for the Rademacher law**: `E ‖1 + X w‖ ^ 2 = 1 + ‖w‖ ^ 2`, the case
`ν = rademacherLaw` of `RMF.integral_norm_one_add_mul_sq_of_centered` (which also shows that the
hypotheses of that lemma are satisfiable). -/
lemma integral_norm_one_add_mul_sq_rademacherLaw (w : ℂ) :
    (∫ z, ‖1 + z * w‖ ^ 2 ∂rademacherLaw) = 1 + ‖w‖ ^ 2 :=
  integral_norm_one_add_mul_sq_of_centered (integrable_rademacherLaw _)
    (integrable_rademacherLaw _) integral_id_rademacherLaw integral_norm_sq_rademacherLaw w

/-! ### The second moment of the Rademacher Euler product -/

/-- **The second moment of the Rademacher random Euler product.**  Each prime contributes
`1 + ‖p ^ (-s)‖ ^ 2`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_sq {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y : ℕ) (s : ℂ) :
    (∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ Nat.primesBelow y, (1 + ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hpt : ∀ ω : Ω,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ 2
        = ∏ p ∈ Nat.primesBelow y, ‖1 + X p ω * (p : ℂ) ^ (-s)‖ ^ 2 := by
    intro ω
    rw [randomEulerProduct, eulerProduct_squarefreeExtension, norm_prod, ← Finset.prod_pow]
  simp_rw [hpt]
  rw [hX.integral_prod (fun _ hp => Nat.prime_of_mem_primesBelow hp)
    (fun p z => ‖1 + z * (p : ℂ) ^ (-s)‖ ^ 2) fun _ _ => by fun_prop (disch := assumption)]
  exact Finset.prod_congr rfl fun p _ => integral_norm_one_add_mul_sq_rademacherLaw _

/-- The same, with the local factors written as powers of `p`: the second moment of the
Rademacher Euler product is `∏_{p < y} (1 + p ^ (-2 σ))`, where `σ = s.re`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_sq' {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y : ℕ) (s : ℂ) :
    (∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ Nat.primesBelow y, (1 + (p : ℝ) ^ (-2 * s.re)) := by
  rw [hf.integral_norm_randomEulerProduct_sq y s]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (Nat.prime_of_mem_primesBelow hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity)]
  ring_nf

/-! ### The Steinhaus local second moment

The local factor `(1 - X w)⁻¹` is not a polynomial in `X`, so unlike the Rademacher case the
computation is a limit: expand into a geometric series, use the orthogonality of the
characters on each partial sum, and pass to the limit by dominated convergence.  The
domination is uniform, since `‖X‖ = 1` almost surely and `‖w‖ < 1`.
-/

/-- Each character is integrable against the Steinhaus law: it has modulus one a.e. -/
lemma integrable_pow_mul_conj_steinhausLaw (j k : ℕ) :
    Integrable (fun z : ℂ => z ^ j * (starRingEnd ℂ) (z ^ k)) steinhausLaw := by
  have hb : ∀ᵐ z ∂steinhausLaw, ‖z ^ j * (starRingEnd ℂ) (z ^ k)‖ ≤ 1 := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [norm_mul, norm_pow, Complex.norm_conj, norm_pow, hz]
    simp
  exact (memLp_top_of_bound (by fun_prop) 1 hb).integrable le_top

/-- The bilinear form of two partial geometric sums: the characters are orthonormal, so only
the diagonal survives, and it contributes powers of `w₁ conj w₂`. -/
lemma integral_geom_sum_mul_conj_steinhausLaw (w₁ w₂ : ℂ) (n : ℕ) :
    (∫ z, (∑ j ∈ Finset.range n, (z * w₁) ^ j)
        * (starRingEnd ℂ) (∑ k ∈ Finset.range n, (z * w₂) ^ k) ∂steinhausLaw)
      = ∑ k ∈ Finset.range n, (w₁ * (starRingEnd ℂ) w₂) ^ k := by
  have hpt : ∀ z : ℂ, (∑ j ∈ Finset.range n, (z * w₁) ^ j)
      * (starRingEnd ℂ) (∑ k ∈ Finset.range n, (z * w₂) ^ k)
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          (w₁ ^ j * (starRingEnd ℂ) (w₂ ^ k)) * (z ^ j * (starRingEnd ℂ) (z ^ k)) := by
    intro z
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_pow, map_mul, map_pow]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    ((integrable_pow_mul_conj_steinhausLaw j k).const_mul _)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => ((integrable_pow_mul_conj_steinhausLaw j k).const_mul _)]
  simp_rw [integral_const_mul, integral_pow_mul_conj_steinhausLaw, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]
  rw [if_pos hj, map_pow, ← mul_pow]

/-- A partial geometric sum on the circle is bounded by `(1 - ‖w‖)⁻¹`. -/
lemma norm_geom_sum_le_steinhausLaw {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, (z * w) ^ k‖ ≤ (1 - ‖w‖)⁻¹ := by
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  calc ‖∑ k ∈ Finset.range n, (z * w) ^ k‖
      ≤ ∑ k ∈ Finset.range n, ‖(z * w) ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range n, ‖w‖ ^ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_pow, norm_mul, hz, one_mul]
    _ ≤ (1 - ‖w‖)⁻¹ := by
        rw [← tsum_geometric_of_lt_one hw0 hw]
        exact (summable_geometric_of_lt_one hw0 hw).sum_le_tsum _ fun _ _ => by positivity

/-- **The two-point local covariance for the Steinhaus law**:

`E (1 - X w₁)⁻¹ conj ((1 - X w₂)⁻¹) = (1 - w₁ conj w₂)⁻¹`.

Only the product `w₁ conj w₂` appears — the same orthogonality that makes the one-point
second moment `(1 - ‖w‖ ^ 2)⁻¹`, which is the case `w₁ = w₂`. -/
theorem integral_inv_one_sub_mul_conj_steinhausLaw {w₁ w₂ : ℂ} (h₁ : ‖w₁‖ < 1) (h₂ : ‖w₂‖ < 1) :
    (∫ z, (1 - z * w₁)⁻¹ * (starRingEnd ℂ) ((1 - z * w₂)⁻¹) ∂steinhausLaw)
      = (1 - w₁ * (starRingEnd ℂ) w₂)⁻¹ := by
  have hprod : ‖w₁ * (starRingEnd ℂ) w₂‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖w₁‖ * ‖w₂‖ ≤ ‖w₁‖ * 1 := by
          exact mul_le_mul_of_nonneg_left h₂.le (norm_nonneg w₁)
      _ < 1 := by simpa using h₁
  have hlim : Filter.Tendsto
      (fun n => ∫ z, (∑ j ∈ Finset.range n, (z * w₁) ^ j)
        * (starRingEnd ℂ) (∑ k ∈ Finset.range n, (z * w₂) ^ k) ∂steinhausLaw) Filter.atTop
      (nhds (∫ z, (1 - z * w₁)⁻¹ * (starRingEnd ℂ) ((1 - z * w₂)⁻¹) ∂steinhausLaw)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 - ‖w₁‖)⁻¹ * (1 - ‖w₂‖)⁻¹)
      (fun n => by fun_prop) (integrable_const _) (fun n => ?_) ?_
    · filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_geom_sum_le_steinhausLaw h₁ hz n)
        (norm_geom_sum_le_steinhausLaw h₂ hz n) (norm_nonneg _) (by positivity)
    · filter_upwards [norm_eq_one_steinhausLaw] with z hz
      have hz₁ : ‖z * w₁‖ < 1 := by rw [norm_mul, hz, one_mul]; exact h₁
      have hz₂ : ‖z * w₂‖ < 1 := by rw [norm_mul, hz, one_mul]; exact h₂
      exact ((hasSum_geometric_of_norm_lt_one hz₁).tendsto_sum_nat).mul
        ((Complex.continuous_conj.tendsto _).comp
          ((hasSum_geometric_of_norm_lt_one hz₂).tendsto_sum_nat))
  rw [tendsto_nhds_unique hlim ?_]
  simp_rw [integral_geom_sum_mul_conj_steinhausLaw]
  exact (hasSum_geometric_of_norm_lt_one hprod).tendsto_sum_nat

/-- **The local second moment for the Steinhaus law**: `E ‖(1 - X w)⁻¹‖ ^ 2 = (1 - ‖w‖ ^ 2)⁻¹`
for `‖w‖ < 1`.  This is the diagonal `w₁ = w₂` of the two-point covariance, and the source of
the `∏ (1 - p ^ (-2σ))⁻¹` in the second moment of the Euler product. -/
theorem integral_norm_inv_one_sub_mul_sq_steinhausLaw {w : ℂ} (hw : ‖w‖ < 1) :
    (∫ z, ‖(1 - z * w)⁻¹‖ ^ 2 ∂steinhausLaw) = (1 - ‖w‖ ^ 2)⁻¹ := by
  have hcast : ((∫ z, ‖(1 - z * w)⁻¹‖ ^ 2 ∂steinhausLaw : ℝ) : ℂ) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
    rw [← integral_complex_ofReal]
    have hpt : ∀ z : ℂ, ((‖(1 - z * w)⁻¹‖ ^ 2 : ℝ) : ℂ)
        = (1 - z * w)⁻¹ * (starRingEnd ℂ) ((1 - z * w)⁻¹) := fun z => by
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp_rw [hpt]
    rw [integral_inv_one_sub_mul_conj_steinhausLaw hw hw, Complex.mul_conj', Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_one]
  exact_mod_cast hcast

/-! ### The second moment of the Steinhaus Euler product -/

/-- **The second moment of the Steinhaus random Euler product.**  Each prime contributes
`(1 - ‖p ^ (-s)‖ ^ 2)⁻¹`. -/
theorem IsSteinhausRMF.integral_norm_randomEulerProduct_sq {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ Nat.primesBelow y, (1 - ‖(p : ℂ) ^ (-s)‖ ^ 2)⁻¹ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hae : ∀ᵐ ω ∂μ,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y s ω‖ ^ 2
        = ∏ p ∈ Nat.primesBelow y, ‖(1 - X p ω * (p : ℂ) ^ (-s))⁻¹‖ ^ 2 := by
    filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw y] with ω hω
    rw [randomEulerProduct_compMult_eq hs hω, norm_prod, ← Finset.prod_pow]
  rw [integral_congr_ae hae,
    hX.integral_prod (fun _ hp => Nat.prime_of_mem_primesBelow hp)
      (fun p z => ‖(1 - z * (p : ℂ) ^ (-s))⁻¹‖ ^ 2) fun _ _ => by fun_prop (disch := assumption)]
  exact Finset.prod_congr rfl fun p hp =>
    integral_norm_inv_one_sub_mul_sq_steinhausLaw
      (norm_prime_cpow_neg_lt_one (Nat.prime_of_mem_primesBelow hp) hs)

/-- The same, as a product of powers of `p`: the second moment of the Steinhaus Euler
product is `∏_{p < y} (1 - p ^ (-2σ))⁻¹`, where `σ = s.re`.  At `σ = 1/2` this is
`∏_{p < y} (1 - 1/p)⁻¹`, which by Mertens' third theorem grows like `e ^ γ log y`. -/
theorem IsSteinhausRMF.integral_norm_randomEulerProduct_sq' {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsSteinhausRMF f μ) (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ ω, ‖randomEulerProduct f y s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ Nat.primesBelow y, (1 - (p : ℝ) ^ (-2 * s.re))⁻¹ := by
  rw [hf.integral_norm_randomEulerProduct_sq y hs]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : 0 < p := (Nat.prime_of_mem_primesBelow hp).pos
  rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity)]
  ring_nf

/-! ### Moments of every order

The second moment is the case `r = 2` of an exact factorisation valid for every exponent.
This is the starting point for the low moments that Harper's theorem concerns: the local
factors can be expanded and the resulting prime sums estimated.  Jensen's inequality applied
to the second moment is *not* the right route — it gives `(∏ (1 - p ^ (-2σ))⁻¹) ^ q`, whereas
the truth involves `q ^ 2` in the exponent, not `q`.
-/

/-- The local integrand `z ↦ ‖(1 - z w)⁻¹‖ ^ r` is a.e. strongly measurable, for any law carried by
the closed unit disc, `‖w‖ < 1` and any `r`.  Off a null set it agrees with a continuous function
obtained by flooring the modulus away from zero; for `r < 0`, `Continuous.rpow_const` cannot be
applied directly, because the base `‖(1 - z w)⁻¹‖` vanishes at the pole `z w = 1`. -/
lemma aestronglyMeasurable_localIntegrand_of_norm_le {ν : Measure ℂ}
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) {w : ℂ} (hw : ‖w‖ < 1) (r : ℝ) :
    AEStronglyMeasurable (fun z : ℂ => ‖(1 - z * w)⁻¹‖ ^ r) ν := by
  have hmax : ∀ z : ℂ, (0 : ℝ) < max ‖1 - z * w‖ (1 - ‖w‖) :=
    fun z => lt_max_of_lt_right (by linarith)
  have hc : Continuous fun z : ℂ => (max ‖1 - z * w‖ (1 - ‖w‖))⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun z => (hmax z).ne'
  have hcr : Continuous fun z : ℂ => ((max ‖1 - z * w‖ (1 - ‖w‖))⁻¹) ^ r :=
    hc.rpow_const fun z => Or.inl (inv_ne_zero (hmax z).ne')
  refine hcr.aestronglyMeasurable.congr ?_
  filter_upwards [hν] with z hz
  have hzw : ‖z * w‖ ≤ ‖w‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg z]
  have h1 : 1 - ‖w‖ ≤ ‖1 - z * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (z * w)
    rw [norm_one] at this
    linarith
  rw [max_eq_left h1, norm_inv]

/-- **Every moment of a squarefree-supported random Euler product factors over the primes**, for
`0 ≤ r` and with no hypothesis on `s` or on the law: the local factors are polynomials.  Without
such hypotheses `1 + z w` can vanish, so a negative exponent needs
`RMF.integral_norm_randomEulerProduct_rpow_sqfree_of_norm_le`. -/
theorem integral_norm_randomEulerProduct_rpow_sqfree {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (y : ℕ) (s : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ r ∂μ)
      = ∏ p ∈ Nat.primesBelow y, ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r ∂ν := by
  have hpt : ∀ ω : Ω,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ r
        = ∏ p ∈ Nat.primesBelow y, ‖1 + X p ω * (p : ℂ) ^ (-s)‖ ^ r := by
    intro ω
    rw [randomEulerProduct, eulerProduct_squarefreeExtension, norm_prod,
      Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _) r]
  simp_rw [hpt]
  rw [hX.integral_prod (fun _ hp => Nat.prime_of_mem_primesBelow hp)
    (fun p z => ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r) fun _ _ => by fun_prop (disch := assumption)]

/-- The companion of `RMF.aestronglyMeasurable_localIntegrand_of_norm_le` for the *polynomial*
local factor.  For a law in the closed unit disc and `‖w‖ < 1`, `1 + z w` is bounded away from
zero by `1 - ‖w‖`, so flooring its modulus there changes nothing and supplies the continuity
`fun_prop` cannot produce at a negative exponent. -/
lemma aestronglyMeasurable_localIntegrandAdd_of_norm_le {ν : Measure ℂ}
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) {w : ℂ} (hw : ‖w‖ < 1) (r : ℝ) :
    AEStronglyMeasurable (fun z : ℂ => ‖1 + z * w‖ ^ r) ν := by
  have hmax : ∀ z : ℂ, (0 : ℝ) < max ‖1 + z * w‖ (1 - ‖w‖) :=
    fun z => lt_max_of_lt_right (by linarith)
  have hc : Continuous fun z : ℂ => max ‖1 + z * w‖ (1 - ‖w‖) := by fun_prop
  have hcr : Continuous fun z : ℂ => (max ‖1 + z * w‖ (1 - ‖w‖)) ^ r :=
    hc.rpow_const fun z => Or.inl (hmax z).ne'
  refine hcr.aestronglyMeasurable.congr ?_
  filter_upwards [hν] with z hz
  have hzw : ‖z * w‖ ≤ ‖w‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg z]
  have h1 : 1 - ‖w‖ ≤ ‖1 + z * w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(z * w))
    rw [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  rw [max_eq_left h1]

/-- **The squarefree factorisation at a signed exponent.**  For a law carried by `‖z‖ ≤ 1` and
`0 < Re s`, `‖1 + z w‖ ≥ 1 - ‖w‖ > 0`, so the exponent `r` may have either sign.  This is what the
Rademacher negative moments need. -/
theorem integral_norm_randomEulerProduct_rpow_sqfree_of_norm_le {X : ℕ → Ω → ℂ} {ν : Measure ℂ}
    {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ) (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) (r : ℝ) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ r ∂μ)
      = ∏ p ∈ Nat.primesBelow y, ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r ∂ν := by
  have hpt : ∀ ω : Ω,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y s ω‖ ^ r
        = ∏ p ∈ Nat.primesBelow y, ‖1 + X p ω * (p : ℂ) ^ (-s)‖ ^ r := by
    intro ω
    rw [randomEulerProduct, eulerProduct_squarefreeExtension, norm_prod,
      Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _) r]
  simp_rw [hpt]
  rw [hX.integral_prod (fun _ hp => Nat.prime_of_mem_primesBelow hp)
    (fun p z => ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r) fun p hp => ?_]
  have hp2 := Nat.prime_of_mem_primesBelow hp
  have hlt : ‖((p : ℂ)) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp2.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp2.one_lt) (by linarith)
  exact aestronglyMeasurable_localIntegrandAdd_of_norm_le hν hlt r

/-- The Rademacher case at a **signed** exponent, for `0 < Re s`: the instance of
`RMF.integral_norm_randomEulerProduct_rpow_sqfree_of_norm_le`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProduct_rpow_of_pos
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y : ℕ) {s : ℂ}
    (hs : 0 < s.re) (r : ℝ) :
    (∫ ω, ‖randomEulerProduct f y s ω‖ ^ r ∂μ)
      = ∏ p ∈ Nat.primesBelow y, ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r ∂rademacherLaw := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  exact integral_norm_randomEulerProduct_rpow_sqfree_of_norm_le hX norm_le_one_rademacherLaw
    y hs r

/-! ### The local moment as a function of `‖w‖`

Throughout, `w` plays the role of `p ^ (-s)` and the *local integrand* is
`z ↦ ‖(1 - z w)⁻¹‖ ^ r`, whose integral against the Steinhaus law is the *local moment*.
On the circle `‖1 - z w‖` lies between `1 - ‖w‖` and `1 + ‖w‖`, so for `‖w‖ < 1` the
integrand is bounded above and away from zero, and the local moment is positive.
-/

/-- An a.e.-bounded function is integrable for the Steinhaus law, a probability measure. -/
lemma integrable_of_norm_le_steinhausLaw {E : Type*} [NormedAddCommGroup E] {g : ℂ → E}
    (hg : AEStronglyMeasurable g steinhausLaw) (C : ℝ)
    (h : ∀ᵐ z ∂steinhausLaw, ‖g z‖ ≤ C) : Integrable g steinhausLaw :=
  (memLp_top_of_bound hg C h).integrable le_top

/-- On the circle, `‖1 - z w‖` is trapped between `1 - ‖w‖` and `1 + ‖w‖`. -/
lemma ae_norm_one_sub_mul_bounds (w : ℂ) :
    ∀ᵐ z ∂steinhausLaw, 1 - ‖w‖ ≤ ‖1 - z * w‖ ∧ ‖1 - z * w‖ ≤ 1 + ‖w‖ := by
  filter_upwards [norm_eq_one_steinhausLaw] with z hz
  have hzw : ‖z * w‖ = ‖w‖ := by rw [norm_mul, hz, one_mul]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (z * w)
    rwa [norm_one, hzw] at this
  · have := norm_sub_le (1 : ℂ) (z * w)
    rwa [norm_one, hzw] at this

/-- The Steinhaus case: the law is supported on the unit circle. -/
lemma aestronglyMeasurable_localIntegrand {w : ℂ} (hw : ‖w‖ < 1) (r : ℝ) :
    AEStronglyMeasurable (fun z : ℂ => ‖(1 - z * w)⁻¹‖ ^ r) steinhausLaw :=
  aestronglyMeasurable_localIntegrand_of_norm_le
    (by filter_upwards [norm_eq_one_steinhausLaw] with z hz using hz.le) hw r

/-! ### The local expansion

For a general exponent the local integral is not computable, and one expands instead.  Writing
`W z = 2 Re (z w) - ‖w‖ ^ 2`, on the unit circle `‖1 - z w‖ ^ 2 = 1 - W z`, so the local moment
is `E (1 - W) ^ (-q)`.  Since `E W = -‖w‖ ^ 2` and `E W ^ 2 = 2‖w‖ ^ 2 + ‖w‖ ^ 4`, a second-order
expansion of `(1 - ·) ^ (-q)` gives

`E ‖(1 - z w)⁻¹‖ ^ (2q) = 1 + q ^ 2 ‖w‖ ^ 2 + O(‖w‖ ^ 3)`,

with the implied constant depending only on a bound `Q` for `|q|`.  The `q ^ 2`, not `q`, is
what makes Harper's exponent `q ^ 2`, and is why Jensen applied to the second moment is not
sharp enough.
-/

/-- The real part of `z w` is integrable against the Steinhaus law. -/
lemma integrable_re_mul_steinhausLaw (w : ℂ) :
    Integrable (fun z : ℂ => (z * w).re) steinhausLaw :=
  integrable_of_norm_le_steinhausLaw (by fun_prop) ‖w‖ <| by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])

lemma integrable_re_mul_sq_steinhausLaw (w : ℂ) :
    Integrable (fun z : ℂ => ((z * w).re) ^ 2) steinhausLaw :=
  integrable_of_norm_le_steinhausLaw (by fun_prop) (‖w‖ ^ 2) <| by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    have h := (Complex.abs_re_le_norm (z * w)).trans_eq (by rw [norm_mul, hz, one_mul])
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- The real part is centered under the Steinhaus law. -/
lemma integral_re_mul_steinhausLaw (w : ℂ) : (∫ z, (z * w).re ∂steinhausLaw) = 0 := by
  have hint : Integrable (fun z : ℂ => z * w) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (by fun_prop) ‖w‖ <| by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [norm_mul, hz, one_mul]
  simp only [← RCLike.re_to_complex]
  rw [integral_re hint, integral_mul_const, integral_steinhausLaw, zero_mul]
  simp

/-- `∫ z ^ 2 = 0`: the square of the identity character is orthogonal to the trivial one. -/
@[simp]
lemma integral_sq_steinhausLaw : (∫ z, z ^ 2 ∂steinhausLaw) = 0 := by
  simpa using integral_pow_mul_conj_steinhausLaw 2 0

/-- The polarization identity `Re a · Re b = (Re (a b) + Re (a conj b)) / 2`. -/
lemma re_mul_re (a b : ℂ) :
    a.re * b.re = ((a * b).re + (a * (starRingEnd ℂ) b).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **The polarisation identity behind every multi-weight local expansion**:
`∑_{a,b} q_a q_b Re(w_a · conj w_b) = ‖∑_a q_a w_a‖²`, for real `q` of either sign.  So the
second-order coefficient of a joint local moment is `‖∑_a q_a w_a‖²`: with one weight it is
`q²‖w‖²`; with `q ≡ 1` and `w_a = p^{-σ-it_a}` it is `(2 + 2cos((t₁-t₂) log p)) p^{-2σ}`, Harper's
(5.1) as `RMF.exists_abs_log_localTwoPointMoment_sub_le` states it. -/
lemma sum_sum_re_mul_conj_eq_norm_sq {ι : Type*} (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    (∑ a ∈ A, ∑ b ∈ A, q a * q b * (w a * (starRingEnd ℂ) (w b)).re)
      = ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 := by
  have h1 : ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2
      = ((∑ a ∈ A, (q a : ℂ) * w a) * (starRingEnd ℂ) (∑ a ∈ A, (q a : ℂ) * w a)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 : (q a : ℂ) * w a * ((starRingEnd ℂ) ((q b : ℂ) * w b))
      = ((q a * q b : ℝ) : ℂ) * (w a * (starRingEnd ℂ) (w b)) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h2, Complex.re_ofReal_mul]

/-- **The polarized second moment for the Steinhaus law**:
`E Re(z w₁) · Re(z w₂) = Re (w₁ conj w₂) / 2`; only the relative phase of `w₁` and `w₂` survives.
With `w₁ = w₂` this is `RMF.integral_re_mul_sq_steinhausLaw`; with `w_j = p ^ (-σ - i t_j)`,
`Re (w₁ conj w₂) = p ^ (-2 σ) cos ((t₁ - t₂) log p)`, the cross term of a two-point estimate. -/
lemma integral_re_mul_mul_re_steinhausLaw (w₁ w₂ : ℂ) :
    (∫ z, (z * w₁).re * (z * w₂).re ∂steinhausLaw) = (w₁ * (starRingEnd ℂ) w₂).re / 2 := by
  have hsq : Integrable (fun z : ℂ => (z ^ 2 * (w₁ * w₂)).re) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (by fun_prop) (‖w₁ * w₂‖) <| by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans_eq ?_
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
  have hchar : (∫ z, (z ^ 2 * (w₁ * w₂)).re ∂steinhausLaw) = 0 := by
    have hint : Integrable (fun z : ℂ => z ^ 2 * (w₁ * w₂)) steinhausLaw :=
      integrable_of_norm_le_steinhausLaw (by fun_prop) (‖w₁ * w₂‖) <| by
        filter_upwards [norm_eq_one_steinhausLaw] with z hz
        rw [norm_mul, norm_pow, hz, one_pow, one_mul]
    simp only [← RCLike.re_to_complex]
    rw [integral_re hint, integral_mul_const, integral_sq_steinhausLaw, zero_mul]
    simp
  have key : (fun z : ℂ => (z * w₁).re * (z * w₂).re) =ᵐ[steinhausLaw]
      fun z => ((z ^ 2 * (w₁ * w₂)).re + (w₁ * (starRingEnd ℂ) w₂).re) / 2 := by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    rw [re_mul_re]
    congr 2
    · congr 1; ring
    · congr 1
      rw [map_mul, show z * w₁ * ((starRingEnd ℂ) z * (starRingEnd ℂ) w₂)
        = z * (starRingEnd ℂ) z * (w₁ * (starRingEnd ℂ) w₂) by ring, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hz]
      norm_num
  rw [integral_congr_ae key, integral_div, integral_add hsq (integrable_const _), hchar,
    integral_const]
  simp

/-- The second moment of the real part under the Steinhaus law: half the second moment of
the modulus, the two coordinates carrying equal shares. -/
lemma integral_re_mul_sq_steinhausLaw (w : ℂ) :
    (∫ z, ((z * w).re) ^ 2 ∂steinhausLaw) = ‖w‖ ^ 2 / 2 := by
  simp_rw [pow_two ((_ : ℂ) * w).re]
  rw [integral_re_mul_mul_re_steinhausLaw w w, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-! ### Characters of higher order, and the truncated summand

The Lindeberg comparison of the block increment with a Gaussian runs not on `RMF.localLog` itself
but on its degree-two Taylor truncation, and needs four things of it: that it is centred,
deterministically bounded, has an explicit variance, and has a finite third moment.

All four come from one generalisation of `RMF.integral_re_mul_mul_re_steinhausLaw`: the polarised
second moment of `Re(z^j w₁)` against `Re(z^k w₂)`.  Distinct characters are orthogonal, so the
value is `Re(w₁ conj w₂)/2` on the diagonal and **zero off it** — and it is the off-diagonal case
`j = 1`, `k = 2` that makes the truncation's cross term vanish. -/

/-- `∫ z ^ j = 0` for `j ≠ 0`: a nontrivial character is orthogonal to the trivial one. -/
lemma integral_pow_steinhausLaw {j : ℕ} (hj : j ≠ 0) : (∫ z, z ^ j ∂steinhausLaw) = 0 := by
  simpa [hj] using integral_pow_mul_conj_steinhausLaw j 0

lemma integrable_re_pow_mul_steinhausLaw (j : ℕ) (w : ℂ) :
    Integrable (fun z : ℂ => (z ^ j * w).re) steinhausLaw :=
  integrable_of_norm_le_steinhausLaw (by fun_prop) ‖w‖ <| by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, norm_pow, hz, one_pow, one_mul])

/-- Every nontrivial character is centred, `RMF.integral_re_mul_steinhausLaw` being `j = 1`. -/
lemma integral_re_pow_mul_steinhausLaw {j : ℕ} (hj : j ≠ 0) (w : ℂ) :
    (∫ z, (z ^ j * w).re ∂steinhausLaw) = 0 := by
  have hint : Integrable (fun z : ℂ => z ^ j * w) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (by fun_prop) ‖w‖ <| by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
  simp only [← RCLike.re_to_complex]
  rw [integral_re hint, integral_mul_const, integral_pow_steinhausLaw hj, zero_mul]
  simp

lemma integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw (j k : ℕ) (w₁ w₂ : ℂ) :
    Integrable (fun z : ℂ => (z ^ j * w₁).re * (z ^ k * w₂).re) steinhausLaw :=
  integrable_of_norm_le_steinhausLaw (by fun_prop) (‖w₁‖ * ‖w₂‖) <| by
    filter_upwards [norm_eq_one_steinhausLaw] with z hz
    have h₁ : |(z ^ j * w₁).re| ≤ ‖w₁‖ :=
      (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, norm_pow, hz, one_pow, one_mul])
    have h₂ : |(z ^ k * w₂).re| ≤ ‖w₂‖ :=
      (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, norm_pow, hz, one_pow, one_mul])
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h₁ h₂ (abs_nonneg _) (norm_nonneg _)

/-- **The polarised second moment at two characters.**  `E Re(z^j w₁) · Re(z^k w₂)` equals
`Re(w₁ conj w₂)/2` when `j = k` and is **zero otherwise**.

`RMF.integral_re_mul_mul_re_steinhausLaw` is the case `j = k = 1`.  The hypothesis `j + k ≠ 0`
only rules out the trivial character, where both factors are deterministic and the identity
fails. -/
lemma integral_re_pow_mul_mul_re_pow_mul_steinhausLaw {j k : ℕ} (hjk : j + k ≠ 0) (w₁ w₂ : ℂ) :
    (∫ z, (z ^ j * w₁).re * (z ^ k * w₂).re ∂steinhausLaw)
      = if j = k then (w₁ * (starRingEnd ℂ) w₂).re / 2 else 0 := by
  have hprod : Integrable (fun z : ℂ => (z ^ (j + k) * (w₁ * w₂)).re) steinhausLaw :=
    integrable_re_pow_mul_steinhausLaw _ _
  have hcross : Integrable (fun z : ℂ =>
      (z ^ j * (starRingEnd ℂ) (z ^ k) * (w₁ * (starRingEnd ℂ) w₂)).re) steinhausLaw :=
    integrable_of_norm_le_steinhausLaw (by fun_prop) ‖w₁ * (starRingEnd ℂ) w₂‖ <| by
      filter_upwards [norm_eq_one_steinhausLaw] with z hz
      refine (Complex.abs_re_le_norm _).trans_eq ?_
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, norm_pow, hz]
      simp
  have h2 : (∫ z, (z ^ j * (starRingEnd ℂ) (z ^ k) * (w₁ * (starRingEnd ℂ) w₂)).re ∂steinhausLaw)
      = if j = k then (w₁ * (starRingEnd ℂ) w₂).re else 0 := by
    have hint : Integrable (fun z : ℂ =>
        z ^ j * (starRingEnd ℂ) (z ^ k) * (w₁ * (starRingEnd ℂ) w₂)) steinhausLaw :=
      (integrable_pow_mul_conj_steinhausLaw j k).mul_const _
    simp only [← RCLike.re_to_complex]
    rw [integral_re hint, integral_mul_const, integral_pow_mul_conj_steinhausLaw]
    split_ifs with h <;> simp
  have key : ∀ z : ℂ, (z ^ j * w₁).re * (z ^ k * w₂).re
      = ((z ^ (j + k) * (w₁ * w₂)).re
        + (z ^ j * (starRingEnd ℂ) (z ^ k) * (w₁ * (starRingEnd ℂ) w₂)).re) / 2 := by
    intro z
    rw [re_mul_re]
    have e₁ : z ^ j * w₁ * (z ^ k * w₂) = z ^ (j + k) * (w₁ * w₂) := by rw [pow_add]; ring
    have e₂ : z ^ j * w₁ * (starRingEnd ℂ) (z ^ k * w₂)
        = z ^ j * (starRingEnd ℂ) (z ^ k) * (w₁ * (starRingEnd ℂ) w₂) := by rw [map_mul]; ring
    rw [e₁, e₂]
  simp_rw [key]
  rw [integral_div, integral_add hprod hcross, integral_re_pow_mul_steinhausLaw hjk, h2]
  split_ifs with h <;> simp

/-- **The per-prime summand of the truncated walk**: `Re(z w) + Re(z² w²)/2`, which at `z = f(p)`,
`w = p^{-s}` is Harper's `f(p)p^{-s} + f(p)²p^{-2s}/2` with its real part taken.  It is the
degree-two Taylor truncation of `RMF.localLog`: expanding `-log‖1-zw‖`, the `-‖w‖²/2` of the linear
term cancels the `+‖w‖²/2` of the quadratic one, which is why the truncation is centred exactly
(`RMF.integral_localTaylorTwo`). -/
noncomputable def localTaylorTwo (w z : ℂ) : ℝ := (z * w).re + (z ^ 2 * w ^ 2).re / 2

lemma measurable_localTaylorTwo (w : ℂ) : Measurable (localTaylorTwo w) := by
  unfold localTaylorTwo
  fun_prop

/-- **`|X_p| ≤ 2‖w‖` deterministically**, not merely in mean.  This is what lets the third moment
be read off without a second integral, and why the Gaussian comparison needs no tail hypothesis. -/
lemma abs_localTaylorTwo_le {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) :
    |localTaylorTwo w z| ≤ 2 * ‖w‖ := by
  have h₁ : |(z * w).re| ≤ ‖w‖ :=
    (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])
  have h₂ : |(z ^ 2 * w ^ 2).re| ≤ ‖w‖ ^ 2 :=
    (Complex.abs_re_le_norm _).trans_eq (by
      rw [norm_mul, norm_pow, norm_pow, hz, one_pow, one_mul])
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hsq : ‖w‖ ^ 2 ≤ ‖w‖ := by nlinarith
  have hsplit : |localTaylorTwo w z| ≤ |(z * w).re| + |(z ^ 2 * w ^ 2).re| / 2 := by
    unfold localTaylorTwo
    calc |(z * w).re + (z ^ 2 * w ^ 2).re / 2|
        ≤ |(z * w).re| + |(z ^ 2 * w ^ 2).re / 2| := abs_add_le _ _
      _ = |(z * w).re| + |(z ^ 2 * w ^ 2).re| / 2 := by rw [abs_div]; norm_num
  linarith

lemma integrable_localTaylorTwo (w : ℂ) : Integrable (localTaylorTwo w) steinhausLaw := by
  have h₁ : Integrable (fun z : ℂ => (z * w).re) steinhausLaw := integrable_re_mul_steinhausLaw w
  have h₂ : Integrable (fun z : ℂ => (z ^ 2 * w ^ 2).re / 2) steinhausLaw :=
    (integrable_re_pow_mul_steinhausLaw 2 (w ^ 2)).div_const 2
  unfold localTaylorTwo
  exact h₁.add h₂

/-- **The truncation is centred exactly**, with no error term: both characters are nontrivial. -/
@[simp]
lemma integral_localTaylorTwo (w : ℂ) : (∫ z, localTaylorTwo w z ∂steinhausLaw) = 0 := by
  have h₁ : Integrable (fun z : ℂ => (z * w).re) steinhausLaw := integrable_re_mul_steinhausLaw w
  have h₂ : Integrable (fun z : ℂ => (z ^ 2 * w ^ 2).re / 2) steinhausLaw :=
    (integrable_re_pow_mul_steinhausLaw 2 (w ^ 2)).div_const 2
  unfold localTaylorTwo
  rw [integral_add h₁ h₂, integral_re_mul_steinhausLaw, integral_div,
    integral_re_pow_mul_steinhausLaw two_ne_zero]
  norm_num

/-- The product of two truncations, expanded into the four products of real parts of the
characters `z` and `z²`. -/
lemma localTaylorTwo_mul_expand (w₁ w₂ z : ℂ) :
    localTaylorTwo w₁ z * localTaylorTwo w₂ z
      = (z ^ 1 * w₁).re * (z ^ 1 * w₂).re + (z ^ 1 * w₁).re * (z ^ 2 * w₂ ^ 2).re / 2
        + (z ^ 2 * w₁ ^ 2).re * (z ^ 1 * w₂).re / 2
        + (z ^ 2 * w₁ ^ 2).re * (z ^ 2 * w₂ ^ 2).re / 4 := by
  unfold localTaylorTwo
  rw [pow_one]
  ring

/-- The product of two truncations is integrable: on the circle it is a finite combination of
character products, each bounded. -/
lemma integrable_localTaylorTwo_mul (w₁ w₂ : ℂ) :
    Integrable (fun z : ℂ => localTaylorTwo w₁ z * localTaylorTwo w₂ z) steinhausLaw := by
  have i11 := integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 1 1 w₁ w₂
  have i12 := (integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 1 2 w₁ (w₂ ^ 2)).div_const 2
  have i21 := (integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 2 1 (w₁ ^ 2) w₂).div_const 2
  have i22 := (integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 2 2 (w₁ ^ 2) (w₂ ^ 2)).div_const 4
  have j1 : Integrable (fun z : ℂ => (z ^ 1 * w₁).re * (z ^ 1 * w₂).re
      + (z ^ 1 * w₁).re * (z ^ 2 * w₂ ^ 2).re / 2) steinhausLaw := i11.add i12
  have j2 : Integrable (fun z : ℂ => (z ^ 1 * w₁).re * (z ^ 1 * w₂).re
      + (z ^ 1 * w₁).re * (z ^ 2 * w₂ ^ 2).re / 2
      + (z ^ 2 * w₁ ^ 2).re * (z ^ 1 * w₂).re / 2) steinhausLaw := j1.add i21
  exact (j2.add i22).congr
    (Filter.Eventually.of_forall fun z => (localTaylorTwo_mul_expand w₁ w₂ z).symm)

/-- **The polarised second moment of the truncation**:
`E localTaylorTwo(w₁)·localTaylorTwo(w₂) = Re(w₁ conj w₂)/2 + Re(w₁² conj(w₂²))/8`.  Both cross
terms vanish because `z` and `z²` are distinct characters
(`RMF.integral_re_pow_mul_mul_re_pow_mul_steinhausLaw`).  The second summand is `O(‖w‖⁴)` and goes
into the cubic error. -/
lemma integral_localTaylorTwo_mul (w₁ w₂ : ℂ) :
    (∫ z, localTaylorTwo w₁ z * localTaylorTwo w₂ z ∂steinhausLaw)
      = (w₁ * (starRingEnd ℂ) w₂).re / 2
        + (w₁ ^ 2 * (starRingEnd ℂ) (w₂ ^ 2)).re / 8 := by
  have hexp := localTaylorTwo_mul_expand w₁ w₂
  have i11 := integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 1 1 w₁ w₂
  have i12 := (integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 1 2 w₁ (w₂ ^ 2)).div_const 2
  have i21 := (integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 2 1 (w₁ ^ 2) w₂).div_const 2
  have i22 := (integrable_re_pow_mul_mul_re_pow_mul_steinhausLaw 2 2 (w₁ ^ 2) (w₂ ^ 2)).div_const 4
  have e11 : (∫ z, (z ^ 1 * w₁).re * (z ^ 1 * w₂).re ∂steinhausLaw)
      = (w₁ * (starRingEnd ℂ) w₂).re / 2 := by
    rw [integral_re_pow_mul_mul_re_pow_mul_steinhausLaw (by norm_num) w₁ w₂, if_pos rfl]
  have e12 : (∫ z, (z ^ 1 * w₁).re * (z ^ 2 * w₂ ^ 2).re ∂steinhausLaw) = 0 := by
    rw [integral_re_pow_mul_mul_re_pow_mul_steinhausLaw (by norm_num) w₁ (w₂ ^ 2),
      if_neg (by norm_num)]
  have e21 : (∫ z, (z ^ 2 * w₁ ^ 2).re * (z ^ 1 * w₂).re ∂steinhausLaw) = 0 := by
    rw [integral_re_pow_mul_mul_re_pow_mul_steinhausLaw (by norm_num) (w₁ ^ 2) w₂,
      if_neg (by norm_num)]
  have e22 : (∫ z, (z ^ 2 * w₁ ^ 2).re * (z ^ 2 * w₂ ^ 2).re ∂steinhausLaw)
      = (w₁ ^ 2 * (starRingEnd ℂ) (w₂ ^ 2)).re / 2 := by
    rw [integral_re_pow_mul_mul_re_pow_mul_steinhausLaw (by norm_num) (w₁ ^ 2) (w₂ ^ 2),
      if_pos rfl]
  -- `Integrable.add` produces a `Pi.add` lambda that `integral_add` will not match, so the
  -- partial sums are ascribed explicitly.
  have j1 : Integrable (fun z : ℂ => (z ^ 1 * w₁).re * (z ^ 1 * w₂).re
      + (z ^ 1 * w₁).re * (z ^ 2 * w₂ ^ 2).re / 2) steinhausLaw := i11.add i12
  have j2 : Integrable (fun z : ℂ => (z ^ 1 * w₁).re * (z ^ 1 * w₂).re
      + (z ^ 1 * w₁).re * (z ^ 2 * w₂ ^ 2).re / 2
      + (z ^ 2 * w₁ ^ 2).re * (z ^ 1 * w₂).re / 2) steinhausLaw := j1.add i21
  simp_rw [hexp]
  rw [integral_add j2 i22, integral_add j1 i21, integral_add i11 i12, e11,
    integral_div, e12, integral_div, e21, integral_div, e22]
  ring

/-- **The second moment of a signed combination of truncations**:
`E (∑_a q_a localTaylorTwo(w_a))² = ‖∑_a q_a w_a‖²/2 + ‖∑_a q_a w_a²‖²/8`, by
`RMF.sum_sum_re_mul_conj_eq_norm_sq` at the weights and at their squares.  The first term, doubled,
is the second-order coefficient of the joint local moment.  Real `q` of either sign are allowed,
as Hamdan's Lemma B.1 needs (`A` three points, `q = (λ₁, λ₂, -λ₂)`). -/
lemma integral_sum_smul_localTaylorTwo_sq {ι : Type*} (A : Finset ι) (q : ι → ℝ) (w : ι → ℂ) :
    (∫ z, (∑ a ∈ A, q a * localTaylorTwo (w a) z) ^ 2 ∂steinhausLaw)
      = ‖∑ a ∈ A, (q a : ℂ) * w a‖ ^ 2 / 2
        + ‖∑ a ∈ A, (q a : ℂ) * w a ^ 2‖ ^ 2 / 8 := by
  have hint : ∀ a ∈ A, ∀ b ∈ A, Integrable
      (fun z : ℂ => q a * q b * (localTaylorTwo (w a) z * localTaylorTwo (w b) z)) steinhausLaw :=
    fun a _ b _ => (integrable_localTaylorTwo_mul (w a) (w b)).const_mul _
  have hsq : ∀ z : ℂ, (∑ a ∈ A, q a * localTaylorTwo (w a) z) ^ 2
      = ∑ a ∈ A, ∑ b ∈ A, q a * q b * (localTaylorTwo (w a) z * localTaylorTwo (w b) z) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hstep : (∫ z, (∑ a ∈ A, q a * localTaylorTwo (w a) z) ^ 2 ∂steinhausLaw)
      = ∑ a ∈ A, ∑ b ∈ A, (q a * q b * (w a * (starRingEnd ℂ) (w b)).re / 2
          + q a * q b * (w a ^ 2 * (starRingEnd ℂ) (w b ^ 2)).re / 8) := by
    simp_rw [hsq]
    rw [integral_finsetSum A fun a ha => integrable_finsetSum A fun b hb => hint a ha b hb]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [integral_finsetSum A fun b hb => hint a ha b hb]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_localTaylorTwo_mul]
    ring
  rw [hstep]
  have hsplit : ∑ a ∈ A, ∑ b ∈ A, (q a * q b * (w a * (starRingEnd ℂ) (w b)).re / 2
        + q a * q b * (w a ^ 2 * (starRingEnd ℂ) (w b ^ 2)).re / 8)
      = (∑ a ∈ A, ∑ b ∈ A, q a * q b * (w a * (starRingEnd ℂ) (w b)).re) / 2
        + (∑ a ∈ A, ∑ b ∈ A, q a * q b * (w a ^ 2 * (starRingEnd ℂ) (w b ^ 2)).re) / 8 := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hsplit, sum_sum_re_mul_conj_eq_norm_sq A q w,
    sum_sum_re_mul_conj_eq_norm_sq A q fun a => w a ^ 2]

/-! ### The summand at a prime, under `μ`

The moments above are computed against `steinhausLaw`.  The Gaussian comparison of the block
increment wants them against `μ`, where the summand is `ω ↦ localTaylorTwo (w p) (f(p)(ω))`.
`HasLaw` transports both the integrals and the integrability, and nothing else changes. -/

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- On the unit circle, `‖1 - z w‖ ^ 2 = 1 - (2 Re (z w) - ‖w‖ ^ 2)`. -/
lemma norm_one_sub_mul_sq_eq {z w : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - z * w‖ ^ 2 = 1 - (2 * (z * w).re - ‖w‖ ^ 2) := by
  have h1 : ‖z * w‖ = ‖w‖ := by rw [norm_mul, hz, one_mul]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_eq_norm_sq, h1]
  simp [Complex.mul_re]
  ring

/-- On the unit circle, `‖1 + z w‖ ^ 2 = 1 + 2 Re (z w) + ‖w‖ ^ 2`.  This is
`RMF.norm_one_sub_mul_sq_eq` applied at `-w`. -/
lemma norm_one_add_mul_sq_eq {z w : ℂ} (hz : ‖z‖ = 1) :
    ‖1 + z * w‖ ^ 2 = 1 + 2 * (z * w).re + ‖w‖ ^ 2 := by
  have h := norm_one_sub_mul_sq_eq (z := z) (w := -w) hz
  rw [show z * -w = -(z * w) by ring, sub_neg_eq_add, norm_neg] at h
  rw [h]
  simp [Complex.neg_re]
  ring

/-! ### The moments of the local variable

Write `W w z = 2 Re (z w) - ‖w‖ ^ 2`, so that on the circle `‖1 - z w‖ ^ 2 = 1 - W w z` and
the local integrand is `(1 - W w z) ^ (-q)`.  Its first two moments are what every expansion
below integrates against.
-/

/-- The local variable `W w z = 2 Re (z w) - ‖w‖ ^ 2`; on the unit circle
`‖1 - z w‖ ^ 2 = 1 - W w z` (`RMF.norm_one_sub_mul_sq_eq`). -/
noncomputable def localW (w : ℂ) (z : ℂ) : ℝ := 2 * (z * w).re - ‖w‖ ^ 2

lemma integrable_localW (w : ℂ) : Integrable (localW w) steinhausLaw :=
  ((integrable_re_mul_steinhausLaw w).const_mul 2).sub (integrable_const _)

lemma integrable_localW_sq (w : ℂ) : Integrable (fun z => localW w z ^ 2) steinhausLaw := by
  have h : ∀ z : ℂ, localW w z ^ 2
      = 4 * ((z * w).re) ^ 2 - 4 * ‖w‖ ^ 2 * (z * w).re + ‖w‖ ^ 4 := by
    intro z; rw [localW]; ring
  have hA : Integrable
      (fun z : ℂ => 4 * ((z * w).re) ^ 2 - 4 * ‖w‖ ^ 2 * (z * w).re) steinhausLaw :=
    ((integrable_re_mul_sq_steinhausLaw w).const_mul 4).sub
      ((integrable_re_mul_steinhausLaw w).const_mul (4 * ‖w‖ ^ 2))
  simp_rw [h]
  exact hA.add (integrable_const _)

/-- **The first moment**: `E W = -‖w‖ ^ 2`. -/
lemma integral_localW (w : ℂ) : (∫ z, localW w z ∂steinhausLaw) = -‖w‖ ^ 2 := by
  have hA : Integrable (fun z : ℂ => 2 * (z * w).re) steinhausLaw :=
    (integrable_re_mul_steinhausLaw w).const_mul 2
  simp_rw [localW]
  rw [integral_sub hA (integrable_const _), integral_const_mul, integral_re_mul_steinhausLaw,
    integral_const]
  simp

/-- **The second moment**: `E W ^ 2 = 2 ‖w‖ ^ 2 + ‖w‖ ^ 4`. -/
lemma integral_localW_sq (w : ℂ) :
    (∫ z, localW w z ^ 2 ∂steinhausLaw) = 2 * ‖w‖ ^ 2 + ‖w‖ ^ 4 := by
  have h : ∀ z : ℂ, localW w z ^ 2
      = 4 * ((z * w).re) ^ 2 - 4 * ‖w‖ ^ 2 * (z * w).re + ‖w‖ ^ 4 := by
    intro z; rw [localW]; ring
  have hA : Integrable (fun z : ℂ => 4 * ((z * w).re) ^ 2) steinhausLaw :=
    (integrable_re_mul_sq_steinhausLaw w).const_mul 4
  have hB : Integrable (fun z : ℂ => 4 * ‖w‖ ^ 2 * (z * w).re) steinhausLaw :=
    (integrable_re_mul_steinhausLaw w).const_mul (4 * ‖w‖ ^ 2)
  have hAB : Integrable
      (fun z : ℂ => 4 * ((z * w).re) ^ 2 - 4 * ‖w‖ ^ 2 * (z * w).re) steinhausLaw := hA.sub hB
  simp_rw [h]
  rw [integral_add hAB (integrable_const _), integral_sub hA hB, integral_const_mul,
    integral_const_mul, integral_re_mul_sq_steinhausLaw, integral_re_mul_steinhausLaw,
    integral_const]
  simp
  ring

/-- On the circle, the local integrand is a power of `1 - W`. -/
lemma norm_inv_one_sub_rpow_eq (q : ℝ) {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    ‖(1 - z * w)⁻¹‖ ^ (2 * q) = (1 - localW w z) ^ (-q) := by
  have hsq : ‖1 - z * w‖ ^ 2 = 1 - localW w z := norm_one_sub_mul_sq_eq hz
  have hpos : (0 : ℝ) < ‖1 - z * w‖ := by
    have hzw : ‖z * w‖ = ‖w‖ := by rw [norm_mul, hz, one_mul]
    have : 1 - ‖w‖ ≤ ‖1 - z * w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (z * w)
      rwa [norm_one, hzw] at this
    linarith
  rw [← hsq, norm_inv, ← Real.rpow_natCast ‖1 - z * w‖ 2, ← Real.rpow_mul hpos.le,
    Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]
  norm_num

/-- Second-order Taylor bound for `-log (1 - w)` on `|w| ≤ 1/2`. -/
lemma abs_neg_log_one_sub_sub_le {w : ℝ} (hw : |w| ≤ 1 / 2) :
    |(-Real.log (1 - w)) - (w + w ^ 2 / 2)| ≤ 2 * |w| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := w) (by linarith) 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  norm_num at h
  have habs : (0 : ℝ) ≤ |w| := abs_nonneg w
  have hden : (1 : ℝ) / 2 ≤ 1 - |w| := by linarith
  have hb : |w| ^ 3 / (1 - |w|) ≤ 2 * |w| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg habs 3]
  calc |(-Real.log (1 - w)) - (w + w ^ 2 / 2)| = |w + w ^ 2 / 2 + Real.log (1 - w)| := by
        rw [← abs_neg]; ring_nf
    _ ≤ |w| ^ 3 / (1 - |w|) := by convert h using 2
    _ ≤ 2 * |w| ^ 3 := hb

/-- Second-order Taylor bound for `exp` on `|u| ≤ 1`. -/
lemma abs_exp_sub_taylor_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp u - (1 + u + u ^ 2 / 2)| ≤ |u| ^ 3 := by
  have h := Real.exp_bound hu (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  calc |Real.exp u - (1 + u + u ^ 2 / 2)| ≤ |u| ^ 3 * (4 / 18) := by convert h using 2; ring
    _ ≤ |u| ^ 3 := by linarith [pow_nonneg (abs_nonneg u) 3]

/-- **The second-order expansion of `(1 - w) ^ (-α)`, uniform for `|α| ≤ Q`**:
`|(1 - w) ^ (-α) - (1 + α w + α(α+1) w²/2)| ≤ C |w|³` for `|w| ≤ 1/2`.  The exponent may have
either sign, covering the Steinhaus powers `(1 - W)^{-q}` and the Rademacher powers `(1 + W)^{q}`.
The proof feeds the expansion of `L = -log (1 - w)` into that of `exp` where `|α L| ≤ 1`; on the
rest of the range `|w|` is bounded below and the estimate is trivial. -/
lemma exists_taylor_bound_one_sub_rpow {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C > 0, ∀ α ∈ Set.Icc (-Q) Q, ∀ w : ℝ, |w| ≤ 1 / 2 →
      |(1 - w) ^ (-α) - (1 + α * w + α * (α + 1) / 2 * w ^ 2)| ≤ C * |w| ^ 3 := by
  set c : ℝ := 1 / (2 * Q + 2) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  set B : ℝ := Real.exp Q + 1 + Q / 2 + Q * (Q + 1) / 8 with hBdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  refine ⟨B / c ^ 3 + 2 * Q + 3 * Q ^ 2 + 8 * Q ^ 3, by positivity, ?_⟩
  rintro α ⟨hαl, hαu⟩ w hw
  have hαabs : |α| ≤ Q := abs_le.mpr ⟨hαl, hαu⟩
  obtain ⟨hw₁, hw₂⟩ := abs_le.mp hw
  have hpos : (0 : ℝ) < 1 - w := by linarith
  have habs : (0 : ℝ) ≤ |w| := abs_nonneg w
  have hcube : (0 : ℝ) ≤ |w| ^ 3 := pow_nonneg habs 3
  -- `L` is the logarithm, and `α * L` the exponent.
  set L : ℝ := -Real.log (1 - w) with hLdef
  have hrpow : (1 - w) ^ (-α) = Real.exp (α * L) := by
    rw [Real.rpow_def_of_pos hpos, hLdef]; ring_nf
  have hLtaylor : |L - (w + w ^ 2 / 2)| ≤ 2 * |w| ^ 3 := abs_neg_log_one_sub_sub_le hw
  have hsqle : |w| ^ 2 ≤ |w| / 2 := by nlinarith [sq_abs w]
  have hcubele : |w| ^ 3 ≤ |w| ^ 2 / 2 := by nlinarith [sq_abs w]
  -- Crude consequences: `|L| ≤ 2|w| ≤ 1` and `|L - w| ≤ 3/2 |w| ^ 2`.
  have hLabs : |L| ≤ 2 * |w| := by
    have := (abs_sub_abs_le_abs_sub L (w + w ^ 2 / 2)).trans hLtaylor
    have h1 : |w + w ^ 2 / 2| ≤ |w| + |w| ^ 2 / 2 := by
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_div, abs_pow, abs_two]
    linarith
  have hLw : |L - w| ≤ 3 / 2 * |w| ^ 2 := by
    have h1 : |L - w| ≤ |L - (w + w ^ 2 / 2)| + |w ^ 2 / 2| := by
      have : L - w = (L - (w + w ^ 2 / 2)) + w ^ 2 / 2 := by ring
      rw [this]; exact abs_add_le _ _
    rw [abs_div, abs_pow, abs_two] at h1
    linarith
  have hαL : |α * L| ≤ 2 * Q * |w| := by
    rw [abs_mul]
    calc |α| * |L| ≤ Q * (2 * |w|) := mul_le_mul hαabs hLabs (abs_nonneg L) hQ
      _ = 2 * Q * |w| := by ring
  by_cases hsmall : |w| ≤ c
  · -- Small `w`: the exponent is at most `1` and the two expansions compose.
    have hu : |α * L| ≤ 1 := by
      refine hαL.trans ?_
      have h2 : 2 * Q * c ≤ 1 := by
        rw [hcdef, mul_one_div, div_le_one (by linarith)]; linarith
      have h3 : 2 * Q * |w| ≤ 2 * Q * c := by
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      linarith
    have hexp : |Real.exp (α * L) - (1 + α * L + (α * L) ^ 2 / 2)| ≤ |α * L| ^ 3 :=
      abs_exp_sub_taylor_le hu
    -- Split the difference into the three error terms.
    have hsplit : Real.exp (α * L) - (1 + α * w + α * (α + 1) / 2 * w ^ 2)
        = (Real.exp (α * L) - (1 + α * L + (α * L) ^ 2 / 2))
          + α * (L - (w + w ^ 2 / 2)) + α ^ 2 * ((L - w) * (L + w)) / 2 := by ring
    have hT1 : |α * L| ^ 3 ≤ 8 * Q ^ 3 * |w| ^ 3 := by
      calc |α * L| ^ 3 ≤ (2 * Q * |w|) ^ 3 := by gcongr
        _ = 8 * Q ^ 3 * |w| ^ 3 := by ring
    have hT2 : |α * (L - (w + w ^ 2 / 2))| ≤ 2 * Q * |w| ^ 3 := by
      rw [abs_mul]
      calc |α| * |L - (w + w ^ 2 / 2)| ≤ Q * (2 * |w| ^ 3) :=
            mul_le_mul hαabs hLtaylor (abs_nonneg _) hQ
        _ = 2 * Q * |w| ^ 3 := by ring
    have hT3 : |α ^ 2 * ((L - w) * (L + w)) / 2| ≤ 3 * Q ^ 2 * |w| ^ 3 := by
      have hsum : |L + w| ≤ 3 * |w| := (abs_add_le _ _).trans (by linarith)
      have hprod : |(L - w) * (L + w)| ≤ 3 / 2 * |w| ^ 2 * (3 * |w|) := by
        rw [abs_mul]
        exact mul_le_mul hLw hsum (abs_nonneg _) (by positivity)
      have hq2 : |α ^ 2| ≤ Q ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg α) hαabs 2
      have hQw : (0 : ℝ) ≤ Q ^ 2 * |w| ^ 3 := by positivity
      calc |α ^ 2 * ((L - w) * (L + w)) / 2|
          = |α ^ 2| * |(L - w) * (L + w)| / 2 := by rw [abs_div, abs_mul, abs_two]
        _ ≤ Q ^ 2 * (3 / 2 * |w| ^ 2 * (3 * |w|)) / 2 := by gcongr
        _ = 9 / 4 * (Q ^ 2 * |w| ^ 3) := by ring
        _ ≤ 3 * Q ^ 2 * |w| ^ 3 := by linarith
    have hC0 : (0 : ℝ) ≤ B / c ^ 3 := by positivity
    rw [hrpow, hsplit]
    calc |(Real.exp (α * L) - (1 + α * L + (α * L) ^ 2 / 2))
            + α * (L - (w + w ^ 2 / 2)) + α ^ 2 * ((L - w) * (L + w)) / 2|
        ≤ |(Real.exp (α * L) - (1 + α * L + (α * L) ^ 2 / 2)) + α * (L - (w + w ^ 2 / 2))|
            + |α ^ 2 * ((L - w) * (L + w)) / 2| := abs_add_le _ _
      _ ≤ (|Real.exp (α * L) - (1 + α * L + (α * L) ^ 2 / 2)| + |α * (L - (w + w ^ 2 / 2))|)
            + |α ^ 2 * ((L - w) * (L + w)) / 2| := by gcongr; exact abs_add_le _ _
      _ ≤ (8 * Q ^ 3 * |w| ^ 3 + 2 * Q * |w| ^ 3) + 3 * Q ^ 2 * |w| ^ 3 := by
          gcongr
          exact hexp.trans hT1
      _ = (2 * Q + 3 * Q ^ 2 + 8 * Q ^ 3) * |w| ^ 3 := by ring
      _ ≤ (B / c ^ 3 + 2 * Q + 3 * Q ^ 2 + 8 * Q ^ 3) * |w| ^ 3 := by gcongr; linarith
  · -- Large `w`: both sides are crudely bounded, and `|w| ^ 3 > c ^ 3`.
    rw [not_le] at hsmall
    have hL1 : |L| ≤ 1 := hLabs.trans (by linarith)
    have hexpQ : Real.exp (α * L) ≤ Real.exp Q := by
      refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
      rw [abs_mul]
      calc |α| * |L| ≤ Q * 1 := mul_le_mul hαabs hL1 (abs_nonneg L) hQ
        _ = Q := mul_one Q
    have hlow : |1 + α * w + α * (α + 1) / 2 * w ^ 2| ≤ 1 + Q / 2 + Q * (Q + 1) / 8 := by
      have h1 : |α * w| ≤ Q / 2 := by
        rw [abs_mul]
        calc |α| * |w| ≤ Q * (1 / 2) := mul_le_mul hαabs hw (abs_nonneg w) hQ
          _ = Q / 2 := by ring
      have h2 : |α * (α + 1) / 2 * w ^ 2| ≤ Q * (Q + 1) / 8 := by
        have hα1 : |α + 1| ≤ Q + 1 := by
          rw [abs_le]; constructor <;> linarith [abs_le.mp hαabs |>.1, abs_le.mp hαabs |>.2]
        have hww : |w| ^ 2 ≤ 1 / 4 := by nlinarith
        have hnum : |α * (α + 1)| ≤ Q * (Q + 1) := by
          rw [abs_mul]
          exact mul_le_mul hαabs hα1 (abs_nonneg _) hQ
        calc |α * (α + 1) / 2 * w ^ 2| = |α * (α + 1)| / 2 * |w| ^ 2 := by
              rw [abs_mul, abs_div, abs_two, abs_pow]
          _ ≤ Q * (Q + 1) / 2 * (1 / 4) :=
              mul_le_mul (by linarith) hww (by positivity) (by positivity)
          _ = Q * (Q + 1) / 8 := by ring
      calc |1 + α * w + α * (α + 1) / 2 * w ^ 2|
          ≤ |1 + α * w| + |α * (α + 1) / 2 * w ^ 2| := abs_add_le _ _
        _ ≤ (1 + |α * w|) + |α * (α + 1) / 2 * w ^ 2| := by
            gcongr; simpa using abs_add_le (1 : ℝ) (α * w)
        _ ≤ 1 + Q / 2 + Q * (Q + 1) / 8 := by linarith
    have hcw : c ^ 3 ≤ |w| ^ 3 := pow_le_pow_left₀ hc0.le hsmall.le 3
    have hLHS : |(1 - w) ^ (-α) - (1 + α * w + α * (α + 1) / 2 * w ^ 2)| ≤ B := by
      rw [hrpow, hBdef]
      calc |Real.exp (α * L) - (1 + α * w + α * (α + 1) / 2 * w ^ 2)|
          ≤ |Real.exp (α * L)| + |1 + α * w + α * (α + 1) / 2 * w ^ 2| :=
            abs_sub _ _
        _ ≤ Real.exp Q + (1 + Q / 2 + Q * (Q + 1) / 8) := by
            gcongr
            rw [abs_of_pos (Real.exp_pos _)]; exact hexpQ
        _ = Real.exp Q + 1 + Q / 2 + Q * (Q + 1) / 8 := by ring
    have hstep : B ≤ B / c ^ 3 * |w| ^ 3 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc0 3)]
      exact mul_le_mul_of_nonneg_left hcw hB0.le
    have hrest : (0 : ℝ) ≤ (2 * Q + 3 * Q ^ 2 + 8 * Q ^ 3) * |w| ^ 3 := by positivity
    calc |(1 - w) ^ (-α) - (1 + α * w + α * (α + 1) / 2 * w ^ 2)| ≤ B := hLHS
      _ ≤ B / c ^ 3 * |w| ^ 3 := hstep
      _ ≤ (B / c ^ 3 + 2 * Q + 3 * Q ^ 2 + 8 * Q ^ 3) * |w| ^ 3 := by linarith

end RMF
