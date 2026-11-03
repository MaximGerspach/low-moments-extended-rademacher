/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfSmallPrimes
import RMF.Probability.RademacherRestrictedFirstMomentLower
import RMF.Weighted.EulerMomentShiftExplicit
import RMF.Weighted.FixedQAboveHalf

/-!
# The barriered first moment at `q = ½`

The counterpart of Proposition 6.3 of the paper,
`RMF.exists_le_setIntegral_halfBarrier_halfAfter`: uniformly for `k ≥ k₁`, `t - k ≥ T₀` and `h` in
the window at scale `k`,

`c·e^{t-k}/√(t-k) ≤ ∫_{L(k,h) ∩ E_>(k)} ‖F_{(k,y)}(½+σ+ih)‖²`,

with `F_{(k,y)}` over the primes `p < y` with `log log p > k`, the barrier `L(k,h)` of
`RMF.halfBarrier` (its constants `(j₀, C₁, a, B)` supplied by the theorem) and the level event
`E_>(k)` of `RMF.halfAfter`.  The barrier splits at depth `j₀` into a box and Harper's tube, and
the primes split with it at `RMF.scaleCut (k+j₀)`.

## Map

* **The two-exponent weight** `E[‖F(σ+ih)‖^{l₁}‖F(σ)‖^{l₂}]`, a product over the primes of two-atom
  averages (`RMF.integral_exp_pair_eq_prod`), at the four exponent pairs the proof uses.
* **Mertens, sharply** (`RMF.le_sum_sq_rpow_neg_primesIco_sharp`): `U ≥ (n-m) - 2` over the scales
  `[m, n)`.  The first moment needs `E‖F‖² ≍ e^{t-k}` with the coefficient of the exponent equal
  to one, so the `σ`-damping is paid additively.
* **Below the cut**: the descent event `A₁` (`RMF.halfDescent`, probability `≥ 2^{-j₀}` by
  symmetry) and the box give `∫_{box ∩ A₁} ‖F_{(k,k+j₀]}(σ+ih)‖² ≥ e^{-2C₁}2^{-j₀-1}`
  (`RMF.le_setIntegral_halfBox_halfDescent`).
* **Above the cut**: Harper's Proposition 5
  (`RMF.exists_const_proposition5_rademacher_of_cutoff_wide`) at offset `k+j₀` with curvature
  `hf j = -2 log j`, its full-product tilt turned into the block product by
  `RMF.le_setIntegral_normSq_of_le_tilted`.
* **The level event** `E_>(k)`, by subtraction over the first exceedance of a level `C₂`
  (`RMF.exists_halfTube_bounds`, `RMF.sum_exceed_weights_le`): Chernoff below the cut,
  Proposition 5's upper half above it.

The constants are chosen in the order `a, B` (Proposition 5), `C₂` (the subtraction), `j₀` (the
descent reaches `-C₂`), `C₁` (the box).  The hypothesis `scaleCut (t+1) ≤ y` asks for one block
beyond the top of the barrier, as Proposition 5's `blockCutoff ϑ n` does; the decomposition meets
it at `y = ⌊x⌋₊+1` (`RMF.scaleCut_le_floor_succ`).
-/

open MeasureTheory

open scoped ENNReal

set_option linter.style.longFile 3000

namespace RMF

/-! ### The two-exponent weight

Every moment used below is of the shape `E[‖F(σ+ih)‖^{l₁}·‖F(σ)‖^{l₂}]`: the normalisation at
`(2,0)`, the Markov bounds for the box at `(±1,0)`, and the Chernoff bound against the
real-point walk at `(2,½)`.  One factorisation serves all of them. -/

section Pair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h : ℝ}

/-- **The two-exponent weight at one prime.**  The two atoms of `RMF.rademacherLaw` give
`‖1 ± p^{-s}‖² = (1 ± u)² ∓ 2ud` at height `h`, with `u = p^{-1/2-σ}` and
`d = 1 - cos(h log p)`, and `1 ± u` at height `0`. -/
lemma integral_exp_pair_rademacherLaw {p : ℕ} (hp : 5 ≤ p) {l₁ l₂ : ℝ} (hσ : 0 ≤ σ) :
    (∫ z, Real.exp (l₁ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖
        + l₂ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖) ∂rademacherLaw)
      = (Real.exp (l₁ / 2 * Real.log ((1 + (p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
              - 2 * (p : ℝ) ^ (-(1 / 2 + σ)) * (1 - Real.cos (h * Real.log p)))
            + l₂ * Real.log (1 + (p : ℝ) ^ (-(1 / 2 + σ))))
          + Real.exp (l₁ / 2 * Real.log ((1 - (p : ℝ) ^ (-(1 / 2 + σ))) ^ 2
              + 2 * (p : ℝ) ^ (-(1 / 2 + σ)) * (1 - Real.cos (h * Real.log p)))
            + l₂ * Real.log (1 - (p : ℝ) ^ (-(1 / 2 + σ))))) / 2 := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set u : ℝ := (p : ℝ) ^ (-(1 / 2 + σ)) with hu_def
  set d : ℝ := 1 - Real.cos (h * Real.log p) with hd_def
  have hu0 : 0 < u := Real.rpow_pos_of_pos hpR _
  have hu2 : u ≤ 1 / 2 := rpow_neg_half_add_le_half hp hσ
  have hnorm0pos : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 + u := by
    rw [one_mul, cpow_neg_shiftLine_zero p σ, ← hu_def,
      show (1 : ℂ) + ((u : ℝ) : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnorm0neg : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ 0)‖ = 1 - u := by
    rw [cpow_neg_shiftLine_zero p σ, ← hu_def,
      show (1 : ℂ) + (-1) * ((u : ℝ) : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnormhpos : ‖1 + (1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 = (1 + u) ^ 2 - 2 * u * d := by
    rw [norm_one_add_mul_sq_eq (by simp), one_mul, re_cpow_neg_shiftLine hp0,
      norm_cpow_neg_shiftLine hp0, ← hu_def, hd_def]
    ring
  have hnormhneg : ‖1 + (-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2 = (1 - u) ^ 2 + 2 * u * d := by
    have hrw : ((-1 : ℂ) * (p : ℂ) ^ (-shiftLine σ h)).re
        = -((p : ℂ) ^ (-shiftLine σ h)).re := by simp
    rw [norm_one_add_mul_sq_eq (by simp), hrw, re_cpow_neg_shiftLine hp0,
      norm_cpow_neg_shiftLine hp0, ← hu_def, hd_def]
    ring
  have hhalf : ∀ z : ℂ, l₁ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖
      = l₁ / 2 * Real.log (‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2) := by
    intro z
    rw [Real.log_pow]
    push_cast
    ring
  rw [integral_rademacherLaw_eq]
  simp only [smul_eq_mul, hhalf, hnormhpos, hnormhneg, hnorm0pos, hnorm0neg]
  ring

/-- **The two-exponent weight over a range, factorised.**  The mirror of
`RMF.integral_exp_mul_twist_eq_prod` with the twist replaced by a free pair of exponents. -/
theorem integral_exp_pair_eq_prod (hX : IsRademacherPrimeValues X μ) (ha5 : 5 ≤ a)
    (hσ : 0 ≤ σ) (l₁ l₂ : ℝ) :
    (∫ ω, Real.exp (l₁ * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
          + l₂ * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) ∂μ)
      = ∏ p ∈ primesIco a b,
          ∫ z, Real.exp (l₁ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖
            + l₂ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖) ∂rademacherLaw := by
  classical
  have hSp : ∀ p ∈ primesIco a b, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hS5 : ∀ p ∈ primesIco a b, 5 ≤ p := by
    intro p hp
    have := (mem_primesIco.1 hp).2.1
    omega
  set g : ℕ → ℂ → ℝ := fun p z => Real.exp (l₁ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖
    + l₂ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖) with hg_def
  have hgm : ∀ p : ℕ, Measurable (g p) := by
    intro p
    rw [hg_def]
    fun_prop
  have hpt : ∀ᵐ ω ∂μ,
      Real.exp (l₁ * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
          + l₂ * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)
        = ∏ p ∈ primesIco a b, g p (X p ω) := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
    have hsmall : ∀ p ∈ primesIco a b, ∀ t : ℝ,
        ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ t))‖ < 1 := by
      intro p hp t
      rw [norm_cpow_neg_shiftLine (hSp p hp).pos]
      have h5 := hS5 p hp
      have := rpow_neg_half_add_le_half h5 hσ
      linarith
    have hposh : ∀ p ∈ primesIco a b, 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ :=
      fun p hp => norm_one_add_mul_pos_of_le_one (hω p hp) (hsmall p hp h)
    have hpos0 : ∀ p ∈ primesIco a b, 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖ :=
      fun p hp => norm_one_add_mul_pos_of_le_one (hω p hp) (hsmall p hp 0)
    rw [hg_def]
    simp only [randomEulerProductIco_sqfree_eq, norm_prod]
    rw [Real.log_prod (fun p hp => ne_of_gt (hposh p hp)),
      Real.log_prod (fun p hp => ne_of_gt (hpos0 p hp)), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, Real.exp_sum]
  rw [integral_congr_ae hpt]
  exact hX.integral_prod hSp g fun p _ => (hgm p).aestronglyMeasurable

end Pair

/-! ### The four atom averages

The per-prime value of `RMF.integral_exp_pair_rademacherLaw` at the four exponent pairs used below.
Writing `u = p^{-1/2-σ}` and `c = cos(h log p) = 1 - d`, the two atoms of `‖1 + z p^{-s}‖²` are
`1 + u² ± 2uc`, and the two of `‖1 + z p^{-σ}‖` are `1 ± u`. -/

section Atoms

variable {u d : ℝ}

private lemma exp_half_log {A : ℝ} (hA : 0 < A) : Real.exp (1 / 2 * Real.log A) = Real.sqrt A := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hA, mul_comm]

private lemma atomPos (hu0 : 0 < u) (hu : u ≤ 1 / 2) (hd2 : d ≤ 2) :
    (0 : ℝ) < (1 + u) ^ 2 - 2 * u * d := by nlinarith [sq_nonneg (1 - u)]

private lemma atomNeg (hu0 : 0 < u) (hu : u ≤ 1 / 2) (hd0 : 0 ≤ d) :
    (0 : ℝ) < (1 - u) ^ 2 + 2 * u * d := by nlinarith [sq_nonneg (1 - u)]

/-- **The first moment at one prime is at most `1 + u²/2`**, by `√A ≤ (1 + A)/2`. -/
lemma atoms_one_zero_le (hu0 : 0 < u) (hu : u ≤ 1 / 2) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    (Real.exp (1 / 2 * Real.log ((1 + u) ^ 2 - 2 * u * d) + 0 * Real.log (1 + u))
        + Real.exp (1 / 2 * Real.log ((1 - u) ^ 2 + 2 * u * d) + 0 * Real.log (1 - u))) / 2
      ≤ 1 + u ^ 2 / 2 := by
  have hA := atomPos hu0 hu hd2
  have hB := atomNeg hu0 hu hd0
  have hsq : ∀ A : ℝ, 0 < A → Real.sqrt A ≤ (1 + A) / 2 := by
    intro A hA'
    rw [show (1 + A) / 2 = Real.sqrt (((1 + A) / 2) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - A)])
  simp only [zero_mul, add_zero]
  rw [exp_half_log hA, exp_half_log hB]
  have h1 := hsq _ hA
  have h2 := hsq _ hB
  linarith

/-- **The reciprocal first moment at one prime is at most `1 + 12u²`.**  The two linear terms
cancel in the average, which is why the quadratic expansion of `(1+y)^{-1/2}` is needed. -/
lemma atoms_neg_one_zero_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    (Real.exp (-1 / 2 * Real.log ((1 + u) ^ 2 - 2 * u * d) + 0 * Real.log (1 + u))
        + Real.exp (-1 / 2 * Real.log ((1 - u) ^ 2 + 2 * u * d) + 0 * Real.log (1 - u))) / 2
      ≤ 1 + 12 * u ^ 2 := by
  have hu2 : u ≤ 1 / 2 := by linarith
  have hA := atomPos hu0 hu2 hd2
  have hB := atomNeg hu0 hu2 hd0
  -- `1/√(1+y) ≤ 1 - y/2 + 3y²` for `|y| ≤ 1/2`
  have hinv : ∀ y : ℝ, |y| ≤ 1 / 2 → (Real.sqrt (1 + y))⁻¹ ≤ 1 - y / 2 + 3 * y ^ 2 := by
    intro y hy
    rw [abs_le] at hy
    have hy1 : (0 : ℝ) < 1 + y := by linarith
    have ht : (0 : ℝ) < 1 - y / 2 + 3 * y ^ 2 := by nlinarith [sq_nonneg y]
    have hs : Real.sqrt (1 + y) ^ 2 = 1 + y := Real.sq_sqrt hy1.le
    have hs0 : 0 < Real.sqrt (1 + y) := Real.sqrt_pos.2 hy1
    have hcube : (0 : ℝ) ≤ y ^ 3 + 1 / 8 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y + 1 / 2)
        (by nlinarith [sq_nonneg (2 * y - 1)] : (0 : ℝ) ≤ y ^ 2 - y / 2 + 1 / 4)]
    have hbr : (0 : ℝ) ≤ 21 / 4 + 13 / 4 * y + 6 * y ^ 2 + 9 * y ^ 3 := by
      linarith [hcube, sq_nonneg y]
    have hpoly : (1 : ℝ) ≤ (1 - y / 2 + 3 * y ^ 2) ^ 2 * (1 + y) := by
      nlinarith [mul_nonneg (sq_nonneg y) hbr]
    have hx : (1 : ℝ) ≤ ((1 - y / 2 + 3 * y ^ 2) * Real.sqrt (1 + y)) ^ 2 := by
      rw [mul_pow, hs]; exact hpoly
    have hxpos : 0 < (1 - y / 2 + 3 * y ^ 2) * Real.sqrt (1 + y) := mul_pos ht hs0
    rw [inv_le_iff_one_le_mul₀ hs0]
    nlinarith [hx, hxpos]
  have hyA : |(1 + u) ^ 2 - 2 * u * d - 1| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hyB : |(1 - u) ^ 2 + 2 * u * d - 1| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have h1 := hinv _ hyA
  have h2 := hinv _ hyB
  rw [show (1 : ℝ) + ((1 + u) ^ 2 - 2 * u * d - 1) = (1 + u) ^ 2 - 2 * u * d by ring] at h1
  rw [show (1 : ℝ) + ((1 - u) ^ 2 + 2 * u * d - 1) = (1 - u) ^ 2 + 2 * u * d by ring] at h2
  simp only [zero_mul, add_zero]
  rw [show (-1 : ℝ) / 2 * Real.log ((1 + u) ^ 2 - 2 * u * d)
      = -(1 / 2 * Real.log ((1 + u) ^ 2 - 2 * u * d)) by ring,
    show (-1 : ℝ) / 2 * Real.log ((1 - u) ^ 2 + 2 * u * d)
      = -(1 / 2 * Real.log ((1 - u) ^ 2 + 2 * u * d)) by ring,
    Real.exp_neg, Real.exp_neg, exp_half_log hA, exp_half_log hB]
  have hw : (0 : ℝ) ≤ u ^ 2 * (4 - (2 - 2 * d) ^ 2) :=
    mul_nonneg (sq_nonneg u) (by nlinarith [mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 2 - d)])
  have hu4 : (0 : ℝ) ≤ u ^ 2 * (1 - 6 * u ^ 2) := mul_nonneg (sq_nonneg u) (by nlinarith)
  have hkey : 3 * (((1 + u) ^ 2 - 2 * u * d - 1) ^ 2 + ((1 - u) ^ 2 + 2 * u * d - 1) ^ 2)
      ≤ 25 * u ^ 2 := by nlinarith [hw, hu4]
  linarith [h1, h2, hkey]

/-- The two square roots `√(1±u)`: their sum is at most `2 - u²/4` and their difference lies
between `u` and `u + 2u³`.  All three follow from `(sp+sm)² + (sp-sm)² = 4` and
`(sp+sm)(sp-sm) = 2u`. -/
private lemma sqrt_pair_bounds {u sp sm : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2)
    (hsp2 : sp ^ 2 = 1 + u) (hsm2 : sm ^ 2 = 1 - u) (hsp0 : 0 < sp) (hsm0 : 0 < sm) :
    u ≤ sp - sm ∧ sp - sm ≤ u + 2 * u ^ 3 ∧ sp + sm ≤ 2 - u ^ 2 / 4 := by
  have hprod : sp * sm ≤ 1 := by nlinarith [sq_nonneg (sp - sm)]
  have hSle2 : sp + sm ≤ 2 := by nlinarith
  have hD1 : u ≤ sp - sm := by nlinarith
  have hsp1 : 1 ≤ sp := by nlinarith
  have hDle2u : sp - sm ≤ 2 * u := by nlinarith
  have hSge : 2 - 2 * u ^ 2 ≤ sp + sm := by nlinarith
  have hD2 : sp - sm ≤ u + 2 * u ^ 3 := by nlinarith
  have hS : sp + sm ≤ 2 - u ^ 2 / 4 := by nlinarith
  exact ⟨hD1, hD2, hS⟩

/-- The cosine term of the mixed moment: `ucD ≤ (1+u²)u²c + u⁴` whenever `u ≤ D ≤ u + 2u³`
and `|c| ≤ 1`, the two signs of `c` being handled separately. -/
private lemma mixed_cos_bound {u c D : ℝ} (hu0 : 0 < u) (hc1 : -1 ≤ c) (hc2 : c ≤ 1)
    (hlo : u ≤ D) (hhi : D ≤ u + 2 * u ^ 3) :
    u * c * D ≤ (1 + u ^ 2) * (u ^ 2 * c) + u ^ 4 := by
  have hXlo : -(u ^ 3) ≤ D - u - u ^ 3 := by linarith
  have hXhi : D - u - u ^ 3 ≤ u ^ 3 := by linarith
  have hkey : u * c * (D - u - u ^ 3) ≤ u ^ 4 := by
    rcases le_total 0 c with hc | hc
    · calc u * c * (D - u - u ^ 3) ≤ u * c * u ^ 3 :=
            mul_le_mul_of_nonneg_left hXhi (by positivity)
        _ ≤ u ^ 4 := by
            nlinarith [mul_nonneg (pow_nonneg hu0.le 4) (by linarith : (0 : ℝ) ≤ 1 - c)]
    · calc u * c * (D - u - u ^ 3) ≤ u * c * -(u ^ 3) :=
            mul_le_mul_of_nonpos_left hXlo (by nlinarith)
        _ ≤ u ^ 4 := by
            nlinarith [mul_nonneg (pow_nonneg hu0.le 4) (by linarith : (0 : ℝ) ≤ 1 + c)]
  have hsplit : u * c * D = (1 + u ^ 2) * (u ^ 2 * c) + u * c * (D - u - u ^ 3) := by ring
  rw [hsplit]
  linarith

/-- **The mixed moment at one prime.**  `E[‖1 + zp^{-s}‖²‖1 + zp^{-σ}‖^{1/2}]` is at most
`(1 + u²)·(1 - u²/8 + u² cos(h log p) + 2u⁴)`: the `-u²/8` is the Chernoff exponent at `λ = ½`,
and the `u² cos` is what the oscillatory sums cancel.  Writing `sp = √(1+u)`, `sm = √(1-u)`,
the value is `(1+u²)(sp+sm)/2 + u cos(h log p)(sp-sm)`. -/
lemma atoms_mixed_le (hu0 : 0 < u) (hu : u ≤ 1 / 200) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    (Real.exp (2 / 2 * Real.log ((1 + u) ^ 2 - 2 * u * d) + 1 / 2 * Real.log (1 + u))
        + Real.exp (2 / 2 * Real.log ((1 - u) ^ 2 + 2 * u * d) + 1 / 2 * Real.log (1 - u))) / 2
      ≤ (1 + u ^ 2) * (1 - u ^ 2 / 8 + u ^ 2 * (1 - d) + 2 * u ^ 4) := by
  have hu2 : u ≤ 1 / 2 := by linarith
  have hA := atomPos hu0 hu2 hd2
  have hB := atomNeg hu0 hu2 hd0
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h1u' : (0 : ℝ) < 1 - u := by linarith
  rw [show (2 : ℝ) / 2 = 1 by norm_num]
  simp only [one_mul]
  rw [Real.exp_add, Real.exp_add, Real.exp_log hA, Real.exp_log hB,
    exp_half_log h1u, exp_half_log h1u']
  obtain ⟨hD1, hD2, hS⟩ := sqrt_pair_bounds (sp := Real.sqrt (1 + u)) (sm := Real.sqrt (1 - u))
    hu0 hu2 (Real.sq_sqrt h1u.le) (Real.sq_sqrt h1u'.le) (Real.sqrt_pos.2 h1u)
    (Real.sqrt_pos.2 h1u')
  set sp : ℝ := Real.sqrt (1 + u) with hsp_def
  set sm : ℝ := Real.sqrt (1 - u) with hsm_def
  have hAB := mixed_cos_bound (c := 1 - d) (D := sp - sm) hu0 (by linarith) (by linarith) hD1 hD2
  have hSmul : (1 + u ^ 2) * (sp + sm) ≤ (1 + u ^ 2) * (2 - u ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have hid : ((1 + u) ^ 2 - 2 * u * d) * sp + ((1 - u) ^ 2 + 2 * u * d) * sm
      = (1 + u ^ 2) * (sp + sm) + 2 * (u * (1 - d) * (sp - sm)) := by ring
  calc (((1 + u) ^ 2 - 2 * u * d) * sp + ((1 - u) ^ 2 + 2 * u * d) * sm) / 2
      = ((1 + u ^ 2) * (sp + sm) + 2 * (u * (1 - d) * (sp - sm))) / 2 := by rw [hid]
    _ ≤ ((1 + u ^ 2) * (2 - u ^ 2 / 4)
          + 2 * ((1 + u ^ 2) * (u ^ 2 * (1 - d)) + u ^ 4)) / 2 := by linarith
    _ ≤ (1 + u ^ 2) * (1 - u ^ 2 / 8 + u ^ 2 * (1 - d) + 2 * u ^ 4) := by
        nlinarith [pow_nonneg hu0.le 4, pow_nonneg hu0.le 6]

end Atoms

/-! ### The mass of a range, sharply

`RMF.le_sum_sq_rpow_neg_primesIco` loses a factor `e^{-3}` to the `σ`-damping.  That is harmless
over a bounded number of scales, but the first moment needs `E‖F‖² ≍ e^{t-k}` with the
*coefficient* of the exponent equal to one, so the damping has to be paid additively. -/

section Mass

variable {σ : ℝ}

/-- Mertens' second theorem over a range of scales, from below. -/
lemma le_sum_inv_primesIco {m n : ℕ} (hm : 20 ≤ m) (hmn : m ≤ n) :
    (n : ℝ) - m - 1 / 10
      ≤ ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)), 1 / (p : ℝ) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hx2 : (2 : ℝ) ≤ blockScale (m : ℝ) 0 := two_le_blockScale_zero hm0
  have hxy : blockScale (m : ℝ) 0 ≤ blockScale (n : ℝ) 0 := by
    simp only [blockScale, Nat.cast_zero, zero_add]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 hmnR)
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le _ _ hx2 hxy
  rw [filter_prime_Ioc_eq_primesIco, log_log_blockScale_zero, log_log_blockScale_zero] at hmert
  have h20 : 20 / Real.log (blockScale (m : ℝ) 0) ≤ 1 / 10 := by
    rw [log_blockScale, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h200 : (200 : ℝ) ≤ Real.exp ((0 : ℝ) + m) := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h1 : Real.exp (20 : ℝ) ≤ Real.exp ((0 : ℝ) + m) := by
        refine Real.exp_le_exp.2 ?_
        linarith
      have h2 : Real.exp (20 : ℝ) = Real.exp 1 ^ (20 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 : (2.7 : ℝ) ^ (20 : ℕ) ≤ Real.exp 1 ^ (20 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) he.le 20
      have h4 : (200 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
      linarith
    push_cast at h200 ⊢
    linarith
  have habs := (abs_le.1 hmert).1
  unfold scaleCut
  linarith

/-- **The mass of a range of scales, from below, sharply**: `U ≥ (n - m) - 2`.

`e^{-x} ≥ 1 - x` turns the `σ`-damping into `2σ ∑_{p} (log p)/p`, which Mertens' *first* theorem
caps at `2σ(e^n + 7)`; `σ e^n ≤ ½` makes that a constant. -/
lemma le_sum_sq_rpow_neg_primesIco_sharp {m n : ℕ} (hm : 20 ≤ m) (hmn : m ≤ n) (hσ : 0 ≤ σ)
    (hσn : σ * Real.exp (n : ℝ) ≤ 1 / 2) :
    (n : ℝ) - m - 2
      ≤ ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
          ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
  classical
  have hinv := le_sum_inv_primesIco hm hmn
  -- `1/p - 2σ (log p)/p ≤ p^{-(1+2σ)}`
  have hterm : ∀ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
      1 / (p : ℝ) - 2 * σ * (Real.log p / p) ≤ ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
    intro p hp
    have hprime := prime_of_mem_primesIco hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hsq : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 = (p : ℝ)⁻¹ * Real.exp (-(2 * σ * Real.log p)) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le,
        Real.rpow_def_of_pos hp0, ← Real.exp_log (inv_pos.2 hp0), ← Real.exp_add, Real.log_inv]
      congr 1
      push_cast
      ring
    have hexp : 1 - 2 * σ * Real.log p ≤ Real.exp (-(2 * σ * Real.log p)) := by
      linarith [Real.add_one_le_exp (-(2 * σ * Real.log p))]
    have hmul := mul_le_mul_of_nonneg_left hexp (inv_nonneg.2 hp0.le)
    rw [← hsq] at hmul
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  -- Mertens' first theorem caps the correction
  have hsub : primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ))
      ⊆ Nat.primesBelow (scaleCut (n : ℝ)) := by
    intro p hp
    obtain ⟨hpp, _, hlt⟩ := mem_primesIco.1 hp
    exact Nat.mem_primesBelow.2 ⟨hlt, hpp⟩
  have hcut1 : 1 ≤ scaleCut (n : ℝ) - 1 := by
    have := five_le_scaleCut (show (1 : ℝ) ≤ (n : ℝ) by
      have : (20 : ℕ) ≤ n := le_trans hm hmn
      have : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith)
    omega
  have hfirst := sum_log_div_primesBelow_le hcut1
  rw [show scaleCut (n : ℝ) - 1 + 1 = scaleCut (n : ℝ) from by omega] at hfirst
  have hlogcut : Real.log ((scaleCut (n : ℝ) - 1 : ℕ) : ℝ) ≤ Real.exp (n : ℝ) + 1 := by
    refine le_trans (Real.log_le_log ?_ ?_) (log_scaleCut_le (n : ℝ))
    · have : (1 : ℕ) ≤ scaleCut (n : ℝ) - 1 := hcut1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    · exact_mod_cast Nat.sub_le _ _
  have hlog4 : Real.log 4 ≤ 2 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h2]
    linarith [Real.log_two_lt_d9]
  have hlogsum : ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)), Real.log p / p
      ≤ Real.exp (n : ℝ) + 7 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      log_div_natCast_nonneg p) ?_
    linarith
  have hshift : (∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
        2 * σ * (Real.log p / p)) ≤ 2 * σ * (Real.exp (n : ℝ) + 7) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hlogsum (by linarith)
  have hen200 : (200 : ℝ) ≤ Real.exp (n : ℝ) := by
    have hnR : (20 : ℝ) ≤ (n : ℝ) := by
      have : (20 : ℕ) ≤ n := le_trans hm hmn
      exact_mod_cast this
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp (20 : ℝ) = Real.exp 1 ^ (20 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : (2.7 : ℝ) ^ (20 : ℕ) ≤ Real.exp 1 ^ (20 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he.le 20
    have h4 : (200 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith [Real.exp_le_exp.2 hnR]
  have hσ400 : σ * 200 ≤ σ * Real.exp (n : ℝ) := mul_le_mul_of_nonneg_left hen200 hσ
  have hbudget : 2 * σ * (Real.exp (n : ℝ) + 7) ≤ 3 / 2 := by nlinarith
  linarith

end Mass

/-! ### The four moments over a range -/

section RangeMoments

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h : ℝ}

/-- A.e. positivity of the block product, at any height. -/
lemma ae_norm_randomEulerProductIco_shift_pos (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    (ha5 : 5 ≤ a) (hσ : 0 ≤ σ) (h : ℝ) :
    ∀ᵐ ω ∂μ, 0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
      (shiftLine σ h) ω‖ := by
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
  rw [randomEulerProductIco_sqfree_eq, norm_prod]
  refine Finset.prod_pos fun p hp => ?_
  have hpp := prime_of_mem_primesIco hp
  have hp5 : 5 ≤ (p : ℕ) := by
    have := (mem_primesIco.1 hp).2.1
    omega
  refine norm_one_add_mul_pos_of_le_one (hω p hp) ?_
  rw [norm_cpow_neg_shiftLine hpp.pos]
  have := rpow_neg_half_add_le_half hp5 hσ
  linarith

/-- A product of per-prime bounds becomes an exponential of a sum. -/
private lemma prod_le_exp_sum {S : Finset ℕ} {f g : ℕ → ℝ} (hf0 : ∀ p ∈ S, 0 ≤ f p)
    (hfg : ∀ p ∈ S, f p ≤ 1 + g p) : ∏ p ∈ S, f p ≤ Real.exp (∑ p ∈ S, g p) := by
  calc ∏ p ∈ S, f p ≤ ∏ p ∈ S, Real.exp (g p) :=
        Finset.prod_le_prod hf0 fun p hp =>
          le_trans (hfg p hp) (by linarith [Real.add_one_le_exp (g p)])
    _ = Real.exp (∑ p ∈ S, g p) := (Real.exp_sum _ _).symm

/-- Every per-prime factor is nonnegative. -/
private lemma atomAvg_nonneg {p : ℕ} {l₁ l₂ : ℝ} :
    (0 : ℝ) ≤ ∫ z, Real.exp (l₁ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖
      + l₂ * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖) ∂rademacherLaw :=
  integral_nonneg fun _ => Real.exp_nonneg _

/-- The hypotheses the atom bounds need, at every prime above `40000`. -/
private lemma range_prime_hyps {p : ℕ} (hp : 40000 ≤ p) (hσ : 0 ≤ σ) :
    0 < (p : ℝ) ^ (-(1 / 2 + σ)) ∧ (p : ℝ) ^ (-(1 / 2 + σ)) ≤ 1 / 200
      ∧ 0 ≤ 1 - Real.cos (h * Real.log p) ∧ 1 - Real.cos (h * Real.log p) ≤ 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hpR : (40000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  refine ⟨Real.rpow_pos_of_pos hp0 _, ?_, by linarith [Real.cos_le_one (h * Real.log p)],
    by linarith [Real.neg_one_le_cos (h * Real.log p)]⟩
  refine rpow_neg_half_add_le_inv (by norm_num) ?_ hσ
  calc (200 : ℝ) ^ 2 = 40000 := by norm_num
    _ ≤ (p : ℝ) := hpR

/-- **The second moment over a range is exactly the product of `1 + p^{-1-2σ}`.**  The
`RMF.shiftLine` form of `RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq`. -/
theorem integral_normSq_range_eq_prod (hX : IsRademacherPrimeValues X μ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
        (shiftLine σ h) ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco a b, (1 + ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq a b (shiftLine σ h)]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [norm_cpow_neg_shiftLine (prime_of_mem_primesIco hp).pos]

/-- **The first moment over a range** is at most `e^{U/2}`. -/
theorem integral_exp_log_range_le (hX : IsRademacherPrimeValues X μ) (ha5 : 5 ≤ a) (hσ : 0 ≤ σ) :
    (∫ ω, Real.exp (1 * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
        + 0 * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) ∂μ)
      ≤ Real.exp ((∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 2) := by
  rw [integral_exp_pair_eq_prod hX ha5 hσ, Finset.sum_div]
  refine prod_le_exp_sum (fun p _ => atomAvg_nonneg) fun p hp => ?_
  have hp5 : 5 ≤ p := by
    have := (mem_primesIco.1 hp).2.1
    omega
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  rw [integral_exp_pair_rademacherLaw hp5 hσ]
  exact atoms_one_zero_le (Real.rpow_pos_of_pos hp0 _) (rpow_neg_half_add_le_half hp5 hσ)
    (by linarith [Real.cos_le_one (h * Real.log p)])
    (by linarith [Real.neg_one_le_cos (h * Real.log p)])

/-- **The reciprocal first moment over a range** is at most `e^{12U}`. -/
theorem integral_exp_neg_log_range_le (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) :
    (∫ ω, Real.exp (-1 * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
        + 0 * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) ∂μ)
      ≤ Real.exp (12 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
  have ha5 : 5 ≤ a := by omega
  rw [integral_exp_pair_eq_prod hX ha5 hσ, Finset.mul_sum]
  refine prod_le_exp_sum (fun p _ => atomAvg_nonneg) fun p hp => ?_
  have hp40 : 40000 ≤ p := by
    have := (mem_primesIco.1 hp).2.1
    omega
  have hp5 : 5 ≤ p := by omega
  obtain ⟨hu0, hu, hd0, hd2⟩ := range_prime_hyps (h := h) hp40 hσ
  rw [integral_exp_pair_rademacherLaw hp5 hσ]
  exact atoms_neg_one_zero_le hu0 hu hd0 hd2

/-- **The mixed moment over a range.**  It is at most the second moment times
`e^{C - U/8 + 2W}`, with `C` the oscillatory sum of `p^{-1-2σ} cos(h log p)` and
`W = ∑ p^{-2-4σ}`.  The `-U/8` is the Chernoff exponent of the real-point walk at `λ = ½`. -/
theorem integral_exp_mixed_range_le (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) :
    (∫ ω, Real.exp (2 * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
        + 1 / 2 * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) ∂μ)
      ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2 ∂μ)
        * Real.exp ((∑ p ∈ primesIco a b,
              ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * Real.cos (h * Real.log p))
            - (∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 8
            + 2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4) := by
  have ha5 : 5 ≤ a := by omega
  rw [integral_exp_pair_eq_prod hX ha5 hσ, integral_normSq_range_eq_prod hX]
  have hstep : (∏ p ∈ primesIco a b,
        ∫ z, Real.exp (2 * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ h)‖
          + 1 / 2 * Real.log ‖1 + z * (p : ℂ) ^ (-shiftLine σ 0)‖) ∂rademacherLaw)
      ≤ ∏ p ∈ primesIco a b, ((1 + ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
          * (1 + (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * Real.cos (h * Real.log p)
              - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 / 8
              + 2 * ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4))) := by
    refine Finset.prod_le_prod (fun p _ => atomAvg_nonneg) fun p hp => ?_
    have hp40 : 40000 ≤ p := by
      have := (mem_primesIco.1 hp).2.1
      omega
    have hp5 : 5 ≤ p := by omega
    obtain ⟨hu0, hu, hd0, hd2⟩ := range_prime_hyps (h := h) hp40 hσ
    rw [integral_exp_pair_rademacherLaw hp5 hσ]
    refine le_trans (atoms_mixed_le hu0 hu hd0 hd2) (le_of_eq ?_)
    ring
  refine le_trans hstep ?_
  rw [Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun p _ => by positivity)
  refine le_trans (prod_le_exp_sum (fun p _ => ?_) fun p _ => le_rfl) (le_of_eq ?_)
  · have hc := Real.neg_one_le_cos (h * Real.log p)
    have hu0 : (0 : ℝ) ≤ ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := sq_nonneg _
    have hu4 : (0 : ℝ) ≤ ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4 := by positivity
    nlinarith [mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 1 + Real.cos (h * Real.log p))]
  · congr 1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]

end RangeMoments

/-! ### The descent of the real-point walk over the first blocks

The event `A₁`: each of the first `j₀` increments of the real-point walk is at
most its mean.  Its probability is at least `2^{-j₀}` — the increments are independent, and each
is *symmetric about its mean*, being a sum of two-atom variables symmetric about theirs.  The
symmetry is read off the law: `RMF.IsRademacherPrimeValues.neg` says `-X` is Rademacher too, so
the tuple of values over a block has the same law as its negative. -/

section Descent

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ : ℝ}

/-- **Two families with the same prime law give the same tuple events.**  Both tuples have law
`Measure.pi ν` by `ProbabilityTheory.iIndepFun.hasLaw_pi`. -/
lemma measure_primeTupleSub_mem_eq {ν : Measure ℂ} {Y : ℕ → Ω → ℂ}
    (hX : IsIIDPrimeValues X ν μ) (hY : IsIIDPrimeValues Y ν μ) (B : Finset Nat.Primes)
    {T : Set (↥B → ℂ)} (hT : MeasurableSet T) :
    μ {ω | (fun p : ↥B => X ((p : Nat.Primes) : ℕ) ω) ∈ T}
      = μ {ω | (fun p : ↥B => Y ((p : Nat.Primes) : ℕ) ω) ∈ T} := by
  have hinj : Function.Injective (fun i : ↥B => (i : Nat.Primes)) :=
    fun _ _ hab => Subtype.ext hab
  have hlaw : ∀ Z : ℕ → Ω → ℂ, IsIIDPrimeValues Z ν μ →
      μ {ω | (fun p : ↥B => Z ((p : Nat.Primes) : ℕ) ω) ∈ T}
        = (Measure.pi fun _ : ↥B => ν) T := by
    intro Z hZ
    have hmeas : Measurable fun ω => (fun p : ↥B => Z ((p : Nat.Primes) : ℕ) ω) :=
      measurable_pi_lambda _ fun p => hZ.measurable _ (p : Nat.Primes).2
    have hpi := ProbabilityTheory.iIndepFun.hasLaw_pi
      (fun i : ↥B => hZ.hasLaw ((i : Nat.Primes) : ℕ) (i : Nat.Primes).2)
      (hZ.iIndep.precomp hinj)
    rw [show {ω | (fun p : ↥B => Z ((p : Nat.Primes) : ℕ) ω) ∈ T}
        = (fun ω => (fun p : ↥B => Z ((p : Nat.Primes) : ℕ) ω)) ⁻¹' T from rfl,
      ← Measure.map_apply hmeas hT, hpi.map_eq]
  rw [hlaw X hX, hlaw Y hY]

/-- **The mean of a block increment of the real-point walk**: `∑_p ½ log(1 - p^{-1-2σ})`, which
is negative and, summed over a range of scales, about `-½` per scale. -/
noncomputable def halfBlockMean (θ σ : ℝ) (m : ℕ) : ℝ :=
  (∑ p ∈ primeBlockSub θ m, Real.log (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) / 2

/-- `p^{-1/2-σ} < 1` at every prime. -/
lemma rpow_neg_half_add_lt_one {p : ℕ} (hp : 2 ≤ p) (hσ : 0 ≤ σ) :
    (p : ℝ) ^ (-(1 / 2 + σ)) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- Every value is `±1`, at every prime of a finite block. -/
lemma ae_forall_sq_eq_one_finset (hX : IsRademacherPrimeValues X μ) (B : Finset Nat.Primes) :
    ∀ᵐ ω ∂μ, ∀ p ∈ B, X ((p : Nat.Primes) : ℕ) ω ^ 2 = 1 := by
  refine (Filter.eventually_all_finset _).2 fun p _ => ?_
  have hmeasP : Measurable fun z : ℂ => z ^ 2 = 1 :=
    measurableSet_setOf.1 (measurableSet_eq_fun (by fun_prop) measurable_const)
  exact ((hX.hasLaw ((p : Nat.Primes) : ℕ) p.2).ae_iff hmeasP).2 sq_eq_one_rademacherLaw

/-- **The block increment is symmetric about its mean**: negating the values reflects it. -/
lemma ae_halfBlock_add_neg (hX : IsRademacherPrimeValues X μ) (θ : ℝ) (hσ : 0 ≤ σ) (m : ℕ) :
    ∀ᵐ ω ∂μ, halfBlock X θ σ 0 m ω
        + halfBlock (fun p ω => (-1 : ℂ) * X p ω) θ σ 0 m ω
      = 2 * halfBlockMean θ σ m := by
  filter_upwards [ae_forall_norm_le_one_finset hX norm_le_one_rademacherLaw (primeBlockSub θ m),
    ae_forall_sq_eq_one_finset hX (primeBlockSub θ m)] with ω hω hsq
  rw [halfBlockMean, halfBlock, halfBlock, ← Finset.sum_add_distrib]
  rw [show (2 : ℝ) * ((∑ p ∈ primeBlockSub θ m,
        Real.log (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) / 2)
      = ∑ p ∈ primeBlockSub θ m, Real.log (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) from by ring]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ ((p : Nat.Primes) : ℕ) := p.2.two_le
  have hu1 : (((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 + σ)) < 1 :=
    rpow_neg_half_add_lt_one hp2 hσ
  have hu0 : (0 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 + σ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hwnorm : ‖((((p : Nat.Primes) : ℕ) : ℂ)) ^ (-shiftLine σ 0)‖ < 1 := by
    rw [norm_cpow_neg_shiftLine p.2.pos]
    simpa using hu1
  have hid := localLogAdd_add_localLogAdd_neg (w := ((((p : Nat.Primes) : ℕ) : ℂ))
    ^ (-shiftLine σ 0)) (z := X ((p : Nat.Primes) : ℕ) ω) (hω p hp) hwnorm
  rw [hid, mul_pow, hsq p hp, one_mul, cpow_neg_shiftLine_zero]
  congr 1
  rw [show (1 : ℂ) - (((((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 + σ)) : ℝ) : ℂ) ^ 2
      = ((1 - ((((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 + σ))) ^ 2 : ℝ) : ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]

/-- **Each block increment is at most its mean with probability at least a half.** -/
lemma half_le_measure_halfBlock_le_mean (hX : IsRademacherPrimeValues X μ) (θ : ℝ) (hσ : 0 ≤ σ)
    (m : ℕ) : (2 : ℝ≥0∞)⁻¹ ≤ μ {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m} := by
  classical
  have hprob : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  set B : Finset Nat.Primes := primeBlockSub θ m with hB_def
  set w : Nat.Primes → ℂ := fun p => (((p : ℕ) : ℂ)) ^ (-shiftLine σ 0) with hw_def
  -- the event as a set of tuples
  set T : Set (↥B → ℂ) :=
    {v | ∑ p : ↥B, localLogAdd (w (p : Nat.Primes)) (v p) ≤ halfBlockMean θ σ m} with hT_def
  have hTmeas : MeasurableSet T := by
    refine measurableSet_le (Finset.measurable_sum _ fun p _ => ?_) measurable_const
    exact (measurable_localLogAdd _).comp (measurable_pi_apply p)
  have hmem : ∀ (Z : ℕ → Ω → ℂ) (ω : Ω),
      ((fun p : ↥B => Z ((p : Nat.Primes) : ℕ) ω) ∈ T
        ↔ halfBlock Z θ σ 0 m ω ≤ halfBlockMean θ σ m) := by
    intro Z ω
    rw [hT_def, Set.mem_setOf_eq, halfBlock,
      Finset.sum_coe_sort B fun p => localLogAdd (w p) (Z ((p : Nat.Primes) : ℕ) ω)]
  have hkey := measure_primeTupleSub_mem_eq hX hX.neg B hTmeas
  have hleft : {ω | (fun p : ↥B => X ((p : Nat.Primes) : ℕ) ω) ∈ T}
      = {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m} := by
    ext ω; exact hmem X ω
  have hright : {ω | (fun p : ↥B => ((-1 : ℂ) * X ((p : Nat.Primes) : ℕ) ω)) ∈ T}
      = {ω | halfBlock (fun p ω => (-1 : ℂ) * X p ω) θ σ 0 m ω ≤ halfBlockMean θ σ m} := by
    ext ω; exact hmem (fun p ω => (-1 : ℂ) * X p ω) ω
  rw [hleft, hright] at hkey
  -- the reflected event is the upper one, up to a null set
  have hrefl : μ {ω | halfBlock (fun p ω => (-1 : ℂ) * X p ω) θ σ 0 m ω ≤ halfBlockMean θ σ m}
      = μ {ω | halfBlockMean θ σ m ≤ halfBlock X θ σ 0 m ω} := by
    refine measure_congr ?_
    filter_upwards [ae_halfBlock_add_neg hX θ hσ m] with ω hω
    simp only [eq_iff_iff]
    constructor
    · intro hle
      have hle' : halfBlock (fun p ω => (-1 : ℂ) * X p ω) θ σ 0 m ω
          ≤ halfBlockMean θ σ m := hle
      change halfBlockMean θ σ m ≤ halfBlock X θ σ 0 m ω
      linarith
    · intro hle
      have hle' : halfBlockMean θ σ m ≤ halfBlock X θ σ 0 m ω := hle
      change halfBlock (fun p ω => (-1 : ℂ) * X p ω) θ σ 0 m ω ≤ halfBlockMean θ σ m
      linarith
  rw [hrefl] at hkey
  have hcover : (Set.univ : Set Ω) ⊆ {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m}
      ∪ {ω | halfBlockMean θ σ m ≤ halfBlock X θ σ 0 m ω} := by
    intro ω _
    rcases le_total (halfBlock X θ σ 0 m ω) (halfBlockMean θ σ m) with hle | hle
    · exact Or.inl hle
    · exact Or.inr hle
  have hone : (1 : ℝ≥0∞) ≤ μ {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m}
      + μ {ω | halfBlockMean θ σ m ≤ halfBlock X θ σ 0 m ω} := by
    calc (1 : ℝ≥0∞) = μ Set.univ := (measure_univ).symm
      _ ≤ μ ({ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m}
            ∪ {ω | halfBlockMean θ σ m ≤ halfBlock X θ σ 0 m ω}) := measure_mono hcover
      _ ≤ _ := measure_union_le _ _
  rw [← hkey, ← two_mul] at hone
  rw [ENNReal.inv_le_iff_le_mul (by simp) (by simp)]
  exact hone

end Descent

/-! ### The descent event and its probability -/

section DescentEvent

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ : ℝ}

/-- **The block increments of the real-point walk are independent** — the local logarithms are,
and the blocks are pairwise disjoint. -/
lemma iIndepFun_halfBlock (hX : IsRademacherPrimeValues X μ) (θ : ℝ) :
    ProbabilityTheory.iIndepFun (fun m => halfBlock X θ σ 0 m) μ := by
  have hindep : ProbabilityTheory.iIndepFun
      (fun p : Nat.Primes => fun ω =>
        localLogAdd ((((p : ℕ)) : ℂ) ^ (-(shiftLine σ 0))) (X (p : ℕ) ω)) μ :=
    hX.iIndep.comp
      (fun (p : Nat.Primes) (z : ℂ) => localLogAdd ((((p : ℕ)) : ℂ) ^ (-(shiftLine σ 0))) z)
      fun _ => measurable_localLogAdd _
  exact iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun p : Nat.Primes => (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2))
    hindep (pairwise_disjoint_primeBlockSub θ)

/-- **The descent event `A₁`**: each of the first `n` increments of the real-point walk from
scale `θ` is at most its mean. -/
def halfDescent (X : ℕ → Ω → ℂ) (θ σ : ℝ) (n : ℕ) : Set Ω :=
  ⋂ m ∈ Finset.range n, {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m}

lemma measurableSet_halfDescent (hX : IsRademacherPrimeValues X μ) (θ : ℝ) (n : ℕ) :
    MeasurableSet (halfDescent X θ σ n) :=
  MeasurableSet.biInter (Set.to_countable _) fun m _ =>
    measurableSet_le (measurable_halfBlock hX θ σ 0 m) measurable_const

/-- **The descent event has probability at least `2^{-n}`.** -/
lemma le_measure_halfDescent (hX : IsRademacherPrimeValues X μ) (θ : ℝ) (hσ : 0 ≤ σ) (n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ n ≤ μ (halfDescent X θ σ n) := by
  classical
  have heq := (iIndepFun_halfBlock (σ := σ) hX θ).meas_biInter (S := Finset.range n)
    (s := fun m => {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m})
    fun m _ => ⟨Set.Iic (halfBlockMean θ σ m), measurableSet_Iic, rfl⟩
  rw [halfDescent, heq]
  calc (2 : ℝ≥0∞)⁻¹ ^ n = ∏ _m ∈ Finset.range n, (2 : ℝ≥0∞)⁻¹ := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ m ∈ Finset.range n, μ {ω | halfBlock X θ σ 0 m ω ≤ halfBlockMean θ σ m} :=
        Finset.prod_le_prod' fun m _ => half_le_measure_halfBlock_le_mean hX θ hσ m

omit [MeasurableSpace Ω] in
/-- On the descent event the walk is below the running sum of the means. -/
lemma walk_le_of_mem_halfDescent {θ : ℝ} {n : ℕ} {ω : Ω} (hω : ω ∈ halfDescent X θ σ n)
    {j : ℕ} (hj : j ≤ n) :
    walk (halfBlock X θ σ 0) j ω ≤ ∑ m ∈ Finset.range j, halfBlockMean θ σ m := by
  rw [walk_apply]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmn : m ∈ Finset.range n := Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hm) hj)
  exact Set.mem_iInter₂.1 hω m hmn

/-- Each block mean is nonpositive. -/
lemma halfBlockMean_nonpos (θ : ℝ) (hσ : 0 ≤ σ) (m : ℕ) : halfBlockMean θ σ m ≤ 0 := by
  refine div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos fun p _ => ?_) (by norm_num)
  have hp2 : 2 ≤ ((p : Nat.Primes) : ℕ) := p.2.two_le
  have hu0 : (0 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 + σ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hu1 : (((p : Nat.Primes) : ℕ) : ℝ) ^ (-(1 / 2 + σ)) < 1 :=
    rpow_neg_half_add_lt_one hp2 hσ
  exact Real.log_nonpos (by nlinarith) (by nlinarith)

/-- **The running sum of the means is at most `-U/2`.**  Each `log(1-u²) ≤ -u²`, and the blocks
telescope to the primes between the two cutoffs. -/
lemma sum_halfBlockMean_le (hσ : 0 ≤ σ) (k n : ℕ) :
    ∑ m ∈ Finset.range n, halfBlockMean (k : ℝ) σ m
      ≤ -((∑ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut ((k + n : ℕ) : ℝ)),
            ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 2) := by
  have hbridge := sum_primesIco_eq_sum_blocks (k : ℝ) n
    (fun p => Real.log (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2))
  have hbridge2 := sum_primesIco_eq_sum_blocks (k : ℝ) n
    (fun p => ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)
  rw [show (⌊blockScale (k : ℝ) 0⌋₊ + 1) = scaleCut (k : ℝ) from rfl,
    show (⌊blockScale (k : ℝ) n⌋₊ + 1) = scaleCut ((k + n : ℕ) : ℝ) from by
      rw [← scaleCut_add]; congr 1; push_cast; ring] at hbridge hbridge2
  have hsum : ∑ m ∈ Finset.range n, halfBlockMean (k : ℝ) σ m
      = (∑ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut ((k + n : ℕ) : ℝ)),
          Real.log (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2)) / 2 := by
    simp only [halfBlockMean]
    rw [← Finset.sum_div, ← hbridge]
  rw [hsum, hbridge2]
  have hterm : ∀ p ∈ primesIco (scaleCut (k : ℝ)) (scaleCut ((k + n : ℕ) : ℝ)),
      Real.log (1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ -(((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hu0 : (0 : ℝ) < (p : ℝ) ^ (-(1 / 2 + σ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hpp.pos) _
    have hu1 : (p : ℝ) ^ (-(1 / 2 + σ)) < 1 := rpow_neg_half_add_lt_one hpp.two_le hσ
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 by
      nlinarith)
    linarith
  have hle := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib] at hle
  linarith

end DescentEvent

/-! ### Independence across a prime cut, for the weight `‖F(σ+ih)‖²`

The events the first moment factorises — the box and the descent below the cut, the tube and the
level event above it — are all conditions on the walk, hence functions of the values at the
primes of one range.  `RMF.primeAlgebra` names that σ-algebra, and `RMF.setIntegral_normSq_split₂`
is the independence statement in those terms. -/

section Algebra

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The σ-algebra of the values at the primes of `[a, b)`.** -/
@[reducible] noncomputable def primeAlgebra (X : ℕ → Ω → ℂ) (a b : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (fun p : ↥(primesIco a b) => X (p : ℕ) ω)) inferInstance

lemma primeAlgebra_le (hX : IsRademacherPrimeValues X μ) (a b : ℕ) :
    primeAlgebra X a b ≤ ‹MeasurableSpace Ω› :=
  (measurable_primeTuple hX (primesIco a b) fun _ hp => prime_of_mem_primesIco hp).comap_le

lemma measurableSet_of_primeAlgebra (hX : IsRademacherPrimeValues X μ) {a b : ℕ} {A : Set Ω}
    (hA : MeasurableSet[primeAlgebra X a b] A) : MeasurableSet A :=
  primeAlgebra_le hX a b _ hA

omit [MeasurableSpace Ω] in
/-- Each value in the range is measurable for the range's algebra. -/
lemma measurable_primeAlgebra_apply {a b p : ℕ} (hp : p ∈ primesIco a b) :
    Measurable[primeAlgebra X a b] (X p) := by
  have hbase : Measurable[primeAlgebra X a b]
      (fun ω => (fun q : ↥(primesIco a b) => X (q : ℕ) ω)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (⟨p, hp⟩ : ↥(primesIco a b))).comp hbase

omit [MeasurableSpace Ω] in
/-- The blocks below `n` at offset `θ` sit inside the primes between the two cutoffs. -/
lemma mem_primesIco_of_mem_primeBlockSub_range {θ : ℝ} {n m : ℕ} (hm : m < n) {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    ((p : ℕ)) ∈ primesIco (scaleCut θ) (scaleCut (θ + n)) := by
  classical
  have hmem : p ∈ (Finset.range n).biUnion (primeBlockSub θ) :=
    Finset.mem_biUnion.2 ⟨m, Finset.mem_range.2 hm, hp⟩
  rw [biUnion_primeBlockSub_eq_sdiff, primesBelowSub_sdiff] at hmem
  rw [mem_primesIcoSub] at hmem
  exact mem_primesIco.2 ⟨p.2, by simpa [scaleCut] using hmem.1, by
    have : (p : ℕ) < ⌊blockScale θ n⌋₊ + 1 := hmem.2
    rwa [← scaleCut_add] at this⟩

omit [MeasurableSpace Ω] in
/-- **The walk is measurable for the range's algebra**: it is literally the sum of the local
logarithms at the primes of the range. -/
lemma measurable_primeAlgebra_walk (θ σ h : ℝ) {n j : ℕ} (hj : j ≤ n) :
    Measurable[primeAlgebra X (scaleCut θ) (scaleCut (θ + n))] (walk (halfBlock X θ σ h) j) := by
  rw [funext (walk_apply (halfBlock X θ σ h) j)]
  refine Finset.measurable_sum _ fun m hm => ?_
  refine Finset.measurable_sum _ fun p hp => ?_
  exact (measurable_localLogAdd _).comp (measurable_primeAlgebra_apply
    (mem_primesIco_of_mem_primeBlockSub_range (lt_of_lt_of_le (Finset.mem_range.1 hm) hj) hp))

/-- `‖F_{[a,b)}(s)‖²` as a function of the values at the primes of `[a, b)`. -/
noncomputable def normSqPoly (S : Finset ℕ) (s : ℂ) (v : ↥S → ℂ) : ℝ := ‖primePoly S s v‖ ^ 2

lemma measurable_normSqPoly (S : Finset ℕ) (s : ℂ) : Measurable (normSqPoly S s) :=
  ((continuous_primePoly S s).norm.pow 2).measurable

omit [MeasurableSpace Ω] in
lemma normSqPoly_primesIco (a b : ℕ) (s : ℂ) (ω : Ω) :
    normSqPoly (primesIco a b) s (fun p => X (p : ℕ) ω)
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ 2 := by
  rw [normSqPoly, primePoly_primesIco]

/-- **The second moment of a product event factorises across a cut.** -/
theorem setIntegral_normSq_split₂ (hX : IsRademacherPrimeValues X μ) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) {s : ℂ} {A B : Set Ω} (hA : MeasurableSet[primeAlgebra X a b] A)
    (hB : MeasurableSet[primeAlgebra X b c] B) :
    (∫ ω in A ∩ B, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c s ω‖
        ^ 2 ∂μ)
      = (∫ ω in A, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖
            ^ 2 ∂μ)
        * ∫ ω in B, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c s ω‖
            ^ 2 ∂μ := by
  classical
  obtain ⟨T₁, hT₁, rfl⟩ := hA
  obtain ⟨T₂, hT₂, rfl⟩ := hB
  rw [show (fun (ω : Ω) (p : ↥(primesIco a b)) => X (p : ℕ) ω) ⁻¹' T₁
      = {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} from rfl,
    show (fun (ω : Ω) (p : ↥(primesIco b c)) => X (p : ℕ) ω) ⁻¹' T₂
      = {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} from rfl]
  have hmeas₁ : MeasurableSet {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} :=
    (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT₁
  have hmeas₂ : MeasurableSet {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} :=
    (measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp) hT₂
  have hsplit := integral_mul_split_Ico hX
    ((measurable_normSqPoly (primesIco a b) s).indicator hT₁)
    ((measurable_normSqPoly (primesIco b c) s).indicator hT₂)
  rw [← integral_indicator (hmeas₁.inter hmeas₂), ← integral_indicator hmeas₁,
    ← integral_indicator hmeas₂]
  have e1 : (∫ ω, Set.indicator ({ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
          ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂})
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c s ω‖
          ^ 2) ω ∂μ)
      = ∫ ω, Set.indicator T₁ (normSqPoly (primesIco a b) s) (fun p => X (p : ℕ) ω)
          * Set.indicator T₂ (normSqPoly (primesIco b c) s) (fun p => X (p : ℕ) ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    by_cases h₁ : (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁
    · by_cases h₂ : (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂
      · have hmem : ω ∈ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
            ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := ⟨h₁, h₂⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h₁, Set.indicator_of_mem h₂,
          normSqPoly_primesIco, normSqPoly_primesIco,
          normSq_randomEulerProductIco_split hab hbc]
      · have hnot : ω ∉ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
            ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := fun hc => h₂ hc.2
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₂,
          Set.indicator_of_mem h₁, mul_zero]
    · have hnot : ω ∉ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
          ∩ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := fun hc => h₁ hc.1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₁, zero_mul]
  have e2 : (∫ ω, Set.indicator {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁}
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖
          ^ 2) ω ∂μ)
      = ∫ ω, Set.indicator T₁ (normSqPoly (primesIco a b) s) (fun p => X (p : ℕ) ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    by_cases h₁ : (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁
    · have hmem : ω ∈ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} := h₁
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h₁, normSqPoly_primesIco]
    · have hnot : ω ∉ {ω | (fun p : ↥(primesIco a b) => X (p : ℕ) ω) ∈ T₁} := h₁
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₁]
  have e3 : (∫ ω, Set.indicator {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂}
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c s ω‖
          ^ 2) ω ∂μ)
      = ∫ ω, Set.indicator T₂ (normSqPoly (primesIco b c) s) (fun p => X (p : ℕ) ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    by_cases h₂ : (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂
    · have hmem : ω ∈ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := h₂
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h₂, normSqPoly_primesIco]
    · have hnot : ω ∉ {ω | (fun p : ↥(primesIco b c) => X (p : ℕ) ω) ∈ T₂} := h₂
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem h₂]
  rw [e1, e2, e3]
  exact hsplit

end Algebra

/-! ### The box

`L(k,h)`'s first part asks `|log‖F_{k,k+j}(σ+ih)‖| ≤ C₁` for `1 ≤ j ≤ j₀`.  Both tails are
Markov against the two first moments of `RMF.integral_exp_log_range_le` and
`RMF.integral_exp_neg_log_range_le`, and `C₁` is chosen after `j₀`. -/

section Box

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h : ℝ}

/-- `|log‖1 + zw‖| ≤ 2u` when `‖z‖ ≤ 1` and `‖w‖ ≤ u ≤ 1/2`. -/
private lemma abs_log_norm_one_add_mul_le {z w : ℂ} (hz : ‖z‖ ≤ 1) {u : ℝ} (hu : ‖w‖ ≤ u)
    (hu0 : 0 ≤ u) (hu2 : u ≤ 1 / 2) : |Real.log ‖1 + z * w‖| ≤ 2 * u := by
  have hzw : ‖z * w‖ ≤ u := by
    rw [norm_mul]
    nlinarith [norm_nonneg z, norm_nonneg w]
  have hup : ‖1 + z * w‖ ≤ 1 + u := by
    calc ‖1 + z * w‖ ≤ ‖(1 : ℂ)‖ + ‖z * w‖ := norm_add_le _ _
      _ ≤ 1 + u := by rw [norm_one]; linarith
  have hlo : 1 - u ≤ ‖1 + z * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(z * w))
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hpos : (0 : ℝ) < ‖1 + z * w‖ := lt_of_lt_of_le h1u hlo
  rw [abs_le]
  constructor
  · have hinv : Real.log (1 - u)⁻¹ ≤ (1 - u)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at hinv
    have hfrac : (1 - u)⁻¹ - 1 ≤ 2 * u := by
      rw [inv_eq_one_div, div_sub' (by linarith), div_le_iff₀ h1u]
      nlinarith
    have := Real.log_le_log h1u hlo
    linarith
  · have := Real.log_le_log hpos hup
    have hlog : Real.log (1 + u) ≤ u := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + u)]
    linarith

/-- **The two-exponent weight is integrable.** -/
lemma integrable_exp_pair (hX : IsRademacherPrimeValues X μ) (ha5 : 5 ≤ a) (hσ : 0 ≤ σ)
    (l₁ l₂ : ℝ) :
    Integrable (fun ω => Real.exp (l₁ * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
        + l₂ * Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)) μ := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (l₁ * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
      + l₂ * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖)) μ := by
    have hm0 := (hf.aemeasurable_randomEulerProductIco a b (shiftLine σ 0)).norm
    have hmh := (hf.aemeasurable_randomEulerProductIco a b (shiftLine σ h)).norm
    exact (((hmh.log.const_mul l₁).add (hm0.log.const_mul l₂)).exp).aestronglyMeasurable
  refine (memLp_top_of_bound hmeas
    (Real.exp ((2 * |l₁| + 2 * |l₂|)
      * ∑ p ∈ primesIco a b, (p : ℝ) ^ (-(1 / 2 + σ)))) ?_).integrable le_top
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
  have hS5 : ∀ p ∈ primesIco a b, 5 ≤ p := by
    intro p hp
    have := (mem_primesIco.1 hp).2.1
    omega
  have hSp : ∀ p ∈ primesIco a b, p.Prime := fun p hp => prime_of_mem_primesIco hp
  have hbnd : ∀ p ∈ primesIco a b, ∀ t : ℝ,
      |Real.log ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ t)‖| ≤ 2 * (p : ℝ) ^ (-(1 / 2 + σ)) := by
    intro p hp t
    refine abs_log_norm_one_add_mul_le (hω p hp) (le_of_eq ?_)
      (Real.rpow_nonneg (by positivity) _) (rpow_neg_half_add_le_half (hS5 p hp) hσ)
    exact norm_cpow_neg_shiftLine (hSp p hp).pos σ t
  have hpos : ∀ (t : ℝ), ∀ p ∈ primesIco a b, 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ t)‖ := by
    intro t p hp
    refine norm_one_add_mul_pos_of_le_one (hω p hp) ?_
    rw [norm_cpow_neg_shiftLine (hSp p hp).pos]
    have := rpow_neg_half_add_le_half (hS5 p hp) hσ
    linarith
  have hexp : ∀ t : ℝ, Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ t) ω‖
      = ∑ p ∈ primesIco a b, Real.log ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ t)‖ := by
    intro t
    simp only [randomEulerProductIco_sqfree_eq, norm_prod]
    exact Real.log_prod (fun p hp => ne_of_gt (hpos t p hp))
  rw [Real.norm_eq_abs, hexp, hexp, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have h1 := hbnd p hp h
  have h2 := hbnd p hp 0
  rw [abs_le] at h1 h2
  have hl1 := abs_nonneg l₁
  have hl2 := abs_nonneg l₂
  have hu0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 + σ)) := Real.rpow_nonneg (by positivity) _
  rcases abs_cases l₁ with ⟨he₁, _⟩ | ⟨he₁, _⟩ <;> rcases abs_cases l₂ with ⟨he₂, _⟩ | ⟨he₂, _⟩ <;>
    rw [he₁, he₂] <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- Markov's inequality, in real form. -/
private lemma measureReal_ge_le_integral_div [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg0 : ∀ ω, 0 ≤ g ω) (hgi : Integrable g μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ g ω} ≤ (∫ ω, g ω ∂μ) / c := by
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hg0) hgi c
  rw [le_div_iff₀ hc]
  linarith

/-- **The upper tail of the block walk.**  Markov against `E‖F‖ ≤ e^{U/2}`. -/
lemma measureReal_walk_ge_le (hX : IsRademacherPrimeValues X μ) {k j : ℕ} (hk : 20 ≤ k)
    (hσ : 0 ≤ σ) (C : ℝ) :
    μ.real {ω | C ≤ walk (halfBlock X (k : ℝ) σ h) j ω} ≤ Real.exp (((j : ℝ) + 1) / 2 - C) := by
  haveI := hX.isProbabilityMeasure
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcast : ((k : ℝ) + (j : ℝ)) = ((k + j : ℕ) : ℝ) := by push_cast; ring
  have ha5 : 5 ≤ scaleCut (k : ℝ) := five_le_scaleCut (by linarith)
  set A : ℕ := scaleCut (k : ℝ) with hA_def
  set B : ℕ := scaleCut ((k : ℝ) + (j : ℝ)) with hB_def
  set g : Ω → ℝ := fun ω => Real.exp (1 * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) A B (shiftLine σ h) ω‖
      + 0 * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) A B (shiftLine σ 0) ω‖) with hg_def
  have hae : μ.real {ω | C ≤ walk (halfBlock X (k : ℝ) σ h) j ω}
      = μ.real {ω | Real.exp C ≤ g ω} := by
    refine measureReal_congr ?_
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw A B] with ω hω
    have hwalk := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) (k : ℝ) σ h j hσ hω
    rw [← hA_def, ← hB_def] at hwalk
    have hiff : (Real.exp C ≤ g ω) ↔ (C ≤ walk (halfBlock X (k : ℝ) σ h) j ω) := by
      simp only [hg_def, one_mul, zero_mul, add_zero, Real.exp_le_exp, hwalk]
    exact propext hiff.symm
  rw [hae]
  have hbound := measureReal_ge_le_integral_div (μ := μ) (g := g)
    (fun ω => (Real.exp_nonneg _)) (integrable_exp_pair hX ha5 hσ 1 0) (Real.exp_pos C)
  refine le_trans hbound ?_
  have hUle : (∑ p ∈ primesIco A B, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ (j : ℝ) + 1 := by
    rw [hA_def, hB_def, hcast]
    have := sum_sq_rpow_neg_primesIco_le (σ := σ) hk (Nat.le_add_right k j) hσ
    push_cast at this ⊢
    linarith
  have hnum : (∫ ω, g ω ∂μ) ≤ Real.exp (((j : ℝ) + 1) / 2) := by
    refine le_trans (integral_exp_log_range_le hX ha5 hσ) (Real.exp_le_exp.2 ?_)
    linarith
  rw [Real.exp_sub, div_le_div_iff_of_pos_right (Real.exp_pos C)]
  exact hnum

/-- **The lower tail of the block walk.**  Markov against `E‖F‖^{-1} ≤ e^{12U}`. -/
lemma measureReal_walk_le_neg_le (hX : IsRademacherPrimeValues X μ) {k j : ℕ} (hk : 20 ≤ k)
    (hσ : 0 ≤ σ) (C : ℝ) :
    μ.real {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C}
      ≤ Real.exp (12 * ((j : ℝ) + 1) - C) := by
  haveI := hX.isProbabilityMeasure
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcast : ((k : ℝ) + (j : ℝ)) = ((k + j : ℕ) : ℝ) := by push_cast; ring
  have ha40 : 40000 ≤ scaleCut (k : ℝ) := by
    have h1 : (100000000000000 : ℕ) ≤ scaleCut (k : ℝ) := pow_fourteen_le_scaleCut hkR
    omega
  have ha5 : 5 ≤ scaleCut (k : ℝ) := by omega
  set A : ℕ := scaleCut (k : ℝ) with hA_def
  set B : ℕ := scaleCut ((k : ℝ) + (j : ℝ)) with hB_def
  set g : Ω → ℝ := fun ω => Real.exp (-1 * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) A B (shiftLine σ h) ω‖
      + 0 * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) A B (shiftLine σ 0) ω‖) with hg_def
  have hae : μ.real {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C}
      = μ.real {ω | Real.exp C ≤ g ω} := by
    refine measureReal_congr ?_
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw A B] with ω hω
    have hwalk := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) (k : ℝ) σ h j hσ hω
    rw [← hA_def, ← hB_def] at hwalk
    have hiff : (Real.exp C ≤ g ω) ↔ (walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C) := by
      simp only [hg_def, neg_one_mul, zero_mul, add_zero, Real.exp_le_exp, hwalk]
      constructor <;> intro hle <;> linarith
    exact propext hiff.symm
  rw [hae]
  have hbound := measureReal_ge_le_integral_div (μ := μ) (g := g)
    (fun ω => (Real.exp_nonneg _)) (integrable_exp_pair hX ha5 hσ (-1) 0) (Real.exp_pos C)
  refine le_trans hbound ?_
  have hUle : (∑ p ∈ primesIco A B, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ≤ (j : ℝ) + 1 := by
    rw [hA_def, hB_def, hcast]
    have := sum_sq_rpow_neg_primesIco_le (σ := σ) hk (Nat.le_add_right k j) hσ
    push_cast at this ⊢
    linarith
  have hU0 : (0 : ℝ) ≤ ∑ p ∈ primesIco A B, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hnum : (∫ ω, g ω ∂μ) ≤ Real.exp (12 * ((j : ℝ) + 1)) := by
    refine le_trans (integral_exp_neg_log_range_le hX ha40 hσ) (Real.exp_le_exp.2 ?_)
    linarith
  rw [Real.exp_sub, div_le_div_iff_of_pos_right (Real.exp_pos C)]
  exact hnum

/-- **The box complement is small.**  A union bound over the `j₀` depths, each tail by Markov. -/
lemma measureReal_compl_halfBox_le (hX : IsRademacherPrimeValues X μ) {k j₀ : ℕ} (hk : 20 ≤ k)
    (hσ : 0 ≤ σ) {C₁ : ℝ} :
    μ.real (barrierEvent (halfBlock X (k : ℝ) σ h) j₀ (fun _ => -C₁) (fun _ => C₁))ᶜ
      ≤ 2 * (j₀ : ℝ) * Real.exp (12 * ((j₀ : ℝ) + 1) - C₁) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hsub : (barrierEvent (halfBlock X (k : ℝ) σ h) j₀ (fun _ => -C₁) (fun _ => C₁))ᶜ
      ⊆ ⋃ j ∈ Finset.Icc 1 j₀, ({ω | C₁ ≤ walk (halfBlock X (k : ℝ) σ h) j ω}
          ∪ {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C₁}) := by
    intro ω hω
    by_contra hcon
    refine hω fun j hj1 hj2 => ?_
    have hnot : ω ∉ ({ω | C₁ ≤ walk (halfBlock X (k : ℝ) σ h) j ω}
        ∪ {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C₁}) := fun hmem =>
      hcon (Set.mem_iUnion₂.2 ⟨j, Finset.mem_Icc.2 ⟨hj1, hj2⟩, hmem⟩)
    rw [Set.mem_union] at hnot
    push Not at hnot
    exact Set.mem_Icc.2 ⟨le_of_lt (not_le.1 hnot.2), le_of_lt (not_le.1 hnot.1)⟩
  calc μ.real (barrierEvent (halfBlock X (k : ℝ) σ h) j₀ (fun _ => -C₁) (fun _ => C₁))ᶜ
      ≤ μ.real (⋃ j ∈ Finset.Icc 1 j₀, ({ω | C₁ ≤ walk (halfBlock X (k : ℝ) σ h) j ω}
          ∪ {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C₁})) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ j ∈ Finset.Icc 1 j₀, μ.real ({ω | C₁ ≤ walk (halfBlock X (k : ℝ) σ h) j ω}
          ∪ {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C₁}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 j₀, 2 * Real.exp (12 * ((j₀ : ℝ) + 1) - C₁) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjle : (j : ℝ) ≤ (j₀ : ℝ) := by
          have := (Finset.mem_Icc.1 hj).2
          exact_mod_cast this
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have h1 := measureReal_walk_ge_le (h := h) hX hk hσ C₁ (j := j)
        have h2 := measureReal_walk_le_neg_le (h := h) hX hk hσ C₁ (j := j)
        have e1 : Real.exp (((j : ℝ) + 1) / 2 - C₁)
            ≤ Real.exp (12 * ((j₀ : ℝ) + 1) - C₁) := Real.exp_le_exp.2 (by linarith)
        have e2 : Real.exp (12 * ((j : ℝ) + 1) - C₁)
            ≤ Real.exp (12 * ((j₀ : ℝ) + 1) - C₁) := Real.exp_le_exp.2 (by linarith)
        have hun := measureReal_union_le (μ := μ)
          {ω | C₁ ≤ walk (halfBlock X (k : ℝ) σ h) j ω}
          {ω | walk (halfBlock X (k : ℝ) σ h) j ω ≤ -C₁}
        linarith
    _ = 2 * (j₀ : ℝ) * Real.exp (12 * ((j₀ : ℝ) + 1) - C₁) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp only [nsmul_eq_mul, Nat.add_sub_cancel]
        ring

/-- `e^{-(n+1)} ≤ 2^{-(n+1)}`. -/
private lemma exp_neg_le_half_pow (n : ℕ) : Real.exp (-((n : ℝ) + 1)) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  have he : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have hcast : -((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) * (-1 : ℝ) := by push_cast; ring
  rw [hcast, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) he (n + 1)

/-- **The first `j₀` scales carry a constant share of the weight.**

On the box the block product is at least `e^{-C₁}` in modulus, and the box meets the descent
event in probability at least `2^{-j₀-1}`: the descent has probability at least `2^{-j₀}` by
symmetry, and `C₁` is large enough that the box complement costs at most half of that. -/
theorem le_setIntegral_halfBox_halfDescent (hX : IsRademacherPrimeValues X μ) {k j₀ : ℕ}
    (hk : 20 ≤ k) (hσ : 0 ≤ σ) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : 12 * ((j₀ : ℝ) + 1) + Real.log (2 * (j₀ : ℝ) + 2) + ((j₀ : ℝ) + 1) ≤ C₁) :
    Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1)
      ≤ ∫ ω in barrierEvent (halfBlock X (k : ℝ) σ h) j₀ (fun _ => -C₁) (fun _ => C₁)
            ∩ halfDescent X (k : ℝ) σ j₀,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + (j₀ : ℝ))) (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set Box : Set Ω := barrierEvent (halfBlock X (k : ℝ) σ h) j₀ (fun _ => -C₁) (fun _ => C₁)
    with hBox_def
  set A₁ : Set Ω := halfDescent X (k : ℝ) σ j₀ with hA₁_def
  have hBoxm : MeasurableSet Box :=
    measurableSet_barrierEvent (measurable_halfBlock hX (k : ℝ) σ h) _ _ _
  have hA₁m : MeasurableSet A₁ := measurableSet_halfDescent hX (k : ℝ) j₀
  -- the box complement is at most half of the descent's probability
  have hbox := measureReal_compl_halfBox_le (h := h) (j₀ := j₀) hX hk hσ (C₁ := C₁)
  have hsmall : 2 * (j₀ : ℝ) * Real.exp (12 * ((j₀ : ℝ) + 1) - C₁) ≤ (1 / 2 : ℝ) ^ (j₀ + 1) := by
    have hj0 : (0 : ℝ) ≤ (j₀ : ℝ) := Nat.cast_nonneg j₀
    have hexp : Real.exp (12 * ((j₀ : ℝ) + 1) - C₁)
        ≤ Real.exp (-Real.log (2 * (j₀ : ℝ) + 2)) * Real.exp (-((j₀ : ℝ) + 1)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hlog : Real.exp (-Real.log (2 * (j₀ : ℝ) + 2)) = 1 / (2 * (j₀ : ℝ) + 2) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
    rw [hlog] at hexp
    have hfrac : 2 * (j₀ : ℝ) * (1 / (2 * (j₀ : ℝ) + 2)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      linarith
    calc 2 * (j₀ : ℝ) * Real.exp (12 * ((j₀ : ℝ) + 1) - C₁)
        ≤ 2 * (j₀ : ℝ) * (1 / (2 * (j₀ : ℝ) + 2) * Real.exp (-((j₀ : ℝ) + 1))) := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (2 * (j₀ : ℝ) * (1 / (2 * (j₀ : ℝ) + 2))) * Real.exp (-((j₀ : ℝ) + 1)) := by ring
      _ ≤ 1 * Real.exp (-((j₀ : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)
      _ ≤ (1 / 2 : ℝ) ^ (j₀ + 1) := by
          rw [one_mul]
          exact exp_neg_le_half_pow j₀
  -- the descent event has probability at least `2^{-j₀}`
  have hdesc : (1 / 2 : ℝ) ^ j₀ ≤ μ.real A₁ := by
    have h := le_measure_halfDescent (σ := σ) hX (k : ℝ) hσ j₀
    have htor := ENNReal.toReal_mono (measure_ne_top μ A₁) h
    simpa [measureReal_def, ENNReal.toReal_pow] using htor
  -- hence the intersection has probability at least `2^{-j₀-1}`
  have hcover : A₁ ⊆ (Box ∩ A₁) ∪ Boxᶜ := by
    intro ω hω
    by_cases hb : ω ∈ Box
    · exact Or.inl ⟨hb, hω⟩
    · exact Or.inr hb
  have hinter : (1 / 2 : ℝ) ^ (j₀ + 1) ≤ μ.real (Box ∩ A₁) := by
    have h1 := measureReal_mono (μ := μ) hcover (measure_ne_top μ _)
    have h2 := measureReal_union_le (μ := μ) (Box ∩ A₁) Boxᶜ
    have hpow : (1 / 2 : ℝ) ^ (j₀ + 1) + (1 / 2 : ℝ) ^ (j₀ + 1) = (1 / 2 : ℝ) ^ j₀ := by
      rw [pow_succ]
      ring
    linarith
  -- on the box the block product is at least `e^{-C₁}`
  have hlow : ∀ᵐ ω ∂μ, ω ∈ Box ∩ A₁ → Real.exp (-(2 * C₁))
      ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + (j₀ : ℝ))) (shiftLine σ h) ω‖ ^ 2 := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw
      (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + (j₀ : ℝ)))] with ω hω hmem
    have hwalk := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) (k : ℝ) σ h j₀ hσ hω
    have hposω : 0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + (j₀ : ℝ))) (shiftLine σ h) ω‖ := by
      rw [randomEulerProductIco_sqfree_eq, norm_prod]
      refine Finset.prod_pos fun p hp => ?_
      have hpp := prime_of_mem_primesIco hp
      have hp5 : 5 ≤ (p : ℕ) := by
        have h1 := (mem_primesIco.1 hp).2.1
        have h2 : 5 ≤ scaleCut (k : ℝ) :=
          five_le_scaleCut (by exact_mod_cast le_trans (by norm_num) hk)
        omega
      refine norm_one_add_mul_pos_of_le_one (hω p hp) ?_
      rw [norm_cpow_neg_shiftLine hpp.pos]
      have := rpow_neg_half_add_le_half hp5 hσ
      linarith
    have hge : -C₁ ≤ walk (halfBlock X (k : ℝ) σ h) j₀ ω := by
      rcases Nat.eq_zero_or_pos j₀ with rfl | hj0
      · simp only [walk_apply, Finset.range_zero, Finset.sum_empty]
        linarith
      · exact (Set.mem_Icc.1 (hmem.1 j₀ hj0 le_rfl)).1
    have hnorm : Real.exp (-C₁)
        ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) (scaleCut ((k : ℝ) + (j₀ : ℝ))) (shiftLine σ h) ω‖ := by
      rw [← Real.exp_log hposω]
      exact Real.exp_le_exp.2 (by rw [hwalk]; exact hge)
    calc Real.exp (-(2 * C₁)) = Real.exp (-C₁) ^ 2 := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hnorm 2
  -- and the set integral follows
  have hint : IntegrableOn (fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k : ℝ))
      (scaleCut ((k : ℝ) + (j₀ : ℝ))) (shiftLine σ h) ω‖ ^ 2) (Box ∩ A₁) μ :=
    (hf.integrable_norm_randomEulerProductIco_sq _ _ _).integrableOn
  have hconst : (∫ _ω in Box ∩ A₁, Real.exp (-(2 * C₁)) ∂μ)
      ≤ ∫ ω in Box ∩ A₁, ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k : ℝ))
          (scaleCut ((k : ℝ) + (j₀ : ℝ))) (shiftLine σ h) ω‖ ^ 2 ∂μ := by
    refine setIntegral_mono_ae_restrict (integrableOn_const (measure_ne_top μ _)) hint ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' (hBoxm.inter hA₁m)]
    exact hlow
  rw [setIntegral_const, smul_eq_mul] at hconst
  calc Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1)
      ≤ Real.exp (-(2 * C₁)) * μ.real (Box ∩ A₁) :=
        mul_le_mul_of_nonneg_left hinter (Real.exp_nonneg _)
    _ = μ.real (Box ∩ A₁) * Real.exp (-(2 * C₁)) := by ring
    _ ≤ _ := hconst

end Box

/-! ### The tilt of a block product

Harper's Proposition 5 bounds the measure tilted by the **full** product below `y`.  The first
moment integrates the **block** product over `[b, y)`.  For an event that is a function of the
values at the primes of `[b, y)` the two agree: the primes below `b` factor out of both sides of
`RMF.IsRademacherRMF.setIntegral_normSq_eq` and cancel, their moment being at least one. -/

section Tilt

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- **The algebra of a range grows with the range.**  The tuple over a sub-range is a measurable
function of the tuple over the range. -/
lemma primeAlgebra_mono {a a' b b' : ℕ} (h1 : a ≤ a') (h2 : b' ≤ b) :
    primeAlgebra X a' b' ≤ primeAlgebra X a b := by
  have hsub : ∀ p ∈ primesIco a' b', p ∈ primesIco a b := fun p hp => by
    obtain ⟨hpp, hlo, hhi⟩ := mem_primesIco.1 hp
    exact mem_primesIco.2 ⟨hpp, le_trans h1 hlo, lt_of_lt_of_le hhi h2⟩
  set res : (↥(primesIco a b) → ℂ) → (↥(primesIco a' b') → ℂ) :=
    fun v p => v ⟨p.1, hsub p.1 p.2⟩ with hres_def
  have hresm : Measurable res := measurable_pi_lambda _ fun p => measurable_pi_apply _
  have hcomp : (fun ω => (fun p : ↥(primesIco a' b') => X (p : ℕ) ω))
      = res ∘ (fun ω => (fun p : ↥(primesIco a b) => X (p : ℕ) ω)) := rfl
  rw [primeAlgebra, primeAlgebra, hcomp, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hresm.comap_le

omit [MeasurableSpace Ω] in
/-- **The barrier event is measurable for the algebra of any range containing its blocks.** -/
lemma measurableSet_primeAlgebra_barrierEvent (θ σ h : ℝ) {n b : ℕ}
    (hb : scaleCut (θ + n) ≤ b) (u v : ℕ → ℝ) :
    MeasurableSet[primeAlgebra X (scaleCut θ) b] (barrierEvent (halfBlock X θ σ h) n u v) := by
  have hrw : barrierEvent (halfBlock X θ σ h) n u v
      = ⋂ j ∈ Set.Icc 1 n, (walk (halfBlock X θ σ h) j) ⁻¹' (Set.Icc (u j) (v j)) := by
    ext ω
    simp only [barrierEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun hω j hj => hω j hj.1 hj.2, fun hω j h1 h2 => hω j ⟨h1, h2⟩⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j hj => ?_
  exact ((measurable_primeAlgebra_walk θ σ h hj.2).mono
    (primeAlgebra_mono le_rfl hb) le_rfl) measurableSet_Icc

/-- The second moment of a block product is at least one. -/
lemma one_le_integral_normSq_Ico (hX : IsRademacherPrimeValues X μ) (a b : ℕ) (s : ℂ) :
    (1 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖
      ^ 2 ∂μ := by
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  rw [hf.integral_norm_randomEulerProductIco_sq a b s]
  exact Finset.one_le_prod fun p _ => le_add_of_nonneg_right (sq_nonneg _)

/-- **The tilt of a block product.**  For an event that is a function of the values at the primes
of `[b, y)`, the block-product integral over it is the tilted measure times the block-product
moment — the primes below `b` cancel between the two sides. -/
theorem setIntegral_normSq_eq_tilted (hX : IsRademacherPrimeValues X μ) {b y : ℕ}
    (hby : b ≤ y) {s : ℂ} (hs : 0 < s.re) {A : Set Ω}
    (hA : MeasurableSet[primeAlgebra X b y] A) :
    (∫ ω in A, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
        ^ 2 ∂μ)
      = (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ A).toReal
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
            ^ 2 ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hAm : MeasurableSet A := measurableSet_of_primeAlgebra hX hA
  have hfull := hf.setIntegral_normSq_eq y hs hAm
  have hsplitA := setIntegral_normSq_split₂ (X := X) (s := s) hX (Nat.zero_le b) hby
    (A := Set.univ) MeasurableSet.univ hA
  have hsplitU := setIntegral_normSq_split₂ (X := X) (s := s) hX (Nat.zero_le b) hby
    (A := Set.univ) MeasurableSet.univ (B := Set.univ) MeasurableSet.univ
  rw [Set.univ_inter, setIntegral_univ] at hsplitA
  rw [Set.univ_inter, setIntegral_univ, setIntegral_univ, setIntegral_univ] at hsplitU
  simp only [randomEulerProductIco_zero] at hsplitA hsplitU
  set P : ℝ := ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) b s ω‖ ^ 2 ∂μ
    with hP_def
  set Q : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
      ^ 2 ∂μ with hQ_def
  set R : ℝ := ∫ ω in A,
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖ ^ 2 ∂μ
    with hR_def
  set T : ℝ := (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ A).toReal
    with hT_def
  have hP1 : (1 : ℝ) ≤ P := by
    have hzero := one_le_integral_normSq_Ico hX 0 b s
    simpa [hP_def] using hzero
  have hkey : P * R = T * (P * Q) := by rw [← hsplitA, ← hsplitU, hfull]
  have hP0 : (0 : ℝ) < P := by linarith
  have hPR : P * R = P * (T * Q) := by rw [hkey]; ring
  exact mul_left_cancel₀ (ne_of_gt hP0) hPR

/-- **A lower bound on the tilted measure is one on the block-product integral.** -/
theorem le_setIntegral_normSq_of_le_tilted (hX : IsRademacherPrimeValues X μ) {b y : ℕ}
    (hby : b ≤ y) {s : ℂ} (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet[primeAlgebra X b y] A)
    {c : ℝ}
    (hc : c ≤ (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ A).toReal) :
    c * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
          ^ 2 ∂μ)
      ≤ ∫ ω in A, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
          ^ 2 ∂μ := by
  rw [setIntegral_normSq_eq_tilted hX hby hs hA]
  exact mul_le_mul_of_nonneg_right hc (integral_nonneg fun ω => by positivity)

/-- **An upper bound on the tilted measure is one on the block-product integral.** -/
theorem setIntegral_normSq_le_of_tilted_le (hX : IsRademacherPrimeValues X μ) {b y : ℕ}
    (hby : b ≤ y) {s : ℂ} (hs : 0 < s.re) {A : Set Ω} (hA : MeasurableSet[primeAlgebra X b y] A)
    {C : ℝ}
    (hC : (tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y s μ A).toReal ≤ C) :
    (∫ ω in A, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
        ^ 2 ∂μ)
      ≤ C * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b y s ω‖
          ^ 2 ∂μ := by
  rw [setIntegral_normSq_eq_tilted hX hby hs hA]
  exact mul_le_mul_of_nonneg_right hC (integral_nonneg fun ω => by positivity)

end Tilt

/-! ### Scalar bounds for the first-exceedance sum

The terms of the first-exceedance sum carry a geometric factor `e^{-i/9}` from the mixed moment
and a free-start tube factor `min(1, a'_i/√(n-i))`.  The three lemmas here are what makes the sum
converge to `O(1/√n)`: geometric sums, `i ≤ 32e^{i/32}`, and `e^{-n/32} ≤ 32/√n`. -/

section ScalarSums

/-- Partial geometric sums: `∑_{m<i} e^{-rm} ≤ (1+r)/r`, from `e^{-r} ≤ 1/(1+r)`. -/
lemma sum_exp_neg_mul_range_le {r : ℝ} (hr : 0 < r) (i : ℕ) :
    ∑ m ∈ Finset.range i, Real.exp (-(r * (m : ℝ))) ≤ (1 + r) / r := by
  have hx0 : (0 : ℝ) < Real.exp (-r) := Real.exp_pos _
  have hxle : Real.exp (-r) ≤ 1 / (1 + r) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos r) (by positivity)]
    linarith [Real.add_one_le_exp r]
  have hxlt : Real.exp (-r) < 1 := by
    refine lt_of_le_of_lt hxle ?_
    rw [div_lt_one (by positivity)]
    linarith
  have hterm : ∀ m : ℕ, Real.exp (-(r * (m : ℝ))) = Real.exp (-r) ^ m := by
    intro m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hterm]
  rw [geom_sum_eq (ne_of_lt hxlt)]
  have hpow : (0 : ℝ) ≤ Real.exp (-r) ^ i := pow_nonneg hx0.le i
  have hstep : (1 + r) / r * (Real.exp (-r) - 1) ≤ -1 := by
    have h1 : Real.exp (-r) - 1 ≤ -(r / (1 + r)) := by
      have : (1 : ℝ) / (1 + r) - 1 = -(r / (1 + r)) := by
        field_simp
        ring
      linarith
    have h2 : (1 + r) / r * (-(r / (1 + r))) = -1 := by field_simp
    calc (1 + r) / r * (Real.exp (-r) - 1) ≤ (1 + r) / r * (-(r / (1 + r))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = -1 := h2
  rw [div_le_iff_of_neg (by linarith : Real.exp (-r) - 1 < 0)]
  linarith

/-- `∑_{m<i} e^{-m} ≤ 2`, the case `r = 1`. -/
lemma sum_exp_neg_range_le (i : ℕ) : ∑ m ∈ Finset.range i, Real.exp (-(m : ℝ)) ≤ 2 := by
  have h := sum_exp_neg_mul_range_le (r := 1) one_pos i
  simp only [one_mul] at h
  norm_num at h
  exact h

/-- `i ≤ 32·e^{i/32}`, from `y ≤ e^y`. -/
lemma natCast_le_exp_div (i : ℕ) : (i : ℝ) ≤ 32 * Real.exp ((i : ℝ) / 32) := by
  have := Real.add_one_le_exp ((i : ℝ) / 32)
  linarith

/-- `e^{-n/c} ≤ c/√n` for `n ≥ 1` and `c > 0`. -/
lemma exp_neg_div_le_inv_sqrt {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) :
    Real.exp (-((n : ℝ) / c)) ≤ c / Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul_self (by linarith)] at h1
  have hsq0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hexp : Real.exp (-((n : ℝ) / c)) ≤ c / (n : ℝ) := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hE := Real.add_one_le_exp ((n : ℝ) / c)
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have h2 : c / (n : ℝ) * ((n : ℝ) / c + 1) ≤ c / (n : ℝ) * Real.exp ((n : ℝ) / c) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have h1 : c / (n : ℝ) * ((n : ℝ) / c + 1) = 1 + c / (n : ℝ) := by
      field_simp
    rw [h1] at h2
    have h3 : (0 : ℝ) ≤ c / (n : ℝ) := by positivity
    linarith
  refine le_trans hexp ?_
  exact div_le_div_of_nonneg_left hc.le hsq0 hsq

/-- **The weight of the `i`-th first-exceedance term, uniformly in `i`.**  Either `2i ≤ n`, and
the free-start tube's `1/(√(n-i)+1)` is already `≤ √2/√n`, or `2i > n`, and half of the
geometric factor pays for it through `e^{-n/36} ≤ 36/√n`. -/
lemma exceed_weight_le {n i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    Real.exp (-((i : ℝ) / 9)) * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
      ≤ 38 * ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) / Real.sqrt (n : ℝ) := by
  have hn1 : 1 ≤ n := le_trans hi1 hin
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
  have hinR : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
  have hsqn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsqni : (0 : ℝ) ≤ Real.sqrt ((n - i : ℕ) : ℝ) := Real.sqrt_nonneg _
  have he9 : Real.exp (-((i : ℝ) / 9))
      = Real.exp (-((i : ℝ) / 18)) * Real.exp (-((i : ℝ) / 18)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos : (0 : ℝ) ≤ 1 + (i : ℝ) := by linarith
  have he18 : (0 : ℝ) < Real.exp (-((i : ℝ) / 18)) := Real.exp_pos _
  rcases le_total (2 * (i : ℝ)) (n : ℝ) with hcase | hcase
  · -- `2i ≤ n`: the tube factor is already `≤ √2/√n`
    have hni : ((n : ℝ) / 2) ≤ ((n - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hin]
      linarith
    have hsq : Real.sqrt ((n : ℝ) / 2) ≤ Real.sqrt ((n - i : ℕ) : ℝ) := Real.sqrt_le_sqrt hni
    have hhalf : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) / 2) := by
      have h2 : Real.sqrt ((n : ℝ) / 2) * Real.sqrt ((n : ℝ) / 2) = (n : ℝ) / 2 :=
        Real.mul_self_sqrt (by linarith)
      have h3 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg ((n : ℝ) / 2), Real.sqrt_nonneg (n : ℝ)]
    have hden : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt ((n - i : ℕ) : ℝ) + 1 := by linarith
    have hfrac : (1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1)
        ≤ (1 + (i : ℝ)) / (Real.sqrt (n : ℝ) / 2) :=
      div_le_div_of_nonneg_left hpos (by linarith) hden
    have hkey : (1 + (i : ℝ)) / (Real.sqrt (n : ℝ) / 2)
        = 2 * (1 + (i : ℝ)) / Real.sqrt (n : ℝ) := by
      field_simp
    rw [hkey] at hfrac
    have hstep := mul_le_mul_of_nonneg_left hfrac he18.le
    rw [he9]
    have hmono : Real.exp (-((i : ℝ) / 18)) * (Real.exp (-((i : ℝ) / 18))
        * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1)))
        ≤ 1 * (Real.exp (-((i : ℝ) / 18)) * (2 * (1 + (i : ℝ)) / Real.sqrt (n : ℝ))) := by
      refine mul_le_mul ?_ hstep (by positivity) (by norm_num)
      exact Real.exp_le_one_iff.2 (by linarith)
    calc Real.exp (-((i : ℝ) / 18)) * Real.exp (-((i : ℝ) / 18))
          * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
        = Real.exp (-((i : ℝ) / 18)) * (Real.exp (-((i : ℝ) / 18))
            * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))) := by ring
      _ ≤ 1 * (Real.exp (-((i : ℝ) / 18)) * (2 * (1 + (i : ℝ)) / Real.sqrt (n : ℝ))) := hmono
      _ ≤ 38 * ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) / Real.sqrt (n : ℝ) := by
          rw [one_mul, show Real.exp (-((i : ℝ) / 18)) * (2 * (1 + (i : ℝ)) / Real.sqrt (n : ℝ))
              = 2 * ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) / Real.sqrt (n : ℝ) from by ring,
            div_le_div_iff_of_pos_right hsqn]
          nlinarith [he18.le, hpos]
  · -- `2i > n`: half the geometric factor pays for the tube
    have hfrac : (1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1) ≤ 1 + (i : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hn36 : Real.exp (-((n : ℝ) / 36)) ≤ 36 / Real.sqrt (n : ℝ) :=
      exp_neg_div_le_inv_sqrt hn1 (by norm_num)
    have hi36 : Real.exp (-((i : ℝ) / 18)) ≤ Real.exp (-((n : ℝ) / 36)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [he9]
    calc Real.exp (-((i : ℝ) / 18)) * Real.exp (-((i : ℝ) / 18))
          * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
        ≤ Real.exp (-((i : ℝ) / 18)) * (36 / Real.sqrt (n : ℝ)) * (1 + (i : ℝ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (le_trans hi36 hn36) he18.le) hfrac
            (by positivity) (by positivity)
      _ ≤ 38 * ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) / Real.sqrt (n : ℝ) := by
          rw [show Real.exp (-((i : ℝ) / 18)) * (36 / Real.sqrt (n : ℝ)) * (1 + (i : ℝ))
              = 36 * ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) / Real.sqrt (n : ℝ) from by ring,
            div_le_div_iff_of_pos_right hsqn]
          nlinarith [he18.le, hpos]

end ScalarSums

/-! ### The oscillatory sum over a range of scales

The mixed moment carries `∑_p p^{-1-2σ} cos(h log p)` over the primes of a range.  Block
by block it is `RMF.exists_abs_sum_cos_primeBlockSub_rpow_le_wide`, whose bounds decay
geometrically, so the whole range costs no more than twice the first block. -/

section Oscillation

/-- **The oscillatory sum over a range of scales.** -/
theorem exists_abs_sum_cos_primesIco_le :
    ∃ K c m₀ : ℝ, 0 < K ∧ 0 < c ∧ ∀ (τ σ θ : ℝ) (i : ℕ), 0 < τ → 0 ≤ θ → m₀ ≤ θ →
      (∀ m : ℕ, m < i → τ ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + θ) / 10))) →
      (∀ m : ℕ, m < i → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1) →
      |∑ p ∈ primesIco (scaleCut θ) (scaleCut (θ + (i : ℕ))),
          Real.cos (τ * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ)|
        ≤ 2 * K / (τ * Real.exp θ) := by
  obtain ⟨K, c, m₀, hK0, hc, H⟩ := exists_abs_sum_cos_primeBlockSub_rpow_le_wide
  refine ⟨K, c, m₀, hK0, hc, ?_⟩
  intro τ σ θ i hτ hθ hm₀ hτ2 hσ
  have hbridge := sum_primesIco_eq_sum_blocks θ i
    (fun p => Real.cos (τ * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ))
  rw [show (⌊blockScale θ 0⌋₊ + 1) = scaleCut θ from rfl,
    show (⌊blockScale θ i⌋₊ + 1) = scaleCut (θ + (i : ℕ)) from (scaleCut_add θ i).symm] at hbridge
  rw [hbridge]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ m ∈ Finset.range i,
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ K / (τ * Real.exp θ) * Real.exp (-(m : ℝ)) := by
    intro m hm
    have hmi := Finset.mem_range.1 hm
    have hb := H τ σ θ m hτ hθ (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (hτ2 m hmi) (hσ m hmi)
    refine le_trans hb (le_of_eq ?_)
    rw [Real.exp_add, Real.exp_neg]
    field_simp
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hKτ : (0 : ℝ) ≤ K / (τ * Real.exp θ) := by positivity
  calc K / (τ * Real.exp θ) * ∑ m ∈ Finset.range i, Real.exp (-(m : ℝ))
      ≤ K / (τ * Real.exp θ) * 2 := mul_le_mul_of_nonneg_left (sum_exp_neg_range_le i) hKτ
    _ = 2 * K / (τ * Real.exp θ) := by ring

end Oscillation

/-! ### The first-exceedance term

Where the real-point walk over a range has already risen above `C`, the weight `‖F(σ+ih)‖²`
integrates to at most `e^{-C/2}` times the mixed moment — Chernoff at exponent `½`, which is
where the `-U/8` of `RMF.atoms_mixed_le` comes from. -/

section Exceedance

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {a b : ℕ} {σ h : ℝ}

/-- The pointwise step of Chernoff: `N ≤ E·N·F` when `1 ≤ E·Gc` and `Gc ≤ F`. -/
private lemma chernoff_pointwise {N E F Gc : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E) (hfac : 1 ≤ E * Gc)
    (hFG : Gc ≤ F) : N ≤ E * N * F := by
  calc N = N * 1 := (mul_one N).symm
    _ ≤ N * (E * Gc) := mul_le_mul_of_nonneg_left hfac hN
    _ = E * N * Gc := by ring
    _ ≤ E * N * F := mul_le_mul_of_nonneg_left hFG (by positivity)

/-- **Chernoff at exponent `½` against the weight `‖F(σ+ih)‖²`.** -/
theorem setIntegral_normSq_gt_le (hX : IsRademacherPrimeValues X μ) (ha : 40000 ≤ a)
    (hσ : 0 ≤ σ) (C : ℝ) :
    (∫ ω in {ω | C < Real.log ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h) ω‖ ^ 2 ∂μ)
      ≤ Real.exp (-C / 2)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
              (shiftLine σ h) ω‖ ^ 2 ∂μ)
          * Real.exp ((∑ p ∈ primesIco a b,
                ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * Real.cos (h * Real.log p))
              - (∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 8
              + 2 * ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4)) := by
  have ha5 : 5 ≤ a := by omega
  haveI := hX.isProbabilityMeasure
  set S : Set Ω := {ω | C < Real.log ‖randomEulerProductIco
    (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖} with hS_def
  set G : Ω → ℝ := fun ω => Real.exp (2 * Real.log ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
    + 1 / 2 * Real.log ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) with hG_def
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const
      (measurable_norm_randomEulerProductIco hX a b (shiftLine σ 0)).log
  have hGint : Integrable G μ := integrable_exp_pair hX ha5 hσ 2 (1 / 2)
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hFint : Integrable (fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖ ^ 2) μ :=
    hf.integrable_norm_randomEulerProductIco_sq _ _ _
  -- the pointwise Chernoff bound on `S`
  have hpt : ∀ᵐ ω ∂μ, ω ∈ S → ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖ ^ 2
        ≤ Real.exp (-C / 2) * G ω := by
    filter_upwards [ae_norm_randomEulerProductIco_shift_pos hX a b ha5 hσ h] with ω hpos hmem
    have hC : C < Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖ := hmem
    have hsq : Real.exp (2 * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖)
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2 := by
      rw [show (2 : ℝ) * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
          = Real.log ‖randomEulerProductIco
              (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖
            + Real.log ‖randomEulerProductIco
              (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖ from by ring,
        Real.exp_add, Real.exp_log hpos, sq]
    have hexp : Real.exp (C / 2) ≤ Real.exp (1 / 2 * Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) :=
      Real.exp_le_exp.2 (by linarith)
    have hGeq : G ω = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h) ω‖ ^ 2
        * Real.exp (1 / 2 * Real.log ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ 0) ω‖) := by
      simp only [hG_def]
      rw [Real.exp_add, hsq]
    rw [hGeq, ← mul_assoc]
    have hfac : (1 : ℝ) ≤ Real.exp (-C / 2) * Real.exp (C / 2) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      linarith
    exact chernoff_pointwise (sq_nonneg _) (Real.exp_nonneg _) hfac hexp
  -- integrate
  have hstep : (∫ ω in S, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) a b (shiftLine σ h) ω‖ ^ 2 ∂μ)
      ≤ ∫ ω in S, Real.exp (-C / 2) * G ω ∂μ := by
    refine setIntegral_mono_ae_restrict hFint.integrableOn (hGint.const_mul _).integrableOn ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' hSm]
    exact hpt
  refine le_trans hstep ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  refine le_trans (setIntegral_le_integral hGint
    (Filter.Eventually.of_forall fun ω => Real.exp_nonneg _)) ?_
  exact integral_exp_mixed_range_le hX ha hσ

end Exceedance

/-! ### The restart

The complement of `E_>` is covered by first-exceedance events.  The `i`-th term is the tube
intersected with `{the real-point walk has passed C₂ by depth i}`, and the two factor across the
cut at `scaleCut (ϑ+i)` — but only after the tube's own constraint at depth `i` has been applied to
replace the tube above `i` by a *free-start* one, whose height `3a + (B+1)i` does not refer to
the walk. -/

section Restart

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}

/-- Harper's curvature is nonpositive. -/
lemma harperHf_nonpos (j : ℕ) : harperHf j ≤ 0 := by
  have := Real.log_natCast_nonneg j
  rw [harperHf]
  linarith

omit [MeasurableSpace Ω] in
/-- **The block family shifts**: block `m` at offset `θ + i` is block `m + i` at offset `θ`. -/
lemma halfBlock_shift (θ σ h : ℝ) (i : ℕ) :
    halfBlock X (θ + (i : ℕ)) σ h = fun m => halfBlock X θ σ h (m + i) := by
  funext m ω
  simp only [halfBlock]
  rw [primeBlockSub_add]

omit [MeasurableSpace Ω] in
/-- **The restart.**  A point of the tube lies, from depth `i` on, in the free-start tube of
height `3a + (B+1)i` and slope `B` with no curvature. -/
lemma barrierEvent_restart {θ σ h : ℝ} {n i : ℕ} {a B : ℝ} (ha : 0 ≤ a) (_hB : 0 ≤ B)
    (hi1 : 1 ≤ i) (hin : i ≤ n) :
    barrierEvent (halfBlock X θ σ h) n (fun j => -a - B * j) (fun j => a + j + harperHf j)
      ⊆ barrierEvent (halfBlock X (θ + (i : ℕ)) σ h) (n - i)
          (fun j => -(3 * a + (B + 1) * (i : ℝ)) - B * j)
          (fun j => 3 * a + (B + 1) * (i : ℝ) + j) := by
  intro ω hω j hj1 hj2
  rw [halfBlock_shift, walk_shift]
  have hij : 1 ≤ i + j := by omega
  have hijn : i + j ≤ n := by omega
  obtain ⟨hL, hU⟩ := Set.mem_Icc.1 (hω (i + j) hij hijn)
  obtain ⟨hL', hU'⟩ := Set.mem_Icc.1 (hω i hi1 hin)
  dsimp only at hL hU hL' hU'
  have hhf1 : harperHf (i + j) ≤ 0 := harperHf_nonpos _
  have hhf2 : harperHf i ≤ 0 := harperHf_nonpos _
  have hcast : ((i + j : ℕ) : ℝ) = (i : ℝ) + (j : ℝ) := by push_cast; ring
  rw [hcast] at hL hU
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  refine Set.mem_Icc.2 ⟨by nlinarith, by nlinarith⟩

omit [MeasurableSpace Ω] in
/-- The free-start tube is measurable for the algebra above the cut. -/
lemma measurableSet_primeAlgebra_restart {θ σ h : ℝ} {n i b : ℕ} (hin : i ≤ n)
    (hb : scaleCut (θ + (n : ℕ)) ≤ b) (u v : ℕ → ℝ) :
    MeasurableSet[primeAlgebra X (scaleCut (θ + (i : ℕ))) b]
      (barrierEvent (halfBlock X (θ + (i : ℕ)) σ h) (n - i) u v) := by
  refine measurableSet_primeAlgebra_barrierEvent (θ + (i : ℕ)) σ h ?_ u v
  refine le_trans (scaleCut_mono ?_) hb
  have hcast : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hin]
  rw [hcast]
  linarith

end Restart

/-! ### The exceedance factor below the restart

The `i`-th first-exceedance term splits at `scaleCut (ϑ+i)`.  Its lower factor is the
first-exceedance integral over `[c_ϑ, c_{ϑ+i})`, and this is where the geometric decay comes
from: Chernoff at exponent `½` costs `e^{-C/2}`, the mixed moment contributes `-U/8` with
`U ≥ i - 2`, and the oscillatory sum is absolutely bounded on the window. -/

section ExceedFirst

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(p^{-1/2-σ})² = p^{-1-2σ}`. -/
lemma sq_rpow_neg_half_add {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 = (p : ℝ) ^ (-1 - 2 * σ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 2, ← Real.rpow_mul hp0.le]
  congr 1
  push_cast
  ring

/-- `u⁴ ≤ u²/40000` for `u ≤ 1/200`. -/
private lemma pow_four_le_sq_div {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 200) :
    u ^ 4 ≤ u ^ 2 / 40000 := by
  have h1 : u ^ 2 ≤ 1 / 40000 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg u)
  calc u ^ 4 = u ^ 2 * u ^ 2 := by ring
    _ ≤ u ^ 2 * (1 / 40000) := h2
    _ = u ^ 2 / 40000 := by ring

/-- `h² ≤ 1` for `0 < h ≤ 1`. -/
private lemma sq_le_one_of_le_one {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) : h ^ 2 ≤ 1 := by
  nlinarith

/-- The exponent of the mixed-moment ratio is at most `2K + 1 - i/9`. -/
private lemma mixed_exponent_bound {osc U W K : ℝ} {i : ℕ} (hosc : osc ≤ 2 * K)
    (hUlo : (i : ℝ) - 2 ≤ U) (hU0 : 0 ≤ U) (hW : W ≤ U / 40000) :
    osc - U / 8 + 2 * W ≤ 2 * K + 1 - (i : ℝ) / 9 := by
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

set_option maxRecDepth 8000 in
/-- **The first-exceedance factor below the restart.** -/
theorem exists_setIntegral_exceed_first_le :
    ∃ (D : ℝ) (k₁ : ℕ), 0 < D ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t j₀ i : ℕ) (σ h C : ℝ), k₁ ≤ k → 1 ≤ j₀ → 1 ≤ i → k + j₀ + i ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → h ∈ halfWindow k →
        (∫ ω in {ω | C < walk (halfBlock X ((k : ℝ) + (j₀ : ℝ)) σ 0) i ω},
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ((k : ℝ) + (j₀ : ℝ))) (scaleCut ((k : ℝ) + (j₀ : ℝ) + (i : ℝ)))
              (shiftLine σ h) ω‖ ^ 2 ∂μ)
          ≤ Real.exp (-C / 2) * D * Real.exp (-((i : ℝ) / 9))
            * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ((k : ℝ) + (j₀ : ℝ))) (scaleCut ((k : ℝ) + (j₀ : ℝ) + (i : ℝ)))
                (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  obtain ⟨K, c, m₀, hK0, hc, HK⟩ := exists_abs_sum_cos_primesIco_le
  refine ⟨Real.exp (2 * K + 1), ⌈m₀⌉₊ + 20, Real.exp_pos _, ?_⟩
  intro X μ hX k t j₀ i σ h C hk hj₀ hi ht hσ0 hσ hwin
  obtain ⟨hwlo, hwhi⟩ := hwin
  have hσ0' : 0 ≤ σ := hσ0.le
  have hk20 : 20 ≤ k := by omega
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk20
  set ϑ : ℝ := (k : ℝ) + (j₀ : ℝ) with hϑ_def
  have hj₀R : (1 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hϑ0 : (0 : ℝ) ≤ ϑ := by rw [hϑ_def]; linarith
  have hcast₀ : ϑ = ((k + j₀ : ℕ) : ℝ) := by rw [hϑ_def]; push_cast; ring
  have hcast₁ : ϑ + (i : ℝ) = ((k + j₀ + i : ℕ) : ℝ) := by rw [hϑ_def]; push_cast; ring
  set c₀ : ℕ := scaleCut ϑ with hc₀_def
  set c₁ : ℕ := scaleCut (ϑ + (i : ℝ)) with hc₁_def
  have hc₀40 : 40000 ≤ c₀ := by
    have h1 : (100000000000000 : ℕ) ≤ scaleCut ϑ := pow_fourteen_le_scaleCut (by linarith)
    omega
  -- the set is the exceedance of the block product at the real point
  have hset : {ω | C < walk (halfBlock X ϑ σ 0) i ω}
      =ᵐ[μ] {ω | C < Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) c₀ c₁ (shiftLine σ 0) ω‖} := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw c₀ c₁] with ω hω
    have hwalk := log_norm_randomEulerProductIco_eq_walk_halfBlock (X := X) ϑ σ 0 i hσ0' hω
    have hiff : (C < Real.log ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) c₀ c₁ (shiftLine σ 0) ω‖)
        ↔ (C < walk (halfBlock X ϑ σ 0) i ω) := by rw [hwalk]
    exact propext hiff.symm
  rw [setIntegral_congr_set hset]
  refine le_trans (setIntegral_normSq_gt_le hX hc₀40 hσ0' C) ?_
  -- the three ingredients
  have hUlo : (i : ℝ) - 2 ≤ ∑ p ∈ primesIco c₀ c₁, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := by
    have hσn : σ * Real.exp (((k + j₀ + i : ℕ)) : ℝ) ≤ 1 / 2 := by
      have h1 : Real.exp (((k + j₀ + i : ℕ)) : ℝ) ≤ Real.exp ((t : ℝ) + 1) := by
        refine Real.exp_le_exp.2 ?_
        have : ((k + j₀ + i : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hσ0'
      linarith
    have h := le_sum_sq_rpow_neg_primesIco_sharp (σ := σ) (m := k + j₀) (n := k + j₀ + i)
      (by omega) (by omega) hσ0' hσn
    have hcast2 : ((k + j₀ + i : ℕ) : ℝ) - ((k + j₀ : ℕ) : ℝ) = (i : ℝ) := by push_cast; ring
    rw [hc₀_def, hc₁_def, hcast₁, hcast₀]
    linarith
  have hU0 : (0 : ℝ) ≤ ∑ p ∈ primesIco c₀ c₁, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hW : (∑ p ∈ primesIco c₀ c₁, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4)
      ≤ (∑ p ∈ primesIco c₀ c₁, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 40000 := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp40 : 40000 ≤ p := by
      have := (mem_primesIco.1 hp).2.1
      omega
    obtain ⟨hu0, hu, _, _⟩ := range_prime_hyps (σ := σ) (h := h) hp40 hσ0'
    exact pow_four_le_sq_div hu0 hu
  have hosc : (∑ p ∈ primesIco c₀ c₁,
      ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * Real.cos (h * Real.log p)) ≤ 2 * K := by
    have hh0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hwlo
    have hm₀ : m₀ ≤ ϑ := by
      have h1 : m₀ ≤ (⌈m₀⌉₊ : ℝ) := Nat.le_ceil m₀
      have h2 : ((⌈m₀⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : ⌈m₀⌉₊ ≤ k := by omega
        exact_mod_cast this
      rw [hϑ_def]
      linarith
    have hτ2 : ∀ m : ℕ, m < i → h ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + ϑ) / 10)) := by
      intro m _
      have hh1 : h ≤ 1 := le_trans hwhi (Real.exp_le_one_iff.2 (by linarith))
      exact le_trans (sq_le_one_of_le_one hh0 hh1) (Real.one_le_exp (by positivity))
    have hσm : ∀ m : ℕ, m < i → |σ| * Real.log (blockScale ϑ (m + 1)) ≤ 1 := by
      intro m hm
      rw [log_blockScale, abs_of_pos hσ0]
      have hle : ((m + 1 : ℕ) : ℝ) + ϑ ≤ (t : ℝ) + 1 := by
        have : (m + 1 : ℕ) + k + j₀ ≤ t + 1 := by omega
        have hcast : ((m + 1 : ℕ) : ℝ) + ϑ = ((m + 1 + k + j₀ : ℕ) : ℝ) := by
          rw [hϑ_def]; push_cast; ring
        rw [hcast]
        have hc2 : ((m + 1 + k + j₀ : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at hc2 ⊢
        linarith
      have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hσ0'
      linarith
    have hK := HK h σ ϑ i hh0 hϑ0 hm₀ hτ2 hσm
    have hrw : (∑ p ∈ primesIco c₀ c₁,
          ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * Real.cos (h * Real.log p))
        = ∑ p ∈ primesIco (scaleCut ϑ) (scaleCut (ϑ + (i : ℕ))),
            Real.cos (h * Real.log p) * (p : ℝ) ^ (-1 - 2 * σ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [sq_rpow_neg_half_add (prime_of_mem_primesIco hp).pos]
      ring
    rw [hrw]
    refine le_trans (le_abs_self _) (le_trans hK ?_)
    have hdenom : 1 ≤ h * Real.exp ϑ := by
      have h1 : Real.exp (-((k : ℝ) + 1)) * Real.exp ϑ = Real.exp ((j₀ : ℝ) - 1) := by
        rw [← Real.exp_add, hϑ_def]
        congr 1
        ring
      have h2 : (1 : ℝ) ≤ Real.exp ((j₀ : ℝ) - 1) := Real.one_le_exp (by linarith)
      have h3 := mul_le_mul_of_nonneg_right hwlo (Real.exp_pos ϑ).le
      linarith
    exact div_le_self (by linarith) hdenom
  have hkey := mixed_exponent_bound hosc hUlo hU0 hW
  have hE0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) c₀ c₁ (shiftLine σ h) ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => by positivity
  calc Real.exp (-C / 2) * ((∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) c₀ c₁ (shiftLine σ h) ω‖ ^ 2 ∂μ)
          * Real.exp ((∑ p ∈ primesIco c₀ c₁,
                ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 * Real.cos (h * Real.log p))
              - (∑ p ∈ primesIco c₀ c₁, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) / 8
              + 2 * ∑ p ∈ primesIco c₀ c₁, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4))
      ≤ Real.exp (-C / 2) * ((∫ ω, ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) c₀ c₁ (shiftLine σ h) ω‖ ^ 2 ∂μ)
          * Real.exp (2 * K + 1 - (i : ℝ) / 9)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hkey) hE0) (Real.exp_nonneg _)
    _ = Real.exp (-C / 2) * Real.exp (2 * K + 1) * Real.exp (-((i : ℝ) / 9))
          * ∫ ω, ‖randomEulerProductIco
              (fun ω => squarefreeExtension fun p => X p ω) c₀ c₁ (shiftLine σ h) ω‖ ^ 2 ∂μ := by
        rw [show (2 * K + 1 - (i : ℝ) / 9) = (2 * K + 1) + -((i : ℝ) / 9) from by ring,
          Real.exp_add]
        ring

end ExceedFirst

section TubeBounds

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1600000 in
-- Proposition 5's hypotheses are discharged twice over, at the base offset and at every
-- restarted one, against the whole of Harper's data; that is what raises the limit here
set_option maxRecDepth 8000 in
/-- **The tube factor and the first-exceedance terms, with one set of constants.**  The two halves
of Harper's Proposition 5 at offset `k + j₀`, sharing `a` and `B`: the lower one bounds the tube
factor, and the upper one the `i`-th exceedance term, which factors across the cut at
`scaleCut (ϑ+i)` into `RMF.exists_setIntegral_exceed_first_le` (with its `e^{-C/2}` and geometric
decay) and the free-start tube of `RMF.barrierEvent_restart`.  Where the restarted tube is too
short for Proposition 5 the trivial bound is used; the constant `√n₀ + 1` in `D` pays for it. -/
theorem exists_halfTube_bounds :
    ∃ (a B α D : ℝ) (j₁ k₁ T₀ : ℕ), 1 ≤ a ∧ 0 ≤ B ∧ 0 < α ∧ 0 < D ∧ 1 ≤ j₁ ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t y j₀ : ℕ) (σ h : ℝ), k₁ ≤ k → j₁ ≤ j₀ → k + j₀ + T₀ ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → scaleCut ((t : ℝ) + 1) ≤ y →
        h ∈ halfWindow k →
        (α * min 1 (a / Real.sqrt ((t - k - j₀ : ℕ) : ℝ))
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ((k : ℝ) + (j₀ : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
          ≤ ∫ ω in barrierEvent (halfBlock X ((k : ℝ) + (j₀ : ℝ)) σ h) (t - k - j₀)
                (fun j => -a - B * j) (fun j => a + j + harperHf j),
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ((k : ℝ) + (j₀ : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
        ∧ (∀ (i : ℕ) (C : ℝ), 1 ≤ i → i ≤ t - k - j₀ →
            (∫ ω in barrierEvent (halfBlock X ((k : ℝ) + (j₀ : ℝ)) σ h) (t - k - j₀)
                  (fun j => -a - B * j) (fun j => a + j + harperHf j)
                ∩ {ω | C < walk (halfBlock X ((k : ℝ) + (j₀ : ℝ)) σ 0) i ω},
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                  (scaleCut ((k : ℝ) + (j₀ : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
              ≤ Real.exp (-C / 2) * D * Real.exp (-((i : ℝ) / 9))
                  * ((1 + (i : ℝ)) / (Real.sqrt ((t - k - j₀ - i : ℕ) : ℝ) + 1))
                * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut ((k : ℝ) + (j₀ : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ) := by
  obtain ⟨ϑ₀, n₀, a₀, α, A, B, Tsh, c, hα, hA, hB, hTsh, hc, H⟩ :=
    exists_const_proposition5_rademacher_of_cutoff_wide
  obtain ⟨D₁, k₂, hD₁, HD⟩ := exists_setIntegral_exceed_first_le (Ω := Ω)
  refine ⟨max a₀ 1, B, α,
    D₁ * max (2 * A * (3 * max a₀ 1 + B + 1)) (Real.sqrt (n₀ : ℝ) + 1),
    ⌈1 + Real.log (Tsh / 2)⌉₊ + 1,
    ⌈ϑ₀⌉₊ + ⌈10 * Real.log (4 / c)⌉₊ + k₂ + 20, n₀ + 1,
    le_max_right _ _, by linarith, hα, ?_, by omega, ?_⟩
  · have h1 : (0 : ℝ) < max (2 * A * (3 * max a₀ 1 + B + 1)) (Real.sqrt (n₀ : ℝ) + 1) :=
      lt_of_lt_of_le (by positivity) (le_max_right _ _)
    positivity
  intro X μ hX k t y j₀ σ h hk hj₀ ht hσ0 hσ hy hwin
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set a : ℝ := max a₀ 1 with ha_def
  set A' : ℝ := max (2 * A * (3 * a + B + 1)) (Real.sqrt (n₀ : ℝ) + 1) with hA'_def
  set n : ℕ := t - k - j₀ with hn_def
  set ϑ : ℝ := (k : ℝ) + (j₀ : ℝ) with hϑ_def
  obtain ⟨hwlo, hwhi⟩ := hwin
  have hσ0' : 0 ≤ σ := hσ0.le
  have hkj : k + j₀ ≤ t := by omega
  have hk20 : 20 ≤ k := by omega
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk20
  have hj₀1 : 1 ≤ j₀ := by omega
  have hj₀R : (1 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀1
  have ha1 : (1 : ℝ) ≤ a := le_max_right _ _
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hncast : ((n : ℕ) : ℝ) = (t : ℝ) - (k : ℝ) - (j₀ : ℝ) := by
    rw [hn_def, Nat.cast_sub (by omega : j₀ ≤ t - k), Nat.cast_sub (by omega : k ≤ t)]
  have hϑn : ϑ + (n : ℝ) = (t : ℝ) := by rw [hϑ_def, hncast]; ring
  have hϑ0 : (0 : ℝ) ≤ ϑ := by rw [hϑ_def]; linarith
  have hh0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hwlo
  have hh1 : h ≤ 1 := le_trans hwhi (Real.exp_le_one_iff.2 (by linarith))
  have hs : (shiftLine σ h).re = 1 / 2 + σ := re_shiftLine σ h
  have hsre : 0 < (shiftLine σ h).re := by rw [hs]; linarith
  have hϑt : ϑ ≤ (t : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hby : scaleCut ϑ ≤ y := le_trans (scaleCut_mono hϑt) hy
  have hby' : scaleCut (ϑ + (n : ℝ)) ≤ y := by
    rw [hϑn]
    exact le_trans (scaleCut_mono (by linarith)) hy
  -- the hypotheses of Proposition 5, at any offset `ϑ + r` with `r + m = n`
  have hprop : ∀ (r m : ℕ) (a' : ℝ) (hff : ℕ → ℝ), r + m = n → a₀ ≤ a' → n₀ ≤ m →
      (∀ j, 1 ≤ j → j ≤ m → |hff j| ≤ 10 * Real.log j) →
      ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
          (barrierEvent (halfBlock X (ϑ + (r : ℕ)) σ h) m
            (fun j => -a' - B * j) (fun j => a' + j + hff j))).toReal
        ≤ A * min 1 (a' / Real.sqrt (m : ℝ)) ∧
      α * min 1 (a' / Real.sqrt (m : ℝ))
        ≤ ((tiltedMeasure (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h) μ)
          (barrierEvent (halfBlock X (ϑ + (r : ℕ)) σ h) m
            (fun j => -a' - B * j) (fun j => a' + j + hff j))).toReal := by
    intro r m a' hff hrm ha' hm hhf
    have hrR : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hrm' : ϑ + (r : ℝ) + (m : ℝ) = (t : ℝ) := by
      have hcast : ((r : ℕ) : ℝ) + ((m : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
        rw [← Nat.cast_add, hrm]
      linarith [hϑn]
    have hϑ₀' : ϑ₀ ≤ ϑ + (r : ℝ) := by
      have h1 : ϑ₀ ≤ (⌈ϑ₀⌉₊ : ℝ) := Nat.le_ceil ϑ₀
      have h2 : ((⌈ϑ₀⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : ⌈ϑ₀⌉₊ ≤ k := by omega
        exact_mod_cast this
      rw [hϑ_def]
      linarith
    have hcut : blockCutoff (ϑ + (r : ℕ)) m ≤ y := by
      have heq : blockCutoff (ϑ + (r : ℕ)) m = scaleCut ((t : ℝ) + 1) := by
        rw [blockCutoff, ← scaleCut_add]
        congr 1
        push_cast
        linarith
      rw [heq]
      exact hy
    have hσtop : |σ| * Real.log (blockScale (ϑ + (r : ℕ)) (m + 1)) ≤ 1 / 10 := by
      rw [log_blockScale, abs_of_pos hσ0]
      have hcast : ((m + 1 : ℕ) : ℝ) + (ϑ + (r : ℝ)) = (t : ℝ) + 1 := by push_cast; linarith
      rw [hcast]
      exact hσ
    have hτ0 : 0 < 2 * (shiftLine σ h).im := by rw [im_shiftLine]; linarith
    have hτsq : (2 * (shiftLine σ h).im) ^ 2
        ≤ Real.exp (c / 2 * Real.exp ((ϑ + (r : ℕ)) / 10)) := by
      rw [im_shiftLine]
      have hexp : 4 / c ≤ Real.exp ((ϑ + (r : ℝ)) / 10) := by
        rcases le_total (4 / c) 1 with hle | hle
        · exact le_trans hle (Real.one_le_exp (by positivity))
        · have h1 : Real.log (4 / c) ≤ (⌈10 * Real.log (4 / c)⌉₊ : ℝ) / 10 := by
            have := Nat.le_ceil (10 * Real.log (4 / c))
            linarith
          have h2 : ((⌈10 * Real.log (4 / c)⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
            have : ⌈10 * Real.log (4 / c)⌉₊ ≤ k := by omega
            exact_mod_cast this
          have h3 : Real.log (4 / c) ≤ (ϑ + (r : ℝ)) / 10 := by rw [hϑ_def]; linarith
          calc 4 / c = Real.exp (Real.log (4 / c)) := (Real.exp_log (by linarith)).symm
            _ ≤ Real.exp ((ϑ + (r : ℝ)) / 10) := Real.exp_le_exp.2 h3
      have h4 : c / 2 * (4 / c) = 2 := by
        field_simp
        norm_num
      have hge : (2 : ℝ) ≤ c / 2 * Real.exp ((ϑ + (r : ℝ)) / 10) := by
        have hmul := mul_le_mul_of_nonneg_left hexp (by linarith : (0 : ℝ) ≤ c / 2)
        linarith [h4]
      have he2 : (4 : ℝ) ≤ Real.exp 2 := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_gt_d9]
      calc (2 * h) ^ 2 ≤ 4 := by nlinarith
        _ ≤ Real.exp 2 := he2
        _ ≤ Real.exp (c / 2 * Real.exp ((ϑ + (r : ℝ)) / 10)) := Real.exp_le_exp.2 hge
    have hT : Tsh ≤ 2 * (shiftLine σ h).im * Real.exp (ϑ + (r : ℕ)) := by
      rw [im_shiftLine]
      have hstep : Tsh / 2 ≤ Real.exp ((j₀ : ℝ) - 1) := by
        rcases le_total (Tsh / 2) 1 with hle | hle
        · exact le_trans hle (Real.one_le_exp (by linarith))
        · have h1 : Real.log (Tsh / 2) ≤ (⌈1 + Real.log (Tsh / 2)⌉₊ : ℝ) - 1 := by
            have := Nat.le_ceil (1 + Real.log (Tsh / 2))
            linarith
          have h2 : ((⌈1 + Real.log (Tsh / 2)⌉₊ : ℕ) : ℝ) ≤ (j₀ : ℝ) := by
            have : ⌈1 + Real.log (Tsh / 2)⌉₊ ≤ j₀ := by omega
            exact_mod_cast this
          calc Tsh / 2 = Real.exp (Real.log (Tsh / 2)) := (Real.exp_log (by linarith)).symm
            _ ≤ Real.exp ((j₀ : ℝ) - 1) := Real.exp_le_exp.2 (by linarith)
      have hmul : Real.exp (-((k : ℝ) + 1)) * Real.exp (ϑ + (r : ℝ))
          = Real.exp ((j₀ : ℝ) - 1) * Real.exp (r : ℝ) := by
        rw [← Real.exp_add, ← Real.exp_add, hϑ_def]
        congr 1
        ring
      have hr1 : (1 : ℝ) ≤ Real.exp (r : ℝ) := Real.one_le_exp hrR
      have hlow := mul_le_mul_of_nonneg_right hwlo (Real.exp_pos (ϑ + (r : ℝ))).le
      rw [hmul] at hlow
      nlinarith [Real.exp_pos ((j₀ : ℝ) - 1)]
    exact ⟨(H Ω X μ hX (ϑ + (r : ℕ)) σ a' m y (shiftLine σ h) hff hϑ₀' hcut hs hσtop
        hτ0 hτsq hT ha' hm hhf).2,
      (H Ω X μ hX (ϑ + (r : ℕ)) σ a' m y (shiftLine σ h) hff hϑ₀' hcut hs hσtop
        hτ0 hτsq hT ha' hm hhf).1⟩
  have hn₀n : n₀ ≤ n := by omega
  have hhfH : ∀ j : ℕ, 1 ≤ j → j ≤ n → |harperHf j| ≤ 10 * Real.log j := by
    intro j hj _
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hlog : 0 ≤ Real.log j := Real.log_nonneg hj1
    rw [harperHf, abs_of_nonpos (by linarith)]
    linarith
  have hA'1 : Real.sqrt (n₀ : ℝ) + 1 ≤ A' := le_max_right _ _
  have hA'0 : (0 : ℝ) < A' := lt_of_lt_of_le (by positivity) hA'1
  refine ⟨?_, ?_⟩
  · -- the tube factor
    have hz := (hprop 0 n a harperHf (by omega) (le_max_left _ _) hn₀n hhfH).2
    rw [show ϑ + ((0 : ℕ) : ℝ) = ϑ from by push_cast; ring] at hz
    have hAmeas : MeasurableSet[primeAlgebra X (scaleCut ϑ) y]
        (barrierEvent (halfBlock X ϑ σ h) n (fun j => -a - B * j)
          (fun j => a + j + harperHf j)) :=
      measurableSet_primeAlgebra_barrierEvent ϑ σ h hby' _ _
    exact le_setIntegral_normSq_of_le_tilted hX hby hsre hAmeas hz
  · -- the `i`-th exceedance term
    intro i C hi1 hin
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := by linarith
    have hinR : ((i : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hin
    have hϑϑ' : ϑ ≤ ϑ + (i : ℝ) := by linarith
    have hϑ't : ϑ + (i : ℝ) ≤ (t : ℝ) + 1 := by linarith [hϑn]
    have hc₀c₁ : scaleCut ϑ ≤ scaleCut (ϑ + (i : ℝ)) := scaleCut_mono hϑϑ'
    have hc₁y : scaleCut (ϑ + (i : ℝ)) ≤ y := le_trans (scaleCut_mono hϑ't) hy
    have hsub : (barrierEvent (halfBlock X ϑ σ h) n (fun j => -a - B * j)
          (fun j => a + j + harperHf j)) ∩ {ω | C < walk (halfBlock X ϑ σ 0) i ω}
        ⊆ {ω | C < walk (halfBlock X ϑ σ 0) i ω}
          ∩ barrierEvent (halfBlock X (ϑ + (i : ℝ)) σ h) (n - i)
              (fun j => -(3 * a + (B + 1) * (i : ℝ)) - B * j)
              (fun j => 3 * a + (B + 1) * (i : ℝ) + j) := by
      rintro ω ⟨hb, hw⟩
      exact ⟨hw, barrierEvent_restart ha0 (by linarith) hi1 hin hb⟩
    have hm1 : MeasurableSet[primeAlgebra X (scaleCut ϑ) (scaleCut (ϑ + (i : ℝ)))]
        {ω | C < walk (halfBlock X ϑ σ 0) i ω} :=
      measurableSet_lt measurable_const (measurable_primeAlgebra_walk ϑ σ 0 (le_refl i))
    have hm2 : MeasurableSet[primeAlgebra X (scaleCut (ϑ + (i : ℝ))) y]
        (barrierEvent (halfBlock X (ϑ + (i : ℝ)) σ h) (n - i)
          (fun j => -(3 * a + (B + 1) * (i : ℝ)) - B * j)
          (fun j => 3 * a + (B + 1) * (i : ℝ) + j)) :=
      measurableSet_primeAlgebra_restart hin hby' _ _
    have hsplit := setIntegral_normSq_split₂ (X := X) (s := shiftLine σ h) hX hc₀c₁ hc₁y hm1 hm2
    have hsplitU := setIntegral_normSq_split₂ (X := X) (s := shiftLine σ h) hX hc₀c₁ hc₁y
      (A := Set.univ) MeasurableSet.univ (B := Set.univ) MeasurableSet.univ
    rw [Set.univ_inter, setIntegral_univ, setIntegral_univ, setIntegral_univ] at hsplitU
    have hmono : (∫ ω in (barrierEvent (halfBlock X ϑ σ h) n (fun j => -a - B * j)
            (fun j => a + j + harperHf j)) ∩ {ω | C < walk (halfBlock X ϑ σ 0) i ω},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
        ≤ ∫ ω in {ω | C < walk (halfBlock X ϑ σ 0) i ω}
              ∩ barrierEvent (halfBlock X (ϑ + (i : ℝ)) σ h) (n - i)
                (fun j => -(3 * a + (B + 1) * (i : ℝ)) - B * j)
                (fun j => 3 * a + (B + 1) * (i : ℝ) + j),
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ :=
      setIntegral_mono_set (hf.integrable_norm_randomEulerProductIco_sq _ _ _).integrableOn
        (Filter.Eventually.of_forall fun ω => by positivity)
        (Filter.Eventually.of_forall hsub)
    refine le_trans hmono ?_
    rw [hsplit]
    have hfirst := HD X μ hX k t j₀ i σ h C (by omega) hj₀1 hi1 (by omega) hσ0 hσ ⟨hwlo, hwhi⟩
    rw [← hϑ_def] at hfirst
    have hE1 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ϑ) (scaleCut (ϑ + (i : ℝ)))
        (shiftLine σ h) ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
    have hE2 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (ϑ + (i : ℝ))) y
        (shiftLine σ h) ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
    have hsecond : (∫ ω in barrierEvent (halfBlock X (ϑ + (i : ℝ)) σ h) (n - i)
            (fun j => -(3 * a + (B + 1) * (i : ℝ)) - B * j)
            (fun j => 3 * a + (B + 1) * (i : ℝ) + j),
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (ϑ + (i : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
        ≤ A' * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut (ϑ + (i : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
      by_cases hcase : 1 ≤ n - i ∧ n₀ ≤ n - i
      · have hup := (hprop i (n - i) (3 * a + (B + 1) * (i : ℝ)) (fun _ => 0) (by omega)
          (le_trans (le_max_left _ _) (by nlinarith)) hcase.2 (by
            intro j hj _
            have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
            simpa using Real.log_nonneg hj1)).1
        rw [show (fun j : ℕ => 3 * a + (B + 1) * (i : ℝ) + (j : ℝ) + (0 : ℝ))
            = (fun j : ℕ => 3 * a + (B + 1) * (i : ℝ) + (j : ℝ)) from by funext j; ring] at hup
        refine setIntegral_normSq_le_of_tilted_le hX hc₁y hsre hm2 (le_trans hup ?_)
        have hni1 : (1 : ℝ) ≤ ((n - i : ℕ) : ℝ) := by exact_mod_cast hcase.1
        have hsq1 : (1 : ℝ) ≤ Real.sqrt ((n - i : ℕ) : ℝ) := by
          rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
          exact Real.sqrt_le_sqrt hni1
        have hS0 : (0 : ℝ) < Real.sqrt ((n - i : ℕ) : ℝ) := by linarith
        have hbi : (0 : ℝ) ≤ (B + 1) * (i : ℝ) :=
          mul_nonneg (by linarith) hi0
        have hnum0 : (0 : ℝ) ≤ A * (3 * a + (B + 1) * (i : ℝ)) :=
          mul_nonneg hA.le (by linarith)
        have hkey : 2 * A * (3 * a + (B + 1) * (i : ℝ)) ≤ A' * (1 + (i : ℝ)) := by
          have hA'2 : 2 * A * (3 * a + B + 1) ≤ A' := le_max_left _ _
          have hmul := mul_le_mul_of_nonneg_right hA'2 (by linarith : (0 : ℝ) ≤ 1 + (i : ℝ))
          nlinarith [hA.le, ha0, hi0, hB, mul_nonneg (mul_nonneg hA.le ha0) hi0]
        calc A * min 1 ((3 * a + (B + 1) * (i : ℝ)) / Real.sqrt ((n - i : ℕ) : ℝ))
            ≤ A * ((3 * a + (B + 1) * (i : ℝ)) / Real.sqrt ((n - i : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hA.le
          _ ≤ A' * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1)) := by
              rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hS0 (by linarith)]
              nlinarith [hkey, hnum0, hsq1]
      · have hni : n - i ≤ n₀ := by omega
        have hniR : ((n - i : ℕ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hni
        have hsq : Real.sqrt ((n - i : ℕ) : ℝ) ≤ Real.sqrt (n₀ : ℝ) := Real.sqrt_le_sqrt hniR
        have hone : (1 : ℝ) ≤ A' * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1)) := by
          rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
          nlinarith [hA'0]
        calc (∫ ω in barrierEvent (halfBlock X (ϑ + (i : ℝ)) σ h) (n - i)
                (fun j => -(3 * a + (B + 1) * (i : ℝ)) - B * j)
                (fun j => 3 * a + (B + 1) * (i : ℝ) + j),
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (ϑ + (i : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
            ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (ϑ + (i : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ :=
              setIntegral_le_integral (hf.integrable_norm_randomEulerProductIco_sq _ _ _)
                (Filter.Eventually.of_forall fun ω => by positivity)
          _ ≤ A' * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
                * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                    (scaleCut (ϑ + (i : ℝ))) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
              nlinarith [hE2, hone]
    have hprod := mul_le_mul hfirst hsecond
      (setIntegral_nonneg (measurableSet_of_primeAlgebra hX hm2) fun ω _ => by positivity)
      (by positivity)
    refine le_trans hprod (le_of_eq ?_)
    rw [hsplitU]
    ring

end TubeBounds

/-! ### The second moment of a range, from below

The first moment's statement asks for `≫ e^{t-k}`, with the *coefficient* of the exponent equal
to one, so the second moment `∏(1 + p^{-1-2σ})` has to be bounded below by `e^{U - O(1)}` and not
`e^{U(1-ε)}`.  That needs `∑_p p^{-2-4σ}` bounded by an absolute constant — not by a multiple of
`U`, which would cost `e^{-εn}`. -/

section SecondMomentLower

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω} {σ h : ℝ}

/-- **`∑_p p^{-2-4σ} ≤ 1/(a-1)`** over the primes of `[a, b)` — an absolute constant, by
`RMF.sum_inv_sq_Ico_le`. -/
lemma sum_pow_four_primesIco_le {a b : ℕ} (ha : 2 ≤ a) (hσ : 0 ≤ σ) :
    ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4 ≤ 1 / ((a : ℝ) - 1) := by
  have hsub : primesIco a b ⊆ Finset.Ico a b := by
    intro p hp
    obtain ⟨_, h1, h2⟩ := mem_primesIco.1 hp
    exact Finset.mem_Ico.2 ⟨h1, h2⟩
  calc ∑ p ∈ primesIco a b, ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4
      ≤ ∑ p ∈ primesIco a b, (1 : ℝ) / (p : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpp := prime_of_mem_primesIco hp
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
        have hfour : ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4 = (p : ℝ) ^ (-(1 / 2 + σ) * (4 : ℕ)) := by
          rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 + σ))) 4, ← Real.rpow_mul hp0.le]
        rw [hfour]
        calc (p : ℝ) ^ (-(1 / 2 + σ) * (4 : ℕ)) ≤ (p : ℝ) ^ (-2 : ℝ) := by
              refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
              push_cast
              linarith
          _ = 1 / (p : ℝ) ^ 2 := by
              rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num, Real.rpow_neg hp0.le,
                Real.rpow_natCast]
              rw [one_div]
    _ ≤ ∑ m ∈ Finset.Ico a b, (1 : ℝ) / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
    _ ≤ 1 / ((a : ℝ) - 1) := sum_inv_sq_Ico_le ha b

/-- **The second moment of a range, from below**: `E‖F_{(m,n]}(σ+ih)‖² ≥ e^{n-m-3}`. -/
theorem le_integral_normSq_range (hX : IsRademacherPrimeValues X μ) {m n : ℕ} (hm : 20 ≤ m)
    (hmn : m ≤ n) (hσ : 0 ≤ σ) (hσn : σ * Real.exp (n : ℝ) ≤ 1 / 2) :
    Real.exp ((n : ℝ) - (m : ℝ) - 3)
      ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut (m : ℝ)) (scaleCut (n : ℝ)) (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  rw [integral_normSq_range_eq_prod hX]
  have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc40 : 40000 ≤ scaleCut (m : ℝ) := by
    have h1 : (100000000000000 : ℕ) ≤ scaleCut (m : ℝ) := pow_fourteen_le_scaleCut hmR
    omega
  have hU := le_sum_sq_rpow_neg_primesIco_sharp hm hmn hσ hσn
  have hW := sum_pow_four_primesIco_le (a := scaleCut (m : ℝ)) (b := scaleCut (n : ℝ))
    (σ := σ) (by omega) hσ
  have hWle : ∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
      ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4 ≤ 1 := by
    refine le_trans hW ?_
    have hc : (40000 : ℝ) ≤ ((scaleCut (m : ℝ) : ℕ) : ℝ) := by exact_mod_cast hc40
    rw [div_le_one (by linarith)]
    linarith
  -- each factor dominates `exp(u² - u⁴)`
  have hstep : Real.exp (∑ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
        (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 - ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4))
      ≤ ∏ p ∈ primesIco (scaleCut (m : ℝ)) (scaleCut (n : ℝ)),
          (1 + ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
    have hp40 : 40000 ≤ p := by
      have := (mem_primesIco.1 hp).2.1
      omega
    obtain ⟨hu0, hu, _, _⟩ := range_prime_hyps (σ := σ) (h := h) hp40 hσ
    have hsq0 : (0 : ℝ) ≤ ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2 := sq_nonneg _
    have hpow : (((p : ℝ) ^ (-(1 / 2 + σ))) ^ 2) ^ 2 = ((p : ℝ) ^ (-(1 / 2 + σ))) ^ 4 := by ring
    have hkey := exp_sub_sq_le_one_add hsq0
    rw [hpow] at hkey
    exact hkey
  refine le_trans ?_ hstep
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_sub_distrib]
  linarith

end SecondMomentLower

/-! ### The first-exceedance sum

`∑_{i=1}^{n} e^{-i/9}(1+i)/(√(n-i)+1) = O(1/√n)`, the order of the main term.  Every term is
`≤ 38(1+i)e^{-i/18}/√n` by `RMF.exceed_weight_le`, and `i ≤ 32e^{i/32}` turns the remaining
`i e^{-i/18}` into another geometric series. -/

section ExceedSum

/-- **The first-exceedance weights sum to `O(1/√n)`.** -/
lemma sum_exceed_weights_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n,
        Real.exp (-((i : ℝ) / 9)) * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
      ≤ 53010 / Real.sqrt (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hstep : ∀ i ∈ Finset.Icc 1 n,
      Real.exp (-((i : ℝ) / 9)) * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))
        ≤ 38 * ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) / Real.sqrt (n : ℝ) := by
    intro i hi
    obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
    exact exceed_weight_le hi1 hin
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_div, ← Finset.mul_sum, div_le_div_iff_of_pos_right hsqn]
  have hsub : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro i hi
    obtain ⟨_, h2⟩ := Finset.mem_Icc.1 hi
    exact Finset.mem_range.2 (by omega)
  have hinner : ∑ i ∈ Finset.Icc 1 n, ((1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))) ≤ 1395 := by
    have hterm : ∀ i ∈ Finset.Icc 1 n, (1 + (i : ℝ)) * Real.exp (-((i : ℝ) / 18))
        ≤ Real.exp (-((1 / 18 : ℝ) * (i : ℝ))) + 32 * Real.exp (-((7 / 288 : ℝ) * (i : ℝ))) := by
      intro i _
      have hbnd : (i : ℝ) * Real.exp (-((1 / 18 : ℝ) * (i : ℝ)))
          ≤ 32 * Real.exp (-((7 / 288 : ℝ) * (i : ℝ))) := by
        have h1 := natCast_le_exp_div i
        have h2 := mul_le_mul_of_nonneg_right h1
          (Real.exp_nonneg (-((1 / 18 : ℝ) * (i : ℝ))))
        refine le_trans h2 (le_of_eq ?_)
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      have he1 : Real.exp (-((i : ℝ) / 18)) = Real.exp (-((1 / 18 : ℝ) * (i : ℝ))) := by
        congr 1
        ring
      rw [he1]
      linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hA : ∑ i ∈ Finset.Icc 1 n, Real.exp (-((1 / 18 : ℝ) * (i : ℝ))) ≤ 19 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
        Real.exp_nonneg _) ?_
      calc ∑ i ∈ Finset.range (n + 1), Real.exp (-((1 / 18 : ℝ) * (i : ℝ)))
          ≤ (1 + (1 / 18 : ℝ)) / (1 / 18) := sum_exp_neg_mul_range_le (by norm_num) (n + 1)
        _ ≤ 19 := by norm_num
    have hB : ∑ i ∈ Finset.Icc 1 n, Real.exp (-((7 / 288 : ℝ) * (i : ℝ))) ≤ 43 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
        Real.exp_nonneg _) ?_
      calc ∑ i ∈ Finset.range (n + 1), Real.exp (-((7 / 288 : ℝ) * (i : ℝ)))
          ≤ (1 + (7 / 288 : ℝ)) / (7 / 288) := sum_exp_neg_mul_range_le (by norm_num) (n + 1)
        _ ≤ 43 := by norm_num
    linarith
  linarith

end ExceedSum

/-! ### Subadditivity of the set integral over a finite cover -/

section Cover

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **A set integral is at most the sum over a finite cover**, for a nonnegative integrand. -/
lemma setIntegral_le_sum_of_subset_biUnion {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) {S : Set Ω} {A : ℕ → Set Ω} {T : Finset ℕ}
    (hA : ∀ i ∈ T, MeasurableSet (A i)) (hS : MeasurableSet S)
    (hsub : S ⊆ ⋃ i ∈ T, A i) :
    (∫ ω in S, f ω ∂μ) ≤ ∑ i ∈ T, ∫ ω in A i, f ω ∂μ := by
  classical
  have hpt : ∀ ω, Set.indicator S f ω ≤ ∑ i ∈ T, Set.indicator (A i) f ω := by
    intro ω
    by_cases hω : ω ∈ S
    · obtain ⟨i, hiT, hiA⟩ := Set.mem_iUnion₂.1 (hsub hω)
      rw [Set.indicator_of_mem hω]
      refine le_trans (le_of_eq (Set.indicator_of_mem hiA f).symm) ?_
      refine Finset.single_le_sum (f := fun i => Set.indicator (A i) f ω) ?_ hiT
      exact fun j _ => Set.indicator_nonneg (fun ω' _ => hf0 ω') ω
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun ω' _ => hf0 ω') ω
  have hint : ∀ i ∈ T, Integrable (Set.indicator (A i) f) μ := fun i hi =>
    (hf.indicator (hA i hi))
  calc (∫ ω in S, f ω ∂μ) = ∫ ω, Set.indicator S f ω ∂μ := (integral_indicator hS).symm
    _ ≤ ∫ ω, ∑ i ∈ T, Set.indicator (A i) f ω ∂μ :=
        integral_mono (hf.indicator hS) (integrable_finsetSum T hint) hpt
    _ = ∑ i ∈ T, ∫ ω, Set.indicator (A i) f ω ∂μ := integral_finsetSum T hint
    _ = ∑ i ∈ T, ∫ ω in A i, f ω ∂μ :=
        Finset.sum_congr rfl fun i hi => integral_indicator (hA i hi)

end Cover

/-! ### The barriered first moment

The two barrier factors and the level event, assembled.  `E_>(k)` is reached by the two events
below and above the cut: on the descent the walk from `k` is below the running sum of the block
means, which Mertens puts below `-C₂`; on the level event the walk from `k+j₀` stays below `C₂`;
together they keep the walk from `k` below `0` all the way to `t`, which is `E_>(k)`.

The constants are chosen in one order and cannot be chosen in another: `a` and `B` come from
Proposition 5; `C₂` is then large enough that `e^{-C₂/2}` beats the barrier's own `α a`; `j₀` is
large enough for the descent to reach `-C₂`; and `C₁` is large enough for the box. -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}

omit [MeasurableSpace Ω] in
/-- A block increment is measurable for the algebra of a range containing it. -/
lemma measurable_primeAlgebra_halfBlock (θ σ h : ℝ) {n m : ℕ} (hm : m < n) :
    Measurable[primeAlgebra X (scaleCut θ) (scaleCut (θ + n))] (halfBlock X θ σ h m) :=
  Finset.measurable_sum _ fun _ hp => (measurable_localLogAdd _).comp
    (measurable_primeAlgebra_apply (mem_primesIco_of_mem_primeBlockSub_range hm hp))

omit [MeasurableSpace Ω] in
/-- The descent event is measurable for the algebra of a range containing its blocks. -/
lemma measurableSet_primeAlgebra_halfDescent (θ σ : ℝ) {n b : ℕ}
    (hb : scaleCut (θ + (n : ℕ)) ≤ b) :
    MeasurableSet[primeAlgebra X (scaleCut θ) b] (halfDescent X θ σ n) := by
  refine MeasurableSet.biInter (Set.to_countable _) fun m hm => ?_
  exact measurableSet_le ((measurable_primeAlgebra_halfBlock θ σ 0 (Finset.mem_range.1 hm)).mono
    (primeAlgebra_mono le_rfl hb) le_rfl) measurable_const

omit [MeasurableSpace Ω] in
/-- The level event is measurable for the algebra of a range containing its blocks. -/
lemma measurableSet_primeAlgebra_level (θ σ : ℝ) {n b : ℕ} (hb : scaleCut (θ + (n : ℕ)) ≤ b)
    (C : ℝ) :
    MeasurableSet[primeAlgebra X (scaleCut θ) b]
      {ω | ∀ i, 1 ≤ i → i ≤ n → walk (halfBlock X θ σ 0) i ω ≤ C} := by
  have hrw : {ω | ∀ i, 1 ≤ i → i ≤ n → walk (halfBlock X θ σ 0) i ω ≤ C}
      = ⋂ i ∈ Set.Icc 1 n, {ω | walk (halfBlock X θ σ 0) i ω ≤ C} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
    exact ⟨fun hω i hi => hω i hi.1 hi.2, fun hω i h1 h2 => hω i ⟨h1, h2⟩⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun i hi => ?_
  exact measurableSet_le ((measurable_primeAlgebra_walk θ σ 0 hi.2).mono
    (primeAlgebra_mono le_rfl hb) le_rfl) measurable_const

omit [MeasurableSpace Ω] in
/-- **The descent and the level event force `E_>(k)`.**  Below the cut the walk is under the
running sum of the means, which is nonpositive and ends below `-C₂`; above it the walk from
`k+j₀` stays under `C₂`. -/
lemma halfDescent_inter_level_subset_halfAfter {σ : ℝ} (hσ : 0 ≤ σ) {k t j₀ : ℕ} {C : ℝ}
    (hkj : k + j₀ ≤ t)
    (hmean : ∑ m ∈ Finset.range j₀, halfBlockMean (k : ℝ) σ m ≤ -C) :
    halfDescent X (k : ℝ) σ j₀
        ∩ {ω | ∀ i, 1 ≤ i → i ≤ t - k - j₀ →
            walk (halfBlock X ((k : ℝ) + (j₀ : ℕ)) σ 0) i ω ≤ C}
      ⊆ halfAfter X σ k t := by
  rintro ω ⟨hA, hL⟩ j hj1 hjt
  rcases le_or_gt j j₀ with hj | hj
  · refine le_trans (walk_le_of_mem_halfDescent hA hj) ?_
    exact Finset.sum_nonpos fun m _ => halfBlockMean_nonpos _ hσ m
  · have hshift : walk (halfBlock X (k : ℝ) σ 0) j ω
        = walk (halfBlock X (k : ℝ) σ 0) j₀ ω
          + walk (halfBlock X ((k : ℝ) + (j₀ : ℕ)) σ 0) (j - j₀) ω := by
      rw [halfBlock_shift, walk_shift, show j₀ + (j - j₀) = j from by omega]
      ring
    have h1 : walk (halfBlock X (k : ℝ) σ 0) j₀ ω ≤ -C :=
      le_trans (walk_le_of_mem_halfDescent hA le_rfl) hmean
    have h2 : walk (halfBlock X ((k : ℝ) + (j₀ : ℕ)) σ 0) (j - j₀) ω ≤ C :=
      hL (j - j₀) (by omega) (by omega)
    rw [hshift]
    linarith

set_option maxHeartbeats 1600000 in
-- the whole assembly is here, against Harper's data through `exists_halfTube_bounds`
set_option maxRecDepth 8000 in
/-- **The barriered first moment**, the counterpart of Proposition 6.3 of the paper.

`c·e^{t-k}/√(t-k) ≤ ∫_{L(k,h) ∩ E_>(k)} ‖F_{(k,y)}(½+σ+ih)‖²`, uniformly for `k ≥ k₁`,
`t - k ≥ T₀` and `h` in the window at scale `k`, when `σe^{t+1} ≤ 1/10`, `e^{-6} ≤ σe^t` and
`scaleCut (t+1) ≤ y`; `F_{(k,y)}` is the Euler product over the primes `p < y` with
`log log p > k`.  The barrier constants `(j₀, C₁, a, B)` are part of the conclusion.

The cutoff `scaleCut (t+1) ≤ y` asks for one block beyond the top of the barrier, as Harper's
Proposition 5's `blockCutoff ϑ n` does; the decomposition meets it at `y = ⌊x⌋₊+1`, since
`e^{t+1} ≤ log x`. -/
theorem exists_le_setIntegral_halfBarrier_halfAfter :
    ∃ (j₀ : ℕ) (C₁ a B c : ℝ) (k₁ T₀ : ℕ), 0 ≤ C₁ ∧ 0 ≤ a ∧ 0 ≤ B ∧ 0 < c ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (k t y : ℕ) (σ h : ℝ), k₁ ≤ k → k + T₀ ≤ t → 0 < σ →
        σ * Real.exp ((t : ℝ) + 1) ≤ 1 / 10 → Real.exp (-6) ≤ σ * Real.exp (t : ℝ) →
        scaleCut ((t : ℝ) + 1) ≤ y → h ∈ halfWindow k →
        c * Real.exp ((t : ℝ) - k) / Real.sqrt ((t : ℝ) - k)
          ≤ ∫ ω in halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t,
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut (k : ℝ)) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
  obtain ⟨a, B, α, D, j₁, k₁', T₀', ha1, hB0, hα, hD, hj₁, H⟩ := exists_halfTube_bounds (Ω := Ω)
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set C₂ : ℝ := 2 * |Real.log (2 * D * 53010 / (α * a))| + 2 with hC₂_def
  have hC₂0 : (0 : ℝ) ≤ C₂ := by positivity
  set j₀ : ℕ := max j₁ ⌈2 * C₂ + 2⌉₊ with hj₀_def
  have hj₀1 : 1 ≤ j₀ := le_trans hj₁ (le_max_left _ _)
  have hj₀R : (2 : ℝ) * C₂ + 2 ≤ (j₀ : ℝ) := by
    have h1 : (2 : ℝ) * C₂ + 2 ≤ (⌈2 * C₂ + 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * C₂ + 2⌉₊ : ℕ) : ℝ) ≤ (j₀ : ℝ) := by
      have : (⌈2 * C₂ + 2⌉₊ : ℕ) ≤ j₀ := le_max_right _ _
      exact_mod_cast this
    linarith
  have hj₀1R : (1 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀1
  set C₁ : ℝ := 12 * ((j₀ : ℝ) + 1) + Real.log (2 * (j₀ : ℝ) + 2) + ((j₀ : ℝ) + 1) with hC₁_def
  have hlog4 : (0 : ℝ) ≤ Real.log (2 * (j₀ : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hC₁0 : (0 : ℝ) ≤ C₁ := by rw [hC₁_def]; linarith
  -- the key numeric fact: the level `C₂` beats the barrier's own constant
  have hkeyC : Real.exp (-C₂ / 2) * D * 53010 ≤ α * a / 2 := by
    have hpos : (0 : ℝ) < 2 * D * 53010 / (α * a) := by positivity
    have hL : Real.exp (-Real.log (2 * D * 53010 / (α * a))) = α * a / (2 * D * 53010) := by
      rw [Real.exp_neg, Real.exp_log hpos]
      field_simp
    have hle : Real.exp (-C₂ / 2) ≤ Real.exp (-Real.log (2 * D * 53010 / (α * a))) := by
      refine Real.exp_le_exp.2 ?_
      rw [hC₂_def]
      linarith [le_abs_self (Real.log (2 * D * 53010 / (α * a))),
        abs_nonneg (Real.log (2 * D * 53010 / (α * a)))]
    rw [hL] at hle
    have hD0 : (0 : ℝ) < 2 * D * 53010 := by positivity
    have := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ 2 * D * 53010)
    rw [div_mul_cancel₀ _ (ne_of_gt hD0)] at this
    nlinarith [this]
  refine ⟨j₀, C₁, a, B,
    Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2) * Real.exp (-((j₀ : ℝ) + 3)),
    max k₁' 20, j₀ + T₀' + ⌈a ^ 2⌉₊ + 1, hC₁0, ha0, hB0, by positivity, ?_⟩
  intro X μ hX k t y σ h hk ht hσ0 hσ _hσlo hy hwin
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hwlo, hwhi⟩ := hwin
  have hσ0' : (0 : ℝ) ≤ σ := hσ0.le
  set n : ℕ := t - k - j₀ with hn_def
  set ϑ : ℝ := (k : ℝ) + (j₀ : ℝ) with hϑ_def
  have hk20 : 20 ≤ k := le_trans (le_max_right _ _) hk
  have hkj : k + j₀ ≤ t := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hncast : ((n : ℕ) : ℝ) = (t : ℝ) - (k : ℝ) - (j₀ : ℝ) := by
    rw [hn_def, Nat.cast_sub (by omega : j₀ ≤ t - k), Nat.cast_sub (by omega : k ≤ t)]
  have hϑn : ϑ + (n : ℝ) = (t : ℝ) := by rw [hϑ_def, hncast]; ring
  have het : (1 : ℝ) ≤ Real.exp ((t : ℝ) + 1) := Real.one_le_exp (by positivity)
  have hσt : σ * Real.exp ((k + j₀ : ℕ) : ℝ) ≤ 1 / 2 := by
    have h1 : Real.exp (((k + j₀ : ℕ)) : ℝ) ≤ Real.exp ((t : ℝ) + 1) := by
      refine Real.exp_le_exp.2 ?_
      have : ((k + j₀ : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkj
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hσ0'
    linarith
  have hσt' : σ * Real.exp ((t : ℕ) : ℝ) ≤ 1 / 2 := by
    have h1 : Real.exp ((t : ℕ) : ℝ) ≤ Real.exp ((t : ℝ) + 1) := Real.exp_le_exp.2 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 hσ0'
    linarith
  -- the descent reaches `-C₂`
  have hmean : ∑ m ∈ Finset.range j₀, halfBlockMean (k : ℝ) σ m ≤ -C₂ := by
    have h1 := sum_halfBlockMean_le (σ := σ) hσ0' k j₀
    have h2 := le_sum_sq_rpow_neg_primesIco_sharp (σ := σ) (m := k) (n := k + j₀)
      hk20 (by omega) hσ0' hσt
    have hcast : ((k + j₀ : ℕ) : ℝ) - (k : ℝ) = (j₀ : ℝ) := by push_cast; ring
    rw [hcast] at h2
    linarith
  -- the four events
  have hϑ0 : (0 : ℝ) ≤ ϑ := by rw [hϑ_def]; positivity
  have hϑt1 : ϑ ≤ (t : ℝ) + 1 := by linarith
  have hby : scaleCut ϑ ≤ y := le_trans (scaleCut_mono hϑt1) hy
  have hbyn : scaleCut (ϑ + ((n : ℕ) : ℝ)) ≤ y := by
    rw [hϑn]
    exact le_trans (scaleCut_mono (by linarith)) hy
  have hkϑ : scaleCut (k : ℝ) ≤ scaleCut ϑ := scaleCut_mono (by rw [hϑ_def]; linarith)
  set Box : Set Ω := barrierEvent (halfBlock X (k : ℝ) σ h) j₀ (fun _ => -C₁) (fun _ => C₁)
    with hBox_def
  set A₁ : Set Ω := halfDescent X (k : ℝ) σ j₀ with hA₁_def
  set Tube : Set Ω := barrierEvent (halfBlock X ϑ σ h) n
    (fun j => -a - B * j) (fun j => a + j + harperHf j) with hTube_def
  set Lev : Set Ω := {ω | ∀ i, 1 ≤ i → i ≤ n → walk (halfBlock X ϑ σ 0) i ω ≤ C₂} with hLev_def
  have hmBox : MeasurableSet[primeAlgebra X (scaleCut (k : ℝ)) (scaleCut ϑ)] (Box ∩ A₁) :=
    (measurableSet_primeAlgebra_barrierEvent (k : ℝ) σ h le_rfl _ _).inter
      (measurableSet_primeAlgebra_halfDescent (k : ℝ) σ le_rfl)
  have hmTube : MeasurableSet[primeAlgebra X (scaleCut ϑ) y] (Tube ∩ Lev) :=
    (measurableSet_primeAlgebra_barrierEvent ϑ σ h hbyn _ _).inter
      (measurableSet_primeAlgebra_level ϑ σ hbyn C₂)
  have hTubeM : MeasurableSet Tube :=
    measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_barrierEvent ϑ σ h hbyn _ _)
  have hLevM : MeasurableSet Lev :=
    measurableSet_of_primeAlgebra hX (measurableSet_primeAlgebra_level ϑ σ hbyn C₂)
  have hsplit := setIntegral_normSq_split₂ (X := X) (s := shiftLine σ h) hX hkϑ hby hmBox hmTube
  have hincl : (Box ∩ A₁) ∩ (Tube ∩ Lev)
      ⊆ halfBarrier X σ h k j₀ t C₁ a B ∩ halfAfter X σ k t := by
    rintro ω ⟨⟨hb, hA⟩, hT, hLv⟩
    exact ⟨⟨hb, hT⟩, halfDescent_inter_level_subset_halfAfter hσ0' hkj hmean ⟨hA, hLv⟩⟩
  have hmono := setIntegral_mono_set
    (hf.integrable_norm_randomEulerProductIco_sq (scaleCut (k : ℝ)) y (shiftLine σ h)).integrableOn
    (Filter.Eventually.of_forall fun ω => by positivity) (LE.le.eventuallyLE hincl)
  refine le_trans ?_ hmono
  rw [hsplit]
  -- the factor below the cut
  have hfac1 : Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1)
      ≤ ∫ ω in Box ∩ A₁, ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (scaleCut (k : ℝ)) (scaleCut ϑ)
          (shiftLine σ h) ω‖ ^ 2 ∂μ :=
    le_setIntegral_halfBox_halfDescent hX hk20 hσ0' hC₁0 (le_of_eq hC₁_def.symm)
  -- the factor above the cut
  have hbounds := H X μ hX k t y j₀ σ h (le_trans (le_max_left _ _) hk) (le_max_left _ _)
    (by omega) hσ0 hσ hy ⟨hwlo, hwhi⟩
  set E : ℝ := ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
    (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ with hE_def
  have hE0 : (0 : ℝ) ≤ E := integral_nonneg fun ω => by positivity
  have hsqn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  -- the level event, by subtraction
  have hcover : Tube \ Lev
      ⊆ ⋃ i ∈ Finset.Icc 1 n, (Tube ∩ {ω | C₂ < walk (halfBlock X ϑ σ 0) i ω}) := by
    rintro ω ⟨hT, hnL⟩
    by_contra hcon
    refine hnL fun i hi1 hin => ?_
    by_contra hlt
    exact hcon (Set.mem_iUnion₂.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hin⟩, ⟨hT, not_le.1 hlt⟩⟩)
  have hdiff : (∫ ω in Tube \ Lev, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
      ≤ ∑ i ∈ Finset.Icc 1 n, ∫ ω in Tube ∩ {ω | C₂ < walk (halfBlock X ϑ σ 0) i ω},
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ :=
    setIntegral_le_sum_of_subset_biUnion
      (hf.integrable_norm_randomEulerProductIco_sq (scaleCut ϑ) y (shiftLine σ h))
      (fun ω => by positivity)
      (fun i _ => hTubeM.inter (measurableSet_lt measurable_const
        (measurable_walk_of (measurable_halfBlock hX ϑ σ 0) i)))
      (hTubeM.diff hLevM) hcover
  have hsum : (∑ i ∈ Finset.Icc 1 n, ∫ ω in Tube ∩ {ω | C₂ < walk (halfBlock X ϑ σ 0) i ω},
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
      ≤ (Real.exp (-C₂ / 2) * D * E) * (53010 / Real.sqrt (n : ℝ)) := by
    have hterm : ∀ i ∈ Finset.Icc 1 n,
        (∫ ω in Tube ∩ {ω | C₂ < walk (halfBlock X ϑ σ 0) i ω},
            ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
          ≤ (Real.exp (-C₂ / 2) * D * E)
            * (Real.exp (-((i : ℝ) / 9))
              * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))) := by
      intro i hi
      obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
      have := hbounds.2 i C₂ hi1 hin
      calc (∫ ω in Tube ∩ {ω | C₂ < walk (halfBlock X ϑ σ 0) i ω},
              ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
                (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ)
          ≤ Real.exp (-C₂ / 2) * D * Real.exp (-((i : ℝ) / 9))
              * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1)) * E := this
        _ = (Real.exp (-C₂ / 2) * D * E)
              * (Real.exp (-((i : ℝ) / 9))
                * ((1 + (i : ℝ)) / (Real.sqrt ((n - i : ℕ) : ℝ) + 1))) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_exceed_weights_le hn1) (by positivity)
  have hadd := integral_inter_add_sdiff (μ := μ) (s := Tube) hLevM
    (hf.integrable_norm_randomEulerProductIco_sq (scaleCut ϑ) y (shiftLine σ h)).integrableOn
  -- `min 1 (a/√n) = a/√n`
  have ha2n : a ^ 2 ≤ (n : ℝ) := by
    have h1 : (⌈a ^ 2⌉₊ : ℕ) ≤ n := by omega
    have h2 : ((⌈a ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith [Nat.le_ceil (a ^ 2)]
  have hasq : a ≤ Real.sqrt (n : ℝ) := by
    rw [show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha0).symm]
    exact Real.sqrt_le_sqrt ha2n
  have hmin : min 1 (a / Real.sqrt (n : ℝ)) = a / Real.sqrt (n : ℝ) :=
    min_eq_right (by rw [div_le_one hsqn]; exact hasq)
  rw [hmin] at hbounds
  -- the factor above the cut, from below
  have hfac2 : α * a / 2 / Real.sqrt (n : ℝ) * E ≤ ∫ ω in Tube ∩ Lev,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        (scaleCut ϑ) y (shiftLine σ h) ω‖ ^ 2 ∂μ := by
    have hkey2 : Real.exp (-C₂ / 2) * D * 53010 / Real.sqrt (n : ℝ) ≤ α * a / 2
        / Real.sqrt (n : ℝ) := by
      rw [div_le_div_iff_of_pos_right hsqn]
      exact hkeyC
    have hE1 : (Real.exp (-C₂ / 2) * D * E) * (53010 / Real.sqrt (n : ℝ))
        = (Real.exp (-C₂ / 2) * D * 53010 / Real.sqrt (n : ℝ)) * E := by ring
    rw [hE1] at hsum
    have hmul := mul_le_mul_of_nonneg_right hkey2 hE0
    have hlow : α * (a / Real.sqrt (n : ℝ)) * E = α * a / Real.sqrt (n : ℝ) * E := by ring
    rw [hlow] at hbounds
    have hhalf : α * a / Real.sqrt (n : ℝ) * E - α * a / 2 / Real.sqrt (n : ℝ) * E
        = α * a / 2 / Real.sqrt (n : ℝ) * E := by
      field_simp
      ring
    linarith [hbounds.1, hdiff, hsum, hadd]
  -- the second moment of the upper range, from below
  have hEge : Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3) ≤ E := by
    have h1 := le_integral_normSq_range (X := X) (h := h) hX (m := k + j₀) (n := t)
      (by omega) hkj hσ0' hσt'
    have hcast : scaleCut ((k + j₀ : ℕ) : ℝ) = scaleCut ϑ := by
      congr 1
      rw [hϑ_def]
      push_cast
      ring
    rw [hcast] at h1
    have hct : scaleCut ((t : ℕ) : ℝ) ≤ y := le_trans (scaleCut_mono (by linarith)) hy
    have hϑct : scaleCut ϑ ≤ scaleCut ((t : ℕ) : ℝ) := by
      refine scaleCut_mono ?_
      rw [hϑ_def]
      have : ((k + j₀ : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkj
      push_cast at this
      linarith
    have hsp := setIntegral_normSq_split₂ (X := X) (s := shiftLine σ h) hX hϑct hct
      (A := Set.univ) MeasurableSet.univ (B := Set.univ) MeasurableSet.univ
    rw [Set.univ_inter, setIntegral_univ, setIntegral_univ, setIntegral_univ] at hsp
    have h2 := one_le_integral_normSq_Ico hX (scaleCut ((t : ℕ) : ℝ)) y (shiftLine σ h)
    have hcast2 : (t : ℝ) - ((k + j₀ : ℕ) : ℝ) - 3 = (t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3 := by
      push_cast
      ring
    rw [hcast2] at h1
    have h3 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => X p ω) (scaleCut ϑ) (scaleCut ((t : ℕ) : ℝ))
        (shiftLine σ h) ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
    rw [hE_def, hsp]
    nlinarith [h1, h2, h3, mul_le_mul_of_nonneg_left h2 h3]
  -- put the two factors together
  have hfac1nonneg : (0 : ℝ) ≤ Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) := by positivity
  have hfac2nonneg : (0 : ℝ) ≤ α * a / 2 / Real.sqrt (n : ℝ) * E := by positivity
  have hprod := mul_le_mul hfac1 hfac2 hfac2nonneg
    (setIntegral_nonneg (measurableSet_of_primeAlgebra hX hmBox) fun ω _ => by positivity)
  refine le_trans ?_ hprod
  -- and the numeric comparison
  have hsqle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((t : ℝ) - (k : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hncast]
    linarith [Nat.cast_nonneg (α := ℝ) j₀]
  have hsqt : (0 : ℝ) < Real.sqrt ((t : ℝ) - (k : ℝ)) := lt_of_lt_of_le hsqn hsqle
  have hEsplit : Real.exp ((t : ℝ) - (k : ℝ)) * Real.exp (-((j₀ : ℝ) + 3))
      = Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnum0 : (0 : ℝ) ≤ Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2)
      * Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3) := by positivity
  calc Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2) * Real.exp (-((j₀ : ℝ) + 3))
        * Real.exp ((t : ℝ) - (k : ℝ)) / Real.sqrt ((t : ℝ) - (k : ℝ))
      = Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2)
          * Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3)
          / Real.sqrt ((t : ℝ) - (k : ℝ)) := by
        rw [← hEsplit]
        ring
    _ ≤ Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2)
          * Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3) / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_left hnum0 hsqn hsqle
    _ ≤ Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2 / Real.sqrt (n : ℝ) * E) := by
        rw [div_eq_mul_inv]
        have hmul := mul_le_mul_of_nonneg_left hEge
          (by positivity : (0 : ℝ) ≤ Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1)
            * (α * a / 2) * (Real.sqrt (n : ℝ))⁻¹)
        calc Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2)
              * Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3) * (Real.sqrt (n : ℝ))⁻¹
            = Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2)
                * (Real.sqrt (n : ℝ))⁻¹ * Real.exp ((t : ℝ) - (k : ℝ) - (j₀ : ℝ) - 3) := by ring
          _ ≤ Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1) * (α * a / 2)
                * (Real.sqrt (n : ℝ))⁻¹ * E := hmul
          _ = Real.exp (-(2 * C₁)) * (1 / 2 : ℝ) ^ (j₀ + 1)
                * (α * a / 2 / Real.sqrt (n : ℝ) * E) := by
              rw [div_eq_mul_inv]
              ring

end Assembly

end RMF
