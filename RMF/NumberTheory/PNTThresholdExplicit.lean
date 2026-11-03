/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.MediumPNTThreshold
import RMF.NumberTheory.ThetaMedium

/-!
# The effective prime number theorem's thresholds, named

With `RMF.MediumPNTConstantExplicit` the threshold of the effective prime number theorem is
`exp RMF.mediumPNTThresholdL`, and the statements here carry it up by name:

* `RMF.thetaExpThreshold = max (exp mediumPNTThresholdL) (exp 100)`, past which
  `|θ x - x| ≤ 10⁴⁰ x e^{-(1/200)(log x)^{1/10}}` and `|θ t - t| ≤ thetaMediumConst·t/log² t`;
* `RMF.blockCosineThreshold = max thetaExpThreshold e`, past which the block cosine sums obey
  the numeral estimate `RMF.abs_cos_prime_sum_block_le_threshold_numeral_explicit`.
-/

open Filter Asymptotics Real Chebyshev

namespace RMF

/-- **The effective PNT's threshold for `θ`**: `exp RMF.mediumPNTThresholdL`, pushed up to
`e¹⁰⁰` for the `ψ → θ` bridge. -/
noncomputable def thetaExpThreshold : ℝ := max (Real.exp mediumPNTThresholdL) (Real.exp 100)

/-- **The block cosine estimates' threshold**, `max RMF.thetaExpThreshold e`. -/
noncomputable def blockCosineThreshold : ℝ := max thetaExpThreshold (Real.exp 1)

/-- **The effective PNT for `θ`, past `RMF.thetaExpThreshold`**: `2 ≤ RMF.thetaExpThreshold`, and
`|θ x - x| ≤ 10⁴⁰ x exp(-(1/200)(log x)^{1/10})` for every `x ≥ RMF.thetaExpThreshold`. -/
theorem abs_theta_sub_le_exp_numeral_explicit :
    2 ≤ thetaExpThreshold ∧ ∀ x ≥ thetaExpThreshold,
      |θ x - x|
        ≤ 10 ^ (40 : ℕ) * (x * Real.exp (-(1 / 200 : ℝ) * Real.log x ^ ((1 : ℝ) / 10))) := by
  have hN := MediumPNTConstantExplicit
  set N := Real.exp mediumPNTThresholdL with hN_def
  rw [show thetaExpThreshold = max N (Real.exp 100) from rfl]
  have he100 : (2 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  refine ⟨le_trans he100 (le_max_right _ _), fun x hx => ?_⟩
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 100 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 100) hxe
  have hx1 : (1 : ℝ) ≤ x := by linarith
  set L : ℝ := Real.log x with hLdef
  have hL100 : (100 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos 100) hxe
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hxE0 : (0 : ℝ) ≤ x * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)) := by positivity
  -- the PNT half, with its numeral
  have hpsi : |ψ x - x|
      ≤ 10 ^ (39 : ℕ) * (x * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10))) := by
    have h := hN x hxN
    rw [show ((ψ - id : ℝ → ℝ) x) = ψ x - x from rfl, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤
        x * Real.exp (-(1 / 200 : ℝ) * Real.log x ^ ((1 : ℝ) / 10)))] at h
    exact h
  -- the bridge, absorbed into the same shape
  have hrpow : L ^ ((1 : ℝ) / 10) ≤ L := by
    calc L ^ ((1 : ℝ) / 10) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hsqrt : Real.sqrt x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, hLdef]
    congr 1
    ring
  have hxexp : x = Real.exp L := (Real.exp_log hx0).symm
  have hquad : 2 * L ≤ Real.exp (0.495 * L) := by
    have h1 : 1 + 0.2475 * L ≤ Real.exp (0.2475 * L) := by
      linarith [Real.add_one_le_exp (0.2475 * L)]
    have h2 : Real.exp (0.495 * L) = Real.exp (0.2475 * L) * Real.exp (0.2475 * L) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h2]
    nlinarith [h1, hL100]
  have hbridge : 2 * Real.sqrt x * L
      ≤ x * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)) := by
    have hstep : Real.exp (0.495 * L) * Real.exp (L / 2)
        ≤ Real.exp L * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hrpow, hL100]
    calc 2 * Real.sqrt x * L = 2 * L * Real.exp (L / 2) := by rw [hsqrt]; ring
      _ ≤ Real.exp (0.495 * L) * Real.exp (L / 2) :=
          mul_le_mul_of_nonneg_right hquad (Real.exp_pos _).le
      _ ≤ Real.exp L * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)) := hstep
      _ = x * Real.exp (-(1 / 200 : ℝ) * L ^ ((1 : ℝ) / 10)) := by rw [← hxexp]
  have hdiff : |ψ x - θ x| ≤ 2 * Real.sqrt x * L :=
    Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hsplit : |θ x - x| ≤ |ψ x - x| + |ψ x - θ x| := by
    have heq : θ x - x = (ψ x - x) - (ψ x - θ x) := by ring
    rw [heq]
    exact abs_sub _ _
  have h10 : (10 : ℝ) ^ (39 : ℕ) + 1 ≤ 10 ^ (40 : ℕ) := by norm_num
  nlinarith [hsplit, hpsi, hdiff, hbridge, hxE0, h10]

/-- **`θ` against `t/log² t`, past `RMF.thetaExpThreshold`**:
`|θ t - t| ≤ RMF.thetaMediumConst·t/log² t` for every `t ≥ RMF.thetaExpThreshold`. -/
theorem abs_theta_sub_le_medium_explicit :
    2 ≤ thetaExpThreshold ∧ ∀ t : ℝ, thetaExpThreshold ≤ t →
      |Chebyshev.theta t - t| ≤ thetaMediumConst * t / Real.log t ^ 2 := by
  obtain ⟨hx₀2, hx₀⟩ := abs_theta_sub_le_exp_numeral_explicit
  refine ⟨hx₀2, fun t ht => ?_⟩
  have ht2 : (2 : ℝ) ≤ t := le_trans hx₀2 ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hL : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hbound := hx₀ t ht
  have hdecay := sq_mul_exp_neg_rpow_tenth_le (c := 1 / 200) (by norm_num) hL.le
  have hc20 : ((1 : ℝ) / 200) ^ 20 = 1 / 200 ^ (20 : ℕ) := by norm_num
  rw [hc20, div_div_eq_mul_div, div_one] at hdecay
  -- `e^{-cu} ≤ 20!·200²⁰ / log² t`
  have hexp : Real.exp (-(1 / 200 : ℝ) * Real.log t ^ ((1 : ℝ) / 10))
      ≤ 2432902008176640000 * 200 ^ (20 : ℕ) / Real.log t ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact hdecay
  refine le_trans hbound ?_
  rw [thetaMediumConst]
  calc 10 ^ (40 : ℕ) * (t * Real.exp (-(1 / 200 : ℝ) * Real.log t ^ ((1 : ℝ) / 10)))
      ≤ 10 ^ (40 : ℕ) * (t * (2432902008176640000 * 200 ^ (20 : ℕ) / Real.log t ^ 2)) := by
        gcongr
    _ = 10 ^ (40 : ℕ) * (2432902008176640000 * 200 ^ (20 : ℕ)) * t / Real.log t ^ 2 := by
        ring

/-- **The block cosine sum from an effective PNT for `θ`**: if
`|θ x - x| ≤ C₀ x e^{-c(log x)^{1/10}}` for `x ≥ x₀ ≥ 2`, then for `τ > 0`, `max x₀ e ≤ y₁ ≤ y₂`
and `log y₂ ≤ 3 log y₁`,
`|∑_{y₁<p≤y₂} cos(τ log p)/p| ≤ 3/(τ log y₁) + 32 C₀ (τ + 1) e^{-c(log y₁)^{1/10}}`. -/
theorem abs_cos_prime_sum_block_le_threshold_of_le {c C₀ : ℝ} (hc0 : 0 < c)
    (hC₀ : 0 ≤ C₀)
    {x₀ : ℝ} (hx₀2 : 2 ≤ x₀) (hE : ∀ x ≥ x₀,
      |θ x - x| ≤ C₀ * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) :
      ∀ τ : ℝ, 0 < τ → ∀ y₁ y₂ : ℝ, max x₀ (Real.exp 1) ≤ y₁ → y₁ ≤ y₂ →
        Real.log y₂ ≤ 3 * Real.log y₁ →
        |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
          ≤ 3 / (τ * Real.log y₁)
            + 32 * C₀ * (τ + 1) * Real.exp (-c * Real.log y₁ ^ ((1 : ℝ) / 10)) := by
  intro τ hτ y₁ y₂ hy₁ hy hlog2
  have hy₁x₀ : x₀ ≤ y₁ := le_trans (le_max_left _ _) hy₁
  have hy₁e : Real.exp 1 ≤ y₁ := le_trans (le_max_right _ _) hy₁
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hx₀2 hy₁x₀
  set L : ℝ := Real.log y₁ with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) hy₁e
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < L := by linarith
  have hr0 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hL0.le _
  set E : ℝ := Real.exp (-c * L ^ ((1 : ℝ) / 10)) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set Cy : ℝ := 9 * C₀ * E * L ^ 2 with hCydef
  have hCy0 : (0 : ℝ) ≤ Cy := by positivity
  -- the exponential error, in the shape the block estimate consumes
  have hEy : ∀ t : ℝ, y₁ ≤ t → t ≤ y₂ →
      |Chebyshev.theta t - t| ≤ Cy * t / Real.log t ^ 2 := by
    intro s hs1 hs2
    have hs0 : (0 : ℝ) < s := by linarith
    have hLs : L ≤ Real.log s := Real.log_le_log (by linarith) hs1
    have hLs0 : (0 : ℝ) < Real.log s := by linarith
    have hLs2 : Real.log s ≤ 3 * L := le_trans (Real.log_le_log (by linarith) hs2) hlog2
    have h1 := hE s (le_trans hy₁x₀ hs1)
    have h2 : Real.exp (-c * Real.log s ^ ((1 : ℝ) / 10)) ≤ E := by
      refine Real.exp_le_exp.2 ?_
      have h3 : L ^ ((1 : ℝ) / 10) ≤ Real.log s ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow hL0.le hLs (by norm_num)
      nlinarith
    have h4 : |Chebyshev.theta s - s| ≤ C₀ * s * E := by
      have h5 : C₀ * (s * Real.exp (-c * Real.log s ^ ((1 : ℝ) / 10))) ≤ C₀ * (s * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hs0.le) hC₀
      nlinarith
    have h6 : C₀ * s * E ≤ Cy * s / Real.log s ^ 2 := by
      rw [hCydef, le_div_iff₀ (by positivity)]
      have h7 : Real.log s ^ 2 ≤ 9 * L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hC₀ hs0.le) hE0.le]
    linarith
  refine (abs_cos_prime_sum_block_le hτ hCy0 hEy hy₁2 hy).trans ?_
  -- `2Cy/L³ = 18C₀E/L` and `Cy(τ+3)/(2L²) = (9/2)C₀E(τ+3)`; `L ≥ 1` folds the first in
  have hCE : (0 : ℝ) ≤ C₀ * E := mul_nonneg hC₀ hE0.le
  have h1 : 2 * Cy / L ^ 3 = 18 * (C₀ * E) / L := by rw [hCydef]; field_simp; ring
  have h2 : Cy * (|τ| + 3) / (2 * L ^ 2) = 9 / 2 * (C₀ * E) * (τ + 3) := by
    rw [abs_of_pos hτ, hCydef]; field_simp
  have h3 : 18 * (C₀ * E) / L ≤ 18 * (C₀ * E) := by
    rw [div_le_iff₀ hL0]; nlinarith
  rw [h1, h2]
  nlinarith [h3, hCE, hτ.le, mul_nonneg hCE hτ.le]

/-- **The block cosine sum in numerals, past `RMF.blockCosineThreshold`**:
`RMF.abs_cos_prime_sum_block_le_threshold_of_le` at `C₀ = 10⁴⁰` and `c = 1/200`. -/
theorem abs_cos_prime_sum_block_le_threshold_numeral_explicit :
    2 ≤ blockCosineThreshold ∧
      ∀ τ : ℝ, 0 < τ → ∀ y₁ y₂ : ℝ, blockCosineThreshold ≤ y₁ → y₁ ≤ y₂ →
        Real.log y₂ ≤ 3 * Real.log y₁ →
        |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
          ≤ 3 / (τ * Real.log y₁)
            + 32 * 10 ^ (40 : ℕ) * (τ + 1)
                * Real.exp (-(1 / 200 : ℝ) * Real.log y₁ ^ ((1 : ℝ) / 10)) := by
  obtain ⟨h2, hE⟩ := abs_theta_sub_le_exp_numeral_explicit
  exact ⟨le_trans h2 (le_max_left _ _),
    abs_cos_prime_sum_block_le_threshold_of_le (by norm_num) (by positivity) h2 hE⟩

end RMF
