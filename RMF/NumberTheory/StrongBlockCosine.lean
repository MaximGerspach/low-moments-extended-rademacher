/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.StrongPNT
import RMF.Probability.RademacherBlockVariance

/-!
# The block cosine bound at Harper's height range

`RMF.exists_abs_sum_cos_primeBlockSub_rpow_le` carries `τ² ≤ e^{m+θ}`, which in the application
reads `D ≳ 2·log(1+|t|)`.  This file restates the same chain against
`RMF.exists_abs_cos_prime_sum_block_le_wide`, giving `τ² ≤ e^{(c/2)e^{(m+θ)/10}}` and hence
`D ≳ 10·log log(1+|t|)` — **Harper's Proposition 6 branch**.

## The restatements

Each is its primed counterpart with the condition changed and one extra block-ratio hypothesis
discharged.  `log (blockScale θ (m+1)) = e·log (blockScale θ (m+1)^{1/e})`, so the ratio is
exactly `e`, which is why `RMF.exists_abs_cos_prime_sum_block_le_wide` asks for `3` rather than
`2`.

Nothing in the underlying estimate changes: `RMF.abs_cos_prime_sum_block_weight_le` and
`RMF.abs_cos_prime_sum_block_le` are reused verbatim, as they are in the primed chain.

The threshold `m₀` is unavoidable: the packaging holds past an absolute `y₀`, and
`log (blockScale θ (m+1)^{1/e}) = e^{m+θ}`, so `y₀ ≤ y₁` is a condition on `m + θ` alone.
-/

open Filter Asymptotics Real

namespace RMF

/-- **The weighted block bound**, past `τ² ≤ log y₁`.  The mirror of
`RMF.exists_abs_cos_prime_sum_block_weight_le'`. -/
theorem exists_abs_cos_prime_sum_block_weight_le_wide :
    ∃ K c y₀ : ℝ, 0 < K ∧ 0 < c ∧ 2 ≤ y₀ ∧
      ∀ τ : ℝ, 0 < τ → ∀ σ y₁ y₂ : ℝ, y₀ ≤ y₁ →
        τ ^ 2 ≤ Real.exp (c / 2 * Real.log y₁ ^ ((1 : ℝ) / 10)) → y₁ ≤ y₂ →
        Real.log y₂ ≤ 3 * Real.log y₁ → |σ| * Real.log y₂ ≤ 1 →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
        ≤ K * (1 + 2 * |σ| * Real.log (y₂ / y₁)) / (τ * Real.log y₁) := by
  obtain ⟨K, c, y₀, hK, hc, hy₀, hbound⟩ := exists_abs_cos_prime_sum_block_le_wide
  refine ⟨Real.exp 2 * K, c, y₀, by positivity, hc, hy₀, ?_⟩
  intro τ hτ σ y₁ y₂ hy₁ hτ2 hy hratio hσ
  have hy₁2 : (2 : ℝ) ≤ y₁ := le_trans hy₀ hy₁
  have hlog₁ : (0 : ℝ) < Real.log y₁ := Real.log_pos (by linarith)
  have hsub : ∀ u ∈ Set.Icc y₁ y₂,
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊u⌋₊ with Nat.Prime p, Real.cos (τ * Real.log p) / p|
        ≤ K / (τ * Real.log y₁) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    refine hbound τ hτ y₁ u hy₁ hu1 ?_ hτ2
    exact le_trans (Real.log_le_log (by linarith) hu2) hratio
  refine (abs_cos_prime_sum_block_weight_le hy₁2 hy hσ hsub).trans (le_of_eq ?_)
  field_simp

/-- **The block cosine sum over `RMF.primeBlockSub`**, past `τ² ≤ e^{m+θ}`.  The mirror of
`RMF.exists_abs_sum_cos_primeBlockSub_le'`.

The block ratio is exactly `e`: `log (blockScale θ (m+1)) = e^{m+1+θ} = e·e^{m+θ}`. -/
theorem exists_abs_sum_cos_primeBlockSub_le_wide :
    ∃ K c m₀ : ℝ, 0 < K ∧ 0 < c ∧ ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → 0 ≤ θ →
      m₀ ≤ (m : ℝ) + θ →
      τ ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + θ) / 10)) →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ)|
        ≤ K / (τ * Real.exp ((m : ℝ) + θ)) := by
  obtain ⟨K₀, c, y₀, hK₀, hc, hy₀2, h28⟩ := exists_abs_cos_prime_sum_block_weight_le_wide
  refine ⟨3 * K₀, c, Real.log (Real.log y₀), by positivity, hc,
    fun τ σ θ m hτ hθ hm hτ2 hσ => ?_⟩
  have hXpos : (0 : ℝ) < blockScale θ (m + 1) := blockScale_pos θ (m + 1)
  set y₁ : ℝ := blockScale θ (m + 1) ^ (Real.exp 1)⁻¹ with hy₁def
  have hlogX : Real.log (blockScale θ (m + 1)) = Real.exp (((m : ℝ) + 1) + θ) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hlogy₁ : Real.log y₁ = Real.exp ((m : ℝ) + θ) := by
    rw [hy₁def, Real.log_rpow hXpos, hlogX,
      show ((m : ℝ) + 1) + θ = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    field_simp
  have hy₁pos : (0 : ℝ) < y₁ := Real.rpow_pos_of_pos hXpos _
  -- the threshold: `y₀ ≤ y₁` is a condition on `m + θ`
  have hy₀0 : (0 : ℝ) < Real.log y₀ := Real.log_pos (by linarith)
  have hy₀y₁ : y₀ ≤ y₁ := by
    have hle : Real.log y₀ ≤ Real.log y₁ := by
      rw [hlogy₁, ← Real.exp_log hy₀0]
      exact Real.exp_le_exp.2 hm
    have h := Real.exp_le_exp.2 hle
    rwa [Real.exp_log (by linarith : (0 : ℝ) < y₀), Real.exp_log hy₁pos] at h
  have hy₁y₂ : y₁ ≤ blockScale θ (m + 1) := by
    rw [← Real.exp_log hy₁pos, ← Real.exp_log hXpos, hlogy₁, hlogX]
    exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))
  -- the condition, transported
  have hτ2' : τ ^ 2 ≤ Real.exp (c / 2 * Real.log y₁ ^ ((1 : ℝ) / 10)) := by
    rw [hlogy₁, ← Real.exp_mul]
    convert hτ2 using 3
    ring_nf
  -- the block ratio is `e < 3`
  have hratio : Real.log (blockScale θ (m + 1)) ≤ 3 * Real.log y₁ := by
    rw [hlogX, hlogy₁, show ((m : ℝ) + 1) + θ = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    have hpos : (0 : ℝ) < Real.exp ((m : ℝ) + θ) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_d9]
  have hrw : (∑ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [primeBlockSub, harperBlock,
      sum_primesIcoSub _ _ fun q => Real.cos (τ * Real.log (q : ℝ)) / ((q : ℝ)) ^ (1 + 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw]
  refine le_trans
    (h28 τ hτ σ y₁ (blockScale θ (m + 1)) hy₀y₁ hτ2' hy₁y₂ hratio hσ) ?_
  have hquot : Real.log (blockScale θ (m + 1) / y₁) ≤ Real.log (blockScale θ (m + 1)) := by
    rw [Real.log_div hXpos.ne' hy₁pos.ne']
    have : (0 : ℝ) ≤ Real.log y₁ := by rw [hlogy₁]; positivity
    linarith
  have habs : (0 : ℝ) ≤ |σ| := abs_nonneg _
  have hnum : 1 + 2 * |σ| * Real.log (blockScale θ (m + 1) / y₁) ≤ 3 := by
    nlinarith [hσ, hquot, habs]
  have hden : (0 : ℝ) < τ * Real.log y₁ := by
    rw [hlogy₁]
    positivity
  rw [hlogy₁] at hden ⊢
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  linarith [mul_le_mul_of_nonneg_left hnum hK₀.le]

/-- **The same, with the weight as a negative `rpow`** — the spelling the drift bound uses.
The mirror of `RMF.exists_abs_sum_cos_primeBlockSub_rpow_le`. -/
theorem exists_abs_sum_cos_primeBlockSub_rpow_le_wide :
    ∃ K c m₀ : ℝ, 0 < K ∧ 0 < c ∧ ∀ (τ σ θ : ℝ) (m : ℕ), 0 < τ → 0 ≤ θ →
      m₀ ≤ (m : ℝ) + θ →
      τ ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + θ) / 10)) →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 →
      |∑ p ∈ primeBlockSub θ m,
          Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
        ≤ K / (τ * Real.exp ((m : ℝ) + θ)) := by
  obtain ⟨K, c, m₀, hK0, hc, hK⟩ := exists_abs_sum_cos_primeBlockSub_le_wide
  refine ⟨K, c, m₀, hK0, hc, fun τ σ θ m hτ hθ hm hτ2 hσ => ?_⟩
  have hrw : ∀ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [Finset.sum_congr rfl hrw]
  exact hK τ σ θ m hτ hθ hm hτ2 hσ

/-- **The block variance bracket, at Harper's height range.**

The mirror of `RMF.exists_sum_re_cpow_neg_sq_primeBlockSub_bounds`, and the second of the two
places the height condition is consumed — the other being the oscillatory pair.  Both bottom out
at the same cosine sum, so both move together. -/
theorem exists_sum_re_cpow_neg_sq_primeBlockSub_bounds_wide :
    ∃ Tsh c m₀ : ℝ, 0 < Tsh ∧ 0 < c ∧ ∀ (θ σ η : ℝ) (m : ℕ) (u : ℂ),
      u.re = 1 / 2 + σ → (9 : ℝ) ≤ (m : ℝ) + θ → m₀ ≤ (m : ℝ) + θ →
      0 ≤ θ → 0 ≤ η → η ≤ 1 / 10 →
      |σ| * Real.log (blockScale θ (m + 1)) ≤ η →
      0 < 2 * u.im →
      (2 * u.im) ^ 2 ≤ Real.exp (c / 2 * Real.exp (((m : ℝ) + θ) / 10)) →
      Tsh ≤ 2 * u.im * Real.exp ((m : ℝ) + θ) →
      1 / 4 ≤ ∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2
        ∧ (∑ p ∈ primeBlockSub θ m, ((((p : ℕ) : ℂ)) ^ (-u)).re ^ 2) ≤ 3 / 4 := by
  obtain ⟨K, c, m₀, hK, hc, hcosbd⟩ := exists_abs_sum_cos_primeBlockSub_le_wide
  refine ⟨10 * K, c, m₀, by positivity, hc, ?_⟩
  intro θ σ η m u hu hmθ hm0 hθ hη hη''' hσ hτ hτ2 hTsh
  have hcos := hcosbd (2 * u.im) σ θ m hτ hθ hm0 hτ2 (by linarith)
  have hprod : (0 : ℝ) < 2 * u.im * Real.exp ((m : ℝ) + θ) := by positivity
  have hsmall : K / (2 * u.im * Real.exp ((m : ℝ) + θ)) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hprod (by norm_num)]
    linarith
  exact sum_re_cpow_neg_sq_primeBlockSub_bounds θ σ η (1 / 10) m hu hmθ hη hη''' hσ le_rfl
    (hcos.trans hsmall)

end RMF
