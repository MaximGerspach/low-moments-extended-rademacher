/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.NumberTheory.StrongBlockCosine
import RMF.NumberTheory.StrongPNT
import RMF.PNTPlus.MediumPNTExplicit

/-!
# The block cosine bound, at the effective PNT rate

The threshold form of the cosine prime sum bound replaces the `K/(τ\log y₁)` decay by a main term
`3/(τ\log y₁)` plus an exponentially small PNT term, with no height condition.  This file carries
it from the intervals `(y₁, y₂]` up to the prime blocks `RMF.primeBlockSub θ m`.  The interval
bound is a hypothesis here; `RMF.abs_cos_prime_sum_block_weight_le_blockCosineThreshold` supplies
it past `y₀ = RMF.blockCosineThreshold`.

## Main results

* `RMF.abs_sum_cos_primeBlockSub_rpow_le_of_weight_bound_of_nonneg`: the block form, past any
  threshold `y₀ ≥ 2`.
-/

open Filter Asymptotics Real

namespace RMF

/-- **The block form of the threshold cosine bound, at any threshold `y₀ ≥ 2`**: the interval
bound `h28` past `y₀` gives the `RMF.primeBlockSub` bound past the block `\log\log y₀`. -/
theorem abs_sum_cos_primeBlockSub_rpow_le_of_weight_bound_of_nonneg {y₀ : ℝ} (hy₀2 : 2 ≤ y₀)
    (h28 : ∀ τ : ℝ, 0 < τ → ∀ σ y₁ y₂ : ℝ, 0 ≤ σ → y₀ ≤ y₁ → y₁ ≤ y₂ →
        Real.log y₂ ≤ 3 * Real.log y₁ →
      |∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log p) / (p : ℝ) ^ (1 + 2 * σ)|
        ≤ 3 / (τ * Real.log y₁)
            + 32 * 10 ^ (40 : ℕ) * (τ + 1)
                * Real.exp (-(1 / 200 : ℝ) * Real.log y₁ ^ ((1 : ℝ) / 10)))
    (τ σ θ : ℝ) (m : ℕ) (hτ : 0 < τ) (hσ0 : 0 ≤ σ)
    (hm : Real.log (Real.log y₀) ≤ (m : ℝ) + θ) :
    |∑ p ∈ primeBlockSub θ m,
        Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)|
      ≤ 3 / (τ * Real.exp ((m : ℝ) + θ))
        + 32 * 10 ^ (40 : ℕ) * (τ + 1)
            * Real.exp (-(1 / 200 : ℝ) * Real.exp (((m : ℝ) + θ) / 10)) := by
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
  have hratio : Real.log (blockScale θ (m + 1)) ≤ 3 * Real.log y₁ := by
    rw [hlogX, hlogy₁, show ((m : ℝ) + 1) + θ = 1 + ((m : ℝ) + θ) by ring, Real.exp_add]
    have hpos : (0 : ℝ) < Real.exp ((m : ℝ) + θ) := Real.exp_pos _
    nlinarith [Real.exp_one_lt_d9]
  have hrw : ∀ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) ^ (1 + 2 * σ) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show (-1 - 2 * σ : ℝ) = -(1 + 2 * σ) by ring, Real.rpow_neg hp0.le]
    ring
  rw [Finset.sum_congr rfl hrw]
  have hrw2 : (∑ p ∈ primeBlockSub θ m,
      Real.cos (τ * Real.log ((p : ℕ) : ℝ)) / (((p : ℕ) : ℝ)) ^ (1 + 2 * σ))
      = ∑ p ∈ Finset.Ioc ⌊y₁⌋₊ ⌊blockScale θ (m + 1)⌋₊ with Nat.Prime p,
          Real.cos (τ * Real.log (p : ℝ)) / ((p : ℝ)) ^ (1 + 2 * σ) := by
    rw [primeBlockSub, harperBlock,
      sum_primesIcoSub _ _ fun q => Real.cos (τ * Real.log (q : ℝ)) / ((q : ℝ)) ^ (1 + 2 * σ),
      filter_prime_Ioc_eq_primesIco]
  rw [hrw2]
  refine le_trans (h28 τ hτ σ y₁ (blockScale θ (m + 1)) hσ0 hy₀y₁ hy₁y₂ hratio) ?_
  have hEeq : Real.exp ((m : ℝ) + θ) ^ ((1 : ℝ) / 10) = Real.exp (((m : ℝ) + θ) / 10) := by
    rw [← Real.exp_mul]
    ring_nf
  rw [hlogy₁, hEeq]

end RMF
