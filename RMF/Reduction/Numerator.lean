/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.MaximalBarrier
import RMF.Probability.RestrictedFirstMoment

/-!
# The numerator of the Paley–Zygmund step

Paley–Zygmund wants `E[X]` from *below*, at `X = ∫_L |F(1/2+σ+it)|² dt` and `σ = 4V/\log x`.  The
restricted first moment (`RMF.exists_le_integral_restricted_normSq_of_top`) supplies the barrier
restriction:

`|T|·α·\min(1, a/√n)·E‖F(1/2+σ)‖²  ≤  E[X]`,

which is a lower bound on `E[X]` *relative to* `E‖F(1/2+σ)‖²`.  This file supplies the other
half, a lower bound on `E‖F(1/2+σ)‖²` itself.

## The `V`-dependence

`E‖F_y(1/2+σ)‖² = ∏_{p<y}(1 - p^{-1-2σ})^{-1}` exactly
(`RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq'`).  At `σ = 0` Mertens III makes that
`≍ \log y`.  **At `σ = 4V/\log y` it is not**: the tilt thins the top of the range, and the truth
is `≍ \log y / V`.

## Where the `V` goes, and why it is uniform

`\log E‖F‖² ≥ ∑_{p<y} p^{-1-2σ}`, so what is needed is a *lower* bound on the shifted prime sum,
and `RMF.abs_sum_primesIco_rpow_sub_le_of_le` gives it two-sidedly with a deficit `45√K` at tilt
scale `K`.  Used directly that would cost `e^{-45√K}` — an absolute constant for `V` in a
bounded range, but a bad one.

Instead the same **drop** the barrier uses (`RMF.sigma_le_one_of_drop`) is applied here: stop the
prime range `d` blocks short of the top, where `d` is chosen so that the tilt scale there is at
most `1`.  The deficit is then the absolute `45 + O(e^{-θ})`, and the whole `V`-dependence is the
`d` blocks given up — which is `e^{-d} ≍ 1/V`.  So

`E‖F_y(1/2+σ)‖²  ≥  c·\log y / \max(V,1)`,   `c` depending only on the block offset `θ`,

which is the true order, with the `V`-dependence explicit and polynomial rather than hidden in a
constant.  In particular it is uniform on any bounded range of `V`, which is all the assembly
needs — `V` is chosen once, large enough for the lower reduction's subtracted term, and then
fixed.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-! ### The Euler product from below

`∏(1-u_p)^{-1} ≥ \exp(∑ u_p)`, one factor at a time.  Nothing is lost that matters: the
difference is `∑ u_p²/2`, which converges. -/

/-- `e^u ≤ (1-u)^{-1}` for `u < 1` — the inequality behind `\log(1-u)^{-1} ≥ u`. -/
lemma exp_le_inv_one_sub {u : ℝ} (h1 : u < 1) : Real.exp u ≤ (1 - u)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - u := by linarith
  have hkey : (1 - u) * Real.exp u ≤ 1 := by
    have h : (1 : ℝ) - u ≤ (Real.exp u)⁻¹ := by
      rw [← Real.exp_neg]
      linarith [Real.add_one_le_exp (-u)]
    calc (1 - u) * Real.exp u ≤ (Real.exp u)⁻¹ * Real.exp u :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos u).le
      _ = 1 := inv_mul_cancel₀ (Real.exp_pos u).ne'
  rw [inv_eq_one_div, le_div_iff₀ hpos, mul_comm]
  exact hkey

/-- **The second moment of the Euler product, from below.**
`E‖F_y(s)‖² ≥ \exp(∑_{p<y} p^{-2σ})`, `σ = \Re s`.

The identity `RMF.IsSteinhausRMF.integral_norm_randomEulerProduct_sq'` is exact; this is that
product bounded factor by factor. -/
theorem exp_sum_le_integral_norm_randomEulerProduct_sq (hX : IsSteinhausPrimeValues X μ) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    Real.exp (∑ p ∈ Nat.primesBelow y, (p : ℝ) ^ (-2 * s.re))
      ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y s ω‖ ^ 2 ∂μ := by
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  rw [hf.integral_norm_randomEulerProduct_sq' y hs, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  exact exp_le_inv_one_sub (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))

/-! ### The shifted prime sum, with the drop

`RMF.abs_sum_primesIco_rpow_sub_le_of_le` is two-sided with deficit `45√K`.  Applied at `K = 1`
over the range that stops `d` blocks short of the top, the deficit is absolute and the only cost
is the `d` blocks. -/

/-- `e^{-4} ≤ 1/50`, which is all the `θ ≥ 3` threshold is used for. -/
private lemma exp_neg_four_le : Real.exp (-(4 : ℝ)) ≤ 1 / 50 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hrw : Real.exp (4 : ℝ) = Real.exp 1 ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hsq : Real.exp 1 ^ (4 : ℕ) = (Real.exp 1 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
  have h2 : (7.29 : ℝ) ≤ Real.exp 1 ^ (2 : ℕ) := by nlinarith
  have hge : (50 : ℝ) ≤ Real.exp 4 := by
    rw [hrw, hsq]; nlinarith
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 50) hge
  rw [Real.exp_neg, inv_eq_one_div]
  exact h

/-- **The shifted prime sum over the range that stops `d` blocks short**:
`∑_{x_0 < p ≤ x_{n-d}} p^{-1-2σ} ≥ (n - d) - 63`, with the `63` **absolute**: no `V`, no `θ`.

The hypothesis is `|σ|·\log x_{n+1} ≤ e^d`, so `d` is the drop the tilt scale forces, and
`RMF.sigma_le_one_of_drop` turns it into `|σ|·\log x_{n-d+1} ≤ 1` — which is exactly the regime
where the block estimate costs `O(1)` rather than `e^{O(K)}`. -/
theorem le_sum_rpow_primesIco_of_drop {θ σ : ℝ} {n d : ℕ} (hθ : (3 : ℝ) ≤ θ) (hd : d ≤ n)
    (hσ0 : 0 ≤ σ) (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ Real.exp d) :
    ((n : ℝ) - (d : ℝ)) - 63
      ≤ ∑ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (n - d)⌋₊ + 1),
          (p : ℝ) ^ (-1 - 2 * σ) := by
  have hdrop := sigma_le_one_of_drop (θ := θ) (σ := σ) (K := Real.exp d) (n := n) (r := d)
    le_rfl hd hσ
  have hmain := abs_sum_primesIco_rpow_sub_le_of_le (θ := θ) (σ := σ) (K := 1)
    (n := n - d) (j := n - d) hθ (by omega) zero_le_one hσ0 hdrop
  rw [Nat.cast_sub hd] at hmain
  have hb := abs_le.1 hmain
  have hexp : Real.exp (-(1 + θ)) ≤ Real.exp (-(4 : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have he2 : Real.exp 2 ≤ 7.4 := by
    have hrw : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [hrw]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have herr : 45 * √(1 : ℝ) + 120 * Real.exp 2 * Real.exp (-(1 + θ)) ≤ 63 := by
    rw [Real.sqrt_one]
    nlinarith [exp_neg_four_le, Real.exp_pos (-(1 + θ)), Real.exp_pos (2 : ℝ)]
  linarith [hb.1]

/-! ### The two together -/

/-- **The second moment at a shifted abscissa, from below**: `E‖F_y(1/2+σ)‖² ≥ e^{n-d-63}`
whenever the prime range reaches `x_{n-d}`.  Since `\log x_{n-d} = e^{n-d+θ}`, the right-hand side
is `(\log x_{n-d})`-sized up to the factor `e^{-θ-63}`, and the entire `V`-dependence sits in the
`d` blocks given up.  This is the input the numerator needs beside the restricted first moment. -/
theorem le_integral_normSq_of_drop (hX : IsSteinhausPrimeValues X μ) {θ σ : ℝ} {n d y : ℕ}
    (hθ : (3 : ℝ) ≤ θ) (hd : d ≤ n) (hσ0 : 0 ≤ σ)
    (hσ : |σ| * Real.log (blockScale θ (n + 1)) ≤ Real.exp d)
    (hy : ⌊blockScale θ (n - d)⌋₊ + 1 ≤ y) :
    Real.exp (((n : ℝ) - (d : ℝ)) - 63)
      ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y
          (shiftLine σ 0) ω‖ ^ 2 ∂μ := by
  have hre : (shiftLine σ 0).re = 1 / 2 + σ := re_shiftLine σ 0
  have hspos : (0 : ℝ) < (shiftLine σ 0).re := by rw [hre]; linarith
  refine le_trans (Real.exp_le_exp.2 ?_)
    (exp_sum_le_integral_norm_randomEulerProduct_sq hX y hspos)
  -- the sum over the shortened range is a subsum of the sum over `primesBelow y`
  have hsub : primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (n - d)⌋₊ + 1)
      ⊆ Nat.primesBelow y := by
    intro p hp
    rw [mem_primesIco] at hp
    exact Nat.mem_primesBelow.2 ⟨by omega, hp.1⟩
  have hterm : ∀ p ∈ Nat.primesBelow y, (0 : ℝ) ≤ (p : ℝ) ^ (-2 * (shiftLine σ 0).re) :=
    fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hterm p hp
  have hcongr : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (n - d)⌋₊ + 1),
      (p : ℝ) ^ (-2 * (shiftLine σ 0).re) = (p : ℝ) ^ (-1 - 2 * σ) := by
    intro p _
    rw [hre, rpow_neg_two_half_add]
  rw [Finset.sum_congr rfl hcongr] at hle
  exact le_trans (le_sum_rpow_primesIco_of_drop hθ hd hσ0 hσ) hle

/-! ### The numerator, assembled

The restricted first moment (`RMF.exists_le_integral_restricted_normSq_of_top`) with its
second-moment factor replaced by the bound above.  The two fit without adjustment: the `d` it
carries from the decoupling is the same `d` the drop wants, and
`RMF.log_blockScale_harperOffset_top` makes `|σ|·\log x ≤ e^d` *literally* the hypothesis
`RMF.le_integral_normSq_of_drop` asks for.

`4 ≤ D` is what gives `3 ≤ harperOffset D x`, which is the block estimate's own threshold; the
chain exposes it for exactly this. -/

/-- **`RMF.exists_le_integral_restricted_normSq_numerator` with the level left
free.**  Trading the second moment for `e^{(n-d)-63}` raises the level to `max a₀ 0` and leaves
the block offset alone, so a bound `a₀ ≤ N` becomes `max a₀ 0 ≤ max N 0` here. -/
theorem le_integral_restricted_normSq_numerator_of_top.{u} {D₀ : ℕ} {a₀ α : ℝ}
    (hD : 4 ≤ D₀) (hα : 0 < α) (H :
      ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (volume T).toReal * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
                * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ 0) ω‖ ^ 2 ∂ν
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν) :
    ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
    ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
        x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → max a₀ 0 ≤ a →
        MeasurableSet T → volume T ≠ ⊤ →
        (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
          (volume T).toReal
              * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
              * Real.exp (((harperBlockCount D x - d : ℕ) : ℝ) - 63)
            ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                  (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                  (harperBlockCount D x - d)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν := by
  intro D hDD d E₀ hE₀ hEd
  obtain ⟨x₁, H⟩ := H D hDD d E₀ hE₀ hEd
  obtain ⟨x₂, hx₂⟩ := exists_harperThreshold_of_blockCount D d
  refine ⟨max x₁ x₂, ?_⟩
  intro Ω' _ Y ν hY x σ η a T hf hx hσ0 hη0 hηE hσ ha hT hTfin hhf
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_max_right _ _) hx
  have haa₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  obtain ⟨hx1, hDlog, hcount⟩ := hx₂ x hxx₂
  refine le_trans ?_ (H Ω' Y ν hY x σ η a T hf hxx₁ hσ0 hη0 hηE hσ haa₀ hT hTfin hhf)
  -- the block estimate's own threshold, from `4 ≤ D`
  have hθ3 : (3 : ℝ) ≤ harperOffset D x := by
    have hsub := sub_one_le_harperOffset D x
    have hD4 : (4 : ℝ) ≤ (D : ℝ) := by exact_mod_cast le_trans hD hDD
    linarith
  -- the tilt hypothesis, at the top of the block range — literally `|σ|·\log x ≤ e^d`
  have hσtop : |σ| * Real.log (blockScale (harperOffset D x)
      (harperBlockCount D x + 1)) ≤ Real.exp d := by
    rw [log_blockScale_harperOffset_top hx1 hDlog]
    exact le_trans (le_trans hσ hηE) hEd
  -- the prime range reaches the cutoff
  have hxeq : blockScale (harperOffset D x) (harperBlockCount D x + 1) = x :=
    blockScale_harperOffset_top hx1 hDlog
  have hy : ⌊blockScale (harperOffset D x) (harperBlockCount D x - d)⌋₊ + 1 ≤ ⌊x⌋₊ + 1 := by
    have hmono := blockScale_mono (harperOffset D x)
      (show harperBlockCount D x - d ≤ harperBlockCount D x + 1 by omega)
    rw [hxeq] at hmono
    exact Nat.succ_le_succ (Nat.floor_mono hmono)
  have heuler := le_integral_normSq_of_drop hY (θ := harperOffset D x)
    (n := harperBlockCount D x) (d := d) (y := ⌊x⌋₊ + 1) hθ3 hcount hσ0 hσtop hy
  rw [← Nat.cast_sub hcount] at heuler
  have hC0 : (0 : ℝ) ≤ (volume T).toReal
      * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ)))) := by
    refine mul_nonneg ENNReal.toReal_nonneg (mul_nonneg hα.le ?_)
    exact le_min zero_le_one (div_nonneg ha0 (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left heuler hC0

/-- **The numerator of the Paley–Zygmund step**:
`|T|·α·\min(1, a/√(n-d))·e^{(n-d)-63} ≤ E[X]`, `n = harperBlockCount D x`, `α` and `63` absolute.
Beside `RMF.exists_le_integral_restricted_normSq_of_top` the second moment is gone: since
`\log x_n = e^{n+θ}`, `e^{n-d}` is `\log x/(e^θ e^d)`, the true order of `E‖F(1/2+σ)‖²` here.  The
denominator is Harper's Key Proposition 5,
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le`. -/
theorem exists_le_integral_restricted_normSq_numerator :
    ∃ (D₀ : ℕ) (a₀ α : ℝ), 4 ≤ D₀ ∧ 0 < α ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ (d : ℕ) (E₀ : ℝ), 0 ≤ E₀ → E₀ ≤ Real.exp d → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (x σ η a : ℝ) (T : Set ℝ) (hf : ℕ → ℝ),
          x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ → |σ| * Real.log x ≤ η → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ))))
                * Real.exp (((harperBlockCount D x - d : ℕ) : ℝ) - 63)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperOffset D x) m,
                      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y ((p : Nat.Primes) : ℕ) ω))
                    (harperBlockCount D x - d)
                    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))
                  (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊x⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2) ω) ∂ν := by
  obtain ⟨D₀, a₀, α, hD, hα, H⟩ := exists_le_integral_restricted_normSq_of_top
  exact ⟨D₀, max a₀ 0, α, hD, hα,
    le_integral_restricted_normSq_numerator_of_top hD hα H⟩

end RMF
