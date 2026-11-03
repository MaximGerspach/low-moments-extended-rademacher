/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Conditional
import RMF.Weighted.Sieve
import RMF.Weighted.Assembly

/-!
# The small-`q` reduction to a random Euler product

For `0 < q ≤ ½` the moment `E|S(x)|^{2q}` of the weighted Rademacher sum is controlled by the
`q`-th moment of a line integral of the random Euler product, plus three explicit error terms
(`RMF.exists_integral_rpow_weightedRademacherSum_le`).

## The shape of the statement

**The constant is outside the `q` binder** and no hypothesis mentions `q`, so the bound is uniform
in `q`: no step of the argument (conditioning, the peeling of `m = 1`, the truncation, the
smoothing, Parseval) introduces a constant depending on `q`.

**`y` and `σ` are parameters**, under the conditions the steps use: `y₀ ≤ y` for an absolute `y₀`
(the sieve's threshold), `y ≤ x`, `⌊x⌋₊ ≤ primorial y`, and `σ·log(x/y) ≤ 1` (used only to pass
from `dw/w` to `dw/w^{1+2σ}` in the principal term).  There is **no threshold on `x`**.

`⌊x⌋₊ ≤ primorial y` is what `RMF.integral_rpow_weightedRademacherSum_le_eulerProduct` needs to
identify the truncated smooth sum with the Euler product: `primorial y` is the largest squarefree
`y`-smooth number, and the third term below is the tail between `x` and it.  The range
`y ≤ x ≤ primorial y` is non-empty for every `y ≥ 2` (at `y = 10`, `10 ≤ x ≤ 210`) and is
`y ≤ x ≤ e^{(1+o(1))y}` for large `y`.  The application fixes `y = x^{1/(4 log log x)}` and
`σ = 1/log x`; that case is `RMF.exists_integral_rpow_weightedRademacherSum_le_reduction`, where
`⌊x⌋₊ ≤ primorial y` becomes a threshold on `x`.

**The Euler product is kept symbolic**: the statement has `E|F_y(½)|^{2q}` where one could write
`(log y)^{q(2q-1)}`; the two agree by a Mertens estimate.  **No `min{(1-2q)⁻¹, log log x}`
factor**: that belongs to the assembly, once the chaos estimates are inserted.

## Proof

Conditioning (`RMF.integral_rpow_weightedRademacherSum_le`), the peeling of `m = 1`, and the
truncation to the Euler product (`RMF.integral_rpow_weightedRademacherSum_le_eulerProduct`); the
smoothing, the principal term, the error and Parseval are combined in
`RMF.exists_integral_rpow_sum_weightedRoughTerm_le` (`RMF/Weighted/Assembly.lean`).
-/

open Finset MeasureTheory

namespace RMF

/-- The absorption at the end of the reduction: two terms carried through unchanged, and a third
bounded by `C` times the remaining two, all fold into `max 1 C` times their sum. -/
theorem add_add_le_max_one_mul {C a b c d T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hT : T ≤ C * (c + d)) : a + b + T ≤ max 1 C * (c + a + b + d) := by
  have h1 : (1 : ℝ) ≤ max 1 C := le_max_left 1 C
  have h2 : C ≤ max 1 C := le_max_right 1 C
  have e1 : a ≤ max 1 C * a := le_mul_of_one_le_left ha h1
  have e2 : b ≤ max 1 C * b := le_mul_of_one_le_left hb h1
  have e3 : C * c ≤ max 1 C * c := mul_le_mul_of_nonneg_right h2 hc
  have e4 : C * d ≤ max 1 C * d := mul_le_mul_of_nonneg_right h2 hd
  have e5 : C * (c + d) = C * c + C * d := by ring
  have e6 : max 1 C * (c + a + b + d)
      = max 1 C * c + max 1 C * a + max 1 C * b + max 1 C * d := by ring
  linarith

/-- **The small-`q` reduction to a random Euler product.**  For `0 < q ≤ ½`, `y₀ ≤ y ≤ x`,
`⌊x⌋₊ ≤ primorial y`, `σ > 0`, `σ·log(x/y) ≤ 1`:

`E|S(x)|^{2q} ≤ C·(E[Z^q] + E|F_y(½)|^{2q} + (∑ 1/m)^q + (log x/√y + (log y)⁻¹)^q)`,

`Z = (log y)⁻¹ ∫_ℝ |F_y(½+σ+it)/(σ+it)|² dt`, the sum over the squarefree `y`-smooth
`m ∈ (⌊x⌋₊, primorial y]`.  `C` and `y₀` are absolute: independent of `q`, `y`, `σ`, `x` and of
the probability space. -/
theorem exists_integral_rpow_weightedRademacherSum_le :
    ∃ C y₀ : ℝ, 0 < C ∧ 2 ≤ y₀ ∧
      ∀ q : ℝ, 0 < q → 2 * q ≤ 1 →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (y : ℕ) (σ x : ℝ), y₀ ≤ (y : ℝ) → (y : ℝ) ≤ x → ⌊x⌋₊ ≤ primorial y →
        0 < σ → σ * Real.log (x / y) ≤ 1 →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
            ∂μ)
          ≤ C * ((∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
                    ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                      / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
                + (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                      (1 / 2) ω‖ ^ (2 * q) ∂μ)
                + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
                    | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) ^ q
                + (Real.log x / Real.sqrt y + (Real.log y)⁻¹) ^ q) := by
  classical
  obtain ⟨C₅, y₅, hC₅, hy₅, hcomb⟩ := exists_integral_rpow_sum_weightedRoughTerm_le
  refine ⟨max 1 C₅, max y₅ 2, lt_of_lt_of_le one_pos (le_max_left 1 C₅), le_max_right y₅ 2, ?_⟩
  intro q hq0 hq2 Ω' _ X μ hX y σ x hy₀' hyx hxy hσ hσlog
  have hy : 2 ≤ y := by
    have h : (2 : ℝ) ≤ (y : ℝ) := le_trans (le_max_right y₅ 2) hy₀'
    exact_mod_cast h
  have hy₀ : y₅ ≤ (y : ℝ) := le_trans (le_max_left y₅ 2) hy₀'
  haveI := hX.isProbabilityMeasure
  have hq1 : q ≤ 1 := by linarith
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  refine le_trans (integral_rpow_weightedRademacherSum_le_eulerProduct hX y hx1 hxy hq0.le hq2) ?_
  -- the rough squarefree `m > 1` up to `x` satisfy what the combination asks
  have hrough : ∀ r ∈ ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}).erase 1, IsRough y r :=
    fun r hr => ((Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).2).1
  have hone : ∀ r ∈ ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}).erase 1, 1 < r := by
    intro r hr
    have h1 : r ≠ 1 := Finset.ne_of_mem_erase hr
    have h2 : 1 ≤ r :=
      (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).1
    omega
  have hle : ∀ r ∈ ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}).erase 1, (r : ℝ) ≤ x := by
    intro r hr
    have h := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).2
    have hc : (r : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h
    exact le_trans hc (Nat.floor_le hx0)
  refine add_add_le_max_one_mul ?_ ?_ ?_ ?_
    (hcomb q hq0 hq1 Ω' X μ hX y σ x hy hy₀ hyx hσ hσlog _ hrough hone hle)
  · exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  · exact Real.rpow_nonneg (Finset.sum_nonneg fun m _ => by positivity) q
  · exact integral_nonneg fun ω =>
      Real.rpow_nonneg (mul_nonneg (inv_nonneg.2 (Real.log_nonneg (by linarith)))
        (integral_nonneg fun t => by positivity)) q
  · refine Real.rpow_nonneg ?_ q
    have h1 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have h2 : (0 : ℝ) ≤ (Real.log y)⁻¹ := inv_nonneg.2 (Real.log_nonneg (by linarith))
    positivity

end RMF
