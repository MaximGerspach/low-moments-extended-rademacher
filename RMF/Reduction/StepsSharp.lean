/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.StepsExplicit

/-!
# Step (h2) as an identity

`RMF.reduction_core` charges the large range `(C_s/π)^q`, and a factor `2` of that is step (h2).
The sieve bounds the fibre `⌊x/m⌋ = r` by `C_s x/(r(r+1) log y)`; the proof weakens `1/(r(r+1))` to
`1/r²`, and `RMF.sum_normSq_div_sq_le` buys it back at the price `2`.  But `A` is constant on
`[r, r+1)`, so `∫_r^{r+1} |A(t)|²/t² dt = |A(r)|²/(r(r+1))` exactly
(`RMF.integral_normSq_smoothPartial_unit`).  With the fibre weights kept, the Riemann sum is the
integral (`RMF.sum_normSq_div_mul_succ_eq`), and the large range costs only `(C_s/2π)^q`
(`RMF.reduction_core_window`).
-/

open MeasureTheory Filter Set
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Step (h2), exactly -/

omit [MeasurableSpace Ω] in
/-- **Step (h2) as an identity.**  `A` is constant on `[r, r+1)`, so with the fibre weights
`1/(r(r+1))` the Riemann sum is the integral:
`∑_{r ≤ R} |A(r)|²/(r(r+1)) = ∫_1^{R+1} |A(t)|²/t² dt`.  `RMF.sum_normSq_div_sq_le` has the
weights `1/r²` and pays `2`. -/
lemma sum_normSq_div_mul_succ_eq {f : Ω → ArithmeticFunction ℂ} (y : ℕ) (R : ℕ) (ω : Ω) :
    ∑ r ∈ Finset.Icc 1 R, ‖smoothPartial f y (r : ℝ) ω‖ ^ 2 / ((r : ℝ) * ((r : ℝ) + 1))
      = ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
  have hadj : ∑ k ∈ Finset.range R,
      (∫ t in ((k : ℝ) + 1)..((k : ℝ) + 1 + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      = ∫ t in (1 : ℝ)..((R : ℝ) + 1), ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) + 1) (n := R)
      (f := fun t : ℝ => ‖smoothPartial f y t ω‖ ^ 2 / t ^ 2)
      (fun k _ => intervalIntegrable_normSq_smoothPartial f y ω
        (by positivity) (by push_cast; linarith))
    simpa using h
  rw [← hadj]
  have hIcc : Finset.Icc 1 R = (Finset.range R).image (· + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨m - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have hinj : ∀ a ∈ Finset.range R, ∀ b ∈ Finset.range R, a + 1 = b + 1 → a = b := by
    intro a _ b _ h
    omega
  rw [hIcc, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hkey := integral_normSq_smoothPartial_unit (f := f) y (Nat.succ_pos k) ω
  push_cast at hkey ⊢
  rw [hkey]

end RMF
