/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import PrimeNumberTheoremAnd.Consequences

/-!
# A lower bound on the primorial

`RMF.exists_integral_rpow_weightedRademacherSum_le` needs `⌊x⌋₊ ≤ primorial y`, so it needs the
primorial from **below**.  By `Chebyshev.theta_eq_log_primorial` that is a lower bound on `θ`,
and `chebyshev_asymptotic` (`θ ~[atTop] id`, `sorryAx`-free) gives `θ y ≥ y/2` for large `y`.
-/

open Finset MeasureTheory

namespace RMF

/-- **The primorial lower bound.**  `log (primorial y) = θ y ≥ y/2` for large `y`, so `y ≥ 2 log x`
forces `x ≤ primorial y`.  The `θ` bound is `chebyshev_asymptotic`. -/
theorem exists_floor_le_primorial :
    ∃ Y : ℝ, ∀ y : ℕ, Y ≤ (y : ℝ) → ∀ x : ℝ, 1 ≤ x → 2 * Real.log x ≤ (y : ℝ) →
      ⌊x⌋₊ ≤ primorial y := by
  -- `θ ~[atTop] id` unfolds to `(θ - id) =o[atTop] id`; run it at `ε = 1/2` and unpack `atTop`.
  obtain ⟨Y, hY⟩ :=
    Filter.eventually_atTop.mp
      (chebyshev_asymptotic.isLittleO.def (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨Y, fun y hy x hx hlogx => ?_⟩
  have hbound := hY (y : ℝ) hy
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hbound
  rw [abs_of_nonneg (Nat.cast_nonneg y : (0 : ℝ) ≤ (y : ℝ))] at hbound
  -- `|θ y - y| ≤ y/2` gives the lower bound `y/2 ≤ θ y`.
  have hhalf : (y : ℝ) / 2 ≤ Chebyshev.theta (y : ℝ) := by
    have := neg_abs_le (Chebyshev.theta (y : ℝ) - (y : ℝ))
    linarith
  have htheta : Real.log (primorial y) = Chebyshev.theta (y : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hppos : (0 : ℝ) < (primorial y : ℝ) := by exact_mod_cast primorial_pos y
  have hlog : Real.log x ≤ Real.log (primorial y) := by rw [htheta]; linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ (primorial y : ℝ) :=
    (Nat.floor_le hxpos.le).trans ((Real.log_le_log_iff hxpos hppos).mp hlog)
  exact_mod_cast hfl

end RMF
