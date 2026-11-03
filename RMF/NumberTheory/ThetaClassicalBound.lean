/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import PrimeNumberTheoremAnd.Defs
import RMF.NumberTheory.CosinePrimeSum

/-!
# The classical bound on `θ`, in the shape the cosine prime sum consumes

The block cosine estimates take the prime number theorem in the shape

`|θ t - t| ≤ Cθ · t / \log² t`.

An explicit bound of this shape may hold only past a threshold `T₀`.  This file extends it to every
`t ≥ 2`: `RMF.abs_theta_sub_le_of_threshold'` absorbs `[2, T₀]` outright, at a cost of
`\log 4·\log²T₀` in the constant, since `RMF.theta_le_mul_log_four` proves `θ x ≤ x\log 4` from
Mathlib's `primorial_le_four_pow`, which is checked by the kernel.  So an explicit bound starting
at any *numeral* `T₀` is as good as one starting at `2`.  What cannot be absorbed is an
*existential* threshold, such as that of `MediumPNT`: `\log² T₀` would be existential too.
-/

namespace RMF

/-- **A classical bound need not start at `2`.**  A crude `|θ t - t| ≤ κt` on `[2, T₀]` costs
only `κ\log²T₀` in the constant, because `\log² t ≤ \log² T₀` there.  So an explicit bound
starting at any **numeral** `T₀` serves as well as one starting at `2`; an *existential*
threshold does not, since `\log² T₀` would then be existential too.
`RMF.abs_theta_sub_le_of_threshold'` is this with `hlow` discharged. -/
theorem abs_theta_sub_le_of_threshold {Cθ κ T₀ : ℝ} (hκ : 0 ≤ κ)
    (hlow : ∀ t : ℝ, 2 ≤ t → t ≤ T₀ → |Chebyshev.theta t - t| ≤ κ * t)
    (hhigh : ∀ t : ℝ, T₀ ≤ t → |Chebyshev.theta t - t| ≤ Cθ * t / Real.log t ^ 2) :
    ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ max Cθ (κ * Real.log T₀ ^ 2) * t / Real.log t ^ 2 := by
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  by_cases hcase : t ≤ T₀
  · -- below the threshold the crude bound suffices, at `κ log² T₀`
    have hmono : Real.log t ≤ Real.log T₀ := Real.log_le_log ht0 hcase
    have hsq : Real.log t ^ 2 ≤ Real.log T₀ ^ 2 :=
      pow_le_pow_left₀ hlogt.le hmono 2
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.log t ^ 2)]
    calc |Chebyshev.theta t - t| * Real.log t ^ 2
        ≤ (κ * t) * Real.log T₀ ^ 2 := by
          exact mul_le_mul (hlow t ht hcase) hsq (by positivity) (by positivity)
      _ = (κ * Real.log T₀ ^ 2) * t := by ring
      _ ≤ max Cθ (κ * Real.log T₀ ^ 2) * t :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) ht0.le
  · -- above it, the classical bound, weakened to the maximum
    have hge : T₀ ≤ t := le_of_not_ge hcase
    refine le_trans (hhigh t hge) ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le)
      (by positivity)

/-! ### Discharging the crude branch

Chebyshev's upper bound `θ x ≤ x\log 4` gives the crude branch of
`RMF.abs_theta_sub_le_of_threshold` outright, from Mathlib's `primorial_le_four_pow`.
`Chebyshev.psi_upper_clean` in `PrimeNumberTheoremAnd` has the better constant `1.11`, but it
carries `native_decide` axioms. -/

/-- **`θ x ≤ x\log 4`**, from `∏_{p ≤ n} p ≤ 4ⁿ`.  Chebyshev's upper bound, at the kernel. -/
lemma theta_le_mul_log_four {t : ℝ} (ht : 0 ≤ t) : Chebyshev.theta t ≤ Real.log 4 * t := by
  have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht
  have hprim : (primorial ⌊t⌋₊ : ℝ) ≤ (4 : ℝ) ^ (⌊t⌋₊ : ℕ) := by
    exact_mod_cast primorial_le_four_pow ⌊t⌋₊
  have hpos : (0 : ℝ) < (primorial ⌊t⌋₊ : ℝ) := by
    exact_mod_cast primorial_pos ⌊t⌋₊
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc Chebyshev.theta t = Real.log (primorial ⌊t⌋₊) := Chebyshev.theta_eq_log_primorial t
    _ ≤ Real.log ((4 : ℝ) ^ (⌊t⌋₊ : ℕ)) := Real.log_le_log hpos hprim
    _ = (⌊t⌋₊ : ℝ) * Real.log 4 := by rw [Real.log_pow]
    _ ≤ t * Real.log 4 := mul_le_mul_of_nonneg_right hfl hlog4
    _ = Real.log 4 * t := by ring

/-- **`1 ≤ \log 4`**, which is what lets `RMF.theta_le_mul_log_four` bound `|θ t - t|` and not
just `θ t`. -/
lemma one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_d9]

/-- **Chebyshev's bound in the shape the crude branch wants**: `|θ t - t| ≤ t\log 4`. -/
lemma abs_theta_sub_le_mul_log_four {t : ℝ} (ht : 0 ≤ t) :
    |Chebyshev.theta t - t| ≤ Real.log 4 * t := by
  have hup := theta_le_mul_log_four ht
  have h0 := Chebyshev.theta_nonneg t
  have h1 := one_le_log_four
  have ht1 : t ≤ Real.log 4 * t := le_mul_of_one_le_left ht h1
  rw [abs_le]
  constructor <;> linarith

/-- **The threshold form with its crude branch discharged.**  An explicit
`|θ x - x| ≤ Cθ·x/\log²x` past any numeral `T₀` extends to every `x ≥ 2` at a cost of
`\log 4·\log²T₀` — `1.386·900 = 1248` at `T₀ = e³⁰`.  No hypothesis beyond the one past the
threshold, and no `native_decide`. -/
theorem abs_theta_sub_le_of_threshold' {Cθ T₀ : ℝ}
    (hhigh : ∀ t : ℝ, T₀ ≤ t → |Chebyshev.theta t - t| ≤ Cθ * t / Real.log t ^ 2) :
    ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t|
        ≤ max Cθ (Real.log 4 * Real.log T₀ ^ 2) * t / Real.log t ^ 2 :=
  abs_theta_sub_le_of_threshold (Real.log_nonneg (by norm_num))
    (fun t ht _ => abs_theta_sub_le_mul_log_four (by linarith)) hhigh

end RMF
