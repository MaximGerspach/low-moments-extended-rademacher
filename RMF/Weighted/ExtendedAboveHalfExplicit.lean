/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedCombineExplicit
import RMF.Weighted.UniformMomentsExplicit

/-!
# The extended sum at and above `q = ½`, explicit

For `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`, every `x ≥ 3` and `Λ = log log x`:

* `E|Y(x)| ≤ 20Λ^{3/4}` (`RMF.integral_norm_normalisedSum_compMultExtension_le_twenty`), from
  `E|Y| ≤ E|S| + E|R| ≤ 10Λ^{3/4} + 1`;
* `E|Y(x)|^{2q} ≤ 30(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}` for `½ < q ≤ 1`
  (`RMF.integral_rpow_normalisedSum_compMultExtension_le_aboveHalf`): for `Λ ≤ 1` by the trivial
  bound `E|Y|^{2q} ≤ x`, for `1 ≤ Λ ≤ 4` by the second moment,
  `E|Y|^{2q} ≤ (√(1 + log x) + 1)^{2q}`, and for `Λ ≥ 4` by Minkowski against the weighted bound
  with `25` (`RMF.weighted_rademacher_moments_upper_uniform_explicit`) and `E|R|^{2q} ≤ 1`.

Both: `RMF.extended_rademacher_moments_upper_aboveHalf_explicit`.
-/

open MeasureTheory

namespace RMF

/-! ### Numerals -/

/-- `c ≤ Λ^{3/4}` from `ℓ ≤ Λ` and `c⁴ ≤ ℓ³`, for `ℓ ≥ 0`. -/
lemma le_rpow_three_quarters_of_le {Λ ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hℓΛ : ℓ ≤ Λ) (h : c ^ 4 ≤ ℓ ^ 3) :
    c ≤ Λ ^ (3 / 4 : ℝ) := by
  have hΛ : 0 ≤ Λ := hℓ.trans hℓΛ
  have e : (Λ ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = Λ ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (Λ ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hΛ,
      show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine le_of_pow_le_pow_left₀ four_ne_zero (Real.rpow_nonneg hΛ _) ?_
  rw [e]
  exact h.trans (pow_le_pow_left₀ hℓ hℓΛ 3)

/-- `1 ≤ 10Λ^{3/4}` for `x ≥ 3`: `Λ ≥ 0.094` and `10⁻⁴ ≤ 0.094³`. -/
lemma one_le_ten_mul_loglog_rpow {x : ℝ} (hx : 3 ≤ x) :
    1 ≤ 10 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have h := le_rpow_three_quarters_of_le (c := 1 / 10) (by norm_num) (loglog_ge_of_three_le hx)
    (by norm_num)
  linarith

/-- **`x ≤ 30Λ^{3/4}` for `x ≥ 3` and `Λ = log log x ≤ 1`**, on `[3, 5]` and `[5, e^e]`: on each,
`Λ ≥ ℓ` and `x ≤ 30c` with `c⁴ ≤ ℓ³`. -/
lemma le_thirty_mul_loglog_rpow {x : ℝ} (hx : 3 ≤ x) (hΛ : Real.log (Real.log x) ≤ 1) :
    x ≤ 30 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have key : ∀ {a ℓ c : ℝ}, 3 ≤ a → a ≤ x → ℓ ≤ Real.log (Real.log a) → 0 ≤ ℓ →
      c ^ 4 ≤ ℓ ^ 3 → x ≤ 30 * c → x ≤ 30 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
    intro a ℓ c ha hax hℓ hℓ0 hc h
    have hla : Real.log (Real.log a) ≤ Real.log (Real.log x) :=
      Real.log_le_log (lt_of_lt_of_le hl3 (Real.log_le_log (by norm_num) ha))
        (Real.log_le_log (by linarith) hax)
    have := le_rpow_three_quarters_of_le hℓ0 (hℓ.trans hla) hc
    linarith
  rcases le_or_gt x 5 with h1 | h1
  · exact key (a := 3) (ℓ := 94 / 1000) (c := 0.1697) le_rfl hx (loglog_ge_of_three_le le_rfl)
      (by norm_num) (by norm_num) (by linarith)
  · have hn : (0.47 : ℝ) ≤ Real.log (Real.log 5) := by interval_decide (trust := kernel)
    have hee : Real.exp (Real.exp 1) ≤ 15.16 := by interval_decide (trust := kernel)
    have hL : Real.log x ≤ Real.exp 1 :=
      (Real.log_le_iff_le_exp (lt_of_lt_of_le hl3 hlx)).1 hΛ
    have hxe : x ≤ Real.exp (Real.exp 1) := (Real.log_le_iff_le_exp (by linarith)).1 hL
    exact key (a := 5) (ℓ := 0.47) (c := 0.565) (by norm_num) h1.le hn (by norm_num)
      (by norm_num) (by linarith)

/-- **The target for `Λ ≤ 1`**: for `x ≥ 3` with `Λ = log log x ≤ 1` and `½ < q ≤ 1`,
`x ≤ 30(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}`: the `min` is `Λ`, `(log x)^{q(2q-1)} ≥ 1`, and
`x ≤ 30Λ^{3/4}` (`RMF.le_thirty_mul_loglog_rpow`). -/
lemma le_aboveHalf_target_of_loglog_le_one {x q : ℝ} (hx : 3 ≤ x)
    (hΛ : Real.log (Real.log x) ≤ 1) (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    x ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
      * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)) := by
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have hlx : 1 ≤ Real.log x := (hlog3.trans_le (Real.log_le_log (by norm_num) hx)).le
  have hΛ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlx
  have hm : min (2 * q - 1)⁻¹ (Real.log (Real.log x)) = Real.log (Real.log x) :=
    min_eq_right (hΛ.trans ((one_le_inv₀ (by linarith)).2 (by linarith)))
  have h1 : 1 ≤ Real.log x ^ (q * (2 * q - 1)) :=
    Real.one_le_rpow hlx (mul_nonneg (by linarith) (by linarith))
  have h3 : 0 ≤ Real.log (Real.log x) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hΛ0 _
  have h4 : Real.log (Real.log x) ^ (3 / 4 : ℝ)
      ≤ Real.log x ^ (q * (2 * q - 1)) * Real.log (Real.log x) ^ (3 / 4 : ℝ) :=
    le_mul_of_one_le_left h3 h1
  rw [hm]
  linarith [le_thirty_mul_loglog_rpow hx hΛ]

/-- **The second moment against the target for `1 ≤ Λ ≤ 4`**: for `½ < q ≤ 1`,
`(√(1 + log x) + 1)^{2q} ≤ 30(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}`.  In exponents, with
`(√(1 + L) + 1)² ≤ 3.2L` (`L = log x ≥ e`), `δ = 2q - 1` and the `min` at least `1`, it is
`log 3.2 + 2q(1 - q)Λ ≤ log 30`, and `2q(1 - q)Λ ≤ Λ/2 ≤ 2`. -/
lemma secondMoment_le_aboveHalf_target {x q : ℝ} (hx : 3 ≤ x)
    (hΛ1 : 1 ≤ Real.log (Real.log x)) (hΛ4 : Real.log (Real.log x) ≤ 4) (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) :
    (Real.sqrt (1 + Real.log x) + 1) ^ (2 * q)
      ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)) := by
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hL3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le hl3 hL3
  set Λ := Real.log L with hΛdef
  have hLe : Real.exp 1 ≤ L := by
    rw [← Real.exp_log hL0]
    exact Real.exp_le_exp.2 hΛ1
  have hL27 : (2.7 : ℝ) ≤ L := by linarith [Real.exp_one_gt_d9]
  set δ := 2 * q - 1 with hδdef
  have hδ0 : 0 < δ := by linarith
  set m := min δ⁻¹ Λ with hmdef
  have hm1 : 1 ≤ m := le_min ((one_le_inv₀ hδ0).2 (by linarith)) hΛ1
  have hm0 : 0 < m := by linarith
  -- `(√(1 + L) + 1)² ≤ 3.2L`
  set s := Real.sqrt (1 + L) with hsdef
  have hs2 : s ^ 2 = 1 + L := Real.sq_sqrt (by linarith)
  have hs1 : s ≤ 1.1 * L - 1 := by
    have hLL : 2.7 * L ≤ L * L := mul_le_mul_of_nonneg_right hL27 hL0.le
    have h1 : 1 + L ≤ (1.1 * L - 1) ^ 2 := by nlinarith
    calc s ≤ Real.sqrt ((1.1 * L - 1) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 1.1 * L - 1 := Real.sqrt_sq (by linarith)
  have hB : (s + 1) ^ 2 ≤ 3.2 * L := by nlinarith
  have hB0 : 0 < s + 1 := by linarith [Real.sqrt_nonneg (1 + L)]
  have hlogB : 2 * Real.log (s + 1) ≤ Real.log 3.2 + Λ := by
    have h := Real.log_le_log (by positivity) hB
    rw [Real.log_pow, Real.log_mul (by norm_num) hL0.ne', ← hΛdef] at h
    push_cast at h
    linarith
  -- exponentiate
  have n32 : Real.log 3.2 ≤ 1.164 := by interval_decide (trust := kernel)
  have n32' : 0 ≤ Real.log 3.2 := Real.log_nonneg (by norm_num)
  have n30 : (3.401 : ℝ) ≤ Real.log 30 := by interval_decide (trust := kernel)
  have hT0 : 0 < L ^ (q * δ) * m ^ (3 / 4 : ℝ) := by positivity
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hB0 _) (by positivity), Real.log_rpow hB0,
    Real.log_mul (by norm_num) hT0.ne',
    Real.log_mul (Real.rpow_pos_of_pos hL0 _).ne' (Real.rpow_pos_of_pos hm0 _).ne',
    Real.log_rpow hL0, Real.log_rpow hm0, ← hΛdef]
  have hq0' : 0 ≤ q := by linarith
  have h1 : 2 * q * Real.log (s + 1) ≤ q * (Real.log 3.2 + Λ) := by
    have := mul_le_mul_of_nonneg_left hlogB hq0'
    linarith
  have h2 : q * Real.log 3.2 ≤ Real.log 3.2 := mul_le_of_le_one_left n32' hq1
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hqq : 2 * q * (1 - q) ≤ 1 / 2 := by nlinarith [sq_nonneg (2 * q - 1)]
  have h3 : 2 * q * (1 - q) * Λ ≤ 1 / 2 * Λ := mul_le_mul_of_nonneg_right hqq (by linarith)
  have e : q * δ * Λ = q * Λ - 2 * q * (1 - q) * Λ := by rw [hδdef]; ring
  linarith

/-- **Absorbing `1` into `25T`**: for `p > 0`, `T > 0` and `p(log 6 + log p) ≤ log 25 + log T`,
`((25T)^{1/p} + 1)^p ≤ 30T`.  With `A = (25T)^{1/p} ≥ 6p`,
`(A + 1)^p = A^p(1 + 1/A)^p ≤ 25T·e^{p/A} ≤ 25T·e^{1/6} ≤ 30T`. -/
lemma rpow_inv_add_one_rpow_le_thirty {p T : ℝ} (hp0 : 0 < p) (hT : 0 < T)
    (h : p * (Real.log 6 + Real.log p) ≤ Real.log 25 + Real.log T) :
    ((25 * T) ^ p⁻¹ + 1) ^ p ≤ 30 * T := by
  have h25T : 0 < 25 * T := by positivity
  set A := (25 * T) ^ p⁻¹ with hAdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos h25T _
  have hAge : 6 * p ≤ A := by
    have h1 : Real.log (6 * p) ≤ Real.log A := by
      rw [hAdef, Real.log_rpow h25T, inv_mul_eq_div, Real.log_mul (by norm_num) hp0.ne',
        Real.log_mul (by norm_num) hT.ne', le_div_iff₀ hp0]
      linarith
    exact (Real.log_le_log_iff (by positivity) hA0).1 h1
  have hAp : A ^ p = 25 * T := by
    rw [hAdef, ← Real.rpow_mul h25T.le, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hexp : Real.exp (1 / 6) ≤ 6 / 5 := by interval_decide (trust := kernel)
  have h1A : (1 + A⁻¹) ^ p ≤ 6 / 5 := by
    have e1 : 1 + A⁻¹ ≤ Real.exp A⁻¹ := by linarith [Real.add_one_le_exp A⁻¹]
    calc (1 + A⁻¹) ^ p ≤ (Real.exp A⁻¹) ^ p := Real.rpow_le_rpow (by positivity) e1 hp0.le
      _ = Real.exp (A⁻¹ * p) := (Real.exp_mul A⁻¹ p).symm
      _ ≤ Real.exp (1 / 6) := by
          refine Real.exp_le_exp.2 ?_
          rw [inv_mul_eq_div, div_le_div_iff₀ hA0 (by norm_num)]
          linarith
      _ ≤ 6 / 5 := hexp
  calc (A + 1) ^ p = (A * (1 + A⁻¹)) ^ p := by
        rw [mul_add, mul_one, mul_inv_cancel₀ hA0.ne']
    _ = A ^ p * (1 + A⁻¹) ^ p := Real.mul_rpow hA0.le (by positivity)
    _ ≤ 25 * T * (6 / 5) := by
        rw [hAp]
        exact mul_le_mul_of_nonneg_left h1A h25T.le
    _ = 30 * T := by ring

/-- **The absorption condition for `Λ ≥ 4`**: for `½ < q ≤ 1` and `T` the target's rate,
`2q(log 6 + log 2q) ≤ log 25 + log T`.  With `δ = 2q - 1`: `log 2q ≤ δ`, and
`log T = qδΛ + (3/4)log m ≥ 4qδ = 2δ(1 + δ)`, the `min` `m` being at least `1`. -/
lemma absorb_cond_of_four_le_loglog {x q : ℝ} (hx : 3 ≤ x) (hΛ : 4 ≤ Real.log (Real.log x))
    (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) :
    2 * q * (Real.log 6 + Real.log (2 * q))
      ≤ Real.log 25 + Real.log (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)) := by
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hL3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le hl3 hL3
  set Λ := Real.log L with hΛdef
  set δ := 2 * q - 1 with hδdef
  have hδ0 : 0 < δ := by linarith
  set m := min δ⁻¹ Λ with hmdef
  have hm1 : 1 ≤ m := le_min ((one_le_inv₀ hδ0).2 (by linarith)) (by linarith)
  have hm0 : 0 < m := by linarith
  rw [Real.log_mul (Real.rpow_pos_of_pos hL0 _).ne' (Real.rpow_pos_of_pos hm0 _).ne',
    Real.log_rpow hL0, Real.log_rpow hm0, ← hΛdef]
  have n6 : Real.log 6 ≤ 1.792 := by interval_decide (trust := kernel)
  have n25 : (3.218 : ℝ) ≤ Real.log 25 := by interval_decide (trust := kernel)
  have hlp : Real.log (2 * q) ≤ δ := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * q by linarith)
    rw [hδdef]
    linarith
  have hlhs : 2 * q * (Real.log 6 + Real.log (2 * q)) ≤ 2 * q * (1.792 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hqδ : 0 ≤ q * δ := mul_nonneg (by linarith) hδ0.le
  have h4 : q * δ * 4 ≤ q * δ * Λ := mul_le_mul_of_nonneg_left hΛ hqδ
  have e4 : q * δ * 4 = 2 * δ * (1 + δ) := by rw [hδdef]; ring
  have e2 : 2 * q * (1.792 + δ) = (1 + δ) * (1.792 + δ) := by rw [hδdef]; ring
  nlinarith

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### `q = ½` -/

/-- **The first moment of the extended sum with the constant `20`**: for every `x ≥ 3`,
`E|x^{-1/2}∑_{n≤x} X^e(n)| ≤ E|S(x)| + E|R(x)| ≤ 10Λ^{3/4} + 1 ≤ 20Λ^{3/4}`
(`RMF.integral_norm_weightedRademacherSum_le_ten_of_three_le`,
`RMF.integral_rpow_norm_fracPartSum_le_one`, `RMF.one_le_ten_mul_loglog_rpow`). -/
theorem integral_norm_normalisedSum_compMultExtension_le_twenty {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 3 ≤ x) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ 20 * Real.log (Real.log x) ^ (3 / 4 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith
  have hY := integral_norm_normalisedSum_compMultExtension_le_add hX hx1
  have hS := integral_norm_weightedRademacherSum_le_ten_of_three_le hX hx
  have hR := integral_rpow_norm_fracPartSum_le_one hX hx1 (q := 1 / 2) (by norm_num)
    (by norm_num)
  simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at hR
  have h10 := one_le_ten_mul_loglog_rpow hx
  linarith

/-! ### Above `q = ½` -/

/-- **The trivial bound, crudely**: `E|Y(x)|^{2q} ≤ (⌊x⌋/√x)^{2q} ≤ x` for `x ≥ 1` and
`0 ≤ q ≤ 1` (`RMF.integral_rpow_norm_normalisedSum_compMultExtension_le_floor`). -/
theorem integral_rpow_normalisedSum_compMultExtension_le_self {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hfl : (⌊x⌋₊ : ℝ) / Real.sqrt x ≤ Real.sqrt x := by
    rw [div_le_iff₀ hs0, Real.mul_self_sqrt hx0]
    exact Nat.floor_le hx0
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ ((⌊x⌋₊ : ℝ) / Real.sqrt x) ^ (2 * q) :=
        integral_rpow_norm_normalisedSum_compMultExtension_le_floor hX x hq0
    _ ≤ Real.sqrt x ^ (2 * q) :=
        Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) hs0.le) hfl (by linarith)
    _ ≤ Real.sqrt x ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (Real.one_le_sqrt.2 hx) (by linarith)
    _ = x := by rw [Real.rpow_two, Real.sq_sqrt hx0]

/-- **The second moment**: for `x ≥ 1` and `0 ≤ q ≤ 1`,
`E|Y(x)|^{2q} ≤ (E|Y(x)|²)^q ≤ (√(1 + log x) + 1)^{2q}`, by Minkowski at `q = 1` with
`E|S(x)|² ≤ 1 + log x` and `E|R(x)|² ≤ 1`. -/
theorem integral_rpow_normalisedSum_compMultExtension_le_secondMoment {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (Real.sqrt (1 + Real.log x) + 1) ^ (2 * q) := by
  haveI := hX.isProbabilityMeasure
  have hJ := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := 1) (q := q) hq0 hq1
    (memLp_normalisedSum_compMultExtension hX x _)
  have hM := integral_rpow_norm_normalisedSum_compMultExtension_le_minkowski hX hx (q := 1)
    (by norm_num)
  have hS2 := integral_normSq_weightedRademacherSum_le_one_add_log hX.isRademacherRMF hx
  have hR2 := integral_normSq_fracPartSum_le_one hX.isRademacherRMF hx
  simp only [mul_one, div_one, Real.rpow_two] at hJ hM
  have hS0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hR0 : 0 ≤ ∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hY0 : 0 ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hSs : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ 2 ∂μ) ^ (2⁻¹ : ℝ) ≤ Real.sqrt (1 + Real.log x) := by
    rw [Real.sqrt_eq_rpow, one_div]
    exact Real.rpow_le_rpow hS0 hS2 (by norm_num)
  have hRs : (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2 ∂μ)
      ^ (2⁻¹ : ℝ) ≤ 1 := by
    calc _ ≤ (1 : ℝ) ^ (2⁻¹ : ℝ) := Real.rpow_le_rpow hR0 hR2 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hY2 : (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2 ∂μ)
      ≤ (Real.sqrt (1 + Real.log x) + 1) ^ 2 :=
    hM.trans (pow_le_pow_left₀ (by positivity) (add_le_add hSs hRs) 2)
  calc (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2 ∂μ) ^ q :=
        hJ
    _ ≤ ((Real.sqrt (1 + Real.log x) + 1) ^ 2) ^ q := Real.rpow_le_rpow hY0 hY2 hq0
    _ = (Real.sqrt (1 + Real.log x) + 1) ^ (2 * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-- **The extended sum above `q = ½` with the constant `30`**: for every `x ≥ 3` and
`½ < q ≤ 1`, `E|Y(x)|^{2q} ≤ 30(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}`.  For `Λ ≤ 1`,
`E|Y|^{2q} ≤ x` (`RMF.le_aboveHalf_target_of_loglog_le_one`); for `1 ≤ Λ ≤ 4`, the second moment
(`RMF.secondMoment_le_aboveHalf_target`); for `Λ ≥ 4`, Minkowski with `E|S|^{2q} ≤ 25T`
(`RMF.weighted_rademacher_moments_upper_uniform_explicit`) and `E|R|^{2q} ≤ 1`
(`RMF.rpow_inv_add_one_rpow_le_thirty`, `RMF.absorb_cond_of_four_le_loglog`). -/
theorem integral_rpow_normalisedSum_compMultExtension_le_aboveHalf {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 3 ≤ x) (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)) := by
  have hx1 : 1 ≤ x := by linarith
  rcases le_or_gt (Real.log (Real.log x)) 1 with h1 | h1
  · exact (integral_rpow_normalisedSum_compMultExtension_le_self hX hx1 (by linarith) hq1).trans
      (le_aboveHalf_target_of_loglog_le_one hx h1 hq0 hq1)
  rcases le_or_gt (Real.log (Real.log x)) 4 with h4 | h4
  · exact (integral_rpow_normalisedSum_compMultExtension_le_secondMoment hX hx1 (by linarith)
      hq1).trans (secondMoment_le_aboveHalf_target hx h1.le h4 hq0 hq1)
  -- `Λ > 4`: Minkowski
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 < Real.log x := lt_trans one_pos (hlog3.trans_le (Real.log_le_log (by norm_num) hx))
  have hδ : 0 < 2 * q - 1 := by linarith
  have hT0 : 0 < Real.log x ^ (q * (2 * q - 1))
      * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hL0 _)
      (Real.rpow_pos_of_pos (lt_min (inv_pos.2 hδ) (by linarith)) _)
  have hS := (weighted_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).2.2 q hq0 hq1
  have hR := integral_rpow_norm_fracPartSum_le_one hX hx1 (by linarith : (0 : ℝ) ≤ q) hq1
  have hM := integral_rpow_norm_normalisedSum_compMultExtension_le_minkowski hX hx1 hq0.le
  have hS0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hR0 : 0 ≤ ∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hp : (0 : ℝ) ≤ (2 * q)⁻¹ := inv_nonneg.2 (by linarith)
  have hRs : (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ ≤ 1 := by
    calc _ ≤ (1 : ℝ) ^ (2 * q)⁻¹ := Real.rpow_le_rpow hR0 hR hp
      _ = 1 := Real.one_rpow _
  refine hM.trans (le_trans ?_ (rpow_inv_add_one_rpow_le_thirty (by linarith) hT0
    (absorb_cond_of_four_le_loglog hx h4.le hq0 hq1)))
  exact Real.rpow_le_rpow (by positivity) (add_le_add (Real.rpow_le_rpow hS0 hS hp) hRs)
    (by linarith)

end

/-! ### The theorem -/

/-- **The extended sum at and above `q = ½`, explicit**: for every `x ≥ 3`, with
`Λ = log log x`,

* `E|x^{-1/2}∑_{n≤x} X^e(n)| ≤ 20Λ^{3/4}`;
* `E|x^{-1/2}∑_{n≤x} X^e(n)|^{2q} ≤ 30(log x)^{q(2q-1)}min(1/(2q - 1), Λ)^{3/4}` for `½ < q ≤ 1`.

The second and third cases of `RMF.weighted_rademacher_moments_upper_uniform_explicit`, for the
extended sum. -/
theorem extended_rademacher_moments_upper_aboveHalf_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x →
        (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ)
          ≤ 20 * Real.log (Real.log x) ^ (3 / 4 : ℝ) ∧
        (∀ q : ℝ, 1 / 2 < q → q ≤ 1 →
          (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
            ≤ 30 * (Real.log x ^ (q * (2 * q - 1))
              * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))) := by
  intro Ω _ X μ hX x hx
  exact ⟨integral_norm_normalisedSum_compMultExtension_le_twenty hX hx,
    fun q hq0 hq1 => integral_rpow_normalisedSum_compMultExtension_le_aboveHalf hX hx hq0 hq1⟩

end RMF
