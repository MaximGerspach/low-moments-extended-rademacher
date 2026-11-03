/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.FixedQAboveHalf
import RMF.Weighted.EulerMomentSmallQExplicit

/-!
# Bonami–Beckner from below, with an explicit constant

For `½ ≤ q ≤ 1` and `t = 2q - 1`,
`E|S(x)|^{2q} ≥ (∑_{n ≤ x} μ²(n) t^{ω(n)}/n)^q` (`RMF.chaosNormSq_rpow_le_integral`, constant `1`),
and the sum is at least `(1/10)(log x)^t` for every `x ≥ e^{405}`, uniformly in `t ∈ [0, 1]`
(`RMF.chaosNormSq_cutCoeff_ge_explicit`):

* a Rankin cut at `y = ⌊x^{5/22}⌋`, whose tail costs `e^{-4.4}e^{1.83 t}`: the Rankin constant is
  `(e - 1)(1 + (log 4 + 4)/log y) ≤ 1.83` once `log y ≥ 90.03`
  (`RMF.prod_one_add_mul_rpow_le_exp_mul_prod_explicit`);
* Mertens' second theorem with its constant, `∏_{p ≤ y}(1 + t/p) ≥ (log y)^t e^{0.05t - 0.75t²}`
  (`RMF.prod_one_add_ge_explicit`).

Hence `E|S(x)|^{2q} ≥ (1/10)(log x)^{q(2q-1)}`
(`RMF.le_integral_rpow_weightedRademacherSum_bb_explicit`), and the large-`q` target
`c(log x)^{q(2q-1)}min{1/(2q-1), log log x}^{3/4}` wherever `10c ≤ (2q-1)^{3/4}`
(`RMF.le_integral_rpow_weightedRademacherSum_largeQ_bb`).
-/

open MeasureTheory

namespace RMF

/-! ### Mertens' second theorem, as a product -/

/-- `∑_{p ≤ y} 1/p² ≤ 3/4`, from `1/n² ≤ 2/(2n-1) - 2/(2n+1)` summed over `n ≥ 2`. -/
lemma sum_primesBelow_inv_sq_le_three_quarters (y : ℕ) :
    ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2 ≤ 3 / 4 := by
  -- `∑_{k < n} 4/((2k+3)(2k+5)) = 2/3 - 2/(2n+3)`
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, 4 / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 5))
      = 2 / 3 - 2 / (2 * (n : ℝ) + 3) := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h1 : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
      have h2 : 2 * (m : ℝ) + 5 ≠ 0 := by positivity
      have h3 : 2 * ((m : ℝ) + 1) + 3 ≠ 0 := by positivity
      field_simp
      ring
  have hsub : Nat.primesBelow (y + 1) ⊆ Finset.Ico 2 (y + 2) := by
    intro p hp
    have := Nat.mem_primesBelow.1 hp
    rw [Finset.mem_Ico]
    exact ⟨this.2.two_le, by omega⟩
  have h1 : ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2
      ≤ ∑ k ∈ Finset.Ico 2 (y + 2), 1 / (k : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  -- `1/(k+2)² ≤ 4/((2k+3)(2k+5))`
  have h2 : ∑ k ∈ Finset.Ico 2 (y + 2), 1 / (k : ℝ) ^ 2
      ≤ ∑ k ∈ Finset.range y, 4 / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 5)) := by
    rw [Finset.sum_Ico_eq_sum_range, show y + 2 - 2 = y by omega]
    refine Finset.sum_le_sum fun k _ => ?_
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3 := htel y
  have hy0 : 0 ≤ 2 / (2 * (y : ℝ) + 3) := by positivity
  linarith

/-- **`∏_{p ≤ y}(1 + t/p) ≥ (log y)^t e^{0.05t - 0.75t²}`** for `t ≥ 0` and `log y ≥ 90.03`:
`log(1 + u) ≥ u - u²` (`RMF.exp_sub_sq_le_one_add`), Mertens' second theorem with its constant
`∑_{p ≤ y} 1/p ≥ log log y + M - 9.0028/log y` (`RMF.log_log_add_le_sum_primesBelow_inv`),
`M ≥ 3/20`, and `∑ 1/p² ≤ 3/4`. -/
theorem prod_one_add_ge_explicit {y : ℕ} (hy : 2 ≤ y) (hlogy : 90.03 ≤ Real.log y) {t : ℝ}
    (ht : 0 ≤ t) :
    Real.log y ^ t * Real.exp (0.05 * t - 0.75 * t ^ 2)
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
  have hlogy0 : 0 < Real.log y := by linarith
  have hper : ∀ p ∈ Nat.primesBelow (y + 1),
      Real.exp (t * (p : ℝ)⁻¹ - t ^ 2 * (1 / (p : ℝ) ^ 2)) ≤ 1 + t * (p : ℝ)⁻¹ := by
    intro p _
    have h := exp_sub_sq_le_one_add (mul_nonneg ht (inv_nonneg.2 (Nat.cast_nonneg p)))
    have heq : t * (p : ℝ)⁻¹ - (t * (p : ℝ)⁻¹) ^ 2
        = t * (p : ℝ)⁻¹ - t ^ 2 * (1 / (p : ℝ) ^ 2) := by ring
    rwa [heq] at h
  have hprod : Real.exp (t * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹
        - t ^ 2 * ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2)
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) hper
  have hm := log_log_add_le_sum_primesBelow_inv hy
  have hM := mertens_const_ge
  have herr : 9.0028 / Real.log y ≤ 0.1 := by
    rw [div_le_iff₀ hlogy0]; linarith
  have hsq := sum_primesBelow_inv_sq_le_three_quarters y
  have h1 : t * (Real.log (Real.log y) + 0.05) ≤ t * ∑ p ∈ Nat.primesBelow (y + 1), (p : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left (by linarith) ht
  have h2 : t ^ 2 * ∑ p ∈ Nat.primesBelow (y + 1), 1 / (p : ℝ) ^ 2 ≤ t ^ 2 * (3 / 4) :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
  refine le_trans ?_ hprod
  rw [Real.rpow_def_of_pos hlogy0, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith)

/-! ### The Rankin cut -/

/-- **The Rankin product, with Mertens' first theorem's constant**: for `δ log y ≤ 1`,
`∏_{p ≤ y}(1 + t p^{δ-1}) ≤ e^{t(e-1)δ(log y + log 4 + 4)}∏_{p ≤ y}(1 + t/p)`
(`RMF.prod_one_add_mul_rpow_le_exp_mul_prod` with the sum kept). -/
theorem prod_one_add_mul_rpow_le_exp_mul_prod_explicit {y : ℕ} (hy : 2 ≤ y) {t δ : ℝ} (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) (hδy : δ * Real.log y ≤ 1) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ (δ - 1))
      ≤ Real.exp (t * ((Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4)))
        * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) := by
  have he := one_le_exp_one_sub_one
  -- one prime: `1 + t p^{δ-1} ≤ (1 + t/p) exp(t (e - 1) δ log p / p)`
  have hper : ∀ p ∈ Nat.primesBelow (y + 1),
      1 + t * (p : ℝ) ^ (δ - 1)
        ≤ (1 + t * (p : ℝ)⁻¹) * Real.exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p)) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hpy : (p : ℝ) ≤ y := by
      exact_mod_cast Nat.lt_succ_iff.1 (Nat.mem_primesBelow.1 hp).1
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hu1 : δ * Real.log p ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpy) hδ) hδy
    have hpδ : (p : ℝ) ^ δ ≤ 1 + (Real.exp 1 - 1) * (δ * Real.log p) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log p)]
      exact exp_le_one_add_mul (mul_nonneg hδ hlogp) hu1
    have hsplit : t * (p : ℝ) ^ (δ - 1)
        ≤ t * (p : ℝ)⁻¹ + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) := by
      rw [Real.rpow_sub_one hp0.ne']
      calc t * ((p : ℝ) ^ δ / p)
          ≤ t * ((1 + (Real.exp 1 - 1) * (δ * Real.log p)) / p) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpδ hp0.le) ht
        _ = t * (p : ℝ)⁻¹ + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) := by ring
    have hv : 0 ≤ t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) :=
      mul_nonneg (mul_nonneg ht (mul_nonneg (by linarith) hδ)) (div_nonneg hlogp hp0.le)
    have ha : 0 ≤ t * (p : ℝ)⁻¹ := mul_nonneg ht (inv_nonneg.2 hp0.le)
    have hexp := Real.add_one_le_exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p))
    calc 1 + t * (p : ℝ) ^ (δ - 1)
        ≤ 1 + t * (p : ℝ)⁻¹ + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p) := by linarith
      _ ≤ (1 + t * (p : ℝ)⁻¹) * (1 + t * ((Real.exp 1 - 1) * δ) * (Real.log p / p)) := by
          nlinarith [mul_nonneg ha hv]
      _ ≤ (1 + t * (p : ℝ)⁻¹) * Real.exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  -- Mertens' first theorem
  have hsum : ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p ≤ Real.log y + Real.log 4 + 4 := by
    have h := sum_log_div_prime_le (x := (y : ℝ)) (by exact_mod_cast (by omega : 1 ≤ y))
    rwa [Nat.floor_natCast, ← primesBelow_succ_eq_filter_Ioc] at h
  have hP0 : 0 ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) :=
    Finset.prod_nonneg fun p _ => add_nonneg zero_le_one (mul_nonneg ht (inv_nonneg.2
      (Nat.cast_nonneg p)))
  have hkey : t * ((Real.exp 1 - 1) * δ * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p)
      ≤ t * ((Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by linarith) hδ)) ht
  calc ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ (δ - 1))
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), ((1 + t * (p : ℝ)⁻¹)
          * Real.exp (t * ((Real.exp 1 - 1) * δ) * (Real.log p / p))) :=
        Finset.prod_le_prod (fun p _ => add_nonneg zero_le_one
          (mul_nonneg ht (Real.rpow_nonneg (Nat.cast_nonneg p) _))) hper
    _ = (∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹))
          * Real.exp (t * ((Real.exp 1 - 1) * δ * ∑ p ∈ Nat.primesBelow (y + 1),
              Real.log p / p)) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, Finset.mul_sum]
        congr 2
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹))
          * Real.exp (t * ((Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hkey) hP0
    _ = _ := mul_comm _ _

/-! ### The chaos norm, from below -/

/-- `e^{-4.4 + 1.83} ≤ 0.0766`: what the Rankin tail keeps. -/
lemma exp_rankinTail_le : Real.exp (-4.4 + 1.83) ≤ 0.0766 := by
  interval_decide (trust := kernel)

/-- `1/10 ≤ 0.9234·0.2255·e^{-0.7}`. -/
lemma one_tenth_le_bbConst : (1 / 10 : ℝ) ≤ 0.9234 * (0.2255 * Real.exp (-0.7)) := by
  have : (0.4965 : ℝ) ≤ Real.exp (-0.7) := by interval_decide (trust := kernel)
  linarith

/-- `0.05t - 0.75t² ≥ -0.7` on `[0, 1]`. -/
lemma neg_seven_tenths_le_mertensExp {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -0.7 ≤ 0.05 * t - 0.75 * t ^ 2 := by
  have : t ^ 2 ≤ t := by nlinarith
  linarith

/-- **`∑_{n ≤ x} μ²(n) t^{ω(n)}/n ≥ (1/10)(log x)^t`** for `x ≥ e^{405}`, uniformly in `0 ≤ t ≤ 1`
(in chaos form): the Rankin cut at `y = ⌊x^{5/22}⌋`, `log y ≥ 0.2255 log x ≥ 90.03`, keeps
`1 - e^{-4.4 + 1.83t} ≥ 0.9234` of `∏_{p ≤ y}(1 + t/p) ≥ (log y)^t e^{-0.7}`. -/
theorem chaosNormSq_cutCoeff_ge_explicit {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : Real.exp 405 ≤ x) :
    (1 / 10) * Real.log x ^ t ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) t := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 405 ≤ Real.log x := by
    rw [← Real.log_exp 405]; exact Real.log_le_log (Real.exp_pos _) hx
  have hlog2 := Real.log_two_lt_d9
  set Y : ℝ := Real.exp (5 / 22 * Real.log x) with hYdef
  set y : ℕ := ⌊Y⌋₊ with hydef
  have hY0 : 0 < Y := Real.exp_pos _
  have hlogY : Real.log Y = 5 / 22 * Real.log x := Real.log_exp _
  have hYx : Y ≤ x := by
    calc Y = Real.exp (5 / 22 * Real.log x) := rfl
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 (by linarith)
      _ = x := Real.exp_log hx0
  have hY2 : (2 : ℝ) ≤ Y := by
    have h1 : 5 / 22 * Real.log x + 1 ≤ Y := Real.add_one_le_exp _
    linarith
  have hy2 : 2 ≤ y := Nat.le_floor (by exact_mod_cast hY2)
  have hyx : y ≤ ⌊x⌋₊ := Nat.floor_le_floor hYx
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  -- `(5/22) log x - log 2 ≤ log y ≤ (5/22) log x`
  have hlogy_le : Real.log y ≤ 5 / 22 * Real.log x := by
    have h := Nat.floor_le hY0.le
    rw [← hydef] at h
    rw [← hlogY]
    exact Real.log_le_log hy0 h
  have hlogy_ge : 5 / 22 * Real.log x - Real.log 2 ≤ Real.log y := by
    have hfl : Y / 2 ≤ (y : ℝ) := by
      have := Nat.sub_one_lt_floor Y
      rw [← hydef] at this
      linarith
    have := Real.log_le_log (by linarith) hfl
    rwa [Real.log_div hY0.ne' (by norm_num), hlogY] at this
  have hlogy : 90.03 ≤ Real.log y := by linarith
  have hlogy0 : 0 < Real.log y := by linarith
  have hratio : 0.2255 * Real.log x ≤ Real.log y := by linarith
  -- the Rankin tail, at `δ = 1/log y`
  set δ : ℝ := (Real.log y)⁻¹ with hδdef
  have hδ0 : 0 ≤ δ := inv_nonneg.2 hlogy0.le
  have hδy : δ * Real.log y ≤ 1 := by rw [hδdef, inv_mul_cancel₀ hlogy0.ne']
  have hrank := chaosNormSq_tailCoeff_le (primesUpTo y) hx0 hδ0 ht0
  rw [prod_primesUpTo y fun p : ℕ => 1 + t * (p : ℝ) ^ (δ - 1)] at hrank
  have hprod := prod_one_add_mul_rpow_le_exp_mul_prod_explicit hy2 ht0 hδ0 hδy
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp 1]
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK : (Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4) ≤ 1.83 := by
    have he := Real.exp_one_lt_d9
    have h1 : δ * (Real.log y + Real.log 4 + 4) ≤ 1.06 := by
      rw [hδdef, inv_mul_eq_div, div_le_iff₀ hlogy0]
      linarith
    calc (Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4)
        = (Real.exp 1 - 1) * (δ * (Real.log y + Real.log 4 + 4)) := by ring
      _ ≤ (Real.exp 1 - 1) * 1.06 := mul_le_mul_of_nonneg_left h1 he1
      _ ≤ 1.83 := by linarith
  have hK0 : 0 ≤ (Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4) :=
    mul_nonneg (mul_nonneg he1 hδ0) (by linarith)
  have hxδ : x ^ (-δ) ≤ Real.exp (-4.4) := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.2 ?_
    have : 4.4 ≤ Real.log x * δ := by
      rw [hδdef, ← div_eq_mul_inv, le_div_iff₀ hlogy0]; linarith
    linarith
  set P := ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ)⁻¹) with hPdef
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun p _ => add_nonneg zero_le_one
    (mul_nonneg ht0 (inv_nonneg.2 (Nat.cast_nonneg p)))
  have htail : chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) t ≤ 0.0766 * P := by
    have h1 : Real.exp (t * ((Real.exp 1 - 1) * δ * (Real.log y + Real.log 4 + 4)))
        ≤ Real.exp 1.83 :=
      Real.exp_le_exp.2 (le_trans (mul_le_of_le_one_left hK0 ht1) hK)
    have h2 : Real.exp (-4.4) * Real.exp 1.83 ≤ 0.0766 := by
      rw [← Real.exp_add]; exact exp_rankinTail_le
    calc chaosNormSq (primesUpTo y) (tailCoeff ⌊x⌋₊) t
        ≤ x ^ (-δ) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + t * (p : ℝ) ^ (δ - 1)) := hrank
      _ ≤ Real.exp (-4.4) * (Real.exp 1.83 * P) :=
          mul_le_mul hxδ (le_trans hprod (mul_le_mul_of_nonneg_right h1 hP0))
            (Finset.prod_nonneg fun p _ => add_nonneg zero_le_one
              (mul_nonneg ht0 (Real.rpow_nonneg (Nat.cast_nonneg p) _))) (Real.exp_pos _).le
      _ = Real.exp (-4.4) * Real.exp 1.83 * P := by ring
      _ ≤ 0.0766 * P := mul_le_mul_of_nonneg_right h2 hP0
  have hfull : chaosNormSq (primesUpTo y) fullCoeff t = P := by
    rw [chaosNormSq_fullCoeff]
    exact prod_primesUpTo y fun p : ℕ => 1 + t * (p : ℝ)⁻¹
  have hsplit := chaosNormSq_cut_add_tail ⌊x⌋₊ (primesUpTo y) t
  -- the main term
  have hmain := prod_one_add_ge_explicit hy2 hlogy ht0
  have hexp : Real.exp (-0.7) ≤ Real.exp (0.05 * t - 0.75 * t ^ 2) :=
    Real.exp_le_exp.2 (neg_seven_tenths_le_mertensExp ht0 ht1)
  have hpow : (0.2255 : ℝ) * Real.log x ^ t ≤ Real.log y ^ t := by
    have h1 : (0.2255 * Real.log x) ^ t ≤ Real.log y ^ t :=
      Real.rpow_le_rpow (mul_nonneg (by norm_num) (by linarith)) hratio ht0
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
    have h2 : (0.2255 : ℝ) ≤ 0.2255 ^ t := by
      calc (0.2255 : ℝ) = 0.2255 ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ 0.2255 ^ t := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht1
    exact le_trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _)) h1
  have hP : 0.2255 * Real.exp (-0.7) * Real.log x ^ t ≤ P := by
    have h1 := mul_le_mul hpow hexp (Real.exp_pos _).le (Real.rpow_nonneg hlogy0.le _)
    calc 0.2255 * Real.exp (-0.7) * Real.log x ^ t
        = 0.2255 * Real.log x ^ t * Real.exp (-0.7) := by ring
      _ ≤ Real.log y ^ t * Real.exp (0.05 * t - 0.75 * t ^ 2) := h1
      _ ≤ P := hmain
  have hlx : 0 ≤ Real.log x ^ t := Real.rpow_nonneg (by linarith) _
  calc (1 / 10) * Real.log x ^ t ≤ 0.9234 * (0.2255 * Real.exp (-0.7)) * Real.log x ^ t :=
        mul_le_mul_of_nonneg_right one_tenth_le_bbConst hlx
    _ = 0.9234 * (0.2255 * Real.exp (-0.7) * Real.log x ^ t) := by ring
    _ ≤ 0.9234 * P := mul_le_mul_of_nonneg_left hP (by norm_num)
    _ ≤ chaosNormSq (primesUpTo y) (cutCoeff ⌊x⌋₊) t := by
        rw [hfull] at hsplit
        linarith only [hsplit, htail]
    _ ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) t :=
        chaosNormSq_mono (primesUpTo_mono hyx) (cutCoeff ⌊x⌋₊) ht0

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bonami–Beckner from below, explicit**: for every Rademacher `X`, `x ≥ e^{405}` and
`½ ≤ q ≤ 1`, `(1/10)(log x)^{q(2q-1)} ≤ E|S(x)|^{2q}`. -/
theorem le_integral_rpow_weightedRademacherSum_bb_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : Real.exp 405 ≤ x) (hq0 : 1 / 2 ≤ q)
    (hq1 : q ≤ 1) :
    (1 / 10) * Real.log x ^ (q * (2 * q - 1))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 0 < Real.log x := by
    have : (405 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 405]; exact Real.log_le_log (Real.exp_pos _) hx
    linarith
  have hhyp := chaosNormSq_rpow_le_integral (μ := μ) (Y := fun p : Nat.Primes => X p)
    (fun p => hX.measurable p p.2) hX.iIndep (fun p => hX.hasLaw p p.2)
    (p := 2 * q) (by linarith) (by linarith) (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊)
  simp_rw [weightedRademacherSum_eq_chaosSum]
  refine le_trans ?_ hhyp
  have hbase := chaosNormSq_cutCoeff_ge_explicit (t := 2 * q - 1) (by linarith) (by linarith) hx
  have hmin : (1 / 10 : ℝ) ≤ (1 / 10) ^ q := by
    calc (1 / 10 : ℝ) = (1 / 10) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / 10) ^ q := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hq1
  calc (1 / 10) * Real.log x ^ (q * (2 * q - 1))
      ≤ (1 / 10) ^ q * Real.log x ^ (q * (2 * q - 1)) :=
        mul_le_mul_of_nonneg_right hmin (Real.rpow_nonneg hlogx.le _)
    _ = ((1 / 10) * Real.log x ^ (2 * q - 1)) ^ q := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hlogx.le _), ← Real.rpow_mul hlogx.le,
          mul_comm (2 * q - 1) q]
    _ ≤ chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) (2 * q - 1) ^ q :=
        Real.rpow_le_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hlogx.le _)) hbase
          (by linarith)
    _ = chaosNormSq (primesUpTo ⌊x⌋₊) (cutCoeff ⌊x⌋₊) (2 * q - 1) ^ (2 * q / 2) := by
        rw [mul_div_cancel_left₀ q two_ne_zero]

/-- **The large-`q` target by Bonami–Beckner**: for `½ < q ≤ 1`, `x ≥ e^{405}` and
`10c ≤ (2q-1)^{3/4}`, `c(log x)^{q(2q-1)}min{1/(2q-1), log log x}^{3/4} ≤ E|S(x)|^{2q}`. -/
theorem le_integral_rpow_weightedRademacherSum_largeQ_bb {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x q c : ℝ} (hx : Real.exp 405 ≤ x) (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) (hc0 : 0 ≤ c) (hc : 10 * c ≤ (2 * q - 1) ^ (3 / 4 : ℝ)) :
    c * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
          ^ (2 * q) ∂μ := by
  have hδ : 0 < 2 * q - 1 := by linarith
  have hlogx : 0 < Real.log x := by
    have : (405 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 405]; exact Real.log_le_log (Real.exp_pos _) hx
    linarith
  have hΛ : 0 < Real.log (Real.log x) := Real.log_pos (by
    have : (405 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 405]; exact Real.log_le_log (Real.exp_pos _) hx
    linarith)
  have hmin0 : 0 ≤ min (2 * q - 1)⁻¹ (Real.log (Real.log x)) := le_min (inv_nonneg.2 hδ.le) hΛ.le
  have hm : min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)
      ≤ ((2 * q - 1) ^ (3 / 4 : ℝ))⁻¹ := by
    rw [← Real.inv_rpow hδ.le]
    exact Real.rpow_le_rpow hmin0 (min_le_left _ _) (by norm_num)
  have hd0 : 0 < (2 * q - 1) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hcm : c * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ) ≤ 1 / 10 := by
    calc c * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)
        ≤ c * ((2 * q - 1) ^ (3 / 4 : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hm hc0
      _ ≤ 1 / 10 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hd0]; linarith
  have hL : 0 ≤ Real.log x ^ (q * (2 * q - 1)) := Real.rpow_nonneg hlogx.le _
  calc c * (Real.log x ^ (q * (2 * q - 1))
        * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ))
      = c * min (2 * q - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)
          * Real.log x ^ (q * (2 * q - 1)) := by ring
    _ ≤ 1 / 10 * Real.log x ^ (q * (2 * q - 1)) := mul_le_mul_of_nonneg_right hcm hL
    _ ≤ _ := le_integral_rpow_weightedRademacherSum_bb_explicit hX hx hq0.le hq1

end RMF
