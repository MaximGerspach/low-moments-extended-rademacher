/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedEulerRatio
import RMF.Weighted.ExtendedLowerParseval
import RMF.Weighted.LowerFixedQ

/-!
# The extended lower bound: the subtracted term

The subtracted term of
`RMF.exists_le_integral_rpow_extendedSum_euler` is the damped line integral of the extended Euler
product `F^e`, and for `0 < q < ½` it is

`E[(∫_ℝ |F^e(½+V/log x+it)/(½+V/log x+it)|² dt)^q] ≪ (1 + (q(1-2q))⁻¹) (log x)^q (log log x)^{-q/2}`

uniformly in `V ≥ 1` (`RMF.exists_const_integral_rpow_lineDivSq_extended_le`).

* **The shift.**  By Parseval the integral decreases in the abscissa
  (`RMF.ae_integral_lineDivSq_le_of_le`), so it is read at `σ = 1/log x`.
* **The ratio.**  `|F^e|² = |F|²·R` with `R = ∏_p |1 - p^{-2s}|^{-2}`, and
  `R·|½+σ+it|^{-2} ≤ K(1+t²)^{1/48}·|σ+it|^{-2}` (`RMF.exists_prod_inv_normSq_mul_inv_le_weight`):
  on `|t| ≤ ½` from `R ≪ min{log N, 1/|t|}²`, beyond from `R ≪ log^{20}(2|t|+3)`, which the weight
  `(1+t²)^{1/48}` absorbs.
* **The three ranges** of the weighted Rademacher integral.  On `|t| ≤ 1` the weight is bounded and
  the whole-line bound `RMF.exists_const_integral_rpow_lineDiv_floor_le` applies.  On
  `1 < |t| ≤ M` the unit windows pay `(1+n²)^{-47/48}` instead of `(1+n²)^{-1}`, and the descent at
  `2/3` still converges, since `47/72 > 5/8`
  (`RMF.exists_const_integral_rpow_windowSum_chaos_weight_le_rademacher`).  Beyond `M` Jensen
  against the second moment, with `∫_{|t|>M}(1+t²)^{1/48}|σ+it|^{-2} ≪ M^{-1/2}`
  (`RMF.exists_integral_rpow_eulerProductLine_weight_tail_le`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The weight `(1+t²)^{1/48}` -/

/-- `log(2|t|+3)^{20} ≤ 5·960^{20}·(1+t²)^{1/48}`: `log u ≤ 960·u^{1/960}` and
`2|t|+3 ≤ 5(1+t²)`. -/
lemma log_two_mul_abs_add_three_pow_le (t : ℝ) :
    Real.log (2 * |t| + 3) ^ 20 ≤ 5 * 960 ^ 20 * (1 + t ^ 2) ^ ((1 : ℝ) / 48) := by
  have hu0 : (0 : ℝ) < 2 * |t| + 3 := by positivity
  have hlog0 : 0 ≤ Real.log (2 * |t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have h1 : Real.log (2 * |t| + 3) ≤ 960 * (2 * |t| + 3) ^ ((1 : ℝ) / 960) := by
    have h := Real.log_le_rpow_div hu0.le (by norm_num : (0 : ℝ) < 1 / 960)
    rw [div_div_eq_mul_div, div_one] at h
    linarith
  have h2 : Real.log (2 * |t| + 3) ^ 20 ≤ (960 * (2 * |t| + 3) ^ ((1 : ℝ) / 960)) ^ 20 :=
    pow_le_pow_left₀ hlog0 h1 20
  have h3 : (960 * (2 * |t| + 3) ^ ((1 : ℝ) / 960)) ^ 20
      = 960 ^ 20 * (2 * |t| + 3) ^ ((1 : ℝ) / 48) := by
    rw [mul_pow, ← Real.rpow_natCast ((2 * |t| + 3) ^ ((1 : ℝ) / 960)) 20,
      ← Real.rpow_mul hu0.le]
    norm_num
  have hle : 2 * |t| + 3 ≤ 5 * (1 + t ^ 2) := by
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
  have h4 : (2 * |t| + 3) ^ ((1 : ℝ) / 48)
      ≤ (5 : ℝ) ^ ((1 : ℝ) / 48) * (1 + t ^ 2) ^ ((1 : ℝ) / 48) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow hu0.le hle (by norm_num)
  have h5 : (5 : ℝ) ^ ((1 : ℝ) / 48) ≤ 5 := by
    calc (5 : ℝ) ^ ((1 : ℝ) / 48) ≤ 5 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 5 := Real.rpow_one 5
  have hw0 : (0 : ℝ) ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 48) := Real.rpow_nonneg (by positivity) _
  calc Real.log (2 * |t| + 3) ^ 20 ≤ 960 ^ 20 * (2 * |t| + 3) ^ ((1 : ℝ) / 48) := h2.trans h3.le
    _ ≤ 960 ^ 20 * ((5 : ℝ) ^ ((1 : ℝ) / 48) * (1 + t ^ 2) ^ ((1 : ℝ) / 48)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ ≤ 960 ^ 20 * (5 * (1 + t ^ 2) ^ ((1 : ℝ) / 48)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 hw0) (by norm_num)
    _ = 5 * 960 ^ 20 * (1 + t ^ 2) ^ ((1 : ℝ) / 48) := by ring

/-- On a window `(n, n+1]` with `n ≥ 1` or `n ≤ -2`, `(1+t²)^{1/48} ≤ 2(1+n²)^{1/48}`, since
`1+t² ≤ 4(1+n²)` there. -/
lemma one_add_sq_rpow_le_of_mid {n : ℤ} (hn : 1 ≤ n ∨ n ≤ -2) {t : ℝ} (h0 : (n : ℝ) < t)
    (h1 : t ≤ (n : ℝ) + 1) :
    (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ 2 * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 48) := by
  have hle : 1 + t ^ 2 ≤ 4 * (1 + (n : ℝ) ^ 2) := by
    rcases hn with h | h
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have ht0 : 0 ≤ t := by linarith
      have hsq : t ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := pow_le_pow_left₀ ht0 h1 2
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    · have hn2 : (n : ℝ) ≤ -2 := by exact_mod_cast h
      have hsq : t ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (n : ℝ)]
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 48) ≤ 2 := by
    calc (4 : ℝ) ^ ((1 : ℝ) / 48) ≤ 4 ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  calc (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ (4 * (1 + (n : ℝ) ^ 2)) ^ ((1 : ℝ) / 48) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = (4 : ℝ) ^ ((1 : ℝ) / 48) * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 48) :=
        Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 48) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (by positivity) _)

/-- On `t > T ≥ 1`, `(1+t²)^{1/48}(σ²+t²)⁻¹ ≤ 2 t^{-3/2}`. -/
lemma weight_mul_inv_sq_add_sq_le {σ t : ℝ} (ht : 1 ≤ t) :
    (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ ≤ 2 * t ^ (-(3 / 2) : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hw : (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ 2 * t ^ ((1 : ℝ) / 2) := by
    have h1 : (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by norm_num)
    have h2 : (1 + t ^ 2) ^ ((1 : ℝ) / 4) ≤ (2 * t ^ 2) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
    have h3 : (2 * t ^ 2) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast t 2,
        ← Real.rpow_mul ht0.le]
      norm_num
    have h4 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) * t ^ ((1 : ℝ) / 2) :=
          h3 ▸ h1.trans h2
      _ ≤ 2 * t ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht0.le _)
  have hd : (σ ^ 2 + t ^ 2)⁻¹ ≤ t ^ (-2 : ℝ) := by
    have hrw : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [hrw]
    exact inv_anti₀ (pow_pos ht0 2) (le_add_of_nonneg_left (sq_nonneg σ))
  have hsplit : t ^ ((1 : ℝ) / 2) * t ^ (-2 : ℝ) = t ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num
  calc (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹
      ≤ (2 * t ^ ((1 : ℝ) / 2)) * t ^ (-2 : ℝ) :=
        mul_le_mul hw hd (inv_nonneg.2 (by positivity)) (by positivity)
    _ = 2 * t ^ (-(3 / 2) : ℝ) := by rw [mul_assoc, hsplit]

/-- **The tail of the weighted Cauchy weight**: `∫_{|t|>T} (1+t²)^{1/48}(σ²+t²)⁻¹ dt ≤ 8T^{-1/2}`
for `T ≥ 1`.  The fold onto `t > T` is `integral_comp_abs`, as in
`RMF.setIntegral_inv_sq_add_sq_abs_gt_le`. -/
lemma setIntegral_weight_inv_sq_add_sq_abs_gt_le (σ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in {t : ℝ | T < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹)
      ≤ 8 * T ^ (-(1 / 2 : ℝ)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hSmeas : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ u, g u = (1 + u ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + u ^ 2)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hgfun : (fun u : ℝ => (1 + u ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + u ^ 2)⁻¹) = g :=
    funext fun u => (hg u).symm
  rw [hgfun]
  have hind : ∀ t : ℝ,
      Set.indicator (Set.Ioi T) g |t| = Set.indicator {t : ℝ | T < |t|} g t := by
    intro t
    by_cases h : T < |t|
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 h),
        Set.indicator_of_mem (show t ∈ {t : ℝ | T < |t|} from h), hg, hg, sq_abs]
    · rw [Set.indicator_of_notMem (by simpa using h),
        Set.indicator_of_notMem (show t ∉ {t : ℝ | T < |t|} from h)]
  have habs := integral_comp_abs (f := Set.indicator (Set.Ioi T) g)
  simp only [hind] at habs
  rw [integral_indicator hSmeas] at habs
  rw [habs, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.2 (Set.Ioi_subset_Ioi hT0.le)]
  have hmaj : IntegrableOn (fun t : ℝ => 2 * t ^ (-(3 / 2) : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT0).const_mul 2
  have hle : ∀ t ∈ Set.Ioi T, g t ≤ 2 * t ^ (-(3 / 2) : ℝ) := fun t ht => by
    rw [hg]
    exact weight_mul_inv_sq_add_sq_le (le_trans hT (le_of_lt ht))
  have hgm : Measurable g := by
    rw [← hgfun]
    fun_prop
  have hsmall : IntegrableOn g (Set.Ioi T) := by
    refine Integrable.mono' hmaj hgm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have hg0 : 0 ≤ g t := by rw [hg]; positivity
    rw [Real.norm_of_nonneg hg0]
    exact hle t ht
  have hcmp : (∫ t in Set.Ioi T, g t) ≤ ∫ t in Set.Ioi T, 2 * t ^ (-(3 / 2) : ℝ) :=
    setIntegral_mono_on hsmall hmaj measurableSet_Ioi hle
  have hval : (∫ t in Set.Ioi T, 2 * t ^ (-(3 / 2) : ℝ)) = 4 * T ^ (-(1 / 2 : ℝ)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT0,
      show (-(3 / 2) : ℝ) + 1 = -(1 / 2) by norm_num]
    ring
  linarith

/-- **The weighted Cauchy weight is integrable** on `ℝ`: it is at most
`(min{σ²,1})⁻¹(1+t²)^{-47/48}`. -/
lemma integrable_weight_inv_sq_add_sq {σ : ℝ} (hσ : 0 < σ) :
    Integrable fun t : ℝ => (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ := by
  have hcmin : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (pow_pos hσ 2) one_pos
  have hJ : Integrable fun t : ℝ => (1 + t ^ 2) ^ (-(47 / 48 : ℝ)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 47 / 24)
      (by rw [Module.finrank_self]; norm_num)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    norm_num
  refine Integrable.mono' (hJ.const_mul (min (σ ^ 2) 1)⁻¹) (by fun_prop)
    (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h2 : min (σ ^ 2) 1 * (1 + t ^ 2) ≤ σ ^ 2 + t ^ 2 := by
    have hb : min (σ ^ 2) 1 * t ^ 2 ≤ 1 * t ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
    have ha : min (σ ^ 2) 1 ≤ σ ^ 2 := min_le_left _ _
    nlinarith
  have hsplit : (1 + t ^ 2) ^ (-(47 / 48 : ℝ))
      = (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (1 + t ^ 2)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add h1]
    norm_num
  rw [Real.norm_of_nonneg (by positivity), hsplit]
  have hinv : (σ ^ 2 + t ^ 2)⁻¹ ≤ (min (σ ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos hcmin h1) h2
  calc (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹
      ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 48) * ((min (σ ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg h1.le _)
    _ = (min (σ ^ 2) 1)⁻¹ * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (1 + t ^ 2)⁻¹) := by ring

/-! ### The Euler-product ratio, against the weight -/

/-- **The ratio of the two Euler products, against the weight.**  With
`R = ∏_{p<N}|1-(p^{-s})²|^{-2}` at `s = ½+σ+it`, for `N ≥ 2`, `σ > 0`, `σ log N ≤ 2` and `t ≠ 0`,
`R·((½+σ)²+t²)⁻¹ ≤ K(1+t²)^{1/48}(σ²+t²)⁻¹`.  On `|t| ≤ ½`,
`R ≪ min{log N, 1/(2|t|)}² ≤ 8(σ²+t²)⁻¹` (`RMF.exists_prod_inv_normSq_le_of_abs_le_half`); beyond,
`R ≪ log^{20}(2|t|+3)` (`RMF.exists_prod_inv_normSq_le_of_half_le_abs`), below the weight by
`RMF.log_two_mul_abs_add_three_pow_le`. -/
theorem exists_prod_inv_normSq_mul_inv_le_weight :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (σ t : ℝ), 2 ≤ N → 0 < σ → σ * Real.log N ≤ 2 → t ≠ 0 →
      (∏ p ∈ Nat.primesBelow N,
          (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹)
        * ((1 / 2 + σ) ^ 2 + t ^ 2)⁻¹
      ≤ K * (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ := by
  obtain ⟨C₁, hC₁, H₁⟩ := exists_prod_inv_normSq_le_of_abs_le_half
  obtain ⟨C₂, hC₂, H₂⟩ := exists_prod_inv_normSq_le_of_half_le_abs
  have hK0 : 0 < 32 * C₁ + 5 * 960 ^ 20 * C₂ :=
    add_pos (mul_pos (by norm_num) hC₁) (mul_pos (by norm_num) hC₂)
  refine ⟨32 * C₁ + 5 * 960 ^ 20 * C₂, hK0, fun N σ t hN hσ hσN ht => ?_⟩
  have ht2 : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht))
  have hst : 0 < σ ^ 2 + t ^ 2 := by positivity
  have hw1 : (1 : ℝ) ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 48) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hw0 : (0 : ℝ) ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 48) := by linarith
  have hD0 : (0 : ℝ) ≤ ((1 / 2 + σ) ^ 2 + t ^ 2)⁻¹ := inv_nonneg.2 (by positivity)
  rcases le_or_gt |t| (1 / 2) with htabs | htabs
  · -- the central window
    have hR := H₁ N σ t hN hσ.le (abs_pos.2 ht) htabs
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hm0 : 0 ≤ min (Real.log N) (1 / (2 * |t|)) := le_min hlogN (by positivity)
    have hmin : min (Real.log N) (1 / (2 * |t|)) ^ 2 ≤ 8 * (σ ^ 2 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hst]
      rcases le_total σ |t| with hσt | hσt
      · have h1 : min (Real.log N) (1 / (2 * |t|)) ^ 2 ≤ (1 / (2 * |t|)) ^ 2 :=
          pow_le_pow_left₀ hm0 (min_le_right _ _) 2
        have hσ2 : σ ^ 2 ≤ t ^ 2 := by
          rw [← sq_abs t]
          exact pow_le_pow_left₀ hσ.le hσt 2
        have e : (1 / (2 * |t|)) ^ 2 * (2 * t ^ 2) = 1 / 2 := by
          rw [div_pow, one_pow, mul_pow, sq_abs, one_div_mul_eq_div,
            div_eq_iff (mul_pos (by norm_num) ht2).ne']
          ring
        calc min (Real.log N) (1 / (2 * |t|)) ^ 2 * (σ ^ 2 + t ^ 2)
            ≤ (1 / (2 * |t|)) ^ 2 * (2 * t ^ 2) :=
              mul_le_mul h1 (by linarith) hst.le (sq_nonneg _)
          _ = 1 / 2 := e
          _ ≤ 8 := by norm_num
      · have h1 : min (Real.log N) (1 / (2 * |t|)) ^ 2 ≤ Real.log N ^ 2 :=
          pow_le_pow_left₀ hm0 (min_le_left _ _) 2
        have ht2σ : t ^ 2 ≤ σ ^ 2 := by
          rw [← sq_abs t]
          exact pow_le_pow_left₀ (abs_nonneg t) hσt 2
        have hlσ : (Real.log N * σ) ^ 2 ≤ 2 ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hlogN hσ.le) (by linarith) 2
        calc min (Real.log N) (1 / (2 * |t|)) ^ 2 * (σ ^ 2 + t ^ 2)
            ≤ Real.log N ^ 2 * (2 * σ ^ 2) :=
              mul_le_mul h1 (by linarith) hst.le (sq_nonneg _)
          _ = 2 * (Real.log N * σ) ^ 2 := by ring
          _ ≤ 8 := by linarith
    have hs : ((1 / 2 + σ) ^ 2 + t ^ 2)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg t]
    calc _ ≤ (C₁ * (8 * (σ ^ 2 + t ^ 2)⁻¹)) * 4 :=
          mul_le_mul (hR.trans (mul_le_mul_of_nonneg_left hmin hC₁.le)) hs hD0
            (mul_nonneg hC₁.le (by positivity))
      _ = 32 * C₁ * (σ ^ 2 + t ^ 2)⁻¹ := by ring
      _ ≤ (32 * C₁ + 5 * 960 ^ 20 * C₂) * (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hst.le)
          calc 32 * C₁ = 32 * C₁ * 1 := (mul_one _).symm
            _ ≤ (32 * C₁ + 5 * 960 ^ 20 * C₂) * (1 + t ^ 2) ^ ((1 : ℝ) / 48) :=
                mul_le_mul (by linarith [mul_pos (by norm_num : (0 : ℝ) < 5 * 960 ^ 20) hC₂])
                  hw1 zero_le_one hK0.le
  · -- beyond the window
    have hR := H₂ N σ t hσ.le htabs.le
    have hs : ((1 / 2 + σ) ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2 + t ^ 2)⁻¹ := inv_anti₀ hst (by nlinarith)
    have hL := log_two_mul_abs_add_three_pow_le t
    calc _ ≤ (C₂ * (5 * 960 ^ 20 * (1 + t ^ 2) ^ ((1 : ℝ) / 48))) * (σ ^ 2 + t ^ 2)⁻¹ :=
          mul_le_mul (hR.trans (mul_le_mul_of_nonneg_left hL hC₂.le)) hs hD0
            (mul_nonneg hC₂.le (by positivity))
      _ = 5 * 960 ^ 20 * C₂ * (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ := by ring
      _ ≤ (32 * C₁ + 5 * 960 ^ 20 * C₂) * (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hw0)
            (inv_nonneg.2 hst.le)
          linarith [mul_pos (by norm_num : (0 : ℝ) < 32) hC₁]

/-- **The extended line integrand against the weighted Rademacher one.**  There is `K` such that
for Rademacher `X` and `N ≥ 2`, almost surely, for every `σ > 0` with `σ log N ≤ 2` and `t ≠ 0`,
`|F^e(½+σ+it)/(½+σ+it)|² ≤ K(1+t²)^{1/48}|F(½+σ+it)/(σ+it)|²`, `F^e` and `F` the Euler
products of `RMF.compMultExtension X` and `RMF.squarefreeExtension X`.  From
`RMF.ae_normSq_randomEulerProduct_compMult_eq` and
`RMF.exists_prod_inv_normSq_mul_inv_le_weight`. -/
theorem exists_ae_lineDivSq_le_weight :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ N : ℕ, 2 ≤ N → ∀ᵐ ω ∂μ, ∀ σ t : ℝ, 0 < σ → σ * Real.log N ≤ 2 → t ≠ 0 →
        lineDivSq (1 / 2 + σ) X N ω t
          ≤ K * (1 + t ^ 2) ^ ((1 : ℝ) / 48)
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  obtain ⟨K, hK, HK⟩ := exists_prod_inv_normSq_mul_inv_le_weight
  refine ⟨K, hK, fun X μ hX N hN => ?_⟩
  filter_upwards [ae_normSq_randomEulerProduct_compMult_eq hX N] with ω hratio
  intro σ t hσ hσN ht
  have hcast : (((1 / 2 + σ : ℝ)) : ℂ) + (t : ℂ) * Complex.I
      = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  have hre : 0 < ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hd1 : ‖(((1 / 2 + σ : ℝ)) : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = (1 / 2 + σ) ^ 2 + t ^ 2 :=
    normSq_ofReal_add_mul_I (1 / 2 + σ) t
  have hd2 : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 :=
    normSq_ofReal_add_mul_I σ t
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∏ p ∈ Nat.primesBelow N,
      (‖1 - ((p : ℂ) ^ (-((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I))) ^ 2‖ ^ 2)⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := ⟨_, rfl⟩
  have hR := HK N σ t hN hσ hσN ht
  rw [← hP] at hR
  have hR' : P / ((1 / 2 + σ) ^ 2 + t ^ 2)
      ≤ K * (1 + t ^ 2) ^ ((1 : ℝ) / 48) / (σ ^ 2 + t ^ 2) := by
    rw [div_eq_mul_inv P ((1 / 2 + σ) ^ 2 + t ^ 2), div_eq_mul_inv _ (σ ^ 2 + t ^ 2)]
    exact hR
  have hL : lineDivSq (1 / 2 + σ) X N ω t = A * (P / ((1 / 2 + σ) ^ 2 + t ^ 2)) := by
    rw [lineDivSq, norm_div, div_pow, hd1, hcast, hratio _ hre, ← hP, ← hA, mul_div_assoc]
  have hRt : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = A / (σ ^ 2 + t ^ 2) := by
    rw [norm_div, div_pow, hd2, ← hA]
  have hA0 : 0 ≤ A := by rw [hA]; exact sq_nonneg _
  rw [hL, hRt]
  calc A * (P / ((1 / 2 + σ) ^ 2 + t ^ 2))
      ≤ A * (K * (1 + t ^ 2) ^ ((1 : ℝ) / 48) / (σ ^ 2 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hR' hA0
    _ = K * (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (A / (σ ^ 2 + t ^ 2)) := by ring

/-! ### The damped line integral of `F^e` decreases in the shift -/

/-- **Almost surely the damped line integral of `F^e` decreases in the abscissa** on `σ ≥ ½`: by
Parseval (`RMF.smoothTailIntegral_eq_lineDivSq_extended`) it is `2π∫_0^∞|A(u)|²u^{-1-2σ}du`, and
the smooth sum `A` vanishes below `1`. -/
lemma ae_integral_lineDivSq_le_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ₁ σ₂ : ℝ} (hσ₁ : 1 / 2 ≤ σ₁)
    (hσ : σ₁ ≤ σ₂) :
    ∀ᵐ ω ∂μ, (∫ t : ℝ, lineDivSq σ₂ X (y + 1) ω t) ≤ ∫ t : ℝ, lineDivSq σ₁ X (y + 1) ω t := by
  have hσ₂ : 1 / 2 ≤ σ₂ := hσ₁.trans hσ
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖(fun ω => compMultExtension fun p => X p ω) ω n‖ ≤ 1 :=
    fun n => hX.ae_norm_compMultExtension_le_one norm_le_one_rademacherLaw n
  filter_upwards [smoothTailIntegral_eq_lineDivSq_extended hX y hσ₁,
    smoothTailIntegral_eq_lineDivSq_extended hX y hσ₂, integrableOn_smoothTail_of hbd y hσ₁,
    integrableOn_smoothTail_of hbd y hσ₂] with ω h₁ h₂ hI₁ hI₂
  have hmono : smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) y σ₂ ω
      ≤ smoothTailIntegral (fun ω => compMultExtension fun p => X p ω) y σ₁ ω := by
    refine setIntegral_mono_on hI₂ hI₁ measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rcases lt_or_ge u 1 with h | h
    · simp [smoothPartial_eq_zero h ω]
    · exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hu0 _)
        (Real.rpow_le_rpow_of_exponent_le h (by linarith))
  rw [h₁, h₂] at hmono
  exact le_of_mul_le_mul_left hmono (inv_pos.2 (by positivity))

/-- **Its `q`-th moment decreases in the shift too.** -/
lemma integral_rpow_lineDivSq_le_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {σ₁ σ₂ q : ℝ} (hσ₁ : 1 / 2 ≤ σ₁)
    (hσ : σ₁ ≤ σ₂) (hq : 0 ≤ q) :
    (∫ ω, (∫ t : ℝ, lineDivSq σ₂ X (y + 1) ω t) ^ q ∂μ)
      ≤ ∫ ω, (∫ t : ℝ, lineDivSq σ₁ X (y + 1) ω t) ^ q ∂μ := by
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg
    (integral_nonneg fun t => by unfold lineDivSq; positivity) _)
    (integrable_lineDivSq_rpow_extended hX (y + 1) hσ₁ hq) ?_
  filter_upwards [ae_integral_lineDivSq_le_of_le hX y hσ₁ hσ] with ω hω
  exact Real.rpow_le_rpow (integral_nonneg fun t => by unfold lineDivSq; positivity) hω hq

/-! ### The far range, with the weight -/

omit [MeasurableSpace Ω] in
/-- **The weighted line integrand is integrable** on a path with `|X(p)| ≤ 1`: bounded numerator
against `RMF.integrable_weight_inv_sq_add_sq`. -/
lemma integrable_weight_line_div_sq {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} {c σ : ℝ}
    (hc : 1 / 2 ≤ c) (hσ : 0 < σ) (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1) :
    Integrable fun t : ℝ => (1 + t ^ 2) ^ ((1 : ℝ) / 48)
      * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hmeas := measurable_randomEulerProduct_sqfree_line (X := X) (N := N) (ω := ω) c
  have hbd : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound N :=
    fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using hc)
  have hwm : Measurable fun t : ℝ => (1 + t ^ 2) ^ ((1 : ℝ) / 48) := by fun_prop
  have hm : Measurable fun t : ℝ => (1 + t ^ 2) ^ ((1 : ℝ) / 48)
      * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    hwm.mul ((hmeas.div (by fun_prop)).norm.pow_const 2)
  refine Integrable.mono' ((integrable_weight_inv_sq_add_sq hσ).const_mul (eulerBound N ^ 2))
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have hnum : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
      ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ≤ eulerBound N ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbd t) 2
  have hw0 : (0 : ℝ) ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 48) := Real.rpow_nonneg (by positivity) _
  have hst : (0 : ℝ) < σ ^ 2 + t ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), norm_div, div_pow, normSq_ofReal_add_mul_I]
  calc (1 + t ^ 2) ^ ((1 : ℝ) / 48)
        * (‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((c : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 / (σ ^ 2 + t ^ 2))
      ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (eulerBound N ^ 2 / (σ ^ 2 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hst.le) hw0
    _ = eulerBound N ^ 2 * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) := by ring

/-- **The far range of the weighted line integral, by Jensen.**  There is `C` such that for
Rademacher `X`, `0 < q ≤ 1`, `y ≥ 2`, `σ > 0` and `T ≥ 1`, with `F` the Euler product over `p ≤ y`,
`E[((log y)⁻¹∫_{|t|>T} (1+t²)^{1/48}|F(½+σ+it)/(σ+it)|² dt)^q] ≤ (C T^{-1/2})^q`, the
unnormalised `q`-th power being integrable.  `RMF.exists_integral_rpow_eulerProductLine_tail_le`
with the weight: the second moment does not depend on the height, and
`RMF.setIntegral_weight_inv_sq_add_sq_abs_gt_le` replaces `2/T`. -/
theorem exists_integral_rpow_eulerProductLine_weight_tail_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ y : ℕ, 2 ≤ y → ∀ σ T : ℝ, 0 < σ → 1 ≤ T →
        Integrable (fun ω => (∫ t in {t : ℝ | T < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ ∧
        (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
              * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
          ≤ (C * T ^ (-(1 / 2 : ℝ))) ^ q := by
  obtain ⟨C₂, -, hprod⟩ := exists_prod_one_add_le_rpow_log
  refine ⟨8 * Real.exp C₂, by positivity, ?_⟩
  intro X μ hX q hq0 hq1 y hy σ T hσ hT
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hSmeas : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  obtain ⟨G, hG⟩ : ∃ G : Ω → ℝ → ℝ, ∀ (ω : Ω) (t : ℝ), G ω t =
      (1 + t ^ 2) ^ ((1 : ℝ) / 48)
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, fun _ _ => rfl⟩
  simp only [← hG]
  have hwint := integrable_weight_inv_sq_add_sq hσ
  have hwtail := setIntegral_weight_inv_sq_add_sq_abs_gt_le σ hT
  -- the second moment, the same at every height
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hre : ∀ t : ℝ, ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + σ := by
    intro t
    rw [hsline t]
    simp
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ,
      P = ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-2 * (1 / 2 + σ))) := ⟨_, rfl⟩
  have hmom : ∀ t : ℝ,
      (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) = P := by
    intro t
    rw [hRa.integral_norm_randomEulerProduct_sq' (y + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I), hre t, hPdef]
  have hnormsq : ∀ (u : ℂ) (t : ℝ), ‖u / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖u‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := by
    intro u t
    have hd : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 :=
      normSq_ofReal_add_mul_I σ t
    rw [norm_div, div_pow, hd, div_eq_mul_inv]
  have hslice : ∀ t : ℝ, (∫ ω, G ω t ∂μ)
      = P * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) := by
    intro t
    have h1 : (fun ω : Ω => G ω t)
        = fun ω : Ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) :=
      funext fun ω => by rw [hG ω t, hnormsq]; ring
    rw [h1, integral_mul_const, hmom t]
  have hG0 : ∀ (ω : Ω) (t : ℝ), 0 ≤ G ω t := fun ω t => by rw [hG ω t]; positivity
  have hslice' : ∀ t : ℝ, (∫ ω, ‖G ω t‖ ∂μ)
      = P * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) := by
    intro t
    have h1 : (fun ω : Ω => ‖G ω t‖) = fun ω : Ω => G ω t :=
      funext fun ω => Real.norm_of_nonneg (hG0 ω t)
    rw [h1, hslice t]
  -- Tonelli: joint measurability, then the two slice conditions
  have hjm : Measurable (Function.uncurry G) := by
    have huncurry : Measurable fun z : Ω × ℝ =>
        randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1 := by
      have h := measurable_randomEulerProduct_sqfree_uncurry (X := X)
        (fun p hp => hX.measurable p hp) (1 / 2 + σ) (y + 1)
      have hcongr : (fun z : Ω × ℝ =>
          randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1)
          = fun z : Ω × ℝ =>
            randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (z.2 : ℂ) * Complex.I) z.1 :=
        funext fun z => by rw [hsline z.2]
      rw [hcongr]
      exact h
    have hden : Measurable fun z : Ω × ℝ => (σ : ℂ) + (z.2 : ℂ) * Complex.I :=
      ((Complex.measurable_ofReal.comp measurable_snd).mul_const Complex.I).const_add _
    have hwm : Measurable fun z : Ω × ℝ => (1 + z.2 ^ 2) ^ ((1 : ℝ) / 48) := by fun_prop
    have hcongr2 : Function.uncurry G
        = fun z : Ω × ℝ => (1 + z.2 ^ 2) ^ ((1 : ℝ) / 48)
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (z.2 : ℂ) * Complex.I) z.1
            / ((σ : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 :=
      funext fun z => hG z.1 z.2
    rw [hcongr2]
    exact hwm.mul ((huncurry.div hden).norm.pow_const 2)
  have hProd : Integrable (Function.uncurry G) (μ.prod (volume.restrict {t : ℝ | T < |t|})) := by
    refine (integrable_prod_iff' hjm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · have h1 : (fun ω : Ω => Function.uncurry G (ω, t))
          = fun ω : Ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
            * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) :=
        funext fun ω => by rw [Function.uncurry_apply_pair, hG ω t, hnormsq]; ring
      rw [h1]
      exact (hRa.integrable_norm_randomEulerProduct_sq (y + 1) _).mul_const _
    · have h2 : (fun t : ℝ => ∫ ω, ‖Function.uncurry G (ω, t)‖ ∂μ)
          = fun t : ℝ => P * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) :=
        funext fun t => by simp only [Function.uncurry_apply_pair]; exact hslice' t
      rw [h2]
      exact (hwint.const_mul P).integrableOn
  -- Mertens: the second moment is `≪ log y`
  have hPle : P ≤ Real.exp C₂ * Real.log y := by
    rw [hPdef]
    have h := hprod y hy 1 zero_le_one (fun p => (p : ℝ) ^ (-2 * (1 / 2 + σ)))
      (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) ?_
    · rwa [one_mul, Real.rpow_one] at h
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    rw [one_mul]
    calc (p : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
  -- the mean of the far-range functional
  have hZ0 : ∀ ω : Ω, (0 : ℝ) ≤ ∫ t in {t : ℝ | T < |t|}, G ω t :=
    fun ω => setIntegral_nonneg hSmeas fun t _ => hG0 ω t
  have hZi : Integrable (fun ω => ∫ t in {t : ℝ | T < |t|}, G ω t) μ := by
    have h := hProd.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h
    exact h
  have hmean : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) ∂μ)
      ≤ 8 * Real.exp C₂ * T ^ (-(1 / 2 : ℝ)) := by
    rw [integral_const_mul, integral_integral_swap hProd]
    have h1 : (∫ t in {t : ℝ | T < |t|}, ∫ ω, G ω t ∂μ)
        = ∫ t in {t : ℝ | T < |t|}, P * ((1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹) :=
      setIntegral_congr_fun hSmeas fun t _ => hslice t
    rw [h1, integral_const_mul]
    have hP0 : (0 : ℝ) ≤ P := by
      rw [hPdef]
      exact Finset.prod_nonneg fun p _ => by positivity
    have hw0 : (0 : ℝ) ≤ ∫ t in {t : ℝ | T < |t|},
        (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹ :=
      setIntegral_nonneg hSmeas fun t _ => by positivity
    have hstep : P * (∫ t in {t : ℝ | T < |t|},
          (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹)
        ≤ Real.exp C₂ * Real.log y * (8 * T ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul hPle hwtail hw0 (mul_nonneg (Real.exp_pos C₂).le hlogy.le)
    calc (Real.log y)⁻¹ * (P * ∫ t in {t : ℝ | T < |t|},
          (1 + t ^ 2) ^ ((1 : ℝ) / 48) * (σ ^ 2 + t ^ 2)⁻¹)
        ≤ (Real.log y)⁻¹ * (Real.exp C₂ * Real.log y * (8 * T ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hlogy.le)
      _ = 8 * Real.exp C₂ * T ^ (-(1 / 2 : ℝ)) := by
          rw [show Real.exp C₂ * Real.log y * (8 * T ^ (-(1 / 2 : ℝ)))
              = Real.log y * (8 * Real.exp C₂ * T ^ (-(1 / 2 : ℝ))) by ring, ← mul_assoc,
            inv_mul_cancel₀ hlogy.ne', one_mul]
  -- Jensen
  have hZ0' : ∀ ω : Ω, (0 : ℝ) ≤ (Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t :=
    fun ω => mul_nonneg (inv_nonneg.2 hlogy.le) (hZ0 ω)
  have hZi' : Integrable (fun ω => (Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) μ :=
    hZi.const_mul _
  have hZqi : Integrable (fun ω => ((Real.log y)⁻¹ * ∫ t in {t : ℝ | T < |t|}, G ω t) ^ q) μ :=
    integrable_rpow_of_integrable hZi' (Filter.Eventually.of_forall hZ0') hq0.le hq1
  refine ⟨integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0.le hq1, ?_⟩
  refine le_trans (integral_rpow_le_rpow_integral hq0.le hq1
    (Filter.Eventually.of_forall hZ0') hZi' hZqi) ?_
  exact Real.rpow_le_rpow (integral_nonneg fun ω => hZ0' ω) hmean hq0.le

/-! ### The mid range, with the weight -/

/-- `shiftWeight (47/48) n ^ (2/3) = shiftWeight (47/72) n`. -/
lemma shiftWeight_rpow_two_thirds (n : ℤ) :
    shiftWeight (47 / 48) n ^ (2 / 3 : ℝ) = shiftWeight (47 / 72) n := by
  have hpos : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  rw [shiftWeight, shiftWeight, ← Real.rpow_mul hpos.le]
  norm_num

/-- **Small-`q` unit windows with the weights `(1+n²)^{-47/48}`.**  For `x ≥ x₀`,
`0 ≤ q ≤ 2/3`, `0 ≤ σ`, `|σ| log x ≤ η ≤ E₀` (`10E₀ ≤ e^d`) and heights `|n| ≤ (log log x)²`,
`E[(∑_n (1+n²)^{-47/48}·chaosWindowShift x σ n)^q] ≤ (C·(1 + ⅓√⌊m/4⌋)^{-2/3})^{3q/2}`,
`m = harperBlockCount D₀ x`: `RMF.exists_const_integral_rpow_windowSum_chaos_le_rademacher` with
the weights `8(1+n²)⁻¹` replaced; the descent through `2/3` meets
`∑_n (1+n²)^{-47/72}(|n|+1)^{1/4}`, which converges because `47/72 > 5/8`. -/
theorem exists_const_integral_rpow_windowSum_chaos_weight_le_rademacher (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (d : ℕ) (hE₁ : 10 * E₀ ≤ Real.exp d) :
    ∃ (D₀ : ℕ) (x₀ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ η q : ℝ) (s : Finset ℤ), x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 2 / 3 →
          (∀ n ∈ s, |(n : ℝ)| ≤ Real.log (Real.log x) ^ 2) →
          (∫ ω, (∑ n ∈ s, shiftWeight (47 / 48) n
              * chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω)
                ^ q ∂ν)
            ≤ (C * (1 + (1 - 2 / 3) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
                  ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2) := by
  classical
  obtain ⟨D₀, x₁, C₁, cr, hC₁, hcr, H⟩ :=
    exists_const_integral_chaosWindowShift_rpow_le_int_rademacher (Ω := Ω) E₀ hE₀ d hE₁
  obtain ⟨A, hA0, hA⟩ := exists_const_harperWindowLevel_add_two_le hcr
  obtain ⟨Λ, hΛ1, hΛ⟩ := exists_threshold_harperWindowLevel_le 2 hcr
  set W : ℝ := ∑' n : ℤ, shiftWeight (47 / 72) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) with hWdef
  have hWs := summable_shiftWeight_mul_abs_add_one_rpow (q := 47 / 72) (by norm_num)
  have hW0 : 0 ≤ W := by
    refine tsum_nonneg fun n => mul_nonneg (shiftWeight_nonneg _ n) ?_
    exact Real.rpow_nonneg (by positivity) _
  have hCA : 0 ≤ C₁ * A ^ 2 := mul_nonneg hC₁.le (sq_nonneg A)
  refine ⟨D₀, max (max x₁ 2) (Real.exp (Real.exp Λ)), W * (C₁ * A ^ 2) + 1,
    by linarith [mul_nonneg hW0 hCA], ?_⟩
  intro Y ν hY x σ η q s hx hσ hη hηE hση hq0 hq hs
  haveI := hY.isProbabilityMeasure
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_right x₁ 2) (le_max_left _ _)) hx
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left x₁ 2) (le_max_left _ _)) hx
  have hxΛ : Real.exp (Real.exp Λ) ≤ x := le_trans (le_max_right _ _) hx
  -- `log log x ≥ Λ`, so the height condition holds across the whole of `s`
  have hLL : Λ ≤ Real.log (Real.log x) := by
    have h1 : Real.exp Λ ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hxΛ
      rwa [Real.log_exp] at this
    have := Real.log_le_log (Real.exp_pos Λ) h1
    rwa [Real.log_exp] at this
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  set T : ℝ := (1 + (1 - 2 / 3) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
    ^ (-(2 / 3) : ℝ) with hTdef
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  -- the per-window bound, at the fixed exponent `2/3`
  have hb : ∀ n ∈ s, (∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω)
        x σ ((n : ℝ)) ω ^ (2 / 3 : ℝ) ∂ν)
      ≤ (C₁ * A ^ 2 * T) * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
    intro n hn
    have habs : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
    have hlvl : harperWindowLevel cr |(n : ℝ)| ≤ Real.log (Real.log x) / 3 :=
      hΛ _ _ hLL habs (hs n hn)
    have hmain := H Y ν hY x σ η (2 / 3) n hx1 hσ hη hηE hση (by norm_num) (by norm_num) hlvl
    rw [← hTdef] at hmain
    have hce : ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1
        ≤ harperWindowLevel cr |(n : ℝ)| + 2 := by
      linarith [Nat.ceil_lt_add_one (harperWindowLevel_nonneg cr |(n : ℝ)|)]
    have hAle := hA |(n : ℝ)| habs
    have hnn : (0 : ℝ) ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1 := by positivity
    have hsq : (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
        ≤ (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2 :=
      pow_le_pow_left₀ hnn (le_trans hce hAle) 2
    have hid : (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2
        = A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
      rw [mul_pow, ← Real.rpow_natCast ((|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hkey : C₁ * (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
        ≤ C₁ * A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
      calc C₁ * (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
          ≤ C₁ * (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hC₁.le
        _ = C₁ * A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by rw [hid]; ring
    exact le_trans hmain
      (le_of_le_of_eq (mul_le_mul_of_nonneg_right hkey hT0) (by ring))
  -- the descent, with the weights summed at `2/3`
  have hstep := integral_rpow_weightedSum_le_of_two_thirds (μ := ν) s
    (a := fun n => shiftWeight (47 / 48) n)
    (g := fun n ω =>
      chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω)
    (b := fun n => (C₁ * A ^ 2 * T) * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
    (fun n => shiftWeight_nonneg _ n)
    (fun n ω => chaosWindowShift_nonneg hx2 σ ((n : ℝ)) ω)
    (fun n _ => integrable_chaosWindowShift_rademacher hY x σ ((n : ℝ)) hσ0)
    hb hq0 hq
  have hCAT : 0 ≤ C₁ * A ^ 2 * T := mul_nonneg hCA hT0
  refine le_trans hstep (Real.rpow_le_rpow (Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg (shiftWeight_nonneg _ n) _)
      (mul_nonneg hCAT (Real.rpow_nonneg (by positivity) _))) ?_ (by linarith))
  have hsum : ∑ n ∈ s, shiftWeight (47 / 48) n ^ (2 / 3 : ℝ)
        * ((C₁ * A ^ 2 * T) * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
      = (∑ n ∈ s, shiftWeight (47 / 72) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
        * (C₁ * A ^ 2 * T) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by rw [shiftWeight_rpow_two_thirds]; ring
  have hle : (∑ n ∈ s, shiftWeight (47 / 72) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) ≤ W :=
    hWs.sum_le_tsum s fun n _ => mul_nonneg (shiftWeight_nonneg _ n)
      (Real.rpow_nonneg (by positivity) _)
  rw [hsum]
  calc (∑ n ∈ s, shiftWeight (47 / 72) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
        * (C₁ * A ^ 2 * T)
      ≤ W * (C₁ * A ^ 2 * T) := mul_le_mul_of_nonneg_right hle hCAT
    _ = W * (C₁ * A ^ 2) * T := by ring
    _ ≤ (W * (C₁ * A ^ 2) + 1) * T := mul_le_mul_of_nonneg_right (by linarith) hT0

/-! ### The pointwise split of the extended line -/

/-- `(1+n²)^{1/48}/(1+n²) = (1+n²)^{-47/48}`. -/
lemma one_add_sq_rpow_div_eq_shiftWeight (n : ℤ) :
    (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 48) / (1 + (n : ℝ) ^ 2) = shiftWeight (47 / 48) n := by
  have hpos : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  rw [shiftWeight, div_eq_mul_inv ((1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 48)) (1 + (n : ℝ) ^ 2),
    ← Real.rpow_neg_one, ← Real.rpow_add hpos]
  norm_num

omit [MeasurableSpace Ω] in
/-- **The pointwise split of the extended line.**  On a path with `|X(p)| ≤ 1` where the bound of
`RMF.exists_ae_lineDivSq_le_weight` holds at `σ > 0`, for `M ≥ 1`,
`∫_ℝ |F^e(½+σ+it)/(½+σ+it)|² ≤ 2K ∫_ℝ |F(½+σ+it)/(σ+it)|²`
`  + 16K ∑_{n ∈ midWindows M} (1+n²)^{-47/48} ∫_{(n,n+1]} |F(½+σ+it)|²`
`  + K ∫_{|t|>M} (1+t²)^{1/48} |F(½+σ+it)/(σ+it)|²`; the weight is at most `2` on `|t| ≤ 1`, and
`2(1+n²)^{1/48}` on the unit window at `n`, whose denominator costs `8/(1+n²)`. -/
lemma integral_lineDivSq_le_split {X : ℕ → Ω → ℂ} {N : ℕ} {ω : Ω} {K σ : ℝ} (M : ℕ)
    (hK : 0 < K) (hσ : 0 < σ) (hM : 1 ≤ M)
    (hω : ∀ p ∈ Nat.primesBelow N, ‖X p ω‖ ≤ 1)
    (hbound : ∀ t : ℝ, t ≠ 0 → lineDivSq (1 / 2 + σ) X N ω t
      ≤ K * (1 + t ^ 2) ^ ((1 : ℝ) / 48)
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :
    (∫ t : ℝ, lineDivSq (1 / 2 + σ) X N ω t)
      ≤ 2 * K * (∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        + 16 * K * (∑ n ∈ midWindows M, shiftWeight (47 / 48) n
            * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
                lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => X p ω) N ω t)
        + K * ∫ t in {t : ℝ | (M : ℝ) < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
                ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
              / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have hσh : (1 : ℝ) / 2 ≤ 1 / 2 + σ := by linarith
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := fun t => by push_cast; ring
  -- the three integrands are integrable
  have hE : Integrable fun t : ℝ => lineDivSq (1 / 2 + σ) X N ω t :=
    integrable_lineDivSqOf (1 / 2 + σ) hσh
      (measurable_randomEulerProduct_compMult_line (1 / 2 + σ) hσh hω)
      (fun t => norm_randomEulerProduct_le hω (by simpa using hσh))
  have hA : Integrable fun t : ℝ =>
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [hsline]
    exact integrable_line_div_sq hσh hσ hω
  have hWh : Integrable fun t : ℝ => (1 + t ^ 2) ^ ((1 : ℝ) / 48)
      * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    simp only [hsline]
    exact integrable_weight_line_div_sq hσh hσ hω
  have hs3 : MeasurableSet {t : ℝ | (M : ℝ) < |t|} :=
    measurableSet_lt measurable_const measurable_id.abs
  have he0 : ∀ t : ℝ, 0 ≤ lineDivSq (1 / 2 + σ) X N ω t := fun t => by
    unfold lineDivSq
    positivity
  -- the split of `RMF.integral_split_four` at `w = 1`, whose second range is empty
  have hsplit := integral_split_four hE (w := 1) (M := (M : ℝ)) le_rfl hM'
  have hempty : {t : ℝ | 1 < |t| ∧ |t| ≤ 1} = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => absurd ht.2 (not_le.2 ht.1)
  rw [hempty, setIntegral_empty, add_zero] at hsplit
  -- (i) `|t| ≤ 1`, where the weight is at most `2`
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := (0 : ℝ)))]
      with t ht
    exact fun h0 => ht (Set.mem_singleton_iff.2 h0)
  have h1 : (∫ t in Set.Icc (-1 : ℝ) 1, lineDivSq (1 / 2 + σ) X N ω t)
      ≤ 2 * K * ∫ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [← integral_const_mul]
    refine le_trans (setIntegral_mono_ae_restrict hE.integrableOn
      (hA.const_mul (2 * K)).integrableOn ?_)
      (setIntegral_le_integral (hA.const_mul (2 * K))
        (Filter.Eventually.of_forall fun t => mul_nonneg (by linarith) (sq_nonneg _)))
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hnull] with t ht ht0
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hw : (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ 2 := by
      calc (1 + t ^ 2) ^ ((1 : ℝ) / 48) ≤ (2 : ℝ) ^ ((1 : ℝ) / 48) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    refine (hbound t ht0).trans ?_
    calc K * (1 + t ^ 2) ^ ((1 : ℝ) / 48)
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ K * 2 * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hK.le) (sq_nonneg _)
      _ = 2 * K * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by ring
  -- (ii) the unit windows of `1 < |t| ≤ M`
  have h2 : (∫ t in {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)}, lineDivSq (1 / 2 + σ) X N ω t)
      ≤ 16 * K * ∑ n ∈ midWindows M, shiftWeight (47 / 48) n
          * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
              lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => X p ω) N ω t := by
    refine le_trans (setIntegral_le_sum_window_of_cover _ (mid_subset_iUnion_midWindows M) he0
      (fun n _ => hE.integrableOn)) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hmid := one_le_or_le_neg_two_of_mem_midWindows hn
    have hmeasF := measurable_randomEulerProduct_sqfree_line (X := X) (N := N) (ω := ω)
      (1 / 2 + σ)
    have hbdF : ∀ t : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ≤ eulerBound N :=
      fun t => norm_randomEulerProduct_sqfree_le hω (by simpa using hσh)
    have hwin := integrableOn_windowOf (1 / 2 + σ) hmeasF hbdF ((n : ℝ)) ((n : ℝ) + 1)
    rw [← mul_assoc, ← integral_const_mul]
    refine setIntegral_mono_on hE.integrableOn (hwin.const_mul _) measurableSet_Ioc
      fun t ht => ?_
    have ht0 : t ≠ 0 := by
      rcases hmid with h | h
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        exact (by linarith [ht.1] : (0 : ℝ) < t).ne'
      · have hn2 : (n : ℝ) ≤ -2 := by exact_mod_cast h
        exact (by linarith [ht.2] : t < 0).ne
    have hw := one_add_sq_rpow_le_of_mid hmid ht.1 ht.2
    have hd := norm_div_sq_le_of_mid (σ := σ) hmid ht.1 ht.2
      (randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
    have hF : ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
        = lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => X p ω) N ω t := by
      unfold lineSqOf
      rw [hsline]
    refine (hbound t ht0).trans ?_
    rw [← hF]
    calc K * (1 + t ^ 2) ^ ((1 : ℝ) / 48)
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ K * (2 * (1 + (n : ℝ) ^ 2) ^ ((1 : ℝ) / 48))
          * (8 / (1 + (n : ℝ) ^ 2)
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hK.le) hd (sq_nonneg _)
            (mul_nonneg hK.le (by positivity))
      _ = 16 * K * shiftWeight (47 / 48) n
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 := by
          rw [← one_add_sq_rpow_div_eq_shiftWeight]
          ring
  -- (iii) `|t| > M`
  have h3 : (∫ t in {t : ℝ | (M : ℝ) < |t|}, lineDivSq (1 / 2 + σ) X N ω t)
      ≤ K * ∫ t in {t : ℝ | (M : ℝ) < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) N
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hE.integrableOn (hWh.const_mul K).integrableOn hs3
      fun t ht => ?_
    have ht0 : t ≠ 0 := by
      rintro rfl
      have h0 : (M : ℝ) < |(0 : ℝ)| := ht
      rw [abs_zero] at h0
      linarith
    exact (hbound t ht0).trans (le_of_eq (mul_assoc _ _ _))
  rw [hsplit]
  linarith [h1, h2, h3]

/-! ### The assembly -/

/-- `Z ≤ 2K·A + 16K·(L·B) + K·C` gives `Z^q ≤ (2K)^q A^q + (16KL)^q B^q + K^q C^q`. -/
lemma rpow_le_of_le_split {Z A B C L K q : ℝ} (hZ : 0 ≤ Z) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 < K) (hL : 0 < L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (h : Z ≤ 2 * K * A + 16 * K * (L * B) + K * C) :
    Z ^ q ≤ (2 * K) ^ q * A ^ q + (L * (16 * K)) ^ q * B ^ q + K ^ q * C ^ q := by
  have h2K : 0 ≤ 2 * K := by linarith
  have hLK : 0 ≤ L * (16 * K) := mul_nonneg hL.le (by linarith)
  have ha : 0 ≤ 2 * K * A := mul_nonneg h2K hA
  have hb : 0 ≤ L * (16 * K) * B := mul_nonneg hLK hB
  have hc : 0 ≤ K * C := mul_nonneg hK.le hC
  have h' : Z ≤ 2 * K * A + L * (16 * K) * B + K * C := h.trans_eq (by ring)
  calc Z ^ q ≤ (2 * K * A + L * (16 * K) * B + K * C) ^ q := Real.rpow_le_rpow hZ h' hq0.le
    _ ≤ (2 * K * A) ^ q + (L * (16 * K) * B) ^ q + (K * C) ^ q := by
        have h1 := Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc hq0.le hq1
        have h2 := Real.rpow_add_le_add_rpow ha hb hq0.le hq1
        linarith
    _ = (2 * K) ^ q * A ^ q + (L * (16 * K)) ^ q * B ^ q + K ^ q * C ^ q := by
        rw [Real.mul_rpow h2K hA, Real.mul_rpow hLK hB, Real.mul_rpow hK.le hC]

/-- The arithmetic of the assembly: `a^q ≤ max 1 a`, `v ≤ u` and `1 ≤ u`. -/
lemma extended_damped_arith {EA EB EC a b c L Λq Kc Cm Ct u v q : ℝ}
    (hL : 0 < L) (hq0 : 0 < q) (hq1 : q ≤ 1) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hΛq : 0 ≤ Λq) (hu : 1 ≤ u) (hv : v ≤ u) (hKc : 0 < Kc)
    (hEA0 : 0 ≤ EA) (hEB0 : 0 ≤ EB) (hEC0 : 0 ≤ EC)
    (hEA : EA ≤ L ^ q * (Kc * (v * Λq)))
    (hEB : EB ≤ 9 * max 1 Cm * Λq)
    (hEC : EC ≤ L ^ q * (max 1 Ct * Λq)) :
    a ^ q * EA + (L * b) ^ q * EB + c ^ q * EC
      ≤ (max 1 a * Kc + max 1 b * (9 * max 1 Cm) + max 1 c * max 1 Ct) * u * L ^ q * Λq := by
  have hLq : 0 < L ^ q := Real.rpow_pos_of_pos hL q
  have haq := rpow_le_max_one ha hq0.le hq1
  have hbq := rpow_le_max_one hb hq0.le hq1
  have hcq := rpow_le_max_one hc hq0.le hq1
  have hma : (0 : ℝ) ≤ max 1 a := le_trans zero_le_one (le_max_left _ _)
  have hmb : (0 : ℝ) ≤ max 1 b := le_trans zero_le_one (le_max_left _ _)
  have hmc : (0 : ℝ) ≤ max 1 c := le_trans zero_le_one (le_max_left _ _)
  have hmCm : (0 : ℝ) ≤ max 1 Cm := le_trans zero_le_one (le_max_left _ _)
  have hmCt : (0 : ℝ) ≤ max 1 Ct := le_trans zero_le_one (le_max_left _ _)
  have t1 : a ^ q * EA ≤ max 1 a * Kc * u * L ^ q * Λq := by
    calc a ^ q * EA ≤ max 1 a * (L ^ q * (Kc * (v * Λq))) := mul_le_mul haq hEA hEA0 hma
      _ ≤ max 1 a * (L ^ q * (Kc * (u * Λq))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hv hΛq) hKc.le) hLq.le) hma
      _ = max 1 a * Kc * u * L ^ q * Λq := by ring
  have t2 : (L * b) ^ q * EB ≤ max 1 b * (9 * max 1 Cm) * u * L ^ q * Λq := by
    rw [Real.mul_rpow hL.le hb.le]
    have h9 : 0 ≤ 9 * max 1 Cm * Λq := mul_nonneg (mul_nonneg (by norm_num) hmCm) hΛq
    calc L ^ q * b ^ q * EB ≤ L ^ q * max 1 b * (9 * max 1 Cm * Λq) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbq hLq.le) hEB hEB0 (mul_nonneg hLq.le hmb)
      _ ≤ L ^ q * max 1 b * (9 * max 1 Cm * Λq) * u :=
          le_mul_of_one_le_right (mul_nonneg (mul_nonneg hLq.le hmb) h9) hu
      _ = max 1 b * (9 * max 1 Cm) * u * L ^ q * Λq := by ring
  have t3 : c ^ q * EC ≤ max 1 c * max 1 Ct * u * L ^ q * Λq := by
    calc c ^ q * EC ≤ max 1 c * (L ^ q * (max 1 Ct * Λq)) := mul_le_mul hcq hEC hEC0 hmc
      _ ≤ max 1 c * (L ^ q * (max 1 Ct * Λq)) * u :=
          le_mul_of_one_le_right (mul_nonneg hmc (mul_nonneg hLq.le (mul_nonneg hmCt hΛq))) hu
      _ = max 1 c * max 1 Ct * u * L ^ q * Λq := by ring
  have hR : (max 1 a * Kc + max 1 b * (9 * max 1 Cm) + max 1 c * max 1 Ct) * u * L ^ q * Λq
      = max 1 a * Kc * u * L ^ q * Λq + max 1 b * (9 * max 1 Cm) * u * L ^ q * Λq
        + max 1 c * max 1 Ct * u * L ^ q * Λq := by ring
  rw [hR]
  linarith

/-- **The subtracted term of the extended reduction.**  There are `K, x₀`, independent of `X`, `V`,
`x` and `q`, such that for every Rademacher `X`, `V ≥ 1`, `x ≥ x₀` and `0 < q < ½`,
`E[(∫_ℝ |F^e(½+V/log x+it)/(½+V/log x+it)|² dt)^q]`
`  ≤ K (1+(q(1-2q))⁻¹) (log x)^q (log log x)^{-q/2}`.  The shift moves to `1/log x`, where the
pointwise split `RMF.integral_lineDivSq_le_split` at `M = ⌈log log x⌉` leaves three pieces of
the Rademacher product. -/
theorem exists_const_integral_rpow_lineDivSq_extended_le :
    ∃ K x₀ : ℝ, 0 < K ∧ ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ V x q : ℝ, 1 ≤ V → x₀ ≤ x → 0 < q → q < 1 / 2 →
        (∫ ω, (∫ t : ℝ, lineDivSq (1 / 2 + V / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q ∂μ)
          ≤ K * (1 + (q * (1 - 2 * q))⁻¹) * Real.log x ^ q
            * Real.log (Real.log x) ^ (-(q / 2)) := by
  classical
  have h10 : (10 : ℝ) * 1 ≤ Real.exp ((3 : ℕ) : ℝ) := by
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : Real.exp ((3 : ℕ) : ℝ) = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    have h2 : (2.7 : ℝ) * 2.7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    rw [h3]
    nlinarith
  obtain ⟨K₁, hK₁, HK⟩ := exists_ae_lineDivSq_le_weight (Ω := Ω)
  obtain ⟨Kc, x₃, hKc, Hc⟩ := exists_const_integral_rpow_lineDiv_floor_le (Ω := Ω)
  obtain ⟨D₀, xm, Cm, hCm, Hm⟩ :=
    exists_const_integral_rpow_windowSum_chaos_weight_le_rademacher (Ω := Ω) 1 zero_le_one 3 h10
  obtain ⟨Ct, hCt, Ht⟩ := exists_integral_rpow_eulerProductLine_weight_tail_le (Ω := Ω)
  have hLL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (max (max x₃ xm) 4)).and
      (hLL.eventually_ge_atTop (8 + 2 * (D₀ : ℝ))))
  have hma : (0 : ℝ) < max 1 (2 * K₁) := lt_max_of_lt_left one_pos
  have hmb : (0 : ℝ) < max 1 (16 * K₁) := lt_max_of_lt_left one_pos
  have hmc : (0 : ℝ) < max 1 K₁ := lt_max_of_lt_left one_pos
  have hmCm : (0 : ℝ) < max 1 Cm := lt_max_of_lt_left one_pos
  have hmCt : (0 : ℝ) < max 1 Ct := lt_max_of_lt_left one_pos
  refine ⟨max 1 (2 * K₁) * Kc + max 1 (16 * K₁) * (9 * max 1 Cm) + max 1 K₁ * max 1 Ct, x₀,
    add_pos (add_pos (mul_pos hma hKc) (mul_pos hmb (by linarith))) (mul_pos hmc hmCt),
    fun X μ hX V x q hV hx hq0 hq2 => ?_⟩
  obtain ⟨hxm, hΛD⟩ := hx₀ x hx
  haveI := hX.isProbabilityMeasure
  have hx₃ : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxm
  have hxm' : xm ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxm
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) hxm
  have hx0 : (0 : ℝ) < x := by linarith
  have hD₀0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hΛD' : 8 + 2 * (D₀ : ℝ) ≤ Real.log (Real.log x) := hΛD
  have hΛ1 : (1 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hΛ0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hq1 : q ≤ 1 := by linarith
  have hα : 0 < q * (1 - 2 * q) := mul_pos hq0 (by linarith)
  -- `y = ⌊x⌋`
  have hy2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ x))
  have hy2' : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hy2
  have hlogy0 : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogyx : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by linarith) (Nat.floor_le hx0.le)
  -- the shift `σ = 1/log x`, with `σ log(⌊x⌋+1) ≤ 2`
  have hσ0 : (0 : ℝ) < 1 / Real.log x := by positivity
  have hσ0' : (0 : ℝ) < 1 / 2 + 1 / Real.log x := by linarith
  have hσN : 1 / Real.log x * Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 := by
    have hN : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x ^ 2 := by
      push_cast
      nlinarith [Nat.floor_le hx0.le]
    have hlogN : Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log x := by
      have h := Real.log_le_log (by positivity) hN
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hL0]
    linarith
  have hσh : (1 : ℝ) / 2 ≤ 1 / 2 + 1 / Real.log x := by linarith
  refine le_trans (integral_rpow_lineDivSq_le_of_le hX ⌊x⌋₊ (σ₁ := 1 / 2 + 1 / Real.log x)
    (σ₂ := 1 / 2 + V / Real.log x) hσh
    (by linarith [div_le_div_of_nonneg_right hV hL0.le]) hq0.le) ?_
  -- the cut `M = ⌈log log x⌉`
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌈Real.log (Real.log x)⌉₊ := ⟨_, rfl⟩
  have hMlo : Real.log (Real.log x) ≤ (M : ℝ) := by rw [hMdef]; exact Nat.le_ceil _
  have hMhi : (M : ℝ) < Real.log (Real.log x) + 1 := by
    rw [hMdef]; exact Nat.ceil_lt_add_one hΛ0.le
  have hM1' : (1 : ℝ) ≤ (M : ℝ) := by linarith
  have hM1 : 1 ≤ M := by exact_mod_cast hM1'
  have hMsq : (M : ℝ) + 1 ≤ Real.log (Real.log x) ^ 2 := by nlinarith
  -- the barrier depth at `x`: `log log x ≤ 9⌊m/4⌋`
  have hD₀Λ : (D₀ : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hcast := cast_harperBlockCount hD₀Λ
  have hfl : Real.log (Real.log x) - 1 ≤ ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one (Real.log (Real.log x))]
  have hm4 : harperBlockCount D₀ x ≤ 4 * (harperBlockCount D₀ x / 4) + 3 := by omega
  have hm4R : ((harperBlockCount D₀ x : ℕ) : ℝ)
      ≤ 4 * ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hm4
  rw [hcast] at hm4R
  have hbar : Real.log (Real.log x) ≤ 9 * ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := by linarith
  have hbpos : (0 : ℝ) < 1 + (1 - 2 / 3) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := by
    have := Real.sqrt_nonneg ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)
    linarith
  have hsq9 : Real.sqrt (Real.log (Real.log x)) ≤ 9 * (1 + (1 - 2 / 3)
      * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) := by
    have h1 : Real.sqrt (Real.log (Real.log x))
        ≤ Real.sqrt (9 * ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hbar
    have h2 : Real.sqrt (9 * ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
        = 3 * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h2] at h1
    have := Real.sqrt_nonneg ((harperBlockCount D₀ x / 4 : ℕ) : ℝ)
    linarith
  -- the pointwise bound
  have hwin : ∀ (ω : Ω) (n : ℤ), (∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
      lineSqOf (1 / 2 + 1 / Real.log x) (fun ω => squarefreeExtension fun p => X p ω)
        (⌊x⌋₊ + 1) ω t)
      = Real.log x * chaosWindowShift (fun ω => squarefreeExtension fun p => X p ω) x
          (1 / Real.log x) ((n : ℝ)) ω := by
    intro ω n
    rw [chaosWindowShift_eq_window (X := X) x (1 / Real.log x) ω n, ← mul_assoc,
      mul_inv_cancel₀ hL0.ne', one_mul]
  have hpt : ∀ᵐ ω ∂μ, (∫ t : ℝ, lineDivSq (1 / 2 + 1 / Real.log x) X (⌊x⌋₊ + 1) ω t) ^ q
      ≤ (2 * K₁) ^ q * (∫ t : ℝ,
            ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q
        + (Real.log x * (16 * K₁)) ^ q * (∑ n ∈ midWindows M, shiftWeight (47 / 48) n
            * chaosWindowShift (fun ω => squarefreeExtension fun p => X p ω) x
              (1 / Real.log x) ((n : ℝ)) ω) ^ q
        + K₁ ^ q * (∫ t in {t : ℝ | (M : ℝ) < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
                ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
              / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q := by
    filter_upwards [ae_forall_norm_le_one hX norm_le_one_rademacherLaw (⌊x⌋₊ + 1),
      HK X μ hX (⌊x⌋₊ + 1) (by omega)] with ω hω hK
    have hsp := integral_lineDivSq_le_split M hK₁ hσ0 hM1 hω
      (fun t ht => hK (1 / Real.log x) t hσ0 hσN ht)
    simp only [hwin ω] at hsp
    have hsum : ∑ n ∈ midWindows M, shiftWeight (47 / 48) n
          * (Real.log x * chaosWindowShift (fun ω => squarefreeExtension fun p => X p ω) x
              (1 / Real.log x) ((n : ℝ)) ω)
        = Real.log x * ∑ n ∈ midWindows M, shiftWeight (47 / 48) n
          * chaosWindowShift (fun ω => squarefreeExtension fun p => X p ω) x
              (1 / Real.log x) ((n : ℝ)) ω := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hsum] at hsp
    refine rpow_le_of_le_split (integral_nonneg fun t => by unfold lineDivSq; positivity)
      (integral_nonneg fun t => sq_nonneg _)
      (Finset.sum_nonneg fun n _ => mul_nonneg (shiftWeight_nonneg _ n)
        (chaosWindowShift_nonneg (by linarith) _ _ ω))
      (setIntegral_nonneg (measurableSet_lt measurable_const measurable_id.abs)
        fun t _ => by positivity) hK₁ hL0 hq0 hq1 hsp
  -- the three moments are integrable
  have hIA : Integrable (fun ω => (2 * K₁) ^ q * (∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
        / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ :=
    (integrable_rpow_eulerProductLine_of_two_le hX hy2 hσ0 hq0.le).const_mul _
  have hIB : Integrable (fun ω => (Real.log x * (16 * K₁)) ^ q * (∑ n ∈ midWindows M,
      shiftWeight (47 / 48) n * chaosWindowShift (fun ω => squarefreeExtension fun p => X p ω) x
        (1 / Real.log x) ((n : ℝ)) ω) ^ q) μ := by
    refine Integrable.const_mul ?_ _
    exact integrable_rpow_of_integrable
      (integrable_finsetSum _ fun n _ =>
        (integrable_chaosWindowShift_rademacher hX x (1 / Real.log x) ((n : ℝ)) hσ0').const_mul _)
      (Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun n _ =>
        mul_nonneg (shiftWeight_nonneg _ n) (chaosWindowShift_nonneg (by linarith) _ _ ω))
      hq0.le hq1
  obtain ⟨hICt, hEC⟩ := Ht X μ hX q hq0 hq1 ⌊x⌋₊ hy2 (1 / Real.log x) (M : ℝ) hσ0 hM1'
  have hIC := hICt.const_mul (K₁ ^ q)
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    Real.rpow_nonneg (integral_nonneg fun t => by unfold lineDivSq; positivity) _)
    ((hIA.add hIB).add hIC) hpt) ?_
  simp only [Pi.add_apply]
  refine le_trans (integral_add_le (hIA.add hIB) hIC
    (integral_add_le hIA hIB (le_of_eq (integral_const_mul _ _))
      (le_of_eq (integral_const_mul _ _))) (le_of_eq (integral_const_mul _ _))) ?_
  -- the three moments
  have hEA := le_trans (integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
      (J := fun ω => ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      hlogy0 hlogyx hq0.le (fun ω => integral_nonneg fun t => sq_nonneg _))
    (mul_le_mul_of_nonneg_left (Hc X μ hX x q hx₃ hq0 hq2) (Real.rpow_nonneg hL0.le _))
  have hEB := le_trans (Hm X μ hX x (1 / Real.log x) 1 q (midWindows M) hxm' hσ0.le
      zero_le_one le_rfl
      (le_of_eq (by rw [abs_of_pos hσ0, one_div, inv_mul_cancel₀ hL0.ne'])) hq0.le
      (by linarith) (fun n hn => (abs_le_of_mem_midWindows hn).trans hMsq))
    (mid_le_target hCm hΛ1 hq0 hq2.le hbpos hsq9)
  have hEC' : (∫ ω, (∫ t in {t : ℝ | (M : ℝ) < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ Real.log x ^ q * (max 1 Ct * Real.log (Real.log x) ^ (-(q / 2))) := by
    refine le_trans (integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
      (J := fun ω => ∫ t in {t : ℝ | (M : ℝ) < |t|}, (1 + t ^ 2) ^ ((1 : ℝ) / 48)
        * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
            ((1 / 2 : ℂ) + ((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
          / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      hlogy0 hlogyx hq0.le (fun ω => setIntegral_nonneg
        (measurableSet_lt measurable_const measurable_id.abs) fun t _ => by positivity)) ?_
    refine mul_le_mul_of_nonneg_left (le_trans hEC ?_) (Real.rpow_nonneg hL0.le _)
    have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
    rw [Real.mul_rpow hCt.le (Real.rpow_nonneg hM0.le _), ← Real.rpow_mul hM0.le]
    have h1 : Ct ^ q ≤ max 1 Ct := rpow_le_max_one hCt hq0.le hq1
    have h2 : (M : ℝ) ^ (-(1 / 2 : ℝ) * q) ≤ Real.log (Real.log x) ^ (-(q / 2)) := by
      rw [show -(1 / 2 : ℝ) * q = -(q / 2) by ring]
      exact Real.rpow_le_rpow_of_nonpos hΛ0 hMlo (by linarith)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hM0.le _) hmCt.le
  have hu1 : (1 : ℝ) ≤ 1 + (q * (1 - 2 * q))⁻¹ := by linarith [inv_pos.2 hα]
  exact extended_damped_arith hL0 hq0 hq1 (by linarith) (by linarith) hK₁
    (Real.rpow_nonneg hΛ0.le _) hu1 (min_le_right _ _) hKc
    (integral_nonneg fun ω => Real.rpow_nonneg (integral_nonneg fun t => sq_nonneg _) _)
    (integral_nonneg fun ω => Real.rpow_nonneg (Finset.sum_nonneg fun n _ =>
      mul_nonneg (shiftWeight_nonneg _ n) (chaosWindowShift_nonneg (by linarith) _ _ ω)) _)
    (integral_nonneg fun ω => Real.rpow_nonneg (setIntegral_nonneg
      (measurableSet_lt measurable_const measurable_id.abs) fun t _ => by positivity) _)
    hEA hEB hEC'

end RMF
