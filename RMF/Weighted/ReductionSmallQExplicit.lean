/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Assembly
import RMF.Weighted.SmoothTail
import RMF.Weighted.EulerMomentSmallQExplicit
import RMF.Weighted.CentralWindowExplicit
import RMF.NumberTheory.MertensUniform

/-!
# The reduction below `q = ½`, with its constants

The small-`q` reduction (`RMF.exists_integral_rpow_weightedRademacherSum_le`) with every constant
explicit and the power `q` kept on each:

`E|S(x)|^{2q} ≤ E|F_y(½)|^{2q} + (∑_{x<m, m y-smooth sqfree} 1/m)^q + C_R^q·E[Z^q] + E_err^q`

(`RMF.integral_rpow_weightedRademacherSum_le_reduction_explicit`), for `0 ≤ q ≤ ½`, with
`Z = (log y)⁻¹∫_ℝ‖F_y(½+σ+it)/(σ+it)‖²dt`.  It branches from
`RMF.integral_rpow_weightedRademacherSum_le_eulerProduct`, whose first two terms already carry
the constant `1`, and redoes the rough sum:

* **the smoothing split is `(1+ε, 1+1/ε)`**, not `(2, 2)`
  (`RMF.sum_weightedRoughTerm_le_setIntegral_eps`), so the main term keeps `1 + ε`;
* **the sieve is Brun–Titchmarsh at a level `z ≤ y`**
  (`RMF.sum_inv_sq_indicator_le_brun`): the rough `r` near `t` number at most
  `2H/log z + 5z(1+log z)³`, `H = tη/(1+η) + 1`, for any natural `2 ≤ z ≤ y`;
* **the Parseval step keeps its coefficient**
  (`RMF.setIntegral_normSq_mul_sieve_le_explicit`): `(x/y)^{2σ} ≤ e^{2c}` when
  `σ log(x/y) ≤ c`, and the `(2π)⁻¹` is not spent.

The result is `C_R = (1+ε)·C_z·((1+η) + (1+η)²/(ηy))·e^{2c}/(2π)` (`RMF.smallQReductionConst`)
with `C_z = 2 log y/log z + 5z(1+log z)³·log y·(1+η)/(yη + 1 + η)` (`RMF.smallQSieveConst`); it
tends to `(1+ε)e^{2c}/π` as the two correction terms vanish.  The error is
`E_err = (1+1/ε)(η(1 + log x) + (1+η)(2/log z + 5z(1+log z)³/x))` (`RMF.smallQReductionErr`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The smoothing step with a `(1+ε)` split -/

omit [MeasurableSpace Ω] in
/-- `‖a‖² ≤ (1+ε)‖b‖² + (1+1/ε)‖a-b‖²` for `ε > 0`. -/
lemma normSq_le_one_add_eps (a b : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖a‖ ^ 2 ≤ (1 + ε) * ‖b‖ ^ 2 + (1 + 1 / ε) * ‖a - b‖ ^ 2 := by
  have h : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    calc ‖a‖ = ‖b + (a - b)‖ := by ring_nf
      _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
  have hsq : ‖a‖ ^ 2 ≤ (‖b‖ + ‖a - b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg a) h 2
  have key : 2 * ‖b‖ * ‖a - b‖ ≤ ε * ‖b‖ ^ 2 + (1 / ε) * ‖a - b‖ ^ 2 := by
    have h0 : 0 ≤ (ε * ‖b‖ - ‖a - b‖) ^ 2 / ε := by positivity
    have e : (ε * ‖b‖ - ‖a - b‖) ^ 2 / ε
        = ε * ‖b‖ ^ 2 - 2 * ‖b‖ * ‖a - b‖ + (1 / ε) * ‖a - b‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith [hsq, key]

/-- **The averaging step with a `(1+ε)` split, for any function.**  Integrating
`RMF.normSq_le_one_add_eps` over `t ∈ [r, r(1+η)]`. -/
lemma normSq_average_bound_eps (G : ℝ → ℂ) (x : ℝ) {r η ε : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hε : 0 < ε)
    (h₁ : IntervalIntegrable (fun t => ‖G (x / t)‖ ^ 2) volume r (r * (1 + η)))
    (h₂ : IntervalIntegrable (fun t => ‖G (x / r) - G (x / t)‖ ^ 2) volume r (r * (1 + η))) :
    (η * r) * ‖G (x / r)‖ ^ 2
      ≤ (1 + ε) * (∫ t in r..(r * (1 + η)), ‖G (x / t)‖ ^ 2)
        + (1 + 1 / ε) * (∫ t in r..(r * (1 + η)), ‖G (x / r) - G (x / t)‖ ^ 2) := by
  have hle : r ≤ r * (1 + η) := by nlinarith
  have hconst : (∫ _t in r..(r * (1 + η)), ‖G (x / r)‖ ^ 2) = (η * r) * ‖G (x / r)‖ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [← hconst, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (h₁.const_mul (1 + ε)) (h₂.const_mul (1 + 1 / ε))]
  refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
    ((h₁.const_mul (1 + ε)).add (h₂.const_mul (1 + 1 / ε))) fun t _ => ?_
  exact normSq_le_one_add_eps _ _ hε

omit [MeasurableSpace Ω] in
/-- `RMF.sum_div_le_of_average` with a constant `K` in the averaging bound in place of `2`. -/
theorem sum_div_le_of_average_const {S : Finset ℕ} {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    {g : ℝ → ℝ} {e : ℕ → ℝ} {J : ℝ} (hS : ∀ r ∈ S, 0 < r)
    (havg : ∀ r ∈ S, (η * (r : ℝ)) * g (r : ℝ)
      ≤ K * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t) + e r)
    (hexch : ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
      * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t) ≤ J) :
    ∑ r ∈ S, g (r : ℝ) / (r : ℝ)
      ≤ (K / η) * J + (1 / η) * ∑ r ∈ S, e r / ((r : ℝ)) ^ 2 := by
  have hstep : ∀ r ∈ S, g (r : ℝ) / (r : ℝ)
      ≤ (K / η) * ((((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
        + (1 / η) * (e r / ((r : ℝ)) ^ 2) := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS r hr
    have hden : (0 : ℝ) < η * (r : ℝ) ^ 2 := by positivity
    calc g (r : ℝ) / (r : ℝ)
        = (η * (r : ℝ) * g (r : ℝ)) / (η * (r : ℝ) ^ 2) := by
          field_simp
      _ ≤ (K * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t) + e r)
            / (η * (r : ℝ) ^ 2) := by
          gcongr
          exact havg r hr
      _ = (K / η) * ((((r : ℝ)) ^ 2)⁻¹
              * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
            + (1 / η) * (e r / ((r : ℝ)) ^ 2) := by
          field_simp
  calc ∑ r ∈ S, g (r : ℝ) / (r : ℝ)
      ≤ ∑ r ∈ S, ((K / η) * ((((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
          + (1 / η) * (e r / ((r : ℝ)) ^ 2)) := Finset.sum_le_sum hstep
    _ = (K / η) * (∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
            * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)), g t))
          + (1 / η) * ∑ r ∈ S, e r / ((r : ℝ)) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (K / η) * J + (1 / η) * ∑ r ∈ S, e r / ((r : ℝ)) ^ 2 := by
        gcongr

omit [MeasurableSpace Ω] in
/-- **The smoothing step with a `(1+ε)` split, composed with the exchange.**  The rough sum is at
most `(1+ε)/η` times a single integral against the counting bound `b`, plus `(1+1/ε)/(2η)` times
the smoothing errors in the form of `RMF.integral_sum_setIntegral_normSq_sub_le`. -/
theorem sum_weightedRoughTerm_le_setIntegral_eps {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) {x η ε : ℝ} (hx : 0 ≤ x) (hη : 0 < η) (hε : 0 < ε)
    {S : Finset ℕ} (hS : ∀ r ∈ S, 0 < r) {T : Set ℝ} (hTm : MeasurableSet T) {b : ℝ → ℝ}
    (hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)) ⊆ T)
    (hb : ∀ t ∈ T, ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t ≤ b t)
    (hint : ∀ r ∈ S, IntegrableOn (fun t => (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator
            (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2) t) T volume)
    (hintT : IntegrableOn
      (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 * b t) T volume) :
    ∑ r ∈ S, weightedRoughTerm f y x ω r
      ≤ ((1 + ε) / η) * (∫ t in T, ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 * b t)
        + ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖smoothWeightedSum f y (x / r) ω - smoothWeightedSum f y (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 := by
  set G : ℝ → ℂ := fun u => smoothWeightedSum f y u ω with hGdef
  have hterm : ∀ r ∈ S, weightedRoughTerm f y x ω r
      = (fun t => ‖G (x / t)‖ ^ 2) (r : ℝ) / (r : ℝ) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hS r hr
    rw [weightedRoughTerm]
    field_simp
    rfl
  rw [Finset.sum_congr rfl hterm]
  have hexch := sum_smul_setIntegral_le
    (g := fun t => ‖G (x / t)‖ ^ 2) (b := b) (S := S)
    (I := fun r => Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)))
    (c := fun r => (((r : ℝ)) ^ 2)⁻¹)
    (fun t => by positivity) hsub (fun r _ => measurableSet_Icc) hint hintT hb hTm
  refine le_trans (sum_div_le_of_average_const (K := 1 + ε) (g := fun t => ‖G (x / t)‖ ^ 2)
    (e := fun r => (1 + 1 / ε) * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
      ‖G (x / r) - G (x / t)‖ ^ 2))
    hη (by positivity) hS (fun r hr => ?_) hexch) (le_of_eq ?_)
  · have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS r hr
    have hle : (r : ℝ) ≤ (r : ℝ) * (1 + η) := by nlinarith
    have hkey := normSq_average_bound_eps G x hr0 hη hε
      (intervalIntegrable_normSq_smoothWeightedSum hbnd y hx hr0
        (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
      (intervalIntegrable_normSq_smoothWeightedSum_sub hbnd y hx hr0
        (le_mul_of_one_le_right (Nat.cast_nonneg r) (by linarith)))
    rw [intervalIntegral_eq_setIntegral_Icc hle, intervalIntegral_eq_setIntegral_Icc hle]
      at hkey
    exact hkey
  · congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
    ring

/-! ### The principal term, with its coefficient -/

/-- `v/w ≤ e^c·v/w^{1+s}` whenever `w^s ≤ e^c`. -/
lemma div_le_exp_mul_div_rpow {v w s c : ℝ} (hv : 0 ≤ v) (hw : 0 < w)
    (hs : w ^ s ≤ Real.exp c) : v / w ≤ Real.exp c * (v / w ^ (1 + s)) := by
  have hws : (0 : ℝ) < w ^ s := Real.rpow_pos_of_pos hw s
  have hsplit : w ^ (1 + s) = w * w ^ s := by rw [Real.rpow_add hw, Real.rpow_one]
  rw [hsplit, mul_div_assoc', div_le_div_iff₀ hw (mul_pos hw hws)]
  linarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hv hw.le)]

omit [MeasurableSpace Ω] in
/-- **The principal term with its coefficient.**  For `σ·log(x/y) ≤ c`, `K, C ≥ 0`,
`(K/η)·∫_{[y, x(1+η)]} ‖A_y(x/t)‖²·C(1+η)²(tη/(1+η)+1)/(t² log y) dt` is at most
`K·C·((1+η)²(η/(1+η) + 1/y)/η)·e^{2c}·(2π)⁻¹` times `(log y)⁻¹∫_ℝ‖F_y(½+σ+it)/(σ+it)‖²dt`.
`RMF.setIntegral_normSq_mul_sieve_le` with the coefficient kept: `(x/y)^{2σ} ≤ e^{2c}` replaces
`e²`, and the `(2π)⁻¹` of Parseval is not spent. -/
theorem setIntegral_normSq_mul_sieve_le_explicit {X : ℕ → Ω → ℂ} (y : ℕ) {σ x η C K c : ℝ}
    (hy : (0 : ℝ) < y) (hyx : (y : ℝ) ≤ x) (hσ : 0 < σ) (hσlog : σ * Real.log (x / y) ≤ c)
    (hη : 0 < η) (hC : 0 ≤ C) (hK : 0 ≤ K) (hlogy : 0 < Real.log y) (ω : Ω) :
    (K / η) * (∫ t in Set.Icc ((y : ℝ)) (x * (1 + η)),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ K * C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ)) / η) * Real.exp (2 * c)
          * (2 * Real.pi)⁻¹ * ((Real.log y)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hpars := integral_normSq_smoothWeightedSum_eq_line (X := X) y hσ ω
  have hIint := integrableOn_normSq_smoothWeightedSum (X := X) y hσ ω
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set P : ℝ := ∫ t : ℝ, ‖randomEulerProduct f (y + 1)
      ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 with hPdef
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hy hyx
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hb : (y : ℝ) ≤ x * (1 + η) := le_trans hyx (le_mul_of_one_le_right hx0.le (by linarith))
  have hgb : ∀ t ∈ Set.Icc ((y : ℝ)) (x * (1 + η)),
      ‖smoothWeightedSum f y (x / t) ω‖
        ≤ ∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖ :=
    fun t ht =>
      norm_smoothWeightedSum_le_sum f y (div_le_div_of_nonneg_left hx0.le hy ht.1) ω
  have hmeas : Measurable fun t : ℝ => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 := by
    have h1 : Measurable fun t : ℝ => smoothWeightedSum f y (x / t) ω :=
      (measurable_smoothWeightedSum_truncation f y ω).comp (measurable_const.div measurable_id)
    fun_prop
  have hint1 : IntegrableOn (fun t => ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 / t)
      (Set.Icc ((y : ℝ)) (x * (1 + η))) volume := by
    refine Measure.integrableOn_of_bounded
      (M := (∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖) ^ 2 / (y : ℝ))
      measure_Icc_lt_top.ne (hmeas.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hy ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ht0.le)]
    calc ‖smoothWeightedSum f y (x / t) ω‖ ^ 2 / t
        ≤ (∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖) ^ 2 / t := by
          gcongr
          exact hgb t ht
      _ ≤ (∑ k ∈ Finset.Icc 1 ⌊x / (y : ℝ)⌋₊, ‖f ω k / (Real.sqrt k : ℂ)‖) ^ 2 / (y : ℝ) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hy ht.1
  have hstep12 : (∫ t in Set.Icc ((y : ℝ)) (x * (1 + η)),
        ‖smoothWeightedSum f y (x / t) ω‖ ^ 2
          * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
              ‖smoothWeightedSum f y w ω‖ ^ 2 / w :=
    setIntegral_mul_sieveShape_le (fun u => ‖smoothWeightedSum f y u ω‖ ^ 2) hx0 hy hb hη
      hC hlogy (fun _ => sq_nonneg _) hint1
  have hlow : (0 : ℝ) < x / (x * (1 + η)) := div_pos hx0 (mul_pos hx0 h1η)
  have hsub : Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)) ⊆ Set.Ioi (0 : ℝ) :=
    fun w hw => lt_trans hlow hw.1
  have hcmp : ∀ w ∈ Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
      ‖smoothWeightedSum f y w ω‖ ^ 2 / w
        ≤ Real.exp (2 * c) * (‖smoothWeightedSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := lt_trans hlow hw.1
    rcases lt_or_ge w 1 with hlt | hge
    · rw [smoothWeightedSum_eq_zero_of_lt_one f y hlt ω]
      simp
    · refine div_le_exp_mul_div_rpow (sq_nonneg _) hw0 ?_
      rw [Real.rpow_def_of_pos hw0]
      refine Real.exp_le_exp.2 ?_
      have hlogw : Real.log w ≤ Real.log (x / (y : ℝ)) := Real.log_le_log hw0 hw.2.le
      have hσ2 : (0 : ℝ) ≤ 2 * σ := by linarith
      have h1 : Real.log w * (2 * σ) ≤ Real.log (x / (y : ℝ)) * (2 * σ) :=
        mul_le_mul_of_nonneg_right hlogw hσ2
      have h2 : Real.log (x / (y : ℝ)) * (2 * σ) = 2 * (σ * Real.log (x / (y : ℝ))) := by ring
      linarith
  have hstep3 : (∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
        ‖smoothWeightedSum f y w ω‖ ^ 2 / w)
      ≤ Real.exp (2 * c) * ∫ u in Set.Ioi (0 : ℝ),
          ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
    calc (∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
            ‖smoothWeightedSum f y w ω‖ ^ 2 / w)
        ≤ ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
            Real.exp (2 * c) * (‖smoothWeightedSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ)) := by
          refine integral_mono_of_nonneg ?_ ((hIint.mono_set hsub).const_mul _) ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact div_nonneg (sq_nonneg _) (lt_trans hlow hw.1).le
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
            exact hcmp w hw
      _ = Real.exp (2 * c) * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
            ‖smoothWeightedSum f y w ω‖ ^ 2 / w ^ (1 + 2 * σ) := integral_const_mul _ _
      _ ≤ Real.exp (2 * c) * ∫ u in Set.Ioi (0 : ℝ),
            ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine setIntegral_mono_set hIint ?_ (Filter.Eventually.of_forall fun w hw => hsub hw)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hu) _)
  have hcoef0 : (0 : ℝ) ≤ C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y := by
    positivity
  calc (K / η) * (∫ t in Set.Icc ((y : ℝ)) (x * (1 + η)),
          ‖smoothWeightedSum f y (x / t) ω‖ ^ 2
            * (C * (1 + η) ^ 2 * (t * η / (1 + η) + 1) / (t ^ 2 * Real.log y)))
      ≤ (K / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y
          * ∫ w in Set.Ioo (x / (x * (1 + η))) (x / (y : ℝ)),
              ‖smoothWeightedSum f y w ω‖ ^ 2 / w) :=
        mul_le_mul_of_nonneg_left hstep12 (by positivity)
    _ ≤ (K / η) * (C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ))) / Real.log y
          * (Real.exp (2 * c) * ∫ u in Set.Ioi (0 : ℝ),
              ‖smoothWeightedSum f y u ω‖ ^ 2 / u ^ (1 + 2 * σ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hcoef0) (by positivity)
    _ = K * C * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ)) / η) * Real.exp (2 * c)
          * (2 * Real.pi)⁻¹ * ((Real.log y)⁻¹ * P) := by
        rw [hpars]
        field_simp

/-! ### The sieve at a level `z ≤ y` -/

/-- **The weighted interval count, by Brun–Titchmarsh at a level `z ≤ y`.**  For `1 + η < t`, the
smoothing intervals of `y`-rough `r` that contain `t` have weighted count at most
`((1+η)²/t²)(2H/log z + 5z(1+log z)³)`, `H = tη/(1+η) + 1`: the `r` are `z`-rough integers in
`(t/(1+η) - 1, t]`, and `RMF.roughCount_sub_le_brun` sifts them at `z`. -/
theorem sum_inv_sq_indicator_le_brun {y z : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) {S : Finset ℕ}
    (hSr : ∀ r ∈ S, IsRough y r) {η t : ℝ} (hη : 0 < η) (ht : 1 + η < t) :
    ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ ((1 + η) ^ 2 / t ^ 2)
          * (2 * (t * η / (1 + η) + 1) / Real.log z + 5 * (z : ℝ) * (1 + Real.log z) ^ 3) := by
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = t / (1 + η) - 1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha, sub_pos, one_lt_div hη0]
    exact ht
  have hat : a < t / (1 + η) := by rw [ha]; linarith
  have hH : t - a = t * η / (1 + η) + 1 := by rw [ha]; exact sub_div_sub_one_eq hη
  have hH0 : 0 < t - a := by rw [hH]; positivity
  refine le_trans (sum_inv_sq_indicator_le_rough hSr hη ht0 ha0.le hat) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum : a + (t - a) = t := by ring
  have hcard := roughCount_sub_eq_card (y := y) (x := a) (H := t - a) hH0.le
  rw [hsum] at hcard
  rw [← hcard]
  have hmono := roughCount_sub_mono hzy (x := a) (H := t - a) hH0.le
  rw [hsum] at hmono
  have hbrun := roughCount_sub_le_brun hz ha0 hH0
  rw [hsum, hH] at hbrun
  linarith

/-- **The sieve constant of the reduction**,
`C_z = 2 log y/log z + 5z(1+log z)³·log y·(1+η)/(yη + 1 + η)`: `RMF.sum_inv_sq_indicator_le_brun` in
the shape `C(1+η)²(tη/(1+η)+1)/(t² log y)` of the principal term, uniformly in `t ≥ y`. -/
noncomputable def smallQSieveConst (y z : ℕ) (η : ℝ) : ℝ :=
  2 * Real.log y / Real.log z
    + 5 * (z : ℝ) * (1 + Real.log z) ^ 3 * Real.log y * (1 + η) / ((y : ℝ) * η + 1 + η)

lemma smallQSieveConst_pos {y z : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) {η : ℝ} (hη : 0 < η) :
    0 < smallQSieveConst y z η := by
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hz hzy
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  rw [smallQSieveConst]
  have h1 : 0 < 2 * Real.log y / Real.log z := by positivity
  have h2 : 0 ≤ 5 * (z : ℝ) * (1 + Real.log z) ^ 3 * Real.log y * (1 + η)
      / ((y : ℝ) * η + 1 + η) := by positivity
  linarith

/-- **The weighted interval count in the principal term's shape**: for `y ≤ t` and `1 + η < y`,
the count is at most `C_z(1+η)²(tη/(1+η)+1)/(t² log y)`. -/
theorem sum_inv_sq_indicator_le_smallQSieveConst {y z : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r) {η t : ℝ} (hη : 0 < η) (hyη : 1 + η < y)
    (hyt : (y : ℝ) ≤ t) :
    ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
        * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
      ≤ smallQSieveConst y z η * (1 + η) ^ 2 * (t * η / (1 + η) + 1)
          / (t ^ 2 * Real.log y) := by
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hz hzy
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hη0 : (0 : ℝ) < 1 + η := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  refine le_trans (sum_inv_sq_indicator_le_brun hz hzy hSr hη (by linarith)) ?_
  set H : ℝ := t * η / (1 + η) + 1 with hHdef
  set E : ℝ := 5 * (z : ℝ) * (1 + Real.log z) ^ 3 with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hH0 : 0 < H := by rw [hHdef]; positivity
  have hden : (0 : ℝ) < (y : ℝ) * η + 1 + η := by positivity
  -- `E ≤ E(1+η)H/(yη+1+η)`, since `(1+η)H = tη + 1 + η ≥ yη + 1 + η`
  have hHge : (y : ℝ) * η + 1 + η ≤ (1 + η) * H := by
    rw [hHdef]
    have : (1 + η) * (t * η / (1 + η) + 1) = t * η + 1 + η := by
      field_simp
      ring
    rw [this]
    nlinarith
  have hEle : E ≤ E * ((1 + η) * H) / ((y : ℝ) * η + 1 + η) := by
    rw [le_div_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hHge hE0
  have hmain : 2 * H / Real.log z + E ≤ smallQSieveConst y z η * H / Real.log y := by
    rw [smallQSieveConst, ← hEdef]
    have e1 : (2 * Real.log y / Real.log z + E * Real.log y * (1 + η) / ((y : ℝ) * η + 1 + η))
          * H / Real.log y
        = 2 * H / Real.log z + E * ((1 + η) * H) / ((y : ℝ) * η + 1 + η) := by
      field_simp
    rw [e1]
    linarith
  calc (1 + η) ^ 2 / t ^ 2 * (2 * H / Real.log z + E)
      ≤ (1 + η) ^ 2 / t ^ 2 * (smallQSieveConst y z η * H / Real.log y) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = smallQSieveConst y z η * (1 + η) ^ 2 * H / (t ^ 2 * Real.log y) := by
        field_simp

/-! ### The two constants -/

/-- **The reduction's constant**
`C_R = (1+ε)·C_z·((1+η)²(η/(1+η) + 1/y)/η)·e^{2c}/(2π)`; the middle factor is
`(1+η) + (1+η)²/(ηy)`. -/
noncomputable def smallQReductionConst (y z : ℕ) (η ε c : ℝ) : ℝ :=
  (1 + ε) * smallQSieveConst y z η * ((1 + η) ^ 2 * (η / (1 + η) + 1 / (y : ℝ)) / η)
    * Real.exp (2 * c) * (2 * Real.pi)⁻¹

/-- **The reduction's error**
`E_err = (1+1/ε)(η(1 + log x) + (1+η)(2/log z + 5z(1+log z)³/x))`. -/
noncomputable def smallQReductionErr (x : ℝ) (z : ℕ) (η ε : ℝ) : ℝ :=
  (1 + 1 / ε) * (η * (1 + Real.log x)
    + (1 + η) * (2 / Real.log z + 5 * (z : ℝ) * (1 + Real.log z) ^ 3 / x))

lemma smallQReductionConst_pos {y z : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) {η ε c : ℝ} (hη : 0 < η)
    (hε : 0 < ε) : 0 < smallQReductionConst y z η ε c := by
  have hy0 : (0 : ℝ) < (y : ℝ) := by
    have : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hz hzy
    linarith
  have := smallQSieveConst_pos hz hzy hη
  rw [smallQReductionConst]
  have hpi : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  positivity

/-! ### The smoothing error, in expectation -/

/-- **The expectation of the smoothing error, explicit.**  For `S` a set of `y`-rough integers in
`[1, x]`, `E[((1+1/ε)/(2η))·∑_{r∈S}(2∫‖A(x/r) - A(x/t)‖²)/r²] ≤ E_err`: each window contributes
`2η(η + (1+η)r/x)/r` (`RMF.integral_sum_setIntegral_normSq_sub_le`), `∑_{r≤x}1/r ≤ 1 + log x`, and
the rough `r ≤ x` number at most `2x/log z + 5z(1+log z)³`. -/
theorem integral_smoothingError_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y z : ℕ} (hz : 2 ≤ z)
    (hzy : z ≤ y) {x η ε : ℝ} (hx : 1 ≤ x) (hη : 0 < η) (hε : 0 < ε) {S : Finset ℕ}
    (hSr : ∀ r ∈ S, IsRough y r) (hS1 : ∀ r ∈ S, 1 ≤ r) (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    (∫ ω, ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
        (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
          ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
            - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
          / ((r : ℝ)) ^ 2 ∂μ)
      ≤ smallQReductionErr x z η ε := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hS0 : ∀ r ∈ S, 0 < r := fun r hr => hS1 r hr
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [integral_const_mul]
  have hE := integral_sum_setIntegral_normSq_sub_le hX y hx0 hη hS0
  have hc0 : (0 : ℝ) ≤ (1 + 1 / ε) / (2 * η) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hE hc0) ?_
  have hterm : ∀ r ∈ S, (1 + 1 / ε) / (2 * η) * (2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ))
      = (1 + 1 / ε) * η * ((r : ℝ))⁻¹ + (1 + 1 / ε) * (1 + η) / x := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS0 r hr
    field_simp
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  -- the harmonic mass
  have hsubI : S ⊆ Finset.Icc 1 ⌊x⌋₊ := fun r hr =>
    Finset.mem_Icc.2 ⟨hS1 r hr, Nat.le_floor (hSx r hr)⟩
  have hH : ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ 1 + Real.log x := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubI fun i _ _ => by positivity) ?_
    have hh := harmonic_le_one_add_log ⌊x⌋₊
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    refine le_trans hh ?_
    rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg hx]
    · linarith [Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le hx0.le)]
  -- the count
  have hcardS : (S.card : ℝ) ≤ 2 * x / Real.log z + 5 * (z : ℝ) * (1 + Real.log z) ^ 3 := by
    have hsubR : S ⊆ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z n} := fun r hr =>
      Finset.mem_filter.2 ⟨hsubI hr, (hSr r hr).mono hzy⟩
    have h1 : (S.card : ℝ) ≤ (roughCount z x : ℝ) := by
      rw [roughCount]
      exact_mod_cast Finset.card_le_card hsubR
    have hzero : roughCount z (1 / 2) = 0 := by
      rw [roughCount, show ⌊(1 / 2 : ℝ)⌋₊ = 0 by norm_num]
      simp
    have hbrun := roughCount_sub_le_brun hz (x := 1 / 2) (H := x - 1 / 2) (by norm_num)
      (by linarith)
    rw [show (1 / 2 : ℝ) + (x - 1 / 2) = x by ring, hzero, Nat.cast_zero, sub_zero] at hbrun
    have h2 : 2 * (x - 1 / 2) / Real.log z ≤ 2 * x / Real.log z :=
      div_le_div_of_nonneg_right (by linarith) hlz.le
    linarith
  have hc1 : 0 ≤ (1 + 1 / ε) * (1 + η) / x := by positivity
  have hstep1 : (1 + 1 / ε) * η * ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ (1 + 1 / ε) * η * (1 + Real.log x) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hstep2 : (S.card : ℝ) * ((1 + 1 / ε) * (1 + η) / x)
      ≤ (2 * x / Real.log z + 5 * (z : ℝ) * (1 + Real.log z) ^ 3) * ((1 + 1 / ε) * (1 + η) / x) :=
    mul_le_mul_of_nonneg_right hcardS hc1
  have hfin : (2 * x / Real.log z + 5 * (z : ℝ) * (1 + Real.log z) ^ 3)
        * ((1 + 1 / ε) * (1 + η) / x)
      = (1 + 1 / ε) * ((1 + η) * (2 / Real.log z + 5 * (z : ℝ) * (1 + Real.log z) ^ 3 / x)) := by
    field_simp
  rw [smallQReductionErr]
  nlinarith [hstep1, hstep2, hfin]

/-! ### The rough sum, in `q`-th moment -/

omit [MeasurableSpace Ω] in
/-- **The rough sum at one `ω`, with its constants.**  For `f` bounded by `1` at `ω`, `S` a set of
`y`-rough integers in `(1, x]`, `2 ≤ z ≤ y`, `1 + η < y ≤ x`, `σ log(x/y) ≤ c`:
`∑_{r∈S} weightedRoughTerm ≤ C_R·Z(ω) + ((1+1/ε)/(2η))∑_{r∈S}(2∫‖A(x/r) - A(x/t)‖²)/r²`. -/
theorem sum_weightedRoughTerm_le_explicit {X : ℕ → Ω → ℂ} {ω : Ω}
    (hbnd : ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1) {y z : ℕ} (hz : 2 ≤ z)
    (hzy : z ≤ y) {σ x η ε c : ℝ} (hyx : (y : ℝ) ≤ x) (hσ : 0 < σ)
    (hσlog : σ * Real.log (x / y) ≤ c) (hη : 0 < η) (hyη : 1 + η < y) (hε : 0 < ε)
    {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r) (hone : ∀ r ∈ S, 1 < r)
    (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    ∑ r ∈ S, weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r
      ≤ smallQReductionConst y z η ε c * ((Real.log y)⁻¹ * ∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
              ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        + ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
                - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖
                  ^ 2)) / ((r : ℝ)) ^ 2 := by
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hz hzy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hypos hyx
  have hden : (0 : ℝ) < 1 + η := by linarith
  have hlogy : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hS : ∀ r ∈ S, 0 < r := fun r hr => lt_trans Nat.zero_lt_one (hone r hr)
  have hC := smallQSieveConst_pos hz hzy hη
  have hAle : ∀ t : ℝ, (y : ℝ) ≤ t → ‖smoothWeightedSum f y (x / t) ω‖ ≤ x / (y : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hypos ht
    refine le_trans (norm_smoothWeightedSum_le_of_bound hbnd y (x / t)) ?_
    refine le_trans (Nat.floor_le (div_nonneg hxpos.le ht0.le)) ?_
    exact div_le_div_of_nonneg_left hxpos.le hypos ht
  have hsub : ∀ r ∈ S, Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))
      ⊆ Set.Icc ((y : ℝ)) (x * (1 + η)) := by
    intro r hr t ht
    have hyr : (y : ℝ) < (r : ℝ) := by
      exact_mod_cast (hSr r hr).lt_of_one_lt (hone r hr)
    exact ⟨le_trans hyr.le ht.1, le_trans ht.2 (mul_le_mul_of_nonneg_right (hSx r hr) hden.le)⟩
  have hbT : ∀ t ∈ Set.Icc ((y : ℝ)) (x * (1 + η)),
      ∑ r ∈ S, (((r : ℝ)) ^ 2)⁻¹
          * (Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η))).indicator (fun _ => (1 : ℝ)) t
        ≤ smallQSieveConst y z η * (1 + η) ^ 2 * (t * η / (1 + η) + 1)
            / (t ^ 2 * Real.log y) :=
    fun t ht => sum_inv_sq_indicator_le_smallQSieveConst hz hzy hSr hη hyη ht.1
  obtain ⟨hint, hintT⟩ := integrableOn_sieveShape_of_bound
    (measurable_smoothWeightedSum_truncation f y ω) (s := x * (1 + η))
    hη hypos hC hlogy hAle
  have hsm := sum_weightedRoughTerm_le_setIntegral_eps
    (T := Set.Icc ((y : ℝ)) (x * (1 + η)))
    (b := fun t => smallQSieveConst y z η * (1 + η) ^ 2 * (t * η / (1 + η) + 1)
      / (t ^ 2 * Real.log y))
    hbnd y hxpos.le hη hε hS measurableSet_Icc hsub hbT (fun r _ => hint r) hintT
  have hpr := setIntegral_normSq_mul_sieve_le_explicit (X := X) y hypos hyx hσ hσlog hη hC.le
    (by positivity : (0 : ℝ) ≤ 1 + ε) hlogy ω
  refine le_trans hsm (add_le_add ?_ le_rfl)
  refine le_trans hpr (le_of_eq ?_)
  rw [smallQReductionConst]

/-- **The rough sum in `q`-th moment, with its constants.**  For `0 < q ≤ 1`:
`E[(∑_{r∈S} weightedRoughTerm)^q] ≤ C_R^q·E[Z^q] + E_err^q`.  The error is bounded in expectation
(`RMF.integral_smoothingError_le_explicit`) and carried to the `q`-th power by Jensen. -/
theorem integral_rpow_sum_weightedRoughTerm_le_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y z : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {σ x η ε c q : ℝ} (hyx : (y : ℝ) ≤ x) (hσ : 0 < σ) (hσlog : σ * Real.log (x / y) ≤ c)
    (hη : 0 < η) (hyη : 1 + η < y) (hε : 0 < ε) (hq0 : 0 < q) (hq1 : q ≤ 1)
    {S : Finset ℕ} (hSr : ∀ r ∈ S, IsRough y r) (hone : ∀ r ∈ S, 1 < r)
    (hSx : ∀ r ∈ S, (r : ℝ) ≤ x) :
    (∫ ω, (∑ r ∈ S, weightedRoughTerm
        (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q ∂μ)
      ≤ (smallQReductionConst y z η ε c) ^ q * (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        + (smallQReductionErr x z η ε) ^ q := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hz hzy
  have hx0 : (0 : ℝ) ≤ x := le_trans (by linarith) hyx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith) hyx
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by linarith)
  have hCR := smallQReductionConst_pos (c := c) hz hzy hη hε
  obtain ⟨Err, hErr⟩ : ∃ Err : Ω → ℝ, Err = fun ω => ((1 + 1 / ε) / (2 * η)) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / r) ω
          - smoothWeightedSum (fun ω => squarefreeExtension fun p => X p ω) y (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Ω → ℝ, Z = fun ω => (Real.log y)⁻¹ * ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨_, rfl⟩
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by
    rw [hZ]
    exact mul_nonneg (inv_nonneg.2 hlogy) (integral_nonneg fun t => by positivity)
  have hErr0 : ∀ ω, 0 ≤ Err ω := fun ω => by
    rw [hErr]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => ?_)
    refine div_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
    exact setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hErrint : Integrable Err μ := by
    rw [hErr]
    refine (integrable_finsetSum S fun r hr => ?_).const_mul _
    have hr0 : (0 : ℝ) < r := by exact_mod_cast lt_trans Nat.zero_lt_one (hone r hr)
    exact ((integrable_setIntegral_normSq_sub_Icc hX y hx0 hr0).const_mul 2).div_const _
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hstep : ∀ᵐ ω ∂μ, (∑ r ∈ S, weightedRoughTerm
      (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q
      ≤ (smallQReductionConst y z η ε c) ^ q * Z ω ^ q + Err ω ^ q := by
    filter_upwards [hbdd] with ω hb
    have h1 : (∑ r ∈ S, weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r)
        ≤ smallQReductionConst y z η ε c * Z ω + Err ω := by
      have h := sum_weightedRoughTerm_le_explicit (X := X) (ω := ω) hb hz hzy hyx hσ hσlog hη
        hyη hε hSr hone hSx
      rw [hZ, hErr]
      exact h
    have hsum0 : (0 : ℝ) ≤ ∑ r ∈ S, weightedRoughTerm
        (fun ω => squarefreeExtension fun p => X p ω) y x ω r :=
      Finset.sum_nonneg fun r _ => weightedRoughTerm_nonneg _ _ _ _ _
    calc (∑ r ∈ S, weightedRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q
        ≤ (smallQReductionConst y z η ε c * Z ω + Err ω) ^ q := Real.rpow_le_rpow hsum0 h1 hq0.le
      _ ≤ (smallQReductionConst y z η ε c * Z ω) ^ q + Err ω ^ q :=
          Real.rpow_add_le_add_rpow (mul_nonneg hCR.le (hZ0 ω)) (hErr0 ω) hq0.le hq1
      _ = (smallQReductionConst y z η ε c) ^ q * Z ω ^ q + Err ω ^ q := by
          rw [Real.mul_rpow hCR.le (hZ0 ω)]
  have hI1 := integrable_rpow_sum_weightedRoughTerm hRa y hx0 (fun m hm => (hone m hm).le) hq0.le
  have hIZ : Integrable (fun ω => (smallQReductionConst y z η ε c) ^ q * Z ω ^ q) μ := by
    rw [hZ]
    exact (integrable_rpow_eulerProductLine hX y hσ hq0.le).const_mul _
  have hIE : Integrable (fun ω => Err ω ^ q) μ :=
    integrable_rpow_of_integrable hErrint (Filter.Eventually.of_forall hErr0) hq0.le hq1
  have hJ : (∫ ω, Err ω ^ q ∂μ) ≤ (smallQReductionErr x z η ε) ^ q := by
    refine integral_rpow_le_rpow_of_integral_le hq0.le hq1 (Filter.Eventually.of_forall hErr0)
      hErrint ?_
    rw [hErr]
    exact integral_smoothingError_le_explicit hX hz hzy hx1 hη hε hSr
      (fun r hr => (hone r hr).le) hSx
  calc (∫ ω, (∑ r ∈ S, weightedRoughTerm
      (fun ω => squarefreeExtension fun p => X p ω) y x ω r) ^ q ∂μ)
      ≤ ∫ ω, ((smallQReductionConst y z η ε c) ^ q * Z ω ^ q + Err ω ^ q) ∂μ :=
        integral_mono_ae hI1 (hIZ.add hIE) hstep
    _ = (smallQReductionConst y z η ε c) ^ q * (∫ ω, Z ω ^ q ∂μ) + ∫ ω, Err ω ^ q ∂μ := by
        rw [integral_add hIZ hIE, integral_const_mul]
    _ ≤ (smallQReductionConst y z η ε c) ^ q * (∫ ω, Z ω ^ q ∂μ)
          + (smallQReductionErr x z η ε) ^ q := by
        linarith [hJ]
    _ = _ := by rw [hZ]

/-! ### The reduction -/

/-- **The reduction below `q = ½`, with its constants.**  For `0 < q ≤ ½`, natural
`2 ≤ z ≤ y` with `1 + η < y ≤ x` and `⌊x⌋ ≤ y#`, `σ > 0` with `σ log(x/y) ≤ c`, `η, ε > 0`:

`E|S(x)|^{2q} ≤ E‖F_y(½)‖^{2q} + (∑_{x<m, m y-smooth sqfree} 1/m)^q + C_R^q·E[Z^q] + E_err^q`,

`C_R = RMF.smallQReductionConst y z η ε c`, `E_err = RMF.smallQReductionErr x z η ε`.  The first
two terms are `RMF.integral_rpow_weightedRademacherSum_le_eulerProduct`'s, the rough sum is
`RMF.integral_rpow_sum_weightedRoughTerm_le_explicit`. -/
theorem integral_rpow_weightedRademacherSum_le_reduction_explicit {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {y z : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    {σ x η ε c q : ℝ} (hyx : (y : ℝ) ≤ x) (hxy : ⌊x⌋₊ ≤ primorial y) (hσ : 0 < σ)
    (hσlog : σ * Real.log (x / y) ≤ c) (hη : 0 < η) (hyη : 1 + η < y) (hε : 0 < ε)
    (hq0 : 0 < q) (hq : 2 * q ≤ 1) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (1 / 2) ω‖
            ^ (2 * q) ∂μ)
        + (∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y)
            | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m}, (m : ℝ)⁻¹) ^ q
        + (smallQReductionConst y z η ε c) ^ q * (∫ ω, ((Real.log y)⁻¹ * ∫ t : ℝ,
              ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                  ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
                / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
        + (smallQReductionErr x z η ε) ^ q := by
  classical
  haveI := hX.isProbabilityMeasure
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast le_trans hz hzy
  have hx1 : (1 : ℝ) ≤ x := le_trans (by linarith) hyx
  have hsplit := integral_rpow_weightedRademacherSum_le_eulerProduct hX y hx1 hxy hq0.le hq
  have hrough := integral_rpow_sum_weightedRoughTerm_le_explicit (μ := μ) hX hz hzy hyx hσ
    hσlog hη hyη hε hq0 (by linarith)
    (S := ({m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m}).erase 1)
    (fun r hr => (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).2.1)
    (fun r hr => by
      have h1 := Finset.ne_of_mem_erase hr
      have h2 := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).1
      omega)
    (fun r hr => by
      have h := (Finset.mem_Icc.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hr)).1).2
      exact le_trans (by exact_mod_cast h) (Nat.floor_le (by linarith)))
  linarith

/-! ### The tail, by Rankin -/

/-- **Rankin's bound for the smooth tail, explicit.**  For `y ≥ 2`, `x > 0` and `κ > 0`,
`∑_{x<m, m y-smooth sqfree} 1/m` is at most
`log y·exp(1.42 + (e^κ - 1)(1 + (log 4 + 4)/log y) - κ log x/log y)`:
`RMF.smoothTailSum_le_rankin` at `δ = κ/log y`, with `p^δ ≤ 1 + (log p/log y)(e^κ - 1)` on
`p ≤ y` (convexity), Mertens' second theorem (`RMF.sum_primesBelow_inv_le_log_log_add`) and his
first (`RMF.sum_log_div_primesBelow_le`).  At `x = y^U` the exponent is
`1.42 + (e^κ - 1)(1 + o(1)) - κU`. -/
theorem smoothTailSum_le_rankin_explicit {y : ℕ} (hy : 2 ≤ y) {x κ : ℝ} (hx : 0 < x)
    (hκ : 0 < κ) :
    ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial y) | m ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree m},
        ((m : ℝ))⁻¹
      ≤ Real.log y * Real.exp (1.42 + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)
          - κ * Real.log x / Real.log y) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  set δ : ℝ := κ / Real.log y with hδ
  have hδ0 : 0 < δ := div_pos hκ hlogy
  refine le_trans (smoothTailSum_le_rankin y hx hδ0) ?_
  -- each factor
  have hfac : ∀ p ∈ Nat.primesBelow (y + 1),
      (1 + (p : ℝ) ^ (δ - 1))
        ≤ Real.exp (((p : ℝ))⁻¹ + (Real.exp κ - 1) / Real.log y * (Real.log p / p)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hpy : (p : ℝ) ≤ (y : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.1 (Nat.lt_of_mem_primesBelow hp)
    have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hlpy : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
    -- `p^δ = e^{(log p/log y)·κ} ≤ 1 + (log p/log y)(e^κ - 1)`
    have hl0 : 0 ≤ Real.log p / Real.log y := div_nonneg hlp0 hlogy.le
    have hl1 : Real.log p / Real.log y ≤ 1 := (div_le_one hlogy).2 hlpy
    have hpδ : (p : ℝ) ^ δ ≤ 1 + Real.log p / Real.log y * (Real.exp κ - 1) := by
      rw [Real.rpow_def_of_pos hp0]
      have : Real.log p * δ = Real.log p / Real.log y * κ := by rw [hδ]; ring
      rw [this]
      exact exp_mul_le_one_add_mul hl0 hl1
    have hsplit : (p : ℝ) ^ (δ - 1) = (p : ℝ) ^ δ * ((p : ℝ))⁻¹ := by
      rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
    have hle : (p : ℝ) ^ (δ - 1)
        ≤ ((p : ℝ))⁻¹ + (Real.exp κ - 1) / Real.log y * (Real.log p / p) := by
      rw [hsplit]
      have hinv : 0 ≤ ((p : ℝ))⁻¹ := inv_nonneg.2 hp0.le
      calc (p : ℝ) ^ δ * ((p : ℝ))⁻¹
          ≤ (1 + Real.log p / Real.log y * (Real.exp κ - 1)) * ((p : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hpδ hinv
        _ = ((p : ℝ))⁻¹ + (Real.exp κ - 1) / Real.log y * (Real.log p / p) := by
            field_simp
    linarith [Real.add_one_le_exp (((p : ℝ))⁻¹
      + (Real.exp κ - 1) / Real.log y * (Real.log p / p))]
  have hnn : ∀ p ∈ Nat.primesBelow (y + 1), 0 ≤ 1 + (p : ℝ) ^ (δ - 1) := fun p hp => by
    have : 0 ≤ (p : ℝ) ^ (δ - 1) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    linarith
  have hprod := Finset.prod_le_prod hnn hfac
  rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hprod
  have hM2 := sum_primesBelow_inv_le_log_log_add hy
  have hM1 := sum_log_div_primesBelow_le (by omega : 1 ≤ y)
  have heκ : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ.le]
  have hsum : ∑ p ∈ Nat.primesBelow (y + 1), ((p : ℝ))⁻¹
        + (Real.exp κ - 1) / Real.log y * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
      ≤ Real.log (Real.log y) + 1.42
        + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y) := by
    have h1 : (Real.exp κ - 1) / Real.log y * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
        ≤ (Real.exp κ - 1) / Real.log y * (Real.log y + Real.log 4 + 4) :=
      mul_le_mul_of_nonneg_left hM1 (div_nonneg heκ hlogy.le)
    have h2 : (Real.exp κ - 1) / Real.log y * (Real.log y + Real.log 4 + 4)
        = (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y) := by
      field_simp
      ring
    linarith
  have hxδ : x ^ (-δ) = Real.exp (-(κ * Real.log x / Real.log y)) := by
    rw [Real.rpow_def_of_pos hx, hδ]
    congr 1
    ring
  rw [hxδ]
  calc Real.exp (-(κ * Real.log x / Real.log y))
        * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1))
      ≤ Real.exp (-(κ * Real.log x / Real.log y))
          * Real.exp (Real.log (Real.log y) + 1.42
            + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)) :=
        mul_le_mul_of_nonneg_left (hprod.trans (Real.exp_le_exp.2 hsum)) (Real.exp_pos _).le
    _ = Real.log y * Real.exp (1.42 + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)
          - κ * Real.log x / Real.log y) := by
        rw [← Real.exp_add]
        rw [show -(κ * Real.log x / Real.log y) + (Real.log (Real.log y) + 1.42
            + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y))
            = Real.log (Real.log y) + (1.42 + (Real.exp κ - 1)
              * (1 + (Real.log 4 + 4) / Real.log y) - κ * Real.log x / Real.log y) by ring]
        rw [Real.exp_add, Real.exp_log hlogy]

/-! ### The primorial -/

/-- **`⌊x⌋ ≤ y#` once `log x ≤ y log 2 - log(y+1) - 2√y log y`**: `log y# = θ(y)` and Mathlib's
`Chebyshev.theta_ge`.  The hypothesis `hxy` of the reduction, with no appeal to the prime number
theorem. -/
theorem floor_le_primorial_of_log_le {y : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (h : Real.log x ≤ (y : ℝ) * Real.log 2 - Real.log ((y : ℝ) + 1)
      - 2 * Real.sqrt y * Real.log y) :
    ⌊x⌋₊ ≤ primorial y := by
  have hθ := Chebyshev.theta_ge y
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at hθ
  have hpos : (0 : ℝ) < (primorial y : ℝ) := by exact_mod_cast primorial_pos y
  have hx0 : (0 : ℝ) < x := by linarith
  have hle : x ≤ (primorial y : ℝ) := by
    rw [← Real.log_le_log_iff hx0 hpos]
    linarith
  have h1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ (primorial y : ℝ) := le_trans (Nat.floor_le hx0.le) hle
  exact_mod_cast h1

end RMF
