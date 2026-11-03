/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SmallXBounds
import RMF.UniformLower.WindowClassical
import RMF.Weighted.ExtendedLowerWindow
import RMF.Weighted.ExtendedUniformMomentsExplicit

/-!
# The extended sum's explicit lower bound: the elementary inputs

For a Rademacher family,
`Y(x) = x^{-1/2}∑_{n≤x} X^e(n)` (`normalisedSum (fun ω => compMultExtension fun p => X p ω) x`)
and `r = ⌊√x⌋/√x`:

* `E Y = r` for `x ≥ 1` (`RMF.integral_normalisedSum_compMultExtension_eq`): of the `X^e(n)` only
  the squares have mean `1`.  So `r ≤ E|Y|`; and `½ ≤ r ≤ 1`, `r ≥ ¾` from `x ≥ 9`,
  `r ≥ 1 - 1/√x`;
* `E|Y|² ≤ 1 + log x` (`RMF.integral_normSq_normalisedSum_compMultExtension_le_one_add_log`),
  from the exact mean square of the square classes at `a = 0`;
* Hölder, `r^{2-2q}(1 + log x)^{-(1-2q)} ≤ E|Y|^{2q}`, so `½(1 + log x)^{-(1-2q)}` from `x ≥ 9`
  (`RMF.le_integral_rpow_normalisedSum_compMultExtension_holder`);
* interpolation against the upper bound `C = 30`
  (`RMF.extended_rademacher_moments_upper_uniform_explicit`),
  `r^{(2b-2q)/(2b-1)}U_b^{-(1-2q)/(2b-1)} ≤ E|Y|^{2q}`
  (`RMF.le_integral_rpow_normalisedSum_compMultExtension_interp`);
* the floor: Khintchine at `y = ⌊x/2⌋`, where `∑_{m≤x/p} X^e(m) = 1`, with `#{x/2 < p ≤ x}/x` in
  place of `∑_{x/2<p≤x} 1/p`
  (`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_of_le_card`).
  As `∑ 1/p ≤ 2#/x`, the elementary count gives `0.23/(2 log x)` from `x ≥ 10^{16}`
  (`RMF.le_integral_rpow_normalisedSum_compMultExtension_floor_small`); the classical one gives
  `#/x ≥ 0.49/log x` from `x ≥ exp(10²⁰)` (`RMF.le_card_largePrimeSet_half_div_classical`).
-/

open MeasureTheory

namespace RMF

/-! ### `r = ⌊√x⌋/√x` -/

/-- `⌊√x⌋/√x ≤ 1` for `x > 0`. -/
lemma floor_sqrt_div_sqrt_le_one {x : ℝ} (hx : 0 < x) :
    (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x ≤ 1 :=
  (div_le_one (Real.sqrt_pos.2 hx)).2 (Nat.floor_le (Real.sqrt_nonneg x))

/-- `½ ≤ ⌊√x⌋/√x` for `x ≥ 1`: `√x < ⌊√x⌋ + 1 ≤ 2⌊√x⌋`. -/
lemma half_le_floor_sqrt_div_sqrt {x : ℝ} (hx : 1 ≤ x) :
    1 / 2 ≤ (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x := by
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
  have hk1 : (1 : ℝ) ≤ ⌊Real.sqrt x⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _).2 hs1
  have hlt : Real.sqrt x < ⌊Real.sqrt x⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `¾ ≤ ⌊√x⌋/√x` for `x ≥ 9`: `√x < ⌊√x⌋ + 1 ≤ (4/3)⌊√x⌋`. -/
lemma three_quarters_le_floor_sqrt_div_sqrt {x : ℝ} (hx : 9 ≤ x) :
    3 / 4 ≤ (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x := by
  have hs3 : 3 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rwa [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hk3 : (3 : ℝ) ≤ ⌊Real.sqrt x⌋₊ := by
    have : 3 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by exact_mod_cast hs3)
    exact_mod_cast this
  have hlt : Real.sqrt x < ⌊Real.sqrt x⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `1 - 1/√x ≤ ⌊√x⌋/√x` for `x > 0`: `√x - 1 < ⌊√x⌋`. -/
lemma one_sub_inv_sqrt_le_floor_sqrt_div_sqrt {x : ℝ} (hx : 0 < x) :
    1 - (Real.sqrt x)⁻¹ ≤ (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlt : Real.sqrt x < ⌊Real.sqrt x⌋₊ + 1 := Nat.lt_floor_add_one _
  have e : 1 - (Real.sqrt x)⁻¹ = (Real.sqrt x - 1) / Real.sqrt x := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hs.le

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The first two moments -/

/-- **`E Y(x) = ⌊√x⌋/√x`** for every Rademacher `X` and `x ≥ 1`: by the square classes
(`RMF.sum_compMultExtension_eq_sum_squarefreeExtension_mul`)
`∑_{n≤x} X^e(n) = ∑_{m≤x} X(m)⌊√(x/m)⌋` almost surely, and `E X(m) = [m = 1]`. -/
theorem integral_normalisedSum_compMultExtension_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    ∫ ω, normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω ∂μ
      = (⌊Real.sqrt x⌋₊ : ℂ) / (Real.sqrt x : ℂ) := by
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hsq : ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), X p ω ^ 2 = 1 :=
    (Filter.eventually_all_finset _).2 fun p hp =>
      ae_sq_X_eq_one hX (Nat.prime_of_mem_primesBelow hp)
  have hae : (fun ω => normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω)
      =ᵐ[μ] fun ω => (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, squarefreeExtension (fun p => X p ω) m
          * (⌊Real.sqrt (x / m)⌋₊ : ℂ)) / (Real.sqrt x : ℂ) := by
    filter_upwards [hsq] with ω hω
    rw [normalisedSum, randomSum, sum_compMultExtension_eq_sum_squarefreeExtension_mul
      (by linarith) fun p hp hpx => hω p (Nat.mem_primesBelow.2 ⟨by omega, hp⟩)]
  have hint : ∀ m ∈ Finset.Icc 1 ⌊x⌋₊, Integrable
      (fun ω => squarefreeExtension (fun p => X p ω) m * (⌊Real.sqrt (x / m)⌋₊ : ℂ)) μ :=
    fun m _ => (Integrable.of_bound (hf.measurable_apply m).aestronglyMeasurable 1
      (hf.norm_apply_le_one m)).mul_const _
  have h1 : 1 ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.2 ⟨le_rfl, (Nat.one_le_floor_iff x).2 hx⟩
  rw [integral_congr_ae hae, integral_div, integral_finsetSum _ hint,
    Finset.sum_eq_single 1 ?_ fun h => absurd h1 h, integral_mul_const,
    integral_squarefreeExtension_eq_ite hX one_ne_zero, if_pos rfl, one_mul, Nat.cast_one,
    div_one]
  intro m hm hm1
  rw [integral_mul_const, integral_squarefreeExtension_eq_ite hX
    (Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hm).1), if_neg hm1, zero_mul]

/-- `⌊√x⌋/√x ≤ E|Y(x)|` for every Rademacher `X` and `x ≥ 1`: `|E Y| ≤ E|Y|`. -/
theorem floor_sqrt_div_sqrt_le_integral_norm_normalisedSum_compMultExtension {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ∂μ := by
  have h := norm_integral_le_integral_norm (μ := μ)
    (normalisedSum (fun ω => compMultExtension fun p => X p ω) x)
  rwa [integral_normalisedSum_compMultExtension_eq hX hx, norm_div, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h

/-- **`E|Y(x)|² ≤ 1 + log x`** for every Rademacher `X` and `x ≥ 1`: the exact mean square of the
square classes at `a = 0` (`RMF.integral_normSq_sum_Ioc_compMult`) is
`∑_{m≤x squarefree} ⌊√(x/m)⌋² ≤ x∑_{m≤x} 1/m ≤ x(1 + log x)`. -/
theorem integral_normSq_normalisedSum_compMultExtension_le_one_add_log {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2 ∂μ)
      ≤ 1 + Real.log x := by
  have hx0 : 0 < x := by linarith
  have hIoc : Finset.Ioc ⌊(0 : ℝ)⌋₊ ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [Nat.floor_zero, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hY : (fun ω => ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ 2)
      = fun ω => ‖∑ n ∈ Finset.Ioc ⌊(0 : ℝ)⌋₊ ⌊x⌋₊, compMultExtension (fun p => X p ω) n‖ ^ 2
          / x := by
    funext ω
    rw [hIoc, normalisedSum, randomSum, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hx0.le]
  rw [hY, integral_div, integral_normSq_sum_Ioc_compMult hX le_rfl hx0.le, div_le_iff₀ hx0]
  -- each class: `⌊√(x/m)⌋² ≤ x/m`
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊x⌋₊,
      (((⌊Real.sqrt (x / m)⌋₊ - ⌊Real.sqrt (0 / m)⌋₊ : ℕ) : ℝ) ^ 2
        * (if Squarefree m then 1 else 0)) ≤ x * (m : ℝ)⁻¹ := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    rw [zero_div, Real.sqrt_zero, Nat.floor_zero, Nat.sub_zero]
    have hfl : (⌊Real.sqrt (x / m)⌋₊ : ℝ) ≤ Real.sqrt (x / m) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have hsq : (⌊Real.sqrt (x / m)⌋₊ : ℝ) ^ 2 ≤ x * (m : ℝ)⁻¹ :=
      calc (⌊Real.sqrt (x / m)⌋₊ : ℝ) ^ 2 ≤ Real.sqrt (x / m) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 2
        _ = x * (m : ℝ)⁻¹ := by rw [Real.sq_sqrt (div_nonneg hx0.le hm0.le), div_eq_mul_inv]
    split_ifs
    · rwa [mul_one]
    · rw [mul_zero]
      exact mul_nonneg hx0.le (inv_nonneg.2 hm0.le)
  have hfl1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx
  have hfl0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (hfl1 : 0 < ⌊x⌋₊)
  have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log hfl0 (Nat.floor_le hx0.le)
  have hxlog := mul_le_mul_of_nonneg_left hlog hx0.le
  calc _ ≤ ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, x * (m : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = x * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ x * (1 + Real.log ⌊x⌋₊) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log _) hx0.le
    _ ≤ (1 + Real.log x) * x := by linarith

/-! ### Hölder -/

/-- **Hölder for `Y`**: for a Rademacher family, `x ≥ 1` and `0 < q < ½`,
`(⌊√x⌋/√x)^{2-2q}(1 + log x)^{-(1-2q)} ≤ E|Y(x)|^{2q}`: `E|Y|^{2q} ≥ (E|Y|)^{2-2q}/(E|Y|²)^{1-2q}`
(`RMF.rpow_integral_div_rpow_integral_sq_le_integral_rpow`), `E|Y| ≥ ⌊√x⌋/√x` and
`E|Y|² ≤ 1 + log x`. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_holder_floor {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 1 ≤ x) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    ((⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x) ^ (2 - 2 * q) * (1 + Real.log x) ^ (-(1 - 2 * q))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hint : ∀ s : ℝ, 0 ≤ s → Integrable (fun ω =>
      ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ s) μ :=
    fun s hs => integrable_rpow_norm_normalisedSum_compMultExtension hX x hs
  have hr := floor_sqrt_div_sqrt_le_integral_norm_normalisedSum_compMultExtension hX hx
  have hr0 : 0 < (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x :=
    lt_of_lt_of_le (by norm_num) (half_le_floor_sqrt_div_sqrt hx)
  have h2 : (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ) ≤ 1 + Real.log x := by
    simp only [Real.rpow_two]
    exact integral_normSq_normalisedSum_compMultExtension_le_one_add_log hX hx
  -- `E|Y|² > 0`, from `E|Y| ≤ (E|Y|²)^{1/2}`
  have hpos : 0 < ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ := by
    have hJ := integral_rpow_le_rpow_integral_of_le (μ := μ) (p := 1) (q := 1 / 2)
      (by norm_num) (by norm_num) (memLp_normalisedSum_compMultExtension hX x _)
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (2 : ℝ) * 1 = 2 by norm_num] at hJ
    simp only [Real.rpow_one] at hJ
    have hI0 : (0 : ℝ) ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
        ^ (2 : ℝ) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
    rcases hI0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow (by norm_num)] at hJ
      linarith
  have hPZ := rpow_integral_div_rpow_integral_sq_le_integral_rpow (μ := μ)
    (X := fun ω => ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖)
    (q := 2 * q) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hint _ (by linarith))
    (hint 2 (by norm_num)) hpos
  have hnum := Real.rpow_le_rpow hr0.le hr (by linarith : (0 : ℝ) ≤ 2 - 2 * q)
  have hden0 : 0 < (∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
      ^ (2 : ℝ) ∂μ) ^ (1 - 2 * q) := Real.rpow_pos_of_pos hpos _
  have hden := Real.rpow_le_rpow hpos.le h2 (by linarith : (0 : ℝ) ≤ 1 - 2 * q)
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv]
  refine le_trans ?_ hPZ
  exact div_le_div₀ (Real.rpow_nonneg (integral_nonneg fun ω => norm_nonneg _) _) hnum hden0 hden

/-- **Hölder for `Y` from `x ≥ 9`**: for a Rademacher family, `x ≥ 9` and `0 < q < ½`,
`½(1 + log x)^{-(1-2q)} ≤ E|Y(x)|^{2q}`, as `(⌊√x⌋/√x)^{2-2q} ≥ (3/4)² ≥ ½`. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_holder {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : 9 ≤ x) (hq0 : 0 < q)
    (hq : q < 1 / 2) :
    1 / 2 * (1 + Real.log x) ^ (-(1 - 2 * q))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h34 := three_quarters_le_floor_sqrt_div_sqrt hx
  have h1 := floor_sqrt_div_sqrt_le_one hx0
  have hr0 : 0 < (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x := by linarith
  have hpow : 1 / 2 ≤ ((⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x) ^ (2 - 2 * q) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hr0 h1 (by linarith : 2 - 2 * q ≤ 2)
    rw [Real.rpow_two] at h
    nlinarith [mul_le_mul h34 h34 (by norm_num) hr0.le]
  refine le_trans ?_
    (le_integral_rpow_normalisedSum_compMultExtension_holder_floor hX (by linarith) hq0 hq)
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by linarith) _)

/-! ### Interpolation against the upper bound `C = 30` -/

/-- **Interpolation, the arithmetic, with `E ≥ r`**: for `a < 1 < c`, `0 < r ≤ E`,
`E ≤ A^{(c-1)/(c-a)}B^{(1-a)/(c-a)}`, `A, B ≥ 0` and `B ≤ U`,
`r^{(c-a)/(c-1)}U^{-(1-a)/(c-1)} ≤ A`.  `RMF.rpow_neg_le_of_interp` is `r = 1`. -/
lemma rpow_mul_rpow_neg_le_of_interp {E A B U a c r : ℝ} (ha1 : a < 1) (hc1 : 1 < c)
    (hr : 0 < r) (hE : r ≤ E) (hH : E ≤ A ^ ((c - 1) / (c - a)) * B ^ ((1 - a) / (c - a)))
    (hA0 : 0 ≤ A) (hB : 0 ≤ B) (hBU : B ≤ U) :
    r ^ ((c - a) / (c - 1)) * U ^ (-((1 - a) / (c - 1))) ≤ A := by
  have hca : 0 < c - a := by linarith
  have hc1' : 0 < c - 1 := by linarith
  have ha1' : 0 < 1 - a := by linarith
  have hθ : 0 < (c - 1) / (c - a) := div_pos hc1' hca
  have hφ : 0 < (1 - a) / (c - a) := div_pos ha1' hca
  have hB0 : 0 < B := by
    rcases hB.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow hφ.ne', mul_zero] at hH
      linarith
  have hφB : 0 < B ^ ((1 - a) / (c - a)) := Real.rpow_pos_of_pos hB0 _
  have h1 : r * B ^ (-((1 - a) / (c - a))) ≤ A ^ ((c - 1) / (c - a)) := by
    rw [Real.rpow_neg hB0.le, ← div_eq_mul_inv, div_le_iff₀ hφB]
    linarith
  have h2 := Real.rpow_le_rpow (mul_nonneg hr.le (Real.rpow_nonneg hB0.le _)) h1
    (inv_nonneg.2 hθ.le)
  rw [← Real.rpow_mul hA0, mul_inv_cancel₀ hθ.ne', Real.rpow_one,
    Real.mul_rpow hr.le (Real.rpow_nonneg hB0.le _), ← Real.rpow_mul hB0.le] at h2
  have e1 : ((c - 1) / (c - a))⁻¹ = (c - a) / (c - 1) := inv_div _ _
  have e2 : -((1 - a) / (c - a)) * ((c - 1) / (c - a))⁻¹ = -((1 - a) / (c - 1)) := by
    field_simp
  rw [e2, e1] at h2
  have hexp : -((1 - a) / (c - 1)) ≤ 0 := by
    have : 0 ≤ (1 - a) / (c - 1) := div_nonneg ha1'.le hc1'.le
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hB0 hBU hexp)
    (Real.rpow_nonneg hr.le _)) h2

/-- **Interpolation for `Y` against `C = 30`**: for a Rademacher family, `x ≥ 3`, `0 < q < ½` and
`½ < b ≤ 1`, with `U = 30(log x)^{b(2b-1)}min{1/(2b-1), log log x}^{3/4}`
(`RMF.extended_rademacher_moments_upper_uniform_explicit` at `b`),
`(⌊√x⌋/√x)^{(2b-2q)/(2b-1)}U^{-(1-2q)/(2b-1)} ≤ E|Y(x)|^{2q}`: `E|Y| ≥ ⌊√x⌋/√x` and
`E|Y| ≤ (E|Y|^{2q})^θ(E|Y|^{2b})^{1-θ}`, `θ = (2b-1)/(2b-2q)`. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_interp {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q b : ℝ} (hx : 3 ≤ x) (hq0 : 0 < q)
    (hq : q < 1 / 2) (hb : 1 / 2 < b) (hb1 : b ≤ 1) :
    ((⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x) ^ ((2 * b - 2 * q) / (2 * b - 1))
        * (30 * (Real.log x ^ (b * (2 * b - 1))
          * min (2 * b - 1)⁻¹ (Real.log (Real.log x)) ^ (3 / 4 : ℝ)))
          ^ (-((1 - 2 * q) / (2 * b - 1)))
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hint : ∀ s : ℝ, 0 ≤ s → Integrable (fun ω =>
      ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ s) μ :=
    fun s hs => integrable_rpow_norm_normalisedSum_compMultExtension hX x hs
  have hH := integral_le_rpow_integral_rpow_mul_rpow_integral_rpow (μ := μ)
    (X := fun ω => ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖)
    (a := 2 * q) (c := 2 * b) (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hint _ (by linarith))
    (hint _ (by linarith))
  have hU := (extended_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).2.2 b hb hb1
  exact rpow_mul_rpow_neg_le_of_interp (by linarith) (by linarith)
    (lt_of_lt_of_le (by norm_num) (half_le_floor_sqrt_div_sqrt hx1))
    (floor_sqrt_div_sqrt_le_integral_norm_normalisedSum_compMultExtension hX hx1) hH
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hU

/-! ### The floor -/

/-- **The floor for `Y`, from a lower bound on the number of primes of `(x/2, x]`**: for a
Rademacher family, `x ≥ 4`, `0 < q ≤ ½` and `0 ≤ c ≤ #{x/2 < p ≤ x}/x`,
`2^{-(1-2q)}3^{-(1-q)}c^q ≤ E|Y(x)|^{2q}`: Khintchine (`RMF.khintchine_rough_extended`) at
`y = ⌊x/2⌋`, where `∑_{m≤x/p} X^e(m) = X^e(1) = 1`, and `E|∑_{n≤x} X^e(n)|^{2q} = x^qE|Y|^{2q}`. -/
theorem le_integral_rpow_normalisedSum_compMultExtension_floor_of_le_card {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q c : ℝ} (hx : 4 ≤ x) (hq0 : 0 < q)
    (hq12 : q ≤ 1 / 2) (hc : 0 ≤ c)
    (hcard : c ≤ ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) / x) :
    (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * c ^ q
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hx0 : (0 : ℝ) < x := by linarith
  -- Khintchine at `y = ⌊x/2⌋`
  have hxy : ⌊x⌋₊ < (⌊x / 2⌋₊ + 1) ^ 2 := by
    have hs : x / 2 < (⌊x / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : x < ((⌊x / 2⌋₊ : ℝ) + 1) ^ 2 := by nlinarith
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hcast : (⌊x⌋₊ : ℝ) < (((⌊x / 2⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hkh := khintchine_rough_extended hX (by linarith) hxy hq0 (by linarith)
  -- the prime sum is deterministic: `∑_{m≤x/p} X^e(m) = X^e(1) = 1` for `x/2 < p ≤ x`
  have hS1 : ∀ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, ∀ ω,
      randomSum (fun ω => compMultExtension fun r => X r ω) (x / p) ω = 1 := by
    intro p hp ω
    obtain ⟨⟨hyp, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpxR : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hpx) (Nat.floor_le hx0.le)
    have hhalf : x / 2 < p := by
      have h1 : (⌊x / 2⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hyp
      have h2 := Nat.lt_floor_add_one (x / 2)
      linarith
    have hfl : ⌊x / p⌋₊ = 1 := by
      refine (Nat.floor_eq_iff (div_nonneg hx0.le hp0.le)).2 ⟨?_, ?_⟩
      · rw [Nat.cast_one, le_div_iff₀ hp0]
        linarith
      · rw [Nat.cast_one, div_lt_iff₀ hp0]
        linarith
    simp [randomSum, hfl]
  have hconst : ∀ ω, (∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊,
      ‖randomSum (fun ω => compMultExtension fun r => X r ω) (x / p) ω‖ ^ 2)
      = ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := fun ω => by
    rw [Finset.sum_congr rfl fun p hp => by rw [hS1 p hp ω, norm_one, one_pow],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  simp only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul] at hkh
  -- the unnormalised moment is `x^q E|Y|^{2q}`
  have hscale : ∀ ω, ‖randomSum (fun ω => compMultExtension fun r => X r ω) x ω‖ ^ (2 * q)
      = x ^ q * ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) := by
    intro ω
    have hs : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hx0).ne'
    have e : randomSum (fun ω => compMultExtension fun r => X r ω) x ω
        = normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω * (Real.sqrt x : ℂ) := by
      rw [normalisedSum, div_mul_cancel₀ _ hs]
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.mul_rpow (norm_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hx0.le, show 1 / 2 * (2 * q) = q by ring, mul_comm]
  simp_rw [hscale] at hkh
  rw [integral_const_mul] at hkh
  -- divide by `x^q`
  set E := ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ
    with hEdef
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx0 q
  have hmono : c ^ q ≤ ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) ^ q / x ^ q := by
    rw [← Real.div_rpow (Nat.cast_nonneg _) hx0.le]
    exact Real.rpow_le_rpow hc hcard hq0.le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - q)) := Real.rpow_nonneg (by norm_num) _
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 - 2 * q)) := Real.rpow_nonneg (by norm_num) _
  have h2 : (2 : ℝ) ^ (-(1 - 2 * q)) * 2 ^ (1 - 2 * q) = 1 := by
    rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
  have p0 : (3 : ℝ) ^ (-(1 - q)) * (((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) ^ q / x ^ q)
      ≤ 2 ^ (1 - 2 * q) * E := by
    rw [← mul_div_assoc, div_le_iff₀ hxq]
    calc (3 : ℝ) ^ (-(1 - q)) * ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) ^ q
        ≤ 2 ^ (1 - 2 * q) * (x ^ q * E) := hkh
      _ = 2 ^ (1 - 2 * q) * E * x ^ q := by ring
  have p1 := le_trans (mul_le_mul_of_nonneg_left hmono h3) p0
  have p2 := mul_le_mul_of_nonneg_left p1 h20
  rw [← mul_assoc ((2 : ℝ) ^ (-(1 - 2 * q))) ((2 : ℝ) ^ (1 - 2 * q)), h2, one_mul] at p2
  linarith

/-- **The bridge from `∑ 1/p` to the count**: `∑_{x/2<p≤x} 1/p ≤ 2#{x/2 < p ≤ x}/x` for `x > 0`,
as each `p > x/2`. -/
lemma sum_inv_largePrimeSet_half_le_two_mul_card_div {x : ℝ} (hx : 0 < x) :
    ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹
      ≤ 2 * ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) / x := by
  have hterm : ∀ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹ ≤ 2 / x := by
    intro p hp
    obtain ⟨⟨hyp, -⟩, -⟩ := mem_largePrimeSet.1 hp
    have h1 : (⌊x / 2⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hyp
    have h2 := Nat.lt_floor_add_one (x / 2)
    have hp0 : (0 : ℝ) < p := by linarith
    rw [inv_eq_one_div, div_le_div_iff₀ hp0 hx]
    linarith
  calc ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, (p : ℝ)⁻¹
      ≤ ∑ _p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, 2 / x := Finset.sum_le_sum hterm
    _ = 2 * ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) / x := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The floor for `Y` for small `x`**: for a Rademacher family, `x ≥ 10^{16}` and `0 < q ≤ ½`,
`2^{-(1-2q)}3^{-(1-q)}(0.23/(2 log x))^q ≤ E|Y(x)|^{2q}`:
`#{x/2 < p ≤ x}/x ≥ ½∑_{x/2<p≤x} 1/p ≥ 0.23/(2 log x)` (`RMF.le_sum_inv_largePrimeSet_half_small`,
`RMF.sum_inv_largePrimeSet_half_le_two_mul_card_div`). -/
theorem le_integral_rpow_normalisedSum_compMultExtension_floor_small {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {x q : ℝ} (hx : (10 : ℝ) ^ 16 ≤ x)
    (hq0 : 0 < q) (hq12 : q ≤ 1 / 2) :
    (2 : ℝ) ^ (-(1 - 2 * q)) * (3 : ℝ) ^ (-(1 - q)) * (23 / (200 * Real.log x)) ^ q
      ≤ ∫ ω, ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hL : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
  refine le_integral_rpow_normalisedSum_compMultExtension_floor_of_le_card hX
    (le_trans (by norm_num) hx) hq0 hq12 (by positivity) ?_
  have h1 := le_sum_inv_largePrimeSet_half_small hx
  have h2 := sum_inv_largePrimeSet_half_le_two_mul_card_div hx0
  have e1 : 23 / (200 * Real.log x) = 1 / 2 * (23 / (100 * Real.log x)) := by
    field_simp
    ring
  have e2 : 2 * ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) / x
      = 2 * (((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) / x) := by ring
  rw [e1]
  linarith

/-- **The primes of `(x/2, x]` counted, from `exp(10²⁰)`**: `0.49/log x ≤ #{x/2 < p ≤ x}/x` for
every `x ≥ exp(10²⁰)`: `θ(x) - θ(x/2) ≥ 0.49x` (`RMF.theta_sub_theta_half_ge_classical`) and
`log p ≤ log x`. -/
theorem le_card_largePrimeSet_half_div_classical {x : ℝ} (hx : Real.exp (10 ^ 20) ≤ x) :
    49 / (100 * Real.log x) ≤ ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) / x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 10 ^ 20 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hθ := theta_sub_theta_half_ge_classical hx
  rw [theta_sub_theta_eq (Nat.floor_mono (by linarith))] at hθ
  have hθ' : 49 / 100 * x ≤ ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p := hθ
  have hsum : ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p
      ≤ ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) * Real.log x := by
    calc ∑ p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p
        ≤ ∑ _p ∈ largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊, Real.log x := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨⟨-, hpx⟩, hprime⟩ := mem_largePrimeSet.1 hp
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
          exact Real.log_le_log hp0 (le_trans (by exact_mod_cast hpx) (Nat.floor_le hx0.le))
      _ = ((largePrimeSet ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) * Real.log x := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_div_iff₀ (by positivity) hx0]
  linarith

end RMF
