/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedCombineExplicit
import RMF.Weighted.ReductionSmallQExplicit
import RMF.Analysis.FracMellinExplicit
import RMF.Probability.CondJensen

/-!
# The remainder's reduction, I: the rough–smooth split

The fractional-part sum is
`R(x)√x = ∑_{n≤x} X(n){√(x/n)} = ∑_{n≤x} X(n)√(x/n)·ψ(x/n)`, `ψ = RMF.fracKernel`, and along
`n = m·k` (`m` `y`-rough, `k` `y`-smooth)

`R(x) = ∑_{m≤x, m rough} X(m)m^{-1/2}·H_y(x/m)`, `H_y(w) = ∑_{k≤w, k smooth} X(k)k^{-1/2}ψ(w/k)`

(`RMF.smoothFracSum`, `RMF.fracPartSum_eq_sum_rough_smoothFracSum`).  Conditionally on the
smooth `σ`-algebra the rough values are orthogonal, so
`E[|R(x)|² | 𝓕_y] = ∑_{m rough squarefree} m⁻¹|H_y(x/m)|²`
(`RMF.condExp_normSq_fracPartSum_sqfree`), and conditional Jensen gives
`E|R(x)| ≤ E[(∑_m m⁻¹|H_y(x/m)|²)^{1/2}]`.

The rough `m < T₀` (`T₀ = √x` in use, `m = 1` among them) are handled in mean square: the smooth
numbers are rare, `E|H_y(w)|² ≤ w⁻¹#{k ≤ w smooth squarefree} ≤ w^{-δ}∏_{p≤y}(1 + p^{δ-1})`
(Rankin, `RMF.integral_normSq_smoothFracSum_le_rankin`), and with `δ = κ/log y` their part is at
most `RMF.fracLowErr`.  The headline of this file,
`RMF.integral_norm_fracPartSum_le_lowErr_add`, is

`E|R(x)| ≤ fracLowErr^{1/2} + E[(∑_{T₀≤m≤x, m rough squarefree} m⁻¹|H_y(x/m)|²)^{1/2}]`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The kernel -/

/-- `ψ ≤ 1`: `{√v} < 1 ≤ √v` for `v ≥ 1`. -/
lemma fracKernel_le_one (v : ℝ) : fracKernel v ≤ 1 := by
  unfold fracKernel
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ Real.sqrt v := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h
    exact div_le_one_of_le₀ ((Int.fract_lt_one _).le.trans h1) (Real.sqrt_nonneg _)
  · exact zero_le_one

/-- `ψ(v)² ≤ 1/v` for `v > 0`. -/
lemma fracKernel_sq_le_inv {v : ℝ} (hv : 0 < v) : fracKernel v ^ 2 ≤ v⁻¹ := by
  have h := fracKernel_div_le (u := v) (k := 1) hv one_pos
  rw [div_one, Real.sqrt_one, one_mul] at h
  have h0 := fracKernel_nonneg v
  calc fracKernel v ^ 2 ≤ (v ^ (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = v⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
        norm_num
        exact Real.rpow_neg_one v

/-- `{√(x/n)}/√x = n^{-1/2}ψ(x/n)` for `1 ≤ n ≤ x`. -/
lemma fract_sqrt_div_div_sqrt_eq {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (hnx : (n : ℝ) ≤ x) :
    Int.fract (Real.sqrt (x / n)) / Real.sqrt x = (Real.sqrt n)⁻¹ * fracKernel (x / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := lt_of_lt_of_le hn0 hnx
  have h1 : 1 ≤ x / n := (one_le_div hn0).2 hnx
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [fracKernel, if_pos h1, Real.sqrt_div' x hn0.le]
  field_simp

/-! ### The smooth factor -/

/-- `H_y(w) = ∑_{k≤w, k y-smooth} f(k)k^{-1/2}ψ(w/k)`, `ψ = RMF.fracKernel`: the smooth factor of
the fractional-part sum (`RMF.fracPartSum_eq_sum_rough_smoothFracSum`). -/
noncomputable def smoothFracSum (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (w : ℝ) (ω : Ω) : ℂ :=
  ∑ k ∈ {k ∈ Finset.Icc 1 ⌊w⌋₊ | k ∈ Nat.smoothNumbers (y + 1)},
    f ω k / (Real.sqrt k : ℂ) * (fracKernel (w / k) : ℂ)

/-- The summand of the rough sum, `m⁻¹|H_y(x/m)|²`. -/
noncomputable def fracRoughTerm (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω)
    (m : ℕ) : ℝ :=
  (m : ℝ)⁻¹ * ‖smoothFracSum f y (x / m) ω‖ ^ 2

omit [MeasurableSpace Ω] in
lemma fracRoughTerm_nonneg (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω) (m : ℕ) :
    0 ≤ fracRoughTerm f y x ω m := by
  rw [fracRoughTerm]
  positivity

omit [MeasurableSpace Ω] in
/-- **Any index range past `w`**: `H_y(w)` is the same sum over `k ≤ N` for `⌊w⌋ ≤ N`, the
kernel vanishing at `w/k < 1`. -/
lemma smoothFracSum_eq_sum_Icc (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {w : ℝ} {N : ℕ}
    (hN : ⌊w⌋₊ ≤ N) (ω : Ω) :
    smoothFracSum f y w ω
      = ∑ k ∈ {k ∈ Finset.Icc 1 N | k ∈ Nat.smoothNumbers (y + 1)},
          f ω k / (Real.sqrt k : ℂ) * (fracKernel (w / k) : ℂ) := by
  refine Finset.sum_subset (fun k hk => ?_) (fun k hk hnot => ?_)
  · rw [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨hk.1.1, le_trans hk.1.2 hN⟩, hk.2⟩
  · rw [Finset.mem_filter, Finset.mem_Icc] at hk hnot
    have hk1 : 1 ≤ k := hk.1.1
    have hlt : ⌊w⌋₊ < k := by
      by_contra hcon
      exact hnot ⟨⟨hk1, not_lt.1 hcon⟩, hk.2⟩
    have hwk : w < k := Nat.lt_of_floor_lt hlt
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hle : w / k ≤ 1 := (div_le_one hk0).2 hwk.le
    rw [fracKernel_eq_zero_of_le_one hle, Complex.ofReal_zero, mul_zero]

omit [MeasurableSpace Ω] in
/-- `H_y(w) = 0` for `w < 1`. -/
lemma smoothFracSum_eq_zero_of_lt_one (f : Ω → ArithmeticFunction ℂ) (y : ℕ) {w : ℝ}
    (hw : w < 1) (ω : Ω) : smoothFracSum f y w ω = 0 := by
  rw [smoothFracSum, Nat.floor_eq_zero.2 hw]
  simp

omit [MeasurableSpace Ω] in
/-- A deterministic bound, at an `ω` where every value has norm at most one: each term is at
most `1`, so `|H_y(w)| ≤ ⌊w⌋`. -/
lemma norm_smoothFracSum_le_of_bound {f : Ω → ArithmeticFunction ℂ} {ω : Ω}
    (hb : ∀ n, ‖f ω n‖ ≤ 1) (y : ℕ) (w : ℝ) :
    ‖smoothFracSum f y w ω‖ ≤ (⌊w⌋₊ : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ k ∈ {k ∈ Finset.Icc 1 ⌊w⌋₊ | k ∈ Nat.smoothNumbers (y + 1)},
      ‖f ω k / (Real.sqrt k : ℂ) * (fracKernel (w / k) : ℂ)‖ ≤ 1 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    have hk1R : (1 : ℝ) ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hk1)
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (fracKernel_nonneg _)]
    exact mul_le_one₀ (div_le_one_of_le₀ (le_trans (hb k) hk1R) (Real.sqrt_nonneg _))
      (fracKernel_nonneg _) (fracKernel_le_one _)
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one]
  exact_mod_cast le_trans (Finset.card_filter_le _ _) (by simp)

/-- The almost-sure form of `RMF.norm_smoothFracSum_le_of_bound`. -/
lemma ae_norm_smoothFracSum_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) (w : ℝ) :
    ∀ᵐ ω ∂μ, ‖smoothFracSum f y w ω‖ ≤ (⌊w⌋₊ : ℝ) := by
  filter_upwards [MeasureTheory.ae_all_iff.2 fun n => hf.norm_apply_le_one n] with ω hω
  exact norm_smoothFracSum_le_of_bound hω y w

/-! ### Measurability -/

/-- `H_y(w)` is measurable in `ω`. -/
lemma measurable_smoothFracSum {f : Ω → ArithmeticFunction ℂ}
    (hf : ∀ n, Measurable fun ω => f ω n) (y : ℕ) (w : ℝ) :
    Measurable (smoothFracSum f y w) :=
  Finset.measurable_sum _ fun n _ => ((hf n).div_const _).mul_const _

/-- **Joint measurability**: `(ω, w) ↦ H_y(w)(ω)`.  For a fixed index range `k ≤ n` the sum is
jointly measurable, and `H_y(w)` is that sum at `n = ⌊w⌋`. -/
lemma measurable_uncurry_smoothFracSum {f : Ω → ArithmeticFunction ℂ}
    (hf : ∀ n, Measurable fun ω => f ω n) (y : ℕ) :
    Measurable fun z : Ω × ℝ => smoothFracSum f y z.2 z.1 := by
  set G : (Ω × ℝ) × ℕ → ℂ := fun p =>
    ∑ k ∈ {k ∈ Finset.Icc 1 p.2 | k ∈ Nat.smoothNumbers (y + 1)},
      f p.1.1 k / (Real.sqrt k : ℂ) * (fracKernel (p.1.2 / k) : ℂ) with hGdef
  have hG : Measurable G := by
    refine measurable_from_prod_countable_left fun n => ?_
    change Measurable fun z : Ω × ℝ =>
      ∑ k ∈ {k ∈ Finset.Icc 1 n | k ∈ Nat.smoothNumbers (y + 1)},
        f z.1 k / (Real.sqrt k : ℂ) * (fracKernel (z.2 / k) : ℂ)
    refine Finset.measurable_sum _ fun k _ => ?_
    refine (((hf k).comp measurable_fst).div_const _).mul ?_
    exact Complex.measurable_ofReal.comp
      (measurable_fracKernel.comp (measurable_snd.div_const _))
  have hcomp : (fun z : Ω × ℝ => smoothFracSum f y z.2 z.1)
      = G ∘ fun z : Ω × ℝ => (z, ⌊z.2⌋₊) := by
    funext z
    rfl
  rw [hcomp]
  exact hG.comp (measurable_id.prodMk (Nat.measurable_floor.comp measurable_snd))

omit [MeasurableSpace Ω] in
/-- `w ↦ H_y(w)(ω)` is measurable: the same argument with `ω` fixed. -/
lemma measurable_smoothFracSum_arg (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (ω : Ω) :
    Measurable fun w : ℝ => smoothFracSum f y w ω := by
  set G : ℝ × ℕ → ℂ := fun p =>
    ∑ k ∈ {k ∈ Finset.Icc 1 p.2 | k ∈ Nat.smoothNumbers (y + 1)},
      f ω k / (Real.sqrt k : ℂ) * (fracKernel (p.1 / k) : ℂ) with hGdef
  have hG : Measurable G := by
    refine measurable_from_prod_countable_left fun n => ?_
    change Measurable fun w : ℝ =>
      ∑ k ∈ {k ∈ Finset.Icc 1 n | k ∈ Nat.smoothNumbers (y + 1)},
        f ω k / (Real.sqrt k : ℂ) * (fracKernel (w / k) : ℂ)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_fracKernel.comp (measurable_id.div_const _)))
  have hcomp : (fun w : ℝ => smoothFracSum f y w ω) = G ∘ fun w : ℝ => (w, ⌊w⌋₊) := by
    funext w
    rfl
  rw [hcomp]
  exact hG.comp (measurable_id.prodMk Nat.measurable_floor)

omit [MeasurableSpace Ω] in
/-- **`H_y(w)` is measurable for the smooth `σ`-algebra**: every `k` in it is `y`-smooth. -/
lemma measurable_smoothAlgebra_smoothFracSum {X : ℕ → Ω → ℂ} (y : ℕ) (w : ℝ) :
    Measurable[smoothAlgebra X y]
      (smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y w) := by
  refine Finset.measurable_sum _ fun n hn => ?_
  exact ((measurable_smoothAlgebra_squarefreeExtension
    (Finset.mem_filter.1 hn).2).div_const _).mul_const _

/-! ### The rough–smooth split -/

omit [MeasurableSpace Ω] in
/-- **The rough–smooth reindexing with a weight**: for multiplicative `f ω`, `x ≥ 0` and any
`w : ℕ → ℂ`, `∑_{n≤x} f(n)w(n) = ∑_{m≤x rough} ∑_{k≤x/m smooth} f(m)f(k)w(mk)`.  The bijection of
`RMF.sum_Icc_eq_sum_rough_smooth`. -/
theorem sum_Icc_mul_eq_sum_rough_smooth {f : Ω → ArithmeticFunction ℂ} (y : ℕ)
    {x : ℝ} (hx : 0 ≤ x) {ω : Ω} (hmul : (f ω).IsMultiplicative) (w : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n * w n
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          ∑ k ∈ {k ∈ Finset.Icc 1 ⌊x / m⌋₊ | k ∈ Nat.smoothNumbers (y + 1)},
            f ω m * f ω k * w (m * k) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun n => (⟨roughPart y n, smoothPart y n⟩ : Σ _ : ℕ, ℕ))
    (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnx : (n : ℝ) ≤ x := le_trans (Nat.cast_le.2 hn.2) (Nat.floor_le hx)
    have hrpos : 0 < roughPart y n := roughPart_pos y n
    have hrposR : (0 : ℝ) < (roughPart y n : ℝ) := by exact_mod_cast hrpos
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hrpos, le_trans (Nat.le_of_dvd (by omega) (roughPart_dvd y hn0)) hn.2⟩,
      isRough_roughPart y n⟩, ⟨smoothPart_pos y n, ?_⟩, smoothPart_mem_smoothNumbers y n⟩
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hrposR, ← Nat.cast_mul, mul_comm]
    exact le_trans (Nat.cast_le.2 (le_of_eq (roughPart_mul_smoothPart y hn0))) hnx
  · rintro ⟨m, k⟩ hp
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, _⟩, ⟨hk1, hk2⟩, _⟩ := hp
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hkx : (k : ℝ) ≤ x / m :=
      le_trans (Nat.cast_le.2 hk2) (Nat.floor_le (by positivity))
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.2 (by positivity), Nat.le_floor ?_⟩
    rw [Nat.cast_mul]
    calc (m : ℝ) * k ≤ (m : ℝ) * (x / m) := by nlinarith [hkx, hmR]
      _ = x := by field_simp
  · intro n hn
    rw [Finset.mem_Icc] at hn
    exact roughPart_mul_smoothPart y (by omega)
  · rintro ⟨m, k⟩ hp
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hm1, _⟩, hmr⟩, _, hks⟩ := hp
    obtain ⟨h1, h2⟩ := roughPart_smoothPart_mul hmr hks hm1
    exact Sigma.ext h1 (heq_of_eq h2)
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    simp only
    rw [← hmul.map_mul_of_coprime
      ((isRough_roughPart y n).coprime_of_mem_smoothNumbers (smoothPart_mem_smoothNumbers y n)),
      roughPart_mul_smoothPart y hn0]

omit [MeasurableSpace Ω] in
/-- **The rough–smooth split of the fractional-part sum.**  For multiplicative `f ω` and `x > 0`,
`R(x) = ∑_{m≤x, m y-rough} f(m)m^{-1/2}·H_y(x/m)`. -/
theorem fracPartSum_eq_sum_rough_smoothFracSum {f : Ω → ArithmeticFunction ℂ} (y : ℕ)
    {x : ℝ} (hx : 0 < x) {ω : Ω} (hmul : (f ω).IsMultiplicative) :
    fracPartSum f x ω
      = ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m},
          f ω m / (Real.sqrt m : ℂ) * smoothFracSum f y (x / m) ω := by
  set w : ℕ → ℂ := fun n => (((Real.sqrt n)⁻¹ * fracKernel (x / n) : ℝ) : ℂ) with hwdef
  have hterm : fracPartSum f x ω = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ω n * w n := by
    rw [fracPartSum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnx : (n : ℝ) ≤ x := le_trans (Nat.cast_le.2 (Finset.mem_Icc.1 hn).2) (Nat.floor_le hx.le)
    change f ω n * ((Int.fract (Real.sqrt (x / n)) : ℝ) : ℂ) / (Real.sqrt x : ℂ)
      = f ω n * ((((Real.sqrt n)⁻¹ * fracKernel (x / n) : ℝ)) : ℂ)
    rw [← fract_sqrt_div_div_sqrt_eq hn1 hnx, mul_div_assoc]
    push_cast
    rfl
  rw [hterm, sum_Icc_mul_eq_sum_rough_smooth y hx.le hmul w]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [smoothFracSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmk : ((m * k : ℕ) : ℝ) = (m : ℝ) * (k : ℝ) := by push_cast; ring
  have hsq : Real.sqrt ((m : ℝ) * (k : ℝ)) = Real.sqrt m * Real.sqrt k :=
    Real.sqrt_mul (Nat.cast_nonneg m) _
  have hdiv : x / ((m : ℝ) * (k : ℝ)) = x / m / k := by rw [div_div]
  simp only [hwdef, hmk, hsq, hdiv]
  push_cast
  rw [mul_inv]
  ring

/-! ### The conditional second moment -/

/-- **The conditional second moment of `R(x)`**, an identity:
`E[|R(x)|² ∣ 𝓕_y] = ∑_{m≤x, m rough and squarefree} m⁻¹|H_y(x/m)|²`.  The `RMF.smoothFracSum`
instance of `RMF.condExp_normSq_roughSmoothSum_sqfree`. -/
theorem condExp_normSq_fracPartSum_sqfree {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) {y : ℕ} {x : ℝ} (hx : 0 < x) :
    μ[fun ω => ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2
        | smoothAlgebra X y]
      =ᵐ[μ] fun ω => ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have key := condExp_normSq_roughSmoothSum_sqfree (x := x) hX
    (G := fun m => smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y (x / m))
    (B := fun m => (⌊x / m⌋₊ : ℝ))
    (fun m => measurable_smoothAlgebra_smoothFracSum y (x / m))
    (fun m => ae_norm_smoothFracSum_le hRa y (x / m))
  refine Filter.EventuallyEq.trans (condExp_congr_ae ?_) key
  filter_upwards with ω
  rw [fracPartSum_eq_sum_rough_smoothFracSum
    (f := fun ω => squarefreeExtension fun p => X p ω) y hx (hRa.isMultiplicative ω)]
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl fun m _ => ?_)
  rw [Complex.ofReal_inv]
  ring

/-- **Conditional Jensen**: `E|R(x)| ≤ E[(∑_{m rough squarefree} m⁻¹|H_y(x/m)|²)^{1/2}]`. -/
theorem integral_norm_fracPartSum_le_integral_sqrt {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {x : ℝ} (hx : 0 < x) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m},
          fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m)
            ^ (1 / 2 : ℝ) ∂μ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX y
  have hm : Measurable (fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x) :=
    Finset.measurable_sum _ fun n _ => ((hRa.measurable_apply n).mul_const _).div_const _
  have h := integral_rpow_norm_le_integral_condExp_rpow hle hm (ae_norm_fracPartSum_le hX x)
    (q := 1 / 2) (by norm_num) (by norm_num)
  have hpow : ∀ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * (1 / 2) : ℝ) = ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ := by
    intro ω
    norm_num
  simp only [hpow] at h
  refine le_trans h (le_of_eq (integral_congr_ae ?_))
  filter_upwards [condExp_normSq_fracPartSum_sqfree hX (y := y) hx] with ω hω
  rw [hω]

/-! ### The rough sum is bounded -/

/-- Every rough term is at most `⌊x⌋²`, almost surely. -/
lemma ae_fracRoughTerm_le {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y : ℕ) {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ ω ∂μ, fracRoughTerm f y x ω m ≤ (⌊x⌋₊ : ℝ) ^ 2 := by
  filter_upwards [ae_norm_smoothFracSum_le hf y (x / m)] with ω hω
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfl : (⌊x / m⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have : x / m ≤ x := div_le_self hx hmR
    exact_mod_cast Nat.floor_le_floor this
  have hsq : ‖smoothFracSum f y (x / m) ω‖ ^ 2 ≤ (⌊x⌋₊ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_trans hω hfl) 2
  rw [fracRoughTerm]
  calc (m : ℝ)⁻¹ * ‖smoothFracSum f y (x / m) ω‖ ^ 2
      ≤ 1 * ‖smoothFracSum f y (x / m) ω‖ ^ 2 := by
        gcongr
        exact inv_le_one_of_one_le₀ hmR
    _ ≤ (⌊x⌋₊ : ℝ) ^ 2 := by rw [one_mul]; exact hsq

/-- The rough sum over any index set is bounded, so it and its powers are integrable. -/
lemma integrable_rpow_sum_fracRoughTerm {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf : IsRademacherRMF f μ) (y : ℕ) {x : ℝ} (hx : 0 ≤ x)
    {s : Finset ℕ} (hs : ∀ m ∈ s, 1 ≤ m) {q : ℝ} (hq0 : 0 ≤ q) :
    Integrable (fun ω => (∑ m ∈ s, fracRoughTerm f y x ω m) ^ q) μ := by
  have hmeas : Measurable fun ω => ∑ m ∈ s, fracRoughTerm f y x ω m := by
    refine Finset.measurable_sum _ fun m _ => ?_
    have : Measurable (smoothFracSum f y (x / m)) :=
      measurable_smoothFracSum hf.measurable_apply y _
    unfold fracRoughTerm
    fun_prop
  have hbdd : ∀ᵐ ω ∂μ, ∑ m ∈ s, fracRoughTerm f y x ω m ≤ (s.card : ℝ) * (⌊x⌋₊ : ℝ) ^ 2 := by
    have hall : ∀ m ∈ s, ∀ᵐ ω ∂μ, fracRoughTerm f y x ω m ≤ (⌊x⌋₊ : ℝ) ^ 2 :=
      fun m hm => ae_fracRoughTerm_le hf y hx m (hs m hm)
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    calc ∑ m ∈ s, fracRoughTerm f y x ω m ≤ ∑ _m ∈ s, (⌊x⌋₊ : ℝ) ^ 2 :=
          Finset.sum_le_sum fun m hm => hω m hm
      _ = (s.card : ℝ) * (⌊x⌋₊ : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmq : Measurable fun ω => (∑ m ∈ s, fracRoughTerm f y x ω m) ^ q :=
    (Real.continuous_rpow_const hq0).measurable.comp hmeas
  refine (memLp_top_of_bound hmq.aestronglyMeasurable
    (((s.card : ℝ) * (⌊x⌋₊ : ℝ) ^ 2) ^ q) ?_).integrable le_top
  filter_upwards [hbdd] with ω hω
  have h0 : (0 : ℝ) ≤ ∑ m ∈ s, fracRoughTerm f y x ω m :=
    Finset.sum_nonneg fun m _ => fracRoughTerm_nonneg _ _ _ _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 q)]
  exact Real.rpow_le_rpow h0 hω hq0

/-! ### The mean square of the smooth factor, by Rankin -/

/-- `E|∑_{n∈S} f(n)c(n)|² ≤ ∑_{n∈S} |c(n)|²` for `0 ∉ S`, by orthogonality. -/
theorem integral_normSq_sum_mul_le_sum_normSq {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (c : ℕ → ℂ) :
    (∫ ω, ‖∑ n ∈ S, f ω n * c n‖ ^ 2 ∂μ) ≤ ∑ n ∈ S, ‖c n‖ ^ 2 := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ) (s := S) (c := c)
    (d := fun m => ((if Squarefree m then 1 else 0 : ℝ) : ℂ))
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hS m hm) (hS n hn)]
      by_cases h : m = n
      · subst h
        by_cases hs : Squarefree m <;> simp [hs]
      · simp [h])
  have hcomm : ∀ ω, ∑ n ∈ S, f ω n * c n = ∑ n ∈ S, c n * f ω n := fun ω =>
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  simp_rw [hcomm]
  have hreal : (∫ ω, ‖∑ n ∈ S, c n * f ω n‖ ^ 2 ∂μ)
      = ∑ m ∈ S, ‖c m‖ ^ 2 * (if Squarefree m then 1 else 0) := by
    exact_mod_cast key
  rw [hreal]
  refine Finset.sum_le_sum fun m _ => ?_
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    exact sq_nonneg _

/-- **Rankin's count of the smooth squarefrees**: for `w > 0` and `δ ≤ 1`,
`#{k ≤ w : k y-smooth squarefree} ≤ w^{1-δ}∏_{p≤y}(1 + p^{δ-1})`: on the range `(w/k)^{1-δ} ≥ 1`,
and the whole sum of `k^{δ-1}` is `RMF.sum_smoothSquarefree_rpow_eq_prod`. -/
theorem card_smoothSquarefree_le_rankin (y : ℕ) {w δ : ℝ} (hw : 0 < w) (hδ1 : δ ≤ 1) :
    (({k ∈ Finset.Icc 1 ⌊w⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k}).card : ℝ)
      ≤ w ^ (1 - δ) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1)) := by
  classical
  rw [← sum_smoothSquarefree_rpow_eq_prod y (δ - 1), Finset.mul_sum, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one]
  refine le_trans (Finset.sum_le_sum (g := fun k : ℕ => w ^ (1 - δ) * (k : ℝ) ^ (δ - 1))
    fun k hk => ?_) ?_
  · have hk := Finset.mem_filter.1 hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk.1).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkw : (k : ℝ) ≤ w :=
      le_trans (Nat.cast_le.2 (Finset.mem_Icc.1 hk.1).2) (Nat.floor_le hw.le)
    have h1 : (k : ℝ) ^ (1 - δ) ≤ w ^ (1 - δ) := Real.rpow_le_rpow hk0.le hkw (by linarith)
    have h2 : (k : ℝ) ^ (1 - δ) * (k : ℝ) ^ (δ - 1) = 1 := by
      rw [← Real.rpow_add hk0]
      norm_num
    calc (1 : ℝ) = (k : ℝ) ^ (1 - δ) * (k : ℝ) ^ (δ - 1) := h2.symm
      _ ≤ w ^ (1 - δ) * (k : ℝ) ^ (δ - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => ?_)
    · have hk := Finset.mem_filter.1 hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk.1).1
      have hp0 : 0 < primorial y := primorial_pos y
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk1, Nat.le_of_dvd hp0
        (dvd_primorial_of_squarefree_of_mem_smoothNumbers hk.2.2 hk.2.1)⟩, hk.2⟩
    · exact mul_nonneg (Real.rpow_nonneg hw.le _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- **The mean square of `H_y(w)`, by Rankin**: for `w > 0` and `δ ≤ 1`,
`E|H_y(w)|² ≤ w^{-δ}∏_{p≤y}(1 + p^{δ-1})`.  Orthogonality leaves
`∑_{k≤w smooth squarefree} ψ(w/k)²/k`, each term at most `1/w` (`ψ(v)² ≤ 1/v`), and the count is
`RMF.card_smoothSquarefree_le_rankin`. -/
theorem integral_normSq_smoothFracSum_le_rankin {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (y : ℕ) {w δ : ℝ} (hw : 0 < w) (hδ1 : δ ≤ 1) :
    (∫ ω, ‖smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y w ω‖ ^ 2 ∂μ)
      ≤ w ^ (-δ) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1)) := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  set S : Finset ℕ := {k ∈ Finset.Icc 1 ⌊w⌋₊ | k ∈ Nat.smoothNumbers (y + 1)} with hSdef
  set c : ℕ → ℂ := fun k => (((Real.sqrt k)⁻¹ * fracKernel (w / k) : ℝ) : ℂ) with hcdef
  have hS0 : ∀ k ∈ S, k ≠ 0 := fun k hk => by
    have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
    omega
  have heq : ∀ ω, smoothFracSum (fun ω => squarefreeExtension fun p => X p ω) y w ω
      = ∑ k ∈ S, squarefreeExtension (fun p => X p ω) k * c k := fun ω => by
    rw [smoothFracSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hcdef]
    push_cast
    ring
  simp_rw [heq]
  -- orthogonality, keeping only the squarefree `k`
  have key := integral_normSq_weightedSum_of_orthogonality'
    (f := fun ω => squarefreeExtension fun p => X p ω) (μ := μ) (s := S) (c := c)
    (d := fun m => ((if Squarefree m then 1 else 0 : ℝ) : ℂ))
    (fun m _ n _ => hRa.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hRa.orthogonality (hS0 m hm) (hS0 n hn)]
      by_cases h : m = n
      · subst h
        by_cases hs : Squarefree m <;> simp [hs]
      · simp [h])
  have hcomm : ∀ ω, ∑ k ∈ S, squarefreeExtension (fun p => X p ω) k * c k
      = ∑ k ∈ S, c k * squarefreeExtension (fun p => X p ω) k := fun ω =>
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  simp_rw [hcomm]
  have hreal : (∫ ω, ‖∑ k ∈ S, c k * squarefreeExtension (fun p => X p ω) k‖ ^ 2 ∂μ)
      = ∑ m ∈ S, ‖c m‖ ^ 2 * (if Squarefree m then 1 else 0) := by
    exact_mod_cast key
  rw [hreal]
  -- each squarefree term is at most `1/w`
  have hterm : ∀ m ∈ S, ‖c m‖ ^ 2 * (if Squarefree m then (1 : ℝ) else 0)
      ≤ (if Squarefree m then w⁻¹ else 0) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    split_ifs
    · rw [mul_one]
      have hc : ‖c m‖ ^ 2 = (m : ℝ)⁻¹ * fracKernel (w / m) ^ 2 := by
        simp only [hcdef]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow,
          Real.sq_sqrt hm0.le]
      rw [hc]
      have hk := fracKernel_sq_le_inv (div_pos hw hm0)
      calc (m : ℝ)⁻¹ * fracKernel (w / m) ^ 2 ≤ (m : ℝ)⁻¹ * (w / m)⁻¹ :=
            mul_le_mul_of_nonneg_left hk (inv_nonneg.2 hm0.le)
        _ = w⁻¹ := by field_simp
    · rw [mul_zero]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
  have hcard := card_smoothSquarefree_le_rankin y hw (δ := δ) hδ1
  have hw1 : w ^ (1 - δ) * w⁻¹ = w ^ (-δ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hw]
    ring_nf
  calc (({k ∈ Finset.Icc 1 ⌊w⌋₊ | k ∈ Nat.smoothNumbers (y + 1) ∧ Squarefree k}).card : ℝ) * w⁻¹
      ≤ (w ^ (1 - δ) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1))) * w⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (inv_nonneg.2 hw.le)
    _ = w ^ (-δ) * ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1)) := by
        rw [← hw1]
        ring

/-- **Rankin's Euler product, explicit**: for `y ≥ 2` and `κ > 0`, at `δ = κ/log y`,
`∏_{p≤y}(1 + p^{δ-1}) ≤ log y·exp(1.42 + (e^κ - 1)(1 + (log 4 + 4)/log y))`: the factor bound
and Mertens' theorems of `RMF.smoothTailSum_le_rankin_explicit`. -/
theorem prod_one_add_rpow_le_rankin_explicit {y : ℕ} (hy : 2 ≤ y) {κ : ℝ} (hκ : 0 < κ) :
    ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (κ / Real.log y - 1))
      ≤ Real.log y * Real.exp (1.42 + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)) := by
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  set δ : ℝ := κ / Real.log y with hδ
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
      ≤ Real.log (Real.log y) + (1.42
        + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)) := by
    have h1 : (Real.exp κ - 1) / Real.log y * ∑ p ∈ Nat.primesBelow (y + 1), Real.log p / p
        ≤ (Real.exp κ - 1) / Real.log y * (Real.log y + Real.log 4 + 4) :=
      mul_le_mul_of_nonneg_left hM1 (div_nonneg heκ hlogy.le)
    have h2 : (Real.exp κ - 1) / Real.log y * (Real.log y + Real.log 4 + 4)
        = (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y) := by
      field_simp
      ring
    linarith
  calc ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1))
      ≤ Real.exp (Real.log (Real.log y) + (1.42
          + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y))) :=
        hprod.trans (Real.exp_le_exp.2 hsum)
    _ = Real.log y * Real.exp (1.42 + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)) := by
        rw [Real.exp_add, Real.exp_log hlogy]

/-! ### The small rough factors -/

/-- **The error of the small rough factors**,
`(1 + log T₀)·log y·exp(1.42 + (e^κ - 1)(1 + (log 4 + 4)/log y) - κ·log(x/T₀)/log y)`. -/
noncomputable def fracLowErr (x T₀ : ℝ) (y : ℕ) (κ : ℝ) : ℝ :=
  (1 + Real.log T₀) * Real.log y
    * Real.exp (1.42 + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)
      - κ * Real.log (x / T₀) / Real.log y)

/-- **The rough factors below `T₀`, in mean square**: for `y ≥ 2`, `1 ≤ T₀ ≤ x` and
`0 < κ ≤ log y`, `E∑_{m<T₀, m rough squarefree} m⁻¹|H_y(x/m)|² ≤ fracLowErr x T₀ y κ`.  Each
`E|H_y(x/m)|² ≤ (x/m)^{-δ}∏(1 + p^{δ-1}) ≤ (x/T₀)^{-δ}∏(1 + p^{δ-1})` at `δ = κ/log y`
(`RMF.integral_normSq_smoothFracSum_le_rankin`), and `∑_{m≤T₀} 1/m ≤ 1 + log T₀`. -/
theorem integral_sum_fracRoughTerm_low_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {x T₀ κ : ℝ} (hT₀ : 1 ≤ T₀)
    (hT₀x : T₀ ≤ x) (hκ : 0 < κ) (hκy : κ ≤ Real.log y) :
    (∫ ω, ∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ (m : ℝ) < T₀},
        fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m ∂μ)
      ≤ fracLowErr x T₀ y κ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  set δ : ℝ := κ / Real.log y with hδ
  have hδ0 : 0 < δ := div_pos hκ hlogy
  have hδ1 : δ ≤ 1 := (div_le_one hlogy).2 hκy
  set P : ℝ := ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (δ - 1)) with hPdef
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun p _ => by
    have : 0 ≤ (p : ℝ) ^ (δ - 1) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    linarith
  set A : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ (m : ℝ) < T₀}
    with hAdef
  have hA1 : ∀ m ∈ A, 1 ≤ m := fun m hm => (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  -- integrability of each term
  have hint : ∀ m ∈ A, Integrable (fun ω =>
      fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m) μ := by
    intro m hm
    have h := integrable_rpow_sum_fracRoughTerm hRa y hx0.le (s := {m})
      (fun m' hm' => by rw [Finset.mem_singleton.1 hm']; exact hA1 m hm) zero_le_one
    simpa using h
  rw [integral_finsetSum _ hint]
  -- each term
  have hterm : ∀ m ∈ A, (∫ ω, fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω)
      y x ω m ∂μ) ≤ (m : ℝ)⁻¹ * ((x / T₀) ^ (-δ) * P) := by
    intro m hm
    have hm1 := hA1 m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmT : (m : ℝ) < T₀ := (Finset.mem_filter.1 hm).2.2.2
    simp only [fracRoughTerm]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hm0.le)
    refine le_trans (integral_normSq_smoothFracSum_le_rankin hX y (div_pos hx0 hm0) hδ1) ?_
    refine mul_le_mul_of_nonneg_right ?_ hP0
    exact Real.rpow_le_rpow_of_nonpos (div_pos hx0 (by linarith))
      (div_le_div_of_nonneg_left hx0.le hm0 hmT.le) (by linarith)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  -- the harmonic mass below `T₀`
  have hH : ∑ m ∈ A, (m : ℝ)⁻¹ ≤ 1 + Real.log T₀ := by
    have hsub : A ⊆ Finset.Icc 1 ⌊T₀⌋₊ := fun m hm => Finset.mem_Icc.2
      ⟨hA1 m hm, Nat.le_floor (Finset.mem_filter.1 hm).2.2.2.le⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity) ?_
    have hh := harmonic_le_one_add_log ⌊T₀⌋₊
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    refine le_trans hh ?_
    have hfl : 0 < ⌊T₀⌋₊ := Nat.floor_pos.2 hT₀
    linarith [Real.log_le_log (by exact_mod_cast hfl) (Nat.floor_le (by linarith : (0 : ℝ) ≤ T₀))]
  have hprod := prod_one_add_rpow_le_rankin_explicit hy hκ
  rw [← hδ, ← hPdef] at hprod
  have hxT : 0 < x / T₀ := div_pos hx0 (by linarith)
  have hrpow : (x / T₀) ^ (-δ) = Real.exp (-(κ * Real.log (x / T₀) / Real.log y)) := by
    rw [Real.rpow_def_of_pos hxT, hδ]
    congr 1
    ring
  have hlogT : 0 ≤ 1 + Real.log T₀ := by linarith [Real.log_nonneg hT₀]
  have hrp0 : 0 ≤ (x / T₀) ^ (-δ) := Real.rpow_nonneg hxT.le _
  calc (∑ m ∈ A, (m : ℝ)⁻¹) * ((x / T₀) ^ (-δ) * P)
      ≤ (1 + Real.log T₀) * ((x / T₀) ^ (-δ) * P) :=
        mul_le_mul_of_nonneg_right hH (mul_nonneg hrp0 hP0)
    _ ≤ (1 + Real.log T₀) * ((x / T₀) ^ (-δ) * (Real.log y
          * Real.exp (1.42 + (Real.exp κ - 1) * (1 + (Real.log 4 + 4) / Real.log y)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hrp0) hlogT
    _ = fracLowErr x T₀ y κ := by
        rw [fracLowErr, hrpow, Real.exp_sub, Real.exp_neg]
        ring

/-! ### The split -/

/-- **The reduction to the large rough factors.**  For `y ≥ 2`, `1 ≤ T₀ ≤ x` and
`0 < κ ≤ log y`:

`E|R(x)| ≤ fracLowErr^{1/2} + E[(∑_{T₀≤m≤x, m rough squarefree} m⁻¹|H_y(x/m)|²)^{1/2}]`.

Conditional Jensen (`RMF.integral_norm_fracPartSum_le_integral_sqrt`), `(a + b)^{1/2} ≤ a^{1/2} +
b^{1/2}`, and Jensen with `RMF.integral_sum_fracRoughTerm_low_le` for `m < T₀`. -/
theorem integral_norm_fracPartSum_le_lowErr_add {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} (hy : 2 ≤ y) {x T₀ κ : ℝ} (hT₀ : 1 ≤ T₀)
    (hT₀x : T₀ ≤ x) (hκ : 0 < κ) (hκy : κ ≤ Real.log y) :
    (∫ ω, ‖fracPartSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ∂μ)
      ≤ fracLowErr x T₀ y κ ^ (1 / 2 : ℝ)
        + ∫ ω, (∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ T₀ ≤ (m : ℝ)},
            fracRoughTerm (fun ω => squarefreeExtension fun p => X p ω) y x ω m)
              ^ (1 / 2 : ℝ) ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hx0 : 0 < x := by linarith
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hfdef
  set A : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m} with hAdef
  set Alo : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ (m : ℝ) < T₀}
    with hAlo
  set Ahi : Finset ℕ := {m ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y m ∧ Squarefree m ∧ T₀ ≤ (m : ℝ)}
    with hAhi
  have hlo : A.filter (fun m : ℕ => (m : ℝ) < T₀) = Alo := by
    rw [hAdef, hAlo, Finset.filter_filter]
    exact Finset.filter_congr fun m _ => by tauto
  have hhi : A.filter (fun m : ℕ => ¬ (m : ℝ) < T₀) = Ahi := by
    rw [hAdef, hAhi, Finset.filter_filter]
    exact Finset.filter_congr fun m _ => by rw [not_lt, and_assoc]
  have hsplit : ∀ ω, ∑ m ∈ A, fracRoughTerm f y x ω m
      = ∑ m ∈ Alo, fracRoughTerm f y x ω m + ∑ m ∈ Ahi, fracRoughTerm f y x ω m := by
    intro ω
    rw [← hlo, ← hhi, Finset.sum_filter_add_sum_filter_not]
  have hlo1 : ∀ m ∈ Alo, 1 ≤ m := fun m hm => (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  have hhi1 : ∀ m ∈ Ahi, 1 ≤ m := fun m hm => (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  have hIlo := integrable_rpow_sum_fracRoughTerm hRa y hx0.le hlo1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hIhi := integrable_rpow_sum_fracRoughTerm hRa y hx0.le hhi1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hIlo1 := integrable_rpow_sum_fracRoughTerm hRa y hx0.le hlo1 (by norm_num : (0 : ℝ) ≤ 1)
  simp only [Real.rpow_one] at hIlo1
  have hA1 : ∀ m ∈ A, 1 ≤ m := fun m hm => (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  have hIA := integrable_rpow_sum_fracRoughTerm hRa y hx0.le hA1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine le_trans (integral_norm_fracPartSum_le_integral_sqrt hX y hx0) ?_
  have hpt : ∀ ω, (∑ m ∈ A, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ)
      ≤ (∑ m ∈ Alo, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ)
        + (∑ m ∈ Ahi, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ) := by
    intro ω
    rw [hsplit ω]
    exact Real.rpow_add_le_add_rpow
      (Finset.sum_nonneg fun m _ => fracRoughTerm_nonneg _ _ _ _ _)
      (Finset.sum_nonneg fun m _ => fracRoughTerm_nonneg _ _ _ _ _) (by norm_num) (by norm_num)
  have hjen : (∫ ω, (∑ m ∈ Alo, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ) ∂μ)
      ≤ fracLowErr x T₀ y κ ^ (1 / 2 : ℝ) :=
    integral_rpow_le_rpow_of_integral_le (by norm_num) (by norm_num)
      (Filter.Eventually.of_forall fun ω =>
        Finset.sum_nonneg fun m _ => fracRoughTerm_nonneg _ _ _ _ _) hIlo1
      (integral_sum_fracRoughTerm_low_le hX hy hT₀ hT₀x hκ hκy)
  calc (∫ ω, (∑ m ∈ A, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ) ∂μ)
      ≤ ∫ ω, ((∑ m ∈ Alo, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ)
          + (∑ m ∈ Ahi, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ)) ∂μ :=
        integral_mono hIA (hIlo.add hIhi) hpt
    _ = (∫ ω, (∑ m ∈ Alo, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ) ∂μ)
          + ∫ ω, (∑ m ∈ Ahi, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ) ∂μ :=
        integral_add hIlo hIhi
    _ ≤ fracLowErr x T₀ y κ ^ (1 / 2 : ℝ)
          + ∫ ω, (∑ m ∈ Ahi, fracRoughTerm f y x ω m) ^ (1 / 2 : ℝ) ∂μ := by
        linarith [hjen]

end RMF
