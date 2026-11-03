/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfBandLevelExplicit
import RMF.Weighted.SharpLevels

/-!
# The hierarchy above `q = ½`, explicit

The layered identity (`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`) at the
scales `z_ℓ = ⌊exp(log x/V_ℓ)⌋`, `V₀ = 3Λ`, `V_{ℓ+1} = 3 log V_ℓ` (`RMF.aboveV`), with every level
explicit:

`‖S(x)‖_{2q} ≤ top(z_L) + ∑_{ℓ<L}(pfFull·bandLevel)^{1/(2q)} + bottomLevel^{1/(2q)}`

(`RMF.rpow_inv_integral_rpow_weightedRademacherSum_le_aboveHierarchy`), for every `L` with
`V_ℓ ≥ 8` up to `L`, once `Λ = log log x ≥ 11`.  The top level is `‖F_z‖_{2q}‖B_z(x)‖_2` with
the rough sum's second moment by Mertens (`RMF.integral_normSq_roughWeightedRademacherSum_le_exp`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The top level -/

/-- **The rough sum's second moment, with Mertens' error**: for `2 ≤ y ≤ x`,
`E|B_y(x)|² ≤ (log x/log y)e^{18.0056/log y}`: orthogonality, the index set inside the block
`(y, ⌊x⌋]` and `∏(1 + 1/p) ≤ exp ∑ 1/p` with Mertens on the block (`RMF.sum_primesIco_inv_le`).
The twin of `RMF.integral_normSq_roughWeightedRademacherSum_le` without its constant `e^{1.86}`. -/
theorem integral_normSq_roughWeightedRademacherSum_le_exp {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} {x : ℝ} (hy : 2 ≤ y) (hyx : (y : ℝ) ≤ x) :
    (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω‖
        ^ 2 ∂μ)
      ≤ Real.log x / Real.log y * Real.exp (18.0056 / Real.log y) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hyz : y ≤ ⌊x⌋₊ := Nat.le_floor hyx
  have hsq : {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}
      ⊆ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n} := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hB : ∀ ω, roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω
      = ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n},
          (squarefreeExtension fun p => X p ω) n / (Real.sqrt n : ℂ) := by
    intro ω
    rw [roughWeightedRademacherSum]
    refine (Finset.sum_subset hsq fun n hn hns => ?_).symm
    have hsf : ¬ Squarefree n := fun h =>
      hns (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2, h⟩)
    simp only [squarefreeExtension_apply_of_not_squarefree _ hsf, zero_div]
  have hs0 : ∀ m ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}, m ≠ 0 := by
    intro m hm
    have h := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
    omega
  have hs1 : ∀ m ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}, Squarefree m :=
    fun m hm => (Finset.mem_filter.1 hm).2.2
  have hmoment : (∫ ω,
      ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω‖ ^ 2 ∂μ)
      = ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}, (n : ℝ)⁻¹ := by
    simp_rw [hB]
    exact integral_normSq_sum_div_sqrt_of_squarefree hRa hs0 hs1
  rw [hmoment]
  have hsub : {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}
      ⊆ {m ∈ Finset.Icc 1 (primorial ⌊x⌋₊)
          | m ∈ Nat.smoothNumbers (⌊x⌋₊ + 1) ∧ IsRough y m ∧ Squarefree m} := by
    intro n hn
    obtain ⟨hnI, hnr, hnsf⟩ := Finset.mem_filter.1 hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hnI
    have hsm : n ∈ Nat.smoothNumbers (⌊x⌋₊ + 1) :=
      Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
    have hdvd := dvd_primorial_of_squarefree_of_mem_smoothNumbers hnsf hsm
    exact Finset.mem_filter.2
      ⟨Finset.mem_Icc.2 ⟨hn1, Nat.le_of_dvd (primorial_pos _) hdvd⟩, hsm, hnr, hnsf⟩
  have hN2 : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast le_trans hy hyz
  have hlogN : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hNx : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hyN : Real.log y ≤ Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hyz)
  have hmert := sum_primesIco_inv_le hy hyz
  calc ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}, (n : ℝ)⁻¹
      ≤ ∑ m ∈ {m ∈ Finset.Icc 1 (primorial ⌊x⌋₊)
          | m ∈ Nat.smoothNumbers (⌊x⌋₊ + 1) ∧ IsRough y m ∧ Squarefree m}, (m : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => inv_nonneg.2 (Nat.cast_nonneg i)
    _ = ∑ m ∈ {m ∈ Finset.Icc 1 (primorial ⌊x⌋₊)
          | m ∈ Nat.smoothNumbers (⌊x⌋₊ + 1) ∧ IsRough y m ∧ Squarefree m}, (m : ℝ) ^ (-1 : ℝ) :=
        Finset.sum_congr rfl fun m _ => by rw [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_one]
    _ = ∏ p ∈ primesIco (y + 1) (⌊x⌋₊ + 1), (1 + (p : ℝ) ^ (-1 : ℝ)) :=
        sum_blockSquarefree_rpow_eq_prod y ⌊x⌋₊ (-1)
    _ = ∏ p ∈ primesIco (y + 1) (⌊x⌋₊ + 1), (1 + ((p : ℝ))⁻¹) :=
        Finset.prod_congr rfl fun p _ => by rw [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_one]
    _ ≤ Real.exp (∑ p ∈ primesIco (y + 1) (⌊x⌋₊ + 1), ((p : ℝ))⁻¹) :=
        Real.prod_one_add_le_exp_sum _ fun p => inv_nonneg.2 (Nat.cast_nonneg p)
    _ ≤ Real.exp (Real.log (Real.log (⌊x⌋₊ : ℝ)) - Real.log (Real.log y)
          + (9.0028 / Real.log (⌊x⌋₊ : ℝ) + 9.0028 / Real.log y)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.log (⌊x⌋₊ : ℝ) / Real.log y
          * Real.exp (9.0028 / Real.log (⌊x⌋₊ : ℝ) + 9.0028 / Real.log y) := by
        rw [Real.exp_add, ← Real.log_div hlogN.ne' hlogy.ne', Real.exp_log (by positivity)]
    _ ≤ Real.log x / Real.log y * Real.exp (18.0056 / Real.log y) := by
        have h1 : 9.0028 / Real.log (⌊x⌋₊ : ℝ) ≤ 9.0028 / Real.log y :=
          div_le_div_of_nonneg_left (by norm_num) hlogy hyN
        have h2 : Real.exp (9.0028 / Real.log (⌊x⌋₊ : ℝ) + 9.0028 / Real.log y)
            ≤ Real.exp (18.0056 / Real.log y) := Real.exp_le_exp.2 (by
          have : 18.0056 / Real.log y = 9.0028 / Real.log y + 9.0028 / Real.log y := by ring
          linarith)
        exact mul_le_mul (div_le_div_of_nonneg_right hNx hlogy.le) h2 (Real.exp_pos _).le
          (div_nonneg (by linarith) hlogy.le)

/-- **The top level, explicit**: for `½ ≤ q ≤ 1` and `2 ≤ z ≤ x`,
`‖F_z(½)‖_{2q}‖B_z(x)‖_{2q} ≤ pfFull(q, z)^{1/(2q)}·((log x/log z)e^{18.0056/log z})^{1/2}`:
(PF) and `‖·‖_{2q} ≤ ‖·‖_2` with the rough sum's second moment. -/
theorem rpow_inv_mul_rpow_inv_le_top_explicit {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) {z : ℕ}
    {x : ℝ} (hz : 2 ≤ z) (hzx : (z : ℝ) ≤ x) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1) (1 / 2) ω‖
        ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      * (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x ω‖
        ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ pfFull q z ^ (2 * q)⁻¹
        * (Real.log x / Real.log z * Real.exp (18.0056 / Real.log z)) ^ (2 : ℝ)⁻¹ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hw0 : 0 ≤ (2 * q)⁻¹ := inv_nonneg.2 (by linarith)
  have hF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1)
      (1 / 2) ω‖ ^ (2 * q) ∂μ) ≤ pfFull q z := by
    have h := hRa.integral_norm_randomEulerProduct_shift_rpow_le_above_half (σ := 0) le_rfl
      hq0 hq1 hz
    have hs : (((1 / 2 + 0 : ℝ)) : ℂ) = 1 / 2 := by norm_num
    rw [hs] at h
    exact h
  have hF0 : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1)
      (1 / 2) ω‖ ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hB : (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x
      ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x
        ω‖ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ :=
    rpow_inv_integral_rpow_le_rpow_inv_integral_sq (by linarith) hq1
      (Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _)
      (ae_norm_sum_div_sqrt_le hRa _)
  have hB2 := integral_normSq_roughWeightedRademacherSum_le_exp hX hz hzx
  have hB20 : 0 ≤ ∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω)
      z x ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have hB' := le_trans hB (Real.rpow_le_rpow hB20 hB2 (by norm_num))
  exact mul_le_mul (Real.rpow_le_rpow hF0 hF hw0) hB'
    (Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) _)
    (Real.rpow_nonneg (le_trans hF0 hF) _)

/-! ### The scales -/

/-- The hierarchy's `V_ℓ`: `V₀ = 3Λ`, `V_{ℓ+1} = 3 log V_ℓ`. -/
noncomputable def aboveV (Λ : ℝ) : ℕ → ℝ
  | 0 => 3 * Λ
  | n + 1 => 3 * Real.log (aboveV Λ n)

/-- The hierarchy's scale `z_ℓ = ⌊exp(log x/V_ℓ)⌋`, `Λ = log log x`. -/
noncomputable def aboveZ (x : ℝ) (ℓ : ℕ) : ℕ :=
  ⌊Real.exp (Real.log x / aboveV (Real.log (Real.log x)) ℓ)⌋₊

lemma aboveV_zero (Λ : ℝ) : aboveV Λ 0 = 3 * Λ := rfl

lemma aboveV_succ (Λ : ℝ) (n : ℕ) : aboveV Λ (n + 1) = 3 * Real.log (aboveV Λ n) := rfl

/-- `3 log v ≤ v` for `v ≥ 8`: `log v ≤ v/8 - 1 + log 8`. -/
lemma three_mul_log_le_self {v : ℝ} (hv : 8 ≤ v) : 3 * Real.log v ≤ v := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < v / 8)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_two_lt_d9
  linarith

/-- Along the hierarchy, while `V ≥ 8`, the `V_ℓ` decrease: `V_ℓ ≤ 3Λ`. -/
lemma aboveV_le {Λ : ℝ} {L : ℕ} (hL : ∀ ℓ ≤ L, 8 ≤ aboveV Λ ℓ) :
    ∀ ℓ ≤ L, aboveV Λ ℓ ≤ 3 * Λ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => exact le_of_eq (aboveV_zero Λ)
  | succ n ih =>
    rw [aboveV_succ]
    exact le_trans (three_mul_log_le_self (hL n (by omega))) (ih (by omega))

lemma aboveV_succ_le {Λ : ℝ} {L : ℕ} (hL : ∀ ℓ ≤ L, 8 ≤ aboveV Λ ℓ) {ℓ : ℕ} (hℓ : ℓ < L) :
    aboveV Λ (ℓ + 1) ≤ aboveV Λ ℓ := by
  rw [aboveV_succ]
  exact three_mul_log_le_self (hL ℓ hℓ.le)

/-- `e^Λ ≥ 21Λ² + 3.6Λ` for `Λ ≥ 11`, through `Λ^7/7! ≤ e^Λ`. -/
lemma exp_ge_poly_of_eleven_le {Λ : ℝ} (hΛ : 11 ≤ Λ) : 21 * Λ ^ 2 + 3.6 * Λ ≤ Real.exp Λ := by
  have h := Real.pow_div_factorial_le_exp (x := Λ) (by linarith : (0 : ℝ) ≤ Λ) 7
  have hf : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hΛ5 : (161051 : ℝ) ≤ Λ ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hΛ 5
    norm_num at this ⊢
    linarith
  have hΛ2 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
  nlinarith [mul_le_mul_of_nonneg_left hΛ5 hΛ2]

/-- **The scales' facts**, for `x ≥ 3` with `Λ = log log x ≥ 11` and `V_ℓ ≥ 8` up to `L`: every
`z_ℓ` is in `[2, x]`, has sieve level `⌊z_ℓ/(log x)^7⌋ ≥ 2`, and the scales increase. -/
lemma aboveZ_facts {x : ℝ} (hx3 : 3 ≤ x) (hΛ : 11 ≤ Real.log (Real.log x)) {L : ℕ}
    (hL : ∀ ℓ ≤ L, 8 ≤ aboveV (Real.log (Real.log x)) ℓ) :
    1 < Real.log x ∧ (∀ ℓ ≤ L, 2 ≤ aboveZ x ℓ ∧ (aboveZ x ℓ : ℝ) ≤ x
      ∧ 2 ≤ sieveLevel x (aboveZ x ℓ)) ∧ (∀ ℓ < L, aboveZ x ℓ ≤ aboveZ x (ℓ + 1)) := by
  set Λ := Real.log (Real.log x) with hΛdef
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx : Real.log x = Real.exp Λ := by rw [hΛdef, Real.exp_log hlx0]
  have hexpΛ := exp_ge_poly_of_eleven_le hΛ
  have hlx1 : 1 < Real.log x := by rw [hlx]; nlinarith
  refine ⟨hlx1, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · have hV8 := hL ℓ hℓ
    have hV3 := aboveV_le hL ℓ hℓ
    have hVpos : 0 < aboveV Λ ℓ := by linarith
    set u := Real.log x / aboveV Λ ℓ with hu
    have hu1 : u ≤ Real.log x := by
      rw [hu, div_le_iff₀ hVpos]
      nlinarith
    -- `u ≥ e^Λ/(3Λ) ≥ 7Λ + 1.2`
    have hΛpos : 0 < Λ := by linarith
    have hu2 : 7 * Λ + 1.2 ≤ u := by
      rw [hu, le_div_iff₀ hVpos, hlx]
      nlinarith
    have hxz : (aboveZ x ℓ : ℝ) ≤ x := by
      have h1 : Real.exp u ≤ x := by
        calc Real.exp u ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 hu1
          _ = x := Real.exp_log hx0
      exact le_trans (Nat.floor_le (Real.exp_pos _).le) h1
    -- `z ≥ e^u - 1 ≥ 2(log x)^7 + 2`
    have hbig : 2 * Real.log x ^ 7 + 2 ≤ Real.exp u - 1 := by
      have h7 : Real.exp (7 * Λ + 1.2) ≤ Real.exp u := Real.exp_le_exp.2 hu2
      have he : Real.exp (7 * Λ + 1.2) = Real.log x ^ 7 * Real.exp 1.2 := by
        rw [Real.exp_add, hlx, ← Real.exp_nat_mul]
        push_cast
        ring_nf
      have he12 : (3 : ℝ) ≤ Real.exp 1.2 := by
        have h2 : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
        have h3 := Real.exp_one_gt_d9
        have h4 : 1.2 ≤ Real.exp 0.2 := by linarith [Real.add_one_le_exp (0.2 : ℝ)]
        nlinarith [Real.exp_pos 0.2]
      have hlx12 : 12 ≤ Real.log x := by
        rw [hlx]
        linarith [Real.add_one_le_exp Λ]
      have hlx7 : Real.log x ≤ Real.log x ^ 7 := by
        have h1 : 1 ≤ Real.log x ^ 6 := one_le_pow₀ (by linarith)
        calc Real.log x = Real.log x * 1 := (mul_one _).symm
          _ ≤ Real.log x * Real.log x ^ 6 := mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = Real.log x ^ 7 := by ring
      nlinarith
    have hfl : Real.exp u - 1 < (aboveZ x ℓ : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp u)
      rw [aboveZ]
      linarith
    refine ⟨?_, hxz, ?_⟩
    · have : (2 : ℝ) ≤ (aboveZ x ℓ : ℝ) := by nlinarith [one_le_pow₀ hlx1.le (n := 7)]
      exact_mod_cast this
    · rw [sieveLevel]
      refine Nat.le_floor ?_
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith
  · have hV := aboveV_succ_le hL hℓ
    have hV8 := hL (ℓ + 1) hℓ
    refine Nat.floor_le_floor (Real.exp_le_exp.2 ?_)
    exact div_le_div_of_nonneg_left hlx0.le (by linarith) hV

/-! ### The hierarchy -/

/-- **The hierarchy above `½`, explicit.**  For `½ ≤ q ≤ 1`, `θ, η', ε > 0`, any
`c_s`, `T_m`, `x ≥ 3` with `Λ = log log x ≥ 11` and any `L` with `V_ℓ ≥ 8` for `ℓ ≤ L`:

`‖S(x)‖_{2q} ≤ pfFull(q, z_L)^{1/(2q)}((log x/log z_L)e^{18.0056/log z_L})^{1/2}
  + ∑_{ℓ<L}(pfFull(q, z_ℓ)·bandLevel(z_ℓ, z_{ℓ+1}))^{1/(2q)} + bottomLevel(z_0)^{1/(2q)}`,

`z_ℓ = RMF.aboveZ x ℓ`: the layered identity top-down (`Y k = z_{L+1-k}`), independence on each
product, and the explicit levels (`RMF.integral_rpow_norm_blockTruncationTail_le_bandLevel`,
`RMF.integral_rpow_norm_truncationTail_le_bottomLevel`,
`RMF.rpow_inv_mul_rpow_inv_le_top_explicit`). -/
theorem rpow_inv_integral_rpow_weightedRademacherSum_le_aboveHierarchy {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {q θ η' ε cs Tm x : ℝ} {L : ℕ}
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hθ : 0 < θ) (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x)
    (hΛ : 11 ≤ Real.log (Real.log x))
    (hL : ∀ ℓ ≤ L, 8 ≤ aboveV (Real.log (Real.log x)) ℓ) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ^ (2 * q)⁻¹
      ≤ pfFull q (aboveZ x L) ^ (2 * q)⁻¹
          * (Real.log x / Real.log (aboveZ x L)
            * Real.exp (18.0056 / Real.log (aboveZ x L))) ^ (2 : ℝ)⁻¹
        + ∑ ℓ ∈ Finset.range L, (pfFull q (aboveZ x ℓ)
            * bandLevel q θ η' ε cs x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ (2 * q)⁻¹
        + bottomLevel q θ η' ε cs Tm x (aboveZ x 0) ^ (2 * q)⁻¹ := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hlx1, hz, hmono⟩ := aboveZ_facts hx3 hΛ hL
  have hw0 : 0 ≤ (2 * q)⁻¹ := inv_nonneg.2 (by linarith)
  -- the layered identity, top-down
  have hY : ∀ k, 1 ≤ k → k < L + 1 → aboveZ x (L + 1 - (k + 1)) ≤ aboveZ x (L + 1 - k) := by
    intro k hk1 hkK
    rw [show L + 1 - (k + 1) = L - k by omega, show L + 1 - k = L - k + 1 by omega]
    exact hmono (L - k) (by omega)
  have hN := rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered hX hq0
    (Y := fun k => aboveZ x (L + 1 - k)) (K := L + 1) (by omega) hY x
  beta_reduce at hN
  rw [show L + 1 - 1 = L by omega, show L + 1 - (L + 1) = 0 by omega] at hN
  refine le_trans hN (add_le_add (add_le_add ?_ ?_) ?_)
  · -- the top level
    obtain ⟨hz2, hzx, -⟩ := hz L le_rfl
    exact rpow_inv_mul_rpow_inv_le_top_explicit hX hq0 hq1 hz2 hzx
  · -- the bands
    have hre : ∑ k ∈ Finset.Ico 1 (L + 1),
        (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (aboveZ x (L + 1 - (k + 1)) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (aboveZ x (L + 1 - (k + 1))) (aboveZ x (L + 1 - k)) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
        = ∑ ℓ ∈ Finset.range L,
          (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (aboveZ x ℓ + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (aboveZ x ℓ) (aboveZ x (ℓ + 1)) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range, show L + 1 - 1 = L by omega]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjL := Finset.mem_range.1 hj
      rw [show L + 1 - (1 + (L - 1 - j) + 1) = j by omega,
        show L + 1 - (1 + (L - 1 - j)) = j + 1 by omega]
    rw [hre]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    have hℓL := Finset.mem_range.1 hℓ
    obtain ⟨hy2, -, -⟩ := hz ℓ hℓL.le
    obtain ⟨-, hzx, hz'⟩ := hz (ℓ + 1) hℓL
    have hlev := integral_rpow_norm_blockTruncationTail_le_bandLevel hX (cs := cs) hq0 hq1 hθ hη'
      hε hy2 (hmono ℓ hℓL) hzx hlx1 hz'
    have hF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (aboveZ x ℓ + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ≤ pfFull q (aboveZ x ℓ) := by
      have h := hRa.integral_norm_randomEulerProduct_shift_rpow_le_above_half (σ := 0) le_rfl
        hq0 hq1 hy2
      have hs : (((1 / 2 + 0 : ℝ)) : ℂ) = 1 / 2 := by norm_num
      rw [hs] at h
      exact h
    have hF0 : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (aboveZ x ℓ + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
    have hT0 : 0 ≤ ∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
        (aboveZ x ℓ) (aboveZ x (ℓ + 1)) x ω‖ ^ (2 * q) ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
    rw [← Real.mul_rpow hF0 hT0]
    exact Real.rpow_le_rpow (mul_nonneg hF0 hT0) (mul_le_mul hF hlev hT0 (le_trans hF0 hF)) hw0
  · -- the bottom level
    obtain ⟨hz2, hzx, hz'⟩ := hz 0 (Nat.zero_le L)
    have hbot := integral_rpow_norm_truncationTail_le_bottomLevel hX (cs := cs) (Tm := Tm) hq0 hq1
      hθ hη' hε hz2 hzx hlx1 hz'
    exact Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hbot hw0

end RMF
