/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.LemmaT
import RMF.Weighted.FixedQ
import RMF.Weighted.BlockSums

/-!
# The levels of the hierarchy

The sharp bound above `½` (`RMF/Weighted/SharpAboveHalf.lean`) bounds `‖S(x)‖_{2q}` by the levels
of the layered identity (`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`), each
a product of an Euler product and a tail in `L^{2q}`.  This file bounds each kind of level by the
power of `log` it carries, in the form the sum over the levels uses:

* **a middle level** (`RMF.exists_rpow_inv_mul_rpow_inv_le_band`):
  `‖F_y‖·‖𝒯_{y,z}‖ ≪ (log z)^{(2q-1)/2}·b(min{1/(2q-1), log κ})^{1/(2q)}`, from the Euler-product
  moment at the shift `0` and the truncation bound for a band (`RMF/Weighted/LemmaT.lean`), whose
  `κ^{q(2q-1)}` turns `log y` into `log z`;
* **the bottom level** (`RMF.exists_rpow_inv_integral_rpow_norm_truncationTail_le`):
  `‖𝒯_z‖ ≪ (log z)^{(2q-1)/2}·b(min{1/(2q-1), log log z})^{1/(2q)}`, the truncation bound for the
  bottom band;
* **the top level** (`RMF.rpow_inv_mul_rpow_inv_le_top`):
  `‖F_z‖·‖B_z(x)‖ ≪ (log z)^{(2q-1)/2}·(log x/log z)^{1/2}`, through `‖B‖_{2q} ≤ ‖B‖_2` and the
  rough sum's second moment (`RMF.integral_normSq_roughWeightedRademacherSum_le`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The second moment of the rough sum.**  For `2 ≤ y ≤ x`,
`E|B_y(x)|² = ∑_{r ≤ x, y-rough, squarefree} 1/r ≤ ∏_{y<p≤x}(1 + 1/p) ≤ e^{1.86}·log x/log y`:

orthogonality (`RMF.integral_normSq_sum_div_sqrt_of_squarefree`), the index set inside the block
`(y, ⌊x⌋]` (`RMF.sum_blockSquarefree_rpow_eq_prod`), and block Mertens
(`RMF.prod_one_add_inv_primesIco_le`). -/
theorem integral_normSq_roughWeightedRademacherSum_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {y : ℕ} {x : ℝ} (hy : 2 ≤ y) (hyx : (y : ℝ) ≤ x) :
    (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω‖
        ^ 2 ∂μ)
      ≤ Real.exp 1.86 * (Real.log x / Real.log y) := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlogyx : Real.log (y : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hyx
  have hyz : y ≤ ⌊x⌋₊ := Nat.le_floor hyx
  -- the sum runs over the squarefree indices
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
  -- inside the block `(y, ⌊x⌋]`
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
  have hΛ1 : 1 ≤ Real.log x / Real.log y := (one_le_div hlogy).2 hlogyx
  have hlogz : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x / Real.log y * Real.log y := by
    rw [div_mul_cancel₀ _ hlogy.ne']
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) (Nat.floor_le (by linarith))
  have hprod := prod_one_add_inv_primesIco_le hy hyz hΛ1 hlogz
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
    _ ≤ Real.exp (Real.log (Real.log x / Real.log y) + 1.86) := hprod
    _ = Real.exp 1.86 * (Real.log x / Real.log y) := by
        rw [Real.exp_add, Real.exp_log (lt_of_lt_of_le one_pos hΛ1), mul_comm]

/-- **A middle level of the hierarchy.**  For `½ < q ≤ 1`, `3 ≤ y`, `κ = log z/log y ≥ e`, `z ≤ x`
and `V = log x/log z ≥ 2 log κ`,
`‖F_y(½)‖_{2q}·‖𝒯_{y,z}(x)‖_{2q} ≤ A·(log z)^{(2q-1)/2}·b(min{1/(2q-1), log κ})^{1/(2q)}`, `A`
independent of `q`, `y`, `z` and `x`: the Euler-product moment at the shift `0`
(`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_signed_shift_rpow_le_log`) and the
truncation bound for a band (`RMF.exists_const_integral_rpow_norm_blockTruncationTail_le`),
`log y·κ = log z`. -/
theorem exists_rpow_inv_mul_rpow_inv_le_band :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (q : ℝ) (y z : ℕ) (x : ℝ), 1 / 2 < q → q ≤ 1 → 3 ≤ y →
        Real.exp 1 ≤ Real.log z / Real.log y → (z : ℝ) ≤ x →
        2 * Real.log (Real.log z / Real.log y) ≤ Real.log x / Real.log z →
        (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
            (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
            ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          ≤ A * (Real.log z ^ ((2 * q - 1) / 2)
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y)))
              ^ (2 * q)⁻¹) := by
  obtain ⟨CT, hCT, hT⟩ := exists_const_integral_rpow_norm_blockTruncationTail_le (Ω := Ω)
  refine ⟨max 1 (Real.exp 21 * CT), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro X μ hX q y z x hq2 hq1 hy hκ hzx hV
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hκ0 : 0 < Real.log z / Real.log y := lt_of_lt_of_le (Real.exp_pos 1) hκ
  have hlogz0 : 0 < Real.log (z : ℝ) := by
    have h := mul_pos hlogy hκ0
    rwa [mul_comm (Real.log (y : ℝ)), div_mul_cancel₀ _ hlogy.ne'] at h
  have hw0 : 0 < (2 * q)⁻¹ := inv_pos.2 (by linarith)
  have hw1 : (2 * q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2q : 2 * q ≠ 0 := ne_of_gt (by linarith)
  have hexp : q * (2 * q - 1) * (2 * q)⁻¹ = (2 * q - 1) / 2 := by
    refine mul_right_cancel₀ h2q ?_
    rw [mul_assoc (q * (2 * q - 1)), inv_mul_cancel₀ h2q, mul_one]
    ring
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (2 * q - 1)⁻¹ (Real.log (Real.log z / Real.log y)) :=
    ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [hm]
    refine le_min ((one_le_inv₀ (by linarith)).2 (by linarith)) ?_
    have h := Real.log_le_log (Real.exp_pos 1) hκ
    rwa [Real.log_exp] at h
  have hb0 : 0 ≤ ballotFactor q m :=
    le_trans (by norm_num) (half_le_ballotFactor (by linarith) hq1 hm1)
  obtain ⟨EF, hEF⟩ : ∃ EF : ℝ, EF = ∫ ω,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (1 / 2) ω‖
        ^ (2 * q) ∂μ := ⟨_, rfl⟩
  obtain ⟨ET, hET⟩ : ∃ ET : ℝ, ET = ∫ ω,
      ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω‖
        ^ (2 * q) ∂μ := ⟨_, rfl⟩
  rw [← hm, ← hEF, ← hET]
  have hEF0 : 0 ≤ EF := by
    rw [hEF]
    exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hET0 : 0 ≤ ET := by
    rw [hET]
    exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- the Euler product at the shift `0`, and the truncation bound
  have hF : EF ≤ Real.exp 21 * Real.log y ^ (q * (2 * q - 1)) := by
    have h := hRa.integral_norm_randomEulerProduct_signed_shift_rpow_le_log (σ := 0) hq2.le hq1
      hy (by simp)
    have hhalf : (((1 / 2 + 0 : ℝ)) : ℂ) = 1 / 2 := by simp
    rwa [hhalf, ← hEF] at h
  have hTT : ET ≤ CT * ((Real.log z / Real.log y) ^ (q * (2 * q - 1)) * ballotFactor q m) := by
    rw [hET, hm]
    exact hT X μ hX q y z x hq2 hq1 (by omega) hκ hzx hV
  -- both at the power `1/(2q)`
  have hF' := Real.rpow_le_rpow hEF0 hF hw0.le
  have hT' := Real.rpow_le_rpow hET0 hTT hw0.le
  rw [Real.mul_rpow (Real.exp_pos 21).le (Real.rpow_nonneg hlogy.le _),
    ← Real.rpow_mul hlogy.le, hexp] at hF'
  rw [Real.mul_rpow hCT.le (mul_nonneg (Real.rpow_nonneg hκ0.le _) hb0),
    Real.mul_rpow (Real.rpow_nonneg hκ0.le _) hb0, ← Real.rpow_mul hκ0.le, hexp] at hT'
  have hlz : Real.log y ^ ((2 * q - 1) / 2) * (Real.log z / Real.log y) ^ ((2 * q - 1) / 2)
      = Real.log z ^ ((2 * q - 1) / 2) := by
    rw [← Real.mul_rpow hlogy.le hκ0.le, mul_comm (Real.log (y : ℝ)),
      div_mul_cancel₀ _ hlogy.ne']
  have hK := rpow_le_max_one (mul_pos (Real.exp_pos 21) hCT) hw0.le hw1
  calc EF ^ (2 * q)⁻¹ * ET ^ (2 * q)⁻¹
      ≤ (Real.exp 21 ^ (2 * q)⁻¹ * Real.log y ^ ((2 * q - 1) / 2))
        * (CT ^ (2 * q)⁻¹ * ((Real.log z / Real.log y) ^ ((2 * q - 1) / 2)
          * ballotFactor q m ^ (2 * q)⁻¹)) :=
        mul_le_mul hF' hT' (Real.rpow_nonneg hET0 _)
          (mul_nonneg (Real.rpow_nonneg (Real.exp_pos 21).le _) (Real.rpow_nonneg hlogy.le _))
    _ = (Real.exp 21 * CT) ^ (2 * q)⁻¹ * ((Real.log y ^ ((2 * q - 1) / 2)
          * (Real.log z / Real.log y) ^ ((2 * q - 1) / 2)) * ballotFactor q m ^ (2 * q)⁻¹) := by
        rw [Real.mul_rpow (Real.exp_pos 21).le hCT.le]
        ring
    _ = (Real.exp 21 * CT) ^ (2 * q)⁻¹
          * (Real.log z ^ ((2 * q - 1) / 2) * ballotFactor q m ^ (2 * q)⁻¹) := by rw [hlz]
    _ ≤ max 1 (Real.exp 21 * CT)
          * (Real.log z ^ ((2 * q - 1) / 2) * ballotFactor q m ^ (2 * q)⁻¹) :=
        mul_le_mul_of_nonneg_right hK
          (mul_nonneg (Real.rpow_nonneg hlogz0.le _) (Real.rpow_nonneg hb0 _))

/-- **The bottom level of the hierarchy.**  For `½ < q ≤ 1`, `log z ≥ e`, `z ≤ x` and
`V = log x/log z ≥ 2 log log z`,
`‖𝒯_z(x)‖_{2q} ≤ A·(log z)^{(2q-1)/2}·b(min{1/(2q-1), log log z})^{1/(2q)}`:
the truncation bound for the bottom band (`RMF.exists_const_integral_rpow_norm_truncationTail_le`)
at the power `1/(2q)`. -/
theorem exists_rpow_inv_integral_rpow_norm_truncationTail_le :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
      ∀ (q : ℝ) (z : ℕ) (x : ℝ), 1 / 2 < q → q ≤ 1 → Real.exp 1 ≤ Real.log z → (z : ℝ) ≤ x →
        2 * Real.log (Real.log z) ≤ Real.log x / Real.log z →
        (∫ ω, ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) z x ω‖
            ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          ≤ A * (Real.log z ^ ((2 * q - 1) / 2)
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log z))) ^ (2 * q)⁻¹) := by
  obtain ⟨CT, hCT, hT⟩ := exists_const_integral_rpow_norm_truncationTail_le (Ω := Ω)
  refine ⟨max 1 CT, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro X μ hX q z x hq2 hq1 hκ hzx hV
  have hlogz0 : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hκ
  have hw0 : 0 < (2 * q)⁻¹ := inv_pos.2 (by linarith)
  have hw1 : (2 * q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2q : 2 * q ≠ 0 := ne_of_gt (by linarith)
  have hexp : q * (2 * q - 1) * (2 * q)⁻¹ = (2 * q - 1) / 2 := by
    refine mul_right_cancel₀ h2q ?_
    rw [mul_assoc (q * (2 * q - 1)), inv_mul_cancel₀ h2q, mul_one]
    ring
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (2 * q - 1)⁻¹ (Real.log (Real.log z)) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [hm]
    refine le_min ((one_le_inv₀ (by linarith)).2 (by linarith)) ?_
    have h := Real.log_le_log (Real.exp_pos 1) hκ
    rwa [Real.log_exp] at h
  have hb0 : 0 ≤ ballotFactor q m :=
    le_trans (by norm_num) (half_le_ballotFactor (by linarith) hq1 hm1)
  obtain ⟨ET, hET⟩ : ∃ ET : ℝ, ET = ∫ ω,
      ‖truncationTail (fun ω => squarefreeExtension fun p => X p ω) z x ω‖ ^ (2 * q) ∂μ :=
    ⟨_, rfl⟩
  rw [← hm, ← hET]
  have hET0 : 0 ≤ ET := by
    rw [hET]
    exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hTT : ET ≤ CT * (Real.log z ^ (q * (2 * q - 1)) * ballotFactor q m) := by
    rw [hET, hm]
    exact hT X μ hX q z x hq2 hq1 hκ hzx hV
  have hT' := Real.rpow_le_rpow hET0 hTT hw0.le
  rw [Real.mul_rpow hCT.le (mul_nonneg (Real.rpow_nonneg hlogz0.le _) hb0),
    Real.mul_rpow (Real.rpow_nonneg hlogz0.le _) hb0, ← Real.rpow_mul hlogz0.le, hexp] at hT'
  exact le_trans hT' (mul_le_mul_of_nonneg_right (rpow_le_max_one hCT hw0.le hw1)
    (mul_nonneg (Real.rpow_nonneg hlogz0.le _) (Real.rpow_nonneg hb0 _)))

/-- **The top level of the hierarchy.**  For `½ < q ≤ 1` and `3 ≤ z ≤ x`,
`‖F_z(½)‖_{2q}·‖B_z(x)‖_{2q} ≤ e^{21}·e^{1.86}·(log z)^{(2q-1)/2}·(log x/log z)^{1/2}`:
the Euler-product moment at the shift `0`, and `‖B‖_{2q} ≤ ‖B‖_2`
(`RMF.rpow_inv_integral_rpow_le_rpow_inv_integral_sq`) with the rough sum's second moment
(`RMF.integral_normSq_roughWeightedRademacherSum_le`). -/
theorem rpow_inv_mul_rpow_inv_le_top {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q : ℝ} (hq2 : 1 / 2 < q) (hq1 : q ≤ 1) {z : ℕ}
    {x : ℝ} (hz : 3 ≤ z) (hzx : (z : ℝ) ≤ x) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1) (1 / 2) ω‖
        ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      * (∫ ω, ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x ω‖
        ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
      ≤ Real.exp 21 * Real.exp 1.86
        * (Real.log z ^ ((2 * q - 1) / 2) * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹) := by
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hlogzx : Real.log (z : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hzx
  have hw0 : 0 < (2 * q)⁻¹ := inv_pos.2 (by linarith)
  have hw1 : (2 * q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2q : 2 * q ≠ 0 := ne_of_gt (by linarith)
  have hexp : q * (2 * q - 1) * (2 * q)⁻¹ = (2 * q - 1) / 2 := by
    refine mul_right_cancel₀ h2q ?_
    rw [mul_assoc (q * (2 * q - 1)), inv_mul_cancel₀ h2q, mul_one]
    ring
  have hdiv0 : 0 ≤ Real.log x / Real.log z := div_nonneg (by linarith) hlogz.le
  obtain ⟨EF, hEF⟩ : ∃ EF : ℝ, EF = ∫ ω,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1) (1 / 2) ω‖
        ^ (2 * q) ∂μ := ⟨_, rfl⟩
  obtain ⟨EB, hEB⟩ : ∃ EB : ℝ, EB = ∫ ω,
      ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x ω‖
        ^ (2 * q) ∂μ := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : ℝ, E2 = ∫ ω,
      ‖roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x ω‖
        ^ 2 ∂μ := ⟨_, rfl⟩
  rw [← hEF, ← hEB]
  have hEF0 : 0 ≤ EF := by
    rw [hEF]
    exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hEB0 : 0 ≤ EB := by
    rw [hEB]
    exact integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hE20 : 0 ≤ E2 := by
    rw [hE2]
    exact integral_nonneg fun ω => by positivity
  -- the Euler product at the shift `0`
  have hF : EF ≤ Real.exp 21 * Real.log z ^ (q * (2 * q - 1)) := by
    have h := hRa.integral_norm_randomEulerProduct_signed_shift_rpow_le_log (σ := 0) hq2.le hq1
      hz (by simp)
    have hhalf : (((1 / 2 + 0 : ℝ)) : ℂ) = 1 / 2 := by simp
    rwa [hhalf, ← hEF] at h
  have hF' := Real.rpow_le_rpow hEF0 hF hw0.le
  rw [Real.mul_rpow (Real.exp_pos 21).le (Real.rpow_nonneg hlogz.le _),
    ← Real.rpow_mul hlogz.le, hexp] at hF'
  have he21 : Real.exp 21 ^ (2 * q)⁻¹ ≤ Real.exp 21 := by
    calc Real.exp 21 ^ (2 * q)⁻¹ ≤ Real.exp 21 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (by norm_num)) hw1
      _ = Real.exp 21 := Real.rpow_one _
  -- the rough sum: `‖B‖_{2q} ≤ ‖B‖_2`, and its second moment
  have hB : EB ^ (2 * q)⁻¹ ≤ E2 ^ (2 : ℝ)⁻¹ := by
    rw [hEB, hE2]
    exact rpow_inv_integral_rpow_le_rpow_inv_integral_sq (by linarith) hq1
      (Finset.measurable_sum _ fun n _ => (hRa.measurable_apply n).div_const _)
      (ae_norm_sum_div_sqrt_le hRa _)
  have hB2 : E2 ≤ Real.exp 1.86 * (Real.log x / Real.log z) := by
    rw [hE2]
    exact integral_normSq_roughWeightedRademacherSum_le hX (by omega) hzx
  have hB' : E2 ^ (2 : ℝ)⁻¹ ≤ Real.exp 1.86 * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹ := by
    refine le_trans (Real.rpow_le_rpow hE20 hB2 (by norm_num)) ?_
    rw [Real.mul_rpow (Real.exp_pos _).le hdiv0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hdiv0 _)
    calc Real.exp 1.86 ^ (2 : ℝ)⁻¹ ≤ Real.exp 1.86 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (by norm_num)) (by norm_num)
      _ = Real.exp 1.86 := Real.rpow_one _
  have hL0 : 0 ≤ Real.log z ^ ((2 * q - 1) / 2) := Real.rpow_nonneg hlogz.le _
  calc EF ^ (2 * q)⁻¹ * EB ^ (2 * q)⁻¹
      ≤ (Real.exp 21 ^ (2 * q)⁻¹ * Real.log z ^ ((2 * q - 1) / 2))
        * (Real.exp 1.86 * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹) :=
        mul_le_mul hF' (le_trans hB hB') (Real.rpow_nonneg hEB0 _)
          (mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) hL0)
    _ ≤ (Real.exp 21 * Real.log z ^ ((2 * q - 1) / 2))
        * (Real.exp 1.86 * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he21 hL0)
          (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hdiv0 _))
    _ = Real.exp 21 * Real.exp 1.86
        * (Real.log z ^ ((2 * q - 1) / 2) * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹) := by ring

end RMF
