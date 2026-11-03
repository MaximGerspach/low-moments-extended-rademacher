/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.C3Explicit
import RMF.UniformLower.HP1Cert.Basic

/-!
# (C3)*'s numerals: the generic rows

What turns `RMF.c3Val` (`RMF/UniformLower/C3Explicit.lean`) into certified numerals at the
damping `η = 1/200` and the smoothing `δ = 10⁻⁴`.

* **The fixed numerals**: `e^{-1/100}`, `c3Slo (1/200)`, `topEps ≤ 2·10⁻⁴⁰`, the ranges of
  `topVLo (1/200)` and `topVHi`, `e^{-2}`, and the Lindeberg error `≤ 10⁻¹⁸`.
* **The Ville factor by rationals** (`RMF.villeSum_le_rat`), and its truncation: once
  `y²e^{-2i₀} + t/2 - (2q - ½) ≤ 0` every later step's exponent is `≤ 0`, so
  `villeFactor … K ≤ villeFactor … i₀` for every `K` (`RMF.villeFactor_le_trunc`).
* **One row** (`RMF.le_c3Val_of`): `c ≤ c3Val` from rational bounds on the top block's mean,
  the two `Φ` values (the alternating Taylor bounds of `RMF/UniformLower/HP1Certificate.lean`),
  one exponential and `F`.
* **Cells and the window**: `RMF.C3CellCert` (a cell's certificate for a set of ladder
  lengths), its consequence for (C3)* (`RMF.le_setIntegral_halfLadder_twistQ_of_cellCert`), and
  the covering of `RMF.halfWindow` by the cells of a partition
  (`RMF.exists_cell_of_mem_halfWindow`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The fixed numerals at `η = 1/200` -/

/-- `e^{-1/100} ∈ [0.9900498337, 0.9900498338]`. -/
lemma exp_neg_two_hundredth_mem :
    (0.9900498337 : ℝ) ≤ Real.exp (-(2 * (1 / 200)))
      ∧ Real.exp (-(2 * (1 / 200))) ≤ 0.9900498338 := by
  constructor
  · exact le_exp_neg_of_taylor (f := 1 / 100) 0 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_sum_neg (y := 1 / 100) 5 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `c3Slo (1/200) ∈ [0.9900432333, 0.9900432335]`. -/
lemma c3Slo_two_hundredth_mem :
    (0.9900432333 : ℝ) ≤ c3Slo (1 / 200) ∧ c3Slo (1 / 200) ≤ 0.9900432335 := by
  obtain ⟨h1, h2⟩ := exp_neg_two_hundredth_mem
  rw [c3Slo]
  constructor <;> nlinarith

lemma topEps_nonneg : 0 ≤ topEps := by
  rw [topEps, c3Shi]
  positivity

/-- `topEps ≤ 2·10⁻⁴⁰`. -/
lemma topEps_le : topEps ≤ 2 / 10 ^ 40 := by
  have h := exp_neg_exp_twenty_half_le
  have h0 := Real.exp_pos (-(Real.exp 20 / 2))
  rw [topEps, c3Shi]
  nlinarith

/-- `topVLo (1/200) ∈ [0.9900432332, 0.9900432335]`. -/
lemma topVLo_two_hundredth_mem :
    (0.9900432332 : ℝ) ≤ topVLo (1 / 200) ∧ topVLo (1 / 200) ≤ 0.9900432335 := by
  obtain ⟨h1, h2⟩ := c3Slo_two_hundredth_mem
  have h3 := topEps_le
  have h4 := topEps_nonneg
  rw [topVLo]
  constructor <;> linarith

/-- `topVHi ∈ [1 + 1/150000, 1.0000066667]`. -/
lemma topVHi_mem : (1 + 1 / 150000 : ℝ) ≤ topVHi ∧ topVHi ≤ 1.0000066667 := by
  have h3 := topEps_le
  have h4 := topEps_nonneg
  rw [topVHi, c3Shi]
  constructor <;> linarith

/-- `e^{-2} ∈ [0.1353352832, 0.1353352833]`. -/
lemma exp_neg_two_mem_sharp :
    (0.1353352832 : ℝ) ≤ Real.exp (-2) ∧ Real.exp (-2) ≤ 0.1353352833 := by
  constructor
  · exact le_exp_neg_of_taylor (f := 0) 2 1 (by norm_num) (by norm_num) le_rfl (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  · exact exp_le_of_sum_neg (y := 2) 18 le_rfl (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `e^{-2i} = (e^{-2})^i`. -/
lemma exp_neg_two_mul_nat (i : ℕ) : Real.exp (-(2 * (i : ℝ))) = Real.exp (-2) ^ i := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **The Lindeberg error at `δ = 10⁻⁴`**: `≤ 10⁻¹⁸` for `0 ≤ t ≤ 10`, `0 ≤ F ≤ 100`. -/
lemma lindebergErr_le {t F : ℝ} (ht : 0 ≤ t) (ht10 : t ≤ 10) (hF : 0 ≤ F) (hF100 : F ≤ 100) :
    lindebergErr (1 / 10 ^ 4) t F ≤ 1 / 10 ^ 18 := by
  have he := exp_neg_exp_twenty_half_le
  have he0 := Real.exp_pos (-(Real.exp 20 / 2))
  have hx : Real.exp (-(t * -(1 / 10 ^ 4))) ≤ 2 :=
    exp_le_of_taylor (f := 1 / 1000) 0 1 (by norm_num) (by push_cast; nlinarith) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  have hx0 := Real.exp_pos (-(t * -(1 / 10 ^ 4)))
  have hP : (105 / 2 / (1 / 10 ^ 4) / (1 / 10 ^ 4) / (1 / 10 ^ 4)
      + 3 * t * (105 / 4 / (1 / 10 ^ 4) / (1 / 10 ^ 4)) + 3 * t ^ 2 * (35 / 16 / (1 / 10 ^ 4))
      + t ^ 3 : ℝ) ≤ 6 * 10 ^ 13 := by
    have h2 : t ^ 2 ≤ 100 := by nlinarith
    have h3 : t ^ 3 ≤ 1000 := by nlinarith
    norm_num
    nlinarith
  have hP0 : (0 : ℝ) ≤ 105 / 2 / (1 / 10 ^ 4) / (1 / 10 ^ 4) / (1 / 10 ^ 4)
      + 3 * t * (105 / 4 / (1 / 10 ^ 4) / (1 / 10 ^ 4)) + 3 * t ^ 2 * (35 / 16 / (1 / 10 ^ 4))
      + t ^ 3 := by positivity
  have hM : lindM (1 / 10 ^ 4) (-(1 / 10 ^ 4)) t 3 ≤ 12 * 10 ^ 13 := by
    simp only [lindM]
    calc _ ≤ 6 * 10 ^ 13 * 2 := mul_le_mul hP hx hx0.le (by norm_num)
      _ = 12 * 10 ^ 13 := by norm_num
  have hM0 : 0 ≤ lindM (1 / 10 ^ 4) (-(1 / 10 ^ 4)) t 3 := by
    simp only [lindM]
    positivity
  have hFM : F * lindM (1 / 10 ^ 4) (-(1 / 10 ^ 4)) t 3 ≤ 100 * (12 * 10 ^ 13) :=
    mul_le_mul hF100 hM hM0 (by norm_num)
  rw [lindebergErr]
  have hA : (105 / 2 / (1 / 10 ^ 4) / (1 / 10 ^ 4) / (1 / 10 ^ 4)
      + F * lindM (1 / 10 ^ 4) (-(1 / 10 ^ 4)) t 3 : ℝ) ≤ 2 * 10 ^ 16 := by
    norm_num at hFM ⊢
    linarith
  have hA0 : (0 : ℝ) ≤ 105 / 2 / (1 / 10 ^ 4) / (1 / 10 ^ 4) / (1 / 10 ^ 4)
      + F * lindM (1 / 10 ^ 4) (-(1 / 10 ^ 4)) t 3 := by positivity
  calc _ ≤ 2 * 10 ^ 16 * (105 * (1 / 10 ^ 40)) :=
        mul_le_mul hA (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity) (by norm_num)
    _ ≤ 1 / 10 ^ 18 := by norm_num

/-- `villeErr t ≤ 10⁻³⁰` for `0 ≤ t ≤ 10`. -/
lemma villeErr_le {t : ℝ} (ht : 0 ≤ t) (ht10 : t ≤ 10) : villeErr t ≤ 1 / 10 ^ 30 := by
  have he := exp_neg_exp_twenty_half_le
  have he0 := Real.exp_pos (-(Real.exp 20 / 2))
  have h1 : 14 * t + t ^ 2 / 2 ≤ 190 := by nlinarith
  have h0 : 0 ≤ 14 * t + t ^ 2 / 2 := by positivity
  rw [villeErr]
  calc _ ≤ 190 * (3 * (1 / 10 ^ 40)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity) (by norm_num)
    _ ≤ 1 / 10 ^ 30 := by norm_num

/-! ### The Ville factor by rationals -/

/-- `c3Scale η z ≤ max(s·z', S_hi·z')` for `z ≤ z'`, `s ≤ c3Slo η`, `η ≥ 0`. -/
lemma c3Scale_le_of {η s z z' : ℝ} (hη : 0 ≤ η) (hs : s ≤ c3Slo η) (hz : z ≤ z') :
    c3Scale η z ≤ max (s * z') (c3Shi * z') := by
  refine (c3Scale_mono hz).trans ?_
  rw [c3Scale]
  refine max_le ?_ (le_max_right _ _)
  rcases le_total 0 z' with h | h
  · exact (mul_le_mul_of_nonneg_right (c3Slo_le_c3Shi hη) h).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hs h).trans (le_max_left _ _)

/-- **One step of the Ville sum by rationals**: with `0 ≤ y ≤ Y`, `s ≤ c3Slo η` and
`e^{-2} ∈ [e₀, e₁]`, the exponent `max(0, c3Step)` is at most the same expression with
`y²e^{-2i}` replaced by `Y²e₁^i`, `c3Slo η` by `s` and `e^{-2}` by `e₀`. -/
lemma max_zero_c3Step_le_rat {q t η y Y s e₀ e₁ : ℝ} (i : ℕ) (ht : 0 ≤ t) (hη : 0 ≤ η)
    (hy0 : 0 ≤ y) (hy : y ≤ Y) (hs : s ≤ c3Slo η) (he₀ : e₀ ≤ Real.exp (-2))
    (he₁ : Real.exp (-2) ≤ e₁) :
    max 0 (c3Step q t η y i) ≤ max 0 (min
      (max (s * (t * (Y ^ 2 * e₁ ^ i + (t / 2 - (2 * q - 1 / 2)))))
        (c3Shi * (t * (Y ^ 2 * e₁ ^ i + (t / 2 - (2 * q - 1 / 2))))))
      (max (s * (t * (t / 2 - (2 * q - 1 / 2)))) (c3Shi * (t * (t / 2 - (2 * q - 1 / 2))))
        + 2 * t * ((1 - e₀) * (Y ^ 2 * e₁ ^ i) / 4 + (1 / 150000 + 7.43 / 10 ^ 8)))) := by
  have hY0 : 0 ≤ Y := hy0.trans hy
  have hE : y ^ 2 * Real.exp (-(2 * (i : ℝ))) ≤ Y ^ 2 * e₁ ^ i := by
    rw [exp_neg_two_mul_nat]
    exact mul_le_mul (pow_le_pow_left₀ hy0 hy 2) (pow_le_pow_left₀ (Real.exp_pos _).le he₁ i)
      (by positivity) (by positivity)
  have he2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  refine max_le_max le_rfl (min_le_min ?_ ?_)
  · exact c3Scale_le_of hη hs (mul_le_mul_of_nonneg_left (by linarith) ht)
  · refine add_le_add (c3Scale_le_of hη hs le_rfl) (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have h1 : (1 - Real.exp (-2)) * y ^ 2 * Real.exp (-(2 * (i : ℝ)))
        = (1 - Real.exp (-2)) * (y ^ 2 * Real.exp (-(2 * (i : ℝ)))) := by ring
    have h3 : (1 - Real.exp (-2)) * (y ^ 2 * Real.exp (-(2 * (i : ℝ))))
        ≤ (1 - e₀) * (Y ^ 2 * e₁ ^ i) :=
      mul_le_mul (by linarith) hE (by positivity) (by linarith)
    rw [h1]
    linarith

/-- **The Ville sum by rationals** (`RMF.max_zero_c3Step_le_rat` step by step). -/
lemma villeSum_le_rat {q t η y Y s e₀ e₁ : ℝ} (K : ℕ) (ht : 0 ≤ t) (hη : 0 ≤ η) (hy0 : 0 ≤ y)
    (hy : y ≤ Y) (hs : s ≤ c3Slo η) (he₀ : e₀ ≤ Real.exp (-2)) (he₁ : Real.exp (-2) ≤ e₁) :
    villeSum q t η y K ≤ ∑ i ∈ Finset.Ico 1 K, max 0 (min
      (max (s * (t * (Y ^ 2 * e₁ ^ i + (t / 2 - (2 * q - 1 / 2)))))
        (c3Shi * (t * (Y ^ 2 * e₁ ^ i + (t / 2 - (2 * q - 1 / 2))))))
      (max (s * (t * (t / 2 - (2 * q - 1 / 2)))) (c3Shi * (t * (t / 2 - (2 * q - 1 / 2))))
        + 2 * t * ((1 - e₀) * (Y ^ 2 * e₁ ^ i) / 4 + (1 / 150000 + 7.43 / 10 ^ 8)))) :=
  Finset.sum_le_sum fun i _ => max_zero_c3Step_le_rat i ht hη hy0 hy hs he₀ he₁

lemma villeFactor_nonneg (q t η y : ℝ) (K : ℕ) : 0 ≤ villeFactor q t η y K :=
  (Real.exp_pos _).le

/-- **The Ville factor from a bound on its sum**: `villeFactor ≤ B` from `villeSum ≤ S` and
`e^{S + 10⁻³⁰} ≤ B`, for `0 ≤ t ≤ 10`. -/
lemma villeFactor_le_of_villeSum_le {q t η y S B : ℝ} {K : ℕ} (ht : 0 ≤ t) (ht10 : t ≤ 10)
    (hS : villeSum q t η y K ≤ S) (hB : Real.exp (S + 1 / 10 ^ 30) ≤ B) :
    villeFactor q t η y K ≤ B := by
  refine le_trans ?_ hB
  rw [villeFactor]
  exact Real.exp_le_exp.2 (add_le_add hS (villeErr_le ht ht10))

/-- **The steps past `i₀` vanish**: if `y²e^{-2i₀} + t/2 - (2q - ½) ≤ 0`, then
`max(0, c3Step q t η y i) = 0` for every `i ≥ i₀`. -/
lemma max_zero_c3Step_eq_zero {q t η y : ℝ} {i₀ i : ℕ} (ht : 0 ≤ t)
    (hi₀ : y ^ 2 * Real.exp (-(2 * (i₀ : ℝ))) + (t / 2 - (2 * q - 1 / 2)) ≤ 0) (hi : i₀ ≤ i) :
    max 0 (c3Step q t η y i) = 0 := by
  refine max_eq_left ?_
  have hexp : Real.exp (-(2 * (i : ℝ))) ≤ Real.exp (-(2 * (i₀ : ℝ))) := by
    have : (i₀ : ℝ) ≤ i := by exact_mod_cast hi
    exact Real.exp_le_exp.2 (by linarith)
  have hz : t * (y ^ 2 * Real.exp (-(2 * (i : ℝ))) + (t / 2 - (2 * q - 1 / 2))) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos ht ?_
    have := mul_le_mul_of_nonneg_left hexp (sq_nonneg y)
    linarith
  have hS0 : 0 ≤ c3Slo η := (c3Slo_pos η).le
  have hS1 : (0 : ℝ) ≤ c3Shi := by norm_num [c3Shi]
  refine (min_le_left _ _).trans ?_
  rw [c3Scale]
  exact max_le (mul_nonpos_of_nonneg_of_nonpos hS0 hz) (mul_nonpos_of_nonneg_of_nonpos hS1 hz)

/-- **The Ville factor truncated, uniform in the ladder's length**: if
`y²e^{-2i₀} + t/2 - (2q - ½) ≤ 0`, the steps from `i₀` on contribute nothing, so
`villeFactor q t η y K ≤ villeFactor q t η y i₀` for every `K`. -/
theorem villeFactor_le_trunc {q t η y : ℝ} {i₀ : ℕ} (ht : 0 ≤ t)
    (hi₀ : y ^ 2 * Real.exp (-(2 * (i₀ : ℝ))) + (t / 2 - (2 * q - 1 / 2)) ≤ 0) (K : ℕ) :
    villeFactor q t η y K ≤ villeFactor q t η y i₀ := by
  classical
  rw [villeFactor, villeFactor]
  refine Real.exp_le_exp.2 (add_le_add ?_ le_rfl)
  rw [villeSum, villeSum]
  have hfilt : ∑ i ∈ (Finset.Ico 1 K).filter (· < i₀), max 0 (c3Step q t η y i)
      = ∑ i ∈ Finset.Ico 1 K, max 0 (c3Step q t η y i) := by
    refine Finset.sum_filter_of_ne fun i _ hne => ?_
    by_contra hlt
    exact hne (max_zero_c3Step_eq_zero ht hi₀ (not_lt.1 hlt))
  rw [← hfilt]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => le_max_left _ _
  rw [Finset.mem_filter, Finset.mem_Ico] at hi
  rw [Finset.mem_Ico]
  exact ⟨hi.1.1, hi.2⟩

/-- The truncation condition by rationals: `Y²e₁^{i₀} + t/2 - (2q - ½) ≤ 0` with
`0 ≤ y ≤ Y`, `e^{-2} ≤ e₁`. -/
lemma trunc_cond_of_rat {q t y Y e₁ : ℝ} {i₀ : ℕ} (hy0 : 0 ≤ y) (hy : y ≤ Y)
    (he₁ : Real.exp (-2) ≤ e₁) (h : Y ^ 2 * e₁ ^ i₀ + (t / 2 - (2 * q - 1 / 2)) ≤ 0) :
    y ^ 2 * Real.exp (-(2 * (i₀ : ℝ))) + (t / 2 - (2 * q - 1 / 2)) ≤ 0 := by
  have hE : y ^ 2 * Real.exp (-(2 * (i₀ : ℝ))) ≤ Y ^ 2 * e₁ ^ i₀ := by
    rw [exp_neg_two_mul_nat]
    exact mul_le_mul (pow_le_pow_left₀ hy0 hy 2) (pow_le_pow_left₀ (Real.exp_pos _).le he₁ i₀)
      (by positivity) (sq_nonneg _ |>.trans (pow_le_pow_left₀ hy0 hy 2))
  linarith

/-! ### One row: `c ≤ c3Val` from rational bounds -/

/-- `z ≤ x/√V` from `m ≤ x`, `V ∈ [v₁, v₂]` and a sign-split rational condition. -/
lemma le_div_sqrt_of_cases {z m x V v₁ v₂ : ℝ} (hV : 0 < V) (hV₁ : v₁ ≤ V) (hV₂ : V ≤ v₂)
    (hmx : m ≤ x)
    (h : (z ≤ 0 ∧ 0 ≤ m) ∨ (z ≤ 0 ∧ m ≤ 0 ∧ m ^ 2 ≤ z ^ 2 * v₁)
      ∨ (0 ≤ z ∧ 0 ≤ m ∧ z ^ 2 * v₂ ≤ m ^ 2)) :
    z ≤ x / √V := by
  have hs : 0 < √V := Real.sqrt_pos.2 hV
  have hs2 : √V ^ 2 = V := Real.sq_sqrt hV.le
  rw [le_div_iff₀ hs]
  refine le_trans ?_ hmx
  rcases h with ⟨hz, hm⟩ | ⟨hz, hm, hq⟩ | ⟨hz, hm, hq⟩
  · have := mul_nonpos_of_nonpos_of_nonneg hz hs.le
    linarith
  · have hzs : z * √V ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz hs.le
    have h1 : m ^ 2 ≤ (z * √V) ^ 2 := by
      rw [mul_pow, hs2]
      exact hq.trans (mul_le_mul_of_nonneg_left hV₁ (sq_nonneg z))
    have h2 := sq_le_sq.1 h1
    rw [abs_of_nonpos hm, abs_of_nonpos hzs] at h2
    linarith
  · have hzs : 0 ≤ z * √V := mul_nonneg hz hs.le
    have h1 : (z * √V) ^ 2 ≤ m ^ 2 := by
      rw [mul_pow, hs2]
      exact (mul_le_mul_of_nonneg_left hV₂ (sq_nonneg z)).trans hq
    have h2 := sq_le_sq.1 h1
    rw [abs_of_nonneg hm, abs_of_nonneg hzs] at h2
    exact h2

/-- `x/√V ≤ z` from `x ≤ M`, `V ∈ [v₁, v₂]` and a sign-split rational condition. -/
lemma div_sqrt_le_of_cases {z M x V v₁ v₂ : ℝ} (hV : 0 < V) (hV₁ : v₁ ≤ V) (hV₂ : V ≤ v₂)
    (hxM : x ≤ M)
    (h : (0 ≤ z ∧ M ≤ 0) ∨ (z ≤ 0 ∧ M ≤ 0 ∧ z ^ 2 * v₂ ≤ M ^ 2)
      ∨ (0 ≤ z ∧ 0 ≤ M ∧ M ^ 2 ≤ z ^ 2 * v₁)) :
    x / √V ≤ z := by
  have hs : 0 < √V := Real.sqrt_pos.2 hV
  have hs2 : √V ^ 2 = V := Real.sq_sqrt hV.le
  rw [div_le_iff₀ hs]
  refine le_trans hxM ?_
  rcases h with ⟨hz, hM⟩ | ⟨hz, hM, hq⟩ | ⟨hz, hM, hq⟩
  · have := mul_nonneg hz hs.le
    linarith
  · have hzs : z * √V ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz hs.le
    have h1 : (z * √V) ^ 2 ≤ M ^ 2 := by
      rw [mul_pow, hs2]
      exact (mul_le_mul_of_nonneg_left hV₂ (sq_nonneg z)).trans hq
    have h2 := sq_le_sq.1 h1
    rw [abs_of_nonpos hM, abs_of_nonpos hzs] at h2
    linarith
  · have hzs : 0 ≤ z * √V := mul_nonneg hz hs.le
    have h1 : M ^ 2 ≤ (z * √V) ^ 2 := by
      rw [mul_pow, hs2]
      exact hq.trans (mul_le_mul_of_nonneg_left hV₁ (sq_nonneg z))
    have h2 := sq_le_sq.1 h1
    rw [abs_of_nonneg hM, abs_of_nonneg hzs] at h2
    exact h2

/-- **The top block's mean from below by rationals**, at `η = 1/200`: `ml ≤ topMuLo q (1/200) ϑ`
from `A_lo ≤ cosExpAnti(-ϑ) - cosExpAnti(-1-ϑ)` and two rational side conditions (one for each
sign of `2q - ½`). -/
lemma topMuLo_ge_of {q ϑ Alo ml : ℝ} (hAlo : Alo ≤ cosExpAnti (-ϑ) - cosExpAnti (-1 - ϑ))
    (h₁ : ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
      ≤ (2 * q - 1 / 2) * 0.9900432333)
    (h₂ : ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
      ≤ (2 * q - 1 / 2) * (1 + 1 / 150000)) :
    ml ≤ topMuLo q (1 / 200) ϑ := by
  obtain ⟨hS1, hS2⟩ := c3Slo_two_hundredth_mem
  have hE := topEps_le
  have hmin : min ((2 * q - 1 / 2) * 0.9900432333) ((2 * q - 1 / 2) * (1 + 1 / 150000))
      ≤ min ((2 * q - 1 / 2) * c3Slo (1 / 200)) ((2 * q - 1 / 2) * c3Shi) := by
    rcases le_total 0 (2 * q - 1 / 2) with ha | ha
    · refine le_min ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hS1 ha))
        ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left (by norm_num [c3Shi]) ha))
    · refine le_min ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left ?_ ha))
        ((min_le_right _ _).trans (le_of_eq (by rw [c3Shi])))
      linarith
  have h3 := le_min h₁ h₂
  have h4 : ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
      ≤ min ((2 * q - 1 / 2) * c3Slo (1 / 200)) ((2 * q - 1 / 2) * c3Shi) := h3.trans hmin
  rw [topMuLo, topDhi, topBlo, c3Shi]
  rw [c3Shi] at h4
  linarith

/-- **The top block's mean from above by rationals**, at `η = 1/200`: `topMuHi q (1/200) ϑ ≤ mh`
from `cosExpAnti(-ϑ) - cosExpAnti(-1-ϑ) ≤ A_hi` and two rational side conditions. -/
lemma topMuHi_le_of {q ϑ Ahi mh : ℝ} (hAhi : cosExpAnti (-ϑ) - cosExpAnti (-1 - ϑ) ≤ Ahi)
    (hD : 0 ≤ (1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8)
    (h₁ : (2 * q - 1 / 2) * 0.9900432333
        - 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
        + 14 * (2 / 10 ^ 40) ≤ mh)
    (h₂ : (2 * q - 1 / 2) * (1 + 1 / 150000)
        - 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
        + 14 * (2 / 10 ^ 40) ≤ mh) :
    topMuHi q (1 / 200) ϑ ≤ mh := by
  obtain ⟨hS1, hS2⟩ := c3Slo_two_hundredth_mem
  obtain ⟨he1, he2⟩ := exp_neg_two_hundredth_mem
  have hE := topEps_le
  have hmax : max ((2 * q - 1 / 2) * c3Slo (1 / 200)) ((2 * q - 1 / 2) * c3Shi)
      ≤ max ((2 * q - 1 / 2) * 0.9900432333) ((2 * q - 1 / 2) * (1 + 1 / 150000)) := by
    rcases le_total 0 (2 * q - 1 / 2) with ha | ha
    · refine max_le ((mul_le_mul_of_nonneg_left ?_ ha).trans (le_max_right _ _))
        (le_of_eq (by rw [c3Shi]) |>.trans (le_max_right _ _))
      linarith
    · exact max_le ((mul_le_mul_of_nonpos_left hS1 ha).trans (le_max_left _ _))
        ((mul_le_mul_of_nonpos_left (by norm_num [c3Shi]) ha).trans (le_max_left _ _))
  have hB : (1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8
      ≤ (1 - 1 / 150000) - topBhi ϑ - 7.43 / 10 ^ 8 := by
    rw [topBhi]
    linarith
  have hDlo : 0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8)
      ≤ topDlo (1 / 200) ϑ := by
    rw [topDlo]
    exact mul_le_mul he1 hB hD (by linarith)
  have h3 : max ((2 * q - 1 / 2) * 0.9900432333) ((2 * q - 1 / 2) * (1 + 1 / 150000))
      ≤ mh + 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
        - 14 * (2 / 10 ^ 40) :=
    max_le (by linarith) (by linarith)
  rw [topMuHi]
  linarith

/-- **One row of the certificate**: `c ≤ c3Val q_lo q_hi (1/200) ϑ_lo ϑ_hi t 10⁻⁴ F` from
rational bounds: the cosine anchors `A_lo`, `A_hi`; the mean's ends `ml ≤ topMuLo`,
`topMuHi ≤ mh` (`RMF.topMuLo_ge_of`, `RMF.topMuHi_le_of`); `z₁ ≤ (ml - δ)/√V`,
`(mh + δ - tV_lo)/√V ≤ z₂` over the variance's range; `Φ(z₁) ≥ p₁`, `Φ(z₂) ≤ p₂`;
`e^X ≤ E_b` with `X ≥ -t·ml + t²V_hi/2`; `F ≤ F_b ≤ 100`; and `c ≤ p₁ - F_b E_b p₂ - 10⁻¹⁸`. -/
theorem le_c3Val_of {q_lo q_hi ϑ_lo ϑ_hi t F Alo Ahi ml mh z₁ z₂ p₁ p₂ X Eb Fb c : ℝ}
    (ht : 0 ≤ t) (ht10 : t ≤ 10)
    (hAlo : Alo ≤ cosExpAnti (-ϑ_lo) - cosExpAnti (-1 - ϑ_lo))
    (hAhi : cosExpAnti (-ϑ_hi) - cosExpAnti (-1 - ϑ_hi) ≤ Ahi)
    (hml : ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
        ≤ (2 * q_lo - 1 / 2) * 0.9900432333
      ∧ ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
        ≤ (2 * q_lo - 1 / 2) * (1 + 1 / 150000))
    (hD : 0 ≤ (1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8)
    (hmh : (2 * q_hi - 1 / 2) * 0.9900432333
          - 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
          + 14 * (2 / 10 ^ 40) ≤ mh
      ∧ (2 * q_hi - 1 / 2) * (1 + 1 / 150000)
          - 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
          + 14 * (2 / 10 ^ 40) ≤ mh)
    (hz₁ : (z₁ ≤ 0 ∧ 0 ≤ ml - 1 / 10 ^ 4)
      ∨ (z₁ ≤ 0 ∧ ml - 1 / 10 ^ 4 ≤ 0 ∧ (ml - 1 / 10 ^ 4) ^ 2 ≤ z₁ ^ 2 * 0.9900432332)
      ∨ (0 ≤ z₁ ∧ 0 ≤ ml - 1 / 10 ^ 4 ∧ z₁ ^ 2 * 1.0000066667 ≤ (ml - 1 / 10 ^ 4) ^ 2))
    (hz₂ : (0 ≤ z₂ ∧ mh + 1 / 10 ^ 4 - t * 0.9900432332 ≤ 0)
      ∨ (z₂ ≤ 0 ∧ mh + 1 / 10 ^ 4 - t * 0.9900432332 ≤ 0
        ∧ z₂ ^ 2 * 1.0000066667 ≤ (mh + 1 / 10 ^ 4 - t * 0.9900432332) ^ 2)
      ∨ (0 ≤ z₂ ∧ 0 ≤ mh + 1 / 10 ^ 4 - t * 0.9900432332
        ∧ (mh + 1 / 10 ^ 4 - t * 0.9900432332) ^ 2 ≤ z₂ ^ 2 * 0.9900432332))
    (hp₁ : p₁ ≤ normCDF z₁) (hp₂ : normCDF z₂ ≤ p₂)
    (hX : -(t * ml) + t ^ 2 * 1.0000066667 / 2 ≤ X) (hE : Real.exp X ≤ Eb)
    (hF0 : 0 ≤ F) (hF : F ≤ Fb) (hFb : Fb ≤ 100)
    (hc : c ≤ p₁ - Fb * (Eb * p₂) - 1 / 10 ^ 18) :
    c ≤ c3Val q_lo q_hi (1 / 200) ϑ_lo ϑ_hi t (1 / 10 ^ 4) F := by
  obtain ⟨hVL1, hVL2⟩ := topVLo_two_hundredth_mem
  obtain ⟨hVH1, hVH2⟩ := topVHi_mem
  have hVL0 : 0 < topVLo (1 / 200) := by linarith
  have hVH0 : 0 < topVHi := by linarith
  have hμlo : ml ≤ topMuLo q_lo (1 / 200) ϑ_lo := topMuLo_ge_of hAlo hml.1 hml.2
  have hμhi : topMuHi q_hi (1 / 200) ϑ_hi ≤ mh := topMuHi_le_of hAhi hD hmh.1 hmh.2
  -- the first term
  have hm : ml - 1 / 10 ^ 4 ≤ topMuLo q_lo (1 / 200) ϑ_lo - 1 / 10 ^ 4 := by linarith
  have h1 : p₁ ≤ min (normCDF ((topMuLo q_lo (1 / 200) ϑ_lo - 1 / 10 ^ 4) / √(topVLo (1 / 200))))
      (normCDF ((topMuLo q_lo (1 / 200) ϑ_lo - 1 / 10 ^ 4) / √topVHi)) :=
    le_min (hp₁.trans (normCDF_mono (le_div_sqrt_of_cases hVL0 hVL1 (by linarith) hm hz₁)))
      (hp₁.trans (normCDF_mono (le_div_sqrt_of_cases hVH0 (by linarith) hVH2 hm hz₁)))
  -- the second term
  have hM : topMuHi q_hi (1 / 200) ϑ_hi + 1 / 10 ^ 4 - t * topVLo (1 / 200)
      ≤ mh + 1 / 10 ^ 4 - t * 0.9900432332 := by
    have := mul_le_mul_of_nonneg_left hVL1 ht
    linarith
  have h2 : max (normCDF ((topMuHi q_hi (1 / 200) ϑ_hi + 1 / 10 ^ 4 - t * topVLo (1 / 200))
        / √(topVLo (1 / 200))))
      (normCDF ((topMuHi q_hi (1 / 200) ϑ_hi + 1 / 10 ^ 4 - t * topVLo (1 / 200)) / √topVHi))
      ≤ p₂ :=
    max_le ((normCDF_mono (div_sqrt_le_of_cases hVL0 hVL1 (by linarith) hM hz₂)).trans hp₂)
      ((normCDF_mono (div_sqrt_le_of_cases hVH0 (by linarith) hVH2 hM hz₂)).trans hp₂)
  have h3 : Real.exp (-(t * topMuLo q_lo (1 / 200) ϑ_lo) + t ^ 2 * topVHi / 2) ≤ Eb := by
    refine le_trans (Real.exp_le_exp.2 ?_) hE
    have ha := mul_le_mul_of_nonneg_left hμlo ht
    have hb := mul_le_mul_of_nonneg_left hVH2 (sq_nonneg t)
    linarith
  have hmax0 : 0 ≤ max (normCDF ((topMuHi q_hi (1 / 200) ϑ_hi + 1 / 10 ^ 4
      - t * topVLo (1 / 200)) / √(topVLo (1 / 200))))
      (normCDF ((topMuHi q_hi (1 / 200) ϑ_hi + 1 / 10 ^ 4 - t * topVLo (1 / 200)) / √topVHi)) :=
    (normCDF_nonneg _).trans (le_max_left _ _)
  have hEb0 : 0 ≤ Eb := (Real.exp_pos _).le.trans hE
  have h4 := mul_le_mul hF (mul_le_mul h3 h2 hmax0 hEb0)
    (mul_nonneg (Real.exp_pos _).le hmax0) (hF0.trans hF)
  have h5 := lindebergErr_le ht ht10 hF0 (hF.trans hFb)
  rw [c3Val]
  linarith

/-! ### The rows' compact forms (one `norm_num` per side condition) -/

/-- `RMF.exp_le_of_taylor` with its numeric side conditions bundled. -/
lemma exp_le_taylor_num {x f B : ℝ} (k n : ℕ)
    (h : 0 < n ∧ x ≤ k + f ∧ 0 ≤ f ∧ f ≤ 1 ∧ 2.7182818286 ^ k * ((∑ m ∈ Finset.range n,
      f ^ m / m.factorial) + f ^ n * (n + 1) / (n.factorial * n)) ≤ B) : Real.exp x ≤ B :=
  exp_le_of_taylor k n h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **The Ville factor at `η = 1/200`, `y = e^{-ϑ}`, by rationals**: from `e^{-ϑ} ≤ Y`, the
rational form of `RMF.villeSum_le_rat` at `s = 0.9900432333`, `e^{-2} ∈ [0.1353352832,
0.1353352833]` bounded by `S`, and `e^{S + 10⁻³⁰} ≤ B`. -/
lemma c3VilleFactor_le {q t ϑ Y S B : ℝ} (K : ℕ) (ht : 0 ≤ t ∧ t ≤ 10)
    (hY : Real.exp (-ϑ) ≤ Y)
    (hS : ∑ i ∈ Finset.Ico 1 K, max 0 (min
      (max (0.9900432333 * (t * (Y ^ 2 * 0.1353352833 ^ i + (t / 2 - (2 * q - 1 / 2)))))
        (c3Shi * (t * (Y ^ 2 * 0.1353352833 ^ i + (t / 2 - (2 * q - 1 / 2))))))
      (max (0.9900432333 * (t * (t / 2 - (2 * q - 1 / 2))))
          (c3Shi * (t * (t / 2 - (2 * q - 1 / 2))))
        + 2 * t * ((1 - 0.1353352832) * (Y ^ 2 * 0.1353352833 ^ i) / 4
          + (1 / 150000 + 7.43 / 10 ^ 8)))) ≤ S)
    (hB : Real.exp (S + 1 / 10 ^ 30) ≤ B) :
    villeFactor q t (1 / 200) (Real.exp (-ϑ)) K ≤ B :=
  villeFactor_le_of_villeSum_le ht.1 ht.2 ((villeSum_le_rat K ht.1 (by norm_num)
    (Real.exp_pos _).le hY c3Slo_two_hundredth_mem.1 exp_neg_two_mem_sharp.1
    exp_neg_two_mem_sharp.2).trans hS) hB

/-- **One row, compact**: `RMF.le_c3Val_of` with every rational side condition in one
conjunction. -/
theorem le_c3Val_of_num {q_lo q_hi ϑ_lo ϑ_hi t F Alo Ahi ml mh z₁ z₂ p₁ p₂ X Eb Fb c : ℝ}
    (hAlo : Alo ≤ cosExpAnti (-ϑ_lo) - cosExpAnti (-1 - ϑ_lo))
    (hAhi : cosExpAnti (-ϑ_hi) - cosExpAnti (-1 - ϑ_hi) ≤ Ahi)
    (hp₁ : p₁ ≤ normCDF z₁) (hp₂ : normCDF z₂ ≤ p₂) (hE : Real.exp X ≤ Eb) (hF0 : 0 ≤ F)
    (hF : F ≤ Fb)
    (hnum : (0 ≤ t ∧ t ≤ 10)
      ∧ (ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
          ≤ (2 * q_lo - 1 / 2) * 0.9900432333
        ∧ ml + 2 * ((1 + 1 / 150000) - (Alo - 1 / 10 ^ 6) + 7.43 / 10 ^ 8) + 14 * (2 / 10 ^ 40)
          ≤ (2 * q_lo - 1 / 2) * (1 + 1 / 150000))
      ∧ 0 ≤ (1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8
      ∧ ((2 * q_hi - 1 / 2) * 0.9900432333
            - 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
            + 14 * (2 / 10 ^ 40) ≤ mh
        ∧ (2 * q_hi - 1 / 2) * (1 + 1 / 150000)
            - 2 * (0.9900498337 * ((1 - 1 / 150000) - (Ahi + 1 / 10 ^ 6) - 7.43 / 10 ^ 8))
            + 14 * (2 / 10 ^ 40) ≤ mh)
      ∧ ((z₁ ≤ 0 ∧ 0 ≤ ml - 1 / 10 ^ 4)
        ∨ (z₁ ≤ 0 ∧ ml - 1 / 10 ^ 4 ≤ 0 ∧ (ml - 1 / 10 ^ 4) ^ 2 ≤ z₁ ^ 2 * 0.9900432332)
        ∨ (0 ≤ z₁ ∧ 0 ≤ ml - 1 / 10 ^ 4 ∧ z₁ ^ 2 * 1.0000066667 ≤ (ml - 1 / 10 ^ 4) ^ 2))
      ∧ ((0 ≤ z₂ ∧ mh + 1 / 10 ^ 4 - t * 0.9900432332 ≤ 0)
        ∨ (z₂ ≤ 0 ∧ mh + 1 / 10 ^ 4 - t * 0.9900432332 ≤ 0
          ∧ z₂ ^ 2 * 1.0000066667 ≤ (mh + 1 / 10 ^ 4 - t * 0.9900432332) ^ 2)
        ∨ (0 ≤ z₂ ∧ 0 ≤ mh + 1 / 10 ^ 4 - t * 0.9900432332
          ∧ (mh + 1 / 10 ^ 4 - t * 0.9900432332) ^ 2 ≤ z₂ ^ 2 * 0.9900432332))
      ∧ -(t * ml) + t ^ 2 * 1.0000066667 / 2 ≤ X
      ∧ Fb ≤ 100
      ∧ c ≤ p₁ - Fb * (Eb * p₂) - 1 / 10 ^ 18) :
    c ≤ c3Val q_lo q_hi (1 / 200) ϑ_lo ϑ_hi t (1 / 10 ^ 4) F := by
  obtain ⟨⟨ht, ht10⟩, hml, hD, hmh, hz₁, hz₂, hX, hFb, hc⟩ := hnum
  exact le_c3Val_of ht ht10 hAlo hAhi hml hD hmh hz₁ hz₂ hp₁ hp₂ hX hE hF0 hF hFb hc

/-! ### Cells -/

/-- **A cell's certificate** at `η = 1/200`, `δ = 10⁻⁴`: on the cell `[ϑ_lo, ϑ_hi]` of the
`q`-interval `[q_lo, q_hi]` there are `t ≥ 0` and one Ville bound `F` serving every ladder
length `K` with `Kok K`, and `c ≤ c3Val q_lo q_hi (1/200) ϑ_lo ϑ_hi t 10⁻⁴ F`. -/
def C3CellCert (q_lo q_hi ϑ_lo ϑ_hi c : ℝ) (Kok : ℕ → Prop) : Prop :=
  ∃ t F : ℝ, 0 ≤ t ∧ (∀ K, Kok K → villeFactor q_lo t (1 / 200) (Real.exp (-ϑ_lo)) K ≤ F)
    ∧ c ≤ c3Val q_lo q_hi (1 / 200) ϑ_lo ϑ_hi t (1 / 10 ^ 4) F

/-- A certificate for a larger `c` and more ladder lengths serves a smaller `c` and fewer. -/
theorem C3CellCert.mono {q_lo q_hi ϑ_lo ϑ_hi c c' : ℝ} {Kok Kok' : ℕ → Prop}
    (h : C3CellCert q_lo q_hi ϑ_lo ϑ_hi c Kok) (hc : c' ≤ c) (hK : ∀ K, Kok' K → Kok K) :
    C3CellCert q_lo q_hi ϑ_lo ϑ_hi c' Kok' := by
  obtain ⟨t, F, ht, hF, hc'⟩ := h
  exact ⟨t, F, ht, fun K hK' => hF K (hK K hK'), hc.trans hc'⟩

/-- **Bounded ladder lengths**: the Ville factor at `K_b` serves every `K ≤ K_b`. -/
theorem C3CellCert.of_le {q_lo q_hi ϑ_lo ϑ_hi c t : ℝ} {Kb : ℕ} (ht : 0 ≤ t)
    (hc : c ≤ c3Val q_lo q_hi (1 / 200) ϑ_lo ϑ_hi t (1 / 10 ^ 4)
      (villeFactor q_lo t (1 / 200) (Real.exp (-ϑ_lo)) Kb)) :
    C3CellCert q_lo q_hi ϑ_lo ϑ_hi c (· ≤ Kb) :=
  ⟨t, _, ht, fun _ hK => villeFactor_le_of_le ht le_rfl (Real.exp_pos _).le le_rfl hK, hc⟩

/-- **Every ladder length, by truncation**: past a step `i₀` with
`Y²e₁^{i₀} + t/2 - (2q_lo - ½) ≤ 0` (`e^{-ϑ_lo} ≤ Y`, `e^{-2} ≤ e₁`), the Ville factor at `i₀`
serves every ladder length. -/
theorem C3CellCert.of_trunc {q_lo q_hi ϑ_lo ϑ_hi c t Y e₁ : ℝ} {i₀ : ℕ} (ht : 0 ≤ t)
    (hY : Real.exp (-ϑ_lo) ≤ Y) (he₁ : Real.exp (-2) ≤ e₁)
    (hdrift : Y ^ 2 * e₁ ^ i₀ + (t / 2 - (2 * q_lo - 1 / 2)) ≤ 0)
    (hc : c ≤ c3Val q_lo q_hi (1 / 200) ϑ_lo ϑ_hi t (1 / 10 ^ 4)
      (villeFactor q_lo t (1 / 200) (Real.exp (-ϑ_lo)) i₀)) :
    C3CellCert q_lo q_hi ϑ_lo ϑ_hi c (fun _ => True) :=
  ⟨t, _, ht, fun K _ => villeFactor_le_trunc ht
    (trunc_cond_of_rat (Real.exp_pos _).le hY he₁ hdrift) K, hc⟩

section Window

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **(C3)* from a cell's certificate**: for the ladder `[k₁, k)`, `k₁ ≥ 20`, `σe^k ≤ 1/200`,
`q ∈ [q_lo, q_hi] ⊆ [0, 1]`, a ladder length `K = k - k₁` the certificate serves, and a height
in the cell (`e^{-(k+ϑ_hi)} ≤ h ≤ e^{-(k+ϑ_lo)}`, `ϑ_lo ≥ 0`):
`c·E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_of_cellCert (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hk : k₁ < k) {σ : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ 1 / 200) {q q_lo q_hi : ℝ} (hqlo : q_lo ≤ q)
    (hqhi : q ≤ q_hi) (hq0 : 0 ≤ q_lo) (hq1 : q_hi ≤ 1) {ϑ_lo ϑ_hi c : ℝ} {Kok : ℕ → Prop}
    (hcert : C3CellCert q_lo q_hi ϑ_lo ϑ_hi c Kok) (hK : Kok (k - k₁)) (hϑ : 0 ≤ ϑ_lo)
    {h : ℝ} (hh1 : Real.exp (-((k : ℝ) + ϑ_hi)) ≤ h) (hh2 : h ≤ Real.exp (-((k : ℝ) + ϑ_lo))) :
    c * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  obtain ⟨t, F, ht, hF, hc⟩ := hcert
  have hmain := le_setIntegral_halfLadder_twistQ_explicit hX ha hk₁ hk hσ hση (by norm_num)
    hqlo hqhi hq0 hq1 ht (by norm_num : (0 : ℝ) < 1 / 10 ^ 4) hϑ hh1 hh2 (hF _ hK)
  have hE0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  exact (mul_le_mul_of_nonneg_right hc hE0).trans hmain

end Window

/-- **The cells cover the window**: for a partition `ϑ 0 = 0`, `ϑ N = 1` (`N ≥ 1`) and
`h ∈ halfWindow k`, some cell `j < N` has `e^{-(k+ϑ(j+1))} ≤ h ≤ e^{-(k+ϑ j)}`. -/
lemma exists_cell_of_mem_halfWindow {ϑ : ℕ → ℝ} {N : ℕ} (hN0 : 0 < N) (h0 : ϑ 0 = 0)
    (hN : ϑ N = 1) {k : ℕ} {h : ℝ} (hh : h ∈ halfWindow k) :
    ∃ j < N, Real.exp (-((k : ℝ) + ϑ (j + 1))) ≤ h ∧ h ≤ Real.exp (-((k : ℝ) + ϑ j)) := by
  classical
  obtain ⟨hh1, hh2⟩ := hh
  have hpos : 0 < h := (Real.exp_pos _).trans_le hh1
  set x := -Real.log h - k with hx
  have hhx : h = Real.exp (-((k : ℝ) + x)) := by
    rw [hx, show -((k : ℝ) + (-Real.log h - k)) = Real.log h by ring, Real.exp_log hpos]
  have hx0 : 0 ≤ x := by
    have := Real.log_le_log hpos hh2
    rw [Real.log_exp] at this
    rw [hx]
    linarith
  have hx1 : x ≤ 1 := by
    have := Real.log_le_log (Real.exp_pos _) hh1
    rw [Real.log_exp] at this
    rw [hx]
    linarith
  have hex : ∃ j, x ≤ ϑ (j + 1) := ⟨N - 1, by rw [Nat.sub_add_cancel hN0, hN]; exact hx1⟩
  set j := Nat.find hex with hj
  have hjspec : x ≤ ϑ (j + 1) := Nat.find_spec hex
  have hjN : j < N := by
    have := Nat.find_min' hex (show x ≤ ϑ (N - 1 + 1) by rw [Nat.sub_add_cancel hN0, hN]; exact hx1)
    omega
  have hjlo : ϑ j ≤ x := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, h0]
      exact hx0
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rw [Nat.sub_add_cancel hj0] at this
      exact (not_le.1 this).le
  refine ⟨j, hjN, ?_, ?_⟩
  · rw [hhx]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hhx]
    exact Real.exp_le_exp.2 (by linarith)

/-! ### Intervals of `q` -/

/-- **A `q`-interval's certificate** on a partition `ϑ` of the window into `N` cells: every cell
certified at `v` (`RMF.C3CellCert`) for the ladder lengths `K ≤ K_b`, or every `K` when
`K_b = 0`. -/
def C3IntervalCert (ϑ : ℕ → ℝ) (N : ℕ) (q_lo q_hi v : ℝ) (Kb : ℕ) : Prop :=
  ∀ j < N, C3CellCert q_lo q_hi (ϑ j) (ϑ (j + 1)) v (fun K => Kb = 0 ∨ K ≤ Kb)

/-- **The ladder lengths below `½`**, `K_max(q) = max(1, ⌊1/(1 - 2q)⌋)`. -/
noncomputable def c3Kmax (q : ℝ) : ℕ := max 1 ⌊1 / (1 - 2 * q)⌋₊

/-- `K ≤ K_max(q)` for `q < q_hi < ½` gives `K ≤ K_b` once `(K_b + 1)(1 - 2q_hi) ≥ 1`. -/
lemma le_of_le_c3Kmax {q q_hi : ℝ} {K Kb : ℕ} (hq : q < q_hi) (hq_hi : q_hi < 1 / 2)
    (hKb1 : 1 ≤ Kb) (hKb : 1 ≤ ((Kb : ℝ) + 1) * (1 - 2 * q_hi)) (hK : K ≤ c3Kmax q) :
    K ≤ Kb := by
  rcases le_max_iff.1 hK with h | h
  · exact h.trans hKb1
  · have hpos : 0 < 1 - 2 * q := by linarith
    have hfl : (K : ℝ) ≤ 1 / (1 - 2 * q) :=
      (Nat.cast_le.2 h).trans (Nat.floor_le (by positivity))
    have hK1 : (K : ℝ) * (1 - 2 * q) ≤ 1 := by
      rwa [le_div_iff₀ hpos] at hfl
    by_contra hlt
    have hK2 : (Kb : ℝ) + 1 ≤ K := by exact_mod_cast (not_le.1 hlt)
    have h1 : ((Kb : ℝ) + 1) * (1 - 2 * q_hi) < ((Kb : ℝ) + 1) * (1 - 2 * q) :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    have h2 : ((Kb : ℝ) + 1) * (1 - 2 * q) ≤ (K : ℝ) * (1 - 2 * q) :=
      mul_le_mul_of_nonneg_right hK2 hpos.le
    linarith

section IntervalWindow

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **(C3)* from a `q`-interval's certificate**, for every height of the window: with the
partition `ϑ 0 = 0`, `ϑ N = 1`, `ϑ ≥ 0`, and a ladder length the certificate serves. -/
theorem le_setIntegral_halfLadder_twistQ_of_intervalCert (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hk : k₁ < k) {σ : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ 1 / 200) {q q_lo q_hi v : ℝ} (hqlo : q_lo ≤ q)
    (hqhi : q ≤ q_hi) (hq0 : 0 ≤ q_lo) (hq1 : q_hi ≤ 1) {ϑ : ℕ → ℝ} {N Kb : ℕ} (hN0 : 0 < N)
    (h0 : ϑ 0 = 0) (hN : ϑ N = 1) (hϑ : ∀ j, 0 ≤ ϑ j)
    (hcert : C3IntervalCert ϑ N q_lo q_hi v Kb) (hK : Kb = 0 ∨ k - k₁ ≤ Kb) {h : ℝ}
    (hh : h ∈ halfWindow k) :
    v * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  obtain ⟨j, hj, hh1, hh2⟩ := exists_cell_of_mem_halfWindow hN0 h0 hN hh
  exact le_setIntegral_halfLadder_twistQ_of_cellCert hX ha hk₁ hk hσ hση hqlo hqhi hq0 hq1
    (hcert j hj) hK (hϑ j) hh1 hh2

end IntervalWindow

end RMF
