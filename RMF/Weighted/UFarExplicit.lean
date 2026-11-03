/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UWindowExplicit

/-!
# The far range of `Z` at an exponent `q ≤ ½`

The far range `|t| > e^{-4}` of the damped line integral `Z`, for the bound (U),
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` with `Λ = log log x`.  By Jensen it costs
`(2·1.195e⁴)^q`, which does not decay with `log log x`; (U) needs the chaos there too.

* **Jensen between two powers** (`RMF.integral_rpow_le_rpow_integral_rpow`):
  `E[Z^q] ≤ (E[Z^r])^{q/r}` for `q ≤ r`, so the windows are summed at the fixed exponent `r`
  (`2/3` in (U)) and no `1/q` appears;
* **the far range split at `e^{n-4}`** (`RMF.integral_rpow_lineDiv_far_le_of_two_ranges`), the part
  below cut into windows `[e^{j-4}, e^{j-3}]` (`RMF.integral_rpow_farRange_le_sum_windows`), the
  part above by Jensen;
* **one far window by the weighted chaos** (`RMF.window_far_chaos`) at the floor `105 + j`: the
  cosine input's height condition at height `e^{j-3}` holds there (`RMF.height_floor_far`), so the
  floor grows with the window's height and not with `x`; the level shift is `K_ϑ ≤ e^{2j+102}`;
* **the assembly** (`RMF.integral_rpow_farRange_le_chaos`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The floor at a height -/

/-- `pntFloorConst` is antitone. -/
lemma pntFloorConst_anti {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) : pntFloorConst θ₂ ≤ pntFloorConst θ₁ := by
  unfold pntFloorConst
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have : Real.exp (θ₁ / 10) ≤ Real.exp (θ₂ / 10) := Real.exp_le_exp.2 (by linarith)
  linarith

/-- **The height condition of the far window `j` at the floor `104 + j`**: for `E₀ ≤ 1/10` and
`ϑ ≥ 104 + j`, `(2e^{j-3} + 1)·pntFloorConst ϑ ≤ e^{-2E₀}/200`, from
`pntFloorConst (104 + j) ≤ 10⁻²⁸e^{-j}` (`RMF.pnt_term_le_geometric_floor`). -/
lemma height_floor_far {E₀ ϑ : ℝ} (hE₀1 : E₀ ≤ 1 / 10) (j : ℕ) (hϑ : 104 + (j : ℝ) ≤ ϑ) :
    (2 * Real.exp ((j : ℝ) - 3) + 1) * pntFloorConst ϑ ≤ Real.exp (-(2 * E₀)) / 200 := by
  have h1 : pntFloorConst ϑ ≤ pntFloorConst (104 + j) := pntFloorConst_anti hϑ
  have h2 : pntFloorConst (104 + j) ≤ pntFloorConst 104 * Real.exp (-(j : ℝ)) := by
    have h := pnt_term_le_geometric_floor (θ := 104) le_rfl j
    rw [show (j : ℝ) + 104 = 104 + j by ring] at h
    exact h
  have h3 : pntFloorConst 104 ≤ 1 / 10 ^ 28 := pntFloorConst_le le_rfl
  have h3e : Real.exp (-3) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (3 : ℝ)])
  have hj1 : Real.exp (-(j : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg j))
  have hj : (2 * Real.exp ((j : ℝ) - 3) + 1) * Real.exp (-(j : ℝ)) ≤ 2 := by
    have he : Real.exp ((j : ℝ) - 3) * Real.exp (-(j : ℝ)) = Real.exp (-3) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (2 * Real.exp ((j : ℝ) - 3) + 1) * Real.exp (-(j : ℝ))
        = 2 * (Real.exp ((j : ℝ) - 3) * Real.exp (-(j : ℝ))) + Real.exp (-(j : ℝ)) := by ring
      _ = 2 * Real.exp (-3) + Real.exp (-(j : ℝ)) := by rw [he]
      _ ≤ 2 * (1 / 2) + 1 := by linarith
      _ = 2 := by norm_num
  have hE : (1 / 1000 : ℝ) ≤ Real.exp (-(2 * E₀)) / 200 := by
    have := Real.add_one_le_exp (-(2 * E₀))
    linarith
  have hA0 : 0 ≤ 2 * Real.exp ((j : ℝ) - 3) + 1 := by positivity
  calc (2 * Real.exp ((j : ℝ) - 3) + 1) * pntFloorConst ϑ
      ≤ (2 * Real.exp ((j : ℝ) - 3) + 1) * (pntFloorConst 104 * Real.exp (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) hA0
    _ = pntFloorConst 104 * ((2 * Real.exp ((j : ℝ) - 3) + 1) * Real.exp (-(j : ℝ))) := by ring
    _ ≤ 1 / 10 ^ 28 * 2 := mul_le_mul h3 hj (by positivity) (by norm_num)
    _ ≤ 1 / 1000 := by norm_num
    _ ≤ Real.exp (-(2 * E₀)) / 200 := hE

/-- `∫_{T/e}^{T}(σ²+t²)⁻¹dt ≤ (e - 1)/T` (`RMF.setIntegral_inv_sq_add_sq_mul_exp_window_le` at
`β = 0`). -/
lemma setIntegral_inv_sq_add_sq_window_le (σ : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹) ≤ (Real.exp 1 - 1) / T := by
  have h := setIntegral_inv_sq_add_sq_mul_exp_window_le σ hT (β := 0) le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one, sub_self, add_zero] at h
  exact h

/-! ### One far window -/

/-- **One far window by the weighted chaos at the floor `105 + j`**: for the window
`[e^{j-4}, e^{j-3}]`, `0 ≤ r ≤ 1`, `y ≥ e^99`, `105 + j ≤ ⌊log log y⌋`, `σ log y ≤ E₀ ≤ 1/10`
and the chaos's parameters,

`(2/log y)^r·E[(∫_{e^{j-4}}^{e^{j-3}}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^r]
  ≤ shiftMomentConst 1 C_i (C_b e^{2j+102}) A s λ δ r·(2·1.195(e-1)e^{3-j})^r
    ·(1 + (1-r)√n)^{-r}`,

`n = harperBlockCount (105 + j) y`: the whole product (`z = 0`), its second moment
`≤ 1.195 log y`, the weight `≤ (e-1)/T`, the level shift `K_ϑ = Te^ϑ ≤ e^{2j+102}`; the floor
grows with the height so that the cosine input's height condition holds
(`RMF.height_floor_far`). -/
theorem window_far_chaos (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 10)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) {j y : ℕ} {σ A lam : ℝ} (hσ : 0 < σ) (hy : Real.exp 99 ≤ (y : ℝ))
    (hDy : 105 + j ≤ ⌊Real.log (Real.log y)⌋₊) (hσy : σ * Real.log y ≤ E₀)
    (hNn : N ≤ harperBlockCount (105 + j) y) (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax)
    (hlam : 1 ≤ lam) :
    (2 / Real.log y) ^ r * ∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1)
        (Real.exp ((j : ℝ) - 3)), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ r ∂ν
      ≤ shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
            (radBlockBadConst E₀ βc * Real.exp (2 * (j : ℝ) + 102)) A
            (radAveragedShift E₀ βc Tr κ) lam δ r
          * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ r
          * (1 + (1 - r) * Real.sqrt (harperBlockCount (105 + j) y : ℝ)) ^ (-r) := by
  haveI := hY.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν :=
    hY.isRademacherRMF
  have hLL : (((105 + j : ℕ) : ℕ) : ℝ) ≤ Real.log (Real.log y) :=
    (Nat.le_floor_iff' (by omega)).1 hDy
  have hy1 : (100 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hx1 : (1 : ℝ) < (y : ℝ) := by linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  set D := 105 + j with hDdef
  have hDR : (D : ℝ) = 105 + (j : ℝ) := by rw [hDdef]; push_cast; ring
  have hϑlo : (D : ℝ) - 1 ≤ harperOffset D y := sub_one_le_harperOffset D (y : ℝ)
  have hϑhi : harperOffset D y < (D : ℝ) := harperOffset_lt_natCast D (y : ℝ)
  have hϑj : 104 + (j : ℝ) ≤ harperOffset D y := by linarith
  have hϑ104 : (104 : ℝ) ≤ harperOffset D y := by linarith
  have hϑ : radFreeStartThreshold E₀ ≤ harperOffset D y :=
    le_trans (radFreeStartThreshold_le_104 hE₀ (by linarith)) hϑ104
  set T := Real.exp ((j : ℝ) - 3) with hTdef
  have hT0 : 0 < T := Real.exp_pos _
  have hhT : (2 * T + 1) * pntFloorConst (harperOffset D y) ≤ Real.exp (-(2 * E₀)) / 200 :=
    height_floor_far hE₀1 j hϑj
  have hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D y) := by
    have h1 : 2 * (T / Real.exp 1) * Real.exp (harperOffset D y)
        = 2 * Real.exp ((j : ℝ) - 4 + harperOffset D y) := by
      rw [hTdef, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, mul_assoc, ← Real.exp_add,
        ← Real.exp_add]
      congr 2
      ring
    rw [h1]
    have h2 : Real.exp 6 ≤ Real.exp ((j : ℝ) - 4 + harperOffset D y) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : (403 : ℝ) ≤ Real.exp 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
      have := Real.exp_one_gt_d9
      have h4 : (2.718 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
      linarith [show (403 : ℝ) ≤ 2.718 ^ 6 by norm_num]
    have h5 : Real.exp (2 * E₀) ≤ Real.exp (1 / 5) := Real.exp_le_exp.2 (by linarith)
    have h6 := exp_one_fifth_le
    linarith
  have hKθ : T * Real.exp (harperOffset D y) ≤ Real.exp (2 * (j : ℝ) + 102) := by
    rw [hTdef, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hzb : ((0 : ℕ) : ℝ) ≤ blockScale (harperOffset D y) 0 := by
    rw [Nat.cast_zero]
    exact (blockScale_pos _ _).le
  obtain ⟨hρb, -, -, hρpos⟩ := window_weights (β := 0) hσ hT0 le_rfl
  have hσx : |σ| * Real.log (y : ℝ) ≤ E₀ := by rw [abs_of_pos hσ]; exact hσy
  have h := integral_rpow_block_weight_le_floor_of_height E₀ βc hE₀ hβc hβc2 hTr hκ hδ0 hδ hN
    hmono hY (x := (y : ℝ)) (σ := σ) (η := E₀) (T := T) (q := r) (A := A) (lam := lam)
    (Bd := (σ ^ 2)⁻¹) (z := 0) (D := D) (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹)
    (Kθ := Real.exp (2 * (j : ℝ) + 102))
    (by fun_prop) (fun t => by positivity) hρb hρpos hx1 hLL hϑ hϑ104 hσ.le hE₀ le_rfl hσx
    hT0 hhT hlo hKθ hzb (Nat.zero_le _) hNn hr0 hr1 hA hAmax hlam
  simp only [Nat.floor_natCast, randomEulerProductIco_zero] at h
  -- the second moment
  have hM2 : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
      (shiftLine σ 0) ω‖ ^ 2 ∂ν) ≤ 1.195 * Real.log y := by
    rw [hRa.integral_norm_randomEulerProduct_sq' (y + 1) (shiftLine σ 0), re_shiftLine]
    refine le_trans (Finset.prod_le_prod (fun m _ => by positivity) fun m hm => ?_)
      (prod_one_add_inv_primesBelow_le hy)
    have hmp := Nat.prime_of_mem_primesBelow hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmp.one_lt.le
    have : (m : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ ((m : ℝ))⁻¹ :=
      calc (m : ℝ) ^ (-2 * (1 / 2 + σ)) ≤ (m : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
        _ = ((m : ℝ))⁻¹ := Real.rpow_neg_one _
    linarith
  have hM0 : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
      (shiftLine σ 0) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => sq_nonneg _
  have hW := setIntegral_inv_sq_add_sq_window_le σ hT0
  have hI0 : 0 ≤ ∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ := hρpos.le
  set C := shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
    (radBlockBadConst E₀ βc * Real.exp (2 * (j : ℝ) + 102)) A
    (radAveragedShift E₀ βc Tr κ) lam δ r with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  set G := (1 + (1 - r) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-r) with hGdef
  have hG0 : 0 ≤ G := by
    have : 0 ≤ 1 - r := by linarith
    exact Real.rpow_nonneg (by positivity) _
  have hprod : (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹)
      * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ 0) ω‖ ^ 2 ∂ν) ≤ (Real.exp 1 - 1) / T * (1.195 * Real.log y) :=
    mul_le_mul hW hM2 hM0 (by
      have : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      positivity)
  have hprodr := Real.rpow_le_rpow (mul_nonneg hI0 hM0) hprod hr0
  have h2y : (0 : ℝ) ≤ (2 / Real.log y) ^ r := Real.rpow_nonneg (by positivity) _
  have hTinv : 1 / T = Real.exp (3 - (j : ℝ)) := by
    rw [hTdef, one_div, ← Real.exp_neg]
    congr 1
    ring
  have hkey : 2 / Real.log y * ((Real.exp 1 - 1) / T * (1.195 * Real.log y))
      = 2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ)) := by
    calc 2 / Real.log y * ((Real.exp 1 - 1) / T * (1.195 * Real.log y))
        = 2 * 1.195 * (Real.exp 1 - 1) * (1 / T) * (Real.log y / Real.log y) := by ring
      _ = 2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ)) := by
          rw [div_self hlogy.ne', mul_one, hTinv]
  have hbase0 : 0 ≤ (Real.exp 1 - 1) / T * (1.195 * Real.log y) := by
    have : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    positivity
  calc (2 / Real.log y) ^ r * ∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ r ∂ν
      ≤ (2 / Real.log y) ^ r * (C * ((∫ t in Set.Icc (T / Real.exp 1) T, (σ ^ 2 + t ^ 2)⁻¹)
          * (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            (shiftLine σ 0) ω‖ ^ 2 ∂ν)) ^ r * G) := mul_le_mul_of_nonneg_left h h2y
    _ ≤ (2 / Real.log y) ^ r * (C * ((Real.exp 1 - 1) / T * (1.195 * Real.log y)) ^ r * G) := by
        refine mul_le_mul_of_nonneg_left ?_ h2y
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprodr hC0) hG0
    _ = C * (2 / Real.log y * ((Real.exp 1 - 1) / T * (1.195 * Real.log y))) ^ r * G := by
        rw [Real.mul_rpow (by positivity) hbase0]
        ring
    _ = C * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ r * G := by rw [hkey]

/-! ### The far range as a sum of windows -/

/-- **The far range up to `e^{n-4}` as a sum of windows, the weight kept inside.**  For `σ > 0`
and `0 < r ≤ 1`, with `T_j = e^{j-3}`:

`E[((log y)⁻¹∫_{e^{-4}<|t|≤e^{n-4}}‖F_{y+1}(½+σ+it)/(σ+it)‖²dt)^r
  ≤ (2/log y)^r·∑_{j<n} E[(∫_{T_j/e}^{T_j}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^r]`,

as `RMF.integral_rpow_mesoRange_le_sum_windows`, with windows above height `1`. -/
theorem integral_rpow_farRange_le_sum_windows {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ r : ℝ} {y n : ℕ} (hy2 : 2 ≤ y) (hσ : 0 < σ)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-4) < |t|
          ∧ |t| ≤ Real.exp ((n : ℝ) - 4)},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r ∂ν)
      ≤ (2 / Real.log y) ^ r * ∑ j ∈ Finset.range n,
          ∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1) (Real.exp ((j : ℝ) - 3)),
            (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ r ∂ν := by
  haveI := hY.isProbabilityMeasure
  have hy2' : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  -- the integrand, decoupled
  have hint : ∀ (ω : Ω) (t : ℝ),
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
        = (σ ^ 2 + t ^ 2)⁻¹
          * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (shiftLine σ t) ω‖ ^ 2 := by
    intro ω t
    rw [norm_div_ofReal_add_mul_I_sq]
    congr 3
    rw [shiftLine]
    push_cast
    ring
  simp only [hint]
  have hρb : ∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹ := fun t =>
    (inv_le_inv₀ (by positivity) (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg t))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hvM : Real.exp (-4) ≤ Real.exp ((n : ℝ) - 4) := Real.exp_le_exp.2 (by linarith)
  -- the reflection
  have hfold := ae_setIntegral_weight_normSq_symm hY (y + 1) hσ.le
    (ρ := fun t => (σ ^ 2 + t ^ 2)⁻¹) (Bρ := (σ ^ 2)⁻¹) (fun t => by norm_num)
    (by fun_prop) (fun t => by positivity) hρb (Real.exp_pos _).le hvM
  have hcongr : (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-4) < |t|
          ∧ |t| ≤ Real.exp ((n : ℝ) - 4)},
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
          (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ r ∂ν)
      = ∫ ω, (2 / Real.log y) ^ r * (∫ t in Set.Ioc (Real.exp (-4))
          (Real.exp ((n : ℝ) - 4)), (σ ^ 2 + t ^ 2)⁻¹
            * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ r ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hfold] with ω hω
    rw [hω, ← Real.mul_rpow (by positivity) (integral_nonneg fun t => by positivity)]
    congr 1
    ring
  rw [hcongr, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  -- the windows
  refine integral_rpow_setIntegral_weight_le_sum_windows_inside hY (y + 1) hσ.le hr0 hr1
    (Finset.range n) (fun j => Real.exp ((j : ℝ) - 3) / Real.exp 1)
    (fun j => Real.exp ((j : ℝ) - 3)) (A := 0) (B := Real.exp ((n : ℝ) - 4))
    (fun t => by positivity) (by fun_prop) hρb measurableSet_Ioc ?_ ?_ ?_
  · intro t ht
    exact ⟨le_trans (Real.exp_pos _).le ht.1.le, ht.2⟩
  · intro j hj t ht
    have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by
      have := Finset.mem_range.1 hj
      exact_mod_cast this
    exact ⟨le_trans (by positivity) ht.1.le, le_trans ht.2 (Real.exp_le_exp.2 (by linarith))⟩
  · intro t ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
    have hlo : -4 < Real.log t := by
      have := Real.log_lt_log (Real.exp_pos _) ht.1
      rwa [Real.log_exp] at this
    have hhi : Real.log t ≤ (n : ℝ) - 4 := by
      have := Real.log_le_log ht0 ht.2
      rwa [Real.log_exp] at this
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log t + 4 := ⟨_, rfl⟩
    have hu0 : 0 < u := by linarith
    have hc1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.2 hu0
    have hclt : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0.le
    have hcge : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have hcn : ⌈u⌉₊ ≤ n := Nat.ceil_le.2 (by linarith)
    have hcast : ((⌈u⌉₊ - 1 : ℕ) : ℝ) = (⌈u⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hc1, Nat.cast_one]
    have htu : t = Real.exp (u - 4) := by
      rw [hu, add_sub_cancel_right, Real.exp_log ht0]
    refine ⟨⌈u⌉₊ - 1, Finset.mem_range.2 (by omega), ?_, ?_⟩
    · change Real.exp (((⌈u⌉₊ - 1 : ℕ) : ℝ) - 3) / Real.exp 1 < t
      rw [hcast, htu, ← Real.exp_sub]
      exact Real.exp_lt_exp.2 (by linarith)
    · change t ≤ Real.exp (((⌈u⌉₊ - 1 : ℕ) : ℝ) - 3)
      rw [hcast, htu]
      exact Real.exp_le_exp.2 (by linarith)

/-! ### Two ranges of the far line, and Jensen between two powers -/

/-- **The far range split at `M`**: `E[(L⁻¹∫_{|t|>v})^r] ≤ E[(L⁻¹∫_{v<|t|≤M})^r] +
E[(L⁻¹∫_{|t|>M})^r]` for `v ≤ M` and `0 ≤ r ≤ 1`, the integrand `|F|²/|σ+it|²` with `F` jointly
measurable and bounded (as `RMF.integral_rpow_lineDiv_le_of_three_ranges`). -/
theorem integral_rpow_lineDiv_far_le_of_two_ranges {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ → ℂ} {σ U L r v M : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hvM : v ≤ M) (hF : Measurable (Function.uncurry F))
    (hU : ∀ᵐ ω ∂μ, ∀ t, ‖F ω t‖ ≤ U) :
    (∫ ω, (L⁻¹ * ∫ t in {t : ℝ | v < |t|},
        ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r ∂μ)
      ≤ (∫ ω, (L⁻¹ * ∫ t in {t : ℝ | v < |t| ∧ |t| ≤ M},
          ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r ∂μ)
        + ∫ ω, (L⁻¹ * ∫ t in {t : ℝ | M < |t|},
          ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r ∂μ := by
  have hpos : ∀ t : ℝ, 0 < σ ^ 2 + t ^ 2 := fun t => by positivity
  have hpt : ∀ ω t, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
      = ‖F ω t‖ ^ 2 * (σ ^ 2 + t ^ 2)⁻¹ := fun ω t => by
    rw [norm_div, div_pow, Complex.sq_norm ((σ : ℂ) + (t : ℂ) * Complex.I),
      Complex.normSq_add_mul_I, div_eq_mul_inv]
  have hρ := integrable_inv_sq_add_sq hσ.ne'
  have hL0 : (0 : ℝ) ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hline : ∀ᵐ ω ∂μ,
      Integrable fun t : ℝ => ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    filter_upwards [hU] with ω hω
    have hmeas : Measurable fun t : ℝ => ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
      have h1 : Measurable fun t : ℝ => F ω t := hF.comp (measurable_const.prodMk measurable_id)
      have h2 : Measurable fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I :=
        (Complex.measurable_ofReal.mul_const Complex.I).const_add _
      exact (h1.div h2).norm.pow_const 2
    refine Integrable.mono' (hρ.const_mul (U ^ 2)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    change ‖‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ U ^ 2 * (σ ^ 2 + t ^ 2)⁻¹
    rw [Real.norm_of_nonneg (sq_nonneg _), hpt ω t]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hω t) 2)
      (inv_nonneg.2 (hpos t).le)
  have hAbs : Measurable fun t : ℝ => |t| := measurable_id.abs
  have hs2 : MeasurableSet {t : ℝ | v < |t| ∧ |t| ≤ M} :=
    (measurableSet_lt measurable_const hAbs).inter (measurableSet_le hAbs measurable_const)
  have hs3 : MeasurableSet {t : ℝ | M < |t|} := measurableSet_lt measurable_const hAbs
  have hunion : {t : ℝ | v < |t|} = {t : ℝ | v < |t| ∧ |t| ≤ M} ∪ {t : ℝ | M < |t|} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hle : |t| ≤ M
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr (not_le.1 hle)
    · rintro (h | h)
      · exact h.1
      · exact lt_of_le_of_lt hvM h
  have hdisj : Disjoint {t : ℝ | v < |t| ∧ |t| ≤ M} {t : ℝ | M < |t|} := by
    rw [Set.disjoint_left]
    rintro t ht ht'
    exact absurd (ht' : M < |t|) (not_lt.2 ht.2)
  have hpt2 : ∀ᵐ ω ∂μ,
      (L⁻¹ * ∫ t in {t : ℝ | v < |t|}, ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r
        ≤ (L⁻¹ * ∫ t in {t : ℝ | v < |t| ∧ |t| ≤ M},
              ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r
          + (L⁻¹ * ∫ t in {t : ℝ | M < |t|},
              ‖F ω t / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ r := by
    filter_upwards [hline] with ω hω
    rw [hunion, setIntegral_union hdisj hs3 hω.integrableOn hω.integrableOn, mul_add]
    exact Real.rpow_add_le_add_rpow
      (mul_nonneg hL0 (setIntegral_nonneg hs2 fun t _ => sq_nonneg _))
      (mul_nonneg hL0 (setIntegral_nonneg hs3 fun t _ => sq_nonneg _)) hr0 hr1
  have hI2 := integrable_rpow_setIntegral_lineDiv_of_bound
    (S := {t : ℝ | v < |t| ∧ |t| ≤ M}) (q := r) hσ hL hr0 hF hU
  have hI3 := integrable_rpow_setIntegral_lineDiv_of_bound (S := {t : ℝ | M < |t|}) (q := r)
    hσ hL hr0 hF hU
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (mul_nonneg hL0 (integral_nonneg fun t => sq_nonneg _)) _)
    (hI2.add hI3) hpt2) ?_
  exact le_of_eq (integral_add hI2 hI3)

/-- **Jensen between two powers**: on a probability space, `E[g^q] ≤ (E[g^r])^{q/r}` for `g ≥ 0`
and `0 < q ≤ r`, when `g^r` and `g^q` are integrable. -/
lemma integral_rpow_le_rpow_integral_rpow {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    {q r : ℝ} (hq0 : 0 < q) (hqr : q ≤ r) (hg0 : ∀ ω, 0 ≤ g ω)
    (hgr : Integrable (fun ω => g ω ^ r) μ) (hgq : Integrable (fun ω => g ω ^ q) μ) :
    (∫ ω, g ω ^ q ∂μ) ≤ (∫ ω, g ω ^ r ∂μ) ^ (q / r) := by
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr
  have hrq : r * (q / r) = q := by field_simp
  have hcongr : (fun ω => g ω ^ q) = fun ω => (g ω ^ r) ^ (q / r) := by
    funext ω
    rw [← Real.rpow_mul (hg0 ω), hrq]
  rw [hcongr] at hgq ⊢
  exact integral_rpow_le_rpow_integral (div_nonneg hq0.le hr0.le) ((div_le_one hr0).2 hqr)
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hg0 ω) r) hgr hgq

/-! ### The far range -/

/-- **The far range of `Z` at exponent `q`, by Jensen to `r ≥ q`, windows and a tail.**  For
`y ≥ e^99`, `σ > 0`, `0 < q ≤ r ≤ 1` and any bound `W` on the windows' sum up to `e^{n-4}`
(`RMF.integral_rpow_farRange_le_sum_windows`),

`E[((log y)⁻¹∫_{|t|>e^{-4}}‖F_{y+1}(½+σ+it)/(σ+it)‖²dt)^q] ≤ (W + (2·1.195/e^{n-4})^r)^{q/r}`:

Jensen between the powers `q ≤ r` (`RMF.integral_rpow_le_rpow_integral_rpow`), the split at
`e^{n-4}` (`RMF.integral_rpow_lineDiv_far_le_of_two_ranges`) and the tail by Jensen
(`RMF.integral_rpow_eulerProductLine_tail_le_explicit`). -/
theorem integral_rpow_farRange_le_holder {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q r W : ℝ} {y n : ℕ} (hy : Real.exp 99 ≤ (y : ℝ))
    (hσ : 0 < σ) (hq0 : 0 < q) (hqr : q ≤ r) (hr1 : r ≤ 1)
    (hW : (2 / Real.log y) ^ r * ∑ j ∈ Finset.range n,
          ∫ ω, (∫ t in Set.Icc (Real.exp ((j : ℝ) - 3) / Real.exp 1) (Real.exp ((j : ℝ) - 3)),
            (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
              (y + 1) (shiftLine σ t) ω‖ ^ 2) ^ r ∂ν ≤ W) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-4) < |t|},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ (W + (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ r) ^ (q / r) := by
  haveI := hY.isProbabilityMeasure
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr
  have hy2R : (2 : ℝ) ≤ (y : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hy
  have hy2 : 2 ≤ y := by exact_mod_cast hy2R
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  -- the field, measurable and bounded
  have hsline : ∀ t : ℝ, (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I
      = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    push_cast
    ring
  have hF : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω) := by
    have h := measurable_randomEulerProduct_sqfree_uncurry (X := Y)
      (fun p hp => hY.measurable p hp) (1 / 2 + σ) (y + 1)
    have hcongr : (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
        = fun z : Ω × ℝ => randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
            (y + 1) (((1 / 2 + σ : ℝ) : ℂ) + (z.2 : ℂ) * Complex.I) z.1 :=
      funext fun z => by
        simp only [Function.uncurry]
        rw [hsline z.2]
    rw [hcongr]
    exact h
  have hU : ∀ᵐ ω ∂ν, ∀ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖
        ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + (p : ℝ) ^ (-(1 / 2 + σ))) := by
    filter_upwards [ae_forall_norm_randomEulerProduct_mem_Icc hY (y + 1) (c := 1 / 2 + σ)
      (by linarith)] with ω hω
    intro t
    exact (hω _ (by rw [hsline t]; simp)).2
  have hS : MeasurableSet {t : ℝ | Real.exp (-4) < |t|} :=
    measurableSet_lt measurable_const measurable_id.abs
  have hgq := integrable_rpow_setIntegral_lineDiv_of_bound (S := {t : ℝ | Real.exp (-4) < |t|})
    (q := q) hσ hlogy hq0.le hF hU
  have hgr := integrable_rpow_setIntegral_lineDiv_of_bound (S := {t : ℝ | Real.exp (-4) < |t|})
    (q := r) hσ hlogy hr0.le hF hU
  have hg0 : ∀ ω : Ω, 0 ≤ (Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-4) < |t|},
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 :=
    fun ω => mul_nonneg (inv_nonneg.2 hlogy.le) (setIntegral_nonneg hS fun t _ => sq_nonneg _)
  refine le_trans (integral_rpow_le_rpow_integral_rpow hq0 hqr hg0 hgr hgq) ?_
  refine Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (hg0 ω) _) ?_
    (div_nonneg hq0.le hr0.le)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hvM : Real.exp (-4) ≤ Real.exp ((n : ℝ) - 4) := Real.exp_le_exp.2 (by linarith)
  refine le_trans (integral_rpow_lineDiv_far_le_of_two_ranges (μ := ν) hσ hlogy hr0.le hr1 hvM
    hF hU) (add_le_add ?_ ?_)
  · exact le_trans (integral_rpow_farRange_le_sum_windows hY hy2 hσ hr0 hr1) hW
  · exact integral_rpow_eulerProductLine_tail_le_explicit hY hr0 hr1 hy hσ (Real.exp_pos _)

/-- **The far range of `Z` at exponent `q`, by the chaos in every window** up to `e^{n-4}`, the
window `j` at the floor `105 + j` (`RMF.window_far_chaos`), with its own level `A j` and room
`N j`: for `0 < q ≤ r ≤ 1`, `y ≥ e^99`, `105 + n ≤ ⌊log log y⌋` and `σ log y ≤ E₀ ≤ 1/10`,

`E[Z_{|t|>e^{-4}}^q] ≤ (∑_{j<n} shiftMomentConst 1 C_i (C_b e^{2j+102}) (A j) s λ δ r
    ·(2·1.195(e-1)e^{3-j})^r·(1 + (1-r)√n_j)^{-r} + (2·1.195/e^{n-4})^r)^{q/r}`,

`n_j = harperBlockCount (105 + j) y`. -/
theorem integral_rpow_farRange_le_chaos (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 10)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ δ lam : ℝ} (hTr : 4 < Tr) (hκ : 1 ≤ κ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hlam : 1 ≤ lam) {N : ℕ → ℕ} {A : ℕ → ℝ}
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {σ q r : ℝ} {y n : ℕ}
    (hσ : 0 < σ) (hy : Real.exp 99 ≤ (y : ℝ)) (hσy : σ * Real.log y ≤ E₀)
    (hq0 : 0 < q) (hqr : q ≤ r) (hr1 : r ≤ 1) (hDy : 105 + n ≤ ⌊Real.log (Real.log y)⌋₊)
    (hwin : ∀ j ∈ Finset.range n,
      A j / 4 + 3 * Real.sqrt (N j : ℝ) / 4 + 1 ≤ δ * N j
        ∧ 3 ≤ 8 * δ * Real.sqrt (N j : ℝ) ∧ N j ≤ harperBlockCount (105 + j) y
        ∧ radBlockBadLevel E₀ ≤ A j) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in {t : ℝ | Real.exp (-4) < |t|},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ (∑ j ∈ Finset.range n, shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
            (radBlockBadConst E₀ βc * Real.exp (2 * (j : ℝ) + 102)) (A j)
            (radAveragedShift E₀ βc Tr κ) lam δ r
          * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ r
          * (1 + (1 - r) * Real.sqrt (harperBlockCount (105 + j) y : ℝ)) ^ (-r)
        + (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ r) ^ (q / r) := by
  refine integral_rpow_farRange_le_holder hY hy hσ hq0 hqr hr1 ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  obtain ⟨hN, hmono, hNn, hA⟩ := hwin j hj
  have hjn : j < n := Finset.mem_range.1 hj
  exact window_far_chaos E₀ βc hE₀ hE₀1 hβc hβc2 hTr hκ hδ0 hδ hN hmono hY
    (le_trans hq0.le hqr) hr1 hσ hy (by omega) hσy hNn hA le_rfl hlam

end RMF
