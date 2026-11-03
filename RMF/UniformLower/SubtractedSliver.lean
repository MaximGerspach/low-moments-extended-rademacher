/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfChaosCellExplicit
import RMF.Weighted.BandWindowsExplicit
import RMF.Weighted.CentralWindowAboveHalfExplicit
import RMF.Weighted.LowerFixedQ

/-!
# The subtracted term in the sliver above `½`

The subtracted term of the explicit reduction
(`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`),
`E[J(V/log x)^q]`, `J(σ) = ∫_ℝ‖F_{⌊x⌋+1}(½+σ+it)/(σ+it)‖²dt`, with an absolute constant in the
sliver `½ < q ≤ 0.50015`, for `log log x ≥ 8` and `V ≥ 1/160000`:

`E[J(V/log x)^q] ≤ 33(log x)^q·(log x)^{q(2q-1)}(2q-1)^{-3/4}`
(`RMF.integral_rpow_lineDiv_le_subtracted_sliver`).

No conditioning: the shift down to the fixed tilt `σ = 1/(160000 log x)`, then
`Z = (log z)⁻¹J_z(σ)` at `z = ⌊x⌋` by the above-`½` chain's bottom windows, whose right sides do
not depend on `σ` once `σ log z ≤ 1/160000`.

* **The bottom's windows at a small tilt** (`RMF.window_bottom_le_chaos_aligned_of_sigma`,
  `RMF.window_bottom_le_winBotCh_of_sigma`): the twins of the chain's windows, which fix
  `σ = (log x)^{-2}`.
* **The central range for `0 < q ≤ 1`** (`RMF.integral_rpow_centralRange_le_of_le_one`): Hölder
  over the window (`RMF.integral_rpow_setIntegral_le_of_mixed`) with the two-point ratio at every
  `q ≤ 1`.
* **`Z` from three ranges** (`RMF.integral_rpow_Z_le_bottom`), then in the sliver
  (`RMF.Z_bottom_le_sliver`): central `≤ 795(log z)^a`, windows
  `≤ 213 + 26.43(log z)^a(2q-1)^{-3/4}` (the chaos profile at `G = 1.254`), far range `≤ 1.195`,
  and `(2q-1)^{-3/4} ≥ 438`: at most `28.73(log z)^a(2q-1)^{-3/4}`, `a = q(2q-1)`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The bottom's windows at a small tilt -/

/-- **The bottom's window at `T log z = e^m` by the chaos, at a small tilt**: as
`RMF.window_bottom_le_chaos_aligned` with `σ > 0`, `σ log z ≤ 1/160000` in place of
`σ = (log x)^{-2}`, `log x ≥ 160000`; the right side does not depend on `σ`. -/
theorem window_bottom_le_chaos_aligned_of_sigma {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ q T : ℝ} {z m : ℕ} (hz : 2 ≤ z) (hσ : 0 < σ)
    (hσz : σ * Real.log z ≤ 1 / 160000) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hm : 2008 ≤ m) (hmL : (m : ℝ) + 97 ≤ Real.log (Real.log z))
    (hTm : T * Real.log z = Real.exp m) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (T / Real.exp 1) T,
          (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ winSplitFull q T (splitPt (3 / 2) T 2 z) z
        * (chaosAbove q * (1 + (1 - q) * Real.sqrt ((m - 8 : ℕ) : ℝ)) ^ (-q)) := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  -- `T ≤ e^{-97}`, so `T log 2 ≤ e`
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hTe : T = Real.exp ((m : ℝ) - Real.log (Real.log z)) := by
    rw [Real.exp_sub, Real.exp_log hlz, eq_div_iff hlz.ne', hTm]
  have hTy : T * Real.log (2 : ℕ) ≤ Real.exp 1 := by
    have h1 : T ≤ 1 := by rw [hTe]; exact Real.exp_le_one_iff.2 (by linarith)
    have h2 : Real.log ((2 : ℕ) : ℝ) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (1 : ℝ)
      push_cast
      linarith
    have h3 : 0 ≤ Real.log ((2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h4 : 0 < T := by rw [hTe]; exact Real.exp_pos _
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  obtain ⟨hT, hT1, hDlog, hϑ, hϑ104, hlo, hKθ, hzb, hNn, hn⟩ :=
    aligned_chaos_conditions (le_refl 2) hz hm hmL hTm hTy
  have h := window_bottom_le_split_chaos_explicit hX (1 / 160000) (11 / 20) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (Tr := 30) (κ := 8) (Kθ := Real.exp 7)
    (Amax := 20) (δc := 1 / 50) (N := 2000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_room half_mono (le_splitPt hz) (splitPt_le _ _ 2 z)
    (η := 1 / 160000) (A := 18) (lam := 98 / 5) hσ hq0 hq1 hT hT1 hDlog hϑ hϑ104
    (by norm_num) le_rfl hσz hlo hKθ hzb hNn radBlockBadLevel_tilt_le (by norm_num) (by norm_num)
  rw [hn] at h
  exact h

/-- **A bottom window at a small tilt**: for `½ ≤ q ≤ 1`, `2 ≤ z`, `σ > 0` with
`σ log z ≤ 1/160000` and `k < RMF.bottomJ 1 2 z`, the window at height `RMF.bottomT 1 2 z k` is
at most `RMF.winBotCh q z k`: the better of no split, the split, and the split with the chaos
(`RMF.window_bottom_le_chaos_aligned_of_sigma`) — the block of
`RMF.integral_rpow_norm_truncationTail_le_bottomLevelCh` at any such `σ`. -/
theorem window_bottom_le_winBotCh_of_sigma {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ q : ℝ} {z k : ℕ} (hz : 2 ≤ z) (hσ : 0 < σ)
    (hσz : σ * Real.log z ≤ 1 / 160000) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1)
    (hk : k < bottomJ 1 2 z) :
    (2 / (2 * Real.pi * Real.log z)) ^ q
        * (∫ ω, (∫ t in Set.Icc (bottomT 1 2 z k / Real.exp 1) (bottomT 1 2 z k),
          (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) 1 (z + 1)
              (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ)
      ≤ winBotCh q z k := by
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hM : ∀ t : ℝ, (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
      (0 + 1) (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ) ≤ mFull z :=
    fun t => integral_normSq_line_le_mFull hX hz hσ.le t
  have hT : 0 < bottomT 1 2 z k := Real.exp_pos _
  rw [winBotCh]
  refine le_min (window_band_le_nosplit_explicit hX 0 z hz hσ (by linarith) hq1 hT hM) ?_
  have hJ : _ ≤ winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z :=
    window_bottom_le_split_explicit hX (le_splitPt (c := 3 / 2) (T := bottomT 1 2 z k) hz)
      (splitPt_le (3 / 2) (bottomT 1 2 z k) 2 z) hσ hq0 hq1 hT le_rfl
  rw [chaosMult]
  split_ifs with hc
  · rw [mul_min_of_nonneg _ _ (winSplitFull_nonneg hq1 hT), mul_one]
    refine le_min hJ ?_
    exact window_bottom_le_chaos_aligned_of_sigma hX hz hσ hσz hq0 hq1 hc.1 hc.2
      (bottomT_aligned hlz hk)
  · rw [mul_one]
    exact hJ

/-! ### The central range for `q ≤ 1` -/

/-- **The central window in the weight form, for `0 < q ≤ 1`.**  For `σ > 0`, any `w` and `F` the
product over `y₀ ≤ p < y₁`,

`E[(∫_{|t|≤w}(σ²+t²)⁻¹‖F(½+σ+it)‖²dt)^q] ≤ (∫_{|t|≤w}(σ²+t²)⁻¹e^{βt²}dt)^q·E‖F(½+σ)‖^{2q}`,

`β = 2(1-q)S₂`, `S₂ = (log y₁)²/2 + 15.003 log y₁ + 34`: Hölder over the window against
`‖F(½+σ)‖^{2q-2}` (`RMF.integral_rpow_setIntegral_le_of_mixed`) with the two-point ratio at every
`q ≤ 1` (`RMF.integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one`). -/
theorem integral_rpow_setIntegral_weight_shiftLine_le_of_le_one {Y : ℕ → Ω → ℂ}
    {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) (y₀ y₁ : ℕ) {σ q w : ℝ} (hσ : 0 < σ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∫ ω, (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν)
      ≤ (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (2 * (1 - q)
          * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) * t ^ 2)) ^ q
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν := by
  haveI := hY.isProbabilityMeasure
  have hc0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hLo0 : (0 : ℝ) < ∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 + σ))) :=
    prod_one_sub_prime_rpow_primesIco_pos_of_pos hc0
  have henv := ae_forall_norm_randomEulerProductIco_mem_Icc_of_pos hY y₀ y₁ hc0
  -- the base point's square is enveloped, and so is the window's integrand
  have hN : ∀ᵐ ω ∂ν, (∏ p ∈ primesIco y₀ y₁, (1 - (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2
        ≤ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2
      ∧ ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2
        ≤ (∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    filter_upwards [henv] with ω hω
    have h := hω (shiftLine σ 0) (re_shiftLine σ 0)
    exact ⟨pow_le_pow_left₀ hLo0.le h.1 2, pow_le_pow_left₀ (norm_nonneg _) h.2 2⟩
  have hGD : ∀ᵐ ω ∂ν, ∀ t : ℝ, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2
      ≤ (σ ^ 2)⁻¹ * (∏ p ∈ primesIco y₀ y₁, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2 := by
    filter_upwards [henv] with ω hω t
    have h := (hω (shiftLine σ t) (re_shiftLine σ t)).2
    have hwt : (σ ^ 2 + t ^ 2)⁻¹ ≤ (σ ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith [sq_nonneg t])
    exact mul_le_mul hwt (pow_le_pow_left₀ (norm_nonneg _) h 2) (sq_nonneg _)
      (inv_nonneg.2 (by positivity))
  -- measurability
  have hline : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
      randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
        (shiftLine σ t) ω) := by
    convert measurable_uncurry_randomEulerProductIco_line hY y₀ y₁ (-σ) using 1
    funext z
    obtain ⟨ω, t⟩ := z
    simp only [Function.uncurry_apply_pair]
    congr 1
    rw [shiftLine]
    push_cast
    ring
  have hNm : Measurable fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁ (shiftLine σ 0) ω‖ ^ 2 :=
    (measurable_norm_randomEulerProductIco_sqfree hY y₀ y₁ (shiftLine σ 0)).pow_const 2
  have hGm : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) => (σ ^ 2 + t ^ 2)⁻¹
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2) := by
    have hc : Measurable fun z : Ω × ℝ => (σ ^ 2 + z.2 ^ 2)⁻¹ := by fun_prop
    exact hc.mul (hline.norm.pow_const 2)
  -- the weight
  have hBc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (2 * (1 - q)
      * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) * t ^ 2) := by
    have hc : Continuous fun t : ℝ => (σ ^ 2 + t ^ 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun t => (by positivity : (0 : ℝ) < σ ^ 2 + t ^ 2).ne'
    exact hc.mul (by fun_prop)
  -- the two-point ratio at each height
  have hper : ∀ t ∈ Set.Icc (-w) w,
      (∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1) * ((σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2) ∂ν)
        ≤ (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (2 * (1 - q)
            * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) * t ^ 2)
          * ∫ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ 2) ^ q ∂ν := by
    intro t _
    have hmix := integral_mixed_norm_shiftLine_primesIco_le_exp_sharp_of_le_one hY y₀ y₁ hσ.le
      hq0.le hq1 t
    have hrw : ∀ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ (q - 1) * ((σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ t) ω‖ ^ 2)
        = (σ ^ 2 + t ^ 2)⁻¹ * (‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁ (shiftLine σ 0) ω‖ ^ (2 * (q - 1))
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
            (shiftLine σ t) ω‖ ^ (2 * (1 : ℝ))) := by
      intro ω
      rw [norm_rpow_two_mul _ (q - 1), norm_rpow_two_mul _ 1, Real.rpow_one]
      ring
    have hrw2 : ∀ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ 2) ^ q
        = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
          (shiftLine σ 0) ω‖ ^ (2 * q) := fun ω => (norm_rpow_two_mul _ q).symm
    simp_rw [hrw, hrw2]
    rw [integral_const_mul]
    have he : Real.exp (2 * (1 - q) * t ^ 2 * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34))
        = Real.exp (2 * (1 - q) * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) * t ^ 2) := by
      congr 1
      ring
    rw [he] at hmix
    have hw0 : 0 ≤ (σ ^ 2 + t ^ 2)⁻¹ := inv_nonneg.2 (by positivity)
    calc _ ≤ (σ ^ 2 + t ^ 2)⁻¹ * (Real.exp (2 * (1 - q)
            * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) * t ^ 2)
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
            (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν) := mul_le_mul_of_nonneg_left hmix hw0
      _ = _ := by ring
  have hmain := integral_rpow_setIntegral_le_of_mixed (μ := ν)
    (N := fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
      (shiftLine σ 0) ω‖ ^ 2)
    (G := fun ω t => (σ ^ 2 + t ^ 2)⁻¹
      * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
        (shiftLine σ t) ω‖ ^ 2)
    (B := fun t => (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (2 * (1 - q)
      * (Real.log y₁ ^ 2 / 2 + 15.003 * Real.log y₁ + 34) * t ^ 2))
    (a := -w) (b := w) hq0 hq1 (pow_pos hLo0 2) hNm hN hGm (fun ω t => by positivity) hGD
    (fun t => by positivity) hBc.integrableOn_Icc hper
  have hrw2 : ∀ ω, (‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
        (shiftLine σ 0) ω‖ ^ 2) ^ q
      = ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) y₀ y₁
        (shiftLine σ 0) ω‖ ^ (2 * q) := fun ω => (norm_rpow_two_mul _ q).symm
  simp_rw [hrw2] at hmain
  exact hmain

/-- **The central range of `Z`, for `0 < q ≤ 1`.**  For `y ≥ 2`, `σ > 0`, `w > 0` and `F_{y+1}`
the Euler product over `p ≤ y`,

`E[((log y)⁻¹∫_{|t|≤w}‖F_{y+1}(½+σ+it)/(σ+it)‖²dt)^q]
  ≤ ((π/σ + 2(e^{2(1-q)S₂w²} - 1)/w)/log y)^q·E‖F_{y+1}(½+σ)‖^{2q}`,

`S₂ = (log(y+1))²/2 + 15.003 log(y+1) + 34`: `RMF.integral_rpow_centralRange_le_sharp` at every
`q ≤ 1`, through `RMF.integral_rpow_setIntegral_weight_shiftLine_le_of_le_one` and the window's
weight `RMF.setIntegral_inv_sq_add_sq_mul_exp_le`; the moment is left to the caller. -/
theorem integral_rpow_centralRange_le_of_le_one {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ q w : ℝ} {y : ℕ} (hy : 2 ≤ y) (hσ : 0 < σ)
    (hw : 0 < w) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∫ ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂ν)
      ≤ ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
            * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
            * w ^ 2) - 1) / w) / Real.log y) ^ q
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν := by
  haveI := hY.isProbabilityMeasure
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hcast : (((y + 1 : ℕ)) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
  have hβ0 : 0 ≤ 2 * (1 - q) * (Real.log ((y : ℝ) + 1) ^ 2 / 2
      + 15.003 * Real.log ((y : ℝ) + 1) + 34) := by
    have : 0 ≤ Real.log ((y : ℝ) + 1) := Real.log_nonneg (by linarith)
    have : 0 ≤ 1 - q := by linarith
    positivity
  -- the integrand in the weight form
  have hpt : ∀ ω, (∫ t in Set.Icc (-w) w,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
        / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) 0 (y + 1)
          (shiftLine σ t) ω‖ ^ 2 := by
    intro ω
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hs : shiftLine σ t = (1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I := by
      rw [shiftLine]
      push_cast
      ring
    simp only [norm_div_ofReal_add_mul_I_sq, randomEulerProductIco_zero, hs]
  have hsplit : ∀ ω : Ω, ((Real.log y)⁻¹ * ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) 0 (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q
      = ((Real.log y)⁻¹) ^ q * (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) 0 (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q := fun ω =>
    Real.mul_rpow (by positivity) (setIntegral_nonneg measurableSet_Icc fun t _ => by positivity)
  simp only [hpt, hsplit]
  rw [integral_const_mul]
  have hmain := integral_rpow_setIntegral_weight_shiftLine_le_of_le_one hY 0 (y + 1) (w := w)
    hσ hq0 hq1
  have hs0 : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hcast, hs0] at hmain
  simp only [randomEulerProductIco_zero] at hmain
  have hW := setIntegral_inv_sq_add_sq_mul_exp_le hσ hw hβ0
  have hW0 : 0 ≤ ∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹ * Real.exp (2 * (1 - q)
      * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34) * t ^ 2) :=
    setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  have hM0 : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
      (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hRq := Real.rpow_le_rpow hW0 hW hq0.le
  have hR0 : 0 ≤ Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
      * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34) * w ^ 2) - 1)
        / w := le_trans hW0 hW
  have hNq : (0 : ℝ) ≤ ((Real.log y)⁻¹) ^ q := Real.rpow_nonneg (by positivity) _
  calc ((Real.log y)⁻¹) ^ q * ∫ ω, (∫ t in Set.Icc (-w) w, (σ ^ 2 + t ^ 2)⁻¹
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) 0 (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν
      ≤ ((Real.log y)⁻¹) ^ q * ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
            * (Real.log ((y : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((y : ℝ) + 1) + 34)
            * w ^ 2) - 1) / w) ^ q
        * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            (((1 / 2 + σ : ℝ)) : ℂ) ω‖ ^ (2 * q) ∂ν) :=
        mul_le_mul_of_nonneg_left (le_trans hmain (mul_le_mul_of_nonneg_right hRq hM0)) hNq
    _ = _ := by
        rw [← mul_assoc, ← Real.mul_rpow (by positivity) hR0, div_eq_mul_inv _ (Real.log y),
          mul_comm _ (Real.log y)⁻¹]

/-! ### `Z` from three ranges -/

/-- **`Z` by the bottom's windows.**  For `½ ≤ q ≤ 1`, `z ≥ e^{99}` and `σ > 0` with
`σ log z ≤ 1/160000`, `Z = (log z)⁻¹∫_ℝ‖F_{z+1}(½+σ+it)/(σ+it)‖²dt` and `J = RMF.bottomJ 1 2 z`:

`E[Z^q] ≤ ((π/σ + 2(e^{2(1-q)S₂/(log z)²} - 1)log z)/log z)^q·RMF.pfFull q z
  + (2π)^q∑_{k<J} RMF.winBotCh q z k + (2·1.195·log z/e^J)^q`,

`S₂ = (log(z+1))²/2 + 15.003 log(z+1) + 34`: the central range `|t| ≤ 1/log z`
(`RMF.integral_rpow_centralRange_le_of_le_one` with (PF)), the windows `(e^{J-k-1}, e^{J-k}]/log z`
(`RMF.integral_rpow_mesoRange_band_le_sum_windows`, `RMF.window_bottom_le_winBotCh_of_sigma`) and
the far range (`RMF.integral_rpow_eulerProductLine_tail_le_explicit`). -/
theorem integral_rpow_Z_le_bottom {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ q : ℝ} {z : ℕ} (hz : Real.exp 99 ≤ (z : ℝ))
    (hσ : 0 < σ) (hσz : σ * Real.log z ≤ 1 / 160000) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
            * (Real.log ((z : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((z : ℝ) + 1) + 34)
            * (1 / Real.log z) ^ 2) - 1) / (1 / Real.log z)) / Real.log z) ^ q * pfFull q z
        + (2 * Real.pi) ^ q * ∑ k ∈ Finset.range (bottomJ 1 2 z), winBotCh q z k
        + (2 * 1.195 / (Real.exp (bottomJ 1 2 z) / Real.log z)) ^ q := by
  haveI := hX.isProbabilityMeasure
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := le_trans (by linarith [Real.add_one_le_exp (99 : ℝ)]) hz
  have hz2 : 2 ≤ z := by exact_mod_cast hz2R
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hq0' : 0 < q := by linarith
  set J := bottomJ 1 2 z with hJdef
  set c := Real.log (1 / Real.log z) + (J : ℝ) with hcdef
  have hlz' : Real.log z ≠ 0 := hlz.ne'
  have hw : Real.exp (c - (J : ℝ)) = 1 / Real.log z := by
    rw [hcdef, add_sub_cancel_right, Real.exp_log (one_div_pos.2 hlz)]
  have hv : Real.exp (c - ((0 : ℕ) : ℝ)) = Real.exp J / Real.log z := by
    rw [Nat.cast_zero, sub_zero, hcdef, Real.exp_add, Real.exp_log (one_div_pos.2 hlz)]
    ring
  have hwv : 1 / Real.log z ≤ Real.exp J / Real.log z :=
    div_le_div_of_nonneg_right (Real.one_le_exp (Nat.cast_nonneg _)) hlz.le
  -- the central range, with (PF)
  have hb1 := integral_rpow_centralRange_le_of_le_one hX (σ := σ) (q := q)
    (w := 1 / Real.log z) hz2 hσ (one_div_pos.2 hlz) hq0' hq1
  have hPF := hX.isRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_above_half
    hσ.le hq0 hq1 hz2
  have hC0 : 0 ≤ ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
      * (Real.log ((z : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((z : ℝ) + 1) + 34)
      * (1 / Real.log z) ^ 2) - 1) / (1 / Real.log z)) / Real.log z) ^ q := by
    refine Real.rpow_nonneg (div_nonneg (add_nonneg (by positivity) (div_nonneg ?_ (by positivity)))
      hlz.le) _
    have : 0 ≤ Real.log ((z : ℝ) + 1) := Real.log_nonneg (by linarith)
    have : 0 ≤ 1 - q := by linarith
    have h1 : 1 ≤ Real.exp (2 * (1 - q)
        * (Real.log ((z : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((z : ℝ) + 1) + 34)
        * (1 / Real.log z) ^ 2) := Real.one_le_exp (by positivity)
    linarith
  have hb1' := le_trans hb1 (mul_le_mul_of_nonneg_left hPF hC0)
  -- the windows
  have hb2 := integral_rpow_mesoRange_band_le_sum_windows hX 1 (z + 1) (σ := σ) (q := q)
    (L := Real.log z) (c := c) (k₀ := 0) (J := J) hσ hq0' hq1 hlz (Nat.zero_le J)
  rw [hw, hv] at hb2
  simp only [randomEulerProductIco_one] at hb2
  have hwin : ∀ k ∈ Finset.Ico 0 J, (2 / Real.log z) ^ q
      * ∫ ω, (∫ t in Set.Icc (Real.exp (c - k) / Real.exp 1) (Real.exp (c - k)),
        (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          (z + 1) (shiftLine σ t) ω‖ ^ 2) ^ q ∂μ
      ≤ (2 * Real.pi) ^ q * winBotCh q z k := by
    intro k hk
    have h := window_bottom_le_winBotCh_of_sigma hX hz2 hσ hσz hq0 hq1 (Finset.mem_Ico.1 hk).2
    simp only [randomEulerProductIco_one] at h
    have hT : bottomT 1 2 z k = Real.exp (c - k) := rfl
    rw [hT] at h
    have e : (2 / Real.log z) ^ q
        = (2 * Real.pi) ^ q * (2 / (2 * Real.pi * Real.log z)) ^ q := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by positivity) _)
  have hb2' : (∫ ω, ((Real.log z)⁻¹ * ∫ t in {t : ℝ | 1 / Real.log z < |t|
        ∧ |t| ≤ Real.exp J / Real.log z},
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ (2 * Real.pi) ^ q * ∑ k ∈ Finset.range J, winBotCh q z k := by
    refine le_trans hb2 ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.range_eq_Ico]
    exact Finset.sum_le_sum hwin
  -- the far range
  have hb3 := integral_rpow_eulerProductLine_tail_le_explicit hX hq0' hq1 hz hσ
    (T := Real.exp J / Real.log z) (div_pos (Real.exp_pos _) hlz)
  exact integral_rpow_eulerLineDiv_le_of_three_ranges hX (σ := σ) (q := q)
    (w := 1 / Real.log z) (v := Real.exp J / Real.log z) hz2 hσ hq0'.le hq1 hwv hb1' hb2' hb3

/-! ### The pieces' numerals over `½ < q ≤ 0.50015` -/

/-- `(2π)^q ≤ 2.509` for `0 ≤ q ≤ 0.50015`. -/
lemma sliver_twoPi_rpow_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 50015 / 100000) :
    (2 * Real.pi) ^ q ≤ 2.509 := by
  have hpi := Real.pi_lt_d4
  have h1 : (2 * Real.pi) ^ q ≤ Real.exp (50015 / 100000 * Real.log 6.2832) :=
    rpow_le_exp_hi (by positivity) (by linarith) (by norm_num) hq0 hq
  have h2 : Real.exp (50015 / 100000 * Real.log 6.2832) ≤ 2.509 := by
    interval_decide (trust := kernel)
  linarith

/-- The split windows' constant `pfC1·ω·1.5^{q(2q-1)} ≤ 0.7772` for `½ < q ≤ 0.50015`
(`RMF.pfC1_le_pfC1Hat`, `RMF.omegaClean_le_hat` at the cell `[½, 0.50015]`). -/
lemma sliver_winConst_le {q : ℝ} (hq0 : 1 / 2 < q) (hq : q ≤ 50015 / 100000) :
    pfC1 q * omegaClean q * (3 / 2 : ℝ) ^ (q * (2 * q - 1)) ≤ 0.7772 := by
  have hq1 : q ≤ 1 := by linarith
  have h1 : pfC1 q ≤ 1.0002 :=
    le_trans (pfC1_le_pfC1Hat (ql := 1 / 2) (qu := 50015 / 100000) le_rfl hq0.le hq
      (by norm_num)) (by unfold pfC1Hat; interval_decide (trust := kernel))
  have h2 : omegaClean q ≤ 0.7768 :=
    le_trans (omegaClean_le_hat (ql := 1 / 2) (qu := 50015 / 100000) le_rfl hq0.le hq
      (by norm_num)) (by unfold windowWHat; interval_decide (trust := kernel))
  have h3 : (3 / 2 : ℝ) ^ (q * (2 * q - 1)) ≤ 1.0002 := by
    refine le_trans (rpow_le_exp_of_one_le (by norm_num) (mul_two_mul_sub_one_le hq0.le hq)) ?_
    interval_decide (trust := kernel)
  have h20 : 0 ≤ omegaClean q := omegaClean_nonneg hq1
  have h30 : 0 ≤ (3 / 2 : ℝ) ^ (q * (2 * q - 1)) := Real.rpow_nonneg (by norm_num) _
  calc pfC1 q * omegaClean q * (3 / 2 : ℝ) ^ (q * (2 * q - 1))
      ≤ 1.0002 * 0.7768 * 1.0002 :=
        mul_le_mul (mul_le_mul h1 h2 h20 (by norm_num)) h3 h30 (by norm_num)
    _ ≤ 0.7772 := by norm_num

/-- `q^{-3/4} ≤ 1.682` for `q ≥ ½`. -/
lemma sliver_rpow_q_le {q : ℝ} (hq0 : 1 / 2 ≤ q) : q ^ (-(3 / 4 : ℝ)) ≤ 1.682 := by
  refine le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hq0 (by norm_num)) ?_
  rw [Real.rpow_def_of_pos (by norm_num)]
  interval_decide (trust := kernel)

/-- `(2q - 1)^{-3/4} ≥ 438` for `½ < q ≤ 0.50015`, where `2q - 1 ≤ 3·10⁻⁴`. -/
lemma sliver_delta_rpow_ge {q : ℝ} (hq0 : 1 / 2 < q) (hq : q ≤ 50015 / 100000) :
    438 ≤ (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
  refine le_trans ?_ (Real.rpow_le_rpow_of_nonpos (by linarith)
    (by linarith : 2 * q - 1 ≤ 3 / 10000) (by norm_num))
  rw [Real.rpow_def_of_pos (by norm_num)]
  interval_decide (trust := kernel)

/-- `e^{97q(2q-1)} ≤ 1.015` for `½ ≤ q ≤ 0.50015`. -/
lemma sliver_exp_tail_le {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq : q ≤ 50015 / 100000) :
    Real.exp (97 * (q * (2 * q - 1))) ≤ 1.015 := by
  refine le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
    (mul_two_mul_sub_one_le hq0 hq) (by norm_num))) ?_
  interval_decide (trust := kernel)

/-! ### The three pieces in the sliver -/

/-- **The central term, abstractly**: for `L ≥ 2300`, `0 ≤ L₁ ≤ L + 0.6932`, `σL ≥ 1/200000`
and `½ ≤ q ≤ 0.50015`,
`((π/σ + 2(e^{2(1-q)S₂/L²} - 1)L)/L)^q·L^a e^{a(0.2641 + 9.0028/L + (2-2q)/3)} ≤ 795L^a`,
`S₂ = L₁²/2 + 15.003L₁ + 34`, `a = q(2q-1)`: `π/σ ≤ 628320L`, `2(1-q)S₂/L² ≤ 0.507`. -/
lemma sliver_central_arith {σ q L L₁ : ℝ} (hL : 2300 ≤ L) (hL₁0 : 0 ≤ L₁)
    (hL₁ : L₁ ≤ L + 0.6932) (hσ0 : 1 / 200000 ≤ σ * L) (hq0 : 1 / 2 ≤ q)
    (hq : q ≤ 50015 / 100000) :
    ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q) * (L₁ ^ 2 / 2 + 15.003 * L₁ + 34)
        * (1 / L) ^ 2) - 1) / (1 / L)) / L) ^ q
      * (L ^ (q * (2 * q - 1))
        * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / L + (2 - 2 * q) / 3)))
      ≤ 795 * L ^ (q * (2 * q - 1)) := by
  have hL0 : 0 < L := by linarith
  have hσ : 0 < σ := by
    by_contra h
    push Not at h
    nlinarith
  have hq0' : 0 ≤ q := by linarith
  -- the window's exponent
  have hS : L₁ ^ 2 / 2 + 15.003 * L₁ + 34 ≤ 0.507 * L ^ 2 := by
    have h1 : L₁ ^ 2 ≤ (L + 0.6932) ^ 2 := pow_le_pow_left₀ hL₁0 hL₁ 2
    nlinarith [sq_nonneg (L - 2300)]
  have hβ : 2 * (1 - q) * (L₁ ^ 2 / 2 + 15.003 * L₁ + 34) * (1 / L) ^ 2 ≤ 0.507 := by
    have h1 : 0 ≤ L₁ ^ 2 / 2 + 15.003 * L₁ + 34 := by positivity
    have h3 : 0 ≤ 1 - 2 * (1 - q) := by linarith
    rw [div_pow, one_pow, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg h3 h1]
  set E := Real.exp (2 * (1 - q) * (L₁ ^ 2 / 2 + 15.003 * L₁ + 34) * (1 / L) ^ 2) with hEdef
  have hE : E ≤ 1.661 := by
    refine le_trans (Real.exp_le_exp.2 hβ) ?_
    interval_decide (trust := kernel)
  have hE1 : 1 ≤ E := Real.one_le_exp (by
    have : 0 ≤ 1 - q := by linarith
    positivity)
  have hπσ : Real.pi / σ ≤ 628320 * L := by
    rw [div_le_iff₀ hσ]
    have hpi := Real.pi_lt_d4
    have e : 628320 * L * σ = 628320 * (σ * L) := by ring
    linarith
  have hbr : (Real.pi / σ + 2 * (E - 1) / (1 / L)) / L ≤ 628400 := by
    rw [div_le_iff₀ hL0]
    have e : 2 * (E - 1) / (1 / L) = 2 * (E - 1) * L := by field_simp
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.2 hE) hL0.le]
  have hbr0 : 0 ≤ (Real.pi / σ + 2 * (E - 1) / (1 / L)) / L := by
    have : 0 ≤ E - 1 := by linarith
    positivity
  have h1 : ((Real.pi / σ + 2 * (E - 1) / (1 / L)) / L) ^ q
      ≤ Real.exp (50015 / 100000 * Real.log 628400) :=
    rpow_le_exp_hi hbr0 hbr (by norm_num) hq0' hq
  have h2 : Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / L + (2 - 2 * q) / 3))
      ≤ Real.exp (50015 / 100000 * (2 * (50015 / 100000) - 1) * 0.6015) := by
    refine Real.exp_le_exp.2 ?_
    have ha := mul_two_mul_sub_one_le hq0 hq
    have h9 : 9.0028 / L ≤ 0.004 := by rw [div_le_iff₀ hL0]; linarith
    have h90 : 0 ≤ 9.0028 / L := by positivity
    exact mul_le_mul ha (by linarith) (by linarith) (by norm_num)
  have h3 : Real.exp (50015 / 100000 * Real.log 628400)
      * Real.exp (50015 / 100000 * (2 * (50015 / 100000) - 1) * 0.6015) ≤ 795 := by
    interval_decide (trust := kernel)
  have hLa : 0 ≤ L ^ (q * (2 * q - 1)) := Real.rpow_nonneg hL0.le _
  calc ((Real.pi / σ + 2 * (E - 1) / (1 / L)) / L) ^ q
        * (L ^ (q * (2 * q - 1))
          * Real.exp (q * (2 * q - 1) * (0.2641 + 9.0028 / L + (2 - 2 * q) / 3)))
      ≤ Real.exp (50015 / 100000 * Real.log 628400) * (L ^ (q * (2 * q - 1))
          * Real.exp (50015 / 100000 * (2 * (50015 / 100000) - 1) * 0.6015)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hLa) (mul_nonneg hLa (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = (Real.exp (50015 / 100000 * Real.log 628400)
          * Real.exp (50015 / 100000 * (2 * (50015 / 100000) - 1) * 0.6015))
          * L ^ (q * (2 * q - 1)) := by ring
    _ ≤ 795 * L ^ (q * (2 * q - 1)) := mul_le_mul_of_nonneg_right h3 hLa

/-- **The central term in the sliver**: for `log z ≥ 2300`, `σ log z ≥ 1/200000` and
`½ ≤ q ≤ 0.50015`, the central term of `RMF.integral_rpow_Z_le_bottom` is at most
`795(log z)^{q(2q-1)}` (`RMF.sliver_central_arith`, `log(z + 1) ≤ log z + log 2`). -/
lemma sliver_central_le {σ q : ℝ} {z : ℕ} (hz : 2300 ≤ Real.log z)
    (hσ0 : 1 / 200000 ≤ σ * Real.log z) (hq0 : 1 / 2 ≤ q) (hq : q ≤ 50015 / 100000) :
    ((Real.pi / σ + 2 * (Real.exp (2 * (1 - q)
        * (Real.log ((z : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((z : ℝ) + 1) + 34)
        * (1 / Real.log z) ^ 2) - 1) / (1 / Real.log z)) / Real.log z) ^ q * pfFull q z
      ≤ 795 * Real.log z ^ (q * (2 * q - 1)) := by
  have hz1 : (1 : ℝ) < z := by
    by_contra h
    push Not at h
    have : Real.log z ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hL₁0 : 0 ≤ Real.log ((z : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL₁ : Real.log ((z : ℝ) + 1) ≤ Real.log z + 0.6932 := by
    have h2 : (z : ℝ) + 1 ≤ 2 * z := by linarith
    have h3 : Real.log ((z : ℝ) + 1) ≤ Real.log (2 * z) := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have := Real.log_two_lt_d9
    linarith
  exact sliver_central_arith hz hL₁0 hL₁ hσ0 hq0 hq

/-- **The windows' arithmetic in the sliver**: with `0 ≤ W ≤ 2.509` (`(2π)^q`), `S₉ ≤ 12.9289`
(the top windows), `S_r ≤ K₀(hP)c` (the rest, `c` the chaos-weighted sum, `P = (log z)^a`),
`c ≤ π_s + ι` (profile and ineligible windows), `π_s ≤ A(QD·1.254)`, `Pι ≤ 91E`, `K₀h ≤ 0.7772`,
`A ≤ 6.4233`, `Q ≤ 1.682` and `E ≤ 1.015`: `W(S₉ + S_r) ≤ 213 + 26.43PD`. -/
lemma sliver_windows_arith {W S9 Sr K₀ h P cws prof inel A Q D E : ℝ} (hW0 : 0 ≤ W)
    (hW : W ≤ 2.509) (hS9 : S9 ≤ 12.9289) (hSr : Sr ≤ K₀ * (h * P) * cws) (hK₀ : 0 ≤ K₀)
    (hh : 0 ≤ h) (hK : K₀ * h ≤ 0.7772) (hP : 0 ≤ P) (hcws : cws ≤ prof + inel)
    (hprof : prof ≤ A * (Q * D * (627 / 500))) (hinel : P * inel ≤ 91 * E) (hA0 : 0 ≤ A)
    (hA : A ≤ 6.4233) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 1.682) (hD : 0 ≤ D) (hE0 : 0 ≤ E)
    (hE : E ≤ 1.015) :
    W * (S9 + Sr) ≤ 213 + 26.43 * (P * D) := by
  have hKh0 : 0 ≤ K₀ * h := mul_nonneg hK₀ hh
  have hKhP0 : 0 ≤ K₀ * (h * P) := mul_nonneg hK₀ (mul_nonneg hh hP)
  have hPD : 0 ≤ P * D := mul_nonneg hP hD
  -- the rest of the windows
  have h1 : Sr ≤ (K₀ * h) * (A * Q) * (627 / 500) * (P * D) + 91 * ((K₀ * h) * E) :=
    calc Sr ≤ K₀ * (h * P) * cws := hSr
      _ ≤ K₀ * (h * P) * (prof + inel) := mul_le_mul_of_nonneg_left hcws hKhP0
      _ = K₀ * (h * P) * prof + (K₀ * h) * (P * inel) := by ring
      _ ≤ K₀ * (h * P) * (A * (Q * D * (627 / 500))) + (K₀ * h) * (91 * E) :=
          add_le_add (mul_le_mul_of_nonneg_left hprof hKhP0)
            (mul_le_mul_of_nonneg_left hinel hKh0)
      _ = (K₀ * h) * (A * Q) * (627 / 500) * (P * D) + 91 * ((K₀ * h) * E) := by ring
  -- the numerals
  have h2 : (K₀ * h) * (A * Q) ≤ 0.7772 * (6.4233 * 1.682) :=
    mul_le_mul hK (mul_le_mul hA hQ hQ0 (by norm_num)) (mul_nonneg hA0 hQ0) (by norm_num)
  have h3 : (K₀ * h) * E ≤ 0.7772 * 1.015 := mul_le_mul hK hE hE0 (by norm_num)
  have h4 : (K₀ * h) * (A * Q) * (627 / 500) * (P * D)
      ≤ 0.7772 * (6.4233 * 1.682) * (627 / 500) * (P * D) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by norm_num)) hPD
  have h5 : S9 + Sr ≤ 12.9289 + 0.7772 * (6.4233 * 1.682) * (627 / 500) * (P * D)
      + 91 * (0.7772 * 1.015) := by linarith
  have h6 : 0 ≤ 12.9289 + 0.7772 * (6.4233 * 1.682) * (627 / 500) * (P * D)
      + 91 * (0.7772 * 1.015) := by positivity
  calc W * (S9 + Sr) ≤ W * (12.9289 + 0.7772 * (6.4233 * 1.682) * (627 / 500) * (P * D)
        + 91 * (0.7772 * 1.015)) := mul_le_mul_of_nonneg_left h5 hW0
    _ ≤ 2.509 * (12.9289 + 0.7772 * (6.4233 * 1.682) * (627 / 500) * (P * D)
        + 91 * (0.7772 * 1.015)) := mul_le_mul_of_nonneg_right hW h6
    _ ≤ 213 + 26.43 * (P * D) := by linarith

/-- **The windows in the sliver**: for `log z ≥ 2300` and `½ < q ≤ 0.50015`,
`(2π)^q∑_{k<J} RMF.winBotCh q z k ≤ 213 + 26.43(log z)^{q(2q-1)}(2q-1)^{-3/4}`: the nine top
windows at most `12.9289` (`RMF.aboveTS_1`), the rest by the chaos profile
(`RMF.bottomWindows_chaos_clean`, `RMF.chaosWinSum_le_profSum_add`, `RMF.profSum_le_gamma`,
`RMF.chaosB_le`: `1.254A(q(2q-1))^{-3/4}`, `A ≤ 6.4233`) and the at most `91` ineligible ones,
each `≤ e^{97a}(log z)^{-a}` (`RMF.bottom_tail_le`). -/
theorem sliver_windows_le {q : ℝ} {z : ℕ} (hz : 2300 ≤ Real.log z) (hq0 : 1 / 2 < q)
    (hq : q ≤ 50015 / 100000) :
    (2 * Real.pi) ^ q * ∑ k ∈ Finset.range (bottomJ 1 2 z), winBotCh q z k
      ≤ 213 + 26.43 * (Real.log z ^ (q * (2 * q - 1)) * (2 * q - 1) ^ (-(3 / 4 : ℝ))) := by
  have hq1 : q < 1 := by linarith
  have hlz : 0 < Real.log z := by linarith
  have hz1 : (1 : ℝ) < z := by
    by_contra h
    push Not at h
    have : Real.log z ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hz2 : 2 ≤ z := by
    have : 1 < z := by exact_mod_cast hz1
    omega
  have ha : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hδ : 0 < 2 * q - 1 := by linarith
  -- the number of windows
  have hJ1 : Real.log (2 * Real.log z) ≤ (bottomJ 1 2 z : ℝ) := by
    have := Nat.le_ceil (Real.log (2 * Real.log z / 1))
    rw [div_one] at this
    rw [bottomJ]
    simpa using this
  have hJ9 : 9 ≤ bottomJ 1 2 z := by
    have h8 : (8 : ℝ) < Real.log (2 * Real.log z) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := exp_eight_bounds.2
      linarith
    have : (8 : ℝ) < bottomJ 1 2 z := lt_of_lt_of_le h8 hJ1
    exact_mod_cast this
  -- the top windows and the rest
  obtain ⟨htop, hrest⟩ := bottomWindows_chaos_clean hq0 hq1.le hz2 (by linarith)
  have hTS := aboveTS_1 hq0.le (by linarith) z hz
  have hsplit := Finset.sum_range_add_sum_Ico (winBotCh q z) hJ9
  -- the chaos-weighted sum
  have hcws := chaosWinSum_le_profSum_add (N := bottomJ 1 2 z - 8) hq0.le hq1
    (bottom_windows_eligible z)
  have hAu := chaosAhat_le_num hq0.le hq
  have hA0 : 0 ≤ chaosAhat q := chaosAhat_nonneg hq1
  have hprof : profSum (q * (2 * q - 1)) (chaosAhat q) (bottomJ 1 2 z - 8)
      ≤ chaosAhat q * ((q * (2 * q - 1)) ^ (-(3 / 4 : ℝ)) * (627 / 500)) :=
    le_trans (profSum_le_gamma ha hA0 _) (chaosB_le hq0 hq)
  have hsplit34 : (q * (2 * q - 1)) ^ (-(3 / 4 : ℝ))
      = q ^ (-(3 / 4 : ℝ)) * (2 * q - 1) ^ (-(3 / 4 : ℝ)) :=
    Real.mul_rpow (by linarith) hδ.le
  rw [hsplit34] at hprof
  -- the ineligible windows
  have htail := bottom_tail_le (x := (z : ℝ)) hz1 ha.le (z := z) (by linarith)
  have hc32 : 3 / 2 * Real.log z / Real.log z = 3 / 2 := by field_simp
  rw [hc32] at htail
  have h32 : (0 : ℝ) < (3 / 2 : ℝ) ^ (q * (2 * q - 1)) := Real.rpow_pos_of_pos (by norm_num) _
  have hLa : Real.log z ^ (q * (2 * q - 1))
      = Real.exp (q * (2 * q - 1) * Real.log (Real.log z)) := by
    rw [Real.rpow_def_of_pos hlz, mul_comm]
  have hinel : Real.log z ^ (q * (2 * q - 1))
      * ∑ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8), Real.exp (-(q * (2 * q - 1) * m))
      ≤ 91 * Real.exp (97 * (q * (2 * q - 1))) := by
    have h1 : ∑ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8), Real.exp (-(q * (2 * q - 1) * m))
        ≤ 91 * Real.exp (97 * (q * (2 * q - 1)))
          * Real.exp (-(q * (2 * q - 1) * Real.log (Real.log z))) := by
      have e : (3 / 2 : ℝ) ^ (q * (2 * q - 1)) * (91 * Real.exp (97 * (q * (2 * q - 1)))
          * Real.exp (-(q * (2 * q - 1) * Real.log (Real.log z))))
          = 91 * (3 / 2 : ℝ) ^ (q * (2 * q - 1)) * Real.exp (97 * (q * (2 * q - 1)))
            * Real.exp (-(q * (2 * q - 1) * Real.log (Real.log z))) := by ring
      rw [← e] at htail
      exact le_of_mul_le_mul_left htail h32
    have h2 : Real.exp (q * (2 * q - 1) * Real.log (Real.log z))
        * Real.exp (-(q * (2 * q - 1) * Real.log (Real.log z))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hLa]
    calc Real.exp (q * (2 * q - 1) * Real.log (Real.log z))
          * ∑ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8), Real.exp (-(q * (2 * q - 1) * m))
        ≤ Real.exp (q * (2 * q - 1) * Real.log (Real.log z))
          * (91 * Real.exp (97 * (q * (2 * q - 1)))
            * Real.exp (-(q * (2 * q - 1) * Real.log (Real.log z)))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 91 * Real.exp (97 * (q * (2 * q - 1)))
          * (Real.exp (q * (2 * q - 1) * Real.log (Real.log z))
            * Real.exp (-(q * (2 * q - 1) * Real.log (Real.log z)))) := by ring
      _ = 91 * Real.exp (97 * (q * (2 * q - 1))) := by rw [h2, mul_one]
  -- the split windows' scale
  have hscale : (3 / 2 * Real.log z) ^ (q * (2 * q - 1))
      = (3 / 2 : ℝ) ^ (q * (2 * q - 1)) * Real.log z ^ (q * (2 * q - 1)) :=
    Real.mul_rpow (by norm_num) hlz.le
  rw [hscale] at hrest
  have hK₀ : 0 ≤ pfC1 q * omegaClean q :=
    mul_nonneg (Real.exp_pos _).le (omegaClean_nonneg hq1.le)
  have hK := sliver_winConst_le hq0 hq
  rw [← hsplit]
  exact sliver_windows_arith (Real.rpow_nonneg (by positivity) _)
    (sliver_twoPi_rpow_le (by linarith) hq) (le_trans (le_trans htop hTS) (by norm_num)) hrest
    hK₀ h32.le hK (Real.rpow_nonneg hlz.le _) hcws hprof hinel hA0
    (le_trans hAu (by norm_num))
    (Real.rpow_nonneg (by linarith) _) (sliver_rpow_q_le hq0.le)
    (Real.rpow_nonneg hδ.le _) (Real.exp_pos _).le (sliver_exp_tail_le hq0.le hq)

/-- **The far range in the sliver**: `(2·1.195·log z/e^J)^q ≤ 1.195` for `log z ≥ 1`,
`0 ≤ q ≤ 1`, `J = RMF.bottomJ 1 2 z ≥ log(2 log z)`. -/
lemma sliver_far_le {q : ℝ} {z : ℕ} (hz : 1 ≤ Real.log z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (2 * 1.195 / (Real.exp (bottomJ 1 2 z) / Real.log z)) ^ q ≤ 1.195 := by
  have hlz : 0 < Real.log z := by linarith
  have hJ1 : Real.log (2 * Real.log z) ≤ (bottomJ 1 2 z : ℝ) := by
    have := Nat.le_ceil (Real.log (2 * Real.log z / 1))
    rw [div_one] at this
    rw [bottomJ]
    simpa using this
  have hJ : 2 * Real.log z ≤ Real.exp (bottomJ 1 2 z) :=
    calc 2 * Real.log z = Real.exp (Real.log (2 * Real.log z)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (bottomJ 1 2 z) := Real.exp_le_exp.2 hJ1
  have hv : 2 ≤ Real.exp (bottomJ 1 2 z) / Real.log z := by
    rw [le_div_iff₀ hlz]
    linarith
  have hb : 2 * 1.195 / (Real.exp (bottomJ 1 2 z) / Real.log z) ≤ 1.195 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hb0 : 0 ≤ 2 * 1.195 / (Real.exp (bottomJ 1 2 z) / Real.log z) := by positivity
  calc (2 * 1.195 / (Real.exp (bottomJ 1 2 z) / Real.log z)) ^ q
      ≤ (1.195 : ℝ) ^ q := Real.rpow_le_rpow hb0 hb hq0
    _ ≤ (1.195 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
    _ = 1.195 := Real.rpow_one _

/-- The last arithmetic: `E ≤ C + W + F`, `C ≤ 795P`, `W ≤ 213 + 26.43PD`, `F ≤ 1.195`, `P ≥ 1`
and `D ≥ 438` give `E ≤ 33PD`. -/
lemma sliver_total_arith {E C W F P D : ℝ} (hE : E ≤ C + W + F) (hC : C ≤ 795 * P)
    (hW : W ≤ 213 + 26.43 * (P * D)) (hF : F ≤ 1.195) (hP : 1 ≤ P) (hD : 438 ≤ D) :
    E ≤ 33 * P * D := by
  have hPD : P * 438 ≤ P * D := mul_le_mul_of_nonneg_left hD (by linarith)
  have h : E ≤ 33 * (P * D) := by linarith
  calc E ≤ 33 * (P * D) := h
    _ = 33 * P * D := by ring

/-! ### `Z` in the sliver -/

/-- **`Z` in the sliver above `½`.**  For `½ < q ≤ 0.50015`, `log z ≥ 2300` and
`1/200000 ≤ σ log z ≤ 1/160000`, `Z = (log z)⁻¹∫_ℝ‖F_{z+1}(½+σ+it)/(σ+it)‖²dt` has

`E[Z^q] ≤ 33(log z)^{q(2q-1)}(2q - 1)^{-3/4}`:

`RMF.integral_rpow_Z_le_bottom` with the central term `≤ 795(log z)^a` (`RMF.sliver_central_le`),
the windows `≤ 213 + 26.43(log z)^a(2q-1)^{-3/4}` (`RMF.sliver_windows_le`) and the far range
`≤ 1.195` (`RMF.sliver_far_le`), then `(log z)^a ≥ 1`, `(2q-1)^{-3/4} ≥ 438`: at most
`28.73(log z)^a(2q-1)^{-3/4}`. -/
theorem Z_bottom_le_sliver {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {σ q : ℝ} {z : ℕ} (hz : 2300 ≤ Real.log z)
    (hσ0 : 1 / 200000 ≤ σ * Real.log z) (hσ1 : σ * Real.log z ≤ 1 / 160000)
    (hq0 : 1 / 2 < q) (hq : q ≤ 50015 / 100000) :
    (∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (z + 1)
            ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω
          / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 33 * Real.log z ^ (q * (2 * q - 1)) * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
  have hlz : 0 < Real.log z := by linarith
  have hσ : 0 < σ := by
    by_contra h
    push Not at h
    nlinarith
  have hz0 : (0 : ℝ) < z := by
    by_contra h
    push Not at h
    have h0 : (z : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [h0, Real.log_zero] at hz
    linarith
  have hz99 : Real.exp 99 ≤ (z : ℝ) := by
    rw [← Real.exp_log hz0]
    exact Real.exp_le_exp.2 (by linarith)
  have h4 := integral_rpow_Z_le_bottom hX hz99 hσ hσ1 hq0.le (by linarith)
  have hC := sliver_central_le hz hσ0 hq0.le hq
  have hW := sliver_windows_le hz hq0 hq
  have hF := sliver_far_le (z := z) (q := q) (by linarith) (by linarith) (by linarith)
  have hP : 1 ≤ Real.log z ^ (q * (2 * q - 1)) :=
    Real.one_le_rpow (by linarith) (mul_nonneg (by linarith) (by linarith))
  exact sliver_total_arith h4 hC hW hF hP (sliver_delta_rpow_ge hq0 hq)

/-! ### The subtracted term -/

/-- **The subtracted term in the sliver above `½`**: for a Rademacher family, `x > 1` with
`log log x ≥ 8`, `V ≥ 1/160000` and `½ < q ≤ 0.50015`,

`E[J(V/log x)^q] ≤ 33(log x)^q·(log x)^{q(2q-1)}(2q - 1)^{-3/4}`,

`J(σ) = ∫_ℝ‖F_{⌊x⌋+1}(½+σ+it)/(σ+it)‖²dt` as in
`RMF.le_integral_rpow_weightedRademacherSum_of_parseval_explicit`: the shift down to
`σ = 1/(160000 log x)` (`RMF.integral_rpow_lineDiv_le_of_le`), `Z = (log ⌊x⌋)⁻¹J`
(`RMF.integral_rpow_le_rpow_mul_integral_rpow_inv_mul`) and `RMF.Z_bottom_le_sliver` at
`z = ⌊x⌋`, where `log ⌊x⌋ ≥ log x - log 2 ≥ 2300`. -/
theorem integral_rpow_lineDiv_le_subtracted_sliver {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x V q : ℝ} (hx : 1 < x)
    (hΛ : 8 ≤ Real.log (Real.log x)) (hV : 1 / 160000 ≤ V) (hq0 : 1 / 2 < q)
    (hq : q ≤ 50015 / 100000) :
    (∫ ω, (∫ t : ℝ,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
              ((1 / 2 : ℂ) + ((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
            / (((V / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
      ≤ 33 * Real.log x ^ q * Real.log x ^ (q * (2 * q - 1)) * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
  haveI := hX.isProbabilityMeasure
  have hx0 : 0 < x := by linarith
  have hLx : 0 < Real.log x := Real.log_pos hx
  have hLx8 : 2500 ≤ Real.log x := by
    have h1 : Real.exp 8 ≤ Real.log x := by
      rw [← Real.exp_log hLx]
      exact Real.exp_le_exp.2 hΛ
    linarith [exp_eight_bounds.1]
  -- `z = ⌊x⌋`
  have hzx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxz : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hz1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx.le)
    exact_mod_cast this
  have hLxz : Real.log x ≤ Real.log 2 + Real.log (⌊x⌋₊ : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hx0 (by linarith)
  have hlog2 := Real.log_two_lt_d9
  have hLz : 2300 ≤ Real.log (⌊x⌋₊ : ℝ) := by linarith
  have hLzx : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hzx
  have hLz0 : 0 < Real.log (⌊x⌋₊ : ℝ) := by linarith
  have hz2 : 2 ≤ ⌊x⌋₊ := by
    have h2 : (2 : ℝ) ≤ x := by
      by_contra h
      push Not at h
      have : Real.log x < Real.log 2 := Real.log_lt_log hx0 h
      linarith
    exact Nat.le_floor (by exact_mod_cast h2)
  -- the tilt `σ = 1/(160000 log x)`
  have hσ : 0 < 1 / (160000 * Real.log x) := by positivity
  have hσV : 1 / (160000 * Real.log x) ≤ V / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) hLx]
    nlinarith
  have hσz1 : 1 / (160000 * Real.log x) * Real.log (⌊x⌋₊ : ℝ) ≤ 1 / 160000 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hσz0 : 1 / 200000 ≤ 1 / (160000 * Real.log x) * Real.log (⌊x⌋₊ : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  -- the shift down, the normalisation and `Z`
  have h1 := integral_rpow_lineDiv_le_of_le hX (N := ⌊x⌋₊) hz2 hσ hσV (q := q) (by linarith)
  have h2 := integral_rpow_le_rpow_mul_integral_rpow_inv_mul (μ := μ)
    (J := fun ω => ∫ t : ℝ,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1)
          ((1 / 2 : ℂ) + ((1 / (160000 * Real.log x) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω
        / (((1 / (160000 * Real.log x) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
    hLz0 hLzx (by linarith : (0 : ℝ) ≤ q) (fun ω => integral_nonneg fun t => sq_nonneg _)
  have h3 := Z_bottom_le_sliver hX (z := ⌊x⌋₊) (σ := 1 / (160000 * Real.log x)) hLz hσz0 hσz1
    hq0 hq
  have ha0 : 0 ≤ q * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
  have h4 : Real.log (⌊x⌋₊ : ℝ) ^ (q * (2 * q - 1)) ≤ Real.log x ^ (q * (2 * q - 1)) :=
    Real.rpow_le_rpow hLz0.le hLzx ha0
  have hD0 : 0 ≤ (2 * q - 1) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hLq : 0 ≤ Real.log x ^ q := Real.rpow_nonneg hLx.le _
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ Real.log x ^ q * (33 * Real.log (⌊x⌋₊ : ℝ) ^ (q * (2 * q - 1))
          * (2 * q - 1) ^ (-(3 / 4 : ℝ))) := mul_le_mul_of_nonneg_left h3 hLq
    _ ≤ Real.log x ^ q * (33 * Real.log x ^ (q * (2 * q - 1))
          * (2 * q - 1) ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h4 (by norm_num)) hD0) hLq
    _ = 33 * Real.log x ^ q * Real.log x ^ (q * (2 * q - 1)) * (2 * q - 1) ^ (-(3 / 4 : ℝ)) := by
        ring

end RMF
