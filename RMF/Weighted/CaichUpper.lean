/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.CaichChaos
import RMF.Reduction.Upper
import RMF.Reduction.Suppliers
import RMF.Probability.RademacherChaosMoment

/-!
# Caich's upper bound, Rademacher case: the assembly

R. Caich, *Random multiplicative functions and typical size of character in short intervals*
(arXiv:2402.06426), Theorem 1.1, Rademacher case: for `x ≥ x₀`, `2 ≤ y ≤ x` and `0 ≤ q ≤ 1`,

`E|M(x,y)|^{2q} ≪ (y·min{1, θ√(log log x) + (1 + (1-q)√(log log x))⁻¹})^q`,  `x/y = (log x)^θ`,

with `(1 + (1-q)√(log log x))⁻¹` in place of Caich's `1/((1-q)√(log log x))`.  The route: the
short-interval reduction (`RMF.integral_rpow_shortSum_le_sqfree`) at the Harper cutoff
`y₀ = ⌊harperCutoff x⌋₊` and `H = y`; the scales
(`RMF.integral_rpow_dilatedLineIntegral_le_scales_sqfree`) at `λ = 1 + y/x` and `M₀ = x/y`, with
`2^J ≥ 1 + √(log log x)`; on each scale the unit window and the long range
(`RMF.exists_const_integral_rpow_lineMassIoc_le_rademacher`).  Three branches: `log(x/y) > √Λ`,
where the `min` is `1` and orthogonality suffices; `q ≥ 2/3` with `log(x/y) ≤ √Λ`, the main
branch; and `q < 2/3`, by Hölder from `q = 2/3`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The integer cutoff, the window level, and the error budget -/

/-- **The integer cutoff `y₀ = ⌊harperCutoff x⌋₊`**, in the four forms the assembly reads, for
`L = log log x ≥ 36`: `y₀ ≥ 4`, `log x/(2L²) ≤ log y₀ ≤ log x/L²`, and `log log y₀ ≥ L/8`.  The
lower bounds are `harperCutoff x ≤ y₀²` and `RMF.loglog_harperCutoff_ge`. -/
lemma floor_harperCutoff_bounds {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    4 ≤ ⌊harperCutoff x⌋₊
      ∧ Real.log x / (2 * Real.log (Real.log x) ^ 2) ≤ Real.log (⌊harperCutoff x⌋₊ : ℝ)
      ∧ Real.log (⌊harperCutoff x⌋₊ : ℝ) ≤ Real.log x / Real.log (Real.log x) ^ 2
      ∧ Real.log (Real.log x) / 8 ≤ Real.log (Real.log (⌊harperCutoff x⌋₊ : ℝ)) := by
  obtain ⟨-, -, hL36⟩ := harper_regime hx
  have hY36 : Real.exp 36 ≤ harperCutoff x := exp_le_harperCutoff hx
  have h37 : (37 : ℝ) ≤ Real.exp 36 := by linarith [Real.add_one_le_exp (36 : ℝ)]
  have hY0 : (0 : ℝ) < harperCutoff x := by linarith
  have hfl4 : 4 ≤ ⌊harperCutoff x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hy4 : (4 : ℝ) ≤ (⌊harperCutoff x⌋₊ : ℝ) := by exact_mod_cast hfl4
  have hyY : (⌊harperCutoff x⌋₊ : ℝ) ≤ harperCutoff x := Nat.floor_le hY0.le
  have hsub : harperCutoff x - 1 < (⌊harperCutoff x⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hsq : harperCutoff x ≤ (⌊harperCutoff x⌋₊ : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hy4 (by linarith : (0 : ℝ) ≤ (⌊harperCutoff x⌋₊ : ℝ))]
  have hlogy0 : 0 < Real.log (⌊harperCutoff x⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogyY : Real.log (⌊harperCutoff x⌋₊ : ℝ) ≤ Real.log (harperCutoff x) :=
    Real.log_le_log (by linarith) hyY
  have hlog2 : Real.log (harperCutoff x) ≤ 2 * Real.log (⌊harperCutoff x⌋₊ : ℝ) := by
    have h := Real.log_le_log hY0 hsq
    rwa [Real.log_pow] at h
  have hlogY0 : 0 < Real.log (harperCutoff x) := lt_of_lt_of_le hlogy0 hlogyY
  refine ⟨hfl4, ?_, by rw [← log_harperCutoff x]; exact hlogyY, ?_⟩
  · have h : Real.log x / (2 * Real.log (Real.log x) ^ 2) = Real.log (harperCutoff x) / 2 := by
      rw [log_harperCutoff x]; ring
    rw [h]; linarith
  · have hLY : Real.log (Real.log x) / 4 ≤ Real.log (Real.log (harperCutoff x)) :=
      loglog_harperCutoff_ge hx
    have h1 : Real.log (Real.log (harperCutoff x) / 2)
        ≤ Real.log (Real.log (⌊harperCutoff x⌋₊ : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (Real.log (harperCutoff x) / 2)
        = Real.log (Real.log (harperCutoff x)) - Real.log 2 :=
      Real.log_div hlogY0.ne' (by norm_num)
    have hlog2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith

/-- **The window level below `log y`.**  For `1 ≤ M` with `2M ≤ log y` and `A = |log(4/c)|`, the
level `RMF.harperWindowLevel c (M - 1) = max 0 (10 log((4/c)·log 2M))` is at most
`10A + 10 + 10 log M`, and at most `log log y / 3` once `√(log log y) ≥ 60 + 30A`: the first by
`log log 2M ≤ log 2M ≤ 1 + log M`, the second by `log log 2M ≤ log log log y ≤ 2√(log log y)`. -/
lemma harperWindowLevel_le_of_le_log {c M y : ℝ} (hc : 0 < c) (hM : 1 ≤ M)
    (hMy : 2 * M ≤ Real.log y) :
    harperWindowLevel c (M - 1) ≤ 10 * |Real.log (4 / c)| + 10 + 10 * Real.log M
      ∧ (60 + 30 * |Real.log (4 / c)| ≤ Real.sqrt (Real.log (Real.log y)) →
          harperWindowLevel c (M - 1) ≤ Real.log (Real.log y) / 3) := by
  have hM0 : 0 < M := by linarith
  have hl2M : 0 < Real.log (2 * M) := Real.log_pos (by linarith)
  have hc4 : 0 < 4 / c := div_pos (by norm_num) hc
  have hlevel : harperWindowLevel c (M - 1)
      = max 0 (10 * (Real.log (4 / c) + Real.log (Real.log (2 * M)))) := by
    rw [harperWindowLevel, show 2 * (M - 1 + 1) = 2 * M by ring,
      Real.log_mul hc4.ne' hl2M.ne']
  have habs : Real.log (4 / c) ≤ |Real.log (4 / c)| := le_abs_self _
  have habs0 : 0 ≤ |Real.log (4 / c)| := abs_nonneg _
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  rw [hlevel]
  refine ⟨max_le (by linarith) ?_, fun hsq => max_le ?_ ?_⟩
  · have hll : Real.log (Real.log (2 * M)) ≤ Real.log (2 * M) := by
      linarith [Real.log_le_sub_one_of_pos hl2M]
    have h2 : Real.log (2 * M) = Real.log 2 + Real.log M :=
      Real.log_mul (by norm_num) hM0.ne'
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  · have hML : Real.log (2 * M) ≤ Real.log (Real.log y) := Real.log_le_log (by linarith) hMy
    linarith
  · have hML : Real.log (2 * M) ≤ Real.log (Real.log y) := Real.log_le_log (by linarith) hMy
    have hL0 : 0 < Real.log (Real.log y) := lt_of_lt_of_le hl2M hML
    have hmono : Real.log (Real.log (2 * M)) ≤ Real.log (Real.log (Real.log y)) :=
      Real.log_le_log hl2M hML
    have hlogL : Real.log (Real.log (Real.log y)) ≤ 2 * Real.sqrt (Real.log (Real.log y)) :=
      log_le_two_sqrt hL0
    have hs2 : Real.sqrt (Real.log (Real.log y)) ^ 2 = Real.log (Real.log y) :=
      Real.sq_sqrt hL0.le
    have hs1 : 1 ≤ Real.sqrt (Real.log (Real.log y)) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg (Real.log (Real.log y))),
      mul_le_mul_of_nonneg_left hs1 habs0]

/-- **The error budget**: `12 L³ e^{2√L} ≤ e^L` once `L ≥ 100`, since `12L³ ≤ L⁴ = e^{4 log L}` and
`4 log L + 2√L ≤ 10√L ≤ L`. -/
lemma twelve_mul_cube_mul_exp_two_sqrt_le_exp {L : ℝ} (hL : 100 ≤ L) :
    12 * L ^ 3 * Real.exp (2 * Real.sqrt L) ≤ Real.exp L := by
  have hL0 : 0 < L := by linarith
  have hs10 : (10 : ℝ) ≤ Real.sqrt L :=
    (Real.le_sqrt (by norm_num) hL0.le).2 (by norm_num; linarith)
  have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
  have hL4 : L ^ 4 = Real.exp (4 * Real.log L) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hL0]
  have h12 : 12 * L ^ 3 ≤ L ^ 4 := by
    have h3 : 0 ≤ L ^ 3 := by positivity
    nlinarith [mul_nonneg h3 (show (0 : ℝ) ≤ L - 12 by linarith)]
  calc 12 * L ^ 3 * Real.exp (2 * Real.sqrt L)
      ≤ L ^ 4 * Real.exp (2 * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right h12 (Real.exp_pos _).le
    _ = Real.exp (4 * Real.log L + 2 * Real.sqrt L) := by rw [hL4, ← Real.exp_add]
    _ ≤ Real.exp L := Real.exp_le_exp.2 (by
        nlinarith [mul_le_mul_of_nonneg_right hs10 (Real.sqrt_nonneg L)])

/-! ### The mass on `(0, M]`: the unit window and the long range -/

/-- **The mass on `(0, M]`, normalised**, for `y ≥ x₀`, `0 ≤ q ≤ 1` and `1 ≤ M` with `2M ≤ log y`:
`E[((M log y)⁻¹ S(M))^q] ≤ K((1 + (1-q)√L)^{-q} + ((1 + log M)/√L)^q)`,  `L = log log y`,
`S = RMF.lineMass`.  `S(M) = S(1) + S(1, M]`; `(M log y)⁻¹S(1)` is at most the unit-window chaos
(`RMF.exists_const_integral_chaosUnitShift_rpow_le_loglog_rademacher`), and the rest is
`RMF.exists_const_integral_rpow_lineMassIoc_le_rademacher`, whose window cut and level raise
`RMF.harperWindowLevel_le_of_le_log` supplies at every such height. -/
theorem exists_const_integral_rpow_lineMass_le_rademacher :
    ∃ K x₀ : ℝ, 0 < K ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (y : ℕ) (M q : ℝ), x₀ ≤ (y : ℝ) → 1 ≤ M → 2 * M ≤ Real.log y → 0 ≤ q → q ≤ 1 →
          ∫ ω, ((M * Real.log y)⁻¹
              * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q ∂ν
            ≤ K * ((1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)
              + ((1 + Real.log M) / Real.sqrt (Real.log (Real.log y))) ^ q) := by
  obtain ⟨D₀, c, K₄, x₄, -, hc, hK₄, H₄⟩ :=
    exists_const_integral_rpow_lineMassIoc_le_rademacher (Ω := Ω)
  obtain ⟨xu, Cu, hCu, Hu⟩ :=
    exists_const_integral_chaosUnitShift_rpow_le_loglog_rademacher (Ω := Ω) 0 le_rfl
  have hA0 : 0 ≤ |Real.log (4 / c)| := abs_nonneg _
  have hK₀ : 0 ≤ Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  refine ⟨Cu + 2 * K₄ + K₄ * (Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11)),
    max (max x₄ xu) (Real.exp (Real.exp (max (2 * (D₀ : ℝ) + 2)
      ((60 + 30 * |Real.log (4 / c)|) ^ 2)))),
    by have := mul_nonneg hK₄.le hK₀; linarith, ?_⟩
  -- the closing algebra, stated while the context is still small
  have halg : ∀ P R : ℝ, 0 ≤ P → 0 ≤ R →
      Cu * P + K₄ * (2 * P + Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11) * R)
        ≤ (Cu + 2 * K₄ + K₄ * (Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11))) * (P + R) := by
    intro P R hP hR
    nlinarith [mul_nonneg hCu.le hR, mul_nonneg hK₄.le hR, mul_nonneg (mul_nonneg hK₄.le hK₀) hP]
  intro Y ν hY y M q hy hM hMy hq0 hq1
  haveI := hY.isProbabilityMeasure
  have hy₄ : x₄ ≤ (y : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyu : xu ≤ (y : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyL : Real.exp (Real.exp (max (2 * (D₀ : ℝ) + 2) ((60 + 30 * |Real.log (4 / c)|) ^ 2)))
      ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hy0 : (0 : ℝ) < (y : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hyL
  have hlogy : Real.exp (max (2 * (D₀ : ℝ) + 2) ((60 + 30 * |Real.log (4 / c)|) ^ 2))
      ≤ Real.log (y : ℝ) := (Real.le_log_iff_exp_le hy0).2 hyL
  have hlogy0 : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlogy
  have hL : max (2 * (D₀ : ℝ) + 2) ((60 + 30 * |Real.log (4 / c)|) ^ 2)
      ≤ Real.log (Real.log (y : ℝ)) := (Real.le_log_iff_exp_le hlogy0).2 hlogy
  have hLD : 2 * (D₀ : ℝ) + 2 ≤ Real.log (Real.log (y : ℝ)) := le_trans (le_max_left _ _) hL
  have hLA : (60 + 30 * |Real.log (4 / c)|) ^ 2 ≤ Real.log (Real.log (y : ℝ)) :=
    le_trans (le_max_right _ _) hL
  have hD0 : (0 : ℝ) ≤ (D₀ : ℝ) := Nat.cast_nonneg _
  have hL0 : 0 < Real.log (Real.log (y : ℝ)) := by linarith
  have hsL : 60 + 30 * |Real.log (4 / c)| ≤ Real.sqrt (Real.log (Real.log (y : ℝ))) :=
    (Real.le_sqrt (by linarith) hL0.le).2 hLA
  have hsL0 : 0 < Real.sqrt (Real.log (Real.log (y : ℝ))) := Real.sqrt_pos.2 hL0
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by
    have h := (Real.le_log_iff_exp_le hy0).1 (by linarith : (2 : ℝ) ≤ Real.log (y : ℝ))
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  -- the window level: the long range's cut, and the raise `k ≪ 1 + log M`
  have hlev := harperWindowLevel_le_of_le_log hc hM hMy
  have hcut : harperWindowLevel c (M - 1) ≤ Real.log (Real.log (y : ℝ)) / 3 := hlev.2 hsL
  have hk : ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ)
      ≤ 10 * |Real.log (4 / c)| + 11 + 10 * Real.log M := by
    have hsub : harperDwExp D₀ c (M - 1) - D₀ = ⌈harperWindowLevel c (M - 1)⌉₊ := by
      rw [harperDwExp]; omega
    rw [hsub]
    have h := (Nat.ceil_lt_add_one (harperWindowLevel_nonneg c (M - 1))).le
    linarith [hlev.1]
  -- the count `t = ⌊L⌋ - D₀ ≥ L/2`
  have hD₀L : (D₀ : ℝ) ≤ Real.log (Real.log (y : ℝ)) := by linarith
  have htR : (harperBlockCount D₀ (y : ℝ) : ℝ)
      = (⌊Real.log (Real.log (y : ℝ))⌋₊ : ℝ) - (D₀ : ℝ) := cast_harperBlockCount hD₀L
  have hfl : Real.log (Real.log (y : ℝ)) - 1 < (⌊Real.log (Real.log (y : ℝ))⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have ht2 : Real.log (Real.log (y : ℝ)) ≤ 2 * (harperBlockCount D₀ (y : ℝ) : ℝ) := by
    rw [htR]; linarith
  have hst : Real.sqrt (Real.log (Real.log (y : ℝ)))
      ≤ Real.sqrt 2 * Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt ht2
  have hst0 : 0 < Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ) := by
    refine Real.sqrt_pos.2 ?_
    rw [htR]; linarith
  -- pointwise: the unit window and the long range
  have hcc0 : 0 ≤ (M * Real.log (y : ℝ))⁻¹ :=
    inv_nonneg.2 (mul_nonneg (by linarith) hlogy0.le)
  have hW0 : ∀ ω, 0 ≤ (M * Real.log (y : ℝ))⁻¹
      * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω :=
    fun ω => mul_nonneg hcc0 (lineMassIoc_nonneg _ _ _ _)
  have hC0 : ∀ ω,
      0 ≤ chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) (y : ℝ) 0 ω :=
    fun ω => chaosUnitShift_nonneg hy2 ω
  have hpt : ∀ ω, ((M * Real.log (y : ℝ))⁻¹
      * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q
      ≤ chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) (y : ℝ) 0 ω ^ q
        + ((M * Real.log (y : ℝ))⁻¹
          * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q := by
    intro ω
    have heq : chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) (y : ℝ) 0 ω
        = (Real.log (y : ℝ))⁻¹
          * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) 1 ω := by
      rw [chaosUnitShift, lineMass, Nat.floor_natCast,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hS0 := lineMass_nonneg (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) 1 ω
    have hinv : (M * Real.log (y : ℝ))⁻¹ ≤ (Real.log (y : ℝ))⁻¹ :=
      inv_anti₀ hlogy0 (le_mul_of_one_le_left hlogy0.le hM)
    have hsplit : (M * Real.log (y : ℝ))⁻¹
        * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω
        ≤ chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) (y : ℝ) 0 ω
          + (M * Real.log (y : ℝ))⁻¹
            * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω := by
      rw [lineMass_eq_add_lineMassIoc_sqfree (X := Y) (y + 1) hM ω, mul_add, heq]
      have := mul_le_mul_of_nonneg_right hinv hS0
      linarith
    have hZ0 : 0 ≤ (M * Real.log (y : ℝ))⁻¹
        * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω :=
      mul_nonneg hcc0 (lineMass_nonneg _ _ _ _)
    exact le_trans (Real.rpow_le_rpow hZ0 hsplit hq0)
      (Real.rpow_add_le_add_rpow (hC0 ω) (hW0 ω) hq0 hq1)
  have hWi : Integrable (fun ω => (M * Real.log (y : ℝ))⁻¹
      * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ν := by
    have h := (integrable_restrictedLineMassIoc_sqfree hY (y + 1) M (fun _ => Set.univ)
      (fun _ => MeasurableSet.univ)
      (by simp only [Set.mem_univ, Set.setOf_true]; exact MeasurableSet.univ)).const_mul
        (M * Real.log (y : ℝ))⁻¹
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [lineMassIoc_eq_restricted_univ]
  have hWqi := integrable_rpow_of_integrable hWi (Filter.Eventually.of_forall hW0) hq0 hq1
  have hCqi := integrable_rpow_of_integrable
    (integrable_chaosUnitShift_rademacher hY (y : ℝ) 0 (by norm_num))
    (Filter.Eventually.of_forall hC0) hq0 hq1
  have hint : (∫ ω, ((M * Real.log (y : ℝ))⁻¹
      * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q ∂ν)
      ≤ (∫ ω, chaosUnitShift (fun ω => squarefreeExtension fun p => Y p ω) (y : ℝ) 0 ω ^ q ∂ν)
        + ∫ ω, ((M * Real.log (y : ℝ))⁻¹
          * lineMassIoc (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q ∂ν := by
    rw [← integral_add hCqi hWqi]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (mul_nonneg hcc0 (lineMass_nonneg _ _ _ _)) q)
      (hCqi.add hWqi) (Filter.Eventually.of_forall hpt)
  -- the two moments, and the passage from the count to `L`
  have hU := Hu Y ν hY (y : ℝ) 0 0 q hyu le_rfl le_rfl le_rfl (by simp) hq0 hq1
  have h4 := H₄ Y ν hY y M q hy₄ hM hq0 hq1 hcut
  have htarget : (1 + (1 - q) * Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ)) ^ (-q)
      ≤ 2 * (1 + (1 - q) * Real.sqrt (Real.log (Real.log (y : ℝ)))) ^ (-q) :=
    rpow_neg_target_le_of_sq_le (by norm_num) (by norm_num; linarith) hq0 hq1
  have hs2 : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hshift : ((Real.log M / 2 + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
      / Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ)) ^ q
      ≤ Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11)
        * ((1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ)))) ^ q := by
    have hnum0 : 0 ≤ Real.log M / 2 + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ) :=
      add_nonneg (by linarith) (Nat.cast_nonneg _)
    have hnum : Real.log M / 2 + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ)
        ≤ (10 * |Real.log (4 / c)| + 11) * (1 + Real.log M) := by
      have h11 : 11 * Real.log M ≤ (10 * |Real.log (4 / c)| + 11) * Real.log M :=
        mul_le_mul_of_nonneg_right (by linarith) hlogM
      rw [mul_add, mul_one]
      linarith
    have hbase : (Real.log M / 2 + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
        / Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ)
        ≤ Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11)
          * ((1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ)))) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hst0 hsL0]
      have h := mul_le_mul hnum hst (Real.sqrt_nonneg _)
        (mul_nonneg (by linarith) (by linarith))
      linarith
    have hR0 : 0 ≤ (1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ))) :=
      div_nonneg (by linarith) hsL0.le
    calc ((Real.log M / 2 + ((harperDwExp D₀ c (M - 1) - D₀ : ℕ) : ℝ))
          / Real.sqrt (harperBlockCount D₀ (y : ℝ) : ℝ)) ^ q
        ≤ (Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11)
          * ((1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ))))) ^ q :=
          Real.rpow_le_rpow (div_nonneg hnum0 hst0.le) hbase hq0
      _ = (Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11)) ^ q
          * ((1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ)))) ^ q :=
          Real.mul_rpow hK₀ hR0
      _ ≤ Real.sqrt 2 * (10 * |Real.log (4 / c)| + 11)
          * ((1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ)))) ^ q :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_self_of_one_le (one_le_mul_of_one_le_of_one_le hs2 (by linarith)) hq1)
            (Real.rpow_nonneg hR0 _)
  have hP0 : 0 ≤ (1 + (1 - q) * Real.sqrt (Real.log (Real.log (y : ℝ)))) ^ (-q) :=
    Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg (sub_nonneg.2 hq1) hsL0.le)) _
  have hR0 : 0 ≤ ((1 + Real.log M) / Real.sqrt (Real.log (Real.log (y : ℝ)))) ^ q :=
    Real.rpow_nonneg (div_nonneg (by linarith) hsL0.le) _
  refine le_trans hint (le_trans (add_le_add hU (le_trans h4 (mul_le_mul_of_nonneg_left
    (add_le_add htarget hshift) hK₄.le))) ?_)
  exact halg _ _ hP0 hR0

/-! ### All scales at once -/

/-- **The weight of scale `j`**: `((2^j)⁻¹)^q·(j + 2)^q ≤ 2·((3/4)^{2/3})^j` for `2/3 ≤ q ≤ 1`, from
`(j + 2)·2^j ≤ 2·3^j`. -/
lemma rpow_inv_two_pow_mul_rpow_le {q : ℝ} (hq : 2 / 3 ≤ q) (hq1 : q ≤ 1) (j : ℕ) :
    (((2 : ℝ) ^ j)⁻¹) ^ q * ((j : ℝ) + 2) ^ q ≤ 2 * ((3 / 4 : ℝ) ^ (2 / 3 : ℝ)) ^ j := by
  have hq0 : 0 ≤ q := by linarith
  have hnat : ∀ n : ℕ, (n + 2) * 2 ^ n ≤ 2 * 3 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      calc (k + 1 + 2) * 2 ^ (k + 1) = (2 * (k + 3)) * 2 ^ k := by ring
        _ ≤ (3 * (k + 2)) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
        _ = 3 * ((k + 2) * 2 ^ k) := by ring
        _ ≤ 3 * (2 * 3 ^ k) := Nat.mul_le_mul_left _ ih
        _ = 2 * 3 ^ (k + 1) := by ring
  have hreal : ((j : ℝ) + 2) * 2 ^ j ≤ 2 * 3 ^ j := by exact_mod_cast hnat j
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
  have hbase : ((2 : ℝ) ^ j)⁻¹ * ((j : ℝ) + 2) ≤ 2 * (3 / 4 : ℝ) ^ j := by
    rw [inv_mul_le_iff₀ h2j]
    refine le_of_mul_le_mul_right ?_ h2j
    have h3 : (3 : ℝ) ^ j = 2 ^ j * 2 ^ j * (3 / 4) ^ j := by
      rw [← mul_pow, ← mul_pow]; norm_num
    calc ((j : ℝ) + 2) * 2 ^ j ≤ 2 * 3 ^ j := hreal
      _ = 2 ^ j * (2 * (3 / 4 : ℝ) ^ j) * 2 ^ j := by rw [h3]; ring
  have hr : (3 / 4 : ℝ) ^ q ≤ (3 / 4 : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hq
  have hpowq : ((3 / 4 : ℝ) ^ j) ^ q = ((3 / 4 : ℝ) ^ q) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 4),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 4), mul_comm]
  have h2q : (2 : ℝ) ^ q ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hq1
  have h34j : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ j := by positivity
  calc (((2 : ℝ) ^ j)⁻¹) ^ q * ((j : ℝ) + 2) ^ q
      = (((2 : ℝ) ^ j)⁻¹ * ((j : ℝ) + 2)) ^ q :=
        (Real.mul_rpow (inv_nonneg.2 h2j.le) hj0).symm
    _ ≤ (2 * (3 / 4 : ℝ) ^ j) ^ q :=
        Real.rpow_le_rpow (mul_nonneg (inv_nonneg.2 h2j.le) hj0) hbase hq0
    _ = 2 ^ q * ((3 / 4 : ℝ) ^ q) ^ j := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) h34j, hpowq]
    _ ≤ 2 * ((3 / 4 : ℝ) ^ (2 / 3 : ℝ)) ^ j :=
        mul_le_mul h2q (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hr j)
          (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _) (by norm_num)

/-- **The scales sum to a constant**: `∑_{j<J} ((2^j)⁻¹)^q·(j + 2)^q ≤ 2(1 - (3/4)^{2/3})⁻¹` for
`2/3 ≤ q ≤ 1`, uniformly in `J`. -/
lemma sum_rpow_inv_two_pow_mul_rpow_le {q : ℝ} (hq : 2 / 3 ≤ q) (hq1 : q ≤ 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, (((2 : ℝ) ^ j)⁻¹) ^ q * ((j : ℝ) + 2) ^ q
      ≤ 2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹ := by
  have hr0 : 0 ≤ (3 / 4 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 / 4 : ℝ) ^ (2 / 3 : ℝ) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  calc ∑ j ∈ Finset.range J, (((2 : ℝ) ^ j)⁻¹) ^ q * ((j : ℝ) + 2) ^ q
      ≤ ∑ j ∈ Finset.range J, 2 * ((3 / 4 : ℝ) ^ (2 / 3 : ℝ)) ^ j :=
        Finset.sum_le_sum fun j _ => rpow_inv_two_pow_mul_rpow_le hq hq1 j
    _ = 2 * ∑ j ∈ Finset.range J, ((3 / 4 : ℝ) ^ (2 / 3 : ℝ)) ^ j := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0 hr1
        rwa [pow_zero, ← Finset.range_eq_Ico, one_div] at h

/-- **The dilated line integral over all scales.**  For `y ≥ x₀`, `1 ≤ λ ≤ 2`, `1 ≤ δ` with
`log λ ≤ δ⁻¹`, `2/3 ≤ q ≤ 1` and `2·(2^J δ) ≤ log y`, with `I = (2π)⁻¹·RMF.dilatedLineIntegral`
at `λ` and `L = log log y`,
`E[I^q] ≤ K (log y/δ)^q ((1 + (1-q)√L)^{-q} + ((1 + log δ)/√L)^q + ((2^J)⁻¹)^q)`: each scale
by `RMF.exists_const_integral_rpow_lineMass_le_rademacher`, summed by
`RMF.sum_rpow_inv_two_pow_mul_rpow_le`; the far tail by Mertens. -/
theorem exists_const_integral_rpow_dilatedLineIntegral_le_rademacher :
    ∃ K x₀ : ℝ, 0 < K ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (y : ℕ) (l δ q : ℝ) (J : ℕ), x₀ ≤ (y : ℝ) → 1 ≤ l → l ≤ 2 → Real.log l ≤ δ⁻¹ →
          1 ≤ δ → 2 / 3 ≤ q → q ≤ 1 → 2 * (2 ^ J * δ) ≤ Real.log y →
          ∫ ω, ((2 * Real.pi)⁻¹ * dilatedLineIntegral
              (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) l ω) ^ q ∂ν
            ≤ K * (Real.log y / δ) ^ q
              * ((1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)
                + ((1 + Real.log δ) / Real.sqrt (Real.log (Real.log y))) ^ q
                + (((2 : ℝ) ^ J)⁻¹) ^ q) := by
  obtain ⟨KU, xU, hKU, HU⟩ := exists_const_integral_rpow_lineMass_le_rademacher (Ω := Ω)
  obtain ⟨CM, hCM, hMert⟩ := exists_const_inv_log_mul_integral_normSq_le_rademacher
  have hr1 : (3 / 4 : ℝ) ^ (2 / 3 : ℝ) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hKs : 0 ≤ 2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.2 (by linarith))
  have hm0 : (1 : ℝ) ≤ max 1 ((2 * Real.pi)⁻¹ * 4) := le_max_left _ _
  have hm1 : (1 : ℝ) ≤ max 1 ((2 * Real.pi)⁻¹ * 28) := le_max_left _ _
  have hm2 : (1 : ℝ) ≤ max 1 ((2 * Real.pi)⁻¹ * 14 * CM) := le_max_left _ _
  -- the closing algebra, while the context is small
  have halg : ∀ B P R T : ℝ, 0 ≤ B → 0 ≤ P → 0 ≤ R → 0 ≤ T →
      max 1 ((2 * Real.pi)⁻¹ * 4) * KU * B * (P + R)
        + max 1 ((2 * Real.pi)⁻¹ * 28) * KU * B * (P + R) * (2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹)
        + max 1 ((2 * Real.pi)⁻¹ * 14 * CM) * B * T
      ≤ (max 1 ((2 * Real.pi)⁻¹ * 4) * KU
          + max 1 ((2 * Real.pi)⁻¹ * 28) * KU * (2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹)
          + max 1 ((2 * Real.pi)⁻¹ * 14 * CM)) * B * (P + R + T) := by
    intro B P R T hB hP hR hT
    have h1 : 0 ≤ max 1 ((2 * Real.pi)⁻¹ * 4) * KU * B * T :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hKU.le) hB) hT
    have h2 : 0 ≤ max 1 ((2 * Real.pi)⁻¹ * 28) * KU * (2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹)
        * B * T :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hKU.le) hKs) hB) hT
    have h3 : 0 ≤ max 1 ((2 * Real.pi)⁻¹ * 14 * CM) * B * (P + R) :=
      mul_nonneg (mul_nonneg (by linarith) hB) (add_nonneg hP hR)
    nlinarith [h1, h2, h3]
  have hKpos : 0 < max 1 ((2 * Real.pi)⁻¹ * 4) * KU
      + max 1 ((2 * Real.pi)⁻¹ * 28) * KU * (2 * (1 - (3 / 4 : ℝ) ^ (2 / 3 : ℝ))⁻¹)
      + max 1 ((2 * Real.pi)⁻¹ * 14 * CM) := by
    have h1 := mul_pos (lt_of_lt_of_le one_pos hm0) hKU
    have h2 := mul_nonneg (mul_nonneg (le_trans zero_le_one hm1) hKU.le) hKs
    linarith
  refine ⟨_, max xU 2, hKpos, ?_⟩
  intro Y ν hY y l δ q J hy hl1 hl2 hlδ hδ hq23 hq1 hJ
  haveI := hY.isProbabilityMeasure
  have hq0 : 0 < q := by linarith
  have hδ0 : 0 < δ := by linarith
  have hδne : δ ≠ 0 := hδ0.ne'
  have hyU : xU ≤ (y : ℝ) := le_trans (le_max_left _ _) hy
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hlogy0 : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlogδ : 0 ≤ Real.log δ := Real.log_nonneg hδ
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hB0 : 0 ≤ Real.log (y : ℝ) / δ := div_nonneg hlogy0.le hδ0.le
  have hBq : 0 ≤ (Real.log (y : ℝ) / δ) ^ q := Real.rpow_nonneg hB0 _
  have hpi0 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  obtain ⟨sL, hsLdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log (Real.log (y : ℝ))) := ⟨_, rfl⟩
  have hsL0 : 0 ≤ sL := by rw [hsLdef]; exact Real.sqrt_nonneg _
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (1 + (1 - q) * sL) ^ (-q) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg (sub_nonneg.2 hq1) hsL0)) _
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ((1 + Real.log δ) / sL) ^ q := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRdef]; exact Real.rpow_nonneg (div_nonneg (by linarith) hsL0) _
  have hT0 : 0 ≤ (((2 : ℝ) ^ J)⁻¹) ^ q := Real.rpow_nonneg (inv_nonneg.2 (by positivity)) _
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = ∫ ω, ‖randomEulerProduct
      (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) (shiftLine 0 0) ω‖ ^ 2 ∂ν :=
    ⟨_, rfl⟩
  have hC3 := integral_rpow_dilatedLineIntegral_le_scales_sqfree hY (y + 1) hq0 hq1 hl1 hl2 hδ0 J
  rw [← hEdef] at hC3
  rw [← hsLdef, ← hPdef, ← hRdef]
  -- each scale, normalised
  have hscale : ∀ M : ℝ, 1 ≤ M → 2 * M ≤ Real.log (y : ℝ) →
      ∫ ω, lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω ^ q ∂ν
        ≤ (M * Real.log (y : ℝ)) ^ q * (KU * (P + ((1 + Real.log M) / sL) ^ q)) := by
    intro M hM hMy
    have hML : 0 < M * Real.log (y : ℝ) := mul_pos (by linarith) hlogy0
    have heq : ∀ ω, lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω ^ q
        = (M * Real.log (y : ℝ)) ^ q * ((M * Real.log (y : ℝ))⁻¹
          * lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) M ω) ^ q := by
      intro ω
      rw [← Real.mul_rpow hML.le (mul_nonneg (inv_nonneg.2 hML.le) (lineMass_nonneg _ _ _ _)),
        ← mul_assoc, mul_inv_cancel₀ hML.ne', one_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul]
    have h := HU Y ν hY y M q hyU hM hMy hq0.le hq1
    rw [← hsLdef, ← hPdef] at h
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hML.le _)
  -- the first scale
  have hδy : 2 * δ ≤ Real.log (y : ℝ) := by
    have h1 : δ ≤ 2 ^ J * δ := le_mul_of_one_le_left hδ0.le (one_le_pow₀ (by norm_num))
    linarith
  have hA : ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
      * (∫ ω, lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) δ ω ^ q ∂ν)
      ≤ max 1 ((2 * Real.pi)⁻¹ * 4) * KU * (Real.log (y : ℝ) / δ) ^ q * (P + R) := by
    have hc0 : 0 ≤ (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2) := mul_nonneg hpi0 (by positivity)
    have hS := hscale δ hδ hδy
    rw [← hRdef] at hS
    have hlsq : Real.log l ^ 2 * δ ≤ δ⁻¹ := by
      have h1 : Real.log l ^ 2 ≤ (δ⁻¹) ^ 2 := pow_le_pow_left₀ hlogl hlδ 2
      calc Real.log l ^ 2 * δ ≤ (δ⁻¹) ^ 2 * δ := mul_le_mul_of_nonneg_right h1 hδ0.le
        _ = δ⁻¹ := by rw [sq, mul_assoc, inv_mul_cancel₀ hδne, mul_one]
    have hcoef : (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2) * (δ * Real.log (y : ℝ))
        ≤ (2 * Real.pi)⁻¹ * 4 * (Real.log (y : ℝ) / δ) := by
      calc (2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2) * (δ * Real.log (y : ℝ))
          = (2 * Real.pi)⁻¹ * 4 * ((Real.log l ^ 2 * δ) * Real.log (y : ℝ)) := by ring
        _ ≤ (2 * Real.pi)⁻¹ * 4 * (δ⁻¹ * Real.log (y : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlsq hlogy0.le)
              (mul_nonneg hpi0 (by norm_num))
        _ = (2 * Real.pi)⁻¹ * 4 * (Real.log (y : ℝ) / δ) := by ring
    have hKPR : 0 ≤ KU * (P + R) := mul_nonneg hKU.le (add_nonneg hP0 hR0)
    have hpi4 : 0 < (2 * Real.pi)⁻¹ * 4 := by positivity
    calc ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
          * (∫ ω, lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1) δ ω ^ q ∂ν)
        ≤ ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2)) ^ q
          * ((δ * Real.log (y : ℝ)) ^ q * (KU * (P + R))) :=
          mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hc0 _)
      _ = ((2 * Real.pi)⁻¹ * (4 * Real.log l ^ 2) * (δ * Real.log (y : ℝ))) ^ q
          * (KU * (P + R)) := by
          rw [Real.mul_rpow hc0 (mul_nonneg hδ0.le hlogy0.le)]; ring
      _ ≤ ((2 * Real.pi)⁻¹ * 4 * (Real.log (y : ℝ) / δ)) ^ q * (KU * (P + R)) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (mul_nonneg hc0 (mul_nonneg hδ0.le hlogy0.le)) hcoef hq0.le) hKPR
      _ = ((2 * Real.pi)⁻¹ * 4) ^ q * (Real.log (y : ℝ) / δ) ^ q * (KU * (P + R)) := by
          rw [Real.mul_rpow hpi4.le hB0]
      _ ≤ max 1 ((2 * Real.pi)⁻¹ * 4) * (Real.log (y : ℝ) / δ) ^ q * (KU * (P + R)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (rpow_le_max_one hpi4 hq0.le hq1) hBq) hKPR
      _ = max 1 ((2 * Real.pi)⁻¹ * 4) * KU * (Real.log (y : ℝ) / δ) ^ q * (P + R) := by ring
  -- the dyadic scales
  have hB : ∀ j ∈ Finset.range J,
      ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * δ) ^ 2)⁻¹)) ^ q
        * (∫ ω, lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
            (2 ^ (j + 1) * δ) ω ^ q ∂ν)
      ≤ max 1 ((2 * Real.pi)⁻¹ * 28) * KU * (Real.log (y : ℝ) / δ) ^ q * (P + R)
        * ((((2 : ℝ) ^ j)⁻¹) ^ q * ((j : ℝ) + 2) ^ q) := by
    intro j hj
    have hjJ : j + 1 ≤ J := Finset.mem_range.1 hj
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have h2j1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hMj1 : 1 ≤ (2 : ℝ) ^ (j + 1) * δ := one_le_mul_of_one_le_of_one_le h2j1 hδ
    have hMjy : 2 * ((2 : ℝ) ^ (j + 1) * δ) ≤ Real.log (y : ℝ) := by
      have h := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjJ) hδ0.le
      linarith
    have hS := hscale _ hMj1 hMjy
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hlogMj : Real.log ((2 : ℝ) ^ (j + 1) * δ)
        = ((j : ℝ) + 1) * Real.log 2 + Real.log δ := by
      rw [Real.log_mul (by positivity) hδne, Real.log_pow]; push_cast; ring
    have hnum : 1 + Real.log ((2 : ℝ) ^ (j + 1) * δ) ≤ ((j : ℝ) + 2) * (1 + Real.log δ) := by
      have h1 : ((j : ℝ) + 1) * Real.log 2 ≤ ((j : ℝ) + 1) * 1 :=
        mul_le_mul_of_nonneg_left hlog2.le (by linarith)
      have h2 : 0 ≤ ((j : ℝ) + 1) * Real.log δ := mul_nonneg (by linarith) hlogδ
      have e : ((j : ℝ) + 2) * (1 + Real.log δ)
          = (j : ℝ) + 2 + Real.log δ + ((j : ℝ) + 1) * Real.log δ := by ring
      rw [hlogMj, e]
      linarith
    have hnum0 : 0 ≤ 1 + Real.log ((2 : ℝ) ^ (j + 1) * δ) := by
      have := Real.log_nonneg hMj1; linarith
    have hj2q : 1 ≤ ((j : ℝ) + 2) ^ q := Real.one_le_rpow (by linarith) hq0.le
    have hRj : ((1 + Real.log ((2 : ℝ) ^ (j + 1) * δ)) / sL) ^ q ≤ ((j : ℝ) + 2) ^ q * R := by
      rw [hRdef, ← Real.mul_rpow (by linarith : (0 : ℝ) ≤ (j : ℝ) + 2)
        (div_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log δ) hsL0)]
      refine Real.rpow_le_rpow (div_nonneg hnum0 hsL0) ?_ hq0.le
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hnum hsL0
    have hPR : P + ((1 + Real.log ((2 : ℝ) ^ (j + 1) * δ)) / sL) ^ q
        ≤ ((j : ℝ) + 2) ^ q * (P + R) := by
      have := mul_le_mul_of_nonneg_right hj2q hP0
      rw [mul_add]; linarith
    have hc0 : 0 ≤ (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * δ) ^ 2)⁻¹) :=
      mul_nonneg hpi0 (mul_nonneg (by norm_num) (inv_nonneg.2 (sq_nonneg _)))
    have hMl0 : 0 ≤ (2 : ℝ) ^ (j + 1) * δ * Real.log (y : ℝ) :=
      mul_nonneg (mul_nonneg (by positivity) hδ0.le) hlogy0.le
    have hcoef : (2 * Real.pi)⁻¹ * (14 * ((2 ^ j * δ) ^ 2)⁻¹)
        * ((2 : ℝ) ^ (j + 1) * δ * Real.log (y : ℝ))
        = (2 * Real.pi)⁻¹ * 28 * (((2 : ℝ) ^ j)⁻¹ * (Real.log (y : ℝ) / δ)) := by
      field_simp
      ring
    have hpi28 : 0 < (2 * Real.pi)⁻¹ * 28 := by positivity
    have h2jq : 0 ≤ (((2 : ℝ) ^ j)⁻¹) ^ q := Real.rpow_nonneg (inv_nonneg.2 h2j.le) _
    have hKPR : 0 ≤ KU * (P + ((1 + Real.log ((2 : ℝ) ^ (j + 1) * δ)) / sL) ^ q) :=
      mul_nonneg hKU.le (add_nonneg hP0 (Real.rpow_nonneg (div_nonneg hnum0 hsL0) _))
    have e1 : ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * δ) ^ 2)⁻¹)) ^ q
        * ((2 : ℝ) ^ (j + 1) * δ * Real.log (y : ℝ)) ^ q
        = ((2 * Real.pi)⁻¹ * 28) ^ q * (((2 : ℝ) ^ j)⁻¹) ^ q * (Real.log (y : ℝ) / δ) ^ q := by
      rw [← Real.mul_rpow hc0 hMl0, hcoef,
        Real.mul_rpow hpi28.le (mul_nonneg (inv_nonneg.2 h2j.le) hB0),
        Real.mul_rpow (inv_nonneg.2 h2j.le) hB0]
      ring
    calc ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * δ) ^ 2)⁻¹)) ^ q
          * (∫ ω, lineMass (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
              (2 ^ (j + 1) * δ) ω ^ q ∂ν)
        ≤ ((2 * Real.pi)⁻¹ * (14 * ((2 ^ j * δ) ^ 2)⁻¹)) ^ q
          * (((2 : ℝ) ^ (j + 1) * δ * Real.log (y : ℝ)) ^ q
            * (KU * (P + ((1 + Real.log ((2 : ℝ) ^ (j + 1) * δ)) / sL) ^ q))) :=
          mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hc0 _)
      _ = ((2 * Real.pi)⁻¹ * 28) ^ q * (((2 : ℝ) ^ j)⁻¹) ^ q * (Real.log (y : ℝ) / δ) ^ q
          * (KU * (P + ((1 + Real.log ((2 : ℝ) ^ (j + 1) * δ)) / sL) ^ q)) := by
          rw [← e1]; ring
      _ ≤ max 1 ((2 * Real.pi)⁻¹ * 28) * (((2 : ℝ) ^ j)⁻¹) ^ q * (Real.log (y : ℝ) / δ) ^ q
          * (KU * (((j : ℝ) + 2) ^ q * (P + R))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (rpow_le_max_one hpi28 hq0.le hq1) h2jq) hBq)
            (mul_le_mul_of_nonneg_left hPR hKU.le) hKPR
            (mul_nonneg (mul_nonneg (le_trans zero_le_one hm1) h2jq) hBq)
      _ = max 1 ((2 * Real.pi)⁻¹ * 28) * KU * (Real.log (y : ℝ) / δ) ^ q * (P + R)
          * ((((2 : ℝ) ^ j)⁻¹) ^ q * ((j : ℝ) + 2) ^ q) := by ring
  -- the far tail
  have hEle : E ≤ CM * Real.log (y : ℝ) := by
    have h := hMert Ω Y ν hY (y : ℝ) hy2
    rw [Nat.floor_natCast, ← hEdef] at h
    have h2 := (inv_mul_le_iff₀ hlogy0).1 h
    linarith
  have hC : ((2 * Real.pi)⁻¹ * 14) ^ q * (E / (2 ^ J * δ)) ^ q
      ≤ max 1 ((2 * Real.pi)⁻¹ * 14 * CM) * (Real.log (y : ℝ) / δ) ^ q
        * (((2 : ℝ) ^ J)⁻¹) ^ q := by
    have hE0 : 0 ≤ E := by rw [hEdef]; exact integral_nonneg fun ω => sq_nonneg _
    have h2J : (0 : ℝ) < 2 ^ J * δ := mul_pos (by positivity) hδ0
    have hpi14 : 0 < (2 * Real.pi)⁻¹ * 14 := by positivity
    have hpi14C : 0 < (2 * Real.pi)⁻¹ * 14 * CM := mul_pos hpi14 hCM
    have h2Ji : (0 : ℝ) ≤ ((2 : ℝ) ^ J)⁻¹ := inv_nonneg.2 (by positivity)
    have hbase : (2 * Real.pi)⁻¹ * 14 * (E / (2 ^ J * δ))
        ≤ (2 * Real.pi)⁻¹ * 14 * CM * (Real.log (y : ℝ) / δ * ((2 : ℝ) ^ J)⁻¹) := by
      calc (2 * Real.pi)⁻¹ * 14 * (E / (2 ^ J * δ))
          ≤ (2 * Real.pi)⁻¹ * 14 * (CM * Real.log (y : ℝ) / (2 ^ J * δ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hEle h2J.le) hpi14.le
        _ = (2 * Real.pi)⁻¹ * 14 * CM * (Real.log (y : ℝ) / δ * ((2 : ℝ) ^ J)⁻¹) := by
            simp only [div_eq_mul_inv, mul_inv]; ring
    calc ((2 * Real.pi)⁻¹ * 14) ^ q * (E / (2 ^ J * δ)) ^ q
        = ((2 * Real.pi)⁻¹ * 14 * (E / (2 ^ J * δ))) ^ q :=
          (Real.mul_rpow hpi14.le (div_nonneg hE0 h2J.le)).symm
      _ ≤ ((2 * Real.pi)⁻¹ * 14 * CM * (Real.log (y : ℝ) / δ * ((2 : ℝ) ^ J)⁻¹)) ^ q :=
          Real.rpow_le_rpow (mul_nonneg hpi14.le (div_nonneg hE0 h2J.le)) hbase hq0.le
      _ = ((2 * Real.pi)⁻¹ * 14 * CM) ^ q
          * ((Real.log (y : ℝ) / δ) ^ q * (((2 : ℝ) ^ J)⁻¹) ^ q) := by
          rw [Real.mul_rpow hpi14C.le (mul_nonneg hB0 h2Ji), Real.mul_rpow hB0 h2Ji]
      _ ≤ max 1 ((2 * Real.pi)⁻¹ * 14 * CM)
          * ((Real.log (y : ℝ) / δ) ^ q * (((2 : ℝ) ^ J)⁻¹) ^ q) :=
          mul_le_mul_of_nonneg_right (rpow_le_max_one hpi14C hq0.le hq1) (mul_nonneg hBq hT0)
      _ = max 1 ((2 * Real.pi)⁻¹ * 14 * CM) * (Real.log (y : ℝ) / δ) ^ q
          * (((2 : ℝ) ^ J)⁻¹) ^ q := by ring
  -- assembly
  have hA1 : 0 ≤ max 1 ((2 * Real.pi)⁻¹ * 28) * KU * (Real.log (y : ℝ) / δ) ^ q * (P + R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one hm1) hKU.le) hBq)
      (add_nonneg hP0 hR0)
  have hsum := le_trans (Finset.sum_le_sum hB)
    (le_of_eq (Finset.mul_sum (Finset.range J) (fun j : ℕ => (((2 : ℝ) ^ j)⁻¹) ^ q
      * ((j : ℝ) + 2) ^ q) _).symm)
  refine le_trans hC3 (le_trans (add_le_add (add_le_add hA (le_trans hsum
    (mul_le_mul_of_nonneg_left (sum_rpow_inv_two_pow_mul_rpow_le hq23 hq1 J) hA1))) hC) ?_)
  exact halg _ _ _ _ hBq hP0 hR0 hT0

/-! ### The trivial branch, and the error terms of the reduction -/

/-- **The second moment of a short sum**: `E|∑_{x<n≤x+y} f(n)|² ≤ y + 1`.  Orthogonality counts the
squarefree `n` in the interval, and there are at most `⌊x + y⌋ - ⌊x⌋ ≤ y + 1` integers there. -/
theorem integral_normSq_sum_Ioc_le_of_rademacherRMF {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ 2 ∂μ ≤ y + 1 := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hs0 : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, n ≠ 0 := fun n hn => by
    have := (Finset.mem_Ioc.1 hn).1; omega
  have key := integral_normSq_weightedSum_of_orthogonality' (f := f) (μ := μ)
    (s := Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊) (c := fun _ => (1 : ℂ))
    (d := fun m => if Squarefree m then 1 else 0)
    (fun m _ n _ => hf.integrable_mul_conj m n)
    (fun m hm n hn => by
      rw [hf.orthogonality (hs0 m hm) (hs0 n hn)]
      by_cases h : m = n
      · subst h; simp
      · simp [h])
  have hval : (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ 2 ∂μ)
      = ∑ m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, (if Squarefree m then (1 : ℝ) else 0) := by
    have hTeq : ∀ ω : Ω, ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n
        = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, (1 : ℂ) * f ω n :=
      fun ω => Finset.sum_congr rfl fun n _ => (one_mul _).symm
    simp_rw [hTeq]
    rw [← Complex.ofReal_inj, key, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [hval]
  have hmono : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  have h1 : (⌊x + y⌋₊ : ℝ) ≤ x + y := Nat.floor_le (by linarith)
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  calc ∑ m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, (if Squarefree m then (1 : ℝ) else 0)
      ≤ ∑ m ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => by split_ifs <;> norm_num
    _ = ((⌊x + y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by simp
    _ ≤ y + 1 := by rw [Nat.cast_sub hmono]; linarith

/-- **The trivial bound**: `E|∑_{x<n≤x+y} f(n)|^{2q} ≤ (y + 1)^q` for `0 ≤ q ≤ 1`, Jensen from
`RMF.integral_normSq_sum_Ioc_le_of_rademacherRMF`. -/
theorem integral_rpow_sum_Ioc_le_of_rademacherRMF {f : Ω → ArithmeticFunction ℂ}
    {μ : Measure Ω} (hf : IsRademacherRMF f μ) {x y q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ (2 * q) ∂μ ≤ (y + 1) ^ q := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hmeas : Measurable fun ω => ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ 2 :=
    (Finset.measurable_sum _ fun n _ => hf.measurable_apply n).norm.pow_const 2
  have hbd : ∀ᵐ ω ∂μ, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ 2
      ≤ ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).card : ℝ) ^ 2 := by
    have hall : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
      fun n _ => hf.norm_apply_le_one n
    filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
    have h1 : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖
        ≤ ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).card : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun n hn => hω n hn) ?_
      simp
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hJ := integral_rpow_le_rpow_integral_of_bound hq0 hq1 hmeas
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) hbd
  have heq : ∀ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ (2 * q)
      = (‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n‖ ^ 2) ^ q := fun ω => by
    rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  simp_rw [heq]
  exact le_trans hJ (Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg _)
    (integral_normSq_sum_Ioc_le_of_rademacherRMF hf hx hy) hq0)

/-- **A short sum is in `L^{4/3}`**, being bounded by its number of terms — the side condition of
`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds`. -/
lemma memLp_sum_Ioc_of_rademacherRMF {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (x y : ℝ) :
    MemLp (fun ω => ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n) (ENNReal.ofReal (4 / 3)) μ := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, -⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hall : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ∀ᵐ ω ∂μ, ‖f ω n‖ ≤ 1 :=
    fun n _ => hf.norm_apply_le_one n
  refine (memLp_top_of_bound
    (Finset.measurable_sum _ fun n _ => hf.measurable_apply n).aestronglyMeasurable
    ((Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊).card : ℝ) ?_).mono_exponent le_top
  filter_upwards [(Filter.eventually_all_finset _).2 hall] with ω hω
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun n hn => hω n hn) ?_
  simp

/-- **The error budget in the form the main branch reads**, for `L ≥ 100`:
`2L²e^{-L} ≤ e^{-√L}(1 + √L)⁻¹`, `12L²e^{2√L} ≤ e^L` and `1 + √L ≤ e^L/(2L²)`, all from
`RMF.twelve_mul_cube_mul_exp_two_sqrt_le_exp`. -/
lemma error_budget_of_hundred_le {L : ℝ} (hL : 100 ≤ L) :
    2 * L ^ 2 * Real.exp (-L) ≤ Real.exp (-Real.sqrt L) * (1 + Real.sqrt L)⁻¹
      ∧ 12 * L ^ 2 * Real.exp (2 * Real.sqrt L) ≤ Real.exp L
      ∧ 1 + Real.sqrt L ≤ Real.exp L / (2 * L ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hbud := twelve_mul_cube_mul_exp_two_sqrt_le_exp hL
  have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hs1 : 1 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) hL0.le).2 (by linarith)
  have hsL : Real.sqrt L ≤ L := by nlinarith
  have hL2 : 0 < L ^ 2 := by positivity
  have hL3 : L ^ 2 ≤ L ^ 3 := by nlinarith [mul_nonneg hL2.le (by linarith : (0 : ℝ) ≤ L - 1)]
  have hes : Real.exp (Real.sqrt L) ≤ Real.exp (2 * Real.sqrt L) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : 12 * L ^ 2 * Real.exp (2 * Real.sqrt L) ≤ Real.exp L :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) hbud
  refine ⟨?_, h2, ?_⟩
  · have hb1 : 2 * L ^ 2 * (1 + Real.sqrt L) * Real.exp (Real.sqrt L) ≤ Real.exp L := by
      have h1 : 2 * L ^ 2 * (1 + Real.sqrt L) ≤ 12 * L ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hsL hL2.le]
      calc 2 * L ^ 2 * (1 + Real.sqrt L) * Real.exp (Real.sqrt L)
          ≤ 12 * L ^ 3 * Real.exp (2 * Real.sqrt L) :=
            mul_le_mul h1 hes (Real.exp_pos _).le (by positivity)
        _ ≤ Real.exp L := hbud
    have hkey : 2 * L ^ 2 * (1 + Real.sqrt L) ≤ Real.exp L * Real.exp (-Real.sqrt L) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      exact hb1
    have hsplit : Real.exp (-Real.sqrt L)
        = Real.exp L * Real.exp (-L) * Real.exp (-Real.sqrt L) := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rw [le_mul_inv_iff₀ (by linarith), hsplit]
    calc 2 * L ^ 2 * Real.exp (-L) * (1 + Real.sqrt L)
        = 2 * L ^ 2 * (1 + Real.sqrt L) * Real.exp (-L) := by ring
      _ ≤ Real.exp L * Real.exp (-Real.sqrt L) * Real.exp (-L) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ = Real.exp L * Real.exp (-L) * Real.exp (-Real.sqrt L) := by ring
  · rw [le_div_iff₀ (by positivity)]
    have he := Real.add_one_le_exp (2 * Real.sqrt L)
    have h3 : (1 + Real.sqrt L) * (2 * L ^ 2) ≤ 12 * L ^ 2 * (2 * Real.sqrt L + 1) := by
      nlinarith [mul_nonneg hL2.le hs0]
    calc (1 + Real.sqrt L) * (2 * L ^ 2) ≤ 12 * L ^ 2 * (2 * Real.sqrt L + 1) := h3
      _ ≤ 12 * L ^ 2 * Real.exp (2 * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ Real.exp L := h2

/-- **The Rankin term of the reduction at the Harper cutoff.**  For `1 ≤ ℓ ≤ log(harperCutoff x)`,
the smooth-number term of `RMF.integral_rpow_shortSum_le_sqfree` at `β = c/ℓ` and
`N = ⌊x^{3/4}⌋₊` is at most `e^{-(c/12)(log log x)²}`: `N^β ≤ e^{(3/4)c log x/ℓ}` leaves
`ℓ(1 + 1/c)·e^{-(c/4) log x/ℓ}`, which `RMF.harper_error_bound` (at `q = 1`) bounds. -/
lemma rankin_term_le_of_harperCutoff {A c C x H ℓ : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hC : 0 < C)
    (hx : Real.exp (Real.exp 36) ≤ x) (hH : 0 ≤ H)
    (hthr : 3 * (|Real.log (C * (1 + 1 / c))| + (A + 1)) / (c / 4) ≤ Real.log (Real.log x))
    (hℓ1 : 1 ≤ ℓ) (hℓY : ℓ ≤ Real.log (harperCutoff x)) :
    C * ℓ ^ A * Real.exp (-c * Real.log (x + H) / ℓ)
        * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ))
      ≤ Real.exp (-(c / 4 / 3 * Real.log (Real.log x) ^ 2)) := by
  obtain ⟨hx0, hu36, -⟩ := harper_regime hx
  have hu0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 36) hu36
  have hℓ0 : 0 < ℓ := by linarith
  have hβ0 : 0 < c / ℓ := div_pos hc hℓ0
  have hlogxH : Real.log x ≤ Real.log (x + H) := Real.log_le_log hx0 (by linarith)
  have he1 : Real.exp (-c * Real.log (x + H) / ℓ) ≤ Real.exp (-c * Real.log x / ℓ) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hℓ0.le)
    have := mul_le_mul_of_nonneg_left hlogxH hc.le
    linarith
  have hN : (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) ≤ Real.exp (3 / 4 * c * Real.log x / ℓ) := by
    have h1 : (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ≤ x ^ (3 / 4 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hx0.le _)
    calc (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) ≤ (x ^ (3 / 4 : ℝ)) ^ (c / ℓ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hβ0.le
      _ = Real.exp (3 / 4 * c * Real.log x / ℓ) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
          congr 1
          ring
  have hE4 : Real.exp (-c * Real.log x / ℓ) ≤ Real.exp (-(c / 4) * Real.log x / ℓ) := by
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hℓ0.le)
    have := mul_pos hc hu0
    linarith
  have hEE : Real.exp (-c * Real.log x / ℓ) * Real.exp (3 / 4 * c * Real.log x / ℓ)
      = Real.exp (-(c / 4) * Real.log x / ℓ) := by
    rw [← Real.exp_add]; congr 1; ring
  have hbr : Real.exp (-c * Real.log (x + H) / ℓ)
        * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ))
      ≤ ℓ * (1 + 1 / c) * Real.exp (-(c / 4) * Real.log x / ℓ) := by
    have hnn : 0 ≤ 1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ) :=
      add_nonneg zero_le_one (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hβ0.le)
    have hE0 := Real.exp_pos (-(c / 4) * Real.log x / ℓ)
    have hstep : 1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ)
        ≤ 1 + Real.exp (3 / 4 * c * Real.log x / ℓ) / (c / ℓ) := by
      have := div_le_div_of_nonneg_right hN hβ0.le
      linarith
    have hdiv : Real.exp (3 / 4 * c * Real.log x / ℓ) / (c / ℓ)
        = Real.exp (3 / 4 * c * Real.log x / ℓ) * (ℓ / c) := by
      rw [div_div_eq_mul_div, mul_div_assoc]
    calc Real.exp (-c * Real.log (x + H) / ℓ)
          * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ))
        ≤ Real.exp (-c * Real.log x / ℓ)
          * (1 + Real.exp (3 / 4 * c * Real.log x / ℓ) / (c / ℓ)) :=
          mul_le_mul he1 hstep hnn (Real.exp_pos _).le
      _ = Real.exp (-c * Real.log x / ℓ)
          + Real.exp (-(c / 4) * Real.log x / ℓ) * (ℓ / c) := by
          rw [hdiv, mul_add, mul_one, ← mul_assoc, hEE]
      _ ≤ ℓ * (1 + 1 / c) * Real.exp (-(c / 4) * Real.log x / ℓ) := by
          have h1 := mul_le_mul_of_nonneg_left hℓ1 hE0.le
          have h2 : ℓ * (1 + 1 / c) * Real.exp (-(c / 4) * Real.log x / ℓ)
              = ℓ * Real.exp (-(c / 4) * Real.log x / ℓ)
                + Real.exp (-(c / 4) * Real.log x / ℓ) * (ℓ / c) := by ring
          rw [h2]
          linarith
  have hkey := harper_error_bound (x := x) (C := C * (1 + 1 / c)) (K := A + 1) (c := c / 4)
    (q := 1) (ℓ := ℓ) (mul_pos hC (by have := one_div_pos.2 hc; linarith)) (by linarith)
    (div_pos hc (by norm_num)) hx hthr (by norm_num) le_rfl hℓ0 hℓY
  rw [Real.rpow_one] at hkey
  calc C * ℓ ^ A * Real.exp (-c * Real.log (x + H) / ℓ)
        * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ))
      = C * ℓ ^ A * (Real.exp (-c * Real.log (x + H) / ℓ)
        * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (c / ℓ) / (c / ℓ))) := by ring
    _ ≤ C * ℓ ^ A * (ℓ * (1 + 1 / c) * Real.exp (-(c / 4) * Real.log x / ℓ)) :=
        mul_le_mul_of_nonneg_left hbr (mul_nonneg hC.le (Real.rpow_nonneg hℓ0.le _))
    _ = C * (1 + 1 / c) * (ℓ ^ (A + 1) * Real.exp (-(c / 4) * Real.log x / ℓ)) := by
        rw [Real.rpow_add_one hℓ0.ne']; ring
    _ ≤ Real.exp (-(c / 4 / 3 * Real.log (Real.log x) ^ 2)) := hkey

/-- **Hölder's price in the target**: for `0 ≤ a`, `0 ≤ q ≤ 2/3` and `0 ≤ s`,
`min{1, a + (1 + (1 - 2/3)s)⁻¹} ≤ 3·min{1, a + (1 + (1 - q)s)⁻¹}`, since
`1 + (1 - q)s ≤ 3(1 + s/3)`. -/
lemma min_target_two_thirds_le {a q s : ℝ} (ha : 0 ≤ a) (hq0 : 0 ≤ q) (hq : q ≤ 2 / 3)
    (hs : 0 ≤ s) :
    min 1 (a + (1 + (1 - 2 / 3) * s)⁻¹) ≤ 3 * min 1 (a + (1 + (1 - q) * s)⁻¹) := by
  have hpos : 0 < 1 + (1 - q) * s := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - q) hs
    linarith
  have hpos' : 0 < 1 + (1 - 2 / 3) * s := by linarith
  have hinv : (1 + (1 - 2 / 3) * s)⁻¹ ≤ 3 * (1 + (1 - q) * s)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, inv_mul_le_iff₀ hpos']
    have := mul_nonneg hq0 hs
    linarith
  have hb0 : 0 ≤ (1 + (1 - q) * s)⁻¹ := inv_nonneg.2 hpos.le
  rcases le_total (a + (1 + (1 - q) * s)⁻¹) 1 with h | h
  · rw [min_eq_right h]
    exact le_trans (min_le_right _ _) (by linarith)
  · rw [min_eq_left h]
    exact le_trans (min_le_left _ _) (by norm_num)

/-! ### The main branch -/

set_option maxHeartbeats 1000000 in
-- the reduction, the scales and the three error terms are discharged in one context
/-- **Caich's bound in the main branch**, `2/3 ≤ q ≤ 1` and `log(x/y) ≤ √Λ`, `Λ = log log x`:
`E|M(x,y)|^{2q} ≤ K·(y·min{1, log(x/y)/√Λ + (1 + (1-q)√Λ)⁻¹})^q` for `x ≥ x₀` and `2 ≤ y ≤ x`.
The reduction `RMF.integral_rpow_shortSum_le_sqfree` at `y₀ = ⌊harperCutoff x⌋₊` and `H = y`, then
`RMF.exists_const_integral_rpow_dilatedLineIntegral_le_rademacher` at `λ = (x+y)/x`, `δ = x/y` and
`J = ⌈√Λ⌉₊`; the Rankin, fibre and top-range errors are below `x·2Λ²e^{-Λ} ≤ y(1 + √Λ)⁻¹`
(`RMF.error_budget_of_hundred_le`), as `y ≥ x e^{-√Λ}`. -/
theorem exists_const_integral_rpow_sum_Ioc_le_main :
    ∃ K x₀ : ℝ, 0 < K ∧
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x y q : ℝ, x₀ ≤ x → 2 ≤ y → y ≤ x →
          Real.log (x / y) ≤ Real.sqrt (Real.log (Real.log x)) → 2 / 3 ≤ q → q ≤ 1 →
          ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
              ^ (2 * q) ∂μ
            ≤ K * (y * min 1 (Real.log (x / y) / Real.sqrt (Real.log (Real.log x))
                + (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))⁻¹)) ^ q := by
  obtain ⟨A, cR, CR, hA, hcR, hCR, hRank⟩ := exists_smoothCount_le
  obtain ⟨Cs, hCs, hSieve⟩ := exists_roughCount_sub_le
  obtain ⟨KS, xS, hKS, HS⟩ :=
    exists_const_integral_rpow_dilatedLineIntegral_le_rademacher (Ω := Ω)
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = max 100 (max (Real.log ((⌈xS⌉₊ : ℝ) + 1))
      (max (Real.log ((⌈Real.exp cR⌉₊ : ℝ) + 1))
        (max (3 * (|Real.log (CR * (1 + 1 / cR))| + (A + 1)) / (cR / 4)) (12 / cR)))) :=
    ⟨_, rfl⟩
  have h100 : 100 ≤ Λ₀ := by rw [hΛ₀]; exact le_max_left _ _
  have hΛS : Real.log ((⌈xS⌉₊ : ℝ) + 1) ≤ Λ₀ := by
    rw [hΛ₀]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hΛc : Real.log ((⌈Real.exp cR⌉₊ : ℝ) + 1) ≤ Λ₀ := by
    rw [hΛ₀]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hΛthr : 3 * (|Real.log (CR * (1 + 1 / cR))| + (A + 1)) / (cR / 4) ≤ Λ₀ := by
    rw [hΛ₀]
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hΛ12 : 12 / cR ≤ Λ₀ := by
    rw [hΛ₀]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hm4 : (1 : ℝ) ≤ max 1 (4 * Cs) := le_max_left _ _
  have hm16 : (1 : ℝ) ≤ max 1 (16 * Cs) := le_max_left _ _
  have hKpos : 0 < 1 + 13 * KS * max 1 (4 * Cs) + max 1 (16 * Cs) + max 1 (4 * Cs) := by
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hKS.le)
      (le_trans zero_le_one hm4)
    linarith
  refine ⟨_, Real.exp (Real.exp Λ₀), hKpos, ?_⟩
  intro X μ hX x y q hx hy2 hyx hθ hq23 hq1
  haveI := hX.isProbabilityMeasure
  have hq0 : 0 ≤ q := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨hx36, hΛx⟩ := harper_regime_of (by linarith : (36 : ℝ) ≤ Λ₀) hx
  obtain ⟨hx0, hu36, -⟩ := harper_regime hx36
  have hu0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 36) hu36
  obtain ⟨hy₀4, hlo, hhi, hLL⟩ := floor_harperCutoff_bounds hx36
  have hℓY : Real.log (⌊harperCutoff x⌋₊ : ℝ) ≤ Real.log (harperCutoff x) := by
    rw [log_harperCutoff]; exact hhi
  have habs := harperCutoff_sieve hx36
  have hxS : xS ≤ (⌊harperCutoff x⌋₊ : ℝ) :=
    le_trans (Nat.le_ceil xS) (by exact_mod_cast le_floor_harperCutoff hx36 (le_trans hΛS hΛx))
  have hecR : Real.exp cR ≤ (⌊harperCutoff x⌋₊ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_floor_harperCutoff hx36 (le_trans hΛc hΛx))
  have hthr := le_trans hΛthr hΛx
  have hcRΛ := le_trans hΛ12 hΛx
  -- `Λ = log log x`
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
  rw [← hΛ] at hΛx hlo hhi hLL hθ hthr hcRΛ ⊢
  have hΛ100 : 100 ≤ Λ := le_trans h100 hΛx
  have hΛ0 : 0 < Λ := by linarith
  have hueq : Real.log x = Real.exp Λ := by rw [hΛ, Real.exp_log hu0]
  obtain ⟨hE1, hE2, hE3⟩ := error_budget_of_hundred_le hΛ100
  have hs0 : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  have hs1 : 1 ≤ Real.sqrt Λ := (Real.le_sqrt (by norm_num) hΛ0.le).2 (by linarith)
  have hΛ2 : 0 < 2 * Λ ^ 2 := mul_pos two_pos (pow_pos hΛ0 2)
  -- `ℓ = log y₀`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (⌊harperCutoff x⌋₊ : ℝ) := ⟨_, rfl⟩
  rw [← hℓ] at hlo hhi hLL hℓY
  have hy₀4R : (4 : ℝ) ≤ (⌊harperCutoff x⌋₊ : ℝ) := by exact_mod_cast hy₀4
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by linarith)
  have hcRℓ : cR ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by linarith)]; exact hecR
  have hℓlo : Real.exp Λ / (2 * Λ ^ 2) ≤ ℓ := by rw [← hueq]; exact hlo
  have hℓs : 1 + Real.sqrt Λ ≤ ℓ := le_trans hE3 hℓlo
  have hℓ1 : 1 ≤ ℓ := by linarith
  -- `δ = x/y`, `λ = (x+y)/x`, and `y ≥ x e^{-√Λ}`
  have hδ1 : 1 ≤ x / y := (one_le_div hy0).2 hyx
  have hδ0 : 0 < x / y := by linarith
  have hl1 : 1 ≤ (x + y) / x := (one_le_div hx0).2 (by linarith)
  have hl2 : (x + y) / x ≤ 2 := (div_le_iff₀ hx0).2 (by linarith)
  have hlδ : Real.log ((x + y) / x) ≤ (x / y)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (x + y) / x)
    have he : (x + y) / x - 1 = (x / y)⁻¹ := by
      rw [inv_div, div_sub_one hx0.ne']; ring
    linarith
  have hδle : x / y ≤ Real.exp (Real.sqrt Λ) := (Real.log_le_iff_le_exp hδ0).1 hθ
  have hyx' : x * Real.exp (-Real.sqrt Λ) ≤ y := by
    have h1 := (div_le_iff₀ hy0).1 hδle
    calc x * Real.exp (-Real.sqrt Λ) ≤ Real.exp (Real.sqrt Λ) * y * Real.exp (-Real.sqrt Λ) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = y := by rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  -- the number of scales: `1 + √Λ ≤ 2^J ≤ 3e^{√Λ}`
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌈Real.sqrt Λ⌉₊ := ⟨_, rfl⟩
  have hJlo : 1 + Real.sqrt Λ ≤ (2 : ℝ) ^ J := by
    have h1 := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) J
    have h2 : Real.sqrt Λ ≤ (J : ℝ) := by rw [hJ]; exact Nat.le_ceil _
    norm_num at h1
    linarith
  have hJhi : (2 : ℝ) ^ J ≤ 3 * Real.exp (Real.sqrt Λ) := by
    have h1 : (J : ℝ) ≤ Real.sqrt Λ + 1 := by rw [hJ]; exact (Nat.ceil_lt_add_one hs0.le).le
    have h2 : (2 : ℝ) ^ J ≤ Real.exp 1 ^ J :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) J
    have h3 : Real.exp 1 ^ J = Real.exp (J : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    have h4 : Real.exp (J : ℝ) ≤ Real.exp 1 * Real.exp (Real.sqrt Λ) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have h5 := mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3)
      (Real.exp_pos (Real.sqrt Λ)).le
    linarith
  have hJcond : 2 * (2 ^ J * (x / y)) ≤ ℓ := by
    have hprod : 2 ^ J * (x / y) ≤ 3 * Real.exp (2 * Real.sqrt Λ) := by
      calc (2 : ℝ) ^ J * (x / y) ≤ 3 * Real.exp (Real.sqrt Λ) * Real.exp (Real.sqrt Λ) :=
            mul_le_mul hJhi hδle hδ0.le (by positivity)
        _ = 3 * Real.exp (2 * Real.sqrt Λ) := by rw [mul_assoc, ← Real.exp_add, two_mul]
    have hbig : 6 * Real.exp (2 * Real.sqrt Λ) ≤ Real.exp Λ / (2 * Λ ^ 2) := by
      rw [le_div_iff₀ hΛ2]
      calc 6 * Real.exp (2 * Real.sqrt Λ) * (2 * Λ ^ 2)
          = 12 * Λ ^ 2 * Real.exp (2 * Real.sqrt Λ) := by ring
        _ ≤ Real.exp Λ := hE2
    linarith
  -- the sieve condition at `H = y`
  have hsqx : Real.sqrt x / 2 ≤ y := by
    have hsx : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; ring_nf
    have hΛsq : Λ ≤ Λ ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have hsΛ : Real.sqrt Λ ≤ Λ := (Real.sqrt_le_left hΛ0.le).2 hΛsq
    have h2Λ : 2 * Λ ≤ Real.log x := by
      have he := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt Λ)
      have h12 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 12 * Λ ^ 2)
      rw [hueq]
      linarith
    have hexp : Real.exp (Real.sqrt Λ) ≤ Real.sqrt x := by
      rw [hsx]; exact Real.exp_le_exp.2 (by linarith)
    have h1 : 1 ≤ Real.sqrt x * Real.exp (-Real.sqrt Λ) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]; exact hexp
    calc Real.sqrt x / 2 ≤ Real.sqrt x * 1 := by
          have := Real.sqrt_nonneg x; linarith
      _ ≤ Real.sqrt x * (Real.sqrt x * Real.exp (-Real.sqrt Λ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
      _ = x * Real.exp (-Real.sqrt Λ) := by rw [← mul_assoc, Real.mul_self_sqrt hx0.le]
      _ ≤ y := hyx'
  -- the reduction, and the scales
  have hβ0 : 0 < cR / Real.log (⌊harperCutoff x⌋₊ : ℝ) := by
    rw [← hℓ]; exact div_pos hcR hℓ0
  have hβ1 : cR / Real.log (⌊harperCutoff x⌋₊ : ℝ) ≤ 1 := by
    rw [← hℓ]; exact (div_le_one hℓ0).2 hcRℓ
  have hC2 := integral_rpow_shortSum_le_sqfree hRank hCR.le hSieve hCs.le hX hy₀4 (x := x)
    (H := y) (q := q) hy0 hyx hq0 hq1 habs (le_trans habs hsqx) hβ0 hβ1
  have hS := HS X μ hX ⌊harperCutoff x⌋₊ ((x + y) / x) (x / y) q J hxS hl1 hl2 hlδ hδ1 hq23 hq1
    (by rw [← hℓ]; exact hJcond)
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ ω, ((2 * Real.pi)⁻¹ * dilatedLineIntegral
      (fun ω => squarefreeExtension fun p => X p ω) (⌊harperCutoff x⌋₊ + 1) ((x + y) / x) ω)
        ^ q ∂μ := ⟨_, rfl⟩
  rw [← hI, ← hℓ] at hS
  rw [← hI, ← hℓ] at hC2
  -- the target
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (1 + (1 - q) * Real.sqrt Λ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.log (x / y) / Real.sqrt Λ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = min 1 (a + b) := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hT]
  have hpos : 0 < 1 + (1 - q) * Real.sqrt Λ := by
    have := mul_nonneg (sub_nonneg.2 hq1) hs0.le; linarith
  have hb0 : 0 ≤ b := by rw [hb]; exact inv_nonneg.2 hpos.le
  have hb1 : b ≤ 1 := by
    have h := inv_anti₀ one_pos (by have := mul_nonneg (sub_nonneg.2 hq1) hs0.le; linarith :
      (1 : ℝ) ≤ 1 + (1 - q) * Real.sqrt Λ)
    rw [inv_one] at h
    rw [hb]; exact h
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (Real.log_nonneg hδ1) hs0.le
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hs0]; exact hθ
  have haT : a ≤ T := by rw [hT]; exact le_min ha1 (by linarith)
  have hbT : b ≤ T := by rw [hT]; exact le_min hb1 (by linarith)
  have hT0 : 0 ≤ T := le_trans hb0 hbT
  have hsb : (1 + Real.sqrt Λ)⁻¹ ≤ b := by
    rw [hb]
    refine inv_anti₀ hpos ?_
    have := mul_le_mul_of_nonneg_right (by linarith : 1 - q ≤ 1) hs0.le
    linarith
  have hinvs : 1 / Real.sqrt Λ ≤ 2 * (1 + Real.sqrt Λ)⁻¹ := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ hs0 (by linarith)]; linarith
  have hyT0 : 0 ≤ y * T := mul_nonneg hy0.le hT0
  -- the scale term, the count, and the tail, each against `T^q`
  have hLL0 : 0 < Real.log ℓ := by linarith
  have hP' : (1 + (1 - q) * Real.sqrt (Real.log ℓ)) ^ (-q) ≤ 3 * T ^ q := by
    have h1 := rpow_neg_target_le_of_sq_le (t := Real.log ℓ) (Λ := Λ) (k := 3) (by norm_num)
      (by norm_num; linarith) hq0 hq1
    have h2 : (1 + (1 - q) * Real.sqrt Λ) ^ (-q) = b ^ q := by
      rw [hb, Real.rpow_neg hpos.le, Real.inv_rpow hpos.le]
    have h3 : b ^ q ≤ T ^ q := Real.rpow_le_rpow hb0 hbT hq0
    linarith
  have hsLL : Real.sqrt Λ ≤ 3 * Real.sqrt (Real.log ℓ) := by
    calc Real.sqrt Λ ≤ Real.sqrt (3 ^ 2 * Real.log ℓ) :=
          Real.sqrt_le_sqrt (by norm_num; linarith)
      _ = 3 * Real.sqrt (Real.log ℓ) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hsLL0 : 0 < Real.sqrt (Real.log ℓ) := Real.sqrt_pos.2 hLL0
  have hR' : ((1 + Real.log (x / y)) / Real.sqrt (Real.log ℓ)) ^ q ≤ 9 * T ^ q := by
    have hsne : Real.sqrt Λ ≠ 0 := hs0.ne'
    have he : 1 + Real.log (x / y) = Real.sqrt Λ * (1 / Real.sqrt Λ + a) := by
      rw [ha]; field_simp
    have h1 : 1 / Real.sqrt Λ + a ≤ 3 * T := by linarith
    have hbase : (1 + Real.log (x / y)) / Real.sqrt (Real.log ℓ) ≤ 9 * T := by
      rw [div_le_iff₀ hsLL0, he]
      calc Real.sqrt Λ * (1 / Real.sqrt Λ + a) ≤ Real.sqrt Λ * (3 * T) :=
            mul_le_mul_of_nonneg_left h1 hs0.le
        _ ≤ 3 * Real.sqrt (Real.log ℓ) * (3 * T) :=
            mul_le_mul_of_nonneg_right hsLL (by linarith)
        _ = 9 * T * Real.sqrt (Real.log ℓ) := by ring
    calc ((1 + Real.log (x / y)) / Real.sqrt (Real.log ℓ)) ^ q ≤ (9 * T) ^ q :=
          Real.rpow_le_rpow (div_nonneg (by linarith [Real.log_nonneg hδ1]) hsLL0.le) hbase hq0
      _ = 9 ^ q * T ^ q := Real.mul_rpow (by norm_num) hT0
      _ ≤ 9 * T ^ q := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hq1) (Real.rpow_nonneg hT0 _)
  have hT' : (((2 : ℝ) ^ J)⁻¹) ^ q ≤ T ^ q := by
    have h1 : ((2 : ℝ) ^ J)⁻¹ ≤ (1 + Real.sqrt Λ)⁻¹ := inv_anti₀ (by linarith) hJlo
    exact Real.rpow_le_rpow (inv_nonneg.2 (by positivity)) (le_trans h1 (le_trans hsb hbT)) hq0
  have hIle : I ≤ KS * (ℓ / (x / y)) ^ q * (13 * T ^ q) :=
    le_trans hS (mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg hKS.le (Real.rpow_nonneg (div_nonneg hℓ0.le hδ0.le) _)))
  -- the error terms, each against `x·2Λ²e^{-Λ} ≤ yT`
  have hkeyE : x * (2 * Λ ^ 2 * Real.exp (-Λ)) ≤ y * T := by
    calc x * (2 * Λ ^ 2 * Real.exp (-Λ))
        ≤ x * (Real.exp (-Real.sqrt Λ) * (1 + Real.sqrt Λ)⁻¹) :=
          mul_le_mul_of_nonneg_left hE1 hx0.le
      _ = x * Real.exp (-Real.sqrt Λ) * (1 + Real.sqrt Λ)⁻¹ := by ring
      _ ≤ y * (1 + Real.sqrt Λ)⁻¹ :=
          mul_le_mul_of_nonneg_right hyx' (inv_nonneg.2 (by linarith))
      _ ≤ y * T := mul_le_mul_of_nonneg_left (le_trans hsb hbT) hy0.le
  have hxℓ : x / ℓ ≤ y * T := by
    refine le_trans ?_ hkeyE
    rw [div_le_iff₀ hℓ0]
    have h2 : 1 ≤ 2 * Λ ^ 2 * Real.exp (-Λ) * ℓ := by
      have h3 := (div_le_iff₀ hΛ2).1 hℓlo
      calc (1 : ℝ) = Real.exp Λ * Real.exp (-Λ) := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ ℓ * (2 * Λ ^ 2) * Real.exp (-Λ) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = 2 * Λ ^ 2 * Real.exp (-Λ) * ℓ := by ring
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * (2 * Λ ^ 2 * Real.exp (-Λ) * ℓ) := mul_le_mul_of_nonneg_left h2 hx0.le
      _ = x * (2 * Λ ^ 2 * Real.exp (-Λ)) * ℓ := by ring
  have hR := rankin_term_le_of_harperCutoff (H := y) hA hcR hCR hx36 hy0.le
    (by rw [← hΛ]; exact hthr) hℓ1 hℓY
  rw [← hΛ] at hR
  have hexpΛ : Real.exp (-(cR / 4 / 3 * Λ ^ 2)) ≤ Real.exp (-Λ) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have h12 := (div_le_iff₀ hcR).1 hcRΛ
    have := mul_le_mul_of_nonneg_left h12 hΛ0.le
    linarith
  have hR0 : 0 ≤ CR * ℓ ^ A * Real.exp (-cR * Real.log (x + y) / ℓ)
      * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / ℓ) / (cR / ℓ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCR.le (Real.rpow_nonneg hℓ0.le _)) (Real.exp_pos _).le)
      (add_nonneg zero_le_one (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (div_pos hcR hℓ0).le))
  have hT1 : ((x + y) * (CR * ℓ ^ A * Real.exp (-cR * Real.log (x + y) / ℓ)
      * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / ℓ) / (cR / ℓ)))) ^ q ≤ (y * T) ^ q := by
    refine Real.rpow_le_rpow (mul_nonneg (by linarith) hR0) ?_ hq0
    have hΛsq1 : 1 ≤ Λ ^ 2 := one_le_pow₀ (by linarith)
    calc (x + y) * (CR * ℓ ^ A * Real.exp (-cR * Real.log (x + y) / ℓ)
          * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / ℓ) / (cR / ℓ)))
        ≤ (2 * x) * Real.exp (-Λ) :=
          mul_le_mul (by linarith) (le_trans hR hexpΛ) hR0 (by linarith)
      _ ≤ x * (2 * Λ ^ 2 * Real.exp (-Λ)) := by
          have := mul_le_mul_of_nonneg_left hΛsq1
            (mul_nonneg hx0.le (Real.exp_pos (-Λ)).le)
          linarith
      _ ≤ y * T := hkeyE
  have hCsx0 : 0 ≤ Cs * x / ℓ := div_nonneg (mul_nonneg hCs.le hx0.le) hℓ0.le
  have h4Cs : 0 < 4 * Cs := mul_pos (by norm_num) hCs
  have h16Cs : 0 < 16 * Cs := mul_pos (by norm_num) hCs
  have hyTq : 0 ≤ (y * T) ^ q := Real.rpow_nonneg hyT0 _
  have hpow_eq : (Cs * x / ℓ) ^ q * 4 ^ q * (ℓ / (x / y)) ^ q = (4 * Cs) ^ q * y ^ q := by
    have hxne := hx0.ne'
    have hyne := hy0.ne'
    have hℓne := hℓ0.ne'
    have hbase : Cs * x / ℓ * 4 * (ℓ / (x / y)) = 4 * Cs * y := by field_simp
    rw [← Real.mul_rpow hCsx0 (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.mul_rpow (mul_nonneg hCsx0 (by norm_num : (0 : ℝ) ≤ 4)) (div_nonneg hℓ0.le hδ0.le),
      hbase, Real.mul_rpow h4Cs.le hy0.le]
  have hT2 : (Cs * x / ℓ) ^ q * (4 ^ q * I + 16 ^ q)
      ≤ 13 * KS * max 1 (4 * Cs) * (y * T) ^ q + max 1 (16 * Cs) * (y * T) ^ q := by
    have hCq : 0 ≤ (Cs * x / ℓ) ^ q := Real.rpow_nonneg hCsx0 _
    have h4q : (0 : ℝ) ≤ 4 ^ q := Real.rpow_nonneg (by norm_num) _
    have hpart1 : (Cs * x / ℓ) ^ q * (4 ^ q * I) ≤ 13 * KS * max 1 (4 * Cs) * (y * T) ^ q := by
      calc (Cs * x / ℓ) ^ q * (4 ^ q * I)
          ≤ (Cs * x / ℓ) ^ q * (4 ^ q * (KS * (ℓ / (x / y)) ^ q * (13 * T ^ q))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIle h4q) hCq
        _ = 13 * KS * ((Cs * x / ℓ) ^ q * 4 ^ q * (ℓ / (x / y)) ^ q) * T ^ q := by ring
        _ = 13 * KS * (4 * Cs) ^ q * (y * T) ^ q := by
            rw [hpow_eq, Real.mul_rpow hy0.le hT0]; ring
        _ ≤ 13 * KS * max 1 (4 * Cs) * (y * T) ^ q :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (rpow_le_max_one h4Cs hq0 hq1) (by linarith)) hyTq
    have hpart2 : (Cs * x / ℓ) ^ q * 16 ^ q ≤ max 1 (16 * Cs) * (y * T) ^ q := by
      calc (Cs * x / ℓ) ^ q * 16 ^ q = (16 * Cs * (x / ℓ)) ^ q := by
            rw [← Real.mul_rpow hCsx0 (by norm_num : (0 : ℝ) ≤ 16)]; congr 1; ring
        _ ≤ (16 * Cs * (y * T)) ^ q :=
            Real.rpow_le_rpow (mul_nonneg h16Cs.le (div_nonneg hx0.le hℓ0.le))
              (mul_le_mul_of_nonneg_left hxℓ h16Cs.le) hq0
        _ = (16 * Cs) ^ q * (y * T) ^ q := Real.mul_rpow h16Cs.le hyT0
        _ ≤ max 1 (16 * Cs) * (y * T) ^ q :=
            mul_le_mul_of_nonneg_right (rpow_le_max_one h16Cs hq0 hq1) hyTq
    calc (Cs * x / ℓ) ^ q * (4 ^ q * I + 16 ^ q)
        = (Cs * x / ℓ) ^ q * (4 ^ q * I) + (Cs * x / ℓ) ^ q * 16 ^ q := by ring
      _ ≤ 13 * KS * max 1 (4 * Cs) * (y * T) ^ q + max 1 (16 * Cs) * (y * T) ^ q :=
          add_le_add hpart1 hpart2
  have hT3 : (4 * (Cs * y / ℓ)) ^ q ≤ max 1 (4 * Cs) * (y * T) ^ q := by
    have h1 : 1 ≤ T * ℓ := by
      have hinv : (1 + Real.sqrt Λ)⁻¹ * (1 + Real.sqrt Λ) = 1 := inv_mul_cancel₀ (by linarith)
      calc (1 : ℝ) = (1 + Real.sqrt Λ)⁻¹ * (1 + Real.sqrt Λ) := hinv.symm
        _ ≤ T * ℓ := mul_le_mul (le_trans hsb hbT) hℓs (by linarith) hT0
    have h2 : ℓ⁻¹ ≤ T := by rw [inv_le_iff_one_le_mul₀ hℓ0]; linarith
    have hbase : 4 * (Cs * y / ℓ) ≤ 4 * Cs * (y * T) := by
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg h4Cs.le hy0.le)
      calc 4 * (Cs * y / ℓ) = 4 * Cs * y * ℓ⁻¹ := by ring
        _ ≤ 4 * Cs * y * T := this
        _ = 4 * Cs * (y * T) := by ring
    calc (4 * (Cs * y / ℓ)) ^ q ≤ (4 * Cs * (y * T)) ^ q :=
          Real.rpow_le_rpow (mul_nonneg (by norm_num)
            (div_nonneg (mul_nonneg hCs.le hy0.le) hℓ0.le)) hbase hq0
      _ = (4 * Cs) ^ q * (y * T) ^ q := Real.mul_rpow h4Cs.le hyT0
      _ ≤ max 1 (4 * Cs) * (y * T) ^ q :=
          mul_le_mul_of_nonneg_right (rpow_le_max_one h4Cs hq0 hq1) hyTq
  refine le_trans hC2 ?_
  calc ((x + y) * (CR * ℓ ^ A * Real.exp (-cR * Real.log (x + y) / ℓ)
        * (1 + (⌊x ^ (3 / 4 : ℝ)⌋₊ : ℝ) ^ (cR / ℓ) / (cR / ℓ)))) ^ q
        + (Cs * x / ℓ) ^ q * (4 ^ q * I + 16 ^ q) + (4 * (Cs * y / ℓ)) ^ q
      ≤ (y * T) ^ q + (13 * KS * max 1 (4 * Cs) * (y * T) ^ q
          + max 1 (16 * Cs) * (y * T) ^ q) + max 1 (4 * Cs) * (y * T) ^ q :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = (1 + 13 * KS * max 1 (4 * Cs) + max 1 (16 * Cs) + max 1 (4 * Cs)) * (y * T) ^ q := by
        ring

/-! ### Caich's Theorem 1.1, Rademacher case -/

/-- The sum over a short interval, `M(x,y) = ∑_{x<n≤x+y} f(n)`. -/
noncomputable def shortIntervalSum (f : Ω → ArithmeticFunction ℂ) (x y : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f ω n

/-- Caich's `θ`, defined by `x/y = (log x)^θ`. -/
noncomputable def caichTheta (x y : ℝ) : ℝ := Real.log (x / y) / Real.log (Real.log x)

/-- **Caich's Theorem 1.1, Rademacher case.**  There are `C` and `x₀`, independent of `X`, `x`,
`y` and `q`, such that for every Rademacher `X`, `x₀ ≤ x`, `2 ≤ y ≤ x` and `0 ≤ q ≤ 1`,

`E|M(x,y)|^{2q} ≤ C·(y·min{1, θ√(log log x) + (1 + (1-q)√(log log x))⁻¹})^q`,  `x/y = (log x)^θ`.

R. Caich, arXiv:2402.06426, Theorem 1.1, with `1/((1-q)√(log log x))` written
`(1 + (1-q)√(log log x))⁻¹`.  Three branches, `Λ = log log x`: for `log(x/y) > √Λ` the `min` is
`1` and `RMF.integral_rpow_sum_Ioc_le_of_rademacherRMF` gives `(y + 1)^q ≤ 2y^q`; for
`log(x/y) ≤ √Λ` and `q ≥ 2/3` it is `RMF.exists_const_integral_rpow_sum_Ioc_le_main`; for
`q < 2/3` it is Hölder (`RMF.integral_rpow_le_rpow_integral_of_le_two_thirds`) from `q = 2/3`, at
the price `RMF.min_target_two_thirds_le`. -/
theorem integral_rpow_shortIntervalSum_le_caich :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ,
      ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsRademacherPrimeValues X μ →
        ∀ x y q : ℝ, x₀ ≤ x → 2 ≤ y → y ≤ x → 0 ≤ q → q ≤ 1 →
          (∫ ω, ‖shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x y ω‖
              ^ (2 * q) ∂μ)
            ≤ C * (y * min 1 (caichTheta x y * Real.sqrt (Real.log (Real.log x))
                + (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))⁻¹)) ^ q := by
  obtain ⟨K, x₁, hK, Hmain⟩ := exists_const_integral_rpow_sum_Ioc_le_main (Ω := Ω)
  have hm1 : (1 : ℝ) ≤ max 1 K := le_max_left _ _
  have hC2 : (2 : ℝ) ≤ max 2 (3 * max 1 K) := le_max_left _ _
  have hC3 : 3 * max 1 K ≤ max 2 (3 * max 1 K) := le_max_right _ _
  refine ⟨max 2 (3 * max 1 K), lt_of_lt_of_le two_pos hC2, max x₁ (Real.exp (Real.exp 36)), ?_⟩
  intro X μ hX x y q hx hy2 hyx hq0 hq1
  haveI := hX.isProbabilityMeasure
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨hx0, -, hL36⟩ := harper_regime (le_trans (le_max_right _ _) hx)
  have hy0 : 0 < y := by linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
  rw [← hΛ] at hL36 ⊢
  have hΛ0 : 0 < Λ := by linarith
  have hs0 : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  -- `θ√Λ = log(x/y)/√Λ`
  have hθ : caichTheta x y * Real.sqrt Λ = Real.log (x / y) / Real.sqrt Λ := by
    rw [caichTheta, ← hΛ, div_mul_eq_mul_div, div_eq_div_iff hΛ0.ne' hs0.ne', mul_assoc,
      Real.mul_self_sqrt hΛ0.le]
  rw [hθ]
  have hM : ∀ ω, shortIntervalSum (fun ω => squarefreeExtension fun p => X p ω) x y ω
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n := fun ω => rfl
  simp_rw [hM]
  have hlogxy : 0 ≤ Real.log (x / y) := Real.log_nonneg ((one_le_div hy0).2 hyx)
  have hpos : 0 < 1 + (1 - q) * Real.sqrt Λ := by
    have := mul_nonneg (sub_nonneg.2 hq1) hs0.le; linarith
  have hT0 : 0 ≤ min 1 (Real.log (x / y) / Real.sqrt Λ + (1 + (1 - q) * Real.sqrt Λ)⁻¹) :=
    le_min zero_le_one (add_nonneg (div_nonneg hlogxy hs0.le) (inv_nonneg.2 hpos.le))
  have hyTq : 0 ≤ (y * min 1 (Real.log (x / y) / Real.sqrt Λ
      + (1 + (1 - q) * Real.sqrt Λ)⁻¹)) ^ q := Real.rpow_nonneg (mul_nonneg hy0.le hT0) _
  rcases le_or_gt (Real.log (x / y)) (Real.sqrt Λ) with hθΛ | hθΛ
  · rcases le_or_gt (2 / 3) q with hq23 | hq23
    · -- the main branch
      have h := Hmain X μ hX x y q hx₁ hy2 hyx (by rw [← hΛ]; exact hθΛ) hq23 hq1
      rw [← hΛ] at h
      refine le_trans h (mul_le_mul_of_nonneg_right ?_ hyTq)
      linarith [le_max_right 1 K]
    · -- Hölder from `q = 2/3`
      have hH : (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
            ^ (2 * q) ∂μ)
          ≤ (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
            ^ (4 / 3 : ℝ) ∂μ) ^ (3 * q / 2) :=
        integral_rpow_le_rpow_integral_of_le_two_thirds hq0 hq23.le
          (memLp_sum_Ioc_of_rademacherRMF hf x y)
      have h23 := Hmain X μ hX x y (2 / 3) hx₁ hy2 hyx (by rw [← hΛ]; exact hθΛ) le_rfl
        (by norm_num)
      rw [← hΛ, show (2 : ℝ) * (2 / 3) = 4 / 3 by norm_num] at h23
      have hT23 := min_target_two_thirds_le (div_nonneg hlogxy hs0.le) hq0 hq23.le hs0.le
      have hpos23 : 0 < 1 + (1 - 2 / 3) * Real.sqrt Λ := by
        have := hs0.le; linarith
      have hT23' : 0 ≤ min 1 (Real.log (x / y) / Real.sqrt Λ
          + (1 + (1 - 2 / 3) * Real.sqrt Λ)⁻¹) :=
        le_min zero_le_one (add_nonneg (div_nonneg hlogxy hs0.le) (inv_nonneg.2 hpos23.le))
      have hW23 : 0 ≤ y * min 1 (Real.log (x / y) / Real.sqrt Λ
          + (1 + (1 - 2 / 3) * Real.sqrt Λ)⁻¹) := mul_nonneg hy0.le hT23'
      have hI0 : 0 ≤ ∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
          ^ (4 / 3 : ℝ) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
      have he : (3 * q / 2) ≤ 1 := by linarith
      calc (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
            ^ (2 * q) ∂μ)
          ≤ (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
            ^ (4 / 3 : ℝ) ∂μ) ^ (3 * q / 2) := hH
        _ ≤ (K * (y * min 1 (Real.log (x / y) / Real.sqrt Λ
              + (1 + (1 - 2 / 3) * Real.sqrt Λ)⁻¹)) ^ (2 / 3 : ℝ)) ^ (3 * q / 2) :=
            Real.rpow_le_rpow hI0 h23 (by linarith)
        _ = K ^ (3 * q / 2) * (y * min 1 (Real.log (x / y) / Real.sqrt Λ
              + (1 + (1 - 2 / 3) * Real.sqrt Λ)⁻¹)) ^ q := by
            rw [Real.mul_rpow hK.le (Real.rpow_nonneg hW23 _), ← Real.rpow_mul hW23]
            congr 2
            ring
        _ ≤ max 1 K * (y * (3 * min 1 (Real.log (x / y) / Real.sqrt Λ
              + (1 + (1 - q) * Real.sqrt Λ)⁻¹))) ^ q :=
            mul_le_mul (rpow_le_max_one hK (by linarith) he)
              (Real.rpow_le_rpow hW23 (mul_le_mul_of_nonneg_left hT23 hy0.le) hq0)
              (Real.rpow_nonneg hW23 _) (le_trans zero_le_one hm1)
        _ = max 1 K * 3 ^ q * (y * min 1 (Real.log (x / y) / Real.sqrt Λ
              + (1 + (1 - q) * Real.sqrt Λ)⁻¹)) ^ q := by
            rw [mul_left_comm y 3, Real.mul_rpow (by norm_num) (mul_nonneg hy0.le hT0)]; ring
        _ ≤ max 1 K * 3 * (y * min 1 (Real.log (x / y) / Real.sqrt Λ
              + (1 + (1 - q) * Real.sqrt Λ)⁻¹)) ^ q :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (Real.rpow_le_self_of_one_le (by norm_num) hq1) (le_trans zero_le_one hm1)) hyTq
        _ ≤ max 2 (3 * max 1 K) * (y * min 1 (Real.log (x / y) / Real.sqrt Λ
              + (1 + (1 - q) * Real.sqrt Λ)⁻¹)) ^ q :=
            mul_le_mul_of_nonneg_right (by linarith) hyTq
  · -- `θ√Λ > 1`: the `min` is `1`, and the trivial bound
    have hT1 : min 1 (Real.log (x / y) / Real.sqrt Λ + (1 + (1 - q) * Real.sqrt Λ)⁻¹) = 1 := by
      refine min_eq_left ?_
      have h1 : 1 < Real.log (x / y) / Real.sqrt Λ := (one_lt_div hs0).2 hθΛ
      have h2 : 0 ≤ (1 + (1 - q) * Real.sqrt Λ)⁻¹ := inv_nonneg.2 hpos.le
      linarith
    rw [hT1, mul_one]
    calc (∫ ω, ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, squarefreeExtension (fun p => X p ω) n‖
          ^ (2 * q) ∂μ)
        ≤ (y + 1) ^ q := integral_rpow_sum_Ioc_le_of_rademacherRMF hf hx0.le hy0.le hq0 hq1
      _ ≤ (2 * y) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq0
      _ = 2 ^ q * y ^ q := Real.mul_rpow (by norm_num) hy0.le
      _ ≤ 2 * y ^ q := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hq1) (Real.rpow_nonneg hy0.le _)
      _ ≤ max 2 (3 * max 1 K) * y ^ q :=
          mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hy0.le _)

end RMF
