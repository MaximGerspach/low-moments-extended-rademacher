/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.HalfWindowExplicit
import RMF.Weighted.ReductionSmallQExplicit

/-!
# The first moment of the weighted Rademacher sum: the parameters

For `x ≥ exp(e^{110})` and `Λ = log log x`, the explicit parameters of the chain at `q = ½`, and
their basic facts:

* the smoothness level `y = ⌊e^{2 log x/Λ}⌋` (`U = Λ/2`), the tilt `σ = (1/32)/log x`, the sieve
  level `z = ⌊e^{2 log x/Λ - 12Λ}⌋`, `η = (log x)^{-3}` and `ε = (log x)^{-1/2}`, for the
  reduction;
* a window `k` of `Z` is a chaos window when `97 ≤ k` and `k + 8 + 2000 ≤ ⌊log log y⌋`: offset
  `D = k + 8`, room `N = 2000`, level `A = 20`, `λ = 104/5`, `δ = 1/50`, `T = 35`, `κ = 10`,
  slope `β = 11/20`, tilt `E₀ = 1/(16Λ)` (`RMF.halfChaosConst`).

The chain is assembled, with its windows split at slope `3/2`, in
`RMF/Weighted/TenAssemblyExplicit.lean`; `RMF/Weighted/HalfNumeralExplicit.lean` evaluates its
pieces at these parameters.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The parameters -/

/-- `2 log x/log log x = log x/U`, `U = Λ/2`: the logarithm of the smoothness level. -/
noncomputable def halfA (x : ℝ) : ℝ := 2 * Real.log x / Real.log (Real.log x)

/-- The smoothness level `y = ⌊e^{halfA x}⌋`. -/
noncomputable def halfY (x : ℝ) : ℕ := ⌊Real.exp (halfA x)⌋₊

/-- The sieve level `z = ⌊e^{halfA x - 12Λ}⌋`. -/
noncomputable def halfZ (x : ℝ) : ℕ := ⌊Real.exp (halfA x - 12 * Real.log (Real.log x))⌋₊

/-- The tilt `σ = (1/32)/log x`. -/
noncomputable def halfSigma (x : ℝ) : ℝ := 1 / 32 / Real.log x

/-- The smoothing width `η = (log x)^{-3}`. -/
noncomputable def halfEta (x : ℝ) : ℝ := (Real.log x ^ 3)⁻¹

/-- The smoothing split `ε = (log x)^{-1/2}`. -/
noncomputable def halfEps (x : ℝ) : ℝ := (Real.sqrt (Real.log x))⁻¹

/-- The chaos constant of a window at `q = ½`, at the tilt `E₀`. -/
noncomputable def halfChaosConst (E₀ : ℝ) : ℝ :=
  shiftMomentConst 1 (radAveragedConst E₀ (11 / 20) 35 10)
    (radBlockBadConst E₀ (11 / 20) * Real.exp 8) 20 (radAveragedShift E₀ (11 / 20) 35 10)
    (104 / 5) (1 / 50) (1 / 2)

/-- The smooth tail of the reduction. -/
noncomputable def halfTail (x : ℝ) : ℝ :=
  ∑ m ∈ {m ∈ Finset.Ioc ⌊x⌋₊ (primorial (halfY x))
    | m ∈ Nat.smoothNumbers (halfY x + 1) ∧ Squarefree m}, (m : ℝ)⁻¹

/-! ### The parameters' facts -/

/-- `e^Λ ≥ 100Λ^{10}` for `Λ ≥ 110`: `Λ^{20}/20! ≤ e^Λ`. -/
lemma hundred_mul_pow_ten_le_exp {Λ : ℝ} (hΛ : 110 ≤ Λ) : 100 * Λ ^ 10 ≤ Real.exp Λ := by
  have h := Real.pow_div_factorial_le_exp (x := Λ) (by linarith) 20
  have hf : ((Nat.factorial 20 : ℕ) : ℝ) = 2432902008176640000 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h10 : (110 : ℝ) ^ 10 ≤ Λ ^ 10 := pow_le_pow_left₀ (by norm_num) hΛ 10
  have hΛ10 : 0 ≤ Λ ^ 10 := by positivity
  have hkey : 100 * Λ ^ 10 ≤ Λ ^ 20 / 2432902008176640000 := by
    rw [le_div_iff₀ (by norm_num), show Λ ^ 20 = Λ ^ 10 * Λ ^ 10 by ring]
    have : (100 : ℝ) * 2432902008176640000 ≤ Λ ^ 10 := by
      linarith [show (100 : ℝ) * 2432902008176640000 ≤ 110 ^ 10 by norm_num]
    nlinarith
  linarith

/-- The basic facts of the parameters at `x ≥ exp(e^{110})`. -/
lemma half_params {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    0 < x ∧ Real.exp 110 ≤ Real.log x ∧ 110 ≤ Real.log (Real.log x)
      ∧ Real.exp (Real.log (Real.log x)) = Real.log x
      ∧ 200 * Real.log (Real.log x) ^ 9 ≤ halfA x ∧ halfA x ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 110 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛ : 110 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le hLpos]
    exact hL
  have hexpΛ : Real.exp (Real.log (Real.log x)) = Real.log x := Real.exp_log hLpos
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  refine ⟨hx0, hL, hΛ, hexpΛ, ?_, ?_⟩
  · have h := hundred_mul_pow_ten_le_exp hΛ
    rw [hexpΛ] at h
    rw [halfA, le_div_iff₀ hΛpos]
    have : Real.log (Real.log x) ^ 9 * Real.log (Real.log x)
        = Real.log (Real.log x) ^ 10 := by ring
    nlinarith
  · rw [halfA, div_le_iff₀ hΛpos]
    nlinarith

/-- `100 ≤ halfA x` and `2^{101} ≤ e^{halfA x}`, with room. -/
lemma halfA_ge {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    200 * Real.log (Real.log x) + 100 ≤ halfA x := by
  obtain ⟨-, -, hΛ, -, ha, -⟩ := half_params hx
  have h9 : 110 ^ 8 * Real.log (Real.log x) ≤ Real.log (Real.log x) ^ 9 := by
    have h8 : (110 : ℝ) ^ 8 ≤ Real.log (Real.log x) ^ 8 := pow_le_pow_left₀ (by norm_num) hΛ 8
    have : Real.log (Real.log x) ^ 9 = Real.log (Real.log x) ^ 8 * Real.log (Real.log x) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  nlinarith

/-- **The smoothness level**: `e^a/2 ≤ y ≤ e^a` with `a = halfA x`, so `a - log 2 ≤ log y ≤ a`;
`y ≤ x` and `y ≥ e^{99}`. -/
lemma halfY_facts {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    2 ≤ halfY x ∧ (halfY x : ℝ) ≤ x ∧ Real.log (halfY x) ≤ halfA x
      ∧ halfA x - Real.log 2 ≤ Real.log (halfY x) ∧ Real.exp 99 ≤ (halfY x : ℝ)
      ∧ Real.exp (halfA x) / 2 ≤ (halfY x : ℝ) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, haL⟩ := half_params hx
  have ha := halfA_ge hx
  have ha100 : 100 ≤ halfA x := by linarith
  have hea : 2 ≤ Real.exp (halfA x) := by linarith [Real.add_one_le_exp (halfA x)]
  have hfl : Real.exp (halfA x) < (halfY x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfl' : (halfY x : ℝ) ≤ Real.exp (halfA x) := Nat.floor_le (Real.exp_pos _).le
  have hyh : Real.exp (halfA x) / 2 ≤ (halfY x : ℝ) := by linarith
  have hypos : 0 < (halfY x : ℝ) := lt_of_lt_of_le (by positivity) hyh
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  refine ⟨?_, ?_, ?_, ?_, ?_, hyh⟩
  · have h1 : (2 : ℝ) ≤ (halfY x : ℝ) := by
      have : (101 : ℝ) ≤ Real.exp (halfA x) := by linarith [Real.add_one_le_exp (halfA x)]
      linarith
    exact_mod_cast h1
  · calc (halfY x : ℝ) ≤ Real.exp (halfA x) := hfl'
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 haL
      _ = x := Real.exp_log hx0
  · calc Real.log (halfY x) ≤ Real.log (Real.exp (halfA x)) := Real.log_le_log hypos hfl'
      _ = halfA x := Real.log_exp _
  · calc halfA x - Real.log 2 = Real.log (Real.exp (halfA x) / 2) := by
          rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
      _ ≤ Real.log (halfY x) := Real.log_le_log (by positivity) hyh
  · have h1 : Real.exp 99 * 2 ≤ Real.exp (halfA x) := by
      have h2 : Real.exp 99 * Real.exp 1 ≤ Real.exp (halfA x) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith)
      have h3 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      nlinarith [Real.exp_pos 99]
    linarith

/-- **The sieve level**: `2 ≤ z ≤ y` and `log z ≥ a - 12Λ - log 2`. -/
lemma halfZ_facts {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    2 ≤ halfZ x ∧ halfZ x ≤ halfY x
      ∧ halfA x - 12 * Real.log (Real.log x) - Real.log 2 ≤ Real.log (halfZ x) := by
  obtain ⟨-, -, hΛ, -, -, -⟩ := half_params hx
  have ha := halfA_ge hx
  set b := halfA x - 12 * Real.log (Real.log x) with hb
  have hb100 : 100 ≤ b := by rw [hb]; linarith
  have heb : 2 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have hfl : Real.exp b < (halfZ x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hzh : Real.exp b / 2 ≤ (halfZ x : ℝ) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (2 : ℝ) ≤ (halfZ x : ℝ) := by
      have : (101 : ℝ) ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
      linarith
    exact_mod_cast h1
  · exact Nat.floor_le_floor (Real.exp_le_exp.2 (by linarith))
  · calc b - Real.log 2 = Real.log (Real.exp b / 2) := by
          rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
      _ ≤ Real.log (halfZ x) := Real.log_le_log (by positivity) hzh

/-- **Chebyshev's lower bound, crudely**: `Y/2 ≤ Y log 2 - log(Y+1) - 2√Y log Y` for
`Y ≥ 2^{100}`. -/
lemma half_le_theta_lower {Y : ℝ} (hY : 2 ^ 100 ≤ Y) :
    Y / 2 ≤ Y * Real.log 2 - Real.log (Y + 1) - 2 * Real.sqrt Y * Real.log Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Y ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hY0 _
  have hs4 : s ^ 4 = Y := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    norm_num
  have hsqrt : Real.sqrt Y = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs25 : (2 : ℝ) ^ 25 ≤ s := by
    by_contra h
    have h1 : s ^ 4 < ((2 : ℝ) ^ 25) ^ 4 := pow_lt_pow_left₀ (not_le.1 h) hs0.le (by norm_num)
    rw [hs4] at h1
    linarith [show ((2 : ℝ) ^ 25) ^ 4 = 2 ^ 100 by norm_num]
  have hlogY : Real.log Y = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]
    norm_num
  have hlogs : Real.log s ≤ s := le_trans (Real.log_le_sub_one_of_pos hs0) (by linarith)
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith [show (1 : ℝ) ≤ 2 ^ 25 by norm_num])
  have hlogY1 : Real.log (Y + 1) ≤ Real.log 2 + Real.log Y := by
    rw [← Real.log_mul (by norm_num) hY0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  rw [hsqrt, hlogY]
  rw [hlogY] at hlogY1
  have h1 : 2 * s ^ 2 * (4 * Real.log s) ≤ 8 * s ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlogs (by positivity : (0 : ℝ) ≤ 8 * s ^ 2)
    nlinarith
  have h6 : 0.6931471803 * Y ≤ Real.log 2 * Y := mul_le_mul_of_nonneg_right hl2.le hY0.le
  have h2 : 8 * s ^ 3 + 4 * s + 1 ≤ s ^ 4 / 10 := by
    have h3 : 80 * s ^ 3 ≤ s ^ 4 := by
      have : (80 : ℝ) ≤ s := le_trans (by norm_num) hs25
      nlinarith [pow_pos hs0 3]
    have h4 : 40 * s + 10 ≤ s ^ 3 := by
      have h5 : (40 : ℝ) ≤ s := le_trans (by norm_num) hs25
      nlinarith [sq_nonneg s]
    nlinarith
  linarith

/-- **`⌊x⌋ ≤ y#`** at the smoothness level. -/
lemma floor_le_primorial_halfY {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    ⌊x⌋₊ ≤ primorial (halfY x) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, -⟩ := half_params hx
  obtain ⟨-, -, -, -, -, hyh⟩ := halfY_facts hx
  have ha := halfA_ge hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hx1 : 1 ≤ x := by
    have : Real.exp 0 ≤ x := le_trans (Real.exp_le_exp.2 (Real.exp_pos _).le) hx
    rwa [Real.exp_zero] at this
  refine floor_le_primorial_of_log_le hx1 ?_
  -- `e^a ≥ e^{Λ+2}·e^{98} ≥ 4 log x` and `≥ 2^{101}`
  have h1 : Real.exp (halfA x) ≥ Real.exp (Real.log (Real.log x) + 100) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (Real.log (Real.log x) + 100) = Real.log x * Real.exp 100 := by
    rw [Real.exp_add, hexpΛ]
  have h3 : (4 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have h4 : (2 : ℝ) ^ 101 ≤ Real.exp 100 := by
    rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    have := Real.exp_one_gt_d9
    have h5 : (2.7 : ℝ) ^ 100 ≤ Real.exp 1 ^ 100 := pow_le_pow_left₀ (by norm_num) (by linarith) 100
    linarith [show (2 : ℝ) ^ 101 ≤ 2.7 ^ 100 by norm_num]
  have hY : (2 : ℝ) ^ 100 ≤ (halfY x : ℝ) := by
    have : Real.exp 100 ≤ Real.exp (halfA x) := by
      have h6 : Real.exp 100 ≤ Real.exp (Real.log (Real.log x) + 100) :=
        Real.exp_le_exp.2 (by linarith)
      linarith
    nlinarith
  have hθ := half_le_theta_lower hY
  have hLY : Real.log x ≤ (halfY x : ℝ) / 2 := by
    have : Real.log x * 4 ≤ Real.exp (halfA x) := by
      have := mul_le_mul_of_nonneg_left h3 hLpos.le
      nlinarith
    linarith
  linarith

/-! ### The windows' bounds -/

lemma half_room :
    (20 : ℝ) / 4 + 3 * Real.sqrt ((2000 : ℕ) : ℝ) / 4 + 1 ≤ 1 / 50 * ((2000 : ℕ) : ℝ) := by
  have hs : Real.sqrt ((2000 : ℕ) : ℝ) ≤ 4473 / 100 := by
    calc Real.sqrt ((2000 : ℕ) : ℝ) ≤ Real.sqrt ((4473 / 100) ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num)
      _ = 4473 / 100 := Real.sqrt_sq (by norm_num)
  push_cast
  linarith

lemma half_mono : (3 : ℝ) ≤ 8 * (1 / 50) * Real.sqrt ((2000 : ℕ) : ℝ) := by
  have hs : (44 : ℝ) ≤ Real.sqrt ((2000 : ℕ) : ℝ) := by
    rw [show (44 : ℝ) = Real.sqrt (44 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc (3 : ℝ) ≤ 8 * (1 / 50) * 44 := by norm_num
    _ ≤ 8 * (1 / 50) * Real.sqrt ((2000 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)

lemma half_tilt_le {Λ : ℝ} (hΛ : 110 ≤ Λ) : 1 / (16 * Λ) ≤ 1 / 10 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma half_level_le {Λ : ℝ} (hΛ : 2105 ≤ Λ) : radBlockBadLevel (1 / (16 * Λ)) ≤ 20 := by
  have hE₀le : 1 / (16 * Λ) ≤ (1 / 183) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsqrt : Real.sqrt (1 / (16 * Λ)) ≤ 1 / 183 := by
    calc Real.sqrt (1 / (16 * Λ)) ≤ Real.sqrt ((1 / 183) ^ 2) := Real.sqrt_le_sqrt hE₀le
      _ = 1 / 183 := Real.sqrt_sq (by norm_num)
  rw [radBlockBadLevel, harperSharpDeficit]
  linarith

lemma halfSigma_mul_log_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    halfSigma x * Real.log (halfY x) ≤ 1 / (16 * Real.log (Real.log x)) := by
  obtain ⟨-, hL, hΛ, -, -, -⟩ := half_params hx
  obtain ⟨-, -, hlogy_le, -, -, -⟩ := halfY_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hΛpos : 0 < Real.log (Real.log x) := by linarith
  have h1 : Real.log (halfY x) ≤ 2 * Real.log x / Real.log (Real.log x) := hlogy_le
  rw [halfSigma]
  calc 1 / 32 / Real.log x * Real.log (halfY x)
      ≤ 1 / 32 / Real.log x * (2 * Real.log x / Real.log (Real.log x)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / (16 * Real.log (Real.log x)) := by
        field_simp
        ring

end RMF
