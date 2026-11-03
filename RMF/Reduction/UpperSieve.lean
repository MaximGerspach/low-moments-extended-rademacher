/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.UpperAveraged
import RMF.Reduction.StepsSieve

/-!
# Harper's upper bound at the sieve constant `1.001·e^{-γ}`

The assembly of Harper's upper bound with the reduction at `RMF.sieveConst = 1.001·e^{-γ}`
(`RMF.reduction_upper_sieve`) rather than at `RMF.roughCountConst = 3`.  That needs three more
facts at Harper's cutoff `y = ⌊Y⌋`:
* `log y ≥ 10⁶`, from `y ≥ exp(exp ℓ₀)` with `e^{ℓ₀} ≥ 10⁶`;
* `(x^{1/4})^{1/(2 log y)} ≥ 40000 log² y`, since `log y ≤ log x/L²` makes the left side at least
  `e^{L²/8}` and `log y ≤ e^L` (`RMF.harperCutoff_sieve_level`);
* `5x^{1/4}(1 + log x^{1/4})³·20000 log y ≤ √x/2`, since `25000 t⁴ ≤ e^{t/4}` for `t = log x`
  (`RMF.harperCutoff_sieve_error`).

The reduction constant becomes `RMF.reductionSieveConst q = (1.001e^{-γ}/2π)^q ∑_n w_n^q`.
`RMF.harper_upper_of_chaos_sieve` takes the chaos moments as a hypothesis; at the averaged free
start they are `RMF.integral_chaosUnit_rpow_le_averaged`.

The threshold is `x ≥ exp(exp Λ)` for a level `Λ` given by inequalities, each monotone in
`L = log log x ≥ Λ` (`RMF.mul_sub_mul_log_le`): the cutoff reaches the chaos's start `exp(exp ℓ₀)`
once `ℓ₀ + 1 + 2 log L ≤ L` (`RMF.exp_exp_le_floor_harperCutoff`, from `log Y = e^L/L²`), and costs
`k` on the target once `k²(2 log L + 1) ≤ (k² - 1)L`
(`RMF.loglog_le_sq_mul_loglog_floor_harperCutoff_of_level`).
-/

open MeasureTheory
open scoped Real

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The sieve conditions at Harper's cutoff -/

/-- `40000 ≤ e^{11}`. -/
lemma forty_thousand_le_exp_eleven : (40000 : ℝ) ≤ Real.exp 11 := by
  have h := Real.exp_one_gt_d9
  have h11 : Real.exp 11 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h11]
  calc (40000 : ℝ) ≤ 2.7182818283 ^ 11 := by norm_num
    _ ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) h.le 11

/-- `2.5·10⁹ ≤ e^{22}`. -/
lemma two_point_five_billion_le_exp_twenty_two : (2500000000 : ℝ) ≤ Real.exp 22 := by
  have h := Real.exp_one_gt_d9
  have h22 : Real.exp 22 = Real.exp 1 ^ 22 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h22]
  calc (2500000000 : ℝ) ≤ 2.7182818283 ^ 22 := by norm_num
    _ ≤ Real.exp 1 ^ 22 := pow_le_pow_left₀ (by norm_num) h.le 22

/-- The logarithm of the rounded-down cutoff: `0 < log ⌊Y⌋ ≤ log x/L²` with `L = log log x`. -/
lemma log_floor_harperCutoff_mem {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    0 < Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)
      ∧ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)
        ≤ Real.log x / Real.log (Real.log x) ^ 2 := by
  have hY36 : Real.exp 36 ≤ harperCutoff x := exp_le_harperCutoff hx
  have hexp36 : (37 : ℝ) ≤ Real.exp 36 := by
    have := Real.add_one_le_exp (36 : ℝ)
    linarith
  have hY0 : (0 : ℝ) < harperCutoff x := by linarith
  have hfl : harperCutoff x / 2 ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (harperCutoff x)
    linarith
  refine ⟨Real.log_pos (by linarith), ?_⟩
  rw [← log_harperCutoff]
  exact Real.log_le_log (by linarith) (Nat.floor_le hY0.le)

/-- **The level condition at Harper's cutoff**: `(x^{1/4})^{1/(2 log y)} ≥ 40000 log² y` for
`y = ⌊Y⌋`.  The left side is `e^{log x/(8 log y)} ≥ e^{L²/8}`, and `40000 log² y ≤ e^{11 + 2L}`
since `log y ≤ log x = e^L`; `11 + 2L ≤ L²/8` for `L ≥ 36`. -/
lemma harperCutoff_sieve_level {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    40000 * Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ^ 2
      ≤ (x ^ (1 / 4 : ℝ)) ^ (1 / (2 * Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ))) := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  obtain ⟨hℓ0, hℓle⟩ := log_floor_harperCutoff_mem hx
  set L := Real.log (Real.log x) with hL
  set ℓ := Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) with hℓ
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hL0 : (0 : ℝ) < L := by linarith
  have hR : (x ^ (1 / 4 : ℝ)) ^ (1 / (2 * ℓ)) = Real.exp (Real.log x / (8 * ℓ)) := by
    rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
    congr 1
    field_simp
    ring
  rw [hR]
  have hℓL : ℓ * L ^ 2 ≤ Real.log x := (le_div_iff₀ (by positivity)).1 hℓle
  have h1 : L ^ 2 / 8 ≤ Real.log x / (8 * ℓ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hℓu : ℓ ≤ Real.log x := by nlinarith [mul_le_mul_of_nonneg_left hL2 hℓ0.le]
  have hlx : Real.log x = Real.exp L := (Real.exp_log hu0).symm
  have h2 : 40000 * ℓ ^ 2 ≤ Real.exp (11 + 2 * L) := by
    rw [show 11 + 2 * L = 11 + (L + L) by ring, Real.exp_add, Real.exp_add, ← hlx]
    have h40 := forty_thousand_le_exp_eleven
    have hsq : ℓ ^ 2 ≤ Real.log x * Real.log x := by nlinarith
    exact mul_le_mul h40 hsq (sq_nonneg _) (Real.exp_pos _).le
  have h3 : 11 + 2 * L ≤ L ^ 2 / 8 := by nlinarith
  calc 40000 * ℓ ^ 2 ≤ Real.exp (11 + 2 * L) := h2
    _ ≤ Real.exp (L ^ 2 / 8) := Real.exp_le_exp.2 h3
    _ ≤ Real.exp (Real.log x / (8 * ℓ)) := Real.exp_le_exp.2 h1

/-- **The error condition at Harper's cutoff**: `5x^{1/4}(1 + log x^{1/4})³·20000 log y ≤ √x/2`
for `y = ⌊Y⌋`.  With `t = log x ≥ e^{36}`, `log y ≤ t` and `1 + t/4 ≤ t/2`, it reduces to
`25000 t⁴ ≤ e^{t/4}`, and `t⁴ ≤ 4!·8⁴ e^{t/8}` with `e^{t/8} ≥ e^{22} ≥ 2.5·10⁹`. -/
lemma harperCutoff_sieve_error {x : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) :
    5 * x ^ (1 / 4 : ℝ) * (1 + Real.log (x ^ (1 / 4 : ℝ))) ^ 3
        * (20000 * Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ))
      ≤ Real.sqrt x / 2 := by
  obtain ⟨hx0, hu36, hL36⟩ := harper_regime hx
  obtain ⟨hℓ0, hℓle⟩ := log_floor_harperCutoff_mem hx
  set t := Real.log x with ht
  set ℓ := Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) with hℓ
  have hexp36 : (648 : ℝ) ≤ Real.exp 36 := by
    have h := Real.pow_div_factorial_le_exp 36 (by norm_num) 2
    norm_num [Nat.factorial] at h
    linarith
  have ht648 : 648 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hL1 : 1 ≤ Real.log (Real.log x) := by linarith
  have hℓt : ℓ ≤ t := by
    refine hℓle.trans (div_le_self ht0.le ?_)
    nlinarith
  -- `x^{1/4} = e^{t/4}`, `√x = e^{t/4}·e^{t/4}`, `log x^{1/4} = t/4`
  have hD : x ^ (1 / 4 : ℝ) = Real.exp (t / 4) := by
    rw [Real.rpow_def_of_pos hx0, ← ht]
    congr 1
    ring
  have hsq : Real.sqrt x = Real.exp (t / 4) * Real.exp (t / 4) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← Real.exp_add, ← ht]
    congr 1
    ring
  have hlogD : Real.log (x ^ (1 / 4 : ℝ)) = t / 4 := by
    rw [Real.log_rpow hx0]
    ring
  rw [hlogD, hD, hsq]
  -- `t⁴ ≤ 98304 e^{t/8}` and `e^{t/8} ≥ 2.5·10⁹`
  have h4 : t ^ 4 ≤ 98304 * Real.exp (t / 8) := by
    have h := Real.pow_div_factorial_le_exp (t / 8) (by positivity) 4
    norm_num [Nat.factorial] at h
    nlinarith
  have h22 : (2500000000 : ℝ) ≤ Real.exp (t / 8) :=
    two_point_five_billion_le_exp_twenty_two.trans (Real.exp_le_exp.2 (by linarith))
  have he : Real.exp (t / 4) = Real.exp (t / 8) * Real.exp (t / 8) := by
    rw [← Real.exp_add]
    ring_nf
  have hcube : (1 + t / 4) ^ 3 ≤ t ^ 3 / 8 := by
    have h1 : 1 + t / 4 ≤ t / 2 := by linarith
    have h2 : (1 + t / 4) ^ 3 ≤ (t / 2) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
    linarith [show (t / 2) ^ 3 = t ^ 3 / 8 by ring]
  have hE0 : 0 < Real.exp (t / 8) := Real.exp_pos _
  have hkey : 200000 * (1 + t / 4) ^ 3 * ℓ ≤ Real.exp (t / 4) := by
    have hA : 200000 * (1 + t / 4) ^ 3 * ℓ ≤ 25000 * t ^ 4 := by
      have hc0 : 0 ≤ (1 + t / 4) ^ 3 := by positivity
      calc 200000 * (1 + t / 4) ^ 3 * ℓ ≤ 200000 * (t ^ 3 / 8) * t := by
            gcongr
        _ = 25000 * t ^ 4 := by ring
    rw [he]
    nlinarith
  have hEt4 : 0 < Real.exp (t / 4) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left hkey hEt4.le]

/-! ### The threshold as a level -/

/-- **`aL - b log L` is increasing past `b/a`**: `aΛ - b log Λ ≤ aL - b log L` for `b ≤ aΛ` and
`0 < Λ ≤ L`, since `b log(L/Λ) ≤ b(L/Λ - 1) ≤ a(L - Λ)`. -/
lemma mul_sub_mul_log_le {a b Λ L : ℝ} (hb : 0 ≤ b) (hΛ0 : 0 < Λ) (hbΛ : b ≤ a * Λ)
    (hΛL : Λ ≤ L) : a * Λ - b * Real.log Λ ≤ a * L - b * Real.log L := by
  have hL0 : 0 < L := lt_of_lt_of_le hΛ0 hΛL
  have h1 : Real.log (L / Λ) ≤ L / Λ - 1 := Real.log_le_sub_one_of_pos (div_pos hL0 hΛ0)
  rw [Real.log_div hL0.ne' hΛ0.ne', div_sub_one hΛ0.ne'] at h1
  have h2 : b * (Real.log L - Real.log Λ) ≤ b * ((L - Λ) / Λ) := mul_le_mul_of_nonneg_left h1 hb
  have h3 : b * ((L - Λ) / Λ) = b / Λ * (L - Λ) := by ring
  have h4 : b / Λ * (L - Λ) ≤ a * (L - Λ) :=
    mul_le_mul_of_nonneg_right ((div_le_iff₀ hΛ0).2 hbΛ) (by linarith)
  have h5 : b * (Real.log L - Real.log Λ) ≤ a * (L - Λ) := by linarith
  have e1 : b * (Real.log L - Real.log Λ) = b * Real.log L - b * Real.log Λ := by ring
  have e2 : a * (L - Λ) = a * L - a * Λ := by ring
  rw [e1, e2] at h5
  linarith

/-- **The cutoff reaches a double-exponential start**: `exp(exp ℓ₀) ≤ ⌊Y⌋` for the Harper cutoff
`Y` once `ℓ₀ + 1 + 2 log L ≤ L`, with `L = log log x` and `ℓ₀ ≥ 0`.  `log Y = e^L/L² ≥ e^{ℓ₀ + 1}
≥ e^{ℓ₀} + 1`, so `Y ≥ e^{e^{ℓ₀} + 1} ≥ e^{e^{ℓ₀}} + 1`. -/
lemma exp_exp_le_floor_harperCutoff {x ℓ₀ : ℝ} (hx : Real.exp (Real.exp 36) ≤ x) (hℓ₀ : 0 ≤ ℓ₀)
    (h : ℓ₀ + 1 + 2 * Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x)) :
    Real.exp (Real.exp ℓ₀) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
  obtain ⟨-, hu36, hL36⟩ := harper_regime hx
  have hu0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hu36
  have hL0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hE : Real.exp (Real.log (Real.log x) - 2 * Real.log (Real.log (Real.log x)))
      = Real.log (harperCutoff x) := by
    rw [log_harperCutoff, Real.exp_sub, Real.exp_log hu0, ← Real.log_rpow hL0,
      Real.exp_log (Real.rpow_pos_of_pos hL0 _), Real.rpow_two]
  have h1 : Real.exp ℓ₀ + 1 ≤ Real.log (harperCutoff x) := by
    rw [← hE]
    exact le_trans (exp_add_one_le_exp_add_one hℓ₀) (Real.exp_le_exp.2 (by linarith))
  have hY0 : (0 : ℝ) < harperCutoff x := by
    rw [harperCutoff]
    exact Real.exp_pos _
  have h2 : Real.exp (Real.exp ℓ₀) + 1 ≤ harperCutoff x :=
    calc Real.exp (Real.exp ℓ₀) + 1 ≤ Real.exp (Real.exp ℓ₀ + 1) :=
          exp_add_one_le_exp_add_one (Real.exp_pos _).le
      _ ≤ Real.exp (Real.log (harperCutoff x)) := Real.exp_le_exp.2 h1
      _ = harperCutoff x := Real.exp_log hY0
  have := Nat.lt_floor_add_one (harperCutoff x)
  linarith

/-- **The cutoff costs a factor `k` on the target, past a level**: `log log x ≤ k² log log ⌊Y⌋`
for the Harper cutoff `Y` once `L = log log x ≥ Λ ≥ 36` and `k²(2 log Λ + 1) ≤ (k² - 1)Λ`.
`log log ⌊Y⌋ ≥ L - 2 log L - 1` (`RMF.loglog_floor_harperCutoff_ge_sub_two_log`), and
`(k² - 1)L - 2k² log L` is increasing past `Λ` (`RMF.mul_sub_mul_log_le`). -/
lemma loglog_le_sq_mul_loglog_floor_harperCutoff_of_level {x k Λ : ℝ} (hk : 1 < k)
    (hx : Real.exp (Real.exp 36) ≤ x) (hΛ36 : 36 ≤ Λ) (hΛL : Λ ≤ Real.log (Real.log x))
    (hΛk : k ^ 2 * (2 * Real.log Λ + 1) ≤ (k ^ 2 - 1) * Λ) :
    Real.log (Real.log x) ≤ k ^ 2 * Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)) := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hlogΛ : 1 ≤ Real.log Λ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have h3 : k ^ 2 * 3 ≤ k ^ 2 * (2 * Real.log Λ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hk2.le
  have hmono := mul_sub_mul_log_le (a := k ^ 2 - 1) (b := 2 * k ^ 2) (by positivity)
    (by linarith) (by linarith) hΛL
  have hfl := mul_le_mul_of_nonneg_left (loglog_floor_harperCutoff_ge_sub_two_log hx) hk2.le
  have e1 : k ^ 2 * (Real.log (Real.log x) - 2 * Real.log (Real.log (Real.log x)) - 1)
      = (k ^ 2 - 1) * Real.log (Real.log x) - 2 * k ^ 2 * Real.log (Real.log (Real.log x))
        - k ^ 2 + Real.log (Real.log x) := by ring
  have e2 : k ^ 2 * (2 * Real.log Λ + 1) = 2 * k ^ 2 * Real.log Λ + k ^ 2 := by ring
  rw [e1] at hfl
  rw [e2] at hΛk
  linarith

/-! ### The reduction constant -/

/-- **The constant of the reduction to the unit chaos, at the sieve constant**:
`(1.001e^{-γ}/2π)^q ∑_n w_n^q`. -/
noncomputable def reductionSieveConst (q : ℝ) : ℝ :=
  (sieveConst / (2 * π)) ^ q * ∑' n : ℤ, lineWeight n ^ q

lemma reductionSieveConst_nonneg (q : ℝ) : 0 ≤ reductionSieveConst q :=
  mul_nonneg (Real.rpow_nonneg (div_nonneg sieveConst_pos.le (by positivity)) q)
    (tsum_nonneg fun n => Real.rpow_nonneg (lineWeight_nonneg n) q)

/-! ### The assembly -/

/-- **Harper's upper bound on `[2/3, 1]` from the chaos moments, at the sieve constant**: by
`RMF.reduction_upper_sieve`, if the chaos moments hold past `exp(exp ℓ₀)`, then past `exp(exp Λ)`
`E|S_x|^{2q} ≤ (k·reductionSieveConst q·K(q) + η)(1 + (1-q)√(log log x))^{-q}`.  The level `Λ`
pays, at `L = log log x ≥ Λ`, for the cutoff to reach the chaos's start (`ℓ₀ + 1 + 2 log Λ ≤ Λ`),
for the cutoff's cost `k` on the target (`k²(2 log Λ + 1) ≤ (k² - 1)Λ`), and for the Rankin term to
be an `η`-fraction of the target (`RMF.harper_error_bound`, `RMF.exp_neg_mul_sq_le_mul_target`);
`e^{ℓ₀} ≥ 10⁶` is the sieve's `log y ≥ 10⁶`. -/
theorem harper_upper_of_chaos_sieve {K : ℝ → ℝ} {ℓ₀ k η Λ : ℝ} (hk : 1 < k) (hη : 0 < η)
    (hℓ₀ : 1000000 ≤ Real.exp ℓ₀) (hΛ36 : 36 ≤ Λ) (hΛℓ : ℓ₀ + 1 + 2 * Real.log Λ ≤ Λ)
    (hΛk : k ^ 2 * (2 * Real.log Λ + 1) ≤ (k ^ 2 - 1) * Λ)
    (hΛC : 3 * (|Real.log reductionUpperConst| + reductionUpperExponent) / reductionUpperDecay
      ≤ Λ)
    (hΛη : 6 * (1 + |Real.log η|) / reductionUpperDecay ≤ Λ)
    (hchaos : ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ y q : ℝ, Real.exp (Real.exp ℓ₀) ≤ y → 2 / 3 ≤ q → q ≤ 1 →
        ∫ ω, chaosUnit f y ω ^ q ∂μ
          ≤ K q * (1 + (1 - q) * Real.sqrt (Real.log (Real.log y))) ^ (-q)) :
    ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ x q : ℝ, Real.exp (Real.exp Λ) ≤ x → 2 / 3 ≤ q → q ≤ 1 →
        ∫ ω, ‖normalisedSum f x ω‖ ^ (2 * q) ∂μ
          ≤ (k * reductionSieveConst q * K q + η)
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
  obtain ⟨hCe, hK, hc, hy₀N, hred⟩ := reduction_upper_sieve (Ω := Ω)
  intro f μ hf x q hx hq23 hq1
  obtain ⟨hx36, hLT⟩ := harper_regime_of hΛ36 hx
  have hℓ₀0 : 0 ≤ ℓ₀ := Real.one_le_exp_iff.1 (by linarith)
  -- the thresholds at `L = log log x ≥ Λ`
  have hthr : 3 * (|Real.log reductionUpperConst| + reductionUpperExponent) / reductionUpperDecay
      ≤ Real.log (Real.log x) := le_trans hΛC hLT
  have hthrη : 6 * (1 + |Real.log η|) / reductionUpperDecay ≤ Real.log (Real.log x) :=
    le_trans hΛη hLT
  have hstart : ℓ₀ + 1 + 2 * Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
    have h := mul_sub_mul_log_le (a := 1) (b := 2) (by norm_num) (by linarith) (by linarith) hLT
    linarith
  -- the cutoff, rounded down
  have hY0 : (0 : ℝ) < harperCutoff x :=
    lt_of_lt_of_le (Real.exp_pos 36) (exp_le_harperCutoff hx36)
  have hy₀' : Real.exp (Real.exp ℓ₀) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) :=
    exp_exp_le_floor_harperCutoff hx36 hℓ₀0 hstart
  have hee : Real.exp ℓ₀ ≤ Real.exp (Real.exp ℓ₀) := by
    linarith [Real.add_one_le_exp (Real.exp ℓ₀)]
  have hy₀y : reductionUpperStart ≤ ⌊harperCutoff x⌋₊ := by
    have hR : reductionUpperStart ≤ 4 := by
      unfold reductionUpperStart smoothCountDecay
      refine max_le le_rfl (Nat.ceil_le.2 ?_)
      have h1 : Real.exp (1 / 4) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
      have h2 := Real.exp_one_lt_d9
      push_cast
      linarith
    have hR' : ((reductionUpperStart : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hR
    exact_mod_cast (show ((reductionUpperStart : ℕ) : ℝ) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) by
      linarith)
  have hℓ : 1000000 ≤ Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hy₀'
    rw [Real.log_exp] at h
    linarith
  have hy2 : (2 : ℝ) ≤ ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := by exact_mod_cast le_trans hy₀N hy₀y
  have hlogy : 0 < Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  -- the reduction, the periodisation, the chaos, the target
  have h1 := hred f μ hf x ⌊harperCutoff x⌋₊ q hy₀y (harperCutoff_sieve hx36) hℓ
    (harperCutoff_sieve_level hx36) (harperCutoff_sieve_error hx36) (by linarith) hq1
  have h2 := periodisation_upper_sharp f μ hf ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) q hy2
    (by linarith) hq1
  have h3 := hchaos f μ hf ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) q hy₀' hq23 hq1
  have h4 := rpow_neg_target_le_of_sq_le
    (t := Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ))) (Λ := Real.log (Real.log x)) hk.le
    (loglog_le_sq_mul_loglog_floor_harperCutoff_of_level hk hx36 hΛ36 hLT hΛk) (by linarith) hq1
  -- the error term
  have h5 := harper_error_bound (C := reductionUpperConst) (K := reductionUpperExponent)
    (c := reductionUpperDecay) (q := q) (ℓ := Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ))
    hCe hK hc hx36 hthr hq23 hq1 hlogy
    (Real.log_le_log (by linarith) (Nat.floor_le hY0.le))
  have hthrη' : 2 * (1 + |Real.log η|) / (reductionUpperDecay / 3) ≤ Real.log (Real.log x) := by
    rw [div_div_eq_mul_div]
    have heq : 2 * (1 + |Real.log η|) * 3 / reductionUpperDecay
        = 6 * (1 + |Real.log η|) / reductionUpperDecay := by ring
    rw [heq]
    exact hthrη
  have h6 := exp_neg_mul_sq_le_mul_target (c := reductionUpperDecay / 3) (q := q)
    (by positivity) hη hx36 hthrη' hq23 hq1
  -- assemble
  have hTy0 : 0 < (1 + (1 - q)
      * Real.sqrt (Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)))) ^ (-q) := by
    refine Real.rpow_pos_of_pos ?_ _
    have := mul_nonneg (sub_nonneg.2 hq1)
      (Real.sqrt_nonneg (Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ))))
    linarith
  have hU0 : (0 : ℝ) ≤ ∫ ω, chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (chaosUnit_nonneg hy2 ω) _
  have hKq : 0 ≤ K q := nonneg_of_mul_nonneg_left (le_trans hU0 h3) hTy0
  have hW0 : 0 ≤ ∑' n : ℤ, lineWeight n ^ q :=
    tsum_nonneg fun n => Real.rpow_nonneg (lineWeight_nonneg n) q
  have hR0 : 0 ≤ (sieveConst / (2 * π)) ^ q :=
    Real.rpow_nonneg (div_nonneg sieveConst_pos.le (by positivity)) q
  have hmain : (sieveConst / (2 * π)) ^ q
        * ∫ ω, eulerLineIntegral f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ
      ≤ k * reductionSieveConst q * K q
        * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
    calc (sieveConst / (2 * π)) ^ q
          * ∫ ω, eulerLineIntegral f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ
        ≤ (sieveConst / (2 * π)) ^ q * ((∑' n : ℤ, lineWeight n ^ q)
            * ∫ ω, chaosUnit f ((⌊harperCutoff x⌋₊ : ℕ) : ℝ) ω ^ q ∂μ) :=
          mul_le_mul_of_nonneg_left h2 hR0
      _ ≤ (sieveConst / (2 * π)) ^ q * ((∑' n : ℤ, lineWeight n ^ q)
            * (K q * (1 + (1 - q)
              * Real.sqrt (Real.log (Real.log ((⌊harperCutoff x⌋₊ : ℕ) : ℝ)))) ^ (-q))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hW0) hR0
      _ ≤ (sieveConst / (2 * π)) ^ q * ((∑' n : ℤ, lineWeight n ^ q)
            * (K q * (k * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h4 hKq) hW0) hR0
      _ = k * reductionSieveConst q * K q
            * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by
          rw [reductionSieveConst]
          ring
  have hgoal : (k * reductionSieveConst q * K q + η)
        * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
      = k * reductionSieveConst q * K q
          * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
        + η * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q) := by ring
  rw [hgoal]
  linarith [h1, hmain, h5, h6]

end RMF
