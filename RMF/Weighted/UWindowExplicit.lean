/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ThetaWindowExplicit

/-!
# The windows of `Z` at an exponent `q ≤ ½`

The windows of `RMF/Weighted/ThetaWindowExplicit.lean` at a general exponent `0 ≤ q ≤ ½`, for the
bound (U), `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}` with `Λ = log log x`.

* **(PF) at the split point** `z_k = ⌈exp(θe^k)⌉`: `E‖F_{z_k+1}(½+σ)‖^{2q} ≤ RMF.thetaPF σ θ q k`,
  `≈ (θe^k)^{-q(1-2q)}`, the geometric decay in `k` that (U) sums
  (`RMF.integral_norm_randomEulerProduct_thetaSplit_le`);
* **the window's constant at `q`**: the two-point ratio's exponent is `2(1-q)S₂`, so
  `G_k(q)² = (2/θ)W(2(1-q)b_k)e^{…}` (`RMF.thetaWindowConstQ`, `RMF.thetaWindowConst` at `q = ½`);
* **one window** by Jensen (`RMF.window_theta_le_jensen_q`) or by the weighted chaos at any offset
  `D ≥ max(k + 8, 105)`, with `K_ϑ = e^{D-k}` (`RMF.window_theta_le_chaos_q`): the low windows of
  (U) need the PNT floor `104` far above their split point, hence the level shift.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The windows at exponent `q` -/

/-- The square of the `k`-th window's constant at slope `θ` and exponent `q`:
`(2/θ)·W(2(1-q)b_k)·e^{9.0028/log y + 9.0028e^{-k}/θ}`, `b_k = RMF.thetaWindowExp θ k`;
`RMF.thetaWindowConst` at `q = ½`. -/
noncomputable def thetaWindowConstQ (θ q : ℝ) (k y : ℕ) : ℝ :=
  2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
    * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ)

/-- (PF) at the `k`-th window's split point, from above:
`e^{q(1-2q)(9.0028/(θe^k) + 2σ(θe^k + 1/100 + log 4 + 4) - 3/20)}·(θe^k)^{q(2q-1)}`. -/
noncomputable def thetaPF (σ θ q : ℝ) (k : ℕ) : ℝ :=
  Real.exp (q * (1 - 2 * q) * (9.0028 / (θ * Real.exp k)
      + 2 * σ * (θ * Real.exp k + 1 / 100 + Real.log 4 + 4) - 3 / 20))
    * (θ * Real.exp k) ^ (q * (2 * q - 1))

lemma thetaWindowConstQ_half (θ : ℝ) (k y : ℕ) :
    thetaWindowConstQ θ (1 / 2) k y = thetaWindowConst θ k y := by
  rw [thetaWindowConstQ, thetaWindowConst]
  norm_num

lemma thetaPF_nonneg (σ θ q : ℝ) (k : ℕ) (hθ : 0 ≤ θ) : 0 ≤ thetaPF σ θ q k := by
  unfold thetaPF
  have := Real.exp_pos (k : ℝ)
  have h0 : 0 ≤ θ * Real.exp k := by positivity
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg h0 _)

/-- **(PF) at the window's split point**: `E‖F_{z_k+1}(½+σ)‖^{2q} ≤ RMF.thetaPF σ θ q k` for
`z_k = RMF.thetaSplit θ k`, `0 ≤ q ≤ ½`, `σ ≥ 0`: the sharp bound
`RMF.IsRademacherRMF.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp` at
`θe^k ≤ log z_k ≤ θe^k + 1/100`. -/
lemma integral_norm_randomEulerProduct_thetaSplit_le {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {σ θ q : ℝ} (hσ : 0 ≤ σ) (hθ : 1 ≤ θ) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 2) {k : ℕ} (hk : 2 ≤ k) :
    (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (thetaSplit θ k + 1)
        (shiftLine σ 0) ω‖ ^ (2 * q) ∂ν) ≤ thetaPF σ θ q k := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => Y p ω) ν := hY.isRademacherRMF
  have hz2 := two_le_thetaSplit hθ k
  have h1 := hRa.integral_norm_randomEulerProduct_shift_rpow_le_log_sharp hσ hq0 hq hz2
  have hs : shiftLine σ 0 = (((1 / 2 + σ : ℝ)) : ℂ) := by simp [shiftLine]
  rw [hs]
  refine le_trans h1 ?_
  have hθe : 0 < θ * Real.exp k := mul_pos (by linarith) (Real.exp_pos _)
  have hlz := mul_exp_le_log_thetaSplit θ k
  have hlz0 : 0 < Real.log (thetaSplit θ k) := lt_of_lt_of_le hθe hlz
  have hlz1 : Real.log (thetaSplit θ k) ≤ θ * Real.exp k + 1 / 100 := by
    have h2 := log_thetaSplit_add_one_le hθ hk
    have h3 : Real.log (thetaSplit θ k) ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < thetaSplit θ k)) (by push_cast; linarith)
    linarith
  have ha : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq0 (by linarith)
  have hinv : 9.0028 / Real.log (thetaSplit θ k) ≤ 9.0028 / (θ * Real.exp k) :=
    div_le_div_of_nonneg_left (by norm_num) hθe hlz
  have hσl : 2 * σ * (Real.log (thetaSplit θ k) + Real.log 4 + 4)
      ≤ 2 * σ * (θ * Real.exp k + 1 / 100 + Real.log 4 + 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hexp : Real.exp (q * (1 - 2 * q) * (9.0028 / Real.log (thetaSplit θ k)
        + 2 * σ * (Real.log (thetaSplit θ k) + Real.log 4 + 4) - 3 / 20))
      ≤ Real.exp (q * (1 - 2 * q) * (9.0028 / (θ * Real.exp k)
        + 2 * σ * (θ * Real.exp k + 1 / 100 + Real.log 4 + 4) - 3 / 20)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) ha)
  have hpow : Real.log (thetaSplit θ k) ^ (q * (2 * q - 1))
      ≤ (θ * Real.exp k) ^ (q * (2 * q - 1)) :=
    Real.rpow_le_rpow_of_nonpos hθe hlz (mul_nonpos_of_nonneg_of_nonpos hq0 (by linarith))
  unfold thetaPF
  exact mul_le_mul hexp hpow (Real.rpow_nonneg hlz0.le _) (Real.exp_pos _).le

/-- **The window's weight and mean at exponent `q`, against the window's constant**:
`(2/log y)·(W(βT²)/T)·(log y/log z_k)e^{…} ≤ RMF.thetaWindowConstQ θ q k y` for
`β = 2(1-q)S₂(z_k+1)`, since `βT² ≤ 2(1-q)b_k` and `T log z_k ≥ θ`. -/
lemma two_div_mul_window_le_thetaWindowConstQ {θ q : ℝ} (hθ : 1 ≤ θ) (hq1 : q ≤ 1) {k y : ℕ}
    (hk : 2 ≤ k) (hky : θ * Real.exp k ≤ Real.log y) :
    2 / Real.log y * (taylorWindowW (2 * (1 - q) * (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2)
          / Real.exp (-(k : ℝ))
        * (Real.log y / Real.log (thetaSplit θ k)
          * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))))
      ≤ thetaWindowConstQ θ q k y := by
  have hθ0 : 0 < θ := by linarith
  have hek : (1 : ℝ) ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (by nlinarith) hky
  have hlz := mul_exp_le_log_thetaSplit θ k
  have hlz0 : 0 < Real.log (thetaSplit θ k) := lt_of_lt_of_le (by positivity) hlz
  have hT0 : 0 < Real.exp (-(k : ℝ)) := Real.exp_pos _
  have hEk : Real.exp k * Real.exp (-(k : ℝ)) = 1 := by rw [← Real.exp_add]; simp
  have h1q : 0 ≤ 2 * (1 - q) := by linarith
  set b := 2 * (1 - q) * (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
    + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2
    with hbdef
  have hb0 : 0 ≤ b := by
    have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
    positivity
  have hbk : b ≤ 2 * (1 - q) * thetaWindowExp θ k := by
    have h := thetaWindow_beta_le hθ hk
    have e : b = 2 * (1 - q) * ((Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
        + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) * Real.exp (-(k : ℝ)) ^ 2) := by
      rw [hbdef]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h h1q
  have hW0 : 0 ≤ taylorWindowW b := taylorWindowW_nonneg hb0
  have hWW : taylorWindowW b ≤ taylorWindowW (2 * (1 - q) * thetaWindowExp θ k) :=
    taylorWindowW_mono hbk
  have hTz : θ ≤ Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k) := by
    calc θ = Real.exp (-(k : ℝ)) * (θ * Real.exp k) := by
          rw [mul_comm θ, ← mul_assoc, mul_comm (Real.exp (-(k : ℝ))), hEk, one_mul]
      _ ≤ Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k) :=
          mul_le_mul_of_nonneg_left hlz hT0.le
  have hinv : 9.0028 / Real.log (thetaSplit θ k) ≤ 9.0028 * Real.exp (-(k : ℝ)) / θ := by
    rw [div_le_div_iff₀ hlz0 hθ0]
    nlinarith
  have hexp : Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))
      ≤ Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) :=
    Real.exp_le_exp.2 (by linarith)
  set Ex := Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k)) with hExdef
  have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
  have heq : 2 / Real.log y * (taylorWindowW b / Real.exp (-(k : ℝ))
      * (Real.log y / Real.log (thetaSplit θ k) * Ex))
      = 2 * taylorWindowW b * Ex / (Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k)) := by
    field_simp
  rw [heq, thetaWindowConstQ]
  rw [div_le_iff₀ (mul_pos hT0 hlz0)]
  have h1 : 2 * taylorWindowW b * Ex ≤ 2 * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hWW (by norm_num)) hexp hEx0
      (mul_nonneg (by norm_num) (le_trans hW0 hWW))
  have hG0 : 0 ≤ 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) := by
    have : 0 ≤ taylorWindowW (2 * (1 - q) * thetaWindowExp θ k) := le_trans hW0 hWW
    positivity
  have h3 : 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) * θ
      ≤ 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ)
      * (Real.exp (-(k : ℝ)) * Real.log (thetaSplit θ k)) :=
    mul_le_mul_of_nonneg_left hTz hG0
  have h4 : 2 / θ * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) * θ
      = 2 * taylorWindowW (2 * (1 - q) * thetaWindowExp θ k)
      * Real.exp (9.0028 / Real.log y + 9.0028 * Real.exp (-(k : ℝ)) / θ) := by
    field_simp
  linarith

/-- **One window at exponent `q ≤ ½`, split at slope `θ`, by Jensen**: for `1 ≤ θ`, `k ≥ 2` with
`θe^k ≤ log y` and `σ > 0`,
`(2/log y)^q·E[(∫_{T_k/e}^{T_k}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^q]
  ≤ RMF.thetaPF σ θ q k·(RMF.thetaWindowConstQ θ q k y)^q`. -/
theorem window_theta_le_jensen_q {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsRademacherPrimeValues Y ν) {θ q : ℝ} (hθ : 1 ≤ θ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    {k y : ℕ} {σ : ℝ} (hσ : 0 < σ) (hk : 2 ≤ k) (hky : θ * Real.exp k ≤ Real.log y) :
    (2 / Real.log y) ^ q * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν
      ≤ thetaPF σ θ q k * thetaWindowConstQ θ q k y ^ q := by
  have hθ0 : 0 < θ := by linarith
  have hek : (1 : ℝ) ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
  have hlogy : 0 < Real.log y := lt_of_lt_of_le (by nlinarith) hky
  have hz2 := two_le_thetaSplit hθ k
  have hzy := thetaSplit_le hθ0 hky
  set β := 2 * (1 - q) * (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) with hβdef
  have hβ0 : 0 ≤ β := by
    have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
    have : 0 ≤ 1 - q := by linarith
    positivity
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ (Real.exp_pos (-(k : ℝ))) hβ0
  have h := integral_rpow_window_le_split_jensen_of_weight hY hz2 hzy (σ := σ) (q := q)
    (T := Real.exp (-(k : ℝ))) (β := β) hσ hq0 hq (Real.exp_pos _) le_rfl hR
  have hPF := integral_norm_randomEulerProduct_thetaSplit_le hY hσ.le hθ hq0 hq hk
  have hW := two_div_mul_window_le_thetaWindowConstQ (q := q) hθ (by linarith) hk hky
  set Q := taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) / Real.exp (-(k : ℝ))
      * (Real.log y / Real.log (thetaSplit θ k)
        * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))) with hQdef
  have hQ0 : 0 ≤ Q := by
    have hlz0 : 0 < Real.log (thetaSplit θ k) :=
      lt_of_lt_of_le (by positivity) (mul_exp_le_log_thetaSplit θ k)
    have h1 : 0 ≤ taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) :=
      taylorWindowW_nonneg (by positivity)
    positivity
  have hPF0 : 0 ≤ thetaPF σ θ q k := thetaPF_nonneg σ θ q k hθ0.le
  have hstep : (∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν) ≤ thetaPF σ θ q k * Q ^ q :=
    le_trans h (mul_le_mul_of_nonneg_right hPF (Real.rpow_nonneg hQ0 _))
  have h2y : (0 : ℝ) ≤ (2 / Real.log y) ^ q := Real.rpow_nonneg (by positivity) _
  have hWq : (2 / Real.log y * Q) ^ q ≤ thetaWindowConstQ θ q k y ^ q :=
    Real.rpow_le_rpow (mul_nonneg (by positivity) hQ0) hW hq0
  calc (2 / Real.log y) ^ q * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν
      ≤ (2 / Real.log y) ^ q * (thetaPF σ θ q k * Q ^ q) := mul_le_mul_of_nonneg_left hstep h2y
    _ = thetaPF σ θ q k * (2 / Real.log y * Q) ^ q := by
        rw [Real.mul_rpow (by positivity) hQ0]
        ring
    _ ≤ thetaPF σ θ q k * thetaWindowConstQ θ q k y ^ q := mul_le_mul_of_nonneg_left hWq hPF0

/-- **One window at exponent `q ≤ ½`, split at slope `θ`, by the weighted chaos at an offset
`D ≥ max(k + 8, 105)`**: for `1 ≤ θ ≤ 2`, `k ≥ 2`, `D ≤ ⌊log log y⌋`, `σ log y ≤ E₀ ≤ 1/10` and the
chaos's parameters,

`(2/log y)^q·E[(∫_{T_k/e}^{T_k}(σ²+t²)⁻¹‖F_{y+1}(½+σ+it)‖²dt)^q]
  ≤ RMF.thetaPF σ θ q k·(RMF.thetaWindowConstQ θ q k y)^q
    ·shiftMomentConst 1 C_i (C_b e^{D-k}) A s λ δ q·(1 + (1-q)√n)^{-q}`,

`n = harperBlockCount D y`: `K_ϑ = T_k e^ϑ ≤ e^{D-k}`, the offset `ϑ ∈ [D-1, D)` at least the PNT
floor `104`. -/
theorem window_theta_le_chaos_q (E₀ βc : ℝ) (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 10)
    (hβc : 1 / 2 < βc) (hβc2 : βc ≤ 2) {Tr κ Amax δ : ℝ} {N : ℕ} (hTr : 4 < Tr)
    (hκ : 1 ≤ κ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hN : Amax / 4 + 3 * Real.sqrt (N : ℝ) / 4 + 1 ≤ δ * N)
    (hmono : 3 ≤ 8 * δ * Real.sqrt (N : ℝ))
    {Y : ℕ → Ω → ℂ} {ν : Measure Ω} (hY : IsRademacherPrimeValues Y ν) {θ q : ℝ} (hθ : 1 ≤ θ)
    (hθ2 : θ ≤ 2) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) {k y D : ℕ} {σ A lam : ℝ}
    (hσ : 0 < σ) (hk : 2 ≤ k) (hkD : k + 8 ≤ D) (hD105 : 105 ≤ D)
    (hDy : D ≤ ⌊Real.log (Real.log y)⌋₊)
    (hσy : σ * Real.log y ≤ E₀) (hNn : N ≤ harperBlockCount D y)
    (hA : radBlockBadLevel E₀ ≤ A) (hAmax : A ≤ Amax) (hlam : 1 ≤ lam) :
    (2 / Real.log y) ^ q * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν
      ≤ thetaPF σ θ q k * thetaWindowConstQ θ q k y ^ q
        * (shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
            (radBlockBadConst E₀ βc * Real.exp ((D : ℝ) - k))
            A (radAveragedShift E₀ βc Tr κ) lam δ q
          * (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q)) := by
  have hθ0 : 0 < θ := by linarith
  -- `log log y ≥ D`
  have hLL : ((D : ℕ) : ℝ) ≤ Real.log (Real.log y) :=
    (Nat.le_floor_iff' (by omega)).1 hDy
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkDR : (k : ℝ) + 8 ≤ (D : ℝ) := by exact_mod_cast hkD
  have hDR : (105 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD105
  have hy2 : 2 ≤ y := by
    by_contra hcon
    have hy1 : y ≤ 1 := by omega
    have h0 : Real.log (Real.log y) = 0 := by
      interval_cases y <;> simp
    rw [h0] at hLL
    have : (0 : ℝ) < ((D : ℕ) : ℝ) := by positivity
    linarith
  have hlogy : 0 < Real.log y :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- `θe^k ≤ e^{k+1} ≤ log y`
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hθek : θ * Real.exp k ≤ Real.exp ((k : ℝ) + 1) := by
    calc θ * Real.exp k ≤ 2 * Real.exp k := mul_le_mul_of_nonneg_right hθ2 (Real.exp_pos _).le
      _ ≤ Real.exp 1 * Real.exp k := mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
      _ = Real.exp ((k : ℝ) + 1) := by rw [Real.exp_add, mul_comm]
  have hky' : θ * Real.exp k ≤ Real.log y := by
    refine le_trans hθek ?_
    calc Real.exp ((k : ℝ) + 1) ≤ Real.exp (Real.log (Real.log y)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.log y := Real.exp_log hlogy
  -- the offset
  have hϑlo : (D : ℝ) - 1 ≤ harperOffset D y := sub_one_le_harperOffset D (y : ℝ)
  have hϑhi : harperOffset D y < (D : ℝ) := harperOffset_lt_natCast D (y : ℝ)
  have hϑ104 : (104 : ℝ) ≤ harperOffset D y := by linarith
  have hϑ : radFreeStartThreshold E₀ ≤ harperOffset D y :=
    le_trans (radFreeStartThreshold_le_104 hE₀ (by linarith)) hϑ104
  -- the window's conditions
  have hT1 : Real.exp (-(k : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hlo : 600 * Real.exp (2 * E₀) ≤ 2 * (Real.exp (-(k : ℝ)) / Real.exp 1)
      * Real.exp (harperOffset D y) := by
    have h1 : 2 * (Real.exp (-(k : ℝ)) / Real.exp 1) * Real.exp (harperOffset D y)
        = 2 * Real.exp (harperOffset D y - k - 1) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    rw [h1]
    have h2 : Real.exp 6 ≤ Real.exp (harperOffset D y - k - 1) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : (403 : ℝ) ≤ Real.exp 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
      have := Real.exp_one_gt_d9
      have h4 : (2.718 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
      linarith [show (403 : ℝ) ≤ 2.718 ^ 6 by norm_num]
    have h5 : Real.exp (2 * E₀) ≤ Real.exp (1 / 5) := Real.exp_le_exp.2 (by linarith)
    have h6 := exp_one_fifth_le
    linarith
  have hKθ : Real.exp (-(k : ℝ)) * Real.exp (harperOffset D y) ≤ Real.exp ((D : ℝ) - k) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hzb : ((thetaSplit θ k + 1 : ℕ) : ℝ) ≤ blockScale (harperOffset D y) 0 := by
    have hl := log_thetaSplit_add_one_le hθ hk
    have hpos : (0 : ℝ) < ((thetaSplit θ k + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((thetaSplit θ k + 1 : ℕ) : ℝ) ≤ Real.exp (θ * Real.exp k + 1 / 100) :=
      (Real.log_le_iff_le_exp hpos).1 hl
    refine le_trans h1 ?_
    rw [blockScale]
    refine Real.exp_le_exp.2 ?_
    have h2 : Real.exp ((k : ℝ) + 2) ≤ Real.exp (((0 : ℕ) : ℝ) + harperOffset D y) :=
      Real.exp_le_exp.2 (by push_cast; linarith)
    have h3 : Real.exp ((k : ℝ) + 2) = Real.exp ((k : ℝ) + 1) * Real.exp 1 := by
      rw [← Real.exp_add]
      ring_nf
    have h6 : Real.exp ((k : ℝ) + 1) * 2 ≤ Real.exp ((k : ℝ) + 1) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left he1 (Real.exp_pos _).le
    have h4 : (1 : ℝ) ≤ Real.exp ((k : ℝ) + 1) := Real.one_le_exp (by positivity)
    calc θ * Real.exp k + 1 / 100 ≤ Real.exp ((k : ℝ) + 1) * 2 := by linarith
      _ ≤ Real.exp ((k : ℝ) + 1) * Real.exp 1 := h6
      _ = Real.exp ((k : ℝ) + 2) := h3.symm
      _ ≤ _ := h2
  set β := 2 * (1 - q) * (Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) ^ 2 / 2
      + 15.003 * Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) + 34) with hβdef
  have hβ0 : 0 ≤ β := by
    have hl0 : 0 ≤ Real.log ((thetaSplit θ k + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ thetaSplit θ k + 1))
    have : 0 ≤ 1 - q := by linarith
    positivity
  have hR := setIntegral_inv_sq_add_sq_mul_exp_window_le_taylor σ (Real.exp_pos (-(k : ℝ))) hβ0
  have h := integral_rpow_window_le_split_chaos_of_weight E₀ βc hE₀ (by linarith) hβc hβc2 hTr
    hκ hδ0 hδ hN hmono hY (two_le_thetaSplit hθ k) (thetaSplit_le hθ0 hky') (D := D)
    (σ := σ) (η := E₀) (q := q) (T := Real.exp (-(k : ℝ))) (Kθ := Real.exp ((D : ℝ) - k))
    (A := A) (lam := lam) hσ hq0 hq (Real.exp_pos _) hT1 le_rfl hLL hϑ hϑ104 hE₀ le_rfl hσy
    hlo hKθ hzb hNn hA hAmax hlam hR
  have hPF := integral_norm_randomEulerProduct_thetaSplit_le hY hσ.le hθ hq0 hq hk
  have hW := two_div_mul_window_le_thetaWindowConstQ (q := q) hθ (by linarith) hk hky'
  set Q := taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) / Real.exp (-(k : ℝ))
      * (Real.log y / Real.log (thetaSplit θ k)
        * Real.exp (9.0028 / Real.log y + 9.0028 / Real.log (thetaSplit θ k))) with hQdef
  have hQ0 : 0 ≤ Q := by
    have hlz0 : 0 < Real.log (thetaSplit θ k) :=
      lt_of_lt_of_le (by positivity) (mul_exp_le_log_thetaSplit θ k)
    have h1 : 0 ≤ taylorWindowW (β * Real.exp (-(k : ℝ)) ^ 2) :=
      taylorWindowW_nonneg (by positivity)
    positivity
  set C := shiftMomentConst 1 (radAveragedConst E₀ βc Tr κ)
    (radBlockBadConst E₀ βc * Real.exp ((D : ℝ) - k))
    A (radAveragedShift E₀ βc Tr κ) lam δ q with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef, shiftMomentConst]
    exact le_trans (Real.rpow_nonneg (by positivity) _) (le_max_left _ _)
  set G := (1 + (1 - q) * Real.sqrt (harperBlockCount D y : ℝ)) ^ (-q) with hGdef
  have hG0 : 0 ≤ G := by
    have : 0 ≤ 1 - q := by linarith
    exact Real.rpow_nonneg (by positivity) _
  have hPF0 : 0 ≤ thetaPF σ θ q k := thetaPF_nonneg σ θ q k hθ0.le
  have hQq : 0 ≤ Q ^ q := Real.rpow_nonneg hQ0 _
  have hstep : (∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1) (Real.exp (-(k : ℝ))),
      (σ ^ 2 + t ^ 2)⁻¹ * ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
        (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν) ≤ thetaPF σ θ q k * (C * Q ^ q * G) :=
    le_trans h (mul_le_mul_of_nonneg_right hPF (by positivity))
  have h2y : (0 : ℝ) ≤ (2 / Real.log y) ^ q := Real.rpow_nonneg (by positivity) _
  have hWq : (2 / Real.log y * Q) ^ q ≤ thetaWindowConstQ θ q k y ^ q :=
    Real.rpow_le_rpow (mul_nonneg (by positivity) hQ0) hW hq0
  calc (2 / Real.log y) ^ q * ∫ ω, (∫ t in Set.Icc (Real.exp (-(k : ℝ)) / Real.exp 1)
        (Real.exp (-(k : ℝ))), (σ ^ 2 + t ^ 2)⁻¹ *
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) (y + 1)
          (shiftLine σ t) ω‖ ^ 2) ^ q ∂ν
      ≤ (2 / Real.log y) ^ q * (thetaPF σ θ q k * (C * Q ^ q * G)) :=
        mul_le_mul_of_nonneg_left hstep h2y
    _ = thetaPF σ θ q k * (2 / Real.log y * Q) ^ q * (C * G) := by
        rw [Real.mul_rpow (by positivity) hQ0]
        ring
    _ ≤ thetaPF σ θ q k * thetaWindowConstQ θ q k y ^ q * (C * G) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWq hPF0) (mul_nonneg hC0 hG0)

end RMF
