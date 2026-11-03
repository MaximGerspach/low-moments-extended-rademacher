/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Analysis.IteratedLog
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The scales of the hierarchy

The scales of the hierarchy behind the sharp bound for `½ < q ≤ 1`
(`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp`): `z_ℓ = ⌊x^{1/V_ℓ}⌋₊` with
`V_ℓ = 3·log_ℓ Λ`, `Λ = log log x`, `ℓ ≤ L`, where the proof takes `L` the last level with
`log_L Λ ≥ 2` (`RMF.exists_maximal_iterLog_ge`).  `RMF.exists_hierarchyScales` records what the
levels of `Weighted/SharpLevels.lean` need at the scales, once `Λ ≥ 2` and `12Λ ≤ log x`:

* at every scale, `3 ≤ z_ℓ ≤ x` and `log z_ℓ ≤ log x/V_ℓ`;
* at consecutive scales, with `κ = log z_{ℓ+1}/log z_ℓ`: `z_ℓ ≤ z_{ℓ+1}`, `κ ≥ e`,
  `2 log κ ≤ log x/log z_{ℓ+1}` and `log κ ≤ log_{ℓ+1} Λ`;
* at the bottom scale, `log z_0 ≥ e`, `2 log log z_0 ≤ log x/log z_0` and `log log z_0 ≤ Λ`;
* at the top scale, `log x/log z_L ≤ 6e²`.

The floors cost at most `log 2` in `log z_ℓ` (`RMF.log_floor_exp_bounds`), against
`log x/V_ℓ ≥ 4`.  Up to that cost `κ = log_ℓ Λ/log_{ℓ+1} Λ = e^s/s` with `s = log_{ℓ+1} Λ ≥ 2`,
and `e²/2 ≤ e^s/s ≤ e^s/2`.
-/

namespace RMF

/-- **The logarithm of `⌊e^u⌋₊`**: for `u ≥ 1`, `u - log 2 ≤ log ⌊e^u⌋₊ ≤ u`, since
`e^u/2 ≤ e^u - 1 < ⌊e^u⌋₊ ≤ e^u`. -/
lemma log_floor_exp_bounds {u : ℝ} (hu : 1 ≤ u) :
    u - Real.log 2 ≤ Real.log (⌊Real.exp u⌋₊ : ℝ) ∧ Real.log (⌊Real.exp u⌋₊ : ℝ) ≤ u := by
  have he : (2 : ℝ) ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hfl := Nat.lt_floor_add_one (Real.exp u)
  have hhalf : Real.exp u / 2 ≤ (⌊Real.exp u⌋₊ : ℝ) := by linarith
  have hfl0 : (0 : ℝ) < (⌊Real.exp u⌋₊ : ℝ) := by linarith
  constructor
  · calc u - Real.log 2 = Real.log (Real.exp u / 2) := by
          rw [Real.log_div (Real.exp_pos u).ne' two_ne_zero, Real.log_exp]
      _ ≤ Real.log (⌊Real.exp u⌋₊ : ℝ) := Real.log_le_log (by positivity) hhalf
  · calc Real.log (⌊Real.exp u⌋₊ : ℝ) ≤ Real.log (Real.exp u) :=
          Real.log_le_log hfl0 (Nat.floor_le (Real.exp_pos u).le)
      _ = u := Real.log_exp u

/-- **The scales of the hierarchy.**  For `0 < x`, `Λ = log log x ≥ 2` and `12Λ ≤ log x` there are
`L` with `RMF.IterLogGood L Λ` and scales `z_ℓ` such that `3 ≤ z_ℓ ≤ x` and
`log z_ℓ ≤ log x/(3·log_ℓ Λ)` for `ℓ ≤ L`; `z_ℓ ≤ z_{ℓ+1}`, `e ≤ κ`, `log κ ≤ log_{ℓ+1} Λ` and
`2 log κ ≤ log x/log z_{ℓ+1}` for `ℓ < L` (`κ = log z_{ℓ+1}/log z_ℓ`); `e ≤ log z_0`,
`2 log log z_0 ≤ log x/log z_0`, `log log z_0 ≤ Λ` and `log x/log z_L ≤ 6e²`.
They are the hypotheses of the levels, of the layered inequality and of the level sums. -/
theorem exists_hierarchyScales {x : ℝ} (hx0 : 0 < x) (hΛ : 2 ≤ Real.log (Real.log x))
    (hx : 12 * Real.log (Real.log x) ≤ Real.log x) :
    ∃ (L : ℕ) (z : ℕ → ℕ),
      IterLogGood L (Real.log (Real.log x)) ∧
      (∀ ℓ ≤ L, 3 ≤ z ℓ ∧ (z ℓ : ℝ) ≤ x ∧
        Real.log (z ℓ) ≤ Real.log x / (3 * iterLog ℓ (Real.log (Real.log x)))) ∧
      (∀ ℓ < L, z ℓ ≤ z (ℓ + 1) ∧ Real.exp 1 ≤ Real.log (z (ℓ + 1)) / Real.log (z ℓ) ∧
        2 * Real.log (Real.log (z (ℓ + 1)) / Real.log (z ℓ))
          ≤ Real.log x / Real.log (z (ℓ + 1)) ∧
        Real.log (Real.log (z (ℓ + 1)) / Real.log (z ℓ))
          ≤ iterLog (ℓ + 1) (Real.log (Real.log x))) ∧
      Real.exp 1 ≤ Real.log (z 0) ∧
      2 * Real.log (Real.log (z 0)) ≤ Real.log x / Real.log (z 0) ∧
      Real.log (Real.log (z 0)) ≤ Real.log (Real.log x) ∧
      Real.log x / Real.log (z L) ≤ 6 * Real.exp 2 := by
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
  rw [← hΛdef] at hΛ hx ⊢
  obtain ⟨L, hL, hL1⟩ := exists_maximal_iterLog_ge (by norm_num : (1 : ℝ) ≤ 2) hΛ
  have hgood : IterLogGood L Λ := fun i hi => le_trans (by norm_num) (hL i hi)
  have hlogx : 24 ≤ Real.log x := by linarith
  have htΛ : ∀ ℓ ≤ L, iterLog ℓ Λ ≤ Λ := fun ℓ hℓ => by
    simpa using iterLog_le_iterLog (Nat.zero_le ℓ) (hgood.mono hℓ)
  have ht0 : ∀ ℓ ≤ L, (0 : ℝ) < 3 * iterLog ℓ Λ := fun ℓ hℓ => by linarith [hL ℓ hℓ]
  -- `u_ℓ = log x/V_ℓ`
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun ℓ => Real.log x / (3 * iterLog ℓ Λ) := ⟨_, rfl⟩
  have huℓ : ∀ ℓ, u ℓ = Real.log x / (3 * iterLog ℓ Λ) := fun ℓ => by rw [hu]
  have hu3 : ∀ ℓ ≤ L, u ℓ * (3 * iterLog ℓ Λ) = Real.log x := fun ℓ hℓ => by
    rw [huℓ, div_mul_cancel₀ _ (ht0 ℓ hℓ).ne']
  have hu4 : ∀ ℓ ≤ L, 4 ≤ u ℓ := fun ℓ hℓ => by
    rw [huℓ, le_div_iff₀ (ht0 ℓ hℓ)]
    linarith [htΛ ℓ hℓ]
  -- the scales and their logarithms
  obtain ⟨z, hz⟩ : ∃ z : ℕ → ℕ, z = fun ℓ => ⌊Real.exp (u ℓ)⌋₊ := ⟨_, rfl⟩
  have hzℓ : ∀ ℓ, z ℓ = ⌊Real.exp (u ℓ)⌋₊ := fun ℓ => by rw [hz]
  have hlz : ∀ ℓ ≤ L, u ℓ - Real.log 2 ≤ Real.log (z ℓ) ∧ Real.log (z ℓ) ≤ u ℓ :=
    fun ℓ hℓ => by
      rw [hzℓ]
      exact log_floor_exp_bounds (by linarith [hu4 ℓ hℓ])
  have hlz3 : ∀ ℓ ≤ L, 3 < Real.log (z ℓ) := fun ℓ hℓ => by
    linarith [(hlz ℓ hℓ).1, hu4 ℓ hℓ, Real.log_two_lt_d9]
  have he1 := Real.exp_one_gt_d9
  have hee : (1 / 4 : ℝ) ≤ Real.exp 1 ^ 2 / 2 - Real.exp 1 := by
    have h17 : (1.7 : ℝ) ≤ Real.exp 1 - 1 := by linarith
    nlinarith [mul_le_mul h17 h17 (by norm_num) (by linarith)]
  -- every scale
  have hevery : ∀ ℓ ≤ L, 3 ≤ z ℓ ∧ (z ℓ : ℝ) ≤ x ∧
      Real.log (z ℓ) ≤ Real.log x / (3 * iterLog ℓ Λ) := by
    intro ℓ hℓ
    refine ⟨?_, ?_, ?_⟩
    · rw [hzℓ]
      exact Nat.le_floor (by exact_mod_cast (show (3 : ℝ) ≤ Real.exp (u ℓ) by
        linarith [Real.add_one_le_exp (u ℓ), hu4 ℓ hℓ]))
    · rw [hzℓ]
      refine le_trans (Nat.floor_le (Real.exp_pos _).le) ?_
      calc Real.exp (u ℓ) ≤ Real.exp (Real.log x) := by
            rw [Real.exp_le_exp, huℓ]
            exact div_le_self (by linarith) (by linarith [hL ℓ hℓ])
        _ = x := Real.exp_log hx0
    · rw [← huℓ]
      exact (hlz ℓ hℓ).2
  -- consecutive scales
  have hcons : ∀ ℓ < L, z ℓ ≤ z (ℓ + 1) ∧ Real.exp 1 ≤ Real.log (z (ℓ + 1)) / Real.log (z ℓ) ∧
      2 * Real.log (Real.log (z (ℓ + 1)) / Real.log (z ℓ))
        ≤ Real.log x / Real.log (z (ℓ + 1)) ∧
      Real.log (Real.log (z (ℓ + 1)) / Real.log (z ℓ)) ≤ iterLog (ℓ + 1) Λ := by
    intro ℓ hℓ
    have hℓ0 : ℓ ≤ L := hℓ.le
    have hℓ1 : ℓ + 1 ≤ L := hℓ
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = iterLog (ℓ + 1) Λ := ⟨_, rfl⟩
    have hs2 : 2 ≤ s := by
      rw [hs]
      exact hL (ℓ + 1) hℓ1
    have hts : iterLog ℓ Λ = Real.exp s := by
      rw [hs, iterLog_succ, Real.exp_log (hgood.pos hℓ0)]
    -- `u_{ℓ+1}·s = u_ℓ·e^s`
    have hrel : u (ℓ + 1) * s = u ℓ * Real.exp s := by
      have h1 := hu3 (ℓ + 1) hℓ1
      have h2 := hu3 ℓ hℓ0
      rw [← hs] at h1
      rw [hts] at h2
      linarith
    have hu4ℓ := hu4 ℓ hℓ0
    have hlzℓ := hlz ℓ hℓ0
    have hlzs := hlz (ℓ + 1) hℓ1
    have hpos : 0 < Real.log (z ℓ) := by linarith [hlz3 ℓ hℓ0]
    have hposs : 0 < Real.log (z (ℓ + 1)) := by linarith [hlz3 (ℓ + 1) hℓ1]
    have hlog2 := Real.log_two_lt_d9
    -- `e^s ≥ (e²/2)·s`, so `u_{ℓ+1} ≥ (e²/2)·u_ℓ`
    have hexps : Real.exp 1 ^ 2 / 2 * s ≤ Real.exp s := by
      have h1 := exp_one_mul_le_exp (s - 1)
      have h2 : Real.exp s = Real.exp 1 * Real.exp (s - 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le,
        mul_nonneg (sq_nonneg (Real.exp 1)) (sub_nonneg.2 hs2)]
    have hus : Real.exp 1 ^ 2 / 2 * u ℓ ≤ u (ℓ + 1) := by
      have h := mul_le_mul_of_nonneg_left hexps (by linarith : (0 : ℝ) ≤ u ℓ)
      have h' : Real.exp 1 ^ 2 / 2 * u ℓ * s ≤ u (ℓ + 1) * s := by linarith
      exact le_of_mul_le_mul_right h' (by linarith)
    -- `κ ≥ e`
    have hκ : Real.exp 1 ≤ Real.log (z (ℓ + 1)) / Real.log (z ℓ) := by
      rw [le_div_iff₀ hpos]
      have h1 : (1 / 4 : ℝ) * 4 ≤ (Real.exp 1 ^ 2 / 2 - Real.exp 1) * u ℓ :=
        mul_le_mul hee hu4ℓ (by norm_num) (by linarith)
      linarith [mul_le_mul_of_nonneg_left hlzℓ.2 (Real.exp_pos 1).le, hlzs.1]
    -- `κ ≤ e^s`, so `log κ ≤ s`
    have hκle : Real.log (z (ℓ + 1)) / Real.log (z ℓ) ≤ Real.exp s := by
      rw [div_le_iff₀ hpos]
      have h1 : u ℓ / 2 ≤ Real.log (z ℓ) := by linarith [hlzℓ.1]
      have h2 : Real.exp s * (u ℓ / 2) ≤ Real.exp s * Real.log (z ℓ) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos s).le
      have h3 : u (ℓ + 1) * 2 ≤ u (ℓ + 1) * s :=
        mul_le_mul_of_nonneg_left hs2 (by linarith [hu4 (ℓ + 1) hℓ1])
      linarith [hlzs.2]
    have hκ0 : 0 < Real.log (z (ℓ + 1)) / Real.log (z ℓ) := div_pos hposs hpos
    have hlogκ : Real.log (Real.log (z (ℓ + 1)) / Real.log (z ℓ)) ≤ s := by
      have h := Real.log_le_log hκ0 hκle
      rwa [Real.log_exp] at h
    refine ⟨?_, hκ, ?_, ?_⟩
    · -- `z_ℓ ≤ z_{ℓ+1}`
      rw [hzℓ, hzℓ]
      have h1 : (0 : ℝ) ≤ (Real.exp 1 ^ 2 / 2 - 1) * u ℓ := mul_nonneg (by linarith) (by linarith)
      exact Nat.floor_mono (Real.exp_le_exp.2 (by linarith))
    · -- `2 log κ ≤ log x/log z_{ℓ+1}`
      rw [le_div_iff₀ hposs]
      have h1 := hu3 (ℓ + 1) hℓ1
      rw [← hs] at h1
      have h2 : 3 * s * Real.log (z (ℓ + 1)) ≤ 3 * s * u (ℓ + 1) :=
        mul_le_mul_of_nonneg_left hlzs.2 (by linarith)
      have h3 : 2 * Real.log (Real.log (z (ℓ + 1)) / Real.log (z ℓ)) * Real.log (z (ℓ + 1))
          ≤ 3 * s * Real.log (z (ℓ + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) hposs.le
      linarith
    · rw [← hs]
      exact hlogκ
  -- the bottom scale
  have hbot : Real.exp 1 ≤ Real.log (z 0) ∧
      2 * Real.log (Real.log (z 0)) ≤ Real.log x / Real.log (z 0) ∧
      Real.log (Real.log (z 0)) ≤ Λ := by
    have h0 := hlz 0 (Nat.zero_le L)
    have hu0 := hu3 0 (Nat.zero_le L)
    rw [iterLog_zero] at hu0
    have hpos : 0 < Real.log (z 0) := by linarith [hlz3 0 (Nat.zero_le L)]
    have hloglog : Real.log (Real.log (z 0)) ≤ Λ := by
      rw [hΛdef]
      refine Real.log_le_log hpos (le_trans h0.2 ?_)
      rw [huℓ, iterLog_zero]
      exact div_le_self (by linarith) (by linarith)
    refine ⟨by linarith [hlz3 0 (Nat.zero_le L), Real.exp_one_lt_d9], ?_, hloglog⟩
    rw [le_div_iff₀ hpos]
    have h2 : 3 * Λ * Real.log (z 0) ≤ 3 * Λ * u 0 :=
      mul_le_mul_of_nonneg_left h0.2 (by linarith)
    have h3 : 2 * Real.log (Real.log (z 0)) * Real.log (z 0) ≤ 3 * Λ * Real.log (z 0) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    linarith
  -- the top scale
  have htop : Real.log x / Real.log (z L) ≤ 6 * Real.exp 2 := by
    have hpos : 0 < Real.log (z L) := by linarith [hlz3 L le_rfl]
    rw [div_le_iff₀ hpos]
    have htL : iterLog L Λ < Real.exp 2 := by
      have h := Real.exp_lt_exp.2 hL1
      rwa [iterLog_succ, Real.exp_log (hgood.pos le_rfl)] at h
    have h1 := hu3 L le_rfl
    have h2 : u L / 2 ≤ Real.log (z L) := by
      linarith [(hlz L le_rfl).1, hu4 L le_rfl, Real.log_two_lt_d9]
    have h3 : u L * (3 * iterLog L Λ) ≤ u L * (3 * Real.exp 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith [hu4 L le_rfl])
    have h4 : 6 * Real.exp 2 * (u L / 2) ≤ 6 * Real.exp 2 * Real.log (z L) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  exact ⟨L, z, hgood, hevery, hcons, hbot.1, hbot.2.1, hbot.2.2, htop⟩

end RMF
