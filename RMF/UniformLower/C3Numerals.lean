/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.C3Numerals.Dispatch

/-!
# (C3)*'s numerals: `c₃(q)` as a certified step function

The constant of `RMF.le_setIntegral_halfLadder_twistQ_explicit` certified in numerals at the
damping `σe^k ≤ 1/200` and the smoothing `δ = 10⁻⁴`, for every `0 ≤ q ≤ ½ + 1/20`.

* **The grid.**  `q`-intervals of width `1/100` on `[0, ¼]`, `1/400` on `[¼, 0.35]`, `1/200` on
  `[0.35, ½]`, then `[½, ½ + 1/400]` and `[½ + 1/400, 11/20]`; heights by the 24 cells of
  `RMF.c3Theta` (finest at `ϑ = 0`, where every interval's minimum sits).  On each (interval, cell)
  a value of `t` is fixed and `c ≤ c3Val` certified by `RMF.le_c3Val_of_num`
  (`C3Numerals/Cells*.lean`).
* **The ladder lengths.**  Below `½`: `K ≤ K_max(q) = max(1, ⌊1/(1 - 2q)⌋)` (`RMF.c3Kmax`), by the
  Ville factor at `K_b` (`RMF.C3CellCert.of_le`) or at a truncation step `i₀`
  (`RMF.villeFactor_le_trunc`); for `q ≥ 0.46` every `K`.
* **The results.**  The step function `RMF.c3Floor` with
  `RMF.le_setIntegral_halfLadder_twistQ_c3Floor`, and per height cell `RMF.c3CellFloor`, both
  certified by `RMF.c3Floor_spec`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- **The certified `c₃(q)`**: the value of the grid step `[n/400, (n+1)/400)` containing `q`
(`RMF.c3FloorTab`), a step function on `0 ≤ q ≤ 11/20`. -/
noncomputable def c3Floor (q : ℝ) : ℝ := c3FloorTab ⌊400 * q⌋₊

/-- **The certified `c₃` on height cell `j`** of `RMF.c3Theta`, on `q`'s grid step. -/
noncomputable def c3CellFloor (q : ℝ) (j : ℕ) : ℝ := c3CellTab ⌊400 * q⌋₊ j

/-- **The step function's certificate**: for `0 ≤ q ≤ 11/20` a `q`-interval `[q_lo, q_hi] ∋ q`
with ladder lengths `K ≤ K_b` (every `K` when `K_b = 0`; else `q < q_hi < ½` and
`(K_b + 1)(1 - 2q_hi) ≥ 1`) on which every cell of `RMF.c3Theta` is certified at `c3Floor q`, and
cell `j` at `c3CellFloor q j`. -/
theorem c3Floor_spec {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11 / 20) :
    ∃ q_lo q_hi : ℝ, ∃ Kb : ℕ, q_lo ≤ q ∧ q ≤ q_hi ∧ 0 ≤ q_lo ∧ q_hi ≤ 1
      ∧ (Kb ≠ 0 → q < q_hi ∧ q_hi < 1 / 2 ∧ 1 ≤ Kb ∧ 1 ≤ ((Kb : ℝ) + 1) * (1 - 2 * q_hi))
      ∧ C3IntervalCert c3Theta 24 q_lo q_hi (c3Floor q) Kb
      ∧ ∀ j < 24, C3CellCert q_lo q_hi (c3Theta j) (c3Theta (j + 1)) (c3CellFloor q j)
        (fun K => Kb = 0 ∨ K ≤ Kb) := by
  set n := ⌊400 * q⌋₊ with hn
  have hn0 : (n : ℝ) ≤ 400 * q := Nat.floor_le (by positivity)
  have hn1 : 400 * q < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn220 : n ≤ 220 := by
    have : (n : ℝ) ≤ 220 := by linarith
    exact_mod_cast this
  obtain ⟨q_lo, q_hi, Kb, ⟨h0, h1, h2, h3, hKb⟩, hcert, hcells⟩ := c3Step_spec n hn220
  have hqlo : q_lo ≤ q := by
    have : (n : ℝ) / 400 ≤ q := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  have hmin : q ≤ min (((n : ℝ) + 1) / 400) (11 / 20) :=
    le_min (by rw [le_div_iff₀ (by norm_num)]; linarith) hq1
  refine ⟨q_lo, q_hi, Kb, hqlo, hmin.trans h2, h0, h3, fun hK => ?_, hcert, hcells⟩
  obtain ⟨hq_hi, hKb1, hKb2⟩ := hKb hK
  refine ⟨?_, hq_hi, hKb1, hKb2⟩
  have hlt : q < ((n : ℝ) + 1) / 400 := by
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  have h2' : ((n : ℝ) + 1) / 400 ≤ q_hi := by
    rcases le_total (((n : ℝ) + 1) / 400) (11 / 20) with h | h
    · rwa [min_eq_left h] at h2
    · rw [min_eq_right h] at h2
      linarith
  linarith

/-- The step function's floor: `c3Floor q ≥ 0.03849` for `0 ≤ q ≤ 11/20` (the minimum, on
`q ∈ [¼, 101/400)`). -/
theorem c3Floor_ge {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11 / 20) : 0.03849 ≤ c3Floor q := by
  have hn0 : ((⌊400 * q⌋₊ : ℕ) : ℝ) ≤ 400 * q := Nat.floor_le (by positivity)
  have hn : ⌊400 * q⌋₊ ≤ 220 := by
    have : ((⌊400 * q⌋₊ : ℕ) : ℝ) ≤ 220 := by linarith
    exact_mod_cast this
  exact c3FloorTab_ge _ hn

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- The ladder lengths of the step's certificate: `K_b = 0`, or `K ≤ K_b` from `K ≤ K_max(q)`. -/
lemma c3_kok_of_le_c3Kmax {q q_hi : ℝ} {Kb K : ℕ}
    (hKb : Kb ≠ 0 → q < q_hi ∧ q_hi < 1 / 2 ∧ 1 ≤ Kb ∧ 1 ≤ ((Kb : ℝ) + 1) * (1 - 2 * q_hi))
    (hK : q < 1 / 2 → K ≤ c3Kmax q) : Kb = 0 ∨ K ≤ Kb := by
  by_cases h0 : Kb = 0
  · exact Or.inl h0
  · obtain ⟨hq, hq_hi, hKb1, hKb2⟩ := hKb h0
    exact Or.inr (le_of_le_c3Kmax hq hq_hi hKb1 hKb2 (hK (by linarith)))

/-- **(C3)* in numerals**: for the ladder `[k₁, k)`, `k₁ ≥ 20`, `σ ≥ 0` with `σe^k ≤ 1/200`,
`0 ≤ q ≤ ½ + 1/20`, the ladder length `K = k - k₁ ≤ K_max(q) = max(1, ⌊1/(1 - 2q)⌋)` when
`q < ½` (every `K` for `q ≥ ½`), and every height `h ∈ halfWindow k`:
`c3Floor q · E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_c3Floor (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hk : k₁ < k) {σ : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ 1 / 200) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1 / 2 + 1 / 20) (hK : q < 1 / 2 → k - k₁ ≤ c3Kmax q) {h : ℝ}
    (hh : h ∈ halfWindow k) :
    c3Floor q * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  obtain ⟨q_lo, q_hi, Kb, hlo, hhi, h0, h1, hKb, hcert, -⟩ :=
    c3Floor_spec hq0 (by linarith)
  exact le_setIntegral_halfLadder_twistQ_of_intervalCert hX ha hk₁ hk hσ hση hlo hhi h0 h1
    (by norm_num) c3Theta_zero c3Theta_last c3Theta_nonneg hcert (c3_kok_of_le_c3Kmax hKb hK) hh

end Main

end RMF
