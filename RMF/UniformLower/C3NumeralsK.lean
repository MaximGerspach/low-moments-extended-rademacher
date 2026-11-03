/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.C3Numerals
import RMF.UniformLower.C3Numerals.OneDispatch

/-!
# (C3)*'s numerals per ladder length

The ladder of length one (`K = k - k₁ = 1`) without the Ville factor
(`RMF.le_setIntegral_halfLadder_twistQ_one`), certified on the grid `q_i = i/200 < ½` and at the
lower end of every cell of `RMF.c3Theta` (`RMF/UniformLower/C3Numerals/One*.lean`,
`RMF.c3OneTab`), and the certified step function `RMF.c3Floor` for the other ladder lengths.

* `RMF.c3FloorK q K`: the ladder of length one's value on `q`'s grid step when `K = 1` and
  `q < ½`, else `RMF.c3Floor q`.
* `RMF.le_setIntegral_halfLadder_twistQ_c3FloorK`: (C3)* with this constant, under
  `RMF.le_setIntegral_halfLadder_twistQ_c3Floor`'s hypotheses.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- **`c₃` per ladder length `K`**: for `K = 1` and `q < ½` the certified value of the ladder of
length one on `q`'s grid step (`RMF.c3OneTab`, no Ville factor), otherwise `RMF.c3Floor q`. -/
noncomputable def c3FloorK (q : ℝ) (K : ℕ) : ℝ :=
  if K = 1 ∧ q < 1 / 2 then c3OneTab ⌊400 * q⌋₊ 0 else c3Floor q

/-- The ladder of length one on `q`'s grid step: for `0 ≤ q < ½` a point `0 ≤ q_lo ≤ q` with every
cell `j` of `RMF.c3Theta` certified, `c3OneTab ⌊400q⌋ j ≤ c3ValOne q_lo (1/200) ϑ_j 10⁻⁴`. -/
lemma c3OneTab_spec {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1 / 2) :
    ∃ q_lo : ℝ, 0 ≤ q_lo ∧ q_lo ≤ q
      ∧ ∀ j < 24, c3OneTab ⌊400 * q⌋₊ j ≤ c3ValOne q_lo (1 / 200) (c3Theta j) (1 / 10 ^ 4) := by
  have hn0 : ((⌊400 * q⌋₊ : ℕ) : ℝ) ≤ 400 * q := Nat.floor_le (by positivity)
  have hn : ⌊400 * q⌋₊ < 200 := by
    have : ((⌊400 * q⌋₊ : ℕ) : ℝ) < 200 := by linarith
    exact_mod_cast this
  obtain ⟨q_lo, ⟨h0, h1⟩, hcells⟩ := c3OneStep_spec _ hn
  refine ⟨q_lo, h0, ?_, hcells⟩
  have : ((⌊400 * q⌋₊ : ℕ) : ℝ) / 400 ≤ q := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **(C3)* per ladder length, in numerals**: under the hypotheses of
`RMF.le_setIntegral_halfLadder_twistQ_c3Floor` (`k₁ ≥ 20`, `k₁ < k`, `σe^k ≤ 1/200`,
`0 ≤ q ≤ ½ + 1/20`, `K = k - k₁ ≤ K_max(q)` when `q < ½`, `h ∈ halfWindow k`):
`c3FloorK q K · E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_c3FloorK (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hk : k₁ < k) {σ : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ 1 / 200) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1 / 2 + 1 / 20) (hK : q < 1 / 2 → k - k₁ ≤ c3Kmax q) {h : ℝ}
    (hh : h ∈ halfWindow k) :
    c3FloorK q (k - k₁)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  unfold c3FloorK
  split_ifs with hone
  · obtain ⟨hK1, hq⟩ := hone
    obtain ⟨q_lo, h0, hlo, hcells⟩ := c3OneTab_spec hq0 hq
    have hc := hcells 0 (by norm_num)
    rw [c3Theta_zero] at hc
    obtain ⟨hh1, hh2⟩ := hh
    exact le_setIntegral_halfLadder_twistQ_one_of_le hX ha hk₁ hK1 hσ hση hlo h0 (by linarith)
      le_rfl hc hh1 (by rwa [add_zero])
  · exact le_setIntegral_halfLadder_twistQ_c3Floor hX ha hk₁ hk hσ hση hq0 hq1 hK hh

end Main

end RMF
