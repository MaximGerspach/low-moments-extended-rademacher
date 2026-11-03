/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Cert.Basic

/-!
# HP1's certificate at the floor `20`: a step in `Λ`

At the floor the bound `Λ` on the exit exponent is larger by `10⁻⁶` on 13 cells than the `Λ` at
which the rows of `RMF/UniformLower/HP1Cert/` certify the lower sums.  They still certify the
larger one, less a Lipschitz step (`RMF.le_sum_hp1Term_of_le_add`):

* `e^δ ≤ 1 + 2δ` for `0 ≤ δ ≤ 1`, so the exit factor `RMF.hp1ExitV2`, `max(1 - e^{…+Λ} - e^{-A_W},
  0)`, loses at most `2δ` when `Λ` grows by `δ` (`e^{…+Λ} ≤ 1` where it is positive), and so does
  its expectation `RMF.exitMean`;
* the rows' weights `RMF.hp1Weight` are nonnegative below the top node, and they telescope:
  `∑_{j<N} w_j = 3/2(Φ(z_N) - Φ(z_0)) + √V(φ(z_N) - φ(z_0)) ≤ 3/2 + 0.3989422805√V`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-- `e^δ ≤ 1 + 2δ` for `0 ≤ δ ≤ 1`. -/
lemma exp_le_one_add_two_mul {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : Real.exp δ ≤ 1 + 2 * δ := by
  have h := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le (x := δ)
    (by rw [abs_of_nonneg h0]; exact h1))).2
  nlinarith

/-- **The exit factor, a step in `Λ`**: for `Λ' ≤ Λ + δ`, `0 ≤ δ ≤ 1`, `RMF.hp1ExitV2` loses at
most `2δ`. -/
lemma hp1ExitV2_sub_le_of_le_add {t L ρ Λ Λ' AW δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hΛ : Λ' ≤ Λ + δ) (y : ℝ) :
    hp1ExitV2 t L ρ Λ AW y - 2 * δ ≤ hp1ExitV2 t L ρ Λ' AW y := by
  unfold hp1ExitV2
  have hE0 : 0 < Real.exp (t * (y + L + ρ) + Λ) := Real.exp_pos _
  have hE : Real.exp (t * (y + L + ρ) + Λ')
      ≤ Real.exp (t * (y + L + ρ) + Λ) + 2 * (δ * Real.exp (t * (y + L + ρ) + Λ)) := by
    calc Real.exp (t * (y + L + ρ) + Λ') ≤ Real.exp (t * (y + L + ρ) + Λ + δ) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (t * (y + L + ρ) + Λ) * Real.exp δ := Real.exp_add _ _
      _ ≤ Real.exp (t * (y + L + ρ) + Λ) * (1 + 2 * δ) :=
          mul_le_mul_of_nonneg_left (exp_le_one_add_two_mul hδ0 hδ1) hE0.le
      _ = _ := by ring
  have hA := Real.exp_pos (-AW)
  have h' := le_max_left (1 - Real.exp (t * (y + L + ρ) + Λ') - Real.exp (-AW)) 0
  have h'' := le_max_right (1 - Real.exp (t * (y + L + ρ) + Λ') - Real.exp (-AW)) 0
  rcases le_or_gt (1 - Real.exp (t * (y + L + ρ) + Λ) - Real.exp (-AW)) 0 with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h.le]
    have hδE : δ * Real.exp (t * (y + L + ρ) + Λ) ≤ δ := mul_le_of_le_one_right hδ0 (by linarith)
    linarith

/-- **The exit expectation, a step in `Λ`**: `RMF.exitMean` loses at most `2δ` when `Λ` grows by
`δ ∈ [0, 1]`. -/
lemma exitMean_sub_le_of_le_add {t L ρ Λ Λ' AW m R δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hΛ : Λ' ≤ Λ + δ) :
    exitMean t L ρ Λ AW m R - 2 * δ ≤ exitMean t L ρ Λ' AW m R := by
  unfold exitMean
  have hi := integrable_hp1ExitV2_comp (gaussianReal 0 R.toNNReal) t L ρ Λ AW m
  have hi' := integrable_hp1ExitV2_comp (gaussianReal 0 R.toNNReal) t L ρ Λ' AW m
  calc (∫ y, hp1ExitV2 t L ρ Λ AW (m + y) ∂(gaussianReal 0 R.toNNReal)) - 2 * δ
      = ∫ y, (hp1ExitV2 t L ρ Λ AW (m + y) - 2 * δ) ∂(gaussianReal 0 R.toNNReal) := by
        rw [integral_sub hi (integrable_const _)]
        simp
    _ ≤ ∫ y, hp1ExitV2 t L ρ Λ' AW (m + y) ∂(gaussianReal 0 R.toNNReal) :=
        integral_mono (hi.sub (integrable_const _)) hi' fun y =>
          hp1ExitV2_sub_le_of_le_add hδ0 hδ1 hΛ (m + y)

/-- The weight of row `j` of HP1's lower sums at `√V = sV`, the second factor of `RMF.hp1Term`:
`3/2(Φ(z_{j+1}) - Φ(z_j)) - √V(φ(z_j) - φ(z_{j+1}))`, `z_j = RMF.sampleNodes j`. -/
noncomputable def hp1Weight (sV : ℝ) (j : ℕ) : ℝ :=
  3 / 2 * (normCDF (sampleNodes (j + 1)) - normCDF (sampleNodes j))
    - sV * (gaussianPDFReal 0 1 (sampleNodes j) - gaussianPDFReal 0 1 (sampleNodes (j + 1)))

lemma hp1Term_eq_mul_hp1Weight (t L Λ R₁ R₂ D P₁ P₂ sV : ℝ) (j : ℕ) :
    hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j
      = max (exitMean t L (1 / 10 ^ 15) Λ 6 (hp1Loc D P₁ P₂ j) R₁
        - t ^ 2 * (1 - Real.exp (-6)) / 2 * (R₂ - R₁)) 0 * hp1Weight sV j := rfl

/-- **The weight is nonnegative below the top node** (`√V ∈ [0, r₂]`, `r₂z_{j+1} ≤ 3/2` or
`z_{j+1} ≤ 0`): it is `E[3/2 - √VZ; z_j < Z ≤ z_{j+1}]`, as in `RMF.hp1Row_zero`. -/
lemma hp1Weight_nonneg {r₂ sV : ℝ} {j : ℕ} (hsV : 0 ≤ sV ∧ sV ≤ r₂)
    (htop : r₂ * sampleNodes (j + 1) ≤ 3 / 2 ∨ sampleNodes (j + 1) ≤ 0) : 0 ≤ hp1Weight sV j := by
  have hle : sampleNodes j ≤ sampleNodes (j + 1) := monotone_sampleNodes (Nat.le_succ j)
  have h := intervalIntegral_affine_gaussianReal hle (3 / 2) sV 1
  rw [one_mul] at h
  unfold hp1Weight
  rw [← h]
  refine intervalIntegral.integral_nonneg hle fun z hz => ?_
  have hz2 : sV * z ≤ sV * sampleNodes (j + 1) := mul_le_mul_of_nonneg_left hz.2 hsV.1
  have htop' : sV * sampleNodes (j + 1) ≤ 3 / 2 := by
    rcases htop with h1 | h1
    · rcases le_total 0 (sampleNodes (j + 1)) with h2 | h2
      · exact le_trans (mul_le_mul_of_nonneg_right hsV.2 h2) h1
      · have := mul_nonpos_of_nonneg_of_nonpos hsV.1 h2
        linarith
    · have := mul_nonpos_of_nonneg_of_nonpos hsV.1 h1
      linarith
  rw [mul_one]
  linarith

/-- **A row, a step in `Λ`**: at `Λ' ≤ Λ + δ`, `0 ≤ δ ≤ 1`, `RMF.hp1Term` is at least its value
at `Λ` less `2δ` times the row's weight, if the weight is nonnegative. -/
lemma hp1Term_sub_le_of_le_add {t L Λ Λ' R₁ R₂ D P₁ P₂ sV δ : ℝ} {j : ℕ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hΛ : Λ' ≤ Λ + δ) (hw : 0 ≤ hp1Weight sV j) :
    hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j - 2 * δ * hp1Weight sV j
      ≤ hp1Term t L Λ' R₁ R₂ D P₁ P₂ sV j := by
  rw [hp1Term_eq_mul_hp1Weight, hp1Term_eq_mul_hp1Weight]
  have he := exitMean_sub_le_of_le_add (t := t) (L := L) (ρ := 1 / 10 ^ 15) (AW := 6)
    (m := hp1Loc D P₁ P₂ j) (R := R₁) hδ0 hδ1 hΛ
  have hmax : max (exitMean t L (1 / 10 ^ 15) Λ 6 (hp1Loc D P₁ P₂ j) R₁
        - t ^ 2 * (1 - Real.exp (-6)) / 2 * (R₂ - R₁)) 0 - 2 * δ
      ≤ max (exitMean t L (1 / 10 ^ 15) Λ' 6 (hp1Loc D P₁ P₂ j) R₁
        - t ^ 2 * (1 - Real.exp (-6)) / 2 * (R₂ - R₁)) 0 := by
    have h₁ := le_max_left (exitMean t L (1 / 10 ^ 15) Λ' 6 (hp1Loc D P₁ P₂ j) R₁
      - t ^ 2 * (1 - Real.exp (-6)) / 2 * (R₂ - R₁)) 0
    have h₂ := le_max_right (exitMean t L (1 / 10 ^ 15) Λ' 6 (hp1Loc D P₁ P₂ j) R₁
      - t ^ 2 * (1 - Real.exp (-6)) / 2 * (R₂ - R₁)) 0
    refine sub_le_iff_le_add.2 (max_le ?_ ?_) <;> linarith
  linarith [mul_le_mul_of_nonneg_right hmax hw]

/-- **The weights telescope**: `∑_{j<N} w_j = 3/2(Φ(z_N) - Φ(z_0)) + √V(φ(z_N) - φ(z_0))`, at
most `3/2 + 0.3989422805√V` for `√V ≥ 0`. -/
lemma sum_hp1Weight_le {sV : ℝ} (hsV : 0 ≤ sV) (N : ℕ) :
    ∑ j ∈ Finset.range N, hp1Weight sV j ≤ 3 / 2 + 0.3989422805 * sV := by
  have h : ∀ j, hp1Weight sV j
      = (3 / 2 * normCDF (sampleNodes (j + 1)) + sV * gaussianPDFReal 0 1 (sampleNodes (j + 1)))
        - (3 / 2 * normCDF (sampleNodes j) + sV * gaussianPDFReal 0 1 (sampleNodes j)) :=
    fun j => by unfold hp1Weight; ring
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_range_sub
    (fun j => 3 / 2 * normCDF (sampleNodes j) + sV * gaussianPDFReal 0 1 (sampleNodes j))]
  have h1 := normCDF_le_one (sampleNodes N)
  have h2 := normCDF_nonneg (sampleNodes 0)
  have h3 : gaussianPDFReal 0 1 (sampleNodes N) ≤ 0.3989422805 := by
    have h0 : Real.exp (-(sampleNodes N ^ 2 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := sq_nonneg (sampleNodes N); linarith)
    have := gaussianPDFReal_zero_one_le h0
    linarith
  have h4 := gaussianPDFReal_nonneg 0 1 (sampleNodes 0)
  have h5 := mul_le_mul_of_nonneg_left h3 hsV
  have h6 := mul_nonneg hsV h4
  linarith

/-- **A lower sum, a step in `Λ`**: if `X ≤ ∑_{j<N} RMF.hp1Term t L Λ …` for every
`√V ∈ [r₁, r₂]`, `r₁ ≥ 0`, with the top node `r₂z_N ≤ 3/2` or `z_N ≤ 0`, then at any
`Λ' ≤ Λ + δ`, `0 ≤ δ ≤ 1`, the lower sum is at least `X - 2δ(3/2 + 0.3989422805r₂)` there. -/
theorem le_sum_hp1Term_of_le_add {t L Λ Λ' R₁ R₂ D P₁ P₂ r₁ r₂ δ X : ℝ} {N : ℕ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hΛ : Λ' ≤ Λ + δ) (hr₁ : 0 ≤ r₁)
    (hN : r₂ * sampleNodes N ≤ 3 / 2 ∨ sampleNodes N ≤ 0)
    (hsum : ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ →
      X ≤ ∑ j ∈ Finset.range N, hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j) :
    ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → X - 2 * δ * (3 / 2 + 0.3989422805 * r₂)
      ≤ ∑ j ∈ Finset.range N, hp1Term t L Λ' R₁ R₂ D P₁ P₂ sV j := by
  intro sV hsV
  have hsV0 : 0 ≤ sV := le_trans hr₁ hsV.1
  have hr₂ : 0 ≤ r₂ := le_trans hsV0 hsV.2
  have hrow : ∀ j ∈ Finset.range N, hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j - 2 * δ * hp1Weight sV j
      ≤ hp1Term t L Λ' R₁ R₂ D P₁ P₂ sV j := by
    intro j hj
    have hz := monotone_sampleNodes (Finset.mem_range.1 hj : j + 1 ≤ N)
    refine hp1Term_sub_le_of_le_add hδ0 hδ1 hΛ (hp1Weight_nonneg ⟨hsV0, hsV.2⟩ ?_)
    rcases le_total (sampleNodes (j + 1)) 0 with h0 | h0
    · exact Or.inr h0
    · rcases hN with h | h
      · exact Or.inl (le_trans (mul_le_mul_of_nonneg_left hz hr₂) h)
      · exact Or.inr (le_trans hz h)
  have h1 := Finset.sum_le_sum hrow
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  have h2 := sum_hp1Weight_le hsV0 N
  have h3 : 0.3989422805 * sV ≤ 0.3989422805 * r₂ :=
    mul_le_mul_of_nonneg_left hsV.2 (by norm_num)
  have h4 : 2 * δ * ∑ j ∈ Finset.range N, hp1Weight sV j
      ≤ 2 * δ * (3 / 2 + 0.3989422805 * r₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith [hsum sV hsV]

end RMF
