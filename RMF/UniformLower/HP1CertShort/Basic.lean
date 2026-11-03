/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1CertFloor.Basic
import RMF.UniformLower.GaussianHP1Short

/-!
# HP1's certificate on short tubes: the interface

The certificate of `RMF.hp1LowerBoundShort` is that of `RMF/UniformLower/HP1Cert/Basic.lean` with
each row damped by the ballot's exponent at the rung `n₀`:

* **The main term by a factored lower sum** (`RMF.sum_le_startMainShort`): on `(z_i, z_{i+1}]`
  the weight `(a - √Vz)e^{-(a-√Vz)²/(2N)}` of `RMF.startMainShort` is at least `(a - √Vz)e_i` once
  `a - √Vz_i ≤ c_i` and `0 ≤ e_i ≤ e^{-c_i²/(2N)}`.
* **The row factor** `RMF.hp1RowFac n₀ v₋ r₁ r₂ j = max(T₅(c_j²/(2(n₀-2)v₋)), 0)`,
  `c_j = max(3/2 - r₁z_j, 3/2 - r₂z_j)`, `T₅` Taylor's polynomial of `e^{-s}` of degree `5`
  (below it, `RMF.expNegTaylor_odd_le_exp_neg`): in `[0, 1]`, and a polynomial for `norm_num`.
* **One cell** (`RMF.hp1LowerBoundShort_of_lowerSum`): `RMF.hp1LowerBoundV2_of_lowerSum` with the
  factored lower sums, the ballot factor `2/√(2πv₊) ≥ k`, the slope loss's rate
  `√(2n₀/(π(n₀-10)v₋))P_R ≤ s_p` on `3/2 + √V(2π)^{-1/2} ≤ 3/2 + 0.3989422805r₂`, and
  `RMF.hp1Loss` at the rung.
* **The rows, factored, a step in `Λ`** (`RMF.le_sum_hp1Term_mul_hp1RowFac`): rows
  `τ_j ≤ RMF.hp1Term … Λ …` give a piece's lower sum at the rung from one numeral,
  `X ≤ ∑_j τ_j·RMF.hp1RowFac n₀ v₋ r₁ r₂ j - 2δ(3/2 + 0.3989422805r₂)` at `Λ' ≤ Λ + δ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Real

namespace RMF

/-! ### The main term by a factored lower sum -/

/-- On `[a - C, a]`, below a bound `c ≥ a - u`: `(a - u)e ≤ RMF.startWeightShort N a C u` for
`e ≤ e^{-c²/(2N)}`, `N ≥ 0`. -/
lemma mul_le_startWeightShort {Nv a C u c e : ℝ} (hNv : 0 ≤ Nv) (h1 : a - C ≤ u) (h2 : u ≤ a)
    (hc : a - u ≤ c) (he : e ≤ Real.exp (-(c ^ 2 / (2 * Nv)))) :
    (a - u) * e ≤ startWeightShort Nv a C u := by
  rw [startWeightShort_eq h1 h2]
  have h0 : 0 ≤ a - u := by linarith
  have hsq : (a - u) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ h0 hc 2
  have hexp : Real.exp (-(c ^ 2 / (2 * Nv))) ≤ Real.exp (-((a - u) ^ 2 / (2 * Nv))) :=
    Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right hsq (by linarith)))
  exact mul_le_mul_of_nonneg_left (he.trans hexp) h0

/-- **A factored lower sum for the start's main term on short tubes** `RMF.startMainShort`:
`RMF.sum_le_startMainV2` with row `i` damped by `e_i`, for `a - √Vz_i ≤ c_i` and
`0 ≤ e_i ≤ e^{-c_i²/(2N)}`: on `(z_i, z_{i+1}]`, where `0 ≤ a - √Vz ≤ c_i`, the weight
`(a - √Vz)e^{-(a-√Vz)²/(2N)}` is at least `(a - √Vz)e_i` (`RMF.mul_le_startWeightShort`). -/
theorem sum_le_startMainShort {Nv a C V S κ D t L ρ Λ AW R₁ R₂ : ℝ} (hNv : 0 ≤ Nv) (hC : 0 ≤ C)
    (hV : 0 < V) (ht : 0 ≤ t) (hAW : 0 ≤ AW) (hR₁ : 0 ≤ R₁) (hR₁R : R₁ ≤ pairResidVar V S κ)
    (hRR₂ : pairResidVar V S κ ≤ R₂) {zs : ℕ → ℝ} (hzs : Monotone zs) {N : ℕ}
    (hlo : a - C ≤ √V * zs 0) (hhi : √V * zs N ≤ a) {mbar c e : ℕ → ℝ}
    (hm : ∀ i < N, ∀ z ∈ Set.Icc (zs i) (zs (i + 1)), D + pairSlope V κ * (√V * z) ≤ mbar i)
    (hc : ∀ i < N, a - √V * zs i ≤ c i)
    (he : ∀ i < N, 0 ≤ e i ∧ e i ≤ Real.exp (-(c i ^ 2 / (2 * Nv)))) :
    ∑ i ∈ Finset.range N,
        max (exitMean t L ρ Λ AW (mbar i) R₁ - t ^ 2 * (1 - Real.exp (-AW)) / 2 * (R₂ - R₁)) 0
          * (a * (normCDF (zs (i + 1)) - normCDF (zs i))
            - √V * (gaussianPDFReal 0 1 (zs i) - gaussianPDFReal 0 1 (zs (i + 1)))) * e i
      ≤ startMainShort Nv a C V S κ D t L ρ Λ AW := by
  set R := pairResidVar V S κ with hRdef
  set K := t ^ 2 * (1 - Real.exp (-AW)) / 2 with hK
  have hK0 : 0 ≤ K := by
    have := Real.exp_le_one_iff.2 (by linarith : -AW ≤ 0)
    have : 0 ≤ 1 - Real.exp (-AW) := by linarith
    positivity
  set Ibar : ℕ → ℝ := fun i => max (exitMean t L ρ Λ AW (mbar i) R₁ - K * (R₂ - R₁)) 0
    with hIbar
  set μ := gaussianReal 0 1 with hμ
  -- the integrand in the standardised height
  set G : ℝ → ℝ := fun z => startWeightShort Nv a C (√V * z)
    * exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R with hG
  have hEm : Measurable fun m => exitMean t L ρ Λ AW m R :=
    (exitMean_antitone ht L ρ Λ AW R).measurable
  have hGm : Measurable G :=
    ((measurable_startWeightShort Nv a C).comp (measurable_const_mul _)).mul
      (hEm.comp (measurable_const.add (measurable_const.mul (measurable_const_mul _))))
  have hG0 : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg (startWeightShort_nonneg hC _) (exitMean_nonneg _ _ _ _ _ _ _)
  have hGC : ∀ z, G z ≤ C := fun z =>
    (mul_le_of_le_one_right (startWeightShort_nonneg hC _) (exitMean_le_one _ _ _ _ _ _ _)).trans
      ((startWeightShort_le hC hNv _).trans (startWeight_le _))
  have hGi : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable C (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 z)]
      exact hGC z)
  -- the main term as an integral over the standardised height
  have hmain : startMainShort Nv a C V S κ D t L ρ Λ AW = ∫ z, G z ∂μ := by
    have hsq : √((V.toNNReal : ℝ≥0) : ℝ) = √V := by rw [Real.coe_toNNReal V hV.le]
    have hFm : Measurable fun u => startWeightShort Nv a C u
        * exitMean t L ρ Λ AW (D + pairSlope V κ * u) R :=
      (measurable_startWeightShort Nv a C).mul
        (hEm.comp (measurable_const.add (measurable_const_mul _)))
    have e : startMainShort Nv a C V S κ D t L ρ Λ AW = ∫ u, startWeightShort Nv a C u
        * exitMean t L ρ Λ AW (D + pairSlope V κ * u) R ∂(gaussianReal 0 V.toNNReal) := rfl
    rw [e, ← gaussianReal_map_sqrt_mul V.toNNReal, integral_map (by fun_prop)
      hFm.aestronglyMeasurable, hsq]
  -- each cell
  have hzN : ∀ i, i ≤ N → zs 0 ≤ zs i ∧ zs i ≤ zs N := fun i hi =>
    ⟨hzs (Nat.zero_le i), hzs hi⟩
  have hcell : ∀ i < N, Ibar i * (a * (normCDF (zs (i + 1)) - normCDF (zs i))
      - √V * (gaussianPDFReal 0 1 (zs i) - gaussianPDFReal 0 1 (zs (i + 1)))) * e i
      ≤ ∫ z in zs i..zs (i + 1), G z ∂μ := by
    intro i hi
    have hle : zs i ≤ zs (i + 1) := hzs (Nat.le_succ i)
    rw [mul_right_comm, ← intervalIntegral_affine_gaussianReal hle a (√V) (Ibar i * e i)]
    refine intervalIntegral.integral_mono_on hle
      ((by fun_prop : Continuous fun z => (a - √V * z) * (Ibar i * e i)).intervalIntegrable _ _)
      (hGi.intervalIntegrable) fun z hz => ?_
    have hz0 : zs 0 ≤ z := le_trans (hzN i hi.le).1 hz.1
    have hzN' : z ≤ zs N := le_trans hz.2 (hzN (i + 1) hi).2
    have hw1 : a - C ≤ √V * z := le_trans hlo (mul_le_mul_of_nonneg_left hz0 (Real.sqrt_nonneg _))
    have hw2 : √V * z ≤ a := le_trans (mul_le_mul_of_nonneg_left hzN' (Real.sqrt_nonneg _)) hhi
    have hcz : a - √V * z ≤ c i := by
      have := mul_le_mul_of_nonneg_left hz.1 (Real.sqrt_nonneg V)
      linarith [hc i hi]
    have hsw := mul_le_startWeightShort hNv hw1 hw2 hcz (he i hi).2
    have hE1 : exitMean t L ρ Λ AW (mbar i) R
        ≤ exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R :=
      exitMean_antitone ht L ρ Λ AW R (hm i hi z hz)
    have hE2 := exitMean_sub_le hAW t L ρ Λ (mbar i) hR₁ hR₁R
    rw [← hK] at hE2
    have hE3 : K * (R - R₁) ≤ K * (R₂ - R₁) := mul_le_mul_of_nonneg_left (by linarith) hK0
    have hIb : Ibar i ≤ exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R :=
      max_le (by linarith) (exitMean_nonneg _ _ _ _ _ _ _)
    calc (a - √V * z) * (Ibar i * e i) = (a - √V * z) * e i * Ibar i := by ring
      _ ≤ startWeightShort Nv a C (√V * z)
          * exitMean t L ρ Λ AW (D + pairSlope V κ * (√V * z)) R :=
        mul_le_mul hsw hIb (le_max_right _ _) (startWeightShort_nonneg hC _)
  -- sum the cells
  have hsum : ∑ i ∈ Finset.range N, ∫ z in zs i..zs (i + 1), G z ∂μ
      = ∫ z in zs 0..zs N, G z ∂μ :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hGi.intervalIntegrable
  have hwhole : ∫ z in zs 0..zs N, G z ∂μ ≤ ∫ z, G z ∂μ := by
    rw [intervalIntegral.integral_of_le (hzN N le_rfl).1]
    exact setIntegral_le_integral hGi (Filter.Eventually.of_forall hG0)
  rw [hmain]
  calc _ ≤ ∑ i ∈ Finset.range N, ∫ z in zs i..zs (i + 1), G z ∂μ :=
        Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.1 hi)
    _ = ∫ z in zs 0..zs N, G z ∂μ := hsum
    _ ≤ ∫ z, G z ∂μ := hwhole

/-! ### The row factor -/

/-- **The factor of row `j` at rung `n₀`**: `max(T₅(c_j²/(2(n₀-2)v₋)), 0)`,
`c_j = max(3/2 - r₁z_j, 3/2 - r₂z_j)` (`z_j = RMF.sampleNodes j`, `√V ∈ [r₁, r₂]`), `T₅` Taylor's
polynomial of `e^{-s}` of degree `5`, below `e^{-s}` (`RMF.hp1RowFac_le_exp`). -/
noncomputable def hp1RowFac (n₀ : ℕ) (vmin r₁ r₂ : ℝ) (j : ℕ) : ℝ :=
  max (expNegTaylor 5 (max (3 / 2 - r₁ * sampleNodes j) (3 / 2 - r₂ * sampleNodes j) ^ 2
    / (2 * (((n₀ : ℝ) - 2) * vmin)))) 0

lemma hp1RowFac_nonneg (n₀ : ℕ) (vmin r₁ r₂ : ℝ) (j : ℕ) : 0 ≤ hp1RowFac n₀ vmin r₁ r₂ j :=
  le_max_right _ _

/-- The row factor is below the exponential it stands for: `T₅(s) ≤ e^{-s}` for `s ≥ 0`
(`RMF.expNegTaylor_odd_le_exp_neg`). -/
lemma hp1RowFac_le_exp {n₀ : ℕ} {vmin : ℝ} (hn₀ : 2 ≤ n₀) (hvmin : 0 ≤ vmin) (r₁ r₂ : ℝ)
    (j : ℕ) :
    hp1RowFac n₀ vmin r₁ r₂ j ≤ Real.exp (-(max (3 / 2 - r₁ * sampleNodes j)
      (3 / 2 - r₂ * sampleNodes j) ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)))) := by
  have hn : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hs : 0 ≤ max (3 / 2 - r₁ * sampleNodes j) (3 / 2 - r₂ * sampleNodes j) ^ 2
      / (2 * (((n₀ : ℝ) - 2) * vmin)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg zero_le_two (mul_nonneg (by linarith) hvmin))
  exact max_le (expNegTaylor_odd_le_exp_neg 2 hs) (Real.exp_pos _).le

lemma hp1RowFac_le_one {n₀ : ℕ} {vmin : ℝ} (hn₀ : 2 ≤ n₀) (hvmin : 0 ≤ vmin) (r₁ r₂ : ℝ)
    (j : ℕ) : hp1RowFac n₀ vmin r₁ r₂ j ≤ 1 := by
  have hn : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hs : 0 ≤ max (3 / 2 - r₁ * sampleNodes j) (3 / 2 - r₂ * sampleNodes j) ^ 2
      / (2 * (((n₀ : ℝ) - 2) * vmin)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg zero_le_two (mul_nonneg (by linarith) hvmin))
  exact (hp1RowFac_le_exp hn₀ hvmin r₁ r₂ j).trans (Real.exp_le_one_iff.2 (by linarith))

/-- `a - √V·z ≤ max(a - r₁z, a - r₂z)` for `√V ∈ [r₁, r₂]`: the bound is affine in `√V`. -/
lemma sub_mul_le_max_of_mem {a sV r₁ r₂ z : ℝ} (hsV : r₁ ≤ sV ∧ sV ≤ r₂) :
    a - sV * z ≤ max (a - r₁ * z) (a - r₂ * z) := by
  rcases le_total 0 z with hz | hz
  · exact le_max_of_le_left (by linarith [mul_le_mul_of_nonneg_right hsV.1 hz])
  · exact le_max_of_le_right (by linarith [mul_le_mul_of_nonpos_right hsV.2 hz])

/-! ### The other terms -/

/-- **HP1's short-tube bound from a lower bound of its main term**, the other terms at their
worst case over the data ranges: `RMF.hp1LowerBoundV2_ge` for `RMF.hp1LowerBoundShort`, the slope
loss at `√V' ≥ √(v₀ + v₁)`, `RMF.hp1Loss` at `V' ≥ v₀ + v₁`. -/
theorem hp1LowerBoundShort_ge {n₀ m₀ : ℕ}
    {vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW Klate σR2 : ℝ}
    {X v₀' v₁' V' σ' S' d₀' D' : ℝ}
    (hX : X ≤ startMainShort (((n₀ : ℝ) - 2) * vmin) a (a + A + 2 * B) (v₀ + v₁)
      (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁)) (β₀ * v₀ + β₁ * v₁) (d₀ + d₁) t L ρ Λ AW)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 2 * vmax ≤ B) (hvmax : 0 ≤ vmax)
    (hv₀ : 0 < v₀) (hv₀' : v₀ ≤ v₀') (hv₁ : 0 ≤ v₁) (hv₁' : v₁ ≤ v₁') (hV' : v₀ + v₁ ≤ V')
    (hσ : 0 < β₀ ^ 2 * v₀ + s₀) (hσ' : β₀ ^ 2 * v₀ + s₀ ≤ σ')
    (hS : 0 < β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁))
    (hS' : β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁) ≤ S')
    (hd₀ : |d₀| ≤ d₀') (hM : d₀' ≤ M₁) (hD : D' ≤ d₀ + d₁) (hK : 0 ≤ K₂ + D') :
    2 / √(2 * π * vmax)
        * (X - (1 - normCDF (a / √v₀')) * (√v₁' * (√(2 * π))⁻¹)
          - (a + A + 2 * B) * (Real.exp (-((A + B) ^ 2 / (2 * v₀')))
            + Real.exp (-((A + 2 * B) ^ 2 / (2 * V')))
            + 2 * Real.exp (-((M₁ - d₀') ^ 2 / (2 * σ')))
            + Real.exp (-((K₂ + D') ^ 2 / (2 * S')))))
      - √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
        * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * (a + √V' * (√(2 * π))⁻¹)
      - hp1Loss n₀ m₀ vmin vmax V' a A B L Klate σR2
      ≤ hp1LowerBoundShort n₀ m₀ vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW Klate
        σR2 := by
  have hB0 : 0 ≤ B := by linarith
  have hC : 0 ≤ a + A + 2 * B := by linarith
  have hceil := ceilLoss_le hv₀ hv₀' hv₁ hv₁' ha hC
  have htails := startTails_le (s₁ := s₁) (β₁ := β₁) (A := A) (B := B) (M₁ := M₁) (K₂ := K₂)
    hv₀ hv₀' (by linarith) hV' hσ hσ' hS hS' (by linarith) (by linarith) hd₀ hM hD hK
  have hstart : X - (1 - normCDF (a / √v₀')) * (√v₁' * (√(2 * π))⁻¹)
      - (a + A + 2 * B) * (Real.exp (-((A + B) ^ 2 / (2 * v₀')))
        + Real.exp (-((A + 2 * B) ^ 2 / (2 * V')))
        + 2 * Real.exp (-((M₁ - d₀') ^ 2 / (2 * σ')))
        + Real.exp (-((K₂ + D') ^ 2 / (2 * S'))))
      ≤ hp1StartShort n₀ vmin v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW := by
    unfold hp1StartShort
    have := mul_le_mul_of_nonneg_left htails hC
    linarith
  have hk0 : 0 ≤ 2 / √(2 * π * vmax) := div_nonneg zero_le_two (Real.sqrt_nonneg _)
  have hloss := hp1Loss_le_of_le (n₀ := n₀) (m₀ := m₀) (vmin := vmin) (L := L)
    (Klate := Klate) (σR2 := σR2) hC hB hV'
  have hslope : √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
        * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * (a + √(v₀ + v₁) * (√(2 * π))⁻¹)
      ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
        * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * (a + √V' * (√(2 * π))⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    have := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hV')
      (inv_nonneg.2 (Real.sqrt_nonneg (2 * π)))
    linarith
  unfold hp1LowerBoundShort
  have := mul_le_mul_of_nonneg_left hstart hk0
  linarith

/-- **The ballot factor from below**: `k ≤ 2/u₁ ≤ 2/√(2πv₊)` for `2·3.141593·v₊ ≤ u₁²`. -/
lemma le_two_div_sqrt_two_pi_mul {vmax u₁ k : ℝ} (hvmax : 0 < vmax) (hu₁0 : 0 ≤ u₁)
    (hu₁ : 2 * 3.141593 * vmax ≤ u₁ ^ 2) (hk : k ≤ 2 / u₁) : k ≤ 2 / √(2 * π * vmax) := by
  have hp := Real.pi_lt_d6
  have hs : √(2 * π * vmax) ≤ u₁ := by
    rw [Real.sqrt_le_left hu₁0]
    nlinarith
  exact hk.trans (div_le_div_of_nonneg_left zero_le_two (Real.sqrt_pos.2 (by positivity)) hs)

/-- **The slope loss's rate, its square root from above**: `√(2n₀/(π(n₀-2-m₀)v₋)) ≤ u₂` for
`2n₀ ≤ u₂²·3.141592(n₀ - 2 - m₀)v₋`, `m₀ + 3 ≤ n₀`. -/
lemma sqrt_slopeLossShort_le {n₀ m₀ : ℕ} {vmin u₂ : ℝ} (hn₀ : m₀ + 3 ≤ n₀) (hvmin : 0 < vmin)
    (hu₂0 : 0 ≤ u₂) (hu₂ : 2 * (n₀ : ℝ) ≤ u₂ ^ 2 * (3.141592 * (((n₀ : ℝ) - 2 - m₀) * vmin))) :
    √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) ≤ u₂ := by
  have hp := Real.pi_gt_d6
  have hn : (m₀ : ℝ) + 3 ≤ n₀ := by exact_mod_cast hn₀
  have hN : 0 < ((n₀ : ℝ) - 2 - m₀) * vmin := mul_pos (by linarith) hvmin
  rw [Real.sqrt_le_left hu₂0, div_le_iff₀ (mul_pos Real.pi_pos hN)]
  have h1 : 0 ≤ u₂ ^ 2 * (((n₀ : ℝ) - 2 - m₀) * vmin) := mul_nonneg (sq_nonneg _) hN.le
  nlinarith

/-- **The slope loss's rate from above**: `√(2n₀/(π(n₀-2-m₀)v₋))P_R ≤ s_p` from
`RMF.sqrt_slopeLossShort_le`, `P_R ≤ e` and `u₂e ≤ s_p`. -/
lemma hp1SlopeLossShort_le {n₀ m₀ : ℕ} {vmin L Klate σR2 u₂ e sp : ℝ} (hn₀ : m₀ + 3 ≤ n₀)
    (hvmin : 0 < vmin) (hu₂0 : 0 ≤ u₂)
    (hu₂ : 2 * (n₀ : ℝ) ≤ u₂ ^ 2 * (3.141592 * (((n₀ : ℝ) - 2 - m₀) * vmin)))
    (he : Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ e) (hsp : u₂ * e ≤ sp) :
    √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
      ≤ sp :=
  le_trans (mul_le_mul (sqrt_slopeLossShort_le hn₀ hvmin hu₂0 hu₂) he (Real.exp_pos _).le hu₂0)
    hsp

/-- **`RMF.hp1Loss` from above at a rung `n₀`** (`m₀ = 8`, `A = 5/2`, `B = 3`):
`RMF.hp1Loss_le_of` with `√(n₀/(n₀-2)) ≤ w₁` from `n₀ ≤ w₁²(n₀ - 2)`, and
`2n₀ ≤ w₇²·3.141592(n₀ - 10)v₋`. -/
lemma hp1Loss_le_of_short {n₀ : ℕ} {vmin vmax V L Klate σR2 w₁ w₃ w₄ l w₆ w₇ e w₈ lo : ℝ}
    (hn₀ : 11 ≤ n₀) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) (hB : 2 * vmax < 3) (h₁0 : 0 ≤ w₁)
    (h₁ : (n₀ : ℝ) ≤ w₁ ^ 2 * ((n₀ : ℝ) - 2)) (h₃0 : 0 ≤ w₃) (h₃ : 3.141593 * vmax / 2 ≤ w₃ ^ 2)
    (h₄0 : 0 ≤ w₄) (h₄ : 4 ≤ w₄ ^ 2 * (3.141592 * vmin))
    (h₄' : 2 ≤ w₄ ^ 2 * (2.7182818283 * (3 - 2 * vmax))) (hl : 0 < l)
    (h₅ : l + 1 ≤ Real.exp ((3 - 2 * vmax) / 2)) (h₆ : Real.exp (V / 2) ≤ w₆) (h₇0 : 0 ≤ w₇)
    (h₇ : 2 * (n₀ : ℝ) ≤ w₇ ^ 2 * (3.141592 * (((n₀ : ℝ) - 2 - 8) * vmin)))
    (he : Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ e) (h₈0 : 0 ≤ w₈)
    (h₈ : e * (8 * vmax) ≤ w₈ ^ 2)
    (hlo : w₁ * (0.00020347 * (3 / 2 + 5 / 2 + 2 * 3 + w₃ + 2) * w₄ / l) * w₆
      + w₇ * (w₃ * e + w₈) ≤ lo) :
    hp1Loss n₀ 8 vmin vmax V (3 / 2) (5 / 2) 3 L Klate σR2 ≤ lo := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have he1 := Real.exp_one_gt_d9
  have hn : (11 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  refine le_trans (hp1Loss_le (w₁ := w₁) (w₂ := 0.00020347) (by norm_num) ?_
    exp_neg_eight_half_le ?_ ?_ ?_ hl ?_ h₆ ?_ he ?_) hlo
  · rw [Real.sqrt_le_left h₁0, div_le_iff₀ (by linarith)]
    exact h₁
  · rw [Real.sqrt_le_left h₃0]
    nlinarith
  · rw [Real.sqrt_le_left h₄0, div_le_iff₀ (by positivity)]
    nlinarith
  · have hB' : 0 < (3 : ℝ) - 2 * vmax := by linarith
    rw [Real.sqrt_le_left h₄0, div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ w₄ ^ 2 * (3 - 2 * vmax) := by positivity
    nlinarith
  · linarith
  · refine sqrt_slopeLossShort_le (m₀ := 8) (by omega) hvmin h₇0 ?_
    push_cast
    exact h₇
  · rw [Real.sqrt_le_left h₈0]
    push_cast
    have := mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 8 * vmax)
    linarith

/-! ### One cell -/

/-- One piece `[b, b']` of the residual variance's range with its factored lower sum:
`RMF.hp1Piece` for `RMF.hp1Term · RMF.hp1RowFac`. -/
lemma hp1PieceShort {n₀ : ℕ} {vmin t L Λ Dh P₁ P₂ r₁ r₂ X Xp s R₂ b b' R : ℝ} {N : ℕ}
    (hs : 0 < s) (hsb : s ^ 2 ≤ b) (hbR : b ≤ R) (hRb : R ≤ b') (hbR₂ : b' ≤ R₂) (hX : X ≤ Xp)
    (hsum : ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → Xp ≤ ∑ j ∈ Finset.range N,
      hp1Term t L Λ (s ^ 2) R₂ Dh P₁ P₂ sV j * hp1RowFac n₀ vmin r₁ r₂ j) :
    ∃ s R₂ : ℝ, 0 < s ∧ s ^ 2 ≤ R ∧ R ≤ R₂ ∧ ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → X ≤ ∑ j ∈ Finset.range N,
      hp1Term t L Λ (s ^ 2) R₂ Dh P₁ P₂ sV j * hp1RowFac n₀ vmin r₁ r₂ j :=
  ⟨s, R₂, hs, le_trans hsb hbR, le_trans hRb hbR₂, fun sV hsV => le_trans hX (hsum sV hsV)⟩

/-- **HP1's short-tube bound on one cell, from its factored lower sums.**
`RMF.hp1LowerBoundV2_of_lowerSum` for `RMF.hp1LowerBoundShort n₀ 8` at the event's parameters
`a = 3/2, A = 5/2, B = 3, M₁ = 7, K₂ = 10`, `ρ = 10⁻¹⁵`, `A_W = 6`: every piece's lower sum has
row `j` damped by `RMF.hp1RowFac n₀ v₋ r₁ r₂ j` (`RMF.sum_le_startMainShort`); given the ballot
factor `2/√(2πv₊) ≥ k ≥ 0`, the slope loss's rate `√(2n₀/(π(n₀-10)v₋))P_R ≤ s_p`, the loss at the
rung `≤ lo` and the ceiling loss `≤ ce`,
`p ≤ k(X - ce - 10·5·4.14·10⁻⁸) - s_p(3/2 + 0.3989422805r₂) - lo` (`RMF.hp1LowerBoundShort_ge`). -/
theorem hp1LowerBoundShort_of_lowerSum {n₀ : ℕ} {v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ}
    {v0l v0h v1l v1h kl kh d0 Dl Dh vmin vmax L t Λ Klate σR2 : ℝ}
    {r₁ r₂ P₁ P₂ K2 k2 Rlo Rhi X ce k sp lo p : ℝ} {N : ℕ} (hn₀ : 2 ≤ n₀) (hvmin : 0 ≤ vmin)
    (hs : HP1StartRanges v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ v0l v0h v1l v1h kl kh 1.99997 2.00003 0.99998
      1.00002 d0 Dl Dh)
    (hX : ∀ R, Rlo ≤ R → R ≤ Rhi → ∃ s R₂ : ℝ, 0 < s ∧ s ^ 2 ≤ R ∧ R ≤ R₂ ∧
      ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → X ≤ ∑ j ∈ Finset.range N,
        hp1Term t L Λ (s ^ 2) R₂ Dh P₁ P₂ sV j * hp1RowFac n₀ vmin r₁ r₂ j)
    (hv0l : 0 < v0l) (hv1l : 0 ≤ v1l) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₁V : r₁ ^ 2 ≤ v0l + v1l)
    (hr₂V : v0h + v1h ≤ r₂ ^ 2)
    (hP : P₁ ≤ kl / r₁ ∧ P₁ ≤ kl / r₂ ∧ kh / r₁ ≤ P₂ ∧ kh / r₂ ≤ P₂)
    (hK2 : kl ^ 2 ≤ K2 ∧ kh ^ 2 ≤ K2)
    (hk2 : 0 ≤ k2 ∧ (k2 = 0 ∨ (0 ≤ kl ∧ k2 ≤ kl ^ 2) ∨ (kh ≤ 0 ∧ k2 ≤ kh ^ 2)))
    (hRlo : Rlo ≤ 1.99997 - K2 / (v0l + v1l)) (hRhi : 2.00003 - k2 / (v0h + v1h) ≤ Rhi)
    (hN : r₂ * sampleNodes N ≤ 3 / 2 ∨ sampleNodes N ≤ 0)
    (hN0 : 3 / 2 - (3 / 2 + 5 / 2 + 2 * 3) ≤ r₂ * sampleNodes 0) (ht : 0 ≤ t)
    (hvmax : 2 * vmax ≤ 3) (hvmax0 : 0 ≤ vmax) (hd0 : d0 ≤ 7) (hDl : 0 ≤ 10 + Dl)
    (htails : 17 ≤ (5 / 2 + 3) ^ 2 / (2 * v0h) ∧ 17 ≤ (5 / 2 + 2 * 3) ^ 2 / (2 * (v0h + v1h))
      ∧ 17 ≤ (7 - d0) ^ 2 / (2 * 1.00002) ∧ 17 ≤ (10 + Dl) ^ 2 / (2 * 2.00003))
    (hk : k ≤ 2 / √(2 * π * vmax)) (hk0 : 0 ≤ k)
    (hsp : √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - (8 : ℕ)) * vmin)))
      * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ sp)
    (hlo : hp1Loss n₀ 8 vmin vmax (v0h + v1h) (3 / 2) (5 / 2) 3 L Klate σR2 ≤ lo)
    (hce : (1 - normCDF (3 / 2 / √v0h)) * (√v1h * (√(2 * π))⁻¹) ≤ ce)
    (hY : 0 ≤ X - ce - (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414))
    (hp : p ≤ k * (X - ce - (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414))
      - sp * (3 / 2 + 0.3989422805 * r₂) - lo) :
    p ≤ hp1LowerBoundShort n₀ 8 vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ (3 / 2) (5 / 2) 3 7 10
      (1 / 10 ^ 15) L t Λ 6 Klate σR2 := by
  obtain ⟨⟨hv₀l, hv₀h⟩, ⟨hv₁l, hv₁h⟩, hκ, hS, ⟨hσl, hσh⟩, hd₀, ⟨hDl', hDh'⟩⟩ := hs
  have hV0 : 0 < v₀ + v₁ := by linarith
  have hsV0 : 0 < √(v₀ + v₁) := Real.sqrt_pos.2 hV0
  have hsV1 : r₁ ≤ √(v₀ + v₁) := (Real.le_sqrt' hr₁).2 (by linarith)
  have hsV2 : √(v₀ + v₁) ≤ r₂ := (Real.sqrt_le_left hr₂.le).2 (by linarith)
  have hVsq : √(v₀ + v₁) * √(v₀ + v₁) = v₀ + v₁ := Real.mul_self_sqrt hV0.le
  -- the slope times `√V` is `κ/√V`
  have hb : pairSlope (v₀ + v₁) (β₀ * v₀ + β₁ * v₁) * √(v₀ + v₁) ∈ Set.Icc P₁ P₂ := by
    have e : pairSlope (v₀ + v₁) (β₀ * v₀ + β₁ * v₁) * √(v₀ + v₁)
        = (β₀ * v₀ + β₁ * v₁) / √(v₀ + v₁) := by
      rw [pairSlope, div_mul_eq_mul_div, div_eq_div_iff hV0.ne' hsV0.ne', mul_assoc, hVsq]
    rw [e]
    exact div_sqrt_mem_of_ranges hr₁ ⟨hsV1, hsV2⟩ hκ hP
  -- the residual variance
  have hR := pairResidVar_mem_of_ranges (by linarith) ⟨(by linarith : v0l + v1l ≤ v₀ + v₁),
    (by linarith : v₀ + v₁ ≤ v0h + v1h)⟩ hS hκ hK2 hk2
  obtain ⟨s, R₂, hs0, hsR, hRR₂, hsum⟩ := hX _ (le_trans hRlo hR.1) (le_trans hR.2 hRhi)
  -- the main term, by the factored lower sum
  have hlo' : 3 / 2 - (3 / 2 + 5 / 2 + 2 * 3) ≤ √(v₀ + v₁) * sampleNodes 0 := by
    have hz : sampleNodes 0 ≤ 0 := by norm_num [sampleNodes]
    exact le_trans hN0 (mul_le_mul_of_nonpos_right hsV2 hz)
  have hhi' : √(v₀ + v₁) * sampleNodes N ≤ 3 / 2 := by
    rcases le_total 0 (sampleNodes N) with hz | hz
    · rcases hN with h | h
      · exact le_trans (mul_le_mul_of_nonneg_right hsV2 hz) h
      · have : sampleNodes N = 0 := le_antisymm h hz
        rw [this, mul_zero]
        norm_num
    · have := mul_nonpos_of_nonneg_of_nonpos hsV0.le hz
      linarith
  have hn : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hmain := sum_le_startMainShort (Nv := ((n₀ : ℝ) - 2) * vmin) (a := 3 / 2)
    (C := 3 / 2 + 5 / 2 + 2 * 3) (S := β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁))
    (κ := β₀ * v₀ + β₁ * v₁) (D := d₀ + d₁) (t := t) (L := L) (ρ := 1 / 10 ^ 15) (Λ := Λ)
    (AW := 6) (R₁ := s ^ 2) (R₂ := R₂) (N := N) (mbar := hp1Loc Dh P₁ P₂)
    (c := fun j => max (3 / 2 - r₁ * sampleNodes j) (3 / 2 - r₂ * sampleNodes j))
    (e := hp1RowFac n₀ vmin r₁ r₂) (mul_nonneg (by linarith) hvmin) (by norm_num) hV0 ht
    (by norm_num) (sq_nonneg s) hsR hRR₂ monotone_sampleNodes hlo' hhi'
    (fun i _ z hz => by
      rw [← mul_assoc]
      exact add_mul_le_corners hDh' hb hz)
    (fun i _ => sub_mul_le_max_of_mem ⟨hsV1, hsV2⟩)
    (fun i _ => ⟨hp1RowFac_nonneg n₀ vmin r₁ r₂ i, hp1RowFac_le_exp hn₀ hvmin r₁ r₂ i⟩)
  have hXm : X ≤ startMainShort (((n₀ : ℝ) - 2) * vmin) (3 / 2) (3 / 2 + 5 / 2 + 2 * 3)
      (v₀ + v₁) (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁)) (β₀ * v₀ + β₁ * v₁) (d₀ + d₁) t L
      (1 / 10 ^ 15) Λ 6 := le_trans (hsum _ ⟨hsV1, hsV2⟩) hmain
  -- the other terms
  have hfin := hp1LowerBoundShort_ge (n₀ := n₀) (m₀ := 8) (vmin := vmin) (vmax := vmax)
    (M₁ := 7) (K₂ := 10) (Klate := Klate) (σR2 := σR2) (v₀' := v0h) (v₁' := v1h)
    (V' := v0h + v1h) (σ' := 1.00002) (S' := 2.00003) (d₀' := d0) (D' := Dl) hXm (by norm_num)
    (by norm_num) hvmax hvmax0 (by linarith) hv₀h (by linarith) hv₁h (by linarith) (by linarith)
    hσh (by linarith [hS.1]) hS.2 hd₀ hd0 hDl' hDl
  have htl := hp1Tails_le htails
  set T := Real.exp (-((5 / 2 + 3) ^ 2 / (2 * v0h)))
    + Real.exp (-((5 / 2 + 2 * 3) ^ 2 / (2 * (v0h + v1h))))
    + 2 * Real.exp (-((7 - d0) ^ 2 / (2 * 1.00002)))
    + Real.exp (-((10 + Dl) ^ 2 / (2 * 2.00003))) with hT
  set Cl := (1 - normCDF (3 / 2 / √v0h)) * (√v1h * (√(2 * π))⁻¹) with hCl
  have hYle : X - ce - (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414)
      ≤ X - Cl - (3 / 2 + 5 / 2 + 2 * 3) * T := by
    have : (3 / 2 + 5 / 2 + 2 * 3 : ℝ) * T ≤ (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414) :=
      mul_le_mul_of_nonneg_left htl (by norm_num)
    linarith
  have hprod := mul_le_mul hk hYle hY (le_trans hk0 hk)
  -- the slope loss on `3/2 + √V'(2π)^{-1/2} ≤ 3/2 + 0.3989422805r₂`
  have hw : 3 / 2 + √(v0h + v1h) * (√(2 * π))⁻¹ ≤ 3 / 2 + 0.3989422805 * r₂ := by
    have := mul_le_mul ((Real.sqrt_le_left hr₂.le).2 hr₂V) inv_sqrt_two_pi_bounds.2
      (inv_nonneg.2 (Real.sqrt_nonneg _)) hr₂.le
    linarith
  have hw0 : 0 ≤ 3 / 2 + √(v0h + v1h) * (√(2 * π))⁻¹ := by positivity
  have hsl := mul_le_mul hsp hw hw0
    (le_trans (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) hsp)
  linarith

/-! ### The rows, factored, a step in `Λ` -/

/-- **Factored rows, a step in `Λ`**: rows `τ_j ≤ RMF.hp1Term … Λ …` on `√V ∈ [r₁, r₂]`, `r₁ ≥ 0`,
the top node `r₂z_N ≤ 3/2` or `z_N ≤ 0`, and factors `f_j ∈ [0, 1]` give, at `Λ' ≤ Λ + δ`,
`0 ≤ δ ≤ 1`, `∑_j τ_jf_j - 2δ(3/2 + 0.3989422805r₂) ≤ ∑_j RMF.hp1Term … Λ' …·f_j`: each row loses at
most `2δ` times its weight (`RMF.hp1Term_sub_le_of_le_add`), and the weights are nonnegative and
telescope (`RMF.sum_hp1Weight_le`). -/
theorem le_sum_hp1Term_mul_of_rows {t L Λ Λ' R₁ R₂ D P₁ P₂ r₁ r₂ δ X : ℝ} {N : ℕ}
    {τ f : ℕ → ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hΛ : Λ' ≤ Λ + δ) (hr₁ : 0 ≤ r₁)
    (hN : r₂ * sampleNodes N ≤ 3 / 2 ∨ sampleNodes N ≤ 0) (hf : ∀ j < N, 0 ≤ f j ∧ f j ≤ 1)
    (hrow : ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → ∀ j < N, τ j ≤ hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j)
    (hX : X ≤ ∑ j ∈ Finset.range N, τ j * f j - 2 * δ * (3 / 2 + 0.3989422805 * r₂)) :
    ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ →
      X ≤ ∑ j ∈ Finset.range N, hp1Term t L Λ' R₁ R₂ D P₁ P₂ sV j * f j := by
  intro sV hsV
  have hsV0 : 0 ≤ sV := le_trans hr₁ hsV.1
  have hr₂ : 0 ≤ r₂ := le_trans hsV0 hsV.2
  have hw : ∀ j ∈ Finset.range N, 0 ≤ hp1Weight sV j := by
    intro j hj
    have hz := monotone_sampleNodes (Finset.mem_range.1 hj : j + 1 ≤ N)
    refine hp1Weight_nonneg ⟨hsV0, hsV.2⟩ ?_
    rcases le_total (sampleNodes (j + 1)) 0 with h0 | h0
    · exact Or.inr h0
    · rcases hN with h | h
      · exact Or.inl (le_trans (mul_le_mul_of_nonneg_left hz hr₂) h)
      · exact Or.inr (le_trans hz h)
  have hrow' : ∀ j ∈ Finset.range N, τ j * f j - 2 * δ * hp1Weight sV j
      ≤ hp1Term t L Λ' R₁ R₂ D P₁ P₂ sV j * f j := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    obtain ⟨hf0, hf1⟩ := hf j hj'
    have h1 : τ j * f j ≤ hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j * f j :=
      mul_le_mul_of_nonneg_right (hrow sV hsV j hj') hf0
    have h2 := mul_le_mul_of_nonneg_right
      (hp1Term_sub_le_of_le_add (t := t) (L := L) (R₁ := R₁) (R₂ := R₂) (D := D) (P₁ := P₁)
        (P₂ := P₂) hδ0 hδ1 hΛ (hw j hj)) hf0
    have h3 : 2 * δ * hp1Weight sV j * f j ≤ 2 * δ * hp1Weight sV j :=
      mul_le_of_le_one_right (mul_nonneg (by linarith) (hw j hj)) hf1
    have e : (hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j - 2 * δ * hp1Weight sV j) * f j
        = hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j * f j - 2 * δ * hp1Weight sV j * f j := by ring
    rw [e] at h2
    linarith
  have h1 := Finset.sum_le_sum hrow'
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  have h2 := sum_hp1Weight_le hsV0 N
  have h3 : 0.3989422805 * sV ≤ 0.3989422805 * r₂ :=
    mul_le_mul_of_nonneg_left hsV.2 (by norm_num)
  have h4 : 2 * δ * ∑ j ∈ Finset.range N, hp1Weight sV j
      ≤ 2 * δ * (3 / 2 + 0.3989422805 * r₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- **The rows at a rung, a step in `Λ`**: `RMF.le_sum_hp1Term_mul_of_rows` at the factors
`RMF.hp1RowFac n₀ v₋ r₁ r₂`, so that a piece's lower sum at rung `n₀` is one numeral,
`X ≤ ∑_j τ_j·RMF.hp1RowFac n₀ v₋ r₁ r₂ j - 2δ(3/2 + 0.3989422805r₂)`. -/
theorem le_sum_hp1Term_mul_hp1RowFac {n₀ : ℕ} {vmin t L Λ Λ' R₁ R₂ D P₁ P₂ r₁ r₂ δ X : ℝ}
    {N : ℕ} {τ : ℕ → ℝ} (hn₀ : 2 ≤ n₀) (hvmin : 0 ≤ vmin) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hΛ : Λ' ≤ Λ + δ) (hr₁ : 0 ≤ r₁) (hN : r₂ * sampleNodes N ≤ 3 / 2 ∨ sampleNodes N ≤ 0)
    (hrow : ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → ∀ j < N, τ j ≤ hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j)
    (hX : X ≤ ∑ j ∈ Finset.range N, τ j * hp1RowFac n₀ vmin r₁ r₂ j
      - 2 * δ * (3 / 2 + 0.3989422805 * r₂)) :
    ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → X ≤ ∑ j ∈ Finset.range N,
      hp1Term t L Λ' R₁ R₂ D P₁ P₂ sV j * hp1RowFac n₀ vmin r₁ r₂ j :=
  le_sum_hp1Term_mul_of_rows hδ0 hδ1 hΛ hr₁ hN
    (fun j _ => ⟨hp1RowFac_nonneg n₀ vmin r₁ r₂ j, hp1RowFac_le_one hn₀ hvmin r₁ r₂ j⟩) hrow hX

/-! ### The cells' statements on short tubes -/

/-- HP1's short-tube bound at rung `n₀` and a cell's numerals `P`, at the event's parameters
`a = 3/2, A = 5/2, B = 3, M₁ = 7, K₂ = 10`, `ρ = 10⁻¹⁵`, `A_W = 6`, `m₀ = 8`. -/
noncomputable def hp1CellLowerBoundShort (n₀ : ℕ) (P : HP1CellNumerals)
    (v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ) : ℝ :=
  hp1LowerBoundShort n₀ 8 P.vmin P.vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ (3 / 2) (5 / 2) 3 7 10
    (1 / 10 ^ 15) P.L P.t P.Λ 6 P.Klate P.σR2

/-- The side conditions of `RMF.le_measure_windowEvent_of_hyps_short` at a cell's numerals `P`
(`A' = 40`, `B' = 2`, `A_W = 6`, and `a, A, B, K₂` of the event): `RMF.HP1CellSide` without
`(a + A + 2B)² ≤ 2(n₀ - 2)v₋`. -/
def HP1CellSideShort (P : HP1CellNumerals) : Prop :=
  0 < P.vmin ∧ 2 * P.vmax < 3 ∧ 0 ≤ P.t ∧ 0 < P.σR2 ∧ P.Klate ≤ P.L ∧ 10 + P.KR + 6 ≤ 40
    ∧ P.BW ≤ 2

end RMF
