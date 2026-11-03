/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Grid.Cells0
import RMF.UniformLower.HP1Grid.Cells1
import RMF.UniformLower.HP1Grid.Cells2
import RMF.UniformLower.HP1Grid.Cells3
import RMF.UniformLower.HP1Grid.Cells4
import RMF.UniformLower.HP1Grid.Cells5
import RMF.UniformLower.HP1Grid.Cells6
import RMF.UniformLower.HP1Grid.Cells7

/-!
# HP1's certificate, the generic rows

The lemmas the emitted certificate of HP1 is made of.  On cell `i` of the window,
`RMF.hp1LowerBoundV2` is bounded below at every data point of the cell's start ranges
(`RMF.HP1StartRanges`), with the event's parameters `a = 3/2, A = 5/2, B = 3, M₁ = 7, K₂ = 10`,
`ρ = 10⁻¹⁵`, `A_W = 6`, `n₀ = 2000`, `m₀ = 8`.

* **`exp` by Taylor's sums** (`RMF.exp_le_of_taylor`, `RMF.exp_le_of_sum_neg`,
  `RMF.le_exp_neg_of_taylor`): every exponential of the certificate is a rational comparison for
  `norm_num`, no interval arithmetic.
* **The rows** (`RMF.hp1Term`, `RMF.hp1Row_le`): `RMF.cell_le` on the fixed nodes
  `RMF.sampleNodes` (`z_j = -17/4 + 3j/20`), whose `Φ` and `φ` values are certified once for all
  cells.
* **The other terms**: `RMF.hp1Slope_ge`, `RMF.hp1Loss_le_of`, `RMF.hp1Ceil_le` reduce them to
  rational side conditions; the tails are `≤ 5e^{-17}`.
* **One cell** (`RMF.hp1LowerBoundV2_of_lowerSum`): the lower sum `RMF.sum_le_startMainV2` at the
  cell's worst location, the residual variance's range covered by pieces (each with its own lower
  sum), then `RMF.hp1LowerBoundV2_ge`.  The slope `κ/√V` and the residual variance `S - κ²/V` are
  bracketed from the ranges of `κ` and `V` with the sign of `κ` taken into account (`min κ² = 0`
  when the range of `κ` contains `0`).
-/

open MeasureTheory ProbabilityTheory
open scoped Real

namespace RMF

/-! ### `exp` by Taylor's sums -/

/-- **`e^x` from above by Taylor**: for `x ≤ k + f`, `0 ≤ f ≤ 1`,
`e^x ≤ 2.7182818286^k (∑_{m<n} f^m/m! + f^n(n+1)/(n!n))` (Mathlib's `Real.exp_bound'`). -/
lemma exp_le_of_taylor {x f B : ℝ} (k n : ℕ) (hn : 0 < n) (hx : x ≤ k + f) (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1)
    (hB : 2.7182818286 ^ k * ((∑ m ∈ Finset.range n, f ^ m / m.factorial) +
      f ^ n * (n + 1) / (n.factorial * n)) ≤ B) :
    Real.exp x ≤ B := by
  have h1 : Real.exp x ≤ Real.exp ((k : ℝ) + f) := Real.exp_le_exp.2 hx
  have h2 : Real.exp ((k : ℝ) + f) = Real.exp 1 ^ k * Real.exp f := by
    rw [Real.exp_add, Real.exp_one_pow]
  have h3 : Real.exp 1 ^ k ≤ 2.7182818286 ^ k :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le k
  have h4 := Real.exp_bound' hf0 hf1 hn
  have h5 : Real.exp 1 ^ k * Real.exp f ≤ 2.7182818286 ^ k * ((∑ m ∈ Finset.range n,
      f ^ m / m.factorial) + f ^ n * (n + 1) / (n.factorial * n)) :=
    mul_le_mul h3 h4 (Real.exp_pos f).le (by positivity)
  linarith

/-- **`e^x` from above for `x ≤ -y`**, by Taylor's lower sums of `e^y`: `1 ≤ B·∑_{m<n} y^m/m!`. -/
lemma exp_le_of_sum_neg {x y B : ℝ} (n : ℕ) (hx : x ≤ -y) (hy : 0 ≤ y)
    (hB : 1 ≤ B * ∑ m ∈ Finset.range n, y ^ m / m.factorial) : Real.exp x ≤ B := by
  set S := ∑ m ∈ Finset.range n, y ^ m / (m.factorial : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  have hSe : S ≤ Real.exp y := Real.sum_le_exp_of_nonneg hy n
  have hSpos : 0 < S := by
    rcases hS0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hB
      linarith
  have hB0 : 0 < B := by
    by_contra hneg
    have : B * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hS0
    linarith
  have h1 : Real.exp x ≤ Real.exp (-y) := Real.exp_le_exp.2 hx
  have h2 : Real.exp (-y) * S ≤ 1 := by
    rw [Real.exp_neg]
    calc (Real.exp y)⁻¹ * S ≤ (Real.exp y)⁻¹ * Real.exp y :=
          mul_le_mul_of_nonneg_left hSe (inv_nonneg.2 (Real.exp_pos y).le)
      _ = 1 := inv_mul_cancel₀ (Real.exp_pos y).ne'
  have h3 : Real.exp (-y) ≤ B := by
    by_contra hlt
    have := mul_lt_mul_of_pos_right (not_le.1 hlt) hSpos
    linarith
  linarith

/-- **`e^{-y}` from below by Taylor**: for `y ≤ k + f`, `0 ≤ f ≤ 1`,
`B·2.7182818286^k (∑_{m<n} f^m/m! + f^n(n+1)/(n!n)) ≤ 1` gives `B ≤ e^{-y}`. -/
lemma le_exp_neg_of_taylor {y f B : ℝ} (k n : ℕ) (hn : 0 < n) (hy : y ≤ k + f) (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1)
    (hB : B * (2.7182818286 ^ k * ((∑ m ∈ Finset.range n, f ^ m / m.factorial) +
      f ^ n * (n + 1) / (n.factorial * n))) ≤ 1) :
    B ≤ Real.exp (-y) := by
  set T := 2.7182818286 ^ k * ((∑ m ∈ Finset.range n, f ^ m / (m.factorial : ℝ)) +
      f ^ n * (n + 1) / (n.factorial * n)) with hT
  have hyT : Real.exp y ≤ T := exp_le_of_taylor k n hn hy hf0 hf1 le_rfl
  rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos y)]
  rcases le_or_gt 0 B with hB0 | hB0
  · calc B * Real.exp y ≤ B * T := mul_le_mul_of_nonneg_left hyT hB0
      _ ≤ 1 := hB
  · have := mul_neg_of_neg_of_pos hB0 (Real.exp_pos y)
    linarith

/-- `B ≤ e^x` for `x ≥ 0` from Taylor's lower sums, `B ≤ ∑_{m<n} x^m/m!`. -/
lemma le_exp_of_sum {x B : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hB : B ≤ ∑ m ∈ Finset.range n, x ^ m / m.factorial) : B ≤ Real.exp x :=
  le_trans hB (Real.sum_le_exp_of_nonneg hx n)

/-! ### The rows of the lower sums -/

/-- The location bound of subcell `j` of the lower sum: `D + max(P₁z_j, P₁z_{j+1}, P₂z_j,
P₂z_{j+1})`, `z_j = RMF.sampleNodes j`, the worst case of `D + bz` over `b ∈ [P₁, P₂]`. -/
noncomputable def hp1Loc (D P₁ P₂ : ℝ) (j : ℕ) : ℝ :=
  D + max (max (P₁ * sampleNodes j) (P₁ * sampleNodes (j + 1)))
    (max (P₂ * sampleNodes j) (P₂ * sampleNodes (j + 1)))

/-- **The summand of HP1's lower sums** on subcell `j` (`RMF.sum_le_startMainV2` at `a = 3/2`,
`ρ = 10⁻¹⁵`, `A_W = 6`, the nodes `RMF.sampleNodes`, the location `RMF.hp1Loc`), at `√V = sV`. -/
noncomputable def hp1Term (t L Λ R₁ R₂ D P₁ P₂ sV : ℝ) (j : ℕ) : ℝ :=
  max (exitMean t L (1 / 10 ^ 15) Λ 6 (hp1Loc D P₁ P₂ j) R₁
      - t ^ 2 * (1 - Real.exp (-6)) / 2 * (R₂ - R₁)) 0
    * (3 / 2 * (normCDF (sampleNodes (j + 1)) - normCDF (sampleNodes j))
      - sV * (gaussianPDFReal 0 1 (sampleNodes j) - gaussianPDFReal 0 1 (sampleNodes (j + 1))))

lemma hp1Loc_le {D P₁ P₂ m : ℝ} {j : ℕ}
    (h : D + P₁ * sampleNodes j ≤ m ∧ D + P₁ * sampleNodes (j + 1) ≤ m
      ∧ D + P₂ * sampleNodes j ≤ m ∧ D + P₂ * sampleNodes (j + 1) ≤ m) :
    hp1Loc D P₁ P₂ j ≤ m := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  unfold hp1Loc
  have : max (max (P₁ * sampleNodes j) (P₁ * sampleNodes (j + 1)))
      (max (P₂ * sampleNodes j) (P₂ * sampleNodes (j + 1))) ≤ m - D :=
    max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
  linarith

/-- **One row of a lower sum**: `RMF.cell_le` at the certificate's global parameters, with
`R₁ = s²`, `c = 0.9975 ≤ 1 - e^{-6}` and `K' = t²/2`.  The row's own inputs are the location `m`,
`Φ(q) ≥ p_q`, `Φ(q - ts) ≤ p'_q` and `e^{t(m+L+ρ)+Λ+t²s²/2} ≤ E`; the node data `Φ(z_{j+1}) ≥ lo`,
`Φ(z_j) ≤ hi`, `φ(z_j) ≤ 0.3989422805e₀`, `φ(z_{j+1}) ≥ 0.3989422804e₁` are shared by all cells. -/
theorem hp1Row_le {t L Λ s R₂ D P₁ P₂ r₁ r₂ sV : ℝ} {j : ℕ} {q m Eq pq pq' lo hi e₀ e₁ τ : ℝ}
    (hsV : r₁ ≤ sV ∧ sV ≤ r₂) (hr₁ : 0 ≤ r₁) (hs : 0 < s) (hR : s ^ 2 ≤ R₂) (ht : 0 ≤ t)
    (hloc : D + P₁ * sampleNodes j ≤ m ∧ D + P₁ * sampleNodes (j + 1) ≤ m
      ∧ D + P₂ * sampleNodes j ≤ m ∧ D + P₂ * sampleNodes (j + 1) ≤ m)
    (hpq : pq ≤ normCDF q) (hpq' : normCDF (q - t * s) ≤ pq')
    (hE : Real.exp (t * (m + L + 1 / 10 ^ 15) + Λ + t ^ 2 * s ^ 2 / 2) ≤ Eq)
    (hlo : lo ≤ normCDF (sampleNodes (j + 1))) (hhi : normCDF (sampleNodes j) ≤ hi)
    (he₀ : gaussianPDFReal 0 1 (sampleNodes j) ≤ 0.3989422805 * e₀)
    (he₁ : 0.3989422804 * e₁ ≤ gaussianPDFReal 0 1 (sampleNodes (j + 1)))
    (hnum : 0 ≤ pq ∧ 0 ≤ 0.9975 * pq - Eq * pq' - t ^ 2 / 2 * (R₂ - s ^ 2)
      ∧ 0 ≤ 3 / 2 * (lo - hi) - max (r₁ * (0.3989422805 * e₀ - 0.3989422804 * e₁))
        (r₂ * (0.3989422805 * e₀ - 0.3989422804 * e₁))
      ∧ τ ≤ (0.9975 * pq - Eq * pq' - t ^ 2 / 2 * (R₂ - s ^ 2))
        * (3 / 2 * (lo - hi) - max (r₁ * (0.3989422805 * e₀ - 0.3989422804 * e₁))
          (r₂ * (0.3989422805 * e₀ - 0.3989422804 * e₁)))) :
    τ ≤ hp1Term t L Λ (s ^ 2) R₂ D P₁ P₂ sV j := by
  obtain ⟨hpq0, hγ, hf, hτ⟩ := hnum
  have hK : t ^ 2 * (1 - Real.exp (-6)) / 2 ≤ t ^ 2 / 2 := by
    have h1 := Real.exp_pos (-6)
    have h2 := sq_nonneg t
    nlinarith
  exact le_trans hτ (cell_le (a := 3 / 2) (c := 0.9975) (K' := t ^ 2 / 2) (R₁ := s ^ 2)
    (mb := hp1Loc D P₁ P₂ j) hs rfl hR ht (hp1Loc_le hloc) hpq hpq0 hpq' hE sample_c
    (by norm_num) hK hγ hlo hhi he₀ he₁ hsV hr₁ (by norm_num) hf)

/-- A row can always be taken as `0`: the summand is nonnegative below the top node. -/
theorem hp1Row_zero {t L Λ R₁ R₂ D P₁ P₂ r₂ sV : ℝ} {j : ℕ} (hsV : 0 ≤ sV ∧ sV ≤ r₂)
    (htop : r₂ * sampleNodes (j + 1) ≤ 3 / 2 ∨ sampleNodes (j + 1) ≤ 0) :
    0 ≤ hp1Term t L Λ R₁ R₂ D P₁ P₂ sV j := by
  have hle : sampleNodes j ≤ sampleNodes (j + 1) := monotone_sampleNodes (Nat.le_succ j)
  have hw : 0 ≤ 3 / 2 * (normCDF (sampleNodes (j + 1)) - normCDF (sampleNodes j))
      - sV * (gaussianPDFReal 0 1 (sampleNodes j) - gaussianPDFReal 0 1 (sampleNodes (j + 1))) := by
    have h := intervalIntegral_affine_gaussianReal hle (3 / 2) sV 1
    rw [one_mul] at h
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
  exact mul_nonneg (le_max_right _ _) hw

/-! ### The other terms, by rational side conditions -/

lemma sqrt_two_thousand_le : √((2000 : ℕ) / ((2000 : ℕ) - 2 : ℝ)) ≤ 1.0006 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

lemma exp_neg_eight_half_le : Real.exp (-(5 / 2 + 2 * 3)) ≤ (0.00020347 : ℝ) :=
  exp_le_of_sum_neg (y := 5 / 2 + 2 * 3) 32 le_rfl (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

lemma exp_neg_seventeen_le : Real.exp (-17) ≤ (0.0000000414 : ℝ) :=
  exp_le_of_sum_neg 50 le_rfl (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- **`RMF.hp1Slope` from below by rational side conditions** (`n₀ = 2000`, `m₀ = 8`,
`a + A + 2B = 10`): `2πv₊ ≤ u₁²`, `2n₀ ≤ u₂²π(n₀ - 2 - m₀)v₋` (by `3.141592 < π < 3.141593`) and
`e^{-(L-K)²/(2σ²)} ≤ e`. -/
lemma hp1Slope_ge {vmin vmax L Klate σR2 u₁ u₂ e sl : ℝ} (hvmin : 0 < vmin) (hvmax : 0 < vmax)
    (hnum : 0 ≤ 1 - (3 / 2 + 5 / 2 + 2 * 3) ^ 2 / (2 * (((2000 : ℕ) - 2 : ℝ) * vmin)))
    (hu₁0 : 0 ≤ u₁) (hu₁ : 2 * 3.141593 * vmax ≤ u₁ ^ 2) (hu₂0 : 0 ≤ u₂)
    (hu₂ : 2 * 2000 ≤ u₂ ^ 2 * (3.141592 * ((2000 - 2 - 8) * vmin)))
    (he : Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ e)
    (hsl : sl ≤ 2 * (1 - (3 / 2 + 5 / 2 + 2 * 3) ^ 2 / (2 * (((2000 : ℕ) - 2 : ℝ) * vmin))) / u₁
      - u₂ * e) :
    sl ≤ hp1Slope 2000 8 vmin vmax (3 / 2) (5 / 2) 3 L Klate σR2 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  refine le_trans hsl (le_hp1Slope hnum hvmax ?_ ?_ he)
  · rw [Real.sqrt_le_left hu₁0]
    nlinarith
  · rw [Real.sqrt_le_left hu₂0]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ u₂ ^ 2 * ((2000 - 2 - 8) * vmin) := by positivity
    nlinarith

/-- **`RMF.hp1Loss` from above by rational side conditions** (`n₀ = 2000`, `m₀ = 8`, `A = 5/2`,
`B = 3`), through `RMF.hp1Loss_le`. -/
lemma hp1Loss_le_of {vmin vmax V L Klate σR2 w₃ w₄ l w₆ w₇ e w₈ lo : ℝ} (hvmin : 0 < vmin)
    (hvmax : 0 ≤ vmax) (hB : 2 * vmax < 3) (h₃0 : 0 ≤ w₃) (h₃ : 3.141593 * vmax / 2 ≤ w₃ ^ 2)
    (h₄0 : 0 ≤ w₄) (h₄ : 4 ≤ w₄ ^ 2 * (3.141592 * vmin))
    (h₄' : 2 ≤ w₄ ^ 2 * (2.7182818283 * (3 - 2 * vmax))) (hl : 0 < l)
    (h₅ : l + 1 ≤ Real.exp ((3 - 2 * vmax) / 2)) (h₆ : Real.exp (V / 2) ≤ w₆) (h₇0 : 0 ≤ w₇)
    (h₇ : 2 * 2000 ≤ w₇ ^ 2 * (3.141592 * ((2000 - 2 - 8) * vmin)))
    (he : Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) ≤ e) (h₈0 : 0 ≤ w₈)
    (h₈ : e * (8 * vmax) ≤ w₈ ^ 2)
    (hlo : 1.0006 * (0.00020347 * (3 / 2 + 5 / 2 + 2 * 3 + w₃ + 2) * w₄ / l) * w₆
      + w₇ * (w₃ * e + w₈) ≤ lo) :
    hp1Loss 2000 8 vmin vmax V (3 / 2) (5 / 2) 3 L Klate σR2 ≤ lo := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have he1 := Real.exp_one_gt_d9
  refine le_trans (hp1Loss_le (w₁ := 1.0006) (w₂ := 0.00020347) (by norm_num)
    sqrt_two_thousand_le exp_neg_eight_half_le ?_ ?_ ?_ hl ?_ h₆ ?_ he ?_) hlo
  · rw [Real.sqrt_le_left h₃0]
    nlinarith
  · rw [Real.sqrt_le_left h₄0, div_le_iff₀ (by positivity)]
    nlinarith
  · have hB' : 0 < (3 : ℝ) - 2 * vmax := by linarith
    rw [Real.sqrt_le_left h₄0, div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ w₄ ^ 2 * (3 - 2 * vmax) := by positivity
    nlinarith
  · linarith
  · rw [Real.sqrt_le_left h₇0]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ w₇ ^ 2 * ((2000 - 2 - 8) * vmin) := by positivity
    nlinarith
  · rw [Real.sqrt_le_left h₈0]
    push_cast
    have := mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 8 * vmax)
    linarith

/-- **The ceiling loss from above**: for `0 ≤ q`, `q²v₀' ≤ (3/2)²` (so `q ≤ a/√v₀'`), `Φ(q) ≥ p`
and `v₁' ≤ w²`: `(1 - Φ(a/√v₀'))√v₁'(2π)^{-1/2} ≤ (1 - p)·0.3989422805w`. -/
lemma hp1Ceil_le {v0h v1h q pc w ce : ℝ} (hv0 : 0 < v0h) (hq : 0 ≤ q)
    (hq2 : q ^ 2 * v0h ≤ (3 / 2) ^ 2) (hpc : pc ≤ normCDF q) (hpc1 : pc ≤ 1) (hw0 : 0 ≤ w)
    (hw : v1h ≤ w ^ 2) (hce : (1 - pc) * (w * 0.3989422805) ≤ ce) :
    (1 - normCDF (3 / 2 / √v0h)) * (√v1h * (√(2 * π))⁻¹) ≤ ce := by
  have hs0 : 0 < √v0h := Real.sqrt_pos.2 hv0
  have hq' : q ≤ 3 / 2 / √v0h := by
    rw [le_div_iff₀ hs0]
    have h1 : (q * √v0h) ^ 2 ≤ (3 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hv0.le]
      exact hq2
    have h2 : 0 ≤ q * √v0h := mul_nonneg hq hs0.le
    nlinarith
  have hΦ : pc ≤ normCDF (3 / 2 / √v0h) := le_trans hpc (normCDF_mono hq')
  have hsw : √v1h ≤ w := (Real.sqrt_le_left hw0).2 hw
  have hc := inv_sqrt_two_pi_bounds.2
  have h1 : 0 ≤ 1 - normCDF (3 / 2 / √v0h) := by linarith [normCDF_le_one (3 / 2 / √v0h)]
  calc (1 - normCDF (3 / 2 / √v0h)) * (√v1h * (√(2 * π))⁻¹)
      ≤ (1 - pc) * (w * 0.3989422805) :=
        mul_le_mul (by linarith) (mul_le_mul hsw hc (by positivity) hw0) (by positivity)
          (by linarith)
    _ ≤ ce := hce

/-- **The start's tails from above**: each of the four exponents of `RMF.hp1LowerBoundV2_ge`'s tails
is at least `17`, so the tails are at most `5e^{-17} ≤ 5·4.14·10⁻⁸`. -/
lemma hp1Tails_le {v0h V d0 Dl : ℝ}
    (h : 17 ≤ (5 / 2 + 3) ^ 2 / (2 * v0h) ∧ 17 ≤ (5 / 2 + 2 * 3) ^ 2 / (2 * V)
      ∧ 17 ≤ (7 - d0) ^ 2 / (2 * 1.00002) ∧ 17 ≤ (10 + Dl) ^ 2 / (2 * 2.00003)) :
    Real.exp (-((5 / 2 + 3) ^ 2 / (2 * v0h))) + Real.exp (-((5 / 2 + 2 * 3) ^ 2 / (2 * V)))
        + 2 * Real.exp (-((7 - d0) ^ 2 / (2 * 1.00002)))
        + Real.exp (-((10 + Dl) ^ 2 / (2 * 2.00003))) ≤ 5 * 0.0000000414 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have e := exp_neg_seventeen_le
  have e₁ : Real.exp (-((5 / 2 + 3) ^ 2 / (2 * v0h))) ≤ Real.exp (-17) :=
    Real.exp_le_exp.2 (by linarith)
  have e₂ : Real.exp (-((5 / 2 + 2 * 3) ^ 2 / (2 * V))) ≤ Real.exp (-17) :=
    Real.exp_le_exp.2 (by linarith)
  have e₃ : Real.exp (-((7 - d0) ^ 2 / (2 * 1.00002))) ≤ Real.exp (-17) :=
    Real.exp_le_exp.2 (by linarith)
  have e₄ : Real.exp (-((10 + Dl) ^ 2 / (2 * 2.00003))) ≤ Real.exp (-17) :=
    Real.exp_le_exp.2 (by linarith)
  linarith

/-! ### One cell -/

/-- The slope `κ/√V` from the ranges `κ ∈ [k₁, k₂]`, `√V ∈ [r₁, r₂]`, whatever the signs. -/
lemma div_sqrt_mem_of_ranges {κ sV k₁ k₂ r₁ r₂ P₁ P₂ : ℝ} (hr₁ : 0 < r₁) (hsV : r₁ ≤ sV ∧ sV ≤ r₂)
    (hκ : k₁ ≤ κ ∧ κ ≤ k₂) (hP : P₁ ≤ k₁ / r₁ ∧ P₁ ≤ k₁ / r₂ ∧ k₂ / r₁ ≤ P₂ ∧ k₂ / r₂ ≤ P₂) :
    κ / sV ∈ Set.Icc P₁ P₂ := by
  obtain ⟨hs₁, hs₂⟩ := hsV
  obtain ⟨hP₁, hP₁', hP₂, hP₂'⟩ := hP
  have hs0 : 0 < sV := lt_of_lt_of_le hr₁ hs₁
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hs0 hs₂
  constructor
  · have h1 : k₁ / sV ≤ κ / sV := div_le_div_of_nonneg_right hκ.1 hs0.le
    rcases le_total 0 k₁ with hk | hk
    · have h2 : k₁ / r₂ ≤ k₁ / sV := div_le_div_of_nonneg_left hk hs0 hs₂
      linarith
    · have h2 : k₁ / r₁ ≤ k₁ / sV := by
        rw [div_le_div_iff₀ hr₁ hs0]
        exact mul_le_mul_of_nonpos_left hs₁ hk
      linarith
  · have h1 : κ / sV ≤ k₂ / sV := div_le_div_of_nonneg_right hκ.2 hs0.le
    rcases le_total 0 k₂ with hk | hk
    · have h2 : k₂ / sV ≤ k₂ / r₁ := div_le_div_of_nonneg_left hk hr₁ hs₁
      linarith
    · have h2 : k₂ / sV ≤ k₂ / r₂ := by
        rw [div_le_div_iff₀ hs0 hr₂]
        exact mul_le_mul_of_nonpos_left hs₂ hk
      linarith

/-- The residual variance `S - κ²/V` from the ranges of `S`, `V` and `κ`: from below with
`κ² ≤ K₂`, from above with `κ² ≥ k₂` (`k₂ = 0` when the range of `κ` contains `0`). -/
lemma pairResidVar_mem_of_ranges {V S κ Vl Vh Sl Sh kl kh K2 k2 : ℝ} (hVl : 0 < Vl)
    (hV : Vl ≤ V ∧ V ≤ Vh) (hS : Sl ≤ S ∧ S ≤ Sh) (hκ : kl ≤ κ ∧ κ ≤ kh)
    (hK2 : kl ^ 2 ≤ K2 ∧ kh ^ 2 ≤ K2)
    (hk2 : 0 ≤ k2 ∧ (k2 = 0 ∨ (0 ≤ kl ∧ k2 ≤ kl ^ 2) ∨ (kh ≤ 0 ∧ k2 ≤ kh ^ 2))) :
    Sl - K2 / Vl ≤ pairResidVar V S κ ∧ pairResidVar V S κ ≤ Sh - k2 / Vh := by
  obtain ⟨hV₁, hV₂⟩ := hV
  obtain ⟨hκ₁, hκ₂⟩ := hκ
  have hV0 : 0 < V := lt_of_lt_of_le hVl hV₁
  have hsq : κ ^ 2 ≤ K2 := by
    rcases le_total 0 κ with h | h
    · exact le_trans (pow_le_pow_left₀ h hκ₂ 2) hK2.2
    · have : (-κ) ^ 2 ≤ (-kl) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      rw [neg_sq, neg_sq] at this
      exact le_trans this hK2.1
  have hsq' : k2 ≤ κ ^ 2 := by
    obtain ⟨hk0, hk | ⟨hkl, hk⟩ | ⟨hkh, hk⟩⟩ := hk2
    · rw [hk]; exact sq_nonneg κ
    · exact le_trans hk (pow_le_pow_left₀ hkl hκ₁ 2)
    · have : (-kh) ^ 2 ≤ (-κ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      rw [neg_sq, neg_sq] at this
      exact le_trans hk this
  have h1 : κ ^ 2 / V ≤ K2 / Vl :=
    div_le_div₀ (le_trans (sq_nonneg κ) hsq) hsq hVl hV₁
  have h2 : k2 / Vh ≤ κ ^ 2 / V := div_le_div₀ (sq_nonneg κ) hsq' hV0 hV₂
  unfold pairResidVar
  constructor <;> linarith [hS.1, hS.2]

/-- One piece `[b, b']` of the residual variance's range: its lower sum (at `R₁ = s² ≤ b`,
`R₂ ≥ b'`) covers every `R ∈ [b, b']`. -/
lemma hp1Piece {t L Λ Dh P₁ P₂ r₁ r₂ X Xp s R₂ b b' R : ℝ} {N : ℕ} (hs : 0 < s)
    (hsb : s ^ 2 ≤ b) (hbR : b ≤ R) (hRb : R ≤ b') (hbR₂ : b' ≤ R₂) (hX : X ≤ Xp)
    (hsum : ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ →
      Xp ≤ ∑ j ∈ Finset.range N, hp1Term t L Λ (s ^ 2) R₂ Dh P₁ P₂ sV j) :
    ∃ s R₂ : ℝ, 0 < s ∧ s ^ 2 ≤ R ∧ R ≤ R₂ ∧
      ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → X ≤ ∑ j ∈ Finset.range N, hp1Term t L Λ (s ^ 2) R₂ Dh P₁ P₂ sV j :=
  ⟨s, R₂, hs, le_trans hsb hbR, le_trans hRb hbR₂, fun sV hsV => le_trans hX (hsum sV hsV)⟩

/-- **HP1's v2 bound on one cell, from its lower sums.**  For every data point of the start
ranges `RMF.HP1StartRanges` (`S ∈ [1.99997, 2.00003]`, `σ₁² ∈ [0.99998, 1.00002]`), at the event's
parameters `a = 3/2, A = 5/2, B = 3, M₁ = 7, K₂ = 10`, `ρ = 10⁻¹⁵`, `A_W = 6`, `n₀ = 2000`,
`m₀ = 8`: `p ≤ RMF.hp1LowerBoundV2`, given

* `hX`: for every residual variance `R ∈ [R_lo, R_hi]` a piece `[s², R₂] ∋ R` whose lower sum
  (`RMF.hp1Term`, location `D_h + max(P z)`) is at least `X` for every `√V ∈ [r₁, r₂]`;
* the rational side conditions bracketing `√V`, `κ/√V`, `S - κ²/V` from the ranges, the top and
  bottom nodes (`RMF.sum_le_startMainV2`), and the tails' exponents `≥ 17`;
* the slope `≥ sl ≥ 0`, the loss at `V' = v₀' + v₁'` `≤ lo`, the ceiling loss `≤ ce`, and
  `p ≤ sl·(X - ce - 10·5·4.14·10⁻⁸) - lo` (`RMF.hp1LowerBoundV2_ge`). -/
theorem hp1LowerBoundV2_of_lowerSum {v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ}
    {v0l v0h v1l v1h kl kh d0 Dl Dh vmin vmax L t Λ Klate σR2 : ℝ}
    {r₁ r₂ P₁ P₂ K2 k2 Rlo Rhi X ce sl lo p : ℝ} {N : ℕ}
    (hs : HP1StartRanges v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ v0l v0h v1l v1h kl kh 1.99997 2.00003 0.99998
      1.00002 d0 Dl Dh)
    (hX : ∀ R, Rlo ≤ R → R ≤ Rhi → ∃ s R₂ : ℝ, 0 < s ∧ s ^ 2 ≤ R ∧ R ≤ R₂ ∧
      ∀ sV, r₁ ≤ sV ∧ sV ≤ r₂ → X ≤ ∑ j ∈ Finset.range N, hp1Term t L Λ (s ^ 2) R₂ Dh P₁ P₂ sV j)
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
    (hsl : sl ≤ hp1Slope 2000 8 vmin vmax (3 / 2) (5 / 2) 3 L Klate σR2) (hsl0 : 0 ≤ sl)
    (hlo : hp1Loss 2000 8 vmin vmax (v0h + v1h) (3 / 2) (5 / 2) 3 L Klate σR2 ≤ lo)
    (hce : (1 - normCDF (3 / 2 / √v0h)) * (√v1h * (√(2 * π))⁻¹) ≤ ce)
    (hY : 0 ≤ X - ce - (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414))
    (hp : p ≤ sl * (X - ce - (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414)) - lo) :
    p ≤ hp1LowerBoundV2 2000 8 vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ (3 / 2) (5 / 2) 3 7 10
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
  -- the main term, by the lower sum
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
  have hmain := sum_le_startMainV2 (a := 3 / 2) (C := 3 / 2 + 5 / 2 + 2 * 3)
    (S := β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁)) (κ := β₀ * v₀ + β₁ * v₁) (D := d₀ + d₁) (t := t)
    (L := L) (ρ := 1 / 10 ^ 15) (Λ := Λ) (AW := 6) (R₁ := s ^ 2) (R₂ := R₂) (N := N)
    (mbar := hp1Loc Dh P₁ P₂) (by norm_num) hV0 ht (by norm_num) (sq_nonneg s) hsR hRR₂
    monotone_sampleNodes hlo' hhi' (fun i _ z hz => by
      rw [← mul_assoc]
      exact add_mul_le_corners hDh' hb hz)
  have hXm : X ≤ startMainV2 (3 / 2) (3 / 2 + 5 / 2 + 2 * 3) (v₀ + v₁)
      (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁)) (β₀ * v₀ + β₁ * v₁) (d₀ + d₁) t L
      (1 / 10 ^ 15) Λ 6 := le_trans (hsum _ ⟨hsV1, hsV2⟩) hmain
  -- the other terms
  have hfin := hp1LowerBoundV2_ge (n₀ := 2000) (m₀ := 8) (vmin := vmin) (vmax := vmax) (M₁ := 7)
    (K₂ := 10) (Klate := Klate) (σR2 := σR2) (v₀' := v0h) (v₁' := v1h) (V' := v0h + v1h)
    (σ' := 1.00002) (S' := 2.00003) (d₀' := d0) (D' := Dl) hXm (by norm_num) (by norm_num) hvmax
    hvmax0 (by linarith) hv₀h (by linarith) hv₁h (by linarith) (by linarith) hσh
    (by linarith [hS.1]) hS.2 hd₀ hd0 hDl' hDl
  have htl := hp1Tails_le htails
  set T := Real.exp (-((5 / 2 + 3) ^ 2 / (2 * v0h)))
    + Real.exp (-((5 / 2 + 2 * 3) ^ 2 / (2 * (v0h + v1h))))
    + 2 * Real.exp (-((7 - d0) ^ 2 / (2 * 1.00002)))
    + Real.exp (-((10 + Dl) ^ 2 / (2 * 2.00003))) with hT
  set Cl := (1 - normCDF (3 / 2 / √v0h)) * (√v1h * (√(2 * π))⁻¹) with hCl
  set Sl := hp1Slope 2000 8 vmin vmax (3 / 2) (5 / 2) 3 L Klate σR2 with hSl
  set Lo := hp1Loss 2000 8 vmin vmax (v0h + v1h) (3 / 2) (5 / 2) 3 L Klate σR2 with hLo
  have hYle : X - ce - (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414)
      ≤ X - Cl - (3 / 2 + 5 / 2 + 2 * 3) * T := by
    have : (3 / 2 + 5 / 2 + 2 * 3 : ℝ) * T ≤ (3 / 2 + 5 / 2 + 2 * 3) * (5 * 0.0000000414) :=
      mul_le_mul_of_nonneg_left htl (by norm_num)
    linarith
  have hprod := mul_le_mul hsl hYle hY (le_trans hsl0 hsl)
  linarith

/-! ### The cells' statements -/

/-- A cell's start ranges at its numerals `P`: the first half of `RMF.HP1CellData`. -/
def HP1CellStart (P : HP1CellNumerals) (v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ) : Prop :=
  HP1StartRanges v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ P.v0l P.v0h P.v1l P.v1h P.kl P.kh 1.99997 2.00003
    0.99998 1.00002 P.d0 P.Dl P.Dh

/-- HP1's v2 bound at a cell's numerals `P`, at the event's parameters `a = 3/2, A = 5/2, B = 3,
M₁ = 7, K₂ = 10` and `ρ = 10⁻¹⁵`, `A_W = 6`, `n₀ = 2000`, `m₀ = 8`. -/
noncomputable def hp1CellLowerBound (P : HP1CellNumerals) (v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ : ℝ) : ℝ :=
  hp1LowerBoundV2 2000 8 P.vmin P.vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ (3 / 2) (5 / 2) 3 7 10
    (1 / 10 ^ 15) P.L P.t P.Λ 6 P.Klate P.σR2

/-- The weight of cell `i` in the window, `e^{-i/80} - e^{-(i+1)/80}`: the cell's Lebesgue
measure is `e^{-k}` times it. -/
noncomputable def hp1WindowWeight (i : ℕ) : ℝ :=
  Real.exp (-((i : ℝ) / 80)) - Real.exp (-(((i : ℝ) + 1) / 80))

lemma hp1WindowWeight_ge {i : ℕ} {lo hi : ℝ} (hlo : lo ≤ Real.exp (-((i : ℝ) / 80)))
    (hhi : Real.exp (-(((i : ℝ) + 1) / 80)) ≤ hi) : lo - hi ≤ hp1WindowWeight i := by
  unfold hp1WindowWeight
  linarith

end RMF
