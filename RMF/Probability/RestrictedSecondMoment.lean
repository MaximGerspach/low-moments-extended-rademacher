/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedSecondMoment.Assembly

/-!
# Key Proposition 5 at Harper's numeric data

Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654), Key Proposition 5:
uniformly for large `x`, `2/3 ≤ q ≤ 1` and `1 ≤ V ≤ (\log x)^{1/100}`,
`E(∫_𝔏 |F(1/2 + 4V/\log x + it)|² dt)²
≪ e^{2\min\{√(\log\log x), 1/(1-q)\}}(\log x/(V(1 + (1-q)√(\log\log x))))²`.

`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le` is this bound at
`θ = RMF.harperTheta B x`, `N = RMF.harperN B x`, `b = RMF.harperBarrierTop B V x` and
`σ = 4V/\log x`, assembled by `RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges` from
the four range bounds below (`crude_split`, `crude_top`, `far`, `middle`).  The proof runs through
`Drift.lean`, `Ranges.lean` and `Assembly.lean` in `RMF/Probability/RestrictedSecondMoment/`, then
this file.  The last section identifies this barrier grid with the one of
`RMF/Reduction/Numerator.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### The instantiation at Harper's numeric data

`RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges` takes the four range bounds as
hypotheses.  Producing them at `θ = harperTheta B x`, `N = harperN B x`,
`b = harperBarrierTop B V x` and `σ = 4V/\log x` means discharging the thresholds of the four
`…_harper_le` theorems.  These are the ones that are not immediate. -/

/-- **Proposition 7's size conditions hold eventually**: `4\log^{20} n ≤ n` and
`4\log^8 n ≤ n/18` for every `n ≥ n₁`, as the middle range needs at `n = b - r`.  The threshold is
absolute but enormous (the first condition first holds around `n = e^{90}`, so this asks for
`\log\log x ≳ e^{90}`); it is the most demanding largeness hypothesis in the chain. -/
lemma exists_forall_log_pow_le :
    ∃ n₁ : ℕ, 1 ≤ n₁ ∧ ∀ n : ℕ, n₁ ≤ n →
      4 * Real.log n ^ 20 ≤ (n : ℝ) ∧ 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) := by
  have h20 := (Real.isLittleO_pow_log_id_atTop (n := 20)).def (by norm_num : (0 : ℝ) < 1 / 4)
  have h8 := (Real.isLittleO_pow_log_id_atTop (n := 8)).def (by norm_num : (0 : ℝ) < 1 / 72)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp h20
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp h8
  refine ⟨max 1 (max ⌈X₁⌉₊ ⌈X₂⌉₊), le_max_left _ _, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hX1n : X₁ ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil X₁) ?_
    have hc : ⌈X₁⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hn
    exact_mod_cast hc
  have hX2n : X₂ ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil X₂) ?_
    have hc : ⌈X₂⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hn
    exact_mod_cast hc
  have e20 := hX₁ (n : ℝ) hX1n
  have e8 := hX₂ (n : ℝ) hX2n
  have habs20 : ‖Real.log (n : ℝ) ^ 20‖ = Real.log (n : ℝ) ^ 20 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habs8 : ‖Real.log (n : ℝ) ^ 8‖ = Real.log (n : ℝ) ^ 8 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have habsid : ‖id (n : ℝ)‖ = (n : ℝ) := by
    simp only [id_eq, Real.norm_eq_abs]
    exact abs_of_nonneg (by linarith)
  rw [habs20, habsid] at e20
  rw [habs8, habsid] at e8
  exact ⟨by linarith, by linarith⟩

/-- **The split index sits below `\log(1/τ) - θ`, so `x_{j+2}` stays under `e²/τ`.**  This is the
middle range's `\exp(j+2+θ) ≤ 1/σ` reduced to a statement about `τ` alone: the floor is at most
what it truncates, so `j + θ ≤ \log(1/τ)` and two blocks cost a factor `e²`.

What the caller then needs is `e²/τ ≤ 1/σ`, which on the middle range is `τ ≥ σe²` — and there
`τ > (\log x)^{-1/3}` against `σe² = 4Ve²/\log x`, so it holds with room to spare. -/
lemma exp_splitIndex_add_two_add_theta_le {θ : ℝ} {m : ℕ} {t : ℝ} (hθ : 0 ≤ θ)
    (h1 : 1 ≤ splitIndex θ m t) :
    Real.exp ((splitIndex θ m t : ℝ) + 2 + θ) ≤ Real.exp 2 / |t| := by
  have hfl : 1 ≤ ⌊Real.log (1 / |t|) - θ⌋₊ := le_trans h1 (min_le_right _ _)
  have ht : (0 : ℝ) < |t| := by
    rcases (abs_nonneg t).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hfl
      simp only [div_zero, Real.log_zero, zero_sub] at hfl
      rw [Nat.floor_eq_zero.2 (by linarith : -θ < 1)] at hfl
      omega
  have hnn : (0 : ℝ) ≤ Real.log (1 / |t|) - θ := by
    by_contra hc
    have hz : ⌊Real.log (1 / |t|) - θ⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith [not_le.1 hc])
    omega
  have hle : ((splitIndex θ m t : ℕ) : ℝ) ≤ Real.log (1 / |t|) - θ := by
    refine le_trans ?_ (Nat.floor_le hnn)
    exact_mod_cast min_le_right m ⌊Real.log (1 / |t|) - θ⌋₊
  calc Real.exp ((splitIndex θ m t : ℝ) + 2 + θ)
      ≤ Real.exp (Real.log (1 / |t|) + 2) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp 2 / |t| := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
        field_simp

/-- **How far the shift must run to clear Proposition 7's level threshold**:
`⌈max(1, R₁)/(1 + B)⌉` with `R₁ = RMF.result1Threshold (1/18) (9/2)` and `B = RMF.blockSlope 125`.
Past this many blocks `RMF.shiftLevel a r RMF.harperHf ≥ (1+B)r` clears `R₁` for every `a ≥ 0`
(`RMF.result1Threshold_le_shiftLevel`), while Harper's `a = min{√Λ, 1/(1-q)}` is `3` at `q = 2/3`
and cannot reach `R₁ ≥ 8000`. -/
noncomputable def harperShiftFloor : ℕ :=
  ⌈max 1 (result1Threshold (1 / 18) (9 / 2)) / (1 + blockSlope 125)⌉₊

/-- **`RMF.harperShiftFloor` at a threshold `R`** for Proposition 7's level, `⌈max(1, R)/(1 + B)⌉`;
Proposition 7 itself needs only `R ≥ 1000` (`RMF.proposition7_upper_of_threshold`). -/
noncomputable def harperShiftFloorOf (R : ℝ) : ℕ :=
  ⌈max 1 R / (1 + blockSlope 125)⌉₊

lemma le_shiftLevel_of_harperShiftFloorOf {R a : ℝ} (ha : 0 ≤ a) {r : ℕ}
    (hr : harperShiftFloorOf R ≤ r) :
    max 1 R ≤ shiftLevel a r harperHf := by
  have hs : (0 : ℝ) < blockSlope 125 := blockSlope_pos 125
  have hden : (0 : ℝ) < 1 + blockSlope 125 := by linarith
  have hceil : max 1 R / (1 + blockSlope 125) ≤ (r : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hr
  rw [div_le_iff₀ hden] at hceil
  have h1 : (0 : ℝ) ≤ |harperHf r| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ 10 * Real.log (1 + (r : ℝ)) := by
    have hr1 : (1 : ℝ) ≤ 1 + (r : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) r
      linarith
    have := Real.log_nonneg hr1
    linarith
  rw [shiftLevel]
  nlinarith

lemma result1Threshold_le_shiftLevel {a : ℝ} (ha : 0 ≤ a) {r : ℕ} (hr : harperShiftFloor ≤ r) :
    max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r harperHf :=
  le_shiftLevel_of_harperShiftFloorOf (R := result1Threshold (1 / 18) (9 / 2)) ha hr

/-- **The middle range's shift**, `max{j₀ + 2 + c, r₀}` with `j₀ = RMF.splitIndex θ b t` and
`r₀ = RMF.harperShiftFloor`.  From below `r` must clear the split (`j₀ + 2 ≤ r`), Proposition 7's
window `Tsh ≤ τe^{r+θ}` (at `c = ⌈\log Tsh⌉`, `RMF.le_mul_exp_harperShift`) and the level `r₀`;
from above, the shear budget `r ≤ 2\log(2/τ) + 1` and the count `Λ ≤ 4(b - r)`.  A larger `θ`
does not clear the window, since `r + θ ≈ \log(1/τ)` whatever `θ` is; the `c` extra blocks do. -/
noncomputable def harperShift (θ : ℝ) (b : ℕ) (t : ℝ) (c : ℕ) : ℕ :=
  max (splitIndex θ b t + 2 + c) harperShiftFloor

/-- **`RMF.harperShift` at a threshold `R`**, with the floor `RMF.harperShiftFloorOf R`. -/
noncomputable def harperShiftOf (R θ : ℝ) (b : ℕ) (t : ℝ) (c : ℕ) : ℕ :=
  max (splitIndex θ b t + 2 + c) (harperShiftFloorOf R)

lemma splitIndex_add_two_le_harperShiftOf (R θ : ℝ) (b : ℕ) (t : ℝ) (c : ℕ) :
    splitIndex θ b t + 2 ≤ harperShiftOf R θ b t c :=
  le_trans (by omega) (le_max_left _ _)

lemma splitIndex_add_two_le_harperShift (θ : ℝ) (b : ℕ) (t : ℝ) (c : ℕ) :
    splitIndex θ b t + 2 ≤ harperShift θ b t c :=
  splitIndex_add_two_le_harperShiftOf _ θ b t c

lemma harperShiftFloorOf_le_harperShiftOf (R θ : ℝ) (b : ℕ) (t : ℝ) (c : ℕ) :
    (harperShiftFloorOf R) ≤ harperShiftOf R θ b t c := le_max_right _ _

lemma harperShiftFloor_le_harperShift (θ : ℝ) (b : ℕ) (t : ℝ) (c : ℕ) :
    harperShiftFloor ≤ harperShift θ b t c :=
  harperShiftFloorOf_le_harperShiftOf _ θ b t c

/-- **The shift is at most `2\log(2/τ)+1`** — the shear budget, which is what stops `r` from
simply being taken large.  Both arms clear it for the same reason, that `θ` is large: the split
arm because `j + 2 + c ≤ \log(1/τ) - θ + 2 + c` and `c + 1 ≤ θ`, the floor arm because on the
middle range `\log(2/τ) ≥ 2θ`. -/
lemma harperShiftOf_le_two_mul_log {R θ : ℝ} {b : ℕ} {t : ℝ} {c : ℕ}
    (hτ0 : 0 < |t|) (hτ1 : |t| ≤ 1) (hc : (c : ℝ) + 1 ≤ θ)
    (hfl : ((harperShiftFloorOf R) : ℝ) ≤ 4 * θ)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t|)) :
    ((harperShiftOf R θ b t c : ℕ) : ℝ) ≤ 2 * Real.log (2 / |t|) + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : (1 : ℝ) ≤ 1 / |t| := by rw [le_div_iff₀ hτ0]; linarith
  have hlogt : (0 : ℝ) ≤ Real.log (1 / |t|) := Real.log_nonneg hinv
  have hlog2t : Real.log (2 / |t|) = Real.log 2 + Real.log (1 / |t|) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hτ0), Real.log_div one_ne_zero (ne_of_gt hτ0),
      Real.log_one]
    ring
  have hy : (0 : ℝ) ≤ Real.log (1 / |t|) - θ := by linarith
  have hsplitR : ((splitIndex θ b t : ℕ) : ℝ) ≤ Real.log (1 / |t|) - θ := by
    refine le_trans ?_ (Nat.floor_le hy)
    exact_mod_cast min_le_right b ⌊Real.log (1 / |t|) - θ⌋₊
  rw [harperShiftOf]
  rcases max_cases (splitIndex θ b t + 2 + c) (harperShiftFloorOf R) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]
    push_cast
    rw [hlog2t]
    linarith
  · rw [he, hlog2t]
    linarith

lemma harperShift_le_two_mul_log {θ : ℝ} {b : ℕ} {t : ℝ} {c : ℕ}
    (hτ0 : 0 < |t|) (hτ1 : |t| ≤ 1) (hc : (c : ℝ) + 1 ≤ θ)
    (hfl : (harperShiftFloor : ℝ) ≤ 4 * θ)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t|)) :
    ((harperShift θ b t c : ℕ) : ℝ) ≤ 2 * Real.log (2 / |t|) + 1 :=
  harperShiftOf_le_two_mul_log (R := result1Threshold (1 / 18) (9 / 2)) hτ0 hτ1 hc hfl
    hsmall

/-- **The shift clears Proposition 7's window.**  `Tsh ≤ τe^{r+θ}` at `c = ⌈\log Tsh⌉`: the floor
loses less than `1`, the two spare blocks pay that back, and the `c` further blocks are exactly
`\log Tsh`.  The `e` left over is slack.

`hfloor` is what makes the split index the floor rather than the cap `b`; without it the shift
could be pinned at `b` and the estimate would say nothing. -/
lemma le_mul_exp_harperShiftOf {R θ : ℝ} {b : ℕ} {t Tsh : ℝ} (hTsh : 0 < Tsh) (hτ0 : 0 < |t|)
    (hfloor : ⌊Real.log (1 / |t|) - θ⌋₊ ≤ b) :
    Tsh ≤ |t| * Real.exp (((harperShiftOf R θ b t ⌈Real.log Tsh⌉₊ : ℕ) : ℝ) + θ) := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  set c : ℕ := ⌈Real.log Tsh⌉₊ with hcdef
  have hsplit : splitIndex θ b t = ⌊Real.log (1 / |t|) - θ⌋₊ := by
    rw [splitIndex, min_eq_right hfloor]
  have hlt := Nat.lt_floor_add_one (Real.log (1 / |t|) - θ)
  have h1 : splitIndex θ b t + 2 + c ≤ harperShiftOf R θ b t c := le_max_left _ _
  have h1R : ((splitIndex θ b t : ℕ) : ℝ) + 2 + (c : ℝ) ≤ ((harperShiftOf R θ b t c : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast at this
    linarith
  rw [hsplit] at h1R
  have hclog : Real.log Tsh ≤ (c : ℝ) := Nat.le_ceil _
  have hexp : Real.log (1 / |t|) + 1 + Real.log Tsh
      ≤ ((harperShiftOf R θ b t c : ℕ) : ℝ) + θ := by linarith
  have hkey : |t| * Real.exp (Real.log (1 / |t|) + 1 + Real.log Tsh) = Real.exp 1 * Tsh := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hTsh]
    field_simp
  calc Tsh ≤ Real.exp 1 * Tsh := by nlinarith
    _ = |t| * Real.exp (Real.log (1 / |t|) + 1 + Real.log Tsh) := hkey.symm
    _ ≤ |t| * Real.exp (((harperShiftOf R θ b t c : ℕ) : ℝ) + θ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hτ0.le

lemma le_mul_exp_harperShift {θ : ℝ} {b : ℕ} {t Tsh : ℝ} (hTsh : 0 < Tsh) (hτ0 : 0 < |t|)
    (hfloor : ⌊Real.log (1 / |t|) - θ⌋₊ ≤ b) :
    Tsh ≤ |t| * Real.exp (((harperShift θ b t ⌈Real.log Tsh⌉₊ : ℕ) : ℝ) + θ) :=
  le_mul_exp_harperShiftOf (R := result1Threshold (1 / 18) (9 / 2)) hTsh hτ0 hfloor

/-- **The middle range's envelope, from the block offset alone**: `RMF.boxEnvelope_pair_le` with
`m` implicit, since the middle range quantifies over every block below the shifted top.  It needs
no threshold beyond `RMF.blockOffsetThreshold ≤ ϑ`, in particular none on `m`. -/
lemma envelope_harper {ϑ : ℝ} {m : ℕ} (hϑ : blockOffsetThreshold ≤ ϑ) :
    boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
        + blockWindow m + blockWindow m + 13
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) :=
  boxEnvelope_pair_le hϑ m

/-- **The barrier top, in the form the middle range's thresholds are compared against.**
`b ≥ Λ - B - \log V - 6`: three from `RMF.harperN_ge` and `\log V + 3` from the drop. -/
lemma barrierTop_ge_data {B : ℕ} {V x : ℝ} (hV : 1 ≤ V)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x) :
    Real.log (Real.log x) - (B : ℝ) - Real.log V - 6 ≤ ((harperBarrierTop B V x : ℕ) : ℝ) := by
  have h1 := harperN_ge (B := B) (x := x) hx
  have h2 := harperBarrierTop_ge (B := B) (V := V) (x := x) hV hle
  linarith

/-- **`\log(2/τ) ≤ 2b`**, the middle range's `hmb`, on the outer range `\log(1/τ) ≤ Λ/3` and at the
threshold `(5/3)Λ ≥ 2B + 2\log V + 13`. -/
lemma log_two_div_le_two_mul_barrierTop {B : ℕ} {V x t : ℝ} (hV : 1 ≤ V) (hτ0 : 0 < |t|)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hτ : Real.log (1 / |t|) ≤ Real.log (Real.log x) / 3)
    (hΛ : 2 * (B : ℝ) + 2 * Real.log V + 13 ≤ 5 / 3 * Real.log (Real.log x)) :
    Real.log (2 / |t|) ≤ 2 * ((harperBarrierTop B V x : ℕ) : ℝ) := by
  have hb := barrierTop_ge_data hV hx hle
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [log_two_div_eq hτ0]
  linarith

/-- **The shifted block count, `r + n₂ ≤ b`**, which discharges `4 ≤ b - r`, the two size
conditions of `RMF.exists_forall_log_pow_le` and the count `Λ ≤ 4(b - r)` at once, with `n₂` the
largest of them.  The split arm of the shift costs `Λ/3` against a top of `Λ - B - \log V - 6`;
the floor arm costs the absolute `RMF.harperShiftFloor`.  Since Key Proposition 5 has
`V ≤ (\log x)^{1/100}`, `\log V ≤ Λ/100` and the threshold stays satisfiable. -/
lemma harperShiftOf_add_le_barrierTop {R : ℝ} {B : ℕ} {V x t : ℝ} {c n₂ : ℕ} (hV : 1 ≤ V)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hτ : Real.log (1 / |t|) ≤ Real.log (Real.log x) / 3)
    (hΛ : (B : ℝ) + Real.log V + 7 + ((harperShiftFloorOf R) : ℝ) + (c : ℝ) + (n₂ : ℝ)
        ≤ 2 / 3 * Real.log (Real.log x)) :
    harperShiftOf R (harperTheta B x) (harperBarrierTop B V x) t c + n₂
      ≤ harperBarrierTop B V x := by
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B V x with hbdef
  have hB : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hSF : (0 : ℝ) ≤ ((harperShiftFloorOf R) : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hn0 : (0 : ℝ) ≤ (n₂ : ℝ) := Nat.cast_nonneg n₂
  have hΛ10 : (10 : ℝ) ≤ Λ := by linarith
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hθge : (B : ℝ) + 1 ≤ θ := le_harperTheta hΛ0
  have hbge : Λ - (B : ℝ) - Real.log V - 6 ≤ (b : ℝ) := barrierTop_ge_data hV hx hle
  -- the split arm is at most `\max\{0, Λ/3 - B - 1\}`
  have hsplit : ((splitIndex θ b t : ℕ) : ℝ) ≤ max 0 (Λ / 3 - (B : ℝ) - 1) := by
    have hfl : ((⌊Real.log (1 / |t|) - θ⌋₊ : ℕ) : ℝ) ≤ max 0 (Real.log (1 / |t|) - θ) := by
      rcases le_or_gt 0 (Real.log (1 / |t|) - θ) with h | h
      · exact le_trans (Nat.floor_le h) (le_max_right _ _)
      · rw [Nat.floor_eq_zero.2 (by linarith)]
        simp
    have hmono : max 0 (Real.log (1 / |t|) - θ) ≤ max 0 (Λ / 3 - (B : ℝ) - 1) :=
      max_le_max le_rfl (by linarith)
    refine le_trans ?_ (le_trans hfl hmono)
    exact_mod_cast min_le_right b ⌊Real.log (1 / |t|) - θ⌋₊
  -- both arms, in the reals
  have hkey : ((harperShiftOf R θ b t c : ℕ) : ℝ) + (n₂ : ℝ) ≤ (b : ℝ) := by
    rw [harperShiftOf]
    rcases max_cases (splitIndex θ b t + 2 + c) (harperShiftFloorOf R) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      push_cast
      rcases le_or_gt (Λ / 3 - (B : ℝ) - 1) 0 with h | h
      · rw [max_eq_left h] at hsplit
        linarith
      · rw [max_eq_right h.le] at hsplit
        linarith
    · rw [he]
      linarith
  exact_mod_cast hkey

lemma harperShift_add_le_barrierTop {B : ℕ} {V x t : ℝ} {c n₂ : ℕ} (hV : 1 ≤ V)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hτ : Real.log (1 / |t|) ≤ Real.log (Real.log x) / 3)
    (hΛ : (B : ℝ) + Real.log V + 7 + (harperShiftFloor : ℝ) + (c : ℝ) + (n₂ : ℝ)
        ≤ 2 / 3 * Real.log (Real.log x)) :
    harperShift (harperTheta B x) (harperBarrierTop B V x) t c + n₂
      ≤ harperBarrierTop B V x :=
  harperShiftOf_add_le_barrierTop (R := result1Threshold (1 / 18) (9 / 2)) hV hx hle hτ hΛ

/-- **The split index, with the two spare blocks, stays under the barrier top**:
`⌊\log(1/τ) - θ⌋ + 2 ≤ b` on the outer range, at the threshold `(2/3)Λ ≥ B + \log V + 8`; this is
what the crude and middle ranges ask for (`RMF.splitIndex θ b τ + 2 ≤ b`). -/
lemma floor_log_one_div_sub_theta_add_two_le_barrierTop {B : ℕ} {V x t : ℝ} (hV : 1 ≤ V)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hτ : Real.log (1 / |t|) ≤ Real.log (Real.log x) / 3)
    (hΛ : (B : ℝ) + Real.log V + 8 ≤ 2 / 3 * Real.log (Real.log x)) :
    ⌊Real.log (1 / |t|) - harperTheta B x⌋₊ + 2 ≤ harperBarrierTop B V x := by
  have hB : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hθ : (B : ℝ) + 1 ≤ harperTheta B x := le_harperTheta hΛ0
  have hb := barrierTop_ge_data hV hx hle
  have hfl : ((⌊Real.log (1 / |t|) - harperTheta B x⌋₊ : ℕ) : ℝ)
      ≤ max 0 (Real.log (1 / |t|) - harperTheta B x) := by
    rcases le_or_gt 0 (Real.log (1 / |t|) - harperTheta B x) with h | h
    · exact le_trans (Nat.floor_le h) (le_max_right _ _)
    · rw [Nat.floor_eq_zero.2 (by linarith)]
      simp
  have hkey : ((⌊Real.log (1 / |t|) - harperTheta B x⌋₊ : ℕ) : ℝ) + 2
      ≤ ((harperBarrierTop B V x : ℕ) : ℝ) := by
    rcases le_or_gt (Real.log (1 / |t|) - harperTheta B x) 0 with h | h
    · rw [max_eq_left h] at hfl
      linarith
    · rw [max_eq_right h.le] at hfl
      linarith
  exact_mod_cast hkey

/-- **`1/τ ≤ L_c/e²` is `e²/τ ≤ 1/σ`** (`L_c = 1/σ`), the form
`RMF.exp_splitIndex_add_two_add_theta_le` hands to the middle range's `hNM`.  On the middle range
it follows from `\log(1/τ) ≤ Λ/3` once `\log(4V) + 2 ≤ (2/3)Λ`
(`RMF.le_one_div_sigma_div_exp_two`); the crude range uses `RMF.exp_splitIndex_add_two_le_of_le`
instead. -/
lemma exp_two_div_le_of_le_div {σ τ : ℝ} (h : 1 / τ ≤ 1 / σ / Real.exp 2) :
    Real.exp 2 / τ ≤ 1 / σ := by
  rw [le_div_iff₀ (Real.exp_pos 2)] at h
  calc Real.exp 2 / τ = 1 / τ * Real.exp 2 := by ring
    _ ≤ 1 / σ := h

/-! ### The crude range at Harper's numeric data

`θ = harperTheta B x`, `N = harperN B x`, `b = harperBarrierTop B V x`, `σ = 4V/\log x`.  After the
discharges above, the regimes' hypotheses are about the application: `B` large, `x` large, and
where `τ` sits. -/

/-- **The first crude regime's boundary.**  `\log(1/τ) ≤ b + θ - 2` keeps the split index two
blocks below the barrier top, and it is what makes `RMF.splitIndex θ b τ` the floor rather than
the cap. -/
lemma floor_log_one_div_sub_theta_add_two_le_of_le {θ : ℝ} {b : ℕ} {t : ℝ} (hb2 : 2 ≤ b)
    (hreg : Real.log (1 / |t|) ≤ (b : ℝ) + θ - 2) :
    ⌊Real.log (1 / |t|) - θ⌋₊ + 2 ≤ b := by
  have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
  have hfl : ((⌊Real.log (1 / |t|) - θ⌋₊ : ℕ) : ℝ) ≤ max 0 (Real.log (1 / |t|) - θ) := by
    rcases le_or_gt 0 (Real.log (1 / |t|) - θ) with h | h
    · exact le_trans (Nat.floor_le h) (le_max_right _ _)
    · rw [Nat.floor_eq_zero.2 (by linarith)]
      simp
  have hkey : ((⌊Real.log (1 / |t|) - θ⌋₊ : ℕ) : ℝ) + 2 ≤ (b : ℝ) := by
    rcases le_or_gt (Real.log (1 / |t|) - θ) 0 with h | h
    · rw [max_eq_left h] at hfl
      linarith
    · rw [max_eq_right h.le] at hfl
      linarith
  exact_mod_cast hkey

/-- **`hNM` in the first crude regime, from the boundary and the drop.**  Once the split is two
blocks below the top, `\exp(j+2+θ) ≤ \exp(b+θ) = \log x_b`, and the drop already gives
`σ\log x_b ≤ 4/e³ < 1`.  So one condition on `τ` discharges both of the regime's `τ`-hypotheses. -/
lemma exp_splitIndex_add_two_le_of_le {θ σ : ℝ} {b : ℕ} {t : ℝ} (hσ0 : 0 < σ)
    (hsp : splitIndex θ b t + 2 ≤ b)
    (hdrop : σ * Real.log (blockScale θ b) ≤ 1) :
    Real.exp ((splitIndex θ b t : ℝ) + 2 + θ) ≤ 1 / σ := by
  have hspR : ((splitIndex θ b t : ℕ) : ℝ) + 2 ≤ (b : ℝ) := by exact_mod_cast hsp
  have h1 : Real.exp ((splitIndex θ b t : ℝ) + 2 + θ) ≤ Real.exp ((b : ℝ) + θ) :=
    Real.exp_le_exp.2 (by linarith)
  rw [← log_blockScale θ b] at h1
  refine le_trans h1 ?_
  rw [le_div_iff₀ hσ0, mul_comm]
  exact hdrop

/-- **The crude range's first regime, at Harper's numeric data**, on `\log(1/τ) ≤ b + θ - 2`, which
discharges both of the regime's `τ`-hypotheses.  The boundary `1/τ ≤ L_c/e²` would not do: at
`\log V = 0` it allows `\log(1/τ)` up to `Λ - \log 4 - 2`, above `b + θ = Λ - ⌊\log V⌋ - 4` by
`2 - \log 4`, and a band of `τ` would belong to neither regime. -/
theorem exists_setIntegral_normSq_pair_crude_split_harper_data_le
    {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (B : ℕ) (V x σ a t u : ℝ),
      124 ≤ B → 1 ≤ V → 1 < x →
      (B : ℝ) + 2 ≤ Real.log (Real.log x) →
      ⌊Real.log V⌋₊ + 3 ≤ harperN B x →
      0 < σ → σ ≤ 1 / 2 → 1 ≤ σ * Real.log x → σ * Real.log x ≤ 4 * V →
      0 < |t - u| → |t - u| ≤ 1 →
      Real.log 2 + 2 * harperTheta B x + 2 ≤ Real.log (1 / |t - u|) →
      Real.log (1 / |t - u|)
        ≤ ((harperBarrierTop B V x : ℕ) : ℝ) + harperTheta B x - 2 →
      Real.log 2 + harperTheta B x - 2 ≤ ((harperBarrierTop B V x : ℕ) : ℝ) →
      (B : ℝ) + Real.log V + 8 ≤ 2 / 3 * Real.log (Real.log x) →
      (∫ ω in barrierEventPair (blockPair (harperTheta B x) (shiftLine σ t)
          (shiftLine σ u) Y) (harperBarrierTop B V x)
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - harperTheta B x)) ^ 2 * KQ * CP
            * bottomConst ((B : ℝ) + 2) / σ ^ 2
            * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 4)) := by
  obtain ⟨KQ, CP, hKQ, hCP, hsrc⟩ :=
    exists_setIntegral_normSq_pair_crude_split_harper_le (Ω' := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY B V x σ a t u hB hV hx1 hx hle hσ0 hσhalf hσx hσ4 hτ0 hτ1 hsmall hreg hbθ hΛ1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hθ125 : (125 : ℝ) ≤ harperTheta B x := harperTheta_ge hB hΛ0
  have hθ0 : (0 : ℝ) ≤ harperTheta B x := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `b ≥ 2`, from the boundary condition and `θ ≥ 125`
  have hb2R : (2 : ℝ) ≤ ((harperBarrierTop B V x : ℕ) : ℝ) := by linarith
  have hb2 : 2 ≤ harperBarrierTop B V x := by exact_mod_cast hb2R
  -- the split index, and the two spare blocks
  have hsp : ⌊Real.log (1 / |t - u|) - harperTheta B x⌋₊ + 2 ≤ harperBarrierTop B V x :=
    floor_log_one_div_sub_theta_add_two_le_of_le hb2 hreg
  have hfloor : ⌊Real.log (1 / |t - u|) - harperTheta B x⌋₊ ≤ harperBarrierTop B V x := by
    omega
  have hsplit : splitIndex (harperTheta B x) (harperBarrierTop B V x) (t - u)
      = ⌊Real.log (1 / |t - u|) - harperTheta B x⌋₊ := by
    rw [splitIndex, min_eq_right hfloor]
  have hb1 : 1 ≤ harperBarrierTop B V x := by omega
  have h1split : 1 ≤ splitIndex (harperTheta B x) (harperBarrierTop B V x) (t - u) :=
    one_le_splitIndex hθ0 hb1 hsmall
  have hspb : splitIndex (harperTheta B x) (harperBarrierTop B V x) (t - u) + 2
      ≤ harperBarrierTop B V x := by rw [hsplit]; exact hsp
  -- `\log(2/τ) ≤ 2b`, from the boundary and `\log 2 + θ - 2 ≤ b`
  have hmb : Real.log (2 / |t - u|) ≤ 2 * ((harperBarrierTop B V x : ℕ) : ℝ) := by
    rw [log_two_div_eq hτ0]
    linarith
  -- the drop, which is what `hNM` reads
  have hdrop : σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) ≤ 1 := by
    have he3 : (4 : ℝ) ≤ Real.exp 3 := by
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hpow : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
      rw [h3]
      linarith [hpow, (by norm_num : (4 : ℝ) ≤ (2.7 : ℝ) ^ 3)]
    refine le_trans (sigma_mul_log_blockScale_barrierTop_le hV hx1 hx hle hσ4) ?_
    rw [div_le_one (Real.exp_pos 3)]
    exact he3
  exact hsrc Y ν hY (harperTheta B x) σ a ((B : ℝ) + 2) t u (harperN B x)
    (harperBarrierTop B V x)
    hθ125 (harperTheta_lt B x).le hσ0 hσhalf (harperBarrierTop_le B V x)
    hspb h1split hfloor hτ0 hτ1 hsmall hmb
    (exp_splitIndex_add_two_le_of_le hσ0 hspb hdrop)
    (one_div_sigma_le_log_blockScale_harperN_succ hx1 hx hσ0 hσx)

/-- **The tilt's truncation scale**, `M = ⌈e^{1/(2σ)}⌉`: the least `M` with `1 ≤ 2σ\log M`, the
hypothesis of `RMF.exists_integral_normSq_pairIco_split_le`, whose bound increases with `M`.  At
Harper's data `\log M ≈ \log x/(8V)` and `\log M/\log x_b ∈ [e³/8, e⁴/8]`: the `V` cancels
between the tilt and the drop. -/
noncomputable def harperTruncation (σ : ℝ) : ℕ := ⌈Real.exp (1 / (2 * σ))⌉₊

/-- `400 ≤ ⌊x_b⌋`, which at `θ ≥ 6` is not close: `x_b = e^{e^{b+θ}} ≥ e^7`. -/
lemma four_hundred_le_floor_blockScale {θ : ℝ} (hθ : 6 ≤ θ) (b : ℕ) :
    (400 : ℝ) ≤ ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have h1 : (7 : ℝ) ≤ Real.exp ((b : ℝ) + θ) := by
    linarith [Real.add_one_le_exp ((b : ℝ) + θ)]
  have he7 : (400 : ℝ) ≤ Real.exp 7 := by
    have h9 : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he1.le 7
    rw [h9]
    linarith [hpow, (by norm_num : (400 : ℝ) ≤ (2.7 : ℝ) ^ 7)]
  have h2 : (400 : ℝ) ≤ blockScale θ b := by
    rw [blockScale]
    exact le_trans he7 (Real.exp_le_exp.2 h1)
  have h3 : (400 : ℕ) ≤ ⌊blockScale θ b⌋₊ := Nat.le_floor (by push_cast; linarith)
  exact_mod_cast h3

/-- **The truncation sits above the barrier top.**  `σ\log x_b ≤ 4/e³ < 1/2` says exactly
`\log x_b ≤ 1/(2σ)`, so `x_b ≤ e^{1/(2σ)} ≤ M`. -/
lemma floor_blockScale_barrierTop_le_harperTruncation {B : ℕ} {V x σ : ℝ} (hV : 1 ≤ V)
    (hx1 : 1 < x) (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x) (hσ0 : 0 < σ)
    (hσ : σ * Real.log x ≤ 4 * V) :
    ⌊blockScale (harperTheta B x) (harperBarrierTop B V x)⌋₊ ≤ harperTruncation σ := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he3 : (8 : ℝ) ≤ Real.exp 3 := by
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
    rw [h3]
    linarith [hpow, (by norm_num : (8 : ℝ) ≤ (2.7 : ℝ) ^ 3)]
  have hkey := sigma_mul_log_blockScale_barrierTop_le hV hx1 hx hle hσ
  have hhalf : σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) ≤ 1 / 2 := by
    refine le_trans hkey ?_
    rw [div_le_div_iff₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hlogle : Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x))
      ≤ 1 / (2 * σ) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hble : blockScale (harperTheta B x) (harperBarrierTop B V x)
      ≤ Real.exp (1 / (2 * σ)) := by
    have hpos := blockScale_pos (harperTheta B x) (harperBarrierTop B V x)
    calc blockScale (harperTheta B x) (harperBarrierTop B V x)
        = Real.exp (Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x))) :=
          (Real.exp_log hpos).symm
      _ ≤ Real.exp (1 / (2 * σ)) := Real.exp_le_exp.2 hlogle
  exact le_trans (Nat.floor_le_floor hble) (Nat.floor_le_ceil _)

/-- **The truncation sits below the product's top.**  `1 ≤ σ\log x` gives `1/(2σ) ≤ (\log x)/2`, so
`M ≤ √x + 1 ≤ x`. -/
lemma harperTruncation_le_floor_blockScale_harperN_succ {B : ℕ} {x σ : ℝ} (hx1 : 1 < x)
    (hx3 : 3 ≤ x) (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x)) (hσ0 : 0 < σ)
    (hσx : 1 ≤ σ * Real.log x) :
    harperTruncation σ ≤ ⌊blockScale (harperTheta B x) (harperN B x + 1)⌋₊ := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hhalf : 1 / (2 * σ) ≤ Real.log x / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
    linarith
  set s : ℝ := Real.exp (Real.log x / 2) with hsdef
  have hs0 : 0 < s := Real.exp_pos _
  have hssq : s ^ 2 = x := by
    rw [hsdef, ← Real.exp_nat_mul]
    rw [show (2 : ℕ) * (Real.log x / 2) = Real.log x by push_cast; ring]
    exact Real.exp_log (by linarith)
  have hs2 : 1 ≤ s := by nlinarith
  have hsle : s ≤ x - 1 := by nlinarith
  have hMle : Real.exp (1 / (2 * σ)) ≤ x - 1 :=
    le_trans (Real.exp_le_exp.2 hhalf) hsle
  have hfl : x - 1 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one x]
  have htop : blockScale (harperTheta B x) (harperN B x + 1) = x :=
    blockScale_harperN_succ hx1 hx
  rw [harperTruncation, htop]
  exact Nat.ceil_le.2 (le_trans hMle hfl)

/-- `1 ≤ 2σ\log M` at `M = ⌈e^{1/(2σ)}⌉` — an equality but for the ceiling. -/
lemma one_le_two_mul_sigma_mul_log_harperTruncation {σ : ℝ} (hσ0 : 0 < σ) :
    1 ≤ 2 * σ * Real.log ((harperTruncation σ : ℕ) : ℝ) := by
  have hexp : Real.exp (1 / (2 * σ)) ≤ ((harperTruncation σ : ℕ) : ℝ) := Nat.le_ceil _
  have hlog : 1 / (2 * σ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ) := by
    rw [← Real.log_exp (1 / (2 * σ))]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have h2σ : (0 : ℝ) < 2 * σ := by linarith
  have hid : 2 * σ * (1 / (2 * σ)) = 1 := by field_simp
  linarith [mul_le_mul_of_nonneg_left hlog h2σ.le, hid]

/-- **The crude range's second regime, at Harper's numeric data**, in the `C·L_b³/n_b⁴` shape that
`RMF.crude_top_le_min` consumes (by `RMF.exp_barrier_top_sq_eq`).  With no hypothesis on `τ`, this
regime covers the band `L_c/e² ≤ 1/τ` the first cannot reach.  The ratio `\log M/\log⌊x_b⌋` stays
in the bound; it does not depend on `t` or `u`, and `RMF.log_harperTruncation_div_log_floor_le`
bounds it by `e⁴`. -/
theorem exists_setIntegral_normSq_pair_crude_top_harper_data_le {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (B : ℕ) (V x σ a t u : ℝ),
      124 ≤ B → 1 ≤ V → 1 < x → 3 ≤ x →
      (B : ℝ) + 2 ≤ Real.log (Real.log x) →
      ⌊Real.log V⌋₊ + 3 ≤ harperN B x →
      1 ≤ harperBarrierTop B V x →
      0 < σ → σ * Real.log x ≤ 4 * V → 1 ≤ σ * Real.log x →
      (∫ ω in barrierEventPair (blockPair (harperTheta B x) (shiftLine σ t)
          (shiftLine σ u) Y) (harperBarrierTop B V x)
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Real.exp (2 * a) * Real.exp (-(2 * harperTheta B x))
            * (KQ * (Real.log ((harperTruncation σ : ℕ) : ℝ)
                / Real.log ((⌊blockScale (harperTheta B x) (harperBarrierTop B V x)⌋₊ : ℕ) : ℝ))
                  ^ 4)
            * CP * bottomConst ((B : ℝ) + 2)
            * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) ^ 3
            / ((harperBarrierTop B V x : ℕ) : ℝ) ^ 4 := by
  obtain ⟨KQ, CP, hKQ, hCP, hsrc⟩ :=
    exists_setIntegral_normSq_pair_crude_top_harper_le (Ω' := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY B V x σ a t u hB hV hx1 hx3 hx hle hb1 hσ0 hσ hσx
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hθ125 : (125 : ℝ) ≤ harperTheta B x := harperTheta_ge hB hΛ0
  have hθ0 : (0 : ℝ) ≤ harperTheta B x := by linarith
  have hsrc' := hsrc Y ν hY (harperTheta B x) σ a ((B : ℝ) + 2) t u (harperN B x)
    (harperBarrierTop B V x) (harperTruncation σ)
    hθ0 (harperTheta_lt B x).le hσ0.le hb1 (harperBarrierTop_le B V x)
    (four_hundred_le_floor_blockScale (by linarith) _)
    (floor_blockScale_barrierTop_le_harperTruncation hV hx1 hx hle hσ0 hσ)
    (harperTruncation_le_floor_blockScale_harperN_succ hx1 hx3 hx hσ0 hσx)
    (one_le_two_mul_sigma_mul_log_harperTruncation hσ0)
  refine le_trans hsrc' (le_of_eq ?_)
  rw [exp_barrier_top_sq_eq a (harperTheta B x) hb1]
  ring

/-- **The block count at the barrier top.**  `RMF.harper_block_count` is stated at `N`; the far
range needs it at `b`, which gives up a further `\log V + 3`.  So the threshold moves from
`Λ ≥ 12S` to `Λ ≥ 3S + 3\log V + 21`, and `\log V ≤ Λ/100` keeps that satisfiable at Harper's
largest `V`. -/
lemma harper_block_count_barrierTop {B : ℕ} {V x τ : ℝ} (hV : 1 ≤ V) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hτL : Real.log (1 / τ) ≤ Real.log (Real.log x) / 3)
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hΛ : 12 * harperSlack B V ≤ Real.log (Real.log x))
    (hΛ2 : 3 * harperSlack B V + 3 * Real.log V + 21 ≤ Real.log (Real.log x)) :
    harperR τ + harperD V + 4 ≤ harperBarrierTop B V x
      ∧ Real.log (Real.log x) / 3 - harperSlack B V - Real.log V - 3
          ≤ ((harperBarrierTop B V x : ℕ) : ℝ) - (harperD V : ℝ) - (harperR τ : ℝ) := by
  have hV4 : (1 : ℝ) / 4 ≤ V := by linarith
  obtain ⟨hnat, hcore⟩ := harper_block_count hV4 hτ0 hτ1 hτL hΛ
  have hb := harperBarrierTop_ge hV hle
  refine ⟨?_, by linarith⟩
  have hR : ((harperR τ + harperD V + 4 : ℕ) : ℝ) ≤ ((harperBarrierTop B V x : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hR

/-- **The drop fits below the top**, `⌊\log V⌋ + 3 ≤ N`, which is what makes
`RMF.harperBarrierTop` an honest subtraction.  A condition on `Λ` alone once `B` and `V` are
fixed. -/
lemma floor_log_add_three_le_harperN {B : ℕ} {V x : ℝ} (hV : 1 ≤ V)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hΛ : (B : ℝ) + Real.log V + 6 ≤ Real.log (Real.log x)) :
    ⌊Real.log V⌋₊ + 3 ≤ harperN B x := by
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hfl : ((⌊Real.log V⌋₊ : ℕ) : ℝ) ≤ Real.log V := Nat.floor_le hlogV
  have hN := harperN_ge (B := B) (x := x) hx
  have hR : ((⌊Real.log V⌋₊ + 3 : ℕ) : ℝ) ≤ ((harperN B x : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hR

/-! ### The four estimates, named

Each `Prop` below is the conclusion of one declaration and, verbatim, a hypothesis of the next;
inline, each would run to some twenty-five arrows.

The `Block` estimates are stated at a general offset `θ` and barrier top `b`; the `Harper`
estimates are the same estimates at Harper's own data, `θ = RMF.harperTheta B x` and
`b = RMF.harperBarrierTop B V x`, for every `B` past an absolute offset `B₀`. -/

/-- **The far range at a general offset**, `τ ≥ e^{-(2θ+2)}/2`: the barrier's own floor `θ₀` and
block count `n₀`, the constant `Cst`, and Harper's interpolation constant `κ`. -/
def HasFarBlockEstimate.{u} (κ Cst θ₀ : ℝ) (n₀ : ℕ) : Prop :=
  ∀ (Ω' : Type u) [MeasurableSpace Ω'],
  ∃ K > 0,
  ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
  ∀ (θ σ a Λ q m V τ0 : ℝ) (N b : ℕ) (t u : ℝ),
    θ₀ ≤ θ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
    harperR |t - u| + harperD V + 4 ≤ b →
    n₀ ≤ b - harperD V - harperR |t - u| →
    |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
    0 < |t - u| → |t - u| ≤ 1 →
    1 ≤ a → 1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
    a ≤ m + κ * Real.log (2 / |t - u|) →
    Λ ≤ 4 * ((b - harperD V - harperR |t - u| : ℕ) : ℝ) →
    1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
    1 / σ ≤ Real.log (blockScale θ (N + 1)) →
        (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
            ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (blockCutoff θ N) (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff θ N) (shiftLine σ u) ω‖ ^ 2 ∂ν)
          ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
              * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
              * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2))

/-- **The far range at Harper's data**, for every `B` past `B₀`.  The conclusion of
`RMF.le_setIntegral_normSq_pair_far_harper_data_of_harper`, and the `hfarsrc` of
`RMF.le_integral_sq_setIntegral_indicator_normSq_of_parts`. -/
def HasFarHarperEstimate.{u} (κ Cst : ℝ) (B₀ : ℕ) : Prop :=
  ∀ B : ℕ, B₀ ≤ B →
  ∀ (Ω' : Type u) [MeasurableSpace Ω'],
    ∃ K > 0, ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ : ℝ,
    ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
    ∀ (σ a q m x τ0 t u : ℝ),
      1 < x → Λ₀ ≤ Real.log (Real.log x) →
      0 < σ → σ ≤ 1 / 2 → σ * Real.log x ≤ 4 * V → 1 ≤ σ * Real.log x →
      0 < |t - u| → |t - u| ≤ 1 →
      Real.log (1 / |t - u|) ≤ Real.log (Real.log x) / 3 →
      1 ≤ a → 0 ≤ q → q ≤ 1 →
      0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
      a ≤ m + κ * Real.log (2 / |t - u|) →
      1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
        (∫ ω in barrierEventPair (blockPair (harperTheta B x) (shiftLine σ t)
            (shiftLine σ u) Y) (harperBarrierTop B V x)
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
            ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
          ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
              * ((1 / σ) ^ 2
                  / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2)
              * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2))

/-- **The middle range at a general offset**, `τ ≤ e^{-(2θ+2)}/2`: split at
`RMF.splitIndex θ b (t-u) + 2`, shifted by `r`, with Proposition 7's window `Tsh`. -/
def HasMiddleBlockEstimate.{u} (κ Cst Tsh : ℝ) : Prop :=
  ∀ (Ω' : Type u) [MeasurableSpace Ω'],
  ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
  ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
  ∀ (θ σ a Λ q m ϑ t u : ℝ) (N b r : ℕ),
    (125 : ℝ) ≤ θ → θ ≤ ϑ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
    splitIndex θ b (t - u) + 2 ≤ r → r ≤ b →
    1 ≤ splitIndex θ b (t - u) → ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b →
    0 < |t - u| → |t - u| ≤ 1 →
    Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) →
    Real.log (2 / |t - u|) ≤ 2 * (b : ℝ) →
    |σ| * Real.log (blockScale θ (b + 1)) ≤ 1 →
    Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
    (∀ mm, mm < b - r →
      boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
          + blockWindow mm + blockWindow mm + 13
        ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
    max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r harperHf → 4 ≤ b - r →
    4 * Real.log ((b - r : ℕ) : ℝ) ^ 20 ≤ ((b - r : ℕ) : ℝ) →
    4 * Real.log ((b - r : ℕ) : ℝ) ^ 8 ≤ ((b - r : ℕ) : ℝ) * (1 / 18) →
    1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
    a ≤ m + κ * Real.log (2 / |t - u|) →
    0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / |t - u|) + 1 → Λ ≤ 4 * ((b - r : ℕ) : ℝ) →
    Real.exp ((splitIndex θ b (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
    1 / σ ≤ Real.log (blockScale θ (N + 1)) →
        (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
            ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
          ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cst * KQ * CP * bottomConst ϑ
              * (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2
              * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2))

/-- **The middle range at Harper's data**, for every `B` past `B₀`.  The conclusion of
`RMF.le_setIntegral_normSq_pair_middle_harper_data_of_harper`, and the `hmidsrc` of
`RMF.le_integral_sq_setIntegral_indicator_normSq_of_parts`. -/
def HasMiddleHarperEstimate.{u} (κ Cst : ℝ) (B₀ : ℕ) : Prop :=
  ∀ B : ℕ, B₀ ≤ B →
  ∀ (Ω' : Type u) [MeasurableSpace Ω'],
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧ ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ : ℝ,
    ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
    ∀ (σ a q m x t u : ℝ),
      1 < x → Λ₀ ≤ Real.log (Real.log x) →
      0 < σ → σ ≤ 1 / 2 → σ * Real.log x ≤ 4 * V → 1 ≤ σ * Real.log x →
      0 < |t - u| → |t - u| ≤ 1 →
      Real.log 2 + 2 * harperTheta B x + 2 ≤ Real.log (1 / |t - u|) →
      Real.log (1 / |t - u|) ≤ Real.log (Real.log x) / 3 →
      1 / |t - u| ≤ 1 / σ / Real.exp 2 →
      0 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
      a ≤ m + κ * Real.log (2 / |t - u|) → 0 ≤ q → q ≤ 1 →
        (∫ ω in barrierEventPair (blockPair (harperTheta B x) (shiftLine σ t)
            (shiftLine σ u) Y) (harperBarrierTop B V x)
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
            (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
            ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ u) ω‖ ^ 2 ∂ν)
          ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - harperTheta B x)) ^ 2 * Cst * KQ * CP
              * bottomConst ((B : ℝ) + 2) * (1 / σ) ^ 2
              / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2
              * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2))

/-- **`RMF.exists_setIntegral_normSq_pair_far_harper_data_le` with its offset named.**  Reading
the far range at Harper's scales asks the offset to clear the range's own `θ₀` and the `124`
that the middle range's thresholds force, so `B₀ = ⌈θ₀⌉₊ + 124`. -/
theorem le_setIntegral_normSq_pair_far_harper_data_of_harper.{u}
    {κ Cst θ₀ : ℝ} {n₀ : ℕ} (hsrc : HasFarBlockEstimate.{u} κ Cst θ₀ n₀) :
    HasFarHarperEstimate.{u} κ Cst (⌈θ₀⌉₊ + 124) := by
  intro B hB Ω' _
  obtain ⟨K, hK, hfar⟩ := hsrc Ω'
  refine ⟨K, hK, ?_⟩
  intro V hV
  refine ⟨12 * harperSlack B V + 12 * Real.log V + 36 + 3 * (n₀ : ℝ) + ((B : ℝ) + 2), ?_⟩
  intro Y ν hY σ a q m x τ0 t u hx1 hΛ₀ hσ0 hσhalf hσ4 hσx hτ0 hτ1 hτL ha hq0 hq1 hm0 hmΛ hmq ham
    hτ0le hτ0σ
  -- the pieces of `Λ₀`
  have hS5 : (5 : ℝ) ≤ harperSlack B V := le_harperSlack (by linarith)
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hn₀0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hx : (B : ℝ) + 2 ≤ Real.log (Real.log x) := by linarith
  have hΛ12 : 12 * harperSlack B V ≤ Real.log (Real.log x) := by linarith
  have hΛ3 : 3 * harperSlack B V + 3 * Real.log V + 21 ≤ Real.log (Real.log x) := by linarith
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Real.log (Real.log x) := by
    have hBS : (B : ℝ) + 5 ≤ harperSlack B V := by
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog4 : (0 : ℝ) ≤ Real.log (4 * V) := Real.log_nonneg (by linarith)
      rw [harperSlack]
      linarith
    linarith
  have hle := floor_log_add_three_le_harperN hV hx hΛ6
  -- the count at the barrier top
  obtain ⟨hnat, hcore⟩ := harper_block_count_barrierTop hV hτ0 hτ1 hτL hle hΛ12 hΛ3
  have hd : harperD V ≤ harperBarrierTop B V x := by omega
  have hr : harperR |t - u| ≤ harperBarrierTop B V x - harperD V := by omega
  have hcast : ((harperBarrierTop B V x - harperD V - harperR |t - u| : ℕ) : ℝ)
      = ((harperBarrierTop B V x : ℕ) : ℝ) - (harperD V : ℝ) - (harperR |t - u| : ℝ) := by
    rw [Nat.cast_sub hr, Nat.cast_sub hd]
  have hn₀le : n₀ ≤ harperBarrierTop B V x - harperD V - harperR |t - u| := by
    have hR : ((n₀ : ℕ) : ℝ)
        ≤ ((harperBarrierTop B V x - harperD V - harperR |t - u| : ℕ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast hR
  have hn4 : Real.log (Real.log x)
      ≤ 4 * ((harperBarrierTop B V x - harperD V - harperR |t - u| : ℕ) : ℝ) := by
    rw [hcast]
    linarith
  -- `θ₀ ≤ θ`
  have hθ₀ : θ₀ ≤ harperTheta B x := by
    have hceil : θ₀ ≤ ((⌈θ₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil θ₀
    have hBc : ((⌈θ₀⌉₊ : ℕ) : ℝ) + 124 ≤ (B : ℝ) := by exact_mod_cast hB
    have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
    linarith [le_harperTheta (B := B) (x := x) hΛ0]
  have hΛ1 : (1 : ℝ) ≤ Real.log (Real.log x) := by linarith
  exact hfar Y ν hY (harperTheta B x) σ a (Real.log (Real.log x)) q m V τ0 (harperN B x)
    (harperBarrierTop B V x) t u hθ₀ hσ0 hσhalf (harperBarrierTop_le B V x) hnat hn₀le
    (le_trans (abs_sigma_mul_log_blockScale_barrierTop_succ_le_one hV hx1 hx hle hσ0.le hσ4)
      (by linarith))
    hτ0 hτ1 ha hΛ1 hq0 hq1 hm0 hmΛ hmq ham hn4 hτ0le hτ0σ
    (one_div_sigma_le_log_blockScale_harperN_succ hx1 hx hσ0 hσx)

/-- **The far range, at Harper's numeric data.**  `B₀` clears the barrier's `θ₀`; `Λ₀` covers the
block count at `b`, the thresholds of `RMF.harper_block_count_barrierTop`, the count
`Λ ≤ 4(b - d - r)` and `n₀`, and depends only on `B` and `V`.  `Cst` depends on none of `B`, `Ω'`
and `V`; `K` is chosen after `B` and `Ω'` and before `V`. -/
theorem exists_setIntegral_normSq_pair_far_harper_data_le.{u} (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ B₀ : ℕ, HasFarHarperEstimate.{u} κ Cst B₀ := by
  obtain ⟨Cst, hCst, n₀, θ₀, hsrc⟩ := exists_setIntegral_normSq_pair_far_harper_le κ hκ
  exact ⟨Cst, hCst, ⌈θ₀⌉₊ + 124,
    le_setIntegral_normSq_pair_far_harper_data_of_harper hsrc⟩

/-- **`RMF.exists_setIntegral_normSq_pair_middle_harper_data_le` with its offset named.**  The
offset clears four things: `124`, the window `⌈\log T_{sh}⌉` of Proposition 7, the envelope
threshold `RMF.blockOffsetThreshold` and the level floor `RMF.harperShiftFloor`. -/
theorem le_setIntegral_normSq_pair_middle_harper_data_of_harper.{u}
    {κ Cst Tsh : ℝ} {n₁ : ℕ} (hTsh : 0 < Tsh)
    (hn₁ :
      ∀ n : ℕ, n₁ ≤ n →
      4 * Real.log n ^ 20 ≤ (n : ℝ) ∧ 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18))
    (hsrc : HasMiddleBlockEstimate.{u} κ Cst Tsh) :
    HasMiddleHarperEstimate.{u} κ Cst
      (124 + ⌈Real.log Tsh⌉₊ + ⌈blockOffsetThreshold⌉₊ + harperShiftFloor) := by
  set c : ℕ := ⌈Real.log Tsh⌉₊ with hcdef
  intro B hB Ω' _
  obtain ⟨KQ, CP, hKQ, hCP, hmid⟩ := hsrc Ω'
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro V hV
  refine ⟨5 * (B : ℝ) + 5 * Real.log V + 50 + 3 * (harperShiftFloor : ℝ) + 3 * (c : ℝ)
      + 3 * (n₁ : ℝ), ?_⟩
  intro Y ν hY σ a q m x t u hx1 hΛ₀ hσ0 hσhalf hσ4 hσx hτ0 hτ1 hsmall hτL hτσ ha0 hm0 hmΛ hmq ham
    hq0 hq1
  -- notation
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B V x with hbdef
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set r : ℕ := harperShift θ b (t - u) c with hrdef
  set n₂ : ℕ := max (max 4 n₁) ⌈Λ / 4⌉₊ with hn₂def
  -- the pieces of `B₀` and `Λ₀`
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hSF0 : (0 : ℝ) ≤ (harperShiftFloor : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hn₁0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg n₁
  have hx : (B : ℝ) + 2 ≤ Λ := by linarith
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hB124 : 124 ≤ B := by omega
  have hθ125 : (125 : ℝ) ≤ θ := harperTheta_ge hB124 hΛ0
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hθB : (B : ℝ) + 1 ≤ θ := le_harperTheta hΛ0
  -- `B` clears the three absolute thresholds
  have hcB : (c : ℝ) + 1 ≤ θ := by
    have : ((c : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : c ≤ B)
    linarith
  have hSFB : (harperShiftFloor : ℝ) ≤ 4 * θ := by
    have : ((harperShiftFloor : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (by omega : harperShiftFloor ≤ B)
    linarith
  have hbot : blockOffsetThreshold ≤ θ + (r : ℝ) := by
    have hcl : blockOffsetThreshold ≤ ((⌈blockOffsetThreshold⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hcb : ((⌈blockOffsetThreshold⌉₊ : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (by omega : ⌈blockOffsetThreshold⌉₊ ≤ B)
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    linarith
  -- the drop, and the split index
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Λ := by linarith
  have hle := floor_log_add_three_le_harperN hV hx hΛ6
  have hsp2 : ⌊Real.log (1 / |t - u|) - θ⌋₊ + 2 ≤ b :=
    floor_log_one_div_sub_theta_add_two_le_barrierTop hV hx hle hτL (by linarith)
  have hfloor : ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b := by omega
  have hsplit : splitIndex θ b (t - u) = ⌊Real.log (1 / |t - u|) - θ⌋₊ := by
    rw [splitIndex, min_eq_right hfloor]
  have hb1 : 1 ≤ b := by omega
  have h1split : 1 ≤ splitIndex θ b (t - u) := one_le_splitIndex hθ0 hb1 hsmall
  -- the count
  have hn₂R : (n₂ : ℝ) ≤ (max 4 n₁ : ℕ) + Λ / 4 + 1 := by
    rw [hn₂def]
    rcases max_cases (max 4 n₁) ⌈Λ / 4⌉₊ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      have : (0 : ℝ) ≤ Λ / 4 := by linarith
      linarith
    · rw [he]
      have hcl : (⌈Λ / 4⌉₊ : ℝ) ≤ Λ / 4 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      have : (0 : ℝ) ≤ ((max 4 n₁ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hmax4 : ((max 4 n₁ : ℕ) : ℝ) ≤ 4 + (n₁ : ℝ) := by
    rcases max_cases 4 n₁ with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; norm_num
    · rw [he]; linarith
  have hcount : (B : ℝ) + Real.log V + 7 + (harperShiftFloor : ℝ) + (c : ℝ) + (n₂ : ℝ)
      ≤ 2 / 3 * Λ := by linarith
  have hshift : r + n₂ ≤ b := harperShift_add_le_barrierTop hV hx hle hτL hcount
  have hrb : r ≤ b := by omega
  have hsr : splitIndex θ b (t - u) + 2 ≤ r := splitIndex_add_two_le_harperShift θ b (t - u) c
  have hn₂le : n₂ ≤ b - r := by omega
  have hn4b : 4 ≤ b - r := le_trans (le_trans (le_max_left 4 n₁) (le_max_left _ _)) hn₂le
  have hn₁b : n₁ ≤ b - r := le_trans (le_trans (le_max_right 4 n₁) (le_max_left _ _)) hn₂le
  obtain ⟨hbig, hbig2⟩ := hn₁ (b - r) hn₁b
  have hcnt4 : Λ ≤ 4 * ((b - r : ℕ) : ℝ) := by
    have hceil : (⌈Λ / 4⌉₊ : ℕ) ≤ b - r :=
      le_trans (le_max_right (max 4 n₁) ⌈Λ / 4⌉₊) hn₂le
    have hR : ((⌈Λ / 4⌉₊ : ℕ) : ℝ) ≤ ((b - r : ℕ) : ℝ) := by exact_mod_cast hceil
    have hcl : Λ / 4 ≤ (⌈Λ / 4⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  -- the remaining analytic inputs
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hsq : (0 : ℝ) ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
  exact hmid Y ν hY θ σ a Λ q m ((B : ℝ) + 2) t u (harperN B x) b r hθ125
    (harperTheta_lt B x).le hσ0 hσhalf (harperBarrierTop_le B V x) hsr hrb h1split hfloor
    hτ0 hτ1 hsmall (log_two_div_le_two_mul_barrierTop hV hτ0 hx hle hτL (by linarith))
    (abs_sigma_mul_log_blockScale_barrierTop_succ_le_one hV hx1 hx hle hσ0.le hσ4)
    (le_mul_exp_harperShift hTsh hτ0 hfloor)
    (fun mm _ => envelope_harper hbot)
    (result1Threshold_le_shiftLevel ha0 (harperShiftFloor_le_harperShift θ b (t - u) c))
    hn4b hbig hbig2 hΛ1 hq0 hq1 hm0 hmΛ hmq ham ha0
    (harperShift_le_two_mul_log hτ0 hτ1 hcB hSFB hsmall) hcnt4
    (le_trans (exp_splitIndex_add_two_add_theta_le hθ0 h1split)
      (exp_two_div_le_of_le_div hτσ))
    (one_div_sigma_le_log_blockScale_harperN_succ hx1 hx hσ0 hσx)

/-- **The middle range, at Harper's numeric data.**  `B₀` clears `RMF.blockOffsetThreshold` (the
envelope), `RMF.harperShiftFloor` (the level) and `⌈\log Tsh⌉` (Proposition 7's window).  `Λ₀`
covers the count, where the shift `r = RMF.harperShift` binds: `r` costs `Λ/3` at the top of the
range and `b - r ≥ Λ/4` is needed.  `Cst` depends on none of `B`, `Ω'` and `V`; `KQ` and `CP` are
chosen after `B` and `Ω'` and before `V`. -/
theorem exists_setIntegral_normSq_pair_middle_harper_data_le.{u} (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ B₀ : ℕ, HasMiddleHarperEstimate.{u} κ Cst B₀ := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hsrc⟩ :=
    exists_setIntegral_normSq_pair_middle_harper_le κ hκ
  obtain ⟨n₁, hn₁1, hn₁⟩ := exists_forall_log_pow_le
  exact ⟨Cst, hCst,
    124 + ⌈Real.log Tsh⌉₊ + ⌈blockOffsetThreshold⌉₊ + harperShiftFloor,
    le_setIntegral_normSq_pair_middle_harper_data_of_harper hTsh hn₁ hsrc⟩

/-! ### The two things the assembly needs and the ranges do not supply -/

/-- **`q√Λ ≥ 1` gives `W² ≤ Λ`**, `W = 1 + (1-q)√Λ`: the hypothesis `W² ≤ Λ` of
`RMF.integral_sq_setIntegral_indicator_normSq_harper_le`, which fails at `q = 0` for every `Λ`.
With `s = √Λ`, `Λ - W² = (qs - 1)((2-q)s + 1)`, so for `q ≤ 1` the condition is also necessary.
Harper's `q ≥ 2/3` meets it once `Λ ≥ 3`. -/
lemma sq_one_add_one_sub_mul_sqrt_le {q Λ : ℝ} (hq1 : q ≤ 1) (hΛ : 1 ≤ Λ)
    (h : 1 ≤ q * Real.sqrt Λ) :
    (1 + (1 - q) * Real.sqrt Λ) ^ 2 ≤ Λ := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hΛ
  have hssq : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt (by linarith)
  nlinarith [h, hs1, hssq,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - q) (by linarith : (0 : ℝ) ≤ Real.sqrt Λ)]

/-- **The barrier event is jointly measurable in `(ω, t)`**, the hypothesis `hSmeas` of
`RMF.integral_sq_setIntegral_indicator_normSq_harper_le` and
`RMF.integral_sq_setIntegral_indicator_normSq_le_of_setIntegral`.  The same set as in
`RMF.measurableSet_barrierEvent_uncurry`, for a Steinhaus family: `s = 1/2 + σ + it` enters only
through `t ↦ p^{-s}`, which is continuous. -/
lemma measurableSet_prod_barrierEvent {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν)
    (θ σ : ℝ) (b : ℕ) (u v : ℕ → ℝ) :
    MeasurableSet {q : Ω' × ℝ |
      q.1 ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) b u v} := by
  -- `t ↦ p^{-(1/2+σ+it)}` is continuous
  have hshift : Continuous fun t : ℝ => -(shiftLine σ t) := by
    simp only [shiftLine]
    exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg
  have hcpow : ∀ p : Nat.Primes,
      Continuous fun t : ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ t)) := by
    intro p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
      have hpos : 0 < (p : ℕ) := p.2.pos
      exact_mod_cast Nat.cast_ne_zero.2 hpos.ne'
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow hp0).comp hshift.continuousAt
  -- each summand is jointly measurable
  have hterm : ∀ p : Nat.Primes, Measurable
      (fun q : Ω' × ℝ => localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) q.1)) := by
    intro p
    have h1 : Measurable fun q : Ω' × ℝ => Y (p : ℕ) q.1 :=
      (hY.measurable (p : ℕ) p.2).comp measurable_fst
    have h2 : Measurable fun q : Ω' × ℝ => ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      (hcpow p).measurable.comp measurable_snd
    have h3 : Measurable fun q : Ω' × ℝ =>
        (1 : ℂ) - Y (p : ℕ) q.1 * ((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2)) :=
      measurable_const.sub (h1.mul h2)
    simp only [localLog]
    exact (Real.measurable_log.comp h3.norm).neg
  -- hence so is each partial sum
  have hwalk : ∀ j : ℕ, Measurable fun q : Ω' × ℝ =>
      walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) j q.1 := by
    intro j
    simp only [walk_apply]
    exact Finset.measurable_sum _ fun m _ =>
      Finset.measurable_sum _ fun p _ => hterm p
  -- the set is a finite intersection of preimages
  have hrw : {q : Ω' × ℝ |
        q.1 ∈ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) b u v}
      = ⋂ j ∈ Set.Icc 1 b, {q : Ω' × ℝ |
          walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
            localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ q.2))) (Y (p : ℕ) ω)) j q.1
            ∈ Set.Icc (u j) (v j)} := by
    ext q
    simp only [barrierEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Icc]
    exact ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ => (hwalk j) measurableSet_Icc

/-- **`σ\log x_b ≥ 4/e⁴` at Harper's data, uniformly in `V`**: from `σ\log x ≥ 4V`,
`σ\log x_b ≥ 4Ve^{-⌊\log V⌋-4} ≥ 4/e⁴`.  With `RMF.sigma_mul_log_blockScale_barrierTop_le` this
pins `σ\log x_b` into `[4/e⁴, 4/e³]`, so the crude boundary `e^{b+θ-2}` is a bounded factor below
`L_c`; that bounds the `K` of `RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges`. -/
lemma le_sigma_mul_log_blockScale_barrierTop {B : ℕ} {V x σ : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hσ : 4 * V ≤ σ * Real.log x) :
    4 / Real.exp 4 ≤ σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hV0 : (0 : ℝ) < V := by linarith
  have hfl : ((⌊Real.log V⌋₊ : ℕ) : ℝ) ≤ Real.log V := Nat.floor_le hlogV
  have htop : Real.log (blockScale (harperTheta B x) (harperN B x + 1)) = Real.log x := by
    rw [blockScale_harperN_succ hx1 hx]
  rw [log_blockScale] at htop
  have hcast : ((harperBarrierTop B V x : ℕ) : ℝ)
      = ((harperN B x : ℕ) : ℝ) - ((⌊Real.log V⌋₊ : ℕ) : ℝ) - 3 := by
    have h1 : harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) = harperN B x := by
      rw [harperBarrierTop]
      omega
    have h2 : ((harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) : ℕ) : ℝ)
        = ((harperN B x : ℕ) : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  have hsplit : Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x))
      = Real.log x * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) := by
    rw [log_blockScale, ← htop, ← Real.exp_add]
    congr 1
    push_cast [hcast]
    ring
  rw [hsplit, ← mul_assoc]
  have hexp : Real.exp (-(Real.log V + 4))
      ≤ Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) :=
    Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-(Real.log V + 4)) = 1 / (V * Real.exp 4) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hV0]
    field_simp
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  calc 4 / Real.exp 4 = 4 * V * (1 / (V * Real.exp 4)) := by field_simp
    _ = 4 * V * Real.exp (-(Real.log V + 4)) := by rw [hval]
    _ ≤ 4 * V * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ ≤ σ * Real.log x * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_right hσ (Real.exp_pos _).le

/-- **The truncation ratio is bounded**: `\log M/\log⌊x_b⌋ ≤ e⁴` for `M = RMF.harperTruncation σ`,
uniformly in `V` and `x`.  `\log M ≈ 1/(2σ)`, `\log x_b` is `1/σ` up to the drop, and
`RMF.le_sigma_mul_log_blockScale_barrierTop` gives `σ\log x_b ≥ 4/e⁴`, so `V` cancels; without
this the crude range's second regime loses `V⁴`.  The true ratio lies in `[e³/8, e⁴/8]`; the
floor and the ceiling are absorbed by halving. -/
lemma log_harperTruncation_div_log_floor_le {B : ℕ} {V x σ : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x)
    (hB : 124 ≤ B) (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x) (hσ0 : 0 < σ)
    (hσ : 4 * V ≤ σ * Real.log x) :
    Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale (harperTheta B x) (harperBarrierTop B V x)⌋₊ : ℕ) : ℝ)
      ≤ Real.exp 4 := by
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B V x with hbdef
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by
    have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    linarith
  have hθ125 : (125 : ℝ) ≤ θ := harperTheta_ge hB hΛ0
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he4 : (1 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  -- `\log x_b = e^{b+θ} ≥ 8`
  set Lb : ℝ := Real.log (blockScale θ b) with hLbdef
  have hLbeq : Lb = Real.exp ((b : ℝ) + θ) := log_blockScale θ b
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hLb8 : (8 : ℝ) ≤ Lb := by
    rw [hLbeq]
    linarith [Real.add_one_le_exp ((b : ℝ) + θ)]
  -- the floor costs at most `\log 2`
  have hXb2 : (2 : ℝ) ≤ blockScale θ b := two_le_blockScale hθ0 b
  have hfl : blockScale θ b / 2 ≤ ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (blockScale θ b)
    linarith
  have hflpos : (0 : ℝ) < ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by linarith
  have hlogfl : Lb - Real.log 2 ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log (blockScale θ b / 2) ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hfl
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hlogflpos : (0 : ℝ) < Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by linarith
  -- the ceiling costs at most `\log 2`
  have hMle : Real.log ((harperTruncation σ : ℕ) : ℝ) ≤ 1 / (2 * σ) + Real.log 2 := by
    have hexp0 : (1 : ℝ) ≤ Real.exp (1 / (2 * σ)) := by
      have : (0 : ℝ) ≤ 1 / (2 * σ) := by positivity
      linarith [Real.add_one_le_exp (1 / (2 * σ))]
    have hceil : ((harperTruncation σ : ℕ) : ℝ) ≤ 2 * Real.exp (1 / (2 * σ)) := by
      rw [harperTruncation]
      have := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Real.exp (1 / (2 * σ)))).le
      linarith
    have h1 : Real.log ((harperTruncation σ : ℕ) : ℝ)
        ≤ Real.log (2 * Real.exp (1 / (2 * σ))) := by
      refine Real.log_le_log ?_ hceil
      rw [harperTruncation]
      have : (0 : ℝ) < Real.exp (1 / (2 * σ)) := Real.exp_pos _
      have h2 := Nat.le_ceil (Real.exp (1 / (2 * σ)))
      linarith
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, add_comm] at h1
  -- the drop from below turns `1/(2σ)` into `e⁴L_b/8`
  have hlow : 4 / Real.exp 4 ≤ σ * Lb :=
    le_sigma_mul_log_blockScale_barrierTop hV hx1 hx hle hσ
  have h8 : (8 : ℝ) ≤ 2 * Real.exp 4 * (σ * Lb) := by
    have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
    have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * Real.exp 4)
    have heq : 2 * Real.exp 4 * (4 / Real.exp 4) = 8 := by
      field_simp
      norm_num
    linarith [hmul, heq.ge, heq.le]
  have hinv : 1 / (2 * σ) ≤ Real.exp 4 * Lb / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    nlinarith [h8]
  -- `\log 2 ≤ L_b/8`
  have hlog2Lb : Real.log 2 ≤ Lb / 8 := by linarith
  rw [div_le_iff₀ hlogflpos]
  nlinarith [hMle, hinv, hlog2Lb, hlogfl, he4, hLb8]

/-- **The middle range's `hτσ`, from the outer range and a threshold.**  `1/τ ≤ L_c/e²` is not an
extra condition on the middle range: there `\log(1/τ) ≤ Λ/3` and `\log(1/σ) ≥ Λ - \log(4V)`, so
the two meet once `\log(4V) + 2 ≤ (2/3)Λ`, a condition independent of `τ`. -/
lemma le_one_div_sigma_div_exp_two {V x σ t : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x) (hσ0 : 0 < σ)
    (hσ : σ * Real.log x ≤ 4 * V) (hτ0 : 0 < |t|)
    (hτL : Real.log (1 / |t|) ≤ Real.log (Real.log x) / 3)
    (hΛ : Real.log (4 * V) + 2 ≤ 2 / 3 * Real.log (Real.log x)) :
    1 / |t| ≤ 1 / σ / Real.exp 2 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have h4V : (0 : ℝ) < 4 * V := by linarith
  -- `σ\log x ≤ 4V` is `\log x/(4V) ≤ 1/σ`, hence `\log(1/σ) ≥ Λ - \log(4V)`
  have hinvge : Real.log x / (4 * V) ≤ 1 / σ := by
    rw [div_le_div_iff₀ h4V hσ0]
    nlinarith [hσ]
  have hlogσ : Real.log (Real.log x) - Real.log (4 * V) ≤ Real.log (1 / σ) := by
    have h1 : Real.log (Real.log x / (4 * V)) ≤ Real.log (1 / σ) :=
      Real.log_le_log (by positivity) hinvge
    rwa [Real.log_div hlogx.ne' h4V.ne'] at h1
  -- compare logarithms
  have hgoal : Real.log (1 / |t|) ≤ Real.log (1 / σ / Real.exp 2) := by
    rw [Real.log_div (by positivity) (Real.exp_pos 2).ne', Real.log_exp]
    linarith
  have hpos : (0 : ℝ) < 1 / σ / Real.exp 2 := by positivity
  have h := Real.exp_le_exp.2 hgoal
  rwa [Real.exp_log (by positivity), Real.exp_log hpos] at h

/-- **`|t-u| ≤ 1` on Harper's `T`.**  `T ⊆ [-1/2,1/2]`, so every difference is at most `1`. -/
lemma abs_sub_le_one_of_mem_Icc {T : Set ℝ} (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    {t u : ℝ} (ht : t ∈ T) (hu : u ∈ T) : |t - u| ≤ 1 := by
  have h1 := hTsub ht
  have h2 := hTsub hu
  simp only [Set.mem_Icc] at h1 h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `4 ≤ e³`, from `e > 2.7`. -/
lemma four_le_exp_three : (4 : ℝ) ≤ Real.exp 3 := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
  rw [h3]
  linarith [hpow, (by norm_num : (4 : ℝ) ≤ (2.7 : ℝ) ^ 3)]

/-- `1 ≤ e⁶/4`, the crude range's slack constant `K`. -/
lemma one_le_exp_six_div_four : (1 : ℝ) ≤ Real.exp 6 / 4 := by
  have h6 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by rw [← Real.exp_add]; norm_num
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  nlinarith [four_le_exp_three, h6.ge, h6.le]

/-- **The crude boundary sits below `L_c`**, from the drop's upper bound. -/
lemma kappa_le_one_div_sigma {Lb σ : ℝ} (hσ0 : 0 < σ) (hup : σ * Lb ≤ 4 / Real.exp 3) :
    Lb / Real.exp 2 ≤ 1 / σ := by
  have hpos2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hpos3 : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  have h23 : (4 : ℝ) ≤ Real.exp 2 * Real.exp 3 := by
    nlinarith [four_le_exp_three, Real.add_one_le_exp (2 : ℝ), hpos2]
  have hkey : σ * Lb ≤ Real.exp 2 := by
    refine le_trans hup ?_
    rw [div_le_iff₀ hpos3]
    nlinarith [h23, hpos3]
  rw [div_le_div_iff₀ hpos2 hσ0]
  nlinarith [hkey]

/-- **The crude boundary is at most a factor `e⁶/4` below `L_c`**, from the drop's lower bound.
Together with `RMF.kappa_le_one_div_sigma` this is what makes the second crude regime's `K`
absolute. -/
lemma one_div_sigma_le_K_mul_kappa {Lb σ : ℝ} (hσ0 : 0 < σ)
    (hlow : 4 / Real.exp 4 ≤ σ * Lb) :
    1 / σ ≤ Real.exp 6 / 4 * (Lb / Real.exp 2) := by
  have hpos2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hpos4 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have h6 : Real.exp 6 = Real.exp 2 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have hkey : Real.exp 6 / 4 * (Lb / Real.exp 2) = Real.exp 4 * Lb / 4 := by
    rw [h6]; field_simp
  have h4 : (4 : ℝ) ≤ Real.exp 4 * (σ * Lb) := by
    have hm := mul_le_mul_of_nonneg_left hlow hpos4.le
    have heq : Real.exp 4 * (4 / Real.exp 4) = 4 := by field_simp
    linarith [hm, heq.ge, heq.le]
  rw [hkey, div_le_div_iff₀ hσ0 (by norm_num : (0 : ℝ) < 4)]
  nlinarith [h4]

/-! ### Key Proposition 5 at Harper's numeric data

Everything above, composed.  `θ = harperTheta B x`, `N = harperN B x`,
`b = harperBarrierTop B V x`, `σ = 4V/\log x`, `L(t)` the barrier event of
`RMF.barrierEvent_inter_eq_blockPair`, and the two case splits at `τ = ε` and `τ = ε'`. -/

/-- **`(4e²e^{a-θ})² ≤ 16e⁴e^{2a}`**, the shape the crude split and the middle range produce
against the one the assembly's constant wants.  The whole content is `e^{-2θ} ≤ 1`. -/
lemma sq_four_exp_sq_exp_sub_le {a θ : ℝ} (hθ : 0 ≤ θ) :
    (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 ≤ 16 * Real.exp 4 * Real.exp (2 * a) := by
  have h1 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e1 : Real.exp (a - θ) ^ 2 = Real.exp (2 * a) * Real.exp (-(2 * θ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h2 : (4 * Real.exp 2 * Real.exp (a - θ)) ^ 2
      = 16 * (Real.exp 2 * Real.exp 2) * (Real.exp (2 * a) * Real.exp (-(2 * θ))) := by
    rw [mul_pow, mul_pow, e1]
    ring
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [h1, h2, h4]
  have h3 : Real.exp (-(2 * θ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hpos : (0 : ℝ) ≤ 16 * (Real.exp 2 * Real.exp 2) * Real.exp (2 * a) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hpos]

/-- The crude split's constant, reshaped. -/
lemma crude_split_reshape {a θ σ KQ CP bc R : ℝ} (hθ : 0 ≤ θ) (hσ0 : 0 < σ)
    (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hbc : 0 ≤ bc) (hR : 0 ≤ R) :
    (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * KQ * CP * bc / σ ^ 2 * R
      ≤ 16 * Real.exp 4 * Real.exp (2 * a) * KQ * CP * bc * (1 / σ) ^ 2 * R := by
  have hfac := sq_four_exp_sq_exp_sub_le (a := a) (θ := θ) hθ
  have hrest : (0 : ℝ) ≤ KQ * CP * bc / σ ^ 2 * R := by positivity
  calc (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * KQ * CP * bc / σ ^ 2 * R
      = (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * (KQ * CP * bc / σ ^ 2 * R) := by ring
    _ ≤ 16 * Real.exp 4 * Real.exp (2 * a) * (KQ * CP * bc / σ ^ 2 * R) :=
        mul_le_mul_of_nonneg_right hfac hrest
    _ = 16 * Real.exp 4 * Real.exp (2 * a) * KQ * CP * bc * (1 / σ) ^ 2 * R := by
        field_simp

/-- The middle range's constant, reshaped. -/
lemma middle_reshape {a θ σ W Cm KQ CP bc R : ℝ} (hθ : 0 ≤ θ) (hσ0 : 0 < σ) (hW : 0 < W)
    (hCm : 0 ≤ Cm) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hbc : 0 ≤ bc) (hR : 0 ≤ R) :
    (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R
      ≤ 16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R := by
  have hfac := sq_four_exp_sq_exp_sub_le (a := a) (θ := θ) hθ
  have hrest : (0 : ℝ) ≤ Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R := by positivity
  calc (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R
      = (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2
          * (Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R) := by ring
    _ ≤ 16 * Real.exp 4 * Real.exp (2 * a) * (Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R) :=
        mul_le_mul_of_nonneg_right hfac hrest
    _ = 16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ * CP * bc * (1 / σ) ^ 2 / W ^ 2 * R := by
        ring

/-- The crude top's constant, reshaped: the ratio's fourth power bounded, and `e^{-2θ}` dropped. -/
lemma crude_top_reshape {a θ R E16 KQ CP bc Lb nb : ℝ} (hθ : 0 ≤ θ)
    (hRE : R ^ 4 ≤ E16) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hbc : 0 ≤ bc) (hLb : 0 ≤ Lb)
    (hnb : 0 < nb) :
    Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4) * CP * bc * Lb ^ 3 / nb ^ 4
      ≤ Real.exp (2 * a) * (KQ * E16) * CP * bc * Lb ^ 3 / nb ^ 4 := by
  have h1 : Real.exp (-(2 * θ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h1pos : (0 : ℝ) < Real.exp (-(2 * θ)) := Real.exp_pos _
  have hapos : (0 : ℝ) < Real.exp (2 * a) := Real.exp_pos _
  have hR4 : (0 : ℝ) ≤ R ^ 4 := by positivity
  have hKR0 : (0 : ℝ) ≤ KQ * R ^ 4 := by positivity
  have hKR : KQ * R ^ 4 ≤ KQ * E16 := mul_le_mul_of_nonneg_left hRE hKQ
  have hstep1 : Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4)
      ≤ Real.exp (2 * a) * (KQ * E16) := by
    calc Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4)
        ≤ Real.exp (2 * a) * 1 * (KQ * R ^ 4) := by gcongr
      _ = Real.exp (2 * a) * (KQ * R ^ 4) := by ring
      _ ≤ Real.exp (2 * a) * (KQ * E16) := mul_le_mul_of_nonneg_left hKR hapos.le
  have hCPbc : (0 : ℝ) ≤ CP * bc := by positivity
  have hnum : Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4) * CP * bc
      ≤ Real.exp (2 * a) * (KQ * E16) * CP * bc := by
    calc Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4) * CP * bc
        = Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4) * (CP * bc) := by ring
      _ ≤ Real.exp (2 * a) * (KQ * E16) * (CP * bc) :=
          mul_le_mul_of_nonneg_right hstep1 hCPbc
      _ = Real.exp (2 * a) * (KQ * E16) * CP * bc := by ring
  have hden : (0 : ℝ) < nb ^ 4 := by positivity
  have hLb3 : (0 : ℝ) ≤ Lb ^ 3 := by positivity
  have hfinal : Real.exp (2 * a) * Real.exp (-(2 * θ)) * (KQ * R ^ 4) * CP * bc * Lb ^ 3
      ≤ Real.exp (2 * a) * (KQ * E16) * CP * bc * Lb ^ 3 :=
    mul_le_mul_of_nonneg_right hnum hLb3
  rw [div_le_div_iff₀ hden hden]
  nlinarith [mul_le_mul_of_nonneg_right hfinal hden.le]

/-- The far range's constant, reshaped: `e^{2a} ≥ 1` is all it needs. -/
lemma far_reshape {a Cf Kf T4 L4 S2 R : ℝ} (ha : 0 ≤ a) (hCf : 0 ≤ Cf) (hKf : 0 ≤ Kf)
    (hT4 : 0 ≤ T4) (hL4 : 0 ≤ L4) (hS2 : 0 ≤ S2) (hR : 0 ≤ R) :
    Cf * Kf * T4 * L4 * S2 * R ≤ Real.exp (2 * a) * (Cf * Kf * T4 * L4) * S2 * R := by
  have hea : (1 : ℝ) ≤ Real.exp (2 * a) := by
    have h0 : (0 : ℝ) ≤ 2 * a := by linarith
    linarith [Real.add_one_le_exp (2 * a)]
  have hbase : (0 : ℝ) ≤ Cf * Kf * T4 * L4 := by positivity
  have hrest : (0 : ℝ) ≤ S2 * R := by positivity
  calc Cf * Kf * T4 * L4 * S2 * R = (Cf * Kf * T4 * L4) * (S2 * R) := by ring
    _ ≤ Real.exp (2 * a) * (Cf * Kf * T4 * L4) * (S2 * R) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hbase hea) hrest
    _ = Real.exp (2 * a) * (Cf * Kf * T4 * L4) * S2 * R := by ring

/-- **The middle range's lower endpoint**, `τ ≤ e^{-(2θ+2)}/2`, as the `hsmall` the chain reads. -/
lemma log_two_add_two_theta_add_two_le {θ t : ℝ} (hτ0 : 0 < |t|)
    (hτ : |t| ≤ Real.exp (-(2 * θ + 2)) / 2) :
    Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t|) := by
  have hpos : (0 : ℝ) < Real.exp (2 * θ + 2) := Real.exp_pos _
  have hne : Real.exp (-(2 * θ + 2)) = 1 / Real.exp (2 * θ + 2) := by
    rw [Real.exp_neg]
    field_simp
  rw [hne, div_div, le_div_iff₀ (by positivity : (0 : ℝ) < Real.exp (2 * θ + 2) * 2)] at hτ
  have hinv : 2 * Real.exp (2 * θ + 2) ≤ 1 / |t| := by
    rw [le_div_iff₀ hτ0]
    nlinarith [hτ]
  have h1 : Real.log (2 * Real.exp (2 * θ + 2)) ≤ Real.log (1 / |t|) :=
    Real.log_le_log (by positivity) hinv
  rw [Real.log_mul (by norm_num) hpos.ne', Real.log_exp] at h1
  linarith [h1]

/-- **The far range's `τ₀`**, from `τ > e^{-(2θ+2)}/2` and any `θ ≤ Bb`. -/
lemma one_div_abs_le_two_mul_exp {θ Bb t : ℝ} (hθ : θ ≤ Bb) (hτ0 : 0 < |t|)
    (hτ : Real.exp (-(2 * θ + 2)) / 2 < |t|) :
    1 / |t| ≤ 2 * Real.exp (2 * Bb + 2) := by
  have hpos : (0 : ℝ) < Real.exp (2 * θ + 2) := Real.exp_pos _
  have hEF : Real.exp (2 * θ + 2) ≤ Real.exp (2 * Bb + 2) := Real.exp_le_exp.2 (by linarith)
  have hne : Real.exp (-(2 * θ + 2)) = 1 / Real.exp (2 * θ + 2) := by
    rw [Real.exp_neg]
    field_simp
  rw [hne, div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < Real.exp (2 * θ + 2) * 2)] at hτ
  rw [div_le_iff₀ hτ0]
  nlinarith [hτ, mul_le_mul_of_nonneg_right hEF hτ0.le, hτ0]

/-- **The far range's window**, `2τ₀ + 7 ≤ 1/σ`, which at `σ = 4V/\log x` is a condition on
`\log x` alone. -/
lemma two_mul_add_seven_le_one_div_sigma {V x σ c : ℝ} (hσ0 : 0 < σ)
    (hσeq : σ * Real.log x = 4 * V) (hV : 1 ≤ V)
    (hwin : 4 * V * (4 * c + 7) ≤ Real.log x) :
    2 * (2 * c) + 7 ≤ 1 / σ := by
  have h4V : (0 : ℝ) < 4 * V := by linarith
  have hσne : σ ≠ 0 := hσ0.ne'
  have hinv : 1 / σ = Real.log x / (4 * V) := by
    rw [eq_div_iff h4V.ne', ← hσeq]
    field_simp
  rw [hinv, le_div_iff₀ h4V]
  nlinarith [hwin]

set_option maxHeartbeats 4000000 in
-- the four range bounds are elaborated against the assembly's twenty-odd parameters, which is
-- what raises the limit here
/-- **`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le` with its block offset
named.**  The denominator's offset is `\max(\max(124, B_f), B_m)`: `124` from the middle
range's own thresholds, `B_f` from the far range and `B_m` from the middle.  The constant `E`
stays existential here because it is chosen after the space `Ω'`; the offset is not, and it is
the `B₀` that reaches Harper's constant as `e^{-2(B₀+69)}`. -/
theorem le_integral_sq_setIntegral_indicator_normSq_of_parts.{u} {κ Cf Cm : ℝ}
    {Bf Bm : ℕ} (hκ : 0 ≤ κ) (hCf : 0 < Cf) (hCm : 0 < Cm)
    (hfarsrc : HasFarHarperEstimate.{u} κ Cf Bf)
    (hmidsrc : HasMiddleHarperEstimate.{u} κ Cm Bm) :
    ∀ B : ℕ, max (max 124 Bf) Bm ≤ B →
      ∀ (Ω' : Type u) [MeasurableSpace Ω'],
        ∃ E : ℝ, 0 < E ∧ ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (σ a q m x : ℝ) (T : Set ℝ),
          1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
          1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log 2 →
          0 ≤ q → q ≤ 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            (∫ ω, (∫ t in T, Set.indicator
                (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                  (harperBarrierTop B V x)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ 2 ∂ν)
              ≤ (6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                  / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2) := by
  intro B hB
  have hB124 : 124 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  intro Ω' _
  obtain ⟨Kf, hKf, hfar1⟩ :=
    hfarsrc B (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB) Ω'
  obtain ⟨KQ3, CP3, hKQ3, hCP3, hmid1⟩ := hmidsrc B (le_trans (le_max_right _ _) hB) Ω'
  obtain ⟨KQ1, CP1, hKQ1, hCP1, hcs⟩ :=
    exists_setIntegral_normSq_pair_crude_split_harper_data_le (Ω' := Ω')
  obtain ⟨KQ2, CP2, hKQ2, hCP2, hct⟩ :=
    exists_setIntegral_normSq_pair_crude_top_harper_data_le (Ω' := Ω')
  set bc : ℝ := bottomConst ((B : ℝ) + 2) with hbcdef
  have hbc1 : (1 : ℝ) ≤ bc := one_le_bottomConst _
  set τ0 : ℝ := 2 * Real.exp (2 * (B : ℝ) + 6) with hτ0def
  have hτ0pos : (0 : ℝ) < τ0 := by positivity
  refine ⟨max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
        (16 * (Real.exp 6 / 4) * (4 / Real.exp 3) ^ 3 * (KQ2 * Real.exp 16 * CP2 * bc)))
      (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
        (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 81 * (16 * Real.exp 4 * KQ1 * CP1 * bc) := by positivity
    exact lt_of_lt_of_le h1 (le_trans (le_max_left _ _) (le_max_left _ _))
  intro V hV
  obtain ⟨Λf, hfar⟩ := hfar1 V hV
  obtain ⟨Λm, hmid⟩ := hmid1 V hV
  refine ⟨max (max Λf Λm) 1, ?_⟩
  intro Y ν hY σ a q m x T hx1 hx3 hΛ₀ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub ha1 hm0 hmΛ hmq ham
    hq0 hq1 hqΛ
  -- notation
  set θ : ℝ := harperTheta B x with hθdef
  set b : ℕ := harperBarrierTop B V x with hbdef
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set Lb : ℝ := Real.log (blockScale θ b) with hLbdef
  -- arithmetic ground
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hΛ1 : (1 : ℝ) ≤ Λ := le_trans (le_max_right _ _) hΛ₀
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hΛf : Λf ≤ Λ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ₀
  have hΛm : Λm ≤ Λ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ₀
  have hx : (B : ℝ) + 2 ≤ Λ := by linarith
  have hσ4 : σ * Real.log x ≤ 4 * V := le_of_eq hσeq
  have hσ4' : 4 * V ≤ σ * Real.log x := ge_of_eq hσeq
  have hσx : 1 ≤ σ * Real.log x := by rw [hσeq]; linarith
  have hΛ6 : (B : ℝ) + Real.log V + 6 ≤ Λ := by linarith
  have hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x := floor_log_add_three_le_harperN hV hx hΛ6
  have hbge : Λ - (B : ℝ) - Real.log V - 6 ≤ (b : ℝ) := barrierTop_ge_data hV hx hle
  have hb1 : 1 ≤ b := by
    have h : (1 : ℝ) ≤ (b : ℝ) := by linarith
    exact_mod_cast h
  have hb0R : (0 : ℝ) < (b : ℝ) := by linarith
  have hθ125 : (125 : ℝ) ≤ θ := harperTheta_ge hB124 hΛ0
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hθlt : θ < (B : ℝ) + 2 := harperTheta_lt B x
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  -- the block scale at the barrier top
  have hLbeq : Lb = Real.exp ((b : ℝ) + θ) := log_blockScale θ b
  have hLb0 : (0 : ℝ) ≤ Lb := by rw [hLbeq]; positivity
  have hlogLb : Real.log Lb = (b : ℝ) + θ := by rw [hLbeq, Real.log_exp]
  have hLbpos : (0 : ℝ) < Lb := by rw [hLbeq]; positivity
  -- the drop, from both sides
  have hdropup : σ * Lb ≤ 4 / Real.exp 3 :=
    sigma_mul_log_blockScale_barrierTop_le hV hx1 hx hle hσ4
  have hdroplow : 4 / Real.exp 4 ≤ σ * Lb :=
    le_sigma_mul_log_blockScale_barrierTop hV hx1 hx hle hσ4'
  -- the crude boundary and its slack
  set κc : ℝ := Lb / Real.exp 2 with hκcdef
  set Kc : ℝ := Real.exp 6 / 4 with hKcdef
  have hK1 : (1 : ℝ) ≤ Kc := one_le_exp_six_div_four
  have hκLc : κc ≤ 1 / σ := kappa_le_one_div_sigma hσ0 hdropup
  have hLcκ : 1 / σ ≤ Kc * κc := one_div_sigma_le_K_mul_kappa hσ0 hdroplow
  -- `ε` and `ε'`
  set ε : ℝ := Real.exp (-(Λ / 3)) with hεdef
  set ε' : ℝ := Real.exp (-(2 * θ + 2)) / 2 with hε'def
  have hε0 : (0 : ℝ) < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hεdef, Real.exp_le_one_iff]
    linarith
  have hcrudeτ : ∀ τ : ℝ, 0 < τ → τ ≤ ε → Λ / 3 ≤ Real.log (1 / τ) := by
    intro τ hτ0 hτε
    have h1 : Real.log τ ≤ -(Λ / 3) := by
      rw [← Real.log_exp (-(Λ / 3))]
      exact Real.log_le_log hτ0 hτε
    rw [one_div, Real.log_inv]
    linarith
  have houterτ : ∀ τ : ℝ, 0 < τ → ε < τ → Real.log (1 / τ) ≤ Λ / 3 := by
    intro τ hτ0 hτε
    have h1 : -(Λ / 3) ≤ Real.log τ := by
      rw [← Real.log_exp (-(Λ / 3))]
      exact Real.log_le_log (Real.exp_pos _) hτε.le
    rw [one_div, Real.log_inv]
    linarith
  -- the two thresholds the ranges share
  have hsmallcr : Real.log 2 + 2 * θ + 2 ≤ Λ / 3 := by linarith
  have hbθ : Real.log 2 + θ - 2 ≤ (b : ℝ) := by linarith
  have hΛcs : (B : ℝ) + Real.log V + 8 ≤ 2 / 3 * Λ := by linarith
  have hΛ4V : Real.log (4 * V) + 2 ≤ 2 / 3 * Λ := by
    have h4V : Real.log (4 * V) = Real.log 4 + Real.log V := Real.log_mul (by norm_num) (by
      linarith : V ≠ 0)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h4V, hlog4]
    linarith
  -- `1/σ ≤ \log x`, hence `\log(2L_c) ≤ \log 2 + Λ`
  have hinvσ : 1 / σ ≤ Real.log x := by
    rw [div_le_iff₀ hσ0, mul_comm]
    linarith
  have hlogL : 1 + Real.log (2 * (1 / σ)) ≤ 3 * Λ := by
    have hpos : (0 : ℝ) < 1 / σ := by positivity
    have h1 : Real.log (1 / σ) ≤ Λ := by
      rw [hΛdef]
      exact Real.log_le_log hpos hinvσ
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith
  -- the barrier event, and its two measurability facts
  have hXmeas : ∀ (t : ℝ) (m : ℕ), Measurable (fun ω => ∑ p ∈ primeBlockSub θ m,
      localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) := fun t m =>
    Finset.measurable_sum _ fun p _ => (measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)
  refine le_trans (integral_sq_setIntegral_indicator_normSq_harper_of_ranges hY
    (blockCutoff θ (harperN B x))
    (fun t => barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
        localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) b
      (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
    (fun t => measurableSet_barrierEvent (hXmeas t) b _ _)
    (measurableSet_prod_barrierEvent hY θ σ b _ _) hTm hTsub
    (C₁ := 16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc)
    (C₂ := Real.exp (2 * a) * (KQ2 * Real.exp 16) * CP2 * bc)
    (E₁ := 16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
    (E₂ := Real.exp (2 * a) * (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
    (S := 4 / Real.exp 3) (Lb := Lb) (nb := (b : ℝ)) (Lc := 1 / σ)
    (W := 1 + (1 - q) * Real.sqrt Λ) (Λ := Λ) (ε := ε) (ε' := ε') (κ := κc) (K := Kc)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hLb0 hb0R hσ0 rfl (by rw [le_div_iff₀ hσ0]; linarith) hΛ1
    (by nlinarith only [Real.sqrt_nonneg Λ, hq1])
    (sq_one_add_one_sub_mul_sqrt_le hq1 hΛ1 hqΛ)
    hlogL hε0 hε1 hdropup (log_log_le_two_mul_barrierTop hV hx hle (by linarith))
    hK1 hκLc hLcκ ?_ ?_ ?_ ?_ ?_) ?_
  · -- `hcrudelog`
    intro τ hτ0 hτε
    have h := hcrudeτ τ hτ0 hτε
    rw [log_two_div_eq hτ0]
    linarith
  · -- `hcr1`, the first crude regime
    intro t ht u hu htu hτε hκτ
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := abs_sub_le_one_of_mem_Icc hTsub ht hu
    have hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) :=
      le_trans hsmallcr (hcrudeτ _ hτ0 hτε)
    have hreg : Real.log (1 / |t - u|) ≤ (b : ℝ) + θ - 2 := by
      have hlogκ : Real.log κc = (b : ℝ) + θ - 2 := by
        rw [hκcdef, Real.log_div hLbpos.ne' (Real.exp_pos 2).ne', Real.log_exp, hlogLb]
      have hpos : (0 : ℝ) < 1 / |t - u| := by positivity
      have := Real.log_le_log hpos hκτ
      rwa [hlogκ] at this
    have hsrc := hcs Y ν hY B V x σ a t u hB124 hV hx1 hx hle hσ0 hσhalf hσx hσ4 hτ0 hτ1
      hsmall
      hreg hbθ hΛcs
    rw [barrierEvent_inter_eq_blockPair]
    exact le_trans hsrc (crude_split_reshape hθ0 hσ0 hKQ1.le hCP1.le (by linarith)
      (by positivity))
  · -- `hcr2`, the second crude regime
    intro t ht u hu htu hτε hτκ
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hsrc := hct Y ν hY B V x σ a t u hB124 hV hx1 hx3 hx hle hb1 hσ0 hσ4 hσx
    rw [barrierEvent_inter_eq_blockPair]
    refine le_trans hsrc ?_
    have hR : Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) ≤ Real.exp 4 :=
      log_harperTruncation_div_log_floor_le hV hx1 hB124 hx hle hσ0 hσ4'
    have hR0 : (0 : ℝ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) := by
      have h400 := four_hundred_le_floor_blockScale (θ := θ) (by linarith) b
      have hM := Nat.le_ceil (Real.exp (1 / (2 * σ)))
      have hMpos : (0 : ℝ) < ((harperTruncation σ : ℕ) : ℝ) := by
        rw [harperTruncation]
        have := Real.exp_pos (1 / (2 * σ))
        linarith
      have hnum : (0 : ℝ) ≤ Real.log ((harperTruncation σ : ℕ) : ℝ) := by
        refine Real.log_nonneg ?_
        rw [harperTruncation]
        have hexp1 : (1 : ℝ) ≤ Real.exp (1 / (2 * σ)) := by
          have : (0 : ℝ) ≤ 1 / (2 * σ) := by positivity
          linarith [Real.add_one_le_exp (1 / (2 * σ))]
        linarith
      have hden : (0 : ℝ) ≤ Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) :=
        Real.log_nonneg (by linarith)
      positivity
    have hpow : (Real.log ((harperTruncation σ : ℕ) : ℝ)
        / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ)) ^ 4 ≤ Real.exp 16 := by
      have h4 : Real.exp 16 = Real.exp 4 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h4]
      exact pow_le_pow_left₀ hR0 hR 4
    exact crude_top_reshape hθ0 hpow hKQ2.le hCP2.le (by linarith) hLb0 hb0R
  · -- `hmid`
    intro t ht u hu htu hτε hτε'
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := abs_sub_le_one_of_mem_Icc hTsub ht hu
    have hτL : Real.log (1 / |t - u|) ≤ Λ / 3 := houterτ _ hτ0 hτε
    have hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) :=
      log_two_add_two_theta_add_two_le hτ0 hτε'
    have hτσ : 1 / |t - u| ≤ 1 / σ / Real.exp 2 :=
      le_one_div_sigma_div_exp_two hV hx1 hσ0 hσ4 hτ0 hτL hΛ4V
    have hamτ : a ≤ m + κ * Real.log (2 / |t - u|) := by
      have hlog : Real.log 2 ≤ Real.log (2 / |t - u|) := by
        refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ hτ0]
        linarith
      nlinarith only [hκ, hlog, ham]
    have hsrc := hmid Y ν hY σ a q m x t u hx1 hΛm hσ0 hσhalf hσ4 hσx hτ0 hτ1 hsmall hτL hτσ
      (by linarith) hm0 hmΛ hmq hamτ hq0 hq1
    have hWpos : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by
      nlinarith only [Real.sqrt_nonneg Λ, hq1]
    rw [barrierEvent_inter_eq_blockPair]
    exact le_trans hsrc (middle_reshape hθ0 hσ0 hWpos hCm.le hKQ3.le hCP3.le (by linarith)
      (by positivity))
  · -- `hfar`
    intro t ht u hu htu hτε hτε'
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := abs_sub_le_one_of_mem_Icc hTsub ht hu
    have hτL : Real.log (1 / |t - u|) ≤ Λ / 3 := houterτ _ hτ0 hτε
    have hτ0le : 1 / |t - u| ≤ τ0 := by
      rw [hτ0def, show 2 * (B : ℝ) + 6 = 2 * ((B : ℝ) + 2) + 2 by ring]
      exact one_div_abs_le_two_mul_exp (by linarith) hτ0 hτε'
    have hτ0σ : 2 * τ0 + 7 ≤ 1 / σ := by
      rw [hτ0def]
      exact two_mul_add_seven_le_one_div_sigma hσ0 hσeq hV hfarwin
    have hamτ : a ≤ m + κ * Real.log (2 / |t - u|) := by
      have hlog : Real.log 2 ≤ Real.log (2 / |t - u|) := by
        refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ hτ0]
        linarith
      nlinarith only [hκ, hlog, ham]
    have hsrc := hfar Y ν hY σ a q m x τ0 t u hx1 hΛf hσ0 hσhalf hσ4 hσx hτ0 hτ1 hτL ha1
      hq0 hq1
      hm0 hmΛ hmq hamτ hτ0le hτ0σ
    rw [barrierEvent_inter_eq_blockPair]
    refine le_trans hsrc ?_
    have hlogT : (0 : ℝ) ≤ Real.log (2 * (2 * τ0 + 7)) :=
      Real.log_nonneg (by nlinarith only [hτ0pos])
    have hlogpos : (0 : ℝ) < Real.log (2 / |t - u|) := log_two_div_pos hτ0 hτ1
    refine le_trans (far_reshape (a := a) (by linarith) hCf.le hKf.le
      (by positivity : (0 : ℝ) ≤ (2 * τ0 + 7) ^ 2)
      (by positivity : (0 : ℝ) ≤ Real.log (2 * (2 * τ0 + 7)) ^ 4)
      (by positivity : (0 : ℝ) ≤ (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
      (by positivity : (0 : ℝ) ≤ 1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)))
      (le_of_eq (by ring))
  · -- collapse the four constants
    have hea : (1 : ℝ) ≤ Real.exp (2 * a) := by
      have : (0 : ℝ) ≤ 2 * a := by linarith
      linarith [Real.add_one_le_exp (2 * a)]
    have hW2 : (0 : ℝ) < (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
      have hs : (0 : ℝ) ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
      have : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by nlinarith
      positivity
    have hE0 : (0 : ℝ) ≤ Real.exp (2 * a) := (Real.exp_pos _).le
    have hmaxle : max (max (81 * (16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc))
          (16 * Kc * (4 / Real.exp 3) ^ 3
            * (Real.exp (2 * a) * (KQ2 * Real.exp 16) * CP2 * bc)))
        (max (16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
          (Real.exp (2 * a)
            * (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4)))
        ≤ max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
              (16 * (Real.exp 6 / 4) * (4 / Real.exp 3) ^ 3 * (KQ2 * Real.exp 16 * CP2 * bc)))
            (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
              (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
          * Real.exp (2 * a) := by
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hE0)
        ring
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hE0)
        rw [hKcdef]
        ring
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hE0)
        ring
      · refine le_trans (le_of_eq ?_)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hE0)
        ring
    have hcoef : (0 : ℝ) ≤ (6 + 2 / Real.log 2)
        * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := by positivity
    calc (6 + 2 / Real.log 2)
          * (max (max (81 * (16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc))
              (16 * Kc * (4 / Real.exp 3) ^ 3
                * (Real.exp (2 * a) * (KQ2 * Real.exp 16) * CP2 * bc)))
            (max (16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
              (Real.exp (2 * a)
                * (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4)))
            * (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
        = (6 + 2 / Real.log 2) * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
            * max (max (81 * (16 * Real.exp 4 * Real.exp (2 * a) * KQ1 * CP1 * bc))
              (16 * Kc * (4 / Real.exp 3) ^ 3
                * (Real.exp (2 * a) * (KQ2 * Real.exp 16) * CP2 * bc)))
            (max (16 * Real.exp 4 * Real.exp (2 * a) * Cm * KQ3 * CP3 * bc)
              (Real.exp (2 * a)
                * (Cf * Kf * (2 * τ0 + 7) ^ 2
                  * Real.log (2 * (2 * τ0 + 7)) ^ 4))) := by ring
      _ ≤ (6 + 2 / Real.log 2) * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
            * (max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
                (16 * (Real.exp 6 / 4) * (4 / Real.exp 3) ^ 3
                  * (KQ2 * Real.exp 16 * CP2 * bc)))
              (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
                (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
              * Real.exp (2 * a)) := mul_le_mul_of_nonneg_left hmaxle hcoef
      _ = (6 + 2 / Real.log 2)
            * (max (max (81 * (16 * Real.exp 4 * KQ1 * CP1 * bc))
                (16 * (Real.exp 6 / 4) * (4 / Real.exp 3) ^ 3
                  * (KQ2 * Real.exp 16 * CP2 * bc)))
              (max (16 * Real.exp 4 * Cm * KQ3 * CP3 * bc)
                (Cf * Kf * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4))
              * Real.exp (2 * a) * (1 / σ) ^ 2
              / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := by ring

/-- **Key Proposition 5 at Harper's data** (Harper, *Moments of random multiplicative functions,
I*).  At `σ\log x = 4V`, with `W = 1 + (1-q)√(\log\log x)`,

`E(∫_T 1_{L(t)}|F(1/2+σ+it)|² dt)² ≤ (6 + 2/\log 2)·E·e^{2a}(\log x/(4V))²/W²`

for `T ⊆ [-1/2, 1/2]`, `1 ≤ a ≤ m + κ\log 2` with `0 ≤ m ≤ min{√(\log\log x), 1/(1-q)}`, and
`L(t)` the barrier on `[1, RMF.harperBarrierTop B V x]` at `θ = RMF.harperTheta B x`.  `E` depends
on `κ`, `B` and `Ω'`, not on `V`, `Y`, `x`, `q`, `a` or `T`; `Λ₀` depends on `V`.

`B₀` collects the middle range's three thresholds and the far range's `θ₀`.  The hypotheses
`6B + 3\log V + 40 ≤ \log\log x` and `4V(4e^{2B+6} + 7) ≤ \log x` are the block count and the
far range's window `2τ₀ + 7 ≤ 1/σ`.  `1 ≤ q√(\log\log x)` gives `W² ≤ \log\log x`
(`RMF.sq_one_add_one_sub_mul_sqrt_le`; the two are equivalent), which fails at `q = 0`; Harper's
`q ≥ 2/3` meets it. -/
theorem integral_sq_setIntegral_indicator_normSq_harper_data_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ E : ℝ, 0 < E ∧ ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (σ a q m x : ℝ) (T : Set ℝ),
          1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 40 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
          1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log 2 →
          0 ≤ q → q ≤ 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            (∫ ω, (∫ t in T, Set.indicator
                (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                  (harperBarrierTop B V x)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j))
                (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ 2 ∂ν)
              ≤ (6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                  / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2) := by
  obtain ⟨Cf, hCf, Bf, hfarsrc⟩ := exists_setIntegral_normSq_pair_far_harper_data_le κ hκ
  obtain ⟨Cm, hCm, Bm, hmidsrc⟩ := exists_setIntegral_normSq_pair_middle_harper_data_le κ hκ
  exact ⟨max (max 124 Bf) Bm,
    le_integral_sq_setIntegral_indicator_normSq_of_parts hκ hCf hCm hfarsrc hmidsrc⟩

/-! ### The numerator's grid and the barrier's

`RMF/Reduction/Numerator.lean` states the lower bound on `E X` on `RMF.harperOffset D x` and
`RMF.harperBlockCount D x - d`; Key Proposition 5 is stated on `RMF.harperTheta B x` and
`RMF.harperBarrierTop B V x`.  The Hölder step needs the same `X` in both, and the grids agree at
`D = B + 2` and `d = ⌊\log V⌋ + 3`.  The tilt budget fits as well: the numerator wants
`|σ|\log x ≤ η ≤ E₀ ≤ e^d`, and at `η = E₀ = 4V` the ratio `e^{⌊\log V⌋+3}/(4V)` exceeds `e²/4`,
since `⌊\log V⌋ > \log V - 1`. -/

/-- `harperOffset (B+2) = harperTheta B`.  Both are `\{\log\log x\}` plus a constant; the
constants differ by `2`, which is the whole content. -/
lemma harperOffset_eq_harperTheta (B : ℕ) {x : ℝ} (hx : 0 ≤ Real.log (Real.log x)) :
    harperOffset (B + 2) x = harperTheta B x := by
  have hfl : ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) = ((⌊Real.log (Real.log x)⌋ : ℤ) : ℝ) :=
    natCast_floor_eq_intCast_floor hx
  rw [harperOffset, harperTheta, ← Int.self_sub_floor, hfl]
  push_cast
  ring

/-- `harperBlockCount (B+2) x - (⌊\log V⌋+3) = harperBarrierTop B V x` — the numerator's drop `d`
is the barrier's drop. -/
lemma harperBlockCount_sub_eq_harperBarrierTop (B : ℕ) (V x : ℝ) :
    harperBlockCount (B + 2) x - (⌊Real.log V⌋₊ + 3) = harperBarrierTop B V x := by
  rw [harperBlockCount, harperBarrierTop, harperN]
  omega

end RMF
