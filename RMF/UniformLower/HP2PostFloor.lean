/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP2Post
import RMF.UniformLower.ComparisonFloor

/-!
# HP2's post part at the floor `20`

The post bound for a pair of heights from window scale `k ≥ 20`, on the post tubes and with the
two-fold block data of `RMF/UniformLower/HP2Post.lean`.

* **The cosine errors**: every block's error is `RMF.blockCosErrDecay` (explicit Mertens below
  scale `104`, the PNT above), at most `7.43·10⁻⁸` per block and `3.2·10⁻⁶` summed over any set of
  blocks (`RMF.sum_blockCosErrDecay_le`); telescoped runs cost `RMF.blockCosTelErr ≤ 3.16·10⁻⁶`.
* **The chain** (`RMF.tiltedMeasure₂_hp2PostTube_le_sum_floor`): the two-fold comparison
  `RMF.exists_isBoxComparison_rademacher_budget₂` at offset `k + b` with the envelope
  `770(b + m + 1)` (budget `RMF.hp2Post_budget`), the barriers inside `200(b + j + 1)`
  (`a + A + B + ρ ≤ 100`), the post blocks' variances, determinants and means
  (`RMF.hp2Post_comparison_inputs_floor`), then the summed-variance pair ballot.
* **The product form and the numerals** (`RMF.tiltedMeasure₂_hp2PostTube_le_Cpost_floor`,
  `RMF.hp2Post_bound_of_numerals_floor`), with the allowances `7.5·10⁻⁸` per block
  (covariances), `3.3·10⁻⁶` summed (covariances), `1.6·10⁻⁶` (variance sums) and `3.2·10⁻⁶`
  (push).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RMF

/-! ### The cosine errors at the floor `20` -/

section Errors

/-- The difference frequency at depth `d` from `k ≥ 20`: `|D|e^{k+d} ≤ 1` gives `|D| ≤ 2e^{-20}`. -/
lemma abs_le_two_exp_neg_twenty_of_depth {k d : ℕ} {D : ℝ} (hk : 20 ≤ k)
    (hd2 : |D| * Real.exp ((k : ℝ) + d) ≤ 1) : |D| ≤ 2 * Real.exp (-20) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have he : Real.exp 20 ≤ Real.exp ((k : ℝ) + d) :=
    Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have h1 : |D| * Real.exp 20 ≤ 1 :=
    (mul_le_mul_of_nonneg_left he (abs_nonneg D)).trans hd2
  have h2 : Real.exp (-20) * Real.exp 20 = 1 := by rw [← Real.exp_add]; norm_num
  have h3 : |D| ≤ Real.exp (-20) := by
    have hpos := Real.exp_pos 20
    nlinarith [Real.exp_pos (-20)]
  linarith [Real.exp_pos (-20)]

/-- A frequency `τ ≤ 2e^{-k}` with `k ≥ 20` has `τ ≤ 2e^{-20}`. -/
lemma le_two_exp_neg_twenty_of_le {k : ℕ} {τ : ℝ} (hk : 20 ≤ k)
    (hτ : τ ≤ 2 * Real.exp (-(k : ℝ))) : τ ≤ 2 * Real.exp (-20) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  exact hτ.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num))

/-- `RMF.blockCosErrDecay` is nonnegative for `τ ≥ 0`. -/
lemma blockCosErrDecay_nonneg {θ τ : ℝ} (m : ℕ) (hτ : 0 ≤ τ) : 0 ≤ blockCosErrDecay θ m τ := by
  have hK := mertensErrConst_nonneg
  unfold blockCosErrDecay
  split_ifs <;> positivity

/-- **The decaying error per block at the floor `20`**: `blockCosErrDecay θ m τ ≤ 7.43·10⁻⁸` for
`m + θ ≥ 20` and `0 ≤ τ ≤ 2e^{-20}` (`RMF.blockCosErr_le_numeral`). -/
lemma blockCosErrDecay_le_numeral {θ τ : ℝ} {m : ℕ} (hm : 20 ≤ (m : ℝ) + θ) (hτ0 : 0 ≤ τ)
    (hτ2 : τ ≤ 2 * Real.exp (-20)) : blockCosErrDecay θ m τ ≤ 7.43 / 10 ^ 8 :=
  (blockCosErrDecay_le_blockCosErr m hτ0).trans (blockCosErr_le_numeral hm hτ2)

/-- **The decaying errors summed over any blocks, at the floor `20`**: for `θ ≥ 20` and
`0 ≤ τ ≤ 2e^{-20}`, `∑_{m∈s} blockCosErrDecay θ m τ ≤ 3.2·10⁻⁶` — below scale `104` (at most `84`
blocks) Mertens' `2Ke^{-(m+θ)} + Kτ`, above it the PNT's `(τ+1)e^{104-(m+θ)}/10²⁸`. -/
theorem sum_blockCosErrDecay_le {θ τ : ℝ} (hθ : 20 ≤ θ) (hτ0 : 0 ≤ τ)
    (hτ2 : τ ≤ 2 * Real.exp (-20)) (s : Finset ℕ) :
    ∑ m ∈ s, blockCosErrDecay θ m τ ≤ 3.2 / 10 ^ 6 := by
  classical
  have hK := mertensErrConst_le
  have hK0 := mertensErrConst_nonneg
  have he := exp_neg_twenty_le_numeral
  have he0 : 0 ≤ Real.exp (-20) := (Real.exp_pos _).le
  rw [← Finset.sum_filter_add_sum_filter_not s (fun m : ℕ => 104 ≤ (m : ℝ) + θ)]
  -- the blocks past the PNT floor
  have hPNT : ∑ m ∈ s.filter (fun m : ℕ => 104 ≤ (m : ℝ) + θ), blockCosErrDecay θ m τ
      ≤ 1.59 * (τ + 1) / 10 ^ 28 := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈104 - θ⌉₊ := ⟨_, rfl⟩
    have hterm : ∀ m ∈ s.filter (fun m : ℕ => 104 ≤ (m : ℝ) + θ), blockCosErrDecay θ m τ
        = (τ + 1) * Real.exp (104 - θ) / 10 ^ 28 * Real.exp (-(m : ℝ))
          * (1 + 0 * (2 * (m : ℝ) + 1)) := by
      intro m hm
      have hm' := (Finset.mem_filter.1 hm).2
      unfold blockCosErrDecay
      rw [if_pos hm', show (104 : ℝ) - ((m : ℝ) + θ) = (104 - θ) + -(m : ℝ) by ring,
        Real.exp_add]
      ring
    rw [Finset.sum_congr rfl hterm]
    have hNm : ∀ m ∈ s.filter (fun m : ℕ => 104 ≤ (m : ℝ) + θ), N ≤ m := by
      intro m hm
      have hm' := (Finset.mem_filter.1 hm).2
      rw [hN]
      exact Nat.ceil_le.2 (by linarith)
    have h := sum_mul_exp_neg_mul_le_numeral_of_le
      (c := (τ + 1) * Real.exp (104 - θ) / 10 ^ 28) (K := 1) (B := 0) (by positivity)
      zero_le_one le_rfl hNm
    refine h.trans ?_
    have hN' : 104 - θ ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil _
    have he1 : Real.exp (104 - θ) * Real.exp (-(N : ℝ)) ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by linarith)
    have hτ1 : 0 ≤ τ + 1 := by linarith
    calc (τ + 1) * Real.exp (104 - θ) / 10 ^ 28 * Real.exp (-(N : ℝ))
          * (1.59 * (1 + 2 * 0 * (N : ℝ)) + 3.43 * 0)
        = 1.59 * (τ + 1) * (Real.exp (104 - θ) * Real.exp (-(N : ℝ))) / 10 ^ 28 := by ring
      _ ≤ 1.59 * (τ + 1) * 1 / 10 ^ 28 := by gcongr
      _ = 1.59 * (τ + 1) / 10 ^ 28 := by ring
  -- the blocks below it: at most `84`, Mertens
  have hMer : ∑ m ∈ s.filter (fun m : ℕ => ¬ 104 ≤ (m : ℝ) + θ), blockCosErrDecay θ m τ
      ≤ 2 * mertensErrConst * Real.exp (-20) * 1.5821 + mertensErrConst * τ * 84 := by
    obtain ⟨s', hs'⟩ : ∃ s' : Finset ℕ, s' = s.filter (fun m : ℕ => ¬ 104 ≤ (m : ℝ) + θ) :=
      ⟨_, rfl⟩
    rw [← hs']
    have hmem : ∀ m ∈ s', ¬ 104 ≤ (m : ℝ) + θ := fun m hm => by
      rw [hs'] at hm
      exact (Finset.mem_filter.1 hm).2
    have hterm : ∀ m ∈ s', blockCosErrDecay θ m τ
        = 2 * mertensErrConst * Real.exp (-θ) * Real.exp (-(m : ℝ)) + mertensErrConst * τ := by
      intro m hm
      unfold blockCosErrDecay
      rw [if_neg (hmem m hm), show -((m : ℝ) + θ) = -θ + -(m : ℝ) by ring, Real.exp_add]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    have hsub : s' ⊆ Finset.range 84 := by
      intro m hm
      rw [Finset.mem_range]
      by_contra hc
      have : (84 : ℝ) ≤ m := by exact_mod_cast not_lt.1 hc
      exact hmem m hm (by linarith)
    have hcard : (s'.card : ℝ) ≤ 84 := by
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hgeo := sum_exp_neg_le s'
    have hq : Real.exp 1 / (Real.exp 1 - 1) ≤ 1.5821 := by
      have he1 : (2.7182 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hθe : Real.exp (-θ) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
    have hs0 : 0 ≤ ∑ m ∈ s', Real.exp (-(m : ℝ)) :=
      Finset.sum_nonneg fun m _ => (Real.exp_pos _).le
    have h1 : 2 * mertensErrConst * Real.exp (-θ) * ∑ m ∈ s', Real.exp (-(m : ℝ))
        ≤ 2 * mertensErrConst * Real.exp (-20) * 1.5821 := by
      calc 2 * mertensErrConst * Real.exp (-θ) * ∑ m ∈ s', Real.exp (-(m : ℝ))
          ≤ 2 * mertensErrConst * Real.exp (-20) * ∑ m ∈ s', Real.exp (-(m : ℝ)) := by gcongr
        _ ≤ 2 * mertensErrConst * Real.exp (-20) * 1.5821 := by gcongr; linarith
    have h2 : (s'.card : ℝ) * (mertensErrConst * τ) ≤ mertensErrConst * τ * 84 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hcard (mul_nonneg hK0 hτ0)
    linarith
  -- the numerals: `K ≤ 9.0028`, `e^{-20} ≤ 1/(4.85·10⁸)`
  have h3 : mertensErrConst * Real.exp (-20) ≤ 9.0028 * (1 / 485000000) :=
    mul_le_mul hK he he0 (by norm_num)
  have h4 : mertensErrConst * τ ≤ mertensErrConst * (2 * Real.exp (-20)) :=
    mul_le_mul_of_nonneg_left hτ2 hK0
  have hτ1 : τ ≤ 1 := by linarith
  have h5 : 1.59 * (τ + 1) / 10 ^ 28 ≤ 1 / 10 ^ 27 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- `RMF.sum_blockCosErrDecay_le` over the blocks `b ≤ m < b + n`. -/
lemma sum_range_blockCosErrDecay_le {θ τ : ℝ} (hθ : 20 ≤ θ) (hτ0 : 0 ≤ τ)
    (hτ2 : τ ≤ 2 * Real.exp (-20)) (b n : ℕ) :
    ∑ m ∈ Finset.range n, blockCosErrDecay θ (m + b) τ ≤ 3.2 / 10 ^ 6 := by
  have h := sum_blockCosErrDecay_le hθ hτ0 hτ2 ((Finset.range n).image (fun m => m + b))
  rwa [Finset.sum_image (fun a _ c _ hac => by omega)] at h

end Errors

/-! ### The envelopes -/

/-- The envelope `200(b + j + 1)` holds the post tube's barriers at block `j` whose summed mean is
at most `1.52j` in size, for a start `z ∈ [-A - Bb - ρ, a + ρ]` and `a, A, B, ρ ≥ 0` summing to at
most `100`. -/
lemma hp2Post_envelope_floor {Mn a A B ρ z : ℝ} {b j : ℕ} (hMn : |Mn| ≤ 1.52 * j) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (henv : a + A + B + ρ ≤ 100)
    (hz : -A - B * b - ρ ≤ z ∧ z ≤ a + ρ) :
    -(200 * ((b : ℝ) + j + 1)) ≤ Mn - A - B * ((b : ℝ) + j) - ρ - z
      ∧ Mn + a + ρ - z ≤ 200 * ((b : ℝ) + j + 1) := by
  have hS := abs_le.1 hMn
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hB100 : B ≤ 100 := by linarith
  have hBbj : B * ((b : ℝ) + j) ≤ 100 * ((b : ℝ) + j) :=
    mul_le_mul_of_nonneg_right hB100 (by positivity)
  have hBb : B * b ≤ 100 * b := mul_le_mul_of_nonneg_right hB100 hb0
  constructor <;> linarith [hz.1, hz.2]

/-- The comparison's envelope `770(b + m + 1)` holds two consecutive barrier envelopes
`200(b + j + 1)` and a window `≤ 1`. -/
lemma hp2Post_envelope_le_floor {b m : ℕ} {w : ℝ} (hw : w ≤ 1) :
    200 * ((b : ℝ) + m + 1) + 200 * ((b : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) + w
      ≤ 770 * ((b : ℝ) + m + 1) := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  linarith

/-! ### The chain: comparison, slack, Gaussian pair ballot -/

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The two-fold comparison's inputs on the post blocks, from `k ≥ 20`**: for
`h₁, h₂ ∈ halfWindow k`, `σe^{k+b+n} ≤ 1/200`, the post start past the decorrelation point with
`b ≥ 4` or `b ≥ 2` and the difference phase past `e`, every post block `m + b`, `m < n`, has both
two-fold variances in `[0.3649, 0.6551]`, determinant `≥ pairBlockDet (m + b)` and both two-fold
means at most `1.93` (`RMF.pair_block_comparison_inputs_det`, `RMF.abs_pair_block_means_le`). -/
lemma hp2Post_comparison_inputs_floor (hX : IsRademacherPrimeValues X μ) {k b n y : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσn : σ * Real.exp ((k : ℝ) + (b + n)) ≤ 1 / 200)
    (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y)
    (hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b))
    (hcase : 4 ≤ b ∨ (2 ≤ b ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b)))
    {m : ℕ} (hm : m < n) :
    ((0.3649 ≤ pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
        ∧ pairVarH X μ y k σ h₁ h₂ h₁ (m + b) ≤ 0.6551)
      ∧ (0.3649 ≤ pairVarH X μ y k σ h₁ h₂ h₂ (m + b)
        ∧ pairVarH X μ y k σ h₁ h₂ h₂ (m + b) ≤ 0.6551)
      ∧ pairBlockDet (m + b) ≤ pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
          * pairVarH X μ y k σ h₁ h₂ h₂ (m + b) - pairCovH X μ y k σ h₁ h₂ (m + b) ^ 2)
    ∧ (|pairMeanH X μ y k σ h₁ h₂ h₁ (m + b)| ≤ 1.93
      ∧ |pairMeanH X μ y k σ h₁ h₂ h₂ (m + b)| ≤ 1.93) := by
  have hmb : ((m + b : ℕ) : ℝ) = (b : ℝ) + m := by push_cast; ring
  have hσm : σ * Real.exp ((k : ℝ) + ((m + b : ℕ) : ℝ) + 1) ≤ 1 / 200 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hσ) hσn
    have : ((m : ℝ) + 1) ≤ n := by exact_mod_cast hm
    rw [hmb]
    linarith
  have hmono : |h₁ - h₂| * Real.exp ((k : ℝ) + b)
      ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + ((m + b : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      rw [hmb]; linarith [Nat.cast_nonneg (α := ℝ) m])) (abs_nonneg _)
  have hcase' : 4 ≤ m + b ∨ (2 ≤ m + b
      ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + ((m + b : ℕ) : ℝ))) := by
    rcases hcase with h4 | ⟨h2, he⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, he.trans hmono⟩
  exact ⟨pair_block_comparison_inputs_det hX y hk hh₁ hh₂ hσ hσm (hdep.trans hmono) hcase'
      (hy m hm),
    abs_pair_block_means_le hX y hk hh₁ hh₂ hσ hσm (hdep.trans hmono) hcase' (hy m hm)⟩

/-- The one-point tilted means of the post blocks are at most `1.52` in size, from `k ≥ 20`
(`RMF.abs_window_block_means_le`). -/
lemma abs_windowMeanH_post_le_floor (hX : IsRademacherPrimeValues X μ) {k b n y : ℕ} {σ h : ℝ}
    (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσn : σ * Real.exp ((k : ℝ) + (b + n)) ≤ 1 / 200)
    (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y) {i : ℕ} (hi : i < n) :
    |windowMeanH X μ y k σ h (i + b)| ≤ 1.52 := by
  have hσi : σ * Real.exp ((k : ℝ) + ((i + b : ℕ) : ℝ) + 1) ≤ 1 / 200 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hσ) hσn
    have : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hi
    push_cast
    linarith
  exact (abs_window_block_means_le hX y hk hh hσ hσi (hy i hi)).1

set_option maxHeartbeats 1000000 in
-- the comparison, its re-indexing and the summed-variance pair ballot in one proof
/-- **HP2's post part at a given start, in sums, from `k ≥ 20`.**  For tube parameters
`a, A, B, ρ ≥ 0` summing to at most `100`, starts `zᵢ ∈ [-A - Bb - ρ, a + ρ]` and pushes `Pᵢ`, the
two post tubes have two-fold tilted probability at most
`(1 + e^{-100})√(2/(π(∑V₁ - v₊)))√(2/(π∑R))((Y₁ + c)(Y₂ + c) + K((Y₁ + c)√v₊ + v₊))`,
`Yᵢ = max(a + ρ - zᵢ, 0) + 2e^{-40} + Pᵢ`, with `R` the residual variances `RMF.pairResidVar` and
`K` the summed slopes `|RMF.pairSlope|`: the comparison
`RMF.exists_isBoxComparison_rademacher_budget₂` at offset `k + b` (envelope `770(b + m + 1)`,
budget `RMF.hp2Post_budget`), the barriers inside `200(b + j + 1)`, then
`RMF.measureReal_barrierEventPair_le_of_boxComparison_sum`. -/
theorem tiltedMeasure₂_hp2PostTube_le_sum_floor (hX : IsRademacherPrimeValues X μ) {k b n y : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσn : σ * Real.exp ((k : ℝ) + (b + n)) ≤ 1 / 200)
    (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y)
    (hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b))
    (hcase : 4 ≤ b ∨ (2 ≤ b ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b))) (hn : 2 ≤ n)
    {a A B ρ z₁ z₂ : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (henv : a + A + B + ρ ≤ 100)
    (hz₁ : -A - B * b - ρ ≤ z₁ ∧ z₁ ≤ a + ρ) (hz₂ : -A - B * b - ρ ≤ z₂ ∧ z₂ ≤ a + ρ)
    {vmax c P₁ P₂ : ℝ}
    (hv₁ : ∀ m, m < n → pairVarH X μ y k σ h₁ h₂ h₁ (m + b) ≤ vmax)
    (hv₂ : ∀ m, m < n → pairVarH X μ y k σ h₁ h₂ h₂ (m + b) ≤ vmax)
    (hsum : vmax < ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
    (hc0 : 0 < c) (hc : √(π * vmax / 2) ≤ c)
    (hP₁ : ∀ j, j ≤ n → -∑ i ∈ Finset.range j,
      (pairMeanH X μ y k σ h₁ h₂ h₁ (i + b) - windowMeanH X μ y k σ h₁ (i + b)) ≤ P₁)
    (hP₂ : ∀ j, j ≤ n → -∑ i ∈ Finset.range j,
      (pairMeanH X μ y k σ h₁ h₂ h₂ (i + b) - windowMeanH X μ y k σ h₂ (i + b)) ≤ P₂) :
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ).real
        (hp2PostTube X μ y k b n σ h₁ a A B ρ z₁ ∩ hp2PostTube X μ y k b n σ h₂ a A B ρ z₂)
      ≤ (1 + Real.exp (-100)) * (√(2 / (π * (∑ m ∈ Finset.range n,
            pairVarH X μ y k σ h₁ h₂ h₁ (m + b) - vmax)))
          * √(2 / (π * ∑ m ∈ Finset.range n, pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
              (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b))))
          * ((max (a + ρ - z₁) 0 + 2 * Real.exp (-40) + P₁ + c)
              * (max (a + ρ - z₂) 0 + 2 * Real.exp (-40) + P₂ + c)
            + (∑ m ∈ Finset.range n, |pairSlope (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
                (pairCovH X μ y k σ h₁ h₂ (m + b))|)
              * ((max (a + ρ - z₁) 0 + 2 * Real.exp (-40) + P₁ + c) * √vmax + vmax))) := by
  classical
  /- basic facts -/
  have hk' : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs₁ : 0 < (shiftLine σ h₁).re := by rw [re_shiftLine]; linarith
  have hs₂ : 0 < (shiftLine σ h₂).re := by rw [re_shiftLine]; linarith
  haveI := isProbabilityMeasure_tiltedMeasure₂_rademacher hX y hs₁ hs₂
  have hb2 : 2 ≤ b := by
    rcases hcase with h | h
    · omega
    · exact h.1
  have hθ : (20 : ℝ) ≤ (k : ℝ) + b := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have hθb : 20 + (b : ℝ) ≤ (k : ℝ) + b := by linarith
  have hyθ : ∀ m, m < n → primeBlockSub ((k : ℝ) + b) m ⊆ primesBelowSub y := fun m hm => by
    rw [← primeBlockSub_add]; exact hy m hm
  have hin := fun m (hm : m < n) =>
    hp2Post_comparison_inputs_floor hX hk hh₁ hh₂ hσ hσn hy hdep hcase hm
  have hσtop : |σ| * Real.log (blockScale ((k : ℝ) + b) n) ≤ 1 := by
    rw [abs_of_nonneg hσ, log_blockScale, show (n : ℝ) + ((k : ℝ) + b) = (k : ℝ) + (b + n) by
      ring]
    linarith
  /- the windows `e^{-40}/(m+1)²` -/
  have hwpos : ∀ m, 0 < Real.exp (-40) * blockWindow m := fun m => by
    unfold blockWindow; positivity
  have hwle : ∀ m : ℕ, Real.exp (-40) * blockWindow m ≤ 1 := by
    intro m
    have h1 : Real.exp (-40) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have h2 : blockWindow m ≤ 1 := by
      unfold blockWindow
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      nlinarith
    have h3 : 0 ≤ blockWindow m := by unfold blockWindow; positivity
    calc Real.exp (-40) * blockWindow m ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
      _ = 1 := one_mul 1
  have hwsum : ∀ j, j ≤ n →
      ∑ m ∈ Finset.range j, Real.exp (-40) * blockWindow m ≤ 2 * Real.exp (-40) :=
    fun j _ => by
      have := sum_mul_blockWindow_le (Real.exp_pos (-40)).le 0 j
      simpa only [add_zero] using this
  /- the comparison at offset `k + b` -/
  obtain ⟨Ω', mΩ', Q, N, hQ, hNm, hNi, hNlaw, hcmpk⟩ :=
    exists_isBoxComparison_rademacher_budget₂ hX (θ := (k : ℝ) + b) (σ := σ)
      (vl := 0.3649) (vu := 0.6551) (K := 1.93) (r := n) (y := y)
      (s₁ := shiftLine σ h₁) (s₂ := shiftLine σ h₂)
      (w := fun m => Real.exp (-40) * blockWindow m)
      (M := fun m => 770 * ((b : ℝ) + m + 1)) (δ := fun m => pairBlockDet (m + b))
      hθ hyθ (re_shiftLine σ h₁) (re_shiftLine σ h₂) hσtop
      (fun m _ => ⟨hwpos m, hwle m⟩) (by norm_num) (by norm_num)
      (fun m hm => by rw [← primeBlockSub_add]; exact (hin m hm).1.1)
      (fun m hm => by rw [← primeBlockSub_add]; exact (hin m hm).1.2.1)
      (fun m _ => lt_of_lt_of_le (by norm_num) (le_pairBlockDet (m + b)))
      (fun m hm => by rw [← primeBlockSub_add]; exact (hin m hm).1.2.2)
      (fun m hm => by rw [← primeBlockSub_add]; exact (hin m hm).2)
      (fun m _ => hp2Post_budget hb2 hθb (by norm_num) le_rfl m)
  haveI := hQ
  have hcmp0 : IsBoxComparison
      (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ) Q
      (fun m ω => (halfBlock X ((k : ℝ) + b) σ h₁ m ω, halfBlock X ((k : ℝ) + b) σ h₂ m ω)) N
      (fun m => Real.exp (-40) * blockWindow m) (fun m => 770 * ((b : ℝ) + m + 1)) n
      (Real.exp (-100)) := by
    have h0 := hcmpk 0 (Nat.zero_le n)
    have hZeq : (fun m ω => ∑ p ∈ primeBlockSub ((k : ℝ) + b) (m + 0),
        (localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₁))) (X (p : ℕ) ω),
          localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ h₂))) (X (p : ℕ) ω)))
        = fun m ω => (halfBlock X ((k : ℝ) + b) σ h₁ m ω, halfBlock X ((k : ℝ) + b) σ h₂ m ω) := by
      funext m ω
      rw [add_zero]
      exact Prod.ext Prod.fst_sum Prod.snd_sum
    rw [hZeq] at h0
    simpa only [add_zero, Nat.sub_zero] using h0
  /- the block laws, re-indexed to offset `k` -/
  have hlaw : ∀ m, m < n → Q.map (N m) = gaussianPairLaw (pairMeanH X μ y k σ h₁ h₂ h₁ (m + b))
      (pairMeanH X μ y k σ h₁ h₂ h₂ (m + b)) (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
      (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b)) := fun m hm => by
    rw [hNlaw m hm]
    simp only [pairMeanH, pairVarH, pairCovH, primeBlockSub_add]
  /- the variances -/
  have hvpos₁ : ∀ m, m < n → 0 < pairVarH X μ y k σ h₁ h₂ h₁ (m + b) := fun m hm =>
    lt_of_lt_of_le (by norm_num) (hin m hm).1.1.1
  have hvpos₂ : ∀ m, m < n → 0 < pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
      (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b)) := by
    intro m hm
    have hdet := (hin m hm).1.2.2
    have hd0 := le_pairBlockDet (m + b)
    rw [pairResidVar, sub_pos, div_lt_iff₀ (hvpos₁ m hm)]
    nlinarith [hdet]
  have hvhi₂ : ∀ m, m < n → pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
      (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b)) ≤ vmax := by
    intro m hm
    rw [pairResidVar]
    have : 0 ≤ pairCovH X μ y k σ h₁ h₂ (m + b) ^ 2 / pairVarH X μ y k σ h₁ h₂ h₁ (m + b) :=
      div_nonneg (sq_nonneg _) (hvpos₁ m hm).le
    linarith [hv₂ m hm]
  /- the envelopes -/
  have hsum152 : ∀ (h : ℝ), h ∈ halfWindow k → ∀ j : ℕ, j ≤ n →
      |∑ i ∈ Finset.range j, windowMeanH X μ y k σ h (i + b)| ≤ 1.52 * j := by
    intro h hh j hj
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun i hi =>
      abs_windowMeanH_post_le_floor hX hk hh hσ hσn hy
        (by have := Finset.mem_range.1 hi; omega)) (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hM0 : ∀ j : ℕ, 0 ≤ 200 * ((b : ℝ) + j + 1) := fun j => by positivity
  have hM₁ : ∀ j, 1 ≤ j → j ≤ n → -(200 * ((b : ℝ) + j + 1))
        ≤ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₁ (i + b) - A - B * ((b : ℝ) + j) - ρ - z₁
      ∧ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₁ (i + b) + a + ρ - z₁
        ≤ 200 * ((b : ℝ) + j + 1) := fun j _ hj =>
    hp2Post_envelope_floor (hsum152 h₁ hh₁ j hj) ha hA hB hρ henv hz₁
  have hM₂ : ∀ j, 1 ≤ j → j ≤ n → -(200 * ((b : ℝ) + j + 1))
        ≤ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₂ (i + b) - A - B * ((b : ℝ) + j) - ρ - z₂
      ∧ ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₂ (i + b) + a + ρ - z₂
        ≤ 200 * ((b : ℝ) + j + 1) := fun j _ hj =>
    hp2Post_envelope_floor (hsum152 h₂ hh₂ j hj) ha hA hB hρ henv hz₂
  have hMM : ∀ m, m < n → 200 * ((b : ℝ) + m + 1)
      + 200 * ((b : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) + Real.exp (-40) * blockWindow m
      ≤ 770 * ((b : ℝ) + m + 1) :=
    fun m _ => hp2Post_envelope_le_floor (hwle m)
  /- the ceilings minus the two-fold drifts -/
  have hP₁0 : 0 ≤ P₁ := by simpa using hP₁ 0 (Nat.zero_le n)
  have hP₂0 : 0 ≤ P₂ := by simpa using hP₂ 0 (Nat.zero_le n)
  have hY₁0 : 0 ≤ max (a + ρ - z₁) 0 + 2 * Real.exp (-40) + P₁ := by
    have := le_max_right (a + ρ - z₁) 0
    positivity
  have hY₂0 : 0 ≤ max (a + ρ - z₂) 0 + 2 * Real.exp (-40) + P₂ := by
    have := le_max_right (a + ρ - z₂) 0
    positivity
  have hY₁ : ∀ j, 1 ≤ j → j ≤ n →
      ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₁ (i + b) + a + ρ - z₁ + 2 * Real.exp (-40)
        - ∑ m ∈ Finset.range j, pairMeanH X μ y k σ h₁ h₂ h₁ (m + b)
      ≤ max (a + ρ - z₁) 0 + 2 * Real.exp (-40) + P₁ := by
    intro j _ hj
    have h1 := hP₁ j hj
    rw [Finset.sum_sub_distrib] at h1
    have h2 := le_max_left (a + ρ - z₁) 0
    linarith
  have hY₂ : ∀ j, 1 ≤ j → j ≤ n →
      ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₂ (i + b) + a + ρ - z₂ + 2 * Real.exp (-40)
        - ∑ m ∈ Finset.range j, pairMeanH X μ y k σ h₁ h₂ h₂ (m + b)
      ≤ max (a + ρ - z₂) 0 + 2 * Real.exp (-40) + P₂ := by
    intro j _ hj
    have h1 := hP₂ j hj
    rw [Finset.sum_sub_distrib] at h1
    have h2 := le_max_left (a + ρ - z₂) 0
    linarith
  /- the summed-variance pair ballot through the comparison -/
  have hmain := measureReal_barrierEventPair_le_of_boxComparison_sum
    (P := tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
      (shiftLine σ h₂) μ) (Q := Q)
    (Z := fun m ω => (halfBlock X ((k : ℝ) + b) σ h₁ m ω, halfBlock X ((k : ℝ) + b) σ h₂ m ω))
    (N := N) (w := fun m => Real.exp (-40) * blockWindow m)
    (M := fun j => 200 * ((b : ℝ) + j + 1))
    (M' := fun m => 770 * ((b : ℝ) + m + 1))
    (r := n) (ε := Real.exp (-100)) (ρ := 2 * Real.exp (-40))
    (m₁ := fun m => pairMeanH X μ y k σ h₁ h₂ h₁ (m + b))
    (m₂ := fun m => pairMeanH X μ y k σ h₁ h₂ h₂ (m + b))
    (V₁ := fun m => pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
    (V₂ := fun m => pairVarH X μ y k σ h₁ h₂ h₂ (m + b))
    (cv := fun m => pairCovH X μ y k σ h₁ h₂ (m + b)) (vmax := vmax) (c := c)
    (u₁ := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₁ (i + b) - A - B * ((b : ℝ) + j)
      - ρ - z₁)
    (v₁ := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₁ (i + b) + a + ρ - z₁)
    (u₂ := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₂ (i + b) - A - B * ((b : ℝ) + j)
      - ρ - z₂)
    (v₂ := fun j => ∑ i ∈ Finset.range j, windowMeanH X μ y k σ h₂ (i + b) + a + ρ - z₂)
    (Y₁ := max (a + ρ - z₁) 0 + 2 * Real.exp (-40) + P₁)
    (Y₂ := max (a + ρ - z₂) 0 + 2 * Real.exp (-40) + P₂)
    (fun m => (measurable_halfBlock hX _ _ _ m).prodMk (measurable_halfBlock hX _ _ _ m))
    hNm hNi hlaw hvpos₁ hv₁ hvpos₂ hvhi₂ hsum hc0 hc hn hwpos hwsum hM0 hM₁ hM₂
    (Real.exp_pos _).le hMM hcmp0 hY₁0 hY₂0 hY₁ hY₂
  exact hmain

end Chain

/-! ### The block cosine sums of a pair, by tiers, from `k ≥ 20`

The tiers `RMF.diffTier`, `RMF.sumTier` with the per-block error `RMF.blockCosErrDecay` added: the
certified ranges of the first blocks absorb the error (`7.43·10⁻⁸ + 1/100 ≤ 0.0101`), the decaying
tails carry it. -/

section Tiers

/-- **A certified range at the difference frequency, transferred, from `k ≥ 20`**: if
`blockCos ξ i ∈ [lo, hi]` for every `ξ ∈ [-1, 0]`, then `C_{d+i}(D) ∈ [lo - 0.0101, hi + 0.0101]`
at depth `d` for `σe^{k+d+i+1} ≤ 1/200` (`RMF.blockCosSum_mem_of_blockCos`, error
`≤ 7.43·10⁻⁸`). -/
lemma blockCosSum_diff_mem_floor {k d i : ℕ} {σ D lo hi : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + ((d + i : ℕ) : ℝ) + 1) ≤ 1 / 200)
    (hd1 : Real.exp (-1) ≤ |D| * Real.exp ((k : ℝ) + d))
    (hd2 : |D| * Real.exp ((k : ℝ) + d) ≤ 1)
    (hb : ∀ ξ : ℝ, -1 ≤ ξ → ξ ≤ 0 → lo ≤ blockCos ξ i ∧ blockCos ξ i ≤ hi) :
    lo - 0.0101 ≤ blockCosSum k σ D (d + i) ∧ blockCosSum k σ D (d + i) ≤ hi + 0.0101 := by
  obtain ⟨hD0, ha1, ha2⟩ := depth_phase_mem hd1 hd2
  have hD := abs_le_two_exp_neg_twenty_of_depth hk hd2
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hrw : blockCos (Real.log |D| + k) (d + i)
      = blockCos ((d : ℝ) + (Real.log |D| + k)) i := by
    rw [blockCos_eq_zero, blockCos_eq_zero ((d : ℝ) + (Real.log |D| + k)) i]
    congr 1
    push_cast
    ring
  have hδ : 2 * σ * Real.exp ((k : ℝ) + ((d + i : ℕ) : ℝ) + 1) ≤ 1 / 100 := by linarith
  have herr : blockCosErr k (d + i) |D| ≤ 7.43 / 10 ^ 8 :=
    blockCosErr_le_numeral (by linarith [Nat.cast_nonneg (α := ℝ) (d + i)]) hD
  have h := blockCosSum_mem_of_blockCos (lo := lo) (hi := hi) hσ hD0 hδ
    (by rw [hrw]; exact hb _ ha1 ha2)
  rw [blockCosSum_abs] at h
  have h3 : (7.43 : ℝ) / 10 ^ 8 + 1 / 100 ≤ 0.0101 := by norm_num
  constructor <;> linarith [h.1, h.2]

/-- **The difference frequency past the transition, two regimes**: at depth `d`,
`|C_{d+i}(D)| ≤ 3e^{1-i} + blockCosErrDecay k (d + i) |D|`
(`RMF.abs_sum_cos_primeBlockSub_le_explicit_floor_decay_two_regime`, `|D|e^{k+d+i} ≥ e^{i-1}`). -/
lemma abs_blockCosSum_diff_le_decay_two_regime {k d i : ℕ} {σ D : ℝ} (hσ : 0 ≤ σ)
    (hd1 : Real.exp (-1) ≤ |D| * Real.exp ((k : ℝ) + d)) :
    |blockCosSum k σ D (d + i)| ≤ 3 * Real.exp (1 - i) + blockCosErrDecay k (d + i) |D| := by
  have hD0 : 0 < |D| := by
    rcases (abs_nonneg D).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hd1
      exact absurd hd1 (not_le.2 (Real.exp_pos _))
  rw [← blockCosSum_abs]
  have h := abs_sum_cos_primeBlockSub_le_explicit_floor_decay_two_regime |D| σ k (d + i) hD0 hσ
    (by positivity)
  have hprod : Real.exp ((i : ℝ) - 1) ≤ |D| * Real.exp (((d + i : ℕ) : ℝ) + k) := by
    calc Real.exp ((i : ℝ) - 1) = Real.exp (-1) * Real.exp (i : ℝ) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ |D| * Real.exp ((k : ℝ) + d) * Real.exp (i : ℝ) :=
          mul_le_mul_of_nonneg_right hd1 (Real.exp_pos _).le
      _ = |D| * Real.exp (((d + i : ℕ) : ℝ) + k) := by
          rw [mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf
  have h1 : 3 / (|D| * Real.exp (((d + i : ℕ) : ℝ) + k)) ≤ 3 * Real.exp (1 - i) := by
    rw [div_le_iff₀ (by positivity)]
    have he : Real.exp (1 - (i : ℝ)) * Real.exp ((i : ℝ) - 1) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (3 : ℝ) = 3 * Real.exp (1 - i) * Real.exp ((i : ℝ) - 1) := by
          rw [mul_assoc, he, mul_one]
      _ ≤ 3 * Real.exp (1 - i) * (|D| * Real.exp (((d + i : ℕ) : ℝ) + k)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  unfold blockCosSum
  linarith

/-- **A sum frequency's block sum decays, two regimes**: for `2e^{-(k+1)} ≤ τ`,
`|C_m(τ)| ≤ 1.5e^{1-m} + blockCosErrDecay k m τ`. -/
lemma abs_blockCosSum_sum_le_decay_two_regime {k m : ℕ} {σ τ : ℝ} (hσ : 0 ≤ σ)
    (hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ τ) :
    |blockCosSum k σ τ m| ≤ 1.5 * Real.exp (1 - m) + blockCosErrDecay k m τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have h := abs_sum_cos_primeBlockSub_le_explicit_floor_decay_two_regime τ σ k m hτ0 hσ
    (by positivity)
  have hprod : 2 * Real.exp ((m : ℝ) - 1) ≤ τ * Real.exp ((m : ℝ) + k) := by
    calc 2 * Real.exp ((m : ℝ) - 1) = 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp ((m : ℝ) + k) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf
      _ ≤ τ * Real.exp ((m : ℝ) + k) := mul_le_mul_of_nonneg_right hτ1 (Real.exp_pos _).le
  have h1 : 3 / (τ * Real.exp ((m : ℝ) + k)) ≤ 1.5 * Real.exp (1 - m) := by
    rw [div_le_iff₀ (by positivity)]
    have he : Real.exp (1 - (m : ℝ)) * Real.exp ((m : ℝ) - 1) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (3 : ℝ) = 1.5 * Real.exp (1 - m) * (2 * Real.exp ((m : ℝ) - 1)) := by
          rw [show 1.5 * Real.exp (1 - m) * (2 * Real.exp ((m : ℝ) - 1))
            = 3 * (Real.exp (1 - (m : ℝ)) * Real.exp ((m : ℝ) - 1)) by ring, he, mul_one]
      _ ≤ 1.5 * Real.exp (1 - m) * (τ * Real.exp ((m : ℝ) + k)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  unfold blockCosSum
  linarith

/-- **Every block of the difference frequency by its tier, from `k ≥ 20`**: at depth `d`, for
`σe^{k+d+i+1} ≤ 1/200`, `|C_{d+i}(D)| ≤ diffTier i + blockCosErrDecay k (d + i) |D|`. -/
lemma abs_blockCosSum_diff_le_tier_floor {k d i : ℕ} {σ D : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + ((d + i : ℕ) : ℝ) + 1) ≤ 1 / 200)
    (hd1 : Real.exp (-1) ≤ |D| * Real.exp ((k : ℝ) + d))
    (hd2 : |D| * Real.exp ((k : ℝ) + d) ≤ 1) :
    |blockCosSum k σ D (d + i)| ≤ diffTier i + blockCosErrDecay k (d + i) |D| := by
  have he : 0 ≤ blockCosErrDecay k (d + i) |D| := blockCosErrDecay_nonneg _ (abs_nonneg D)
  have hmem := fun {lo hi : ℝ} (hb : ∀ ξ : ℝ, -1 ≤ ξ → ξ ≤ 0 → lo ≤ blockCos ξ i
      ∧ blockCos ξ i ≤ hi) => blockCosSum_diff_mem_floor hk hσ hσm hd1 hd2 hb
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with h | h | h | h | h
  · subst h
    have := hmem fun ξ h1 h2 => blockCos_zero_bounds_one_point h1 h2
    rw [abs_le]
    simp only [diffTier, if_true]
    constructor <;> linarith [this.1, this.2]
  · subst h
    have := hmem fun ξ h1 h2 => blockCos_one_bounds_one_point h1 h2
    rw [abs_le]
    simp only [diffTier, one_ne_zero, if_false, if_true]
    constructor <;> linarith [this.1, this.2]
  · subst h
    have := hmem fun ξ h1 h2 => blockCos_two_bounds_one_point h1 h2
    rw [abs_le]
    simp only [diffTier, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, if_true]
    constructor <;> linarith [this.1, this.2]
  · subst h
    have := hmem fun ξ h1 h2 => blockCos_three_bounds_one_point h1 h2
    rw [abs_le]
    simp only [diffTier, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
      show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true]
    constructor <;> linarith [this.1, this.2]
  · have hdiff : diffTier i = 3 * Real.exp (1 - i) := by
      simp only [diffTier, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
        show i ≠ 3 by omega, if_false]
    rw [hdiff]
    exact abs_blockCosSum_diff_le_decay_two_regime hσ hd1

/-- **Every post block of a sum frequency by its tier, from `k ≥ 20`**: for
`2e^{-(k+1)} ≤ τ ≤ 2e^{-k}`, `m ≥ 2` and `σe^{k+m+1} ≤ 1/200`,
`|C_m(τ)| ≤ sumTier m + blockCosErrDecay k m τ`. -/
lemma abs_blockCosSum_sum_le_tier_floor {k m : ℕ} {σ τ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) (hm : 2 ≤ m)
    (hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ τ) (hτ2 : τ ≤ 2 * Real.exp (-(k : ℝ))) :
    |blockCosSum k σ τ m| ≤ sumTier m + blockCosErrDecay k m τ := by
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ1
  have he : 0 ≤ blockCosErrDecay k m τ := blockCosErrDecay_nonneg _ hτ0
  have hb := blockCosSum_sum_bounds hk hσ hσm hτ1 hτ2
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with h | h | h
  · obtain ⟨h1, h2⟩ := hb.2.2 h
    subst h
    rw [abs_le]
    simp only [sumTier, if_true]
    constructor <;> linarith
  · have h1 := hb.2.1 h
    subst h
    simp only [sumTier, show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true]
    linarith
  · have hs : sumTier m = 1.5 * Real.exp (1 - m) := by
      simp only [sumTier, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
    rw [hs]
    exact abs_blockCosSum_sum_le_decay_two_regime hσ hτ1

/-- **A telescoped sum frequency, from `k ≥ 20`**: for `2e^{-(k+1)} ≤ τ ≤ 2e^{-k}` and any start
`b`, `|∑_{i<j} C_{i+b}(τ)| ≤ e^{1-b} + 3.16·10⁻⁶` (`RMF.abs_sum_blockCosSum_le`,
`RMF.blockCosTelErr_le_numeral`). -/
lemma abs_sum_blockCosSum_sum_le_floor {k b j : ℕ} {σ τ : ℝ} (hk : 20 ≤ k) (hσ : 0 ≤ σ)
    (hτ1 : 2 * Real.exp (-((k : ℝ) + 1)) ≤ τ) (hτ2 : τ ≤ 2 * Real.exp (-(k : ℝ))) :
    |∑ i ∈ Finset.range j, blockCosSum k σ τ (i + b)| ≤ Real.exp (1 - b) + 3.16 / 10 ^ 6 := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ1
  have hIco : ∑ i ∈ Finset.range j, blockCosSum k σ τ (i + b)
      = ∑ m ∈ Finset.Ico b (b + j), blockCosSum k σ τ m := by
    rw [Finset.sum_Ico_eq_sum_range, show b + j - b = j by omega]
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm i b]
  rw [hIco]
  have h := abs_sum_blockCosSum_le (τ := τ) (σ := σ) (θ := k) (m₁ := b) (M := b + j) (by omega)
    hτ0 hσ (by positivity)
  have h3 := blockCosTelErr_le_numeral (θ := k) (m₁ := b)
    (by linarith [Nat.cast_nonneg (α := ℝ) b]) hτ0.le (le_two_exp_neg_twenty_of_le hk hτ2)
  have hξ : Real.log 2 - 1 ≤ Real.log τ + k := by
    have h1 := Real.log_le_log (by positivity) hτ1
    rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith
  have h1 : 2 * Real.exp (-((b : ℝ) + (Real.log τ + k))) ≤ Real.exp (1 - b) := by
    have he : Real.exp (-((b : ℝ) + (Real.log τ + k))) ≤ Real.exp (-((b : ℝ) + (Real.log 2 - 1))) :=
      Real.exp_le_exp.2 (by linarith)
    have he2 : Real.exp (-((b : ℝ) + (Real.log 2 - 1))) = Real.exp (1 - b) / 2 := by
      rw [show -((b : ℝ) + (Real.log 2 - 1)) = (1 - b) + -Real.log 2 by ring, Real.exp_add,
        Real.exp_neg, Real.exp_log two_pos]
      ring
    linarith
  linarith

end Tiers

/-! ### The post blocks' two-fold statistics, from `k ≥ 20` -/

section PostData

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The two-fold variances by tiers, from `k ≥ 20`**: for `h ∈ halfWindow k` and a block `m ≥ 2`
with `σe^{k+m+1} ≤ 1/200` below the cutoff, `varLoTier m ≤ pairVarH … h m ≤ varHiTier m`. -/
lemma pairVarH_mem_tier_floor (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k m : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσm : σ * Real.exp ((k : ℝ) + m + 1) ≤ 1 / 200) (hm : 2 ≤ m)
    (hB : primeBlockSub k m ⊆ primesBelowSub y) :
    varLoTier m ≤ pairVarH X μ y k σ h₁ h₂ h m ∧ pairVarH X μ y k σ h₁ h₂ h m ≤ varHiTier m := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hV := abs_le.1 (abs_blockMatchedVarAdd₂_sub_le_decay hX y (h₁ := h₁) (h₂ := h₂) (h := h)
    hσ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m]) hB)
  have hS1 := (blockRpowSum_bounds hk hσ hσm).1
  have hS2 := blockRpowSum_le (θ := k) (m := m) hσ (by linarith [Nat.cast_nonneg (α := ℝ) m])
  obtain ⟨hh1, hh2⟩ := hh
  have hC := blockCosSum_sum_bounds (τ := 2 * h) hk hσ hσm (by linarith) (by linarith)
  have hε : Real.exp (-(m : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by simp)) (by positivity)
  have hε0 : 0 ≤ Real.exp (-(m : ℝ)) / 10 ^ 20 := by positivity
  unfold pairVarH
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with h2 | h3 | h4
  · obtain ⟨c1, c2⟩ := hC.2.2 h2
    subst h2
    simp only [varLoTier, varHiTier, if_true]
    constructor <;> linarith
  · have c := abs_le.1 (hC.2.1 h3)
    subst h3
    simp only [varLoTier, varHiTier, show (3 : ℕ) ≠ 2 by norm_num, if_false, if_true]
    constructor <;> linarith [c.1, c.2]
  · have c := abs_le.1 (hC.1 h4)
    simp only [varLoTier, varHiTier, show m ≠ 2 by omega, show m ≠ 3 by omega, if_false]
    constructor <;> linarith [c.1, c.2]

/-- **The two-fold variances summed over the post blocks, from `k ≥ 20`**: for `h ∈ halfWindow k`,
`∑_{m<n} V_{m+b}(h) ≥ 0.495n - e^{1-b}/2 - 1.6·10⁻⁶` (`S ≥ 0.99` per block, the telescoped
`∑C_m(2h)`, `RMF.abs_sum_blockCosSum_sum_le_floor`). -/
lemma sum_pairVarH_ge_floor (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k b n : ℕ}
    {σ h₁ h₂ h : ℝ} (hk : 20 ≤ k) (hh : h ∈ halfWindow k) (hσ : 0 ≤ σ)
    (hσn : σ * Real.exp ((k : ℝ) + (b + n)) ≤ 1 / 200)
    (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y) :
    0.495 * n - (Real.exp (1 - b) / 2 + 1.6 / 10 ^ 6)
      ≤ ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h (m + b) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hh1, hh2⟩ := hh
  have hterm : ∀ m ∈ Finset.range n, 0.495 + blockCosSum k σ (2 * h) (m + b) / 2
      - Real.exp (-((m + b : ℕ) : ℝ)) / 10 ^ 20 ≤ pairVarH X μ y k σ h₁ h₂ h (m + b) := by
    intro m hm
    have hmn := Finset.mem_range.1 hm
    have hσm : σ * Real.exp ((k : ℝ) + ((m + b : ℕ) : ℝ) + 1) ≤ 1 / 200 := by
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hσ) hσn
      have : ((m : ℝ) + 1) ≤ n := by exact_mod_cast hmn
      push_cast
      linarith
    have hV := abs_le.1 (abs_blockMatchedVarAdd₂_sub_le_decay hX y (h₁ := h₁) (h₂ := h₂)
      (h := h) (m := m + b) hσ (by positivity)
      (by linarith [Nat.cast_nonneg (α := ℝ) (m + b)]) (hy m hmn))
    have hS1 := (blockRpowSum_bounds hk hσ hσm).1
    unfold pairVarH
    linarith [hV.1]
  have hC := abs_le.1 (abs_sum_blockCosSum_sum_le_floor (j := n) (b := b) hk hσ
    (τ := 2 * h) (by linarith) (by linarith))
  have hE : ∑ m ∈ Finset.range n, Real.exp (-((m + b : ℕ) : ℝ)) / 10 ^ 20 ≤ 1.59 / 10 ^ 20 := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (sum_exp_neg_add_le b n) (by positivity)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.sum_div] at hsum
  have h5 : (3.16 : ℝ) / 10 ^ 6 / 2 + 1.59 / 10 ^ 20 ≤ 1.6 / 10 ^ 6 := by norm_num
  nlinarith [hC.1]

end PostData

/-! ### The pair's push against the one-point centring, from `k ≥ 20` -/

section Push

/-- **Summing the push, from `k ≥ 20`**: if every term `fᵢ` is at least
`gᵢ + sᵢ - 2e^{-(i+b)}/10²⁰`, where `-∑_{i<j} gᵢ ≤ P_D` and `|∑_{i<j} sᵢ| ≤ e^{1-b} + 3.16·10⁻⁶`,
then `-∑_{i<j} fᵢ ≤ P_D + e^{1-b} + 3.2·10⁻⁶`. -/
lemma neg_sum_le_of_terms_floor {f g s : ℕ → ℝ} {b j : ℕ} {PD : ℝ}
    (hterm : ∀ i ∈ Finset.range j, g i + s i - 2 * (Real.exp (-((i + b : ℕ) : ℝ)) / 10 ^ 20) ≤ f i)
    (hg : -∑ i ∈ Finset.range j, g i ≤ PD)
    (hs : |∑ i ∈ Finset.range j, s i| ≤ Real.exp (1 - b) + 3.16 / 10 ^ 6) :
    -∑ i ∈ Finset.range j, f i ≤ PD + Real.exp (1 - b) + 3.2 / 10 ^ 6 := by
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
  have hE := sum_exp_neg_add_le b j
  have hs' := (abs_le.1 hs).1
  have h1 : 2 * ((∑ i ∈ Finset.range j, Real.exp (-((i + b : ℕ) : ℝ))) / 10 ^ 20)
      ≤ 2 * (1.59 / 10 ^ 20) := by gcongr
  have h5 : (3.16 : ℝ) / 10 ^ 6 + 2 * (1.59 / 10 ^ 20) ≤ 3.2 / 10 ^ 6 := by norm_num
  linarith

end Push

/-! ### The push of both walks, from `k ≥ 20` -/

section PushWalks

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The pair's push against the one-point centring, both walks, from `k ≥ 20`**: a bound `P_D`
on the difference frequency's negative partial sums gives, for both walks,
`-∑_{i<j}(pairMeanH - windowMeanH)(i + b) ≤ P_D + e^{1-b} + 3.2·10⁻⁶` for every `j ≤ n` (the sum
frequency by `RMF.abs_sum_blockCosSum_sum_le_floor`). -/
lemma hp2Post_push_le_floor (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k b n : ℕ}
    {σ h₁ h₂ PD : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y)
    (hPD : ∀ j, j ≤ n → -∑ i ∈ Finset.range j, blockCosSum k σ (h₁ - h₂) (i + b) ≤ PD) :
    (∀ j, j ≤ n → -∑ i ∈ Finset.range j, (pairMeanH X μ y k σ h₁ h₂ h₁ (i + b)
        - windowMeanH X μ y k σ h₁ (i + b)) ≤ PD + Real.exp (1 - b) + 3.2 / 10 ^ 6)
      ∧ (∀ j, j ≤ n → -∑ i ∈ Finset.range j, (pairMeanH X μ y k σ h₁ h₂ h₂ (i + b)
        - windowMeanH X μ y k σ h₂ (i + b)) ≤ PD + Real.exp (1 - b) + 3.2 / 10 ^ 6) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hS := fun (j : ℕ) => abs_sum_blockCosSum_sum_le_floor (j := j) (b := b) (τ := h₁ + h₂) hk
    hσ (by linarith) (by linarith)
  have hm : ∀ i : ℕ, 20 ≤ ((i + b : ℕ) : ℝ) + k := fun i => by
    linarith [Nat.cast_nonneg (α := ℝ) (i + b)]
  refine ⟨fun j hj => neg_sum_le_of_terms_floor (fun i hi => ?_) (hPD j hj) (hS j),
    fun j hj => neg_sum_le_of_terms_floor (fun i hi => ?_) (hPD j hj) (hS j)⟩
  · have hB := hy i (by have := Finset.mem_range.1 hi; omega)
    have h1 := abs_le.1 (abs_blockMeanAdd₂_fst_sub_le_decay hX y (θ := k) (σ := σ) (h₁ := h₁)
      (h₂ := h₂) (m := i + b) hσ (by positivity) (hm i) hB)
    have h2 := abs_le.1 (abs_blockMeanAdd_height_sub_le_decay hX y (θ := k) (σ := σ) (h := h₁)
      (m := i + b) hσ (by positivity) (hm i) hB)
    unfold pairMeanH windowMeanH
    linarith [h1.1, h2.2]
  · have hB := hy i (by have := Finset.mem_range.1 hi; omega)
    have h1 := abs_le.1 (abs_blockMeanAdd₂_snd_sub_le_decay hX y (θ := k) (σ := σ) (h₁ := h₁)
      (h₂ := h₂) (m := i + b) hσ (by positivity) (hm i) hB)
    have h2 := abs_le.1 (abs_blockMeanAdd_height_sub_le_decay hX y (θ := k) (σ := σ) (h := h₂)
      (m := i + b) hσ (by positivity) (hm i) hB)
    unfold pairMeanH windowMeanH
    linarith [h1.1, h2.2]

end PushWalks

/-! ### The post bound in the product form, from `k ≥ 20` -/

section Cpost

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

set_option maxHeartbeats 1000000 in
-- the chain theorem, the variance sums and the bracket in one proof
/-- **HP2's post part at a given start, in product form, from `k ≥ 20`.**  For tube parameters
summing to at most `100`, under the hypotheses of `RMF.tiltedMeasure₂_hp2PostTube_le_sum_floor`
(without the variance and push data), block data `VL ≤ V₁`, `V₁, V₂ ≤ v₊`, `|cov| ≤ κ`,
`∑|cov| ≤ K_t`, variance sums `∑Vᵢ ≥ 0.495n - V_d`, a push `P` for both walks and `n ≥ n₀ ≥ 2`
with `α₁ = 0.495 - (V_d + v₊)/n₀ > 0`, `α₂ = 0.495 - (V_d + κK_t/VL)/n₀ > 0`: the two post tubes
have two-fold tilted probability at most
`(1 + e^{-100})(2/π)/√(α₁α₂)·(1 + (K_t/VL)(√v₊ + v₊/c')/c')·(A₁ + c')(A₂ + c')/n`,
`Aᵢ = max(a + ρ - zᵢ, 0)`, `c' = c + 2e^{-40} + P`, `c ≥ √(πv₊/2)`. -/
theorem tiltedMeasure₂_hp2PostTube_le_Cpost_floor (hX : IsRademacherPrimeValues X μ)
    {k b n y n₀ : ℕ} {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k)
    (hh₂ : h₂ ∈ halfWindow k) (hσ : 0 ≤ σ) (hσn : σ * Real.exp ((k : ℝ) + (b + n)) ≤ 1 / 200)
    (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y)
    (hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b))
    (hcase : 4 ≤ b ∨ (2 ≤ b ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b)))
    (hn₀2 : 2 ≤ n₀) (hn₀ : n₀ ≤ n)
    {a A B ρ z₁ z₂ : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (henv : a + A + B + ρ ≤ 100)
    (hz₁ : -A - B * b - ρ ≤ z₁ ∧ z₁ ≤ a + ρ) (hz₂ : -A - B * b - ρ ≤ z₂ ∧ z₂ ≤ a + ρ)
    {vmax c P VL κ Kt Vd : ℝ} (hVL : 0 < VL) (hVd : 0 ≤ Vd)
    (hv : ∀ m, m < n → VL ≤ pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
      ∧ pairVarH X μ y k σ h₁ h₂ h₁ (m + b) ≤ vmax ∧ pairVarH X μ y k σ h₁ h₂ h₂ (m + b) ≤ vmax)
    (hκ : ∀ m, m < n → |pairCovH X μ y k σ h₁ h₂ (m + b)| ≤ κ)
    (hKt : ∑ m ∈ Finset.range n, |pairCovH X μ y k σ h₁ h₂ (m + b)| ≤ Kt)
    (hVs₁ : 0.495 * n - Vd ≤ ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
    (hVs₂ : 0.495 * n - Vd ≤ ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₂ (m + b))
    (hα₁ : 0 < 0.495 - (Vd + vmax) / n₀) (hα₂ : 0 < 0.495 - (Vd + κ * (Kt / VL)) / n₀)
    (hc0 : 0 < c) (hc : √(π * vmax / 2) ≤ c)
    (hP₁ : ∀ j, j ≤ n → -∑ i ∈ Finset.range j,
      (pairMeanH X μ y k σ h₁ h₂ h₁ (i + b) - windowMeanH X μ y k σ h₁ (i + b)) ≤ P)
    (hP₂ : ∀ j, j ≤ n → -∑ i ∈ Finset.range j,
      (pairMeanH X μ y k σ h₁ h₂ h₂ (i + b) - windowMeanH X μ y k σ h₂ (i + b)) ≤ P) :
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ).real
        (hp2PostTube X μ y k b n σ h₁ a A B ρ z₁ ∩ hp2PostTube X μ y k b n σ h₂ a A B ρ z₂)
      ≤ (1 + Real.exp (-100)) * (2 / π / √((0.495 - (Vd + vmax) / n₀)
            * (0.495 - (Vd + κ * (Kt / VL)) / n₀)))
          * (1 + Kt / VL * (√vmax + vmax / (c + 2 * Real.exp (-40) + P))
            / (c + 2 * Real.exp (-40) + P))
          * (max (a + ρ - z₁) 0 + (c + 2 * Real.exp (-40) + P))
          * (max (a + ρ - z₂) 0 + (c + 2 * Real.exp (-40) + P)) / n := by
  have hπ := Real.pi_pos
  have hn2 : 2 ≤ n := le_trans hn₀2 hn₀
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hn₀0 : (0 : ℝ) < n₀ := by
    have : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀2
    linarith
  have hnn₀ : (n₀ : ℝ) ≤ n := by exact_mod_cast hn₀
  obtain ⟨α₁, hα₁def⟩ : ∃ α, α = 0.495 - (Vd + vmax) / n₀ := ⟨_, rfl⟩
  obtain ⟨α₂, hα₂def⟩ : ∃ α, α = 0.495 - (Vd + κ * (Kt / VL)) / n₀ := ⟨_, rfl⟩
  rw [← hα₁def, ← hα₂def]
  rw [← hα₁def] at hα₁
  rw [← hα₂def] at hα₂
  obtain ⟨c', hc'def⟩ : ∃ c', c' = c + 2 * Real.exp (-40) + P := ⟨_, rfl⟩
  rw [← hc'def]
  have hP0 : 0 ≤ P := by simpa using hP₁ 0 (Nat.zero_le n)
  have hc'0 : 0 < c' := by rw [hc'def]; positivity
  /- the block data -/
  have hV1pos : ∀ m, m < n → 0 < pairVarH X μ y k σ h₁ h₂ h₁ (m + b) := fun m hm =>
    lt_of_lt_of_le hVL (hv m hm).1
  have hvmax0 : 0 < vmax := lt_of_lt_of_le (hV1pos 0 (by omega)) (hv 0 (by omega)).2.1
  have hκ0 : 0 ≤ κ := le_trans (abs_nonneg _) (hκ 0 (by omega))
  have hKt0 : 0 ≤ Kt := le_trans (Finset.sum_nonneg fun m _ => abs_nonneg _) hKt
  /- the first variance sum -/
  have hX₁ : α₁ * n ≤ ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b) - vmax := by
    rw [hα₁def]
    have h1 : (Vd + vmax) / n₀ * n ≥ Vd + vmax := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hn₀0]
      nlinarith
    nlinarith
  have hsum : vmax < ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b) := by
    nlinarith
  /- the residual sum -/
  have hslope : ∀ m, m < n → |pairSlope (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
      (pairCovH X μ y k σ h₁ h₂ (m + b))| ≤ |pairCovH X μ y k σ h₁ h₂ (m + b)| / VL := by
    intro m hm
    rw [pairSlope, abs_div, abs_of_pos (hV1pos m hm)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hVL (hv m hm).1
  have hKsum : ∑ m ∈ Finset.range n, |pairSlope (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
      (pairCovH X μ y k σ h₁ h₂ (m + b))| ≤ Kt / VL := by
    refine (Finset.sum_le_sum fun m hm => hslope m (Finset.mem_range.1 hm)).trans ?_
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hKt hVL.le
  have hRterm : ∀ m, m < n → pairVarH X μ y k σ h₁ h₂ h₂ (m + b)
      - κ * (|pairCovH X μ y k σ h₁ h₂ (m + b)| / VL)
      ≤ pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
        (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b)) := by
    intro m hm
    rw [pairResidVar]
    have hq : pairCovH X μ y k σ h₁ h₂ (m + b) ^ 2 / pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
        ≤ κ * (|pairCovH X μ y k σ h₁ h₂ (m + b)| / VL) := by
      rw [← sq_abs]
      have h1 : |pairCovH X μ y k σ h₁ h₂ (m + b)| ^ 2 / pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
          ≤ |pairCovH X μ y k σ h₁ h₂ (m + b)| ^ 2 / VL :=
        div_le_div_of_nonneg_left (sq_nonneg _) hVL (hv m hm).1
      have h2 : |pairCovH X μ y k σ h₁ h₂ (m + b)| ^ 2 / VL
          ≤ κ * (|pairCovH X μ y k σ h₁ h₂ (m + b)| / VL) := by
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (hκ m hm) (div_nonneg (abs_nonneg _) hVL.le)
      linarith
    linarith
  have hRsum : 0.495 * n - (Vd + κ * (Kt / VL)) ≤ ∑ m ∈ Finset.range n,
      pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b)) (pairVarH X μ y k σ h₁ h₂ h₂ (m + b))
        (pairCovH X μ y k σ h₁ h₂ (m + b)) := by
    have h1 := Finset.sum_le_sum fun m hm => hRterm m (Finset.mem_range.1 hm)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div] at h1
    have h2 : κ * ((∑ m ∈ Finset.range n, |pairCovH X μ y k σ h₁ h₂ (m + b)|) / VL)
        ≤ κ * (Kt / VL) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hKt hVL.le) hκ0
    linarith
  have hX₂ : α₂ * n ≤ ∑ m ∈ Finset.range n,
      pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b)) (pairVarH X μ y k σ h₁ h₂ h₂ (m + b))
        (pairCovH X μ y k σ h₁ h₂ (m + b)) := by
    rw [hα₂def]
    have h0 : 0 ≤ Vd + κ * (Kt / VL) := by positivity
    have h1 : (Vd + κ * (Kt / VL)) / n₀ * n ≥ Vd + κ * (Kt / VL) := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hn₀0]
      nlinarith
    nlinarith
  /- the chain -/
  have hchain := tiltedMeasure₂_hp2PostTube_le_sum_floor hX hk hh₁ hh₂ hσ hσn hy hdep hcase hn2
    ha hA hB hρ henv hz₁ hz₂ (fun m hm => (hv m hm).2.1) (fun m hm => (hv m hm).2.2) hsum hc0 hc
    hP₁ hP₂
  /- the square roots -/
  have hq₁ : √(2 / (π * (∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b) - vmax)))
      ≤ √(2 / (π * (α₁ * n))) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hX₁ hπ.le))
  have hq₂ : √(2 / (π * ∑ m ∈ Finset.range n, pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
        (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b))))
      ≤ √(2 / (π * (α₂ * n))) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hX₂ hπ.le))
  have hqq := sqrt_two_div_mul_le hα₁ hα₂ hn0
  have hβ : √(2 / (π * (∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b) - vmax)))
      * √(2 / (π * ∑ m ∈ Finset.range n, pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
        (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b))))
      ≤ 2 / π / √(α₁ * α₂) / n :=
    le_trans (mul_le_mul hq₁ hq₂ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hqq
  /- the bracket -/
  have hA₁ : 0 ≤ max (a + ρ - z₁) 0 := le_max_right _ _
  have hA₂ : 0 ≤ max (a + ρ - z₂) 0 := le_max_right _ _
  have hbr := pairBallot_bracket_le hA₁ hA₂ hc'0 hvmax0.le
    (Finset.sum_nonneg fun m _ => abs_nonneg _) hKsum
  have hY₁ : max (a + ρ - z₁) 0 + 2 * Real.exp (-40) + P + c = max (a + ρ - z₁) 0 + c' := by
    rw [hc'def]; ring
  have hY₂ : max (a + ρ - z₂) 0 + 2 * Real.exp (-40) + P + c = max (a + ρ - z₂) 0 + c' := by
    rw [hc'def]; ring
  rw [hY₁, hY₂] at hchain
  have hbr0 : 0 ≤ (max (a + ρ - z₁) 0 + c') * (max (a + ρ - z₂) 0 + c')
      + (∑ m ∈ Finset.range n, |pairSlope (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
        (pairCovH X μ y k σ h₁ h₂ (m + b))|) * ((max (a + ρ - z₁) 0 + c') * √vmax + vmax) := by
    have := Finset.sum_nonneg (s := Finset.range n) fun m _ =>
      abs_nonneg (pairSlope (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
        (pairCovH X μ y k σ h₁ h₂ (m + b)))
    positivity
  have hε : 0 ≤ 1 + Real.exp (-100) := by positivity
  refine hchain.trans ?_
  have hT0 : 0 ≤ 2 / π / √(α₁ * α₂) / n := by positivity
  calc (1 + Real.exp (-100)) * (√(2 / (π * (∑ m ∈ Finset.range n,
          pairVarH X μ y k σ h₁ h₂ h₁ (m + b) - vmax)))
        * √(2 / (π * ∑ m ∈ Finset.range n, pairResidVar (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
          (pairVarH X μ y k σ h₁ h₂ h₂ (m + b)) (pairCovH X μ y k σ h₁ h₂ (m + b))))
        * ((max (a + ρ - z₁) 0 + c') * (max (a + ρ - z₂) 0 + c')
          + (∑ m ∈ Finset.range n, |pairSlope (pairVarH X μ y k σ h₁ h₂ h₁ (m + b))
              (pairCovH X μ y k σ h₁ h₂ (m + b))|)
            * ((max (a + ρ - z₁) 0 + c') * √vmax + vmax)))
      ≤ (1 + Real.exp (-100)) * (2 / π / √(α₁ * α₂) / n
        * ((max (a + ρ - z₁) 0 + c') * (max (a + ρ - z₂) 0 + c')
          * (1 + Kt / VL * (√vmax + vmax / c') / c'))) := by
        refine mul_le_mul_of_nonneg_left ?_ hε
        exact mul_le_mul hβ hbr hbr0 hT0
    _ = _ := by ring

end Cpost

/-! ### A case's numerals, from `k ≥ 20` -/

section CaseData

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **One post block's covariance by its tiers, from `k ≥ 20`**: at depth `d`, block `d + i ≥ 2`
with `σe^{k+d+i+1} ≤ 1/200`, `|cov_{d+i}|` is at most
`(diffTier i + sumTier(d + i))/2 + (E_D + E_S)/2 + e^{-(d+i)}/10²⁰`, with `E_D`, `E_S` the block's
`RMF.blockCosErrDecay` at `|h₁ - h₂|` and `h₁ + h₂`. -/
lemma abs_pairCovH_le_tier_floor (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k d i : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσm : σ * Real.exp ((k : ℝ) + ((d + i : ℕ) : ℝ) + 1) ≤ 1 / 200)
    (hd1 : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + d))
    (hd2 : |h₁ - h₂| * Real.exp ((k : ℝ) + d) ≤ 1) (hm2 : 2 ≤ d + i)
    (hB : primeBlockSub k (d + i) ⊆ primesBelowSub y) :
    |pairCovH X μ y k σ h₁ h₂ (d + i)|
      ≤ (diffTier i + sumTier (d + i)) / 2
        + (blockCosErrDecay k (d + i) |h₁ - h₂| + blockCosErrDecay k (d + i) (h₁ + h₂)) / 2
        + Real.exp (-((d + i : ℕ) : ℝ)) / 10 ^ 20 := by
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have hc := abs_pairCovH_le hX y (m := d + i) (h₁ := h₁) (h₂ := h₂) hk hσ hB
  have hD := abs_blockCosSum_diff_le_tier_floor hk hσ hσm hd1 hd2
  have hS := abs_blockCosSum_sum_le_tier_floor (τ := h₁ + h₂) hk hσ hσm hm2 (by linarith)
    (by linarith)
  linarith

/-- The window's sum frequency `h₁ + h₂` lies in `[0, 2e^{-20}]` from `k ≥ 20`. -/
lemma add_mem_of_mem_halfWindow_floor {k : ℕ} {h₁ h₂ : ℝ} (hk : 20 ≤ k)
    (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k) :
    0 ≤ h₁ + h₂ ∧ h₁ + h₂ ≤ 2 * Real.exp (-20) := by
  obtain ⟨hh₁l, hh₁u⟩ := hh₁
  obtain ⟨hh₂l, hh₂u⟩ := hh₂
  have h0 : 0 < Real.exp (-((k : ℝ) + 1)) := Real.exp_pos _
  exact ⟨by linarith, le_two_exp_neg_twenty_of_le hk (by linarith)⟩

/-- **The post blocks' data at depth `d`, post start `b = d + s ≥ 2`, from `k ≥ 20`**: from tier
bounds on the blocks `m ≥ b` (variances in `[VL, v₊]`, difference tiers `≤ D₊` from phase `s`, sum
tiers `≤ S₊`) and the tier sums `D_T, S_T`: every post block has `VL ≤ V₁`, `V₁, V₂ ≤ v₊` and
`|cov| ≤ (D₊ + S₊)/2 + 7.5·10⁻⁸`; `∑|cov| ≤ (D_T + S_T)/2 + 3.3·10⁻⁶`; and
`∑Vᵢ ≥ 0.495n - e^{1-b}/2 - 1.6·10⁻⁶`. -/
lemma hp2Post_case_data_floor (hX : IsRademacherPrimeValues X μ) (y : ℕ) {k d s b n : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hbs : b = d + s) (hσn : σ * Real.exp ((k : ℝ) + ((b : ℝ) + n)) ≤ 1 / 200)
    (hy : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y)
    (hd1 : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + d))
    (hd2 : |h₁ - h₂| * Real.exp ((k : ℝ) + d) ≤ 1) (hb2 : 2 ≤ b)
    {VL vmax Dmax Smax DT ST : ℝ}
    (hVL : ∀ m, b ≤ m → VL ≤ varLoTier m) (hvmax : ∀ m, b ≤ m → varHiTier m ≤ vmax)
    (hDmax : ∀ i, s ≤ i → diffTier i ≤ Dmax) (hSmax : ∀ m, b ≤ m → sumTier m ≤ Smax)
    (hDT : ∑ j ∈ Finset.range n, diffTier (s + j) ≤ DT)
    (hST : ∑ j ∈ Finset.range n, sumTier (b + j) ≤ ST) :
    (∀ m, m < n → VL ≤ pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
      ∧ pairVarH X μ y k σ h₁ h₂ h₁ (m + b) ≤ vmax ∧ pairVarH X μ y k σ h₁ h₂ h₂ (m + b) ≤ vmax)
    ∧ (∀ m, m < n → |pairCovH X μ y k σ h₁ h₂ (m + b)| ≤ (Dmax + Smax) / 2 + 7.5 / 10 ^ 8)
    ∧ ∑ m ∈ Finset.range n, |pairCovH X μ y k σ h₁ h₂ (m + b)| ≤ (DT + ST) / 2 + 3.3 / 10 ^ 6
    ∧ 0.495 * n - (Real.exp (1 - b) / 2 + 1.6 / 10 ^ 6)
        ≤ ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₁ (m + b)
    ∧ 0.495 * n - (Real.exp (1 - b) / 2 + 1.6 / 10 ^ 6)
        ≤ ∑ m ∈ Finset.range n, pairVarH X μ y k σ h₁ h₂ h₂ (m + b) := by
  have hk' : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hσm : ∀ m, m < n → σ * Real.exp ((k : ℝ) + ((m + b : ℕ) : ℝ) + 1) ≤ 1 / 200 :=
    fun m hm => sigma_exp_le_of_lt hσ hσn (by omega)
  have hblk : ∀ m : ℕ, m + b = d + (s + m) := fun m => by omega
  have hD := abs_le_two_exp_neg_twenty_of_depth hk hd2
  obtain ⟨hS0, hS2⟩ := add_mem_of_mem_halfWindow_floor hk hh₁ hh₂
  have hcov : ∀ m, m < n → |pairCovH X μ y k σ h₁ h₂ (m + b)|
      ≤ (diffTier (s + m) + sumTier (m + b)) / 2
        + (blockCosErrDecay k (m + b) |h₁ - h₂| + blockCosErrDecay k (m + b) (h₁ + h₂)) / 2
        + Real.exp (-((m + b : ℕ) : ℝ)) / 10 ^ 20 := by
    intro m hm
    have h := abs_pairCovH_le_tier_floor hX y (i := s + m) hk hh₁ hh₂ hσ
      (by rw [← hblk]; exact hσm m hm) hd1 hd2 (by omega) (by rw [← hblk]; exact hy m hm)
    rwa [← hblk] at h
  have hexp1 : ∀ m : ℕ, Real.exp (-((m + b : ℕ) : ℝ)) ≤ 1 := fun m =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg _))
  have hm20 : ∀ m : ℕ, (20 : ℝ) ≤ ((m + b : ℕ) : ℝ) + k := fun m => by
    linarith [Nat.cast_nonneg (α := ℝ) (m + b)]
  refine ⟨fun m hm => ?_, fun m hm => ?_, ?_, sum_pairVarH_ge_floor hX y hk hh₁ hσ hσn hy,
    sum_pairVarH_ge_floor hX y hk hh₂ hσ hσn hy⟩
  · have t₁ := pairVarH_mem_tier_floor hX y (h₁ := h₁) (h₂ := h₂) (h := h₁) hk hh₁ hσ (hσm m hm)
      (by omega) (hy m hm)
    have t₂ := pairVarH_mem_tier_floor hX y (h₁ := h₁) (h₂ := h₂) (h := h₂) hk hh₂ hσ (hσm m hm)
      (by omega) (hy m hm)
    have l := hVL (m + b) (by omega)
    have u := hvmax (m + b) (by omega)
    exact ⟨l.trans t₁.1, t₁.2.trans u, t₂.2.trans u⟩
  · have h := hcov m hm
    have hD' := hDmax (s + m) (by omega)
    have hS' := hSmax (m + b) (by omega)
    have eD := blockCosErrDecay_le_numeral (hm20 m) (abs_nonneg (h₁ - h₂)) hD
    have eS := blockCosErrDecay_le_numeral (hm20 m) hS0 hS2
    have h2 : Real.exp (-((m + b : ℕ) : ℝ)) / 10 ^ 20 ≤ 1 / 10 ^ 20 :=
      div_le_div_of_nonneg_right (hexp1 m) (by positivity)
    have h3 : (7.43 : ℝ) / 10 ^ 8 + 1 / 10 ^ 20 ≤ 7.5 / 10 ^ 8 := by norm_num
    linarith
  · have hsum := Finset.sum_le_sum fun m (hm : m ∈ Finset.range n) =>
      hcov m (Finset.mem_range.1 hm)
    have hsplit : ∑ m ∈ Finset.range n, ((diffTier (s + m) + sumTier (m + b)) / 2
        + (blockCosErrDecay k (m + b) |h₁ - h₂| + blockCosErrDecay k (m + b) (h₁ + h₂)) / 2
        + Real.exp (-((m + b : ℕ) : ℝ)) / 10 ^ 20)
        = (∑ m ∈ Finset.range n, diffTier (s + m) + ∑ m ∈ Finset.range n, sumTier (m + b)) / 2
          + (∑ m ∈ Finset.range n, blockCosErrDecay k (m + b) |h₁ - h₂|
            + ∑ m ∈ Finset.range n, blockCosErrDecay k (m + b) (h₁ + h₂)) / 2
          + (∑ m ∈ Finset.range n, Real.exp (-((m + b : ℕ) : ℝ))) / 10 ^ 20 := by
      simp only [Finset.sum_add_distrib, Finset.sum_div, add_div]
    rw [hsplit] at hsum
    have hST' : ∑ m ∈ Finset.range n, sumTier (m + b) ≤ ST := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_)) hST
      rw [add_comm]
    have hED := sum_range_blockCosErrDecay_le (θ := k) hk' (abs_nonneg (h₁ - h₂)) hD b n
    have hES := sum_range_blockCosErrDecay_le (θ := k) hk' hS0 hS2 b n
    have hE := sum_exp_neg_add_le b n
    have h2 : (∑ m ∈ Finset.range n, Real.exp (-((m + b : ℕ) : ℝ))) / 10 ^ 20 ≤ 1.59 / 10 ^ 20 :=
      div_le_div_of_nonneg_right hE (by positivity)
    have h3 : ((3.2 : ℝ) / 10 ^ 6 + 3.2 / 10 ^ 6) / 2 + 1.59 / 10 ^ 20 ≤ 3.3 / 10 ^ 6 := by
      norm_num
    linarith

set_option maxHeartbeats 1000000 in
-- the case data, the push, the product form and its simplification in one proof
/-- **The post bound from a case's numerals, from `k ≥ 20`.**  For tube parameters summing to at
most `100` and numerals bounding the tiers, their sums and the push `P_D`, with the allowances
`7.5·10⁻⁸` (`κ`), `3.3·10⁻⁶` (`K_t`), `1.6·10⁻⁶` (`V_d`) and `3.2·10⁻⁶` (`P`): the two post tubes
have two-fold tilted probability at most `C₀/√(β₁β₂)·(A₁ + c_h)(A₂ + c_h)/(r - b)`,
`Aᵢ = max(a + ρ - zᵢ, 0)`. -/
theorem hp2Post_bound_of_numerals_floor (hX : IsRademacherPrimeValues X μ) {k d s b r y n₀ : ℕ}
    {σ h₁ h₂ : ℝ} (hk : 20 ≤ k) (hh₁ : h₁ ∈ halfWindow k) (hh₂ : h₂ ∈ halfWindow k)
    (hσ : 0 ≤ σ) (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hy : ∀ m, m < r → primeBlockSub k m ⊆ primesBelowSub y) (hbs : b = d + s) (hb2 : 2 ≤ b)
    (hd1 : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + d))
    (hd2 : |h₁ - h₂| * Real.exp ((k : ℝ) + d) ≤ 1)
    (hcase : 4 ≤ b ∨ (2 ≤ b ∧ Real.exp 1 ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b)))
    (hn₀ : 3 ≤ n₀) (hr : b + n₀ ≤ r)
    {a A B ρ z₁ z₂ : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (henv : a + A + B + ρ ≤ 100)
    (hz₁ : -A - B * b - ρ ≤ z₁ ∧ z₁ ≤ a + ρ) (hz₂ : -A - B * b - ρ ≤ z₂ ∧ z₂ ≤ a + ρ)
    {VL vmax Dmax Smax DT ST PD κ Kt Vd P c sq β₁ β₂ Kn C₀ ch : ℝ}
    (hVL : ∀ m, b ≤ m → VL ≤ varLoTier m) (hvmax : ∀ m, b ≤ m → varHiTier m ≤ vmax)
    (hDmax : ∀ i, s ≤ i → diffTier i ≤ Dmax) (hSmax : ∀ m, b ≤ m → sumTier m ≤ Smax)
    (hDT : ∀ n, ∑ j ∈ Finset.range n, diffTier (s + j) ≤ DT)
    (hST : ∀ n, ∑ j ∈ Finset.range n, sumTier (b + j) ≤ ST)
    (hPD : ∀ n j, b + n ≤ r → j ≤ n →
      -∑ i ∈ Finset.range j, blockCosSum k σ (h₁ - h₂) (i + b) ≤ PD)
    (hVL0 : 0 < VL) (hκ : (Dmax + Smax) / 2 + 7.5 / 10 ^ 8 ≤ κ)
    (hKt : (DT + ST) / 2 + 3.3 / 10 ^ 6 ≤ Kt) (hVd : Real.exp (1 - b) / 2 + 1.6 / 10 ^ 6 ≤ Vd)
    (hP : PD + Real.exp (1 - b) + 3.2 / 10 ^ 6 ≤ P) (hc0 : 0 < c) (hc : π * vmax / 2 ≤ c ^ 2)
    (hsq0 : 0 ≤ sq) (hsq : vmax ≤ sq ^ 2) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (hβ₁' : β₁ ≤ 0.495 - (Vd + vmax) / n₀) (hβ₂' : β₂ ≤ 0.495 - (Vd + κ * (Kt / VL)) / n₀)
    (hKn : 1 + Kt / VL * (sq + vmax / (c + P)) / (c + P) ≤ Kn) (hC₀ : 0.636621 * Kn ≤ C₀)
    (hch : c + 1 / 10 ^ 4 + P ≤ ch) :
    (tiltedMeasure₂ (fun ω => squarefreeExtension fun p => X p ω) y (shiftLine σ h₁)
        (shiftLine σ h₂) μ).real
        (hp2PostTube X μ y k b (r - b) σ h₁ a A B ρ z₁
          ∩ hp2PostTube X μ y k b (r - b) σ h₂ a A B ρ z₂)
      ≤ C₀ / √(β₁ * β₂) * (max (a + ρ - z₁) 0 + ch) * (max (a + ρ - z₂) 0 + ch)
        / ((r - b : ℕ) : ℝ) := by
  obtain ⟨n, hn⟩ : ∃ n, n = r - b := ⟨_, rfl⟩
  rw [← hn]
  have hnr : b + n = r := by omega
  have hn₀n : n₀ ≤ n := by omega
  have hσn : σ * Real.exp ((k : ℝ) + ((b : ℝ) + n)) ≤ 1 / 200 := by
    have : ((b : ℝ) + n) = r := by rw [← hnr]; push_cast; ring
    rw [this]
    exact hσr
  have hy' : ∀ m, m < n → primeBlockSub k (m + b) ⊆ primesBelowSub y := fun m hm =>
    hy (m + b) (by omega)
  have hdep : Real.exp (-1) ≤ |h₁ - h₂| * Real.exp ((k : ℝ) + b) :=
    hd1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      have : (d : ℝ) ≤ b := by exact_mod_cast (show d ≤ b by omega)
      linarith)) (abs_nonneg _))
  obtain ⟨hv, hκb, hKb, hVs₁, hVs₂⟩ := hp2Post_case_data_floor hX y hk hh₁ hh₂ hσ hbs hσn hy'
    hd1 hd2 hb2 hVL hvmax hDmax hSmax (hDT n) (hST n)
  obtain ⟨hP₁, hP₂⟩ := hp2Post_push_le_floor hX y hk hh₁ hh₂ hσ hy' (PD := PD)
    fun j hj => hPD n j (le_of_eq hnr) hj
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hα₁ : 0 < 0.495 - (Vd + vmax) / n₀ := lt_of_lt_of_le hβ₁ hβ₁'
  have hα₂ : 0 < 0.495 - (Vd + κ * (Kt / VL)) / n₀ := lt_of_lt_of_le hβ₂ hβ₂'
  have hvmax0 : 0 ≤ vmax := by
    have := hv 0 (by omega)
    linarith [this.1, this.2.1]
  have hVd0 : 0 ≤ Vd := le_trans (by positivity) hVd
  have hPD0 : 0 ≤ PD := by simpa using hPD n 0 (le_of_eq hnr) (Nat.zero_le n)
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have hmain := tiltedMeasure₂_hp2PostTube_le_Cpost_floor hX hk hh₁ hh₂ hσ hσn hy' hdep hcase
    (n₀ := n₀) (by omega) hn₀n ha hA hB hρ henv hz₁ hz₂ (vmax := vmax) (c := c) (P := P)
    (VL := VL) (κ := κ) (Kt := Kt) (Vd := Vd) hVL0 hVd0 hv (fun m hm => (hκb m hm).trans hκ)
    (hKb.trans hKt) (by linarith) (by linarith) hα₁ hα₂ hc0
    (sqrt_le_of_le_sq hc0.le hc) (fun j hj => (hP₁ j hj).trans hP) (fun j hj => (hP₂ j hj).trans hP)
  refine hmain.trans ?_
  have hn0 : (0 : ℝ) < n := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    linarith
  have hKt0 : 0 ≤ Kt := le_trans (by
    have := Finset.sum_nonneg (s := Finset.range n) fun m _ =>
      abs_nonneg (pairCovH X μ y k σ h₁ h₂ (m + b))
    linarith) hKt
  have hcP : 0 < c + P := by linarith
  have hKf := (slope_factor_le (K := Kt / VL) (v := vmax) (s := sq) (cl := c + P)
    (c' := c + 2 * Real.exp (-40) + P) (by positivity) hvmax0 (sqrt_le_of_le_sq hsq0 hsq) hcP
    (by linarith [Real.exp_pos (-40)])).trans hKn
  have hKf0 : 0 ≤ 1 + Kt / VL * (√vmax + vmax / (c + 2 * Real.exp (-40) + P))
      / (c + 2 * Real.exp (-40) + P) := by
    have : 0 < c + 2 * Real.exp (-40) + P := by positivity
    positivity
  have hKn0 : 0 ≤ Kn := le_trans hKf0 hKf
  have hC : (1 + Real.exp (-100)) * (2 / π) * Kn ≤ C₀ :=
    le_trans (mul_le_mul_of_nonneg_right two_div_pi_mul_le hKn0) hC₀
  exact post_Cpost_simplify hβ₁ hβ₂ hβ₁' hβ₂' hKf0 hKf hC (by positivity)
    (by linarith [two_exp_neg_forty_le]) (le_max_right _ _) (le_max_right _ _) hn0

end CaseData

end RMF
