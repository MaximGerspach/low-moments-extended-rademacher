/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosMoment

/-!
# The chaos-moment interpolation, with the bad-set constant as a level shift

`RMF.integral_rpow_le_of_goodSets` takes one constant `C₂` for both of its inputs, the bad sets
(`P(bad_a) ≤ C₂e^{-2a}`) and the restricted chaos (`E R_a ≤ C₂ min{1, a/√(t - ⌈a/4⌉)}`).  Here the
two constants are separate, and the bad-set constant `C_b` costs only a shift of the level.
Running the levels `A_j = A + j/(1-q)`, it enters through `(C_b e^{-2A})^{1-q}`, which is at most
`1` once `A ≥ ½ log C_b`.  The restricted chaos may carry an additive shift,
`E R_a ≤ C_i min{1, (a + s)/√(t - ⌈a/4⌉)}`.

The constant `RMF.shiftMomentConst` depends on `q` and on two free parameters:
* `λ₀ ≥ 1`, where the proof switches from Jensen (`E Z^q ≤ C₁^q`, for `(1-q)√t ≤ λ₀`) to the level
  decomposition;
* the start level `A ≥ a₀`.

`δ` is what the free start costs: the levels used stay below `A + 3√t`, and
`t - ⌈a/4⌉ ≥ (1-δ)t` for those levels once `A/4 + 3√t/4 + 1 + n₀ ≤ δt`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Three pieces of arithmetic -/

/-- `∑_{j<m} e^{-2j}(u + j + 1)^q ≤ (u+1)^q(1-e^{-2})⁻¹ + e^{-2}(1-e^{-2})^{-2}`: subadditivity
gives `(u + 1 + j)^q ≤ (u+1)^q + j`, and the two series are geometric. -/
lemma sum_range_exp_mul_add_rpow_le {q u : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hu : 0 ≤ u) (m : ℕ) :
    ∑ j ∈ Finset.range m, Real.exp (-2 * (j : ℝ)) * (u + (j : ℝ) + 1) ^ q
      ≤ (u + 1) ^ q * (1 - Real.exp (-2))⁻¹ + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ := by
  set r : ℝ := Real.exp (-2) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hu1 : (0 : ℝ) ≤ (u + 1) ^ q := Real.rpow_nonneg (by linarith) q
  have hterm : ∀ j : ℕ, Real.exp (-2 * (j : ℝ)) * (u + (j : ℝ) + 1) ^ q
      ≤ (u + 1) ^ q * r ^ j + (j : ℝ) * r ^ j := by
    intro j
    have hexp : Real.exp (-2 * (j : ℝ)) = r ^ j := by
      rw [show -2 * (j : ℝ) = (j : ℝ) * (-2) by ring, Real.exp_nat_mul]
    have hsub : (u + (j : ℝ) + 1) ^ q ≤ (u + 1) ^ q + (j : ℝ) ^ q := by
      rw [show u + (j : ℝ) + 1 = (u + 1) + (j : ℝ) by ring]
      exact Real.rpow_add_le_add_rpow (by linarith) (Nat.cast_nonneg j) hq0.le hq1
    have hjq : (j : ℝ) ^ q ≤ (j : ℝ) := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simp [Real.zero_rpow hq0.ne']
      · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        calc (j : ℝ) ^ q ≤ (j : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hj1 hq1
          _ = (j : ℝ) := Real.rpow_one _
    rw [hexp]
    calc r ^ j * (u + (j : ℝ) + 1) ^ q ≤ r ^ j * ((u + 1) ^ q + (j : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr0 j)
      _ = (u + 1) ^ q * r ^ j + (j : ℝ) * r ^ j := by ring
  refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hg : ∑ j ∈ Finset.range m, r ^ j ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hr0 j)
      (summable_geometric_of_lt_one hr0 hr1)
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hjg : ∑ j ∈ Finset.range m, (j : ℝ) * r ^ j ≤ r * ((1 - r) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, ← tsum_coe_mul_geometric_of_norm_lt_one hnorm]
    exact Summable.sum_le_tsum _ (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hr0 j))
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  exact add_le_add (mul_le_mul_of_nonneg_left hg hu1) hjg

/-- `Λ^{-q} ≤ (1 + λ₀⁻¹)^q (1 + Λ)^{-q}` for `Λ ≥ λ₀ > 0`: the decomposition's `((1-q)√t)^{-q}` is
the target's up to `(1 + λ₀⁻¹)^q`. -/
lemma rpow_neg_le_one_add_inv_rpow_mul {Λ lam q : ℝ} (hlam : 0 < lam) (hΛ : lam ≤ Λ)
    (hq0 : 0 ≤ q) : Λ ^ (-q) ≤ (1 + lam⁻¹) ^ q * (1 + Λ) ^ (-q) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le hlam hΛ
  have hΛne : Λ ≠ 0 := hΛ0.ne'
  have h2 : (0 : ℝ) < (1 + Λ) ^ q := Real.rpow_pos_of_pos (by linarith) q
  have heq : Λ ^ (-q) = ((1 + Λ) / Λ) ^ q * (1 + Λ) ^ (-q) := by
    rw [Real.div_rpow (by linarith) hΛ0.le, Real.rpow_neg (show (0 : ℝ) ≤ 1 + Λ by linarith),
      Real.rpow_neg hΛ0.le, div_mul_eq_mul_div, mul_inv_cancel₀ h2.ne', one_div]
  have hle : (1 + Λ) / Λ ≤ 1 + lam⁻¹ := by
    have h4 : (1 + Λ) / Λ = 1 + Λ⁻¹ := by
      field_simp
      ring
    rw [h4]
    linarith [inv_anti₀ hlam hΛ]
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (div_nonneg (by linarith) hΛ0.le) hle hq0)
    (Real.rpow_nonneg (by linarith) _)

/-- `e^{-2m} ≤ e^{-2}(1 + Λ)^{-q}` for `m ≥ Λ + 1`, `Λ ≥ 0` and `q ≤ 1`: the tail of the
decomposition, at the last level `m = ⌈Λ⌉₊ + 1`. -/
lemma exp_neg_two_mul_le_exp_neg_two_mul_rpow_neg {Λ q m : ℝ} (hΛ : 0 ≤ Λ) (hm : Λ + 1 ≤ m)
    (hq1 : q ≤ 1) :
    Real.exp (-2 * m) ≤ Real.exp (-2) * (1 + Λ) ^ (-q) := by
  have h1 : (1 + Λ) ^ (-(1 : ℝ)) ≤ (1 + Λ) ^ (-q) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at h1
  have h2 : Real.exp (-2 * m) ≤ Real.exp (-2) * Real.exp (-(2 * Λ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-(2 * Λ)) ≤ (1 + Λ)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp (2 * Λ)])
  have h4 : Real.exp (-2) * Real.exp (-(2 * Λ)) ≤ Real.exp (-2) * (1 + Λ) ^ (-q) :=
    mul_le_mul_of_nonneg_left (le_trans h3 h1) (Real.exp_pos _).le
  linarith

/-- **Room for the free start past a block count `N`**: if `A_max/4 + 3√N/4 + 1 ≤ δN` and
`3 ≤ 8δ√N`, then `A/4 + 3√t/4 + 1 ≤ δt` for every `t ≥ N` and `A ≤ A_max`.  Past `√N ≥ 3/(8δ)`
the right side grows faster: `δ(t - N) = δ(√t + √N)(√t - √N) ≥ 3(√t - √N)/4`. -/
lemma free_start_room_of_le {A Amax δ N t : ℝ} (hδ0 : 0 ≤ δ) (hA : A ≤ Amax) (hN0 : 0 ≤ N)
    (hN : Amax / 4 + 3 * Real.sqrt N / 4 + 1 ≤ δ * N) (hmono : 3 ≤ 8 * δ * Real.sqrt N)
    (hNt : N ≤ t) :
    A / 4 + 3 * Real.sqrt t / 4 + 1 ≤ δ * t := by
  have hst : Real.sqrt N ≤ Real.sqrt t := Real.sqrt_le_sqrt hNt
  have ht0 : 0 ≤ t := le_trans hN0 hNt
  have hN2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
  have ht2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
  have h1 : 0 ≤ Real.sqrt t - Real.sqrt N := by linarith
  have h2 : 3 / 4 ≤ δ * (Real.sqrt t + Real.sqrt N) := by
    have := mul_le_mul_of_nonneg_left hst hδ0
    linarith
  have h3 : δ * (t - N) = (Real.sqrt t - Real.sqrt N) * (δ * (Real.sqrt t + Real.sqrt N)) := by
    linear_combination (-δ) * ht2 + δ * hN2
  have hkey : 3 * (Real.sqrt t - Real.sqrt N) / 4 ≤ δ * (t - N) := by
    rw [h3]
    have := mul_le_mul_of_nonneg_left h2 h1
    linarith
  linarith

/-! ### The interpolation -/

/-- **The constant of the level-shift interpolation** at `q`: the larger of the Jensen branch
`(C₁(1+λ₀))^q` and the decomposition branch
`((1+λ₀⁻¹)C_i/√(1-δ))^q (u^q + E((u+1)^q S₁ + S₂)) + e^{-2}E C₁^q`, where `u = (A+s)(1-q)`,
`E = (C_b e^{-2A})^{1-q}`, `S₁ = (1-e^{-2})⁻¹` and `S₂ = e^{-2}(1-e^{-2})^{-2}`. -/
noncomputable def shiftMomentConst (C₁ Ci Cb A s lam δ q : ℝ) : ℝ :=
  max ((C₁ * (1 + lam)) ^ q)
    (((1 + lam⁻¹) * Ci / Real.sqrt (1 - δ)) ^ q
        * (((A + s) * (1 - q)) ^ q + (Cb * Real.exp (-(2 * A))) ^ (1 - q)
          * (((A + s) * (1 - q) + 1) ^ q * (1 - Real.exp (-2))⁻¹
            + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹))
      + Real.exp (-2) * (Cb * Real.exp (-(2 * A))) ^ (1 - q) * C₁ ^ q)

set_option maxHeartbeats 1000000 in
-- the decomposition, the hulls and the level arithmetic in one proof, as in the main file
/-- **The interpolation, with the bad-set constant as a level shift.**  For `q ∈ [0,1]`,
`E[Z^q] ≤ shiftMomentConst C₁ C_i C_b A s λ₀ δ q·(1 + (1-q)√t)^{-q}`, given `E Z ≤ C₁`, a
decomposition `hdec` of `Z` along good sets, bad sets of measure `≤ C_b e^{-2a}` and a restricted
chaos `≤ C_i min{1, (a+s)/√(t - ⌈a/4⌉)}`, for `a ≥ a₀`.

For `(1-q)√t ≤ λ₀` Jensen gives `E Z^q ≤ C₁^q`.  Otherwise the levels are `A_j = A + j/(1-q)` for
`j ≤ m = ⌈(1-q)√t⌉₊ + 1`, all below `A + 3√t`; there `P(bad)^{1-q} ≤ (C_b e^{-2A})^{1-q} e^{-2j}`,
the restricted chaos is `≤ C_i(A_j + s)/√((1-δ)t)`, and the tail is `≤ e^{-2}(1 + (1-q)√t)^{-q}`. -/
theorem integral_rpow_le_of_goodSets_shift {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} {Rst : (ℝ → Set Ω) → Ω → ℝ} {win : Set ℝ}
    {q : ℝ} {t n₀ : ℕ} {a₀ C₁ Ci Cb A s lam δ : ℝ}
    (hZ0' : ∀ ω, 0 ≤ Z ω) (hZi' : Integrable Z ν)
    (hR0' : ∀ (S : ℝ → Set Ω) (ω : Ω), 0 ≤ Rst S ω)
    (hRi' : ∀ S : ℝ → Set Ω, (∀ h, MeasurableSet (S h)) →
      MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2} → Integrable (Rst S) ν)
    (hdec : ∀ (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ), r ≤ m →
      Z ω ≤ Rst (S r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ win, ω ∉ S j h} (fun _ => (1 : ℝ)) ω * Rst (S (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ win, ω ∉ S m h} (fun _ => (1 : ℝ)) ω * Z ω)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 < C₁) (hCi : 0 < Ci) (hCb : 0 < Cb)
    (hA : a₀ ≤ A) (hA0 : 0 ≤ A) (hs : 0 ≤ s) (hlam : 1 ≤ lam) (hδ : δ ≤ 1 / 2)
    (hZmean : (∫ ω, Z ω ∂ν) ≤ C₁)
    (hT : A / 4 + 3 * Real.sqrt (t : ℝ) / 4 + 1 + (n₀ : ℝ) ≤ δ * t)
    (Gset : ℝ → ℝ → Set Ω)
    (Gmeas : ∀ a h, MeasurableSet (Gset a h))
    (Gunc : ∀ a, MeasurableSet {p : Ω × ℝ | p.1 ∈ Gset a p.2})
    (Gbad : ∀ a, a₀ ≤ a → ν.real {ω | ∃ h ∈ win, ω ∉ Gset a h} ≤ Cb * Real.exp (-(2 * a)))
    (Gint : ∀ a, a₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ t → n₀ ≤ t - ⌈a / 4⌉₊ →
      (∫ ω, Rst (Gset a) ω ∂ν) ≤ Ci * min 1 ((a + s) / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) :
    (∫ ω, Z ω ^ q ∂ν)
      ≤ shiftMomentConst C₁ Ci Cb A s lam δ q * (1 + (1 - q) * Real.sqrt (t : ℝ)) ^ (-q) := by
  obtain ⟨ZZ, hZZ⟩ : ∃ ZZ : Ω → ℝ, ZZ = Z := ⟨_, rfl⟩
  rw [← hZZ]
  have hZ0 : ∀ ω, 0 ≤ ZZ ω := by rw [hZZ]; exact hZ0'
  have hZi : Integrable ZZ ν := by rw [hZZ]; exact hZi'
  have hZmean0 : (0 : ℝ) ≤ ∫ ω, ZZ ω ∂ν := integral_nonneg hZ0
  have hZmean1 : (∫ ω, ZZ ω ∂ν) ≤ C₁ := by rw [hZZ]; exact hZmean
  have hZpow : (∫ ω, ZZ ω ∂ν) ^ q ≤ C₁ ^ q := Real.rpow_le_rpow hZmean0 hZmean1 hq0
  have hjensen : (∫ ω, ZZ ω ^ q ∂ν) ≤ C₁ ^ q := by
    have hZqi := integrable_rpow_of_integrable hZi (Filter.Eventually.of_forall hZ0) hq0 hq1
    exact le_trans (integral_rpow_le_rpow_integral hq0 hq1
      (Filter.Eventually.of_forall hZ0) hZi hZqi) hZpow
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hKJ : (C₁ * (1 + lam)) ^ q ≤ shiftMomentConst C₁ Ci Cb A s lam δ q := le_max_left _ _
  have hKD : ((1 + lam⁻¹) * Ci / Real.sqrt (1 - δ)) ^ q
        * (((A + s) * (1 - q)) ^ q + (Cb * Real.exp (-(2 * A))) ^ (1 - q)
          * (((A + s) * (1 - q) + 1) ^ q * (1 - Real.exp (-2))⁻¹
            + Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹))
      + Real.exp (-2) * (Cb * Real.exp (-(2 * A))) ^ (1 - q) * C₁ ^ q
      ≤ shiftMomentConst C₁ Ci Cb A s lam δ q := le_max_right _ _
  set st : ℝ := Real.sqrt (t : ℝ) with hstdef
  have hst0 : (0 : ℝ) ≤ st := Real.sqrt_nonneg _
  have htar0 : (0 : ℝ) < 1 + (1 - q) * st := by
    have := mul_nonneg (sub_nonneg.2 hq1) hst0
    linarith
  -- `q = 0`: both sides are constants
  rcases eq_or_lt_of_le hq0 with rfl | hq0p
  · have h1 : (∫ ω, ZZ ω ^ (0 : ℝ) ∂ν) = 1 := by simp
    rw [h1, neg_zero, Real.rpow_zero, mul_one]
    rw [Real.rpow_zero] at hKJ
    exact hKJ
  -- the Jensen branch
  rcases le_or_gt ((1 - q) * st) lam with hJ | hD
  · have hpos : (0 : ℝ) < (1 + lam) ^ q := Real.rpow_pos_of_pos (by linarith) q
    have hpow : C₁ ^ q = (C₁ * (1 + lam)) ^ q * (1 + lam) ^ (-q) := by
      rw [Real.mul_rpow hC₁.le (by linarith), Real.rpow_neg (by linarith), mul_assoc,
        mul_inv_cancel₀ hpos.ne', mul_one]
    have hmono : (1 + lam) ^ (-q) ≤ (1 + (1 - q) * st) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos htar0 (by linarith) (by linarith)
    calc (∫ ω, ZZ ω ^ q ∂ν) ≤ C₁ ^ q := hjensen
      _ = (C₁ * (1 + lam)) ^ q * (1 + lam) ^ (-q) := hpow
      _ ≤ shiftMomentConst C₁ Ci Cb A s lam δ q * (1 + (1 - q) * st) ^ (-q) :=
          mul_le_mul hKJ hmono (Real.rpow_nonneg (by linarith) _)
            (le_trans (Real.rpow_nonneg (mul_nonneg hC₁.le (by linarith)) _) hKJ)
  -- the decomposition branch
  have h1q : (0 : ℝ) < 1 - q := by
    by_contra hc
    push Not at hc
    have h := mul_le_mul_of_nonneg_right hc hst0
    rw [zero_mul] at h
    linarith
  have hq1p : q < 1 := by linarith
  set Λ : ℝ := (1 - q) * st with hΛdef
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hst_pos : (0 : ℝ) < st := pos_of_mul_pos_right hΛ0 h1q.le
  set m : ℕ := ⌈Λ⌉₊ + 1 with hmdef
  have hm_ge : Λ + 1 ≤ (m : ℝ) := by
    rw [hmdef]
    push_cast
    linarith [Nat.le_ceil Λ]
  have hm_le : (m : ℝ) ≤ Λ + 2 := by
    rw [hmdef]
    push_cast
    linarith [Nat.ceil_lt_add_one hΛ0.le]
  set lev : ℕ → ℝ := fun j => A + (j : ℝ) / (1 - q) with hlevdef
  have hlevA : ∀ j : ℕ, A ≤ lev j := fun j => by
    simp only [hlevdef]
    linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) j) h1q.le]
  have hlev_le : ∀ j : ℕ, j ≤ m → lev j ≤ A + 3 * st := by
    intro j hj
    have hjR : (j : ℝ) ≤ Λ + 2 := le_trans (by exact_mod_cast hj) hm_le
    have hdiv : (j : ℝ) / (1 - q) ≤ 3 * st := by
      rw [div_le_iff₀ h1q]
      linarith [hΛdef]
    simp only [hlevdef]
    linarith
  have hceil : ∀ j : ℕ, j ≤ m → ((⌈lev j / 4⌉₊ : ℕ) : ℝ) + (n₀ : ℝ) ≤ δ * t := by
    intro j hj
    have hl0 : (0 : ℝ) ≤ lev j / 4 := div_nonneg (le_trans hA0 (hlevA j)) (by norm_num)
    have hc := Nat.ceil_lt_add_one hl0
    have hle := hlev_le j hj
    linarith
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hδt : δ * t ≤ t / 2 := by
    have h := mul_le_mul_of_nonneg_right hδ ht0
    linarith
  have hGok : ∀ j : ℕ, j ≤ m → 2 * ⌈lev j / 4⌉₊ ≤ t ∧ n₀ ≤ t - ⌈lev j / 4⌉₊ := by
    intro j hj
    have h := hceil j hj
    have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
    constructor
    · have hc : ((2 * ⌈lev j / 4⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hc
    · refine Nat.le_sub_of_add_le ?_
      have hc : ((n₀ + ⌈lev j / 4⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hc
  -- the restricted chaos at each level
  obtain ⟨RR, hRR⟩ : ∃ RR : ℕ → Ω → ℝ, RR = fun j => Rst (Gset (lev j)) := ⟨_, rfl⟩
  have hR0 : ∀ (j : ℕ) (ω : Ω), 0 ≤ RR j ω := by
    rw [hRR]; exact fun j ω => hR0' _ ω
  have hRi : ∀ j : ℕ, Integrable (RR j) ν := by
    rw [hRR]
    exact fun j => hRi' _ (fun h => Gmeas (lev j) h) (Gunc (lev j))
  have hRmean0 : ∀ j : ℕ, (0 : ℝ) ≤ ∫ ω, RR j ω ∂ν := fun j => integral_nonneg (hR0 j)
  have hsq1δ : (0 : ℝ) < Real.sqrt (1 - δ) := Real.sqrt_pos.2 (by linarith)
  have hden0 : (0 : ℝ) < Real.sqrt (1 - δ) * st := mul_pos hsq1δ hst_pos
  have hRle : ∀ j : ℕ, j ≤ m →
      (∫ ω, RR j ω ∂ν) ≤ Ci * (lev j + s) / (Real.sqrt (1 - δ) * st) := by
    intro j hj
    obtain ⟨h2, hn⟩ := hGok j hj
    have hb := Gint (lev j) (le_trans hA (hlevA j)) h2 hn
    rw [hRR]
    refine le_trans hb ?_
    have hls : (0 : ℝ) ≤ lev j + s := by linarith [hlevA j]
    have hden : Real.sqrt (1 - δ) * st ≤ Real.sqrt ((t : ℝ) - ⌈lev j / 4⌉₊) := by
      rw [hstdef, ← Real.sqrt_mul (by linarith) (t : ℝ)]
      refine Real.sqrt_le_sqrt ?_
      have h := hceil j hj
      have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
      linarith
    calc Ci * min 1 ((lev j + s) / Real.sqrt ((t : ℝ) - ⌈lev j / 4⌉₊))
        ≤ Ci * ((lev j + s) / Real.sqrt ((t : ℝ) - ⌈lev j / 4⌉₊)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCi.le
      _ ≤ Ci * ((lev j + s) / (Real.sqrt (1 - δ) * st)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hls hden0 hden) hCi.le
      _ = Ci * (lev j + s) / (Real.sqrt (1 - δ) * st) := by ring
  -- the `q`-th power of a restricted-chaos bound, in the target's variable
  set Kc : ℝ := Ci / Real.sqrt (1 - δ) with hKcdef
  have hKc0 : (0 : ℝ) ≤ Kc := div_nonneg hCi.le hsq1δ.le
  have hconv : ∀ x : ℝ, 0 ≤ x → (Ci * x / (Real.sqrt (1 - δ) * st)) ^ q
      = Kc ^ q * ((x * (1 - q)) ^ q * Λ ^ (-q)) := by
    intro x hx
    have heq : Ci * x / (Real.sqrt (1 - δ) * st) = Kc * ((x * (1 - q)) * Λ⁻¹) := by
      rw [hKcdef, hΛdef]
      field_simp
    rw [heq, Real.mul_rpow hKc0 (mul_nonneg (mul_nonneg hx h1q.le) (inv_nonneg.2 hΛ0.le)),
      Real.mul_rpow (mul_nonneg hx h1q.le) (inv_nonneg.2 hΛ0.le), Real.inv_rpow hΛ0.le,
      ← Real.rpow_neg hΛ0.le]
  -- the bad sets, replaced by measurable hulls of the same measure
  choose B hBsub hBmeas hBmeasure using fun j : ℕ => exists_measurable_superset ν
    {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h}
  have hBreal : ∀ j : ℕ, ν.real (B j) = ν.real {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h} := by
    intro j
    rw [measureReal_def, measureReal_def, hBmeasure j]
  set E : ℝ := (Cb * Real.exp (-(2 * A))) ^ (1 - q) with hEdef
  have hCbA : (0 : ℝ) ≤ Cb * Real.exp (-(2 * A)) := mul_nonneg hCb.le (Real.exp_pos _).le
  have hE0 : (0 : ℝ) ≤ E := Real.rpow_nonneg hCbA _
  have hbadpow : ∀ j : ℕ, ν.real (B j) ^ (1 - q) ≤ E * Real.exp (-2 * (j : ℝ)) := by
    intro j
    have h0 : (0 : ℝ) ≤ ν.real (B j) := measureReal_nonneg
    have h1 : ν.real (B j)
        ≤ (Cb * Real.exp (-(2 * A))) * Real.exp (-(2 * ((j : ℝ) / (1 - q)))) := by
      rw [hBreal j]
      refine le_trans (Gbad (lev j) (le_trans hA (hlevA j))) (le_of_eq ?_)
      rw [mul_assoc, ← Real.exp_add]
      simp only [hlevdef]
      congr 2
      ring
    have h2 := Real.rpow_le_rpow h0 h1 h1q.le
    rw [Real.mul_rpow hCbA (Real.exp_pos _).le, ← Real.exp_mul] at h2
    refine le_trans h2 (le_of_eq ?_)
    have hexp : -(2 * ((j : ℝ) / (1 - q))) * (1 - q) = -2 * (j : ℝ) := by
      field_simp
    rw [hexp]
  -- the pointwise decomposition, on the hulls
  have hpt : ∀ ω, ZZ ω ≤ RR 0 ω
      + (∑ j ∈ Finset.Ico 0 m, Set.indicator (B j) (fun _ => (1 : ℝ)) ω * RR (j + 1) ω)
      + Set.indicator (B m) (fun _ => (1 : ℝ)) ω * ZZ ω := by
    intro ω
    rw [hZZ, hRR]
    refine le_trans (hdec (fun j => Gset (lev j)) ω 0 m (Nat.zero_le _)) ?_
    have hstep : ∀ (j : ℕ) (w : ℝ), 0 ≤ w →
        Set.indicator {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h} (fun _ => (1 : ℝ)) ω * w
          ≤ Set.indicator (B j) (fun _ => (1 : ℝ)) ω * w := by
      intro j w hw
      refine mul_le_mul_of_nonneg_right ?_ hw
      by_cases hmem : ω ∈ {ω | ∃ h ∈ win, ω ∉ Gset (lev j) h}
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hBsub j hmem)]
      · rw [Set.indicator_of_notMem hmem]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.Ico 0 m) =>
      hstep j _ (by simpa [hRR] using hR0 (j + 1) ω))
    have htail := hstep m _ (by simpa [hZZ] using hZ0 ω)
    linarith
  have hmain := integral_rpow_le_of_decomposition hZ0 hR0 hZi hRi hBmeas hq0p hq1p 0 m hpt
  -- the three terms
  set u : ℝ := (A + s) * (1 - q) with hudef
  have hu0 : (0 : ℝ) ≤ u := mul_nonneg (by linarith) h1q.le
  have hΛq0 : (0 : ℝ) ≤ Λ ^ (-q) := Real.rpow_nonneg hΛ0.le _
  have hfirst : (∫ ω, RR 0 ω ∂ν) ^ q ≤ Kc ^ q * (u ^ q * Λ ^ (-q)) := by
    have h := hRle 0 (Nat.zero_le _)
    have hlev0 : lev 0 = A := by simp [hlevdef]
    rw [hlev0] at h
    have h2 := Real.rpow_le_rpow (hRmean0 0) h hq0
    rwa [hconv (A + s) (by linarith)] at h2
  have hterm : ∀ j : ℕ, j < m →
      ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q
        ≤ E * Kc ^ q * Λ ^ (-q) * (Real.exp (-2 * (j : ℝ)) * (u + (j : ℝ) + 1) ^ q) := by
    intro j hj
    have hbad := hbadpow j
    have h := hRle (j + 1) hj
    have hl0 : (0 : ℝ) ≤ lev (j + 1) + s := by linarith [hlevA (j + 1)]
    have h2 := Real.rpow_le_rpow (hRmean0 (j + 1)) h hq0
    rw [hconv _ hl0] at h2
    have hx : (lev (j + 1) + s) * (1 - q) = u + (j : ℝ) + 1 := by
      simp only [hlevdef, hudef]
      push_cast
      field_simp
      ring
    rw [hx] at h2
    have hprod := mul_le_mul hbad h2 (Real.rpow_nonneg (hRmean0 _) _)
      (mul_nonneg hE0 (Real.exp_pos _).le)
    calc ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q
        ≤ (E * Real.exp (-2 * (j : ℝ))) * (Kc ^ q * ((u + (j : ℝ) + 1) ^ q * Λ ^ (-q))) :=
          hprod
      _ = E * Kc ^ q * Λ ^ (-q) * (Real.exp (-2 * (j : ℝ)) * (u + (j : ℝ) + 1) ^ q) := by
          ring
  set S₁ : ℝ := (1 - Real.exp (-2))⁻¹ with hS₁def
  set S₂ : ℝ := Real.exp (-2) * ((1 - Real.exp (-2)) ^ 2)⁻¹ with hS₂def
  have hsum : (∑ j ∈ Finset.Ico 0 m, ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q)
      ≤ E * Kc ^ q * Λ ^ (-q) * ((u + 1) ^ q * S₁ + S₂) := by
    rw [← Finset.range_eq_Ico]
    refine le_trans (Finset.sum_le_sum fun j hj => hterm j (Finset.mem_range.1 hj)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_range_exp_mul_add_rpow_le hq0p hq1 hu0 m)
      (mul_nonneg (mul_nonneg hE0 (Real.rpow_nonneg hKc0 _)) hΛq0)
  have htail : ν.real (B m) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q
      ≤ Real.exp (-2) * E * C₁ ^ q * (1 + Λ) ^ (-q) := by
    have hbad := hbadpow m
    have hexp := exp_neg_two_mul_le_exp_neg_two_mul_rpow_neg hΛ0.le hm_ge hq1
    calc ν.real (B m) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q
        ≤ (E * Real.exp (-2 * (m : ℝ))) * C₁ ^ q :=
          mul_le_mul hbad hZpow (Real.rpow_nonneg hZmean0 _)
            (mul_nonneg hE0 (Real.exp_pos _).le)
      _ ≤ (E * (Real.exp (-2) * (1 + Λ) ^ (-q))) * C₁ ^ q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hE0)
            (Real.rpow_nonneg hC₁.le _)
      _ = Real.exp (-2) * E * C₁ ^ q * (1 + Λ) ^ (-q) := by ring
  -- assemble
  have hΛtar := rpow_neg_le_one_add_inv_rpow_mul hlam0 hD.le hq0
  have htar1 : (0 : ℝ) ≤ (1 + Λ) ^ (-q) := Real.rpow_nonneg (by linarith) _
  have hS₁0 : (0 : ℝ) ≤ S₁ :=
    inv_nonneg.2 (by linarith [Real.exp_lt_one_iff.2 (show (-2 : ℝ) < 0 by norm_num)])
  have hS₂0 : (0 : ℝ) ≤ S₂ := mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (sq_nonneg _))
  have hbr : (0 : ℝ) ≤ u ^ q + E * ((u + 1) ^ q * S₁ + S₂) := by
    have hu1 : (0 : ℝ) ≤ (u + 1) ^ q := Real.rpow_nonneg (by linarith) q
    have := mul_nonneg hE0 (add_nonneg (mul_nonneg hu1 hS₁0) hS₂0)
    linarith [Real.rpow_nonneg hu0 q]
  have hKceq : ((1 + lam⁻¹) * Ci / Real.sqrt (1 - δ)) ^ q = (1 + lam⁻¹) ^ q * Kc ^ q := by
    rw [hKcdef, mul_div_assoc, Real.mul_rpow (by positivity) hKc0]
  have hKc0q : (0 : ℝ) ≤ Kc ^ q := Real.rpow_nonneg hKc0 _
  calc (∫ ω, ZZ ω ^ q ∂ν)
      ≤ (∫ ω, RR 0 ω ∂ν) ^ q
        + (∑ j ∈ Finset.Ico 0 m, ν.real (B j) ^ (1 - q) * (∫ ω, RR (j + 1) ω ∂ν) ^ q)
        + ν.real (B m) ^ (1 - q) * (∫ ω, ZZ ω ∂ν) ^ q := hmain
    _ ≤ Kc ^ q * Λ ^ (-q) * (u ^ q + E * ((u + 1) ^ q * S₁ + S₂))
        + Real.exp (-2) * E * C₁ ^ q * (1 + Λ) ^ (-q) := by
        have h1 : Kc ^ q * (u ^ q * Λ ^ (-q)) + E * Kc ^ q * Λ ^ (-q) * ((u + 1) ^ q * S₁ + S₂)
            = Kc ^ q * Λ ^ (-q) * (u ^ q + E * ((u + 1) ^ q * S₁ + S₂)) := by ring
        linarith [hfirst, hsum, htail]
    _ ≤ Kc ^ q * ((1 + lam⁻¹) ^ q * (1 + Λ) ^ (-q)) * (u ^ q + E * ((u + 1) ^ q * S₁ + S₂))
        + Real.exp (-2) * E * C₁ ^ q * (1 + Λ) ^ (-q) := by
        have h := mul_le_mul_of_nonneg_left hΛtar hKc0q
        have h2 := mul_le_mul_of_nonneg_right h hbr
        linarith
    _ = (((1 + lam⁻¹) * Ci / Real.sqrt (1 - δ)) ^ q * (u ^ q + E * ((u + 1) ^ q * S₁ + S₂))
        + Real.exp (-2) * E * C₁ ^ q) * (1 + Λ) ^ (-q) := by
        rw [hKceq]
        ring
    _ ≤ shiftMomentConst C₁ Ci Cb A s lam δ q * (1 + Λ) ^ (-q) :=
        mul_le_mul_of_nonneg_right hKD htar1

/-! ### The Steinhaus chaos -/

/-- **A good family with separate constants**: `RMF.GoodFamily` with the bad sets at `C_b` and the
restricted chaos at `C_i`, with an additive shift `s` of the level. -/
structure GoodFamilySplit {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℂ) (ν : Measure Ω)
    (x σ : ℝ) (t n₀ : ℕ) (a₀ Cb Ci s : ℝ) where
  /-- The good set at level `a` and height `h`. -/
  set : ℝ → ℝ → Set Ω
  measurableSet : ∀ a h, MeasurableSet (set a h)
  measurableSet_uncurry : ∀ a, MeasurableSet {p : Ω × ℝ | p.1 ∈ set a p.2}
  /-- The bad set is exponentially small in the level. -/
  measure_bad_le : ∀ a, a₀ ≤ a →
    ν.real {ω | ∃ h ∈ Set.Ico (0 : ℝ) 1, ω ∉ set a h} ≤ Cb * Real.exp (-(2 * a))
  /-- The chaos, restricted to the good set. -/
  integral_restricted_le : ∀ a, a₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ t → n₀ ≤ t - ⌈a / 4⌉₊ →
    (∫ ω, restrictedChaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ (set a) ω ∂ν)
      ≤ Ci * min 1 ((a + s) / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))

/-- **The level-shift interpolation for the Steinhaus RMF**:
`RMF.integral_rpow_le_of_goodSets_shift` on the unit window, for a split good family. -/
theorem integral_rpow_le_of_goodFamilySplit {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsSteinhausPrimeValues Y ν) {x σ q : ℝ} {t n₀ : ℕ} {a₀ C₁ Ci Cb A s lam δ : ℝ}
    (hx2 : (2 : ℝ) ≤ x) (hxgt1 : (1 : ℝ) < x) (hσ0 : 0 ≤ σ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hC₁ : 0 < C₁) (hCi : 0 < Ci) (hCb : 0 < Cb)
    (hA : a₀ ≤ A) (hA0 : 0 ≤ A) (hs : 0 ≤ s) (hlam : 1 ≤ lam) (hδ : δ ≤ 1 / 2)
    (hZmean : (∫ ω, chaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ ω ∂ν) ≤ C₁)
    (hT : A / 4 + 3 * Real.sqrt (t : ℝ) / 4 + 1 + (n₀ : ℝ) ≤ δ * t)
    (G : GoodFamilySplit Y ν x σ t n₀ a₀ Cb Ci s) :
    (∫ ω, chaosUnitShift
        (fun ω => compMultExtension fun p => Y p ω) x σ ω ^ q ∂ν)
      ≤ shiftMomentConst C₁ Ci Cb A s lam δ q * (1 + (1 - q) * Real.sqrt (t : ℝ)) ^ (-q) := by
  haveI := hY.isProbabilityMeasure
  exact integral_rpow_le_of_goodSets_shift
    (Z := chaosUnitShift (fun ω => compMultExtension fun p => Y p ω) x σ)
    (Rst := fun S => restrictedChaosUnitShift
      (fun ω => compMultExtension fun p => Y p ω) x σ S)
    (win := Set.Ico (0 : ℝ) 1)
    (fun ω => chaosUnitShift_nonneg hx2 ω)
    (integrable_chaosUnitShift hY x σ (by linarith))
    (fun S ω => restrictedChaosUnitShift_nonneg hxgt1 σ S ω)
    (fun S hm hu => integrable_restrictedChaosUnitShift hY x σ (by linarith) S hm hu)
    (fun S ω r m hrm => chaosUnitShift_le_decomposition hxgt1 σ S ω r m hrm)
    hq0 hq1 hC₁ hCi hCb hA hA0 hs hlam hδ hZmean hT
    G.set G.measurableSet G.measurableSet_uncurry G.measure_bad_le G.integral_restricted_le

end RMF
