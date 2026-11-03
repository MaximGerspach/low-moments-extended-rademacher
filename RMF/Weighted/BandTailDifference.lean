/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BandTail

/-!
# The band tail on `[1, ∞)`: Plancherel without a left shift

On `w ≥ 1` the band tail `T(w) = ∑_{m > w} X(m)/√m` is a *head* sum: of the coefficients
`c₁ = F_{y,z}(½) - 1` and `c_m = -X(m)/√m` for `m ≥ 2`, whose Dirichlet polynomial is
`F_{y,z}(½) - F_{y,z}(½ + s)`.  Head Parseval (`RMF.integral_normSq_partialSum_eq_line`)
therefore gives, for every `σ > 0`,

`∫_1^∞ |T(w)|² w^{-1-2σ} dw = (2π)⁻¹ ∫_ℝ |F(½) - F(½+σ+it)|²/|σ+it|² dt`

(`RMF.integral_normSq_blockTailSum_eq_line_sub`).  Tail Plancherel
(`RMF.integral_normSq_blockTailSum_eq_line`) reads the same tail on all of `w > 0`, where `T(w)` is
the coherent value `F(½)` below `1`, and so needs the line `½ - c` to the left of `½`.  Here that
range is absent, and the difference vanishes at `s = 0`.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*}

/-- **Below `1` the band tail is the whole band product**: `T_{y,z}(w) = F_{y,z}(½)` for `w < 1`,
since every index exceeds `⌊w⌋₊ = 0` (`RMF.sum_blockWeighted_cpow_eq_randomEulerProductIco`). -/
lemma blockTailSum_of_lt_one {X : ℕ → Ω → ℂ} (y z : ℕ) {w : ℝ} (hw : w < 1) (ω : Ω) :
    blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω
      = randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          (1 / 2 : ℂ) ω := by
  rw [← sum_blockWeighted_cpow_eq_randomEulerProductIco y z (1 / 2 : ℂ) ω, blockTailSum,
    Nat.floor_eq_zero.2 hw]
  refine Finset.sum_congr (Finset.filter_congr fun m hm => ?_) fun m hm => ?_
  · have h0 : 0 < m := (Finset.mem_Icc.1 hm).1
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h0⟩⟩
  · have hm0 : (m : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1; omega)
    have hsq : (((Real.sqrt m : ℝ) : ℂ))⁻¹ = (m : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg m)]
      norm_num
    rw [div_eq_mul_inv, hsq]

/-- **The integrand of Plancherel on `[1, ∞)` is integrable**: `|T(w)|² w^{-1-2σ}` for `σ > 0`,
the tail being bounded and measurable. -/
lemma integrableOn_normSq_blockTailSum_div_rpow (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (ω : Ω) :
    IntegrableOn (fun w : ℝ => ‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ)) (Set.Ioi 1) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ w, ‖blockTailSum f y z w ω‖ ≤ B :=
    ⟨_, fun w => norm_blockTailSum_le_sum f y z w ω⟩
  have hmeas : Measurable fun w : ℝ => ‖blockTailSum f y z w ω‖ ^ 2 :=
    (measurable_blockTailSum_truncation f y z ω).norm.pow_const 2
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-(1 + 2 * σ))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have h : IntegrableOn (fun w : ℝ => ‖blockTailSum f y z w ω‖ ^ 2 * w ^ (-(1 + 2 * σ)))
      (Set.Ioi 1) := by
    refine hpow.bdd_mul (c := B ^ 2) hmeas.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB w) 2
  refine IntegrableOn.congr_fun h (fun w hw => ?_) measurableSet_Ioi
  rw [Real.rpow_neg (le_of_lt (lt_trans one_pos hw)), div_eq_mul_inv]

/-- **Plancherel for the band tail on `[1, ∞)`.**  For `σ > 0`,
`∫_1^∞ |T_{y,z}(w)|² w^{-1-2σ} dw = (2π)⁻¹ ∫_ℝ |F_{y,z}(½) - F_{y,z}(½+σ+it)|²/|σ+it|² dt`.

Head Parseval (`RMF.integral_normSq_partialSum_eq_line`) at the coefficients
`c_n = [n = 1]·F(½) - X(n)/√n` (the second over the band's `n ≤ z#`): their head sums vanish below
`1` and are the band tail above it, and their Dirichlet polynomial is `F(½) - F(½ + s)`
(`RMF.sum_blockWeighted_cpow_eq_randomEulerProductIco`). -/
theorem integral_normSq_blockTailSum_eq_line_sub {X : ℕ → Ω → ℂ} (y z : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (ω : Ω) :
    (∫ w in Set.Ioi (1 : ℝ),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2
          / w ^ (1 + 2 * σ))
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
          ‖(randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
                (1 / 2 : ℂ) ω
              - randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                (z + 1) ((1 / 2 : ℂ) + (σ : ℂ) + (t : ℂ) * Complex.I) ω)
            / ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  classical
  set f : Ω → ArithmeticFunction ℂ := fun ω => squarefreeExtension fun p => X p ω with hf
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = fun s => randomEulerProductIco f (y + 1) (z + 1) s ω :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = {m ∈ Finset.Icc 1 (primorial z) |
      m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m} := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℂ, φ = fun n => f ω n / (Real.sqrt n : ℂ) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℂ, g = fun n => if n ∈ S then φ n else 0 := ⟨_, rfl⟩
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => by
    rw [hS] at hn
    exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
  have h1S : 1 ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, primorial_pos z⟩, Nat.mem_smoothNumbers.2 ⟨one_ne_zero, by simp⟩,
      isRough_one y⟩
  -- the band product as a Dirichlet polynomial in `φ`
  have hF : ∀ s : ℂ, F ((1 / 2 : ℂ) + s) = ∑ n ∈ S, φ n * (n : ℂ) ^ (-s) := by
    intro s
    rw [hFdef]
    dsimp only
    rw [← sum_blockWeighted_cpow_eq_randomEulerProductIco y z ((1 / 2 : ℂ) + s) ω, ← hS]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hS1 n hn; omega)
    have hsq : (((Real.sqrt n : ℝ) : ℂ))⁻¹ = (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      norm_num
    rw [hφ]
    dsimp only
    rw [show -((1 / 2 : ℂ) + s) = -(1 / 2 : ℂ) + -s by ring, Complex.cpow_add _ _ hn0, ← hsq]
    simp only [hf, div_eq_mul_inv]
    ring
  have hF0 : F (1 / 2 : ℂ) = ∑ n ∈ S, φ n := by
    have h := hF 0
    rw [add_zero] at h
    rw [h]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [neg_zero, Complex.cpow_zero, mul_one]
  -- the coefficients
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => (if n = 1 then F (1 / 2 : ℂ) else 0) - g n :=
    ⟨_, rfl⟩
  have hsupp : ∀ n ∉ S, c n = 0 := by
    intro n hn
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hn h1S
    rw [hc, hg]
    dsimp only
    rw [if_neg h1, if_neg hn, sub_zero]
  -- their head sums: the band tail from `1` on, nothing below
  have hhead : ∀ u : ℝ, ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n
      = Set.indicator (Set.Ici (1 : ℝ)) (fun w => blockTailSum f y z w ω) u := by
    intro u
    by_cases hu : 1 ≤ u
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 hu)]
      have hN : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu)
      have h1 : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (if n = 1 then F (1 / 2 : ℂ) else 0)
          = F (1 / 2 : ℂ) := by
        rw [Finset.sum_ite_eq' (Finset.Icc 1 ⌊u⌋₊) 1 (fun _ => F (1 / 2 : ℂ)),
          if_pos (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)]
      have h2 : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, g n = ∑ n ∈ S with n ≤ ⌊u⌋₊, φ n := by
        rw [hg, ← Finset.sum_filter]
        refine Finset.sum_congr (Finset.ext fun n => ?_) fun _ _ => rfl
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩
          exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩
          exact ⟨⟨hS1 n h3, h2⟩, h3⟩
      have h3 : blockTailSum f y z u ω = ∑ n ∈ S with ¬ n ≤ ⌊u⌋₊, φ n := by
        rw [blockTailSum, hφ, hS, Finset.filter_filter]
        refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
        rw [not_le, and_assoc]
      rw [hc]
      dsimp only
      rw [Finset.sum_sub_distrib, h1, h2, h3, hF0,
        ← Finset.sum_filter_add_sum_filter_not S (fun n => n ≤ ⌊u⌋₊) φ]
      ring
    · rw [Set.indicator_of_notMem (fun h => hu (Set.mem_Ici.1 h))]
      have h0 : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.2 (not_le.1 hu)
      rw [h0, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  -- their Dirichlet polynomial: `F(½) - F(½ + s)`
  have hpoly : ∀ s : ℂ, ∑' n : ℕ, c n / (n : ℂ) ^ s = F (1 / 2 : ℂ) - F ((1 / 2 : ℂ) + s) := by
    intro s
    rw [tsum_eq_sum (s := S) fun n hn => by rw [hsupp n hn, zero_div], hF s]
    have hsplit : ∀ n ∈ S, c n / (n : ℂ) ^ s
        = (if n = 1 then F (1 / 2 : ℂ) else 0) - φ n * (n : ℂ) ^ (-s) := by
      intro n hn
      rw [hc, hg]
      dsimp only
      rw [if_pos hn, sub_div, Complex.cpow_neg, div_eq_mul_inv (φ n)]
      congr 1
      split_ifs with h
      · rw [h, Nat.cast_one, Complex.one_cpow, div_one]
      · rw [zero_div]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' S 1 (fun _ => F (1 / 2 : ℂ)), if_pos h1S]
  -- summability, from the finite support
  have hsum : Summable (coeffWeight σ c) :=
    summable_of_ne_finset_zero (s := S) fun n hn => by
      rw [coeffWeight, hsupp n hn, norm_zero, zero_div]
  have hpars := integral_normSq_partialSum_eq_line σ c hσ hsum
  -- the left side: the head sums are the band tail on `[1, ∞)`
  have hL : (∫ u in Set.Ioi (0 : ℝ), ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n‖ ^ 2 / u ^ (1 + 2 * σ))
      = ∫ w in Set.Ioi (1 : ℝ), ‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ) := by
    have hpt : ∀ u : ℝ, ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n‖ ^ 2 / u ^ (1 + 2 * σ)
        = Set.indicator (Set.Ici (1 : ℝ))
            (fun w => ‖blockTailSum f y z w ω‖ ^ 2 / w ^ (1 + 2 * σ)) u := by
      intro u
      rw [hhead u]
      by_cases hu : u ∈ Set.Ici (1 : ℝ)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero,
          zero_pow two_ne_zero, zero_div]
    simp_rw [hpt]
    rw [setIntegral_indicator measurableSet_Ici,
      show Set.Ioi (0 : ℝ) ∩ Set.Ici 1 = Set.Ici 1 from
        Set.inter_eq_right.2 fun u hu => lt_of_lt_of_le one_pos (Set.mem_Ici.1 hu),
      integral_Ici_eq_integral_Ioi]
  rw [← hL, hpars]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hpoly, hFdef, add_assoc]

end RMF
