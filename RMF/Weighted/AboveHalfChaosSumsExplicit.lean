/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The chaos windows' sums above `q = ½`

A level's windows carry the weights `e^{-am}` and the chaos profile `RMF.chaosProf A m` (`1` below
`2008`, then `min 1 (A(m-8)^{-1/4})`).  Their sums `RMF.profSum a A J` are bounded by the Gamma
integral,

`profSum a A J ≤ ∑_{1≤m<2008} e^{-am} + A(Γ(3/4)a^{-3/4} - e^{-1999a}(4/3)1999^{3/4})`

(`RMF.profSum_le_gamma`), for short levels by `2007 + A(4/3)J^{3/4}`
(`RMF.profSum_le_small`), and a level's tail past `N` from below by an integral
(`RMF.tail_profSum_ge_integral`), which prices the restart of the chaos at the next level.
-/

open MeasureTheory Set

namespace RMF

/-- The chaos profile of a window at local index `m`: `1` below `2008`, then
`min 1 (A(m-8)^{-1/4})`. -/
noncomputable def chaosProf (A : ℝ) (m : ℕ) : ℝ :=
  if 2008 ≤ m then min 1 (A * ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) else 1

/-- The profile's window sum `∑_{1 ≤ m < J} e^{-am}·RMF.chaosProf A m`. -/
noncomputable def profSum (a A : ℝ) (J : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 J, Real.exp (-(a * m)) * chaosProf A m

lemma chaosProf_le_one (A : ℝ) (m : ℕ) : chaosProf A m ≤ 1 := by
  rw [chaosProf]; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma chaosProf_nonneg {A : ℝ} (hA : 0 ≤ A) (m : ℕ) : 0 ≤ chaosProf A m := by
  rw [chaosProf]; split_ifs
  · exact le_min zero_le_one (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · exact zero_le_one

lemma profSum_nonneg {a A : ℝ} (hA : 0 ≤ A) (J : ℕ) : 0 ≤ profSum a A J :=
  Finset.sum_nonneg fun m _ => mul_nonneg (Real.exp_pos _).le (chaosProf_nonneg hA m)

lemma profSum_mono {a A : ℝ} (hA : 0 ≤ A) {J J' : ℕ} (h : J ≤ J') :
    profSum a A J ≤ profSum a A J' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right h)
    fun m _ _ => mul_nonneg (Real.exp_pos _).le (chaosProf_nonneg hA m)

/-- A profile sum is at most its number of windows. -/
lemma profSum_le_card {a A : ℝ} (ha : 0 ≤ a) (J : ℕ) : profSum a A J ≤ (J : ℝ) := by
  rw [profSum]
  calc ∑ m ∈ Finset.Ico 1 J, Real.exp (-(a * m)) * chaosProf A m
      ≤ ∑ m ∈ Finset.Ico 1 J, (1 : ℝ) := Finset.sum_le_sum fun m _ => by
        have h1 : Real.exp (-(a * m)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) m; nlinarith)
        have h2 := chaosProf_le_one A m
        by_cases h0 : 0 ≤ chaosProf A m
        · calc Real.exp (-(a * m)) * chaosProf A m ≤ 1 * 1 :=
                mul_le_mul h1 h2 h0 zero_le_one
            _ = 1 := one_mul 1
        · have : Real.exp (-(a * m)) * chaosProf A m ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (le_of_not_ge h0)
          linarith
    _ = ((Finset.Ico 1 J).card : ℝ) := by simp
    _ ≤ J := by rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le J 1

/-! ### The Gamma integral -/

lemma integrableOn_rpow_quarter_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 4)) (p := 1) (b := a)
    (by norm_num) le_rfl ha
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

lemma integral_rpow_quarter_exp_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi 0, t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t))
      = (1 / a) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3 / 4) (r := a) (by norm_num) ha
  rw [show (3 / 4 : ℝ) - 1 = -(1 / 4) by norm_num] at h
  exact h

lemma intervalIntegrable_rpow_quarter_exp (a X Y : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t))) volume X Y :=
  (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).mul_continuousOn
    (Real.continuous_exp.comp (by fun_prop)).continuousOn

/-- `∫_0^X t^{-1/4}e^{-at}dt ≤ Γ(3/4)a^{-3/4}`. -/
lemma intervalIntegral_rpow_quarter_exp_le {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) :
    ∫ t in (0 : ℝ)..X, t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t))
      ≤ (1 / a) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4) := by
  rw [← integral_rpow_quarter_exp_Ioi ha, intervalIntegral.integral_of_le hX]
  refine setIntegral_mono_set (integrableOn_rpow_quarter_exp ha) ?_
    (Ioc_subset_Ioi_self).eventuallyLE
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le

/-- `∫_0^X t^{-1/4}e^{-at}dt ≥ e^{-aX}(4/3)X^{3/4}` for `a ≥ 0`. -/
lemma intervalIntegral_rpow_quarter_exp_ge {a X : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X) :
    Real.exp (-(a * X)) * (4 / 3 * X ^ (3 / 4 : ℝ))
      ≤ ∫ t in (0 : ℝ)..X, t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t)) := by
  have hint : ∫ t in (0 : ℝ)..X, t ^ (-(1 / 4 : ℝ)) = 4 / 3 * X ^ (3 / 4 : ℝ) := by
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [show -(1 / 4 : ℝ) + 1 = 3 / 4 by norm_num, Real.zero_rpow (by norm_num)]
    ring
  rw [← hint, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hX
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
    (intervalIntegrable_rpow_quarter_exp a 0 X) fun t ht => ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht.1 _)
  nlinarith [ht.2]

/-- `t ↦ t^{-1/4}e^{-at}` decreases on `(0, ∞)`. -/
lemma antitoneOn_rpow_quarter_exp {a : ℝ} (ha : 0 ≤ a) {X Y : ℝ} (hX : 0 < X) :
    AntitoneOn (fun t : ℝ => t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t))) (Icc X Y) := by
  intro s hs t ht hst
  have hs0 : 0 < s := lt_of_lt_of_le hX hs.1
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hs0 hst (by norm_num))
    (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
    (Real.rpow_nonneg hs0.le _)

/-- **The chaos windows' sum by the Gamma integral**: for `a > 0` and `N ≥ 2000`,
`∑_{2000 ≤ n < N} e^{-an}n^{-1/4} ≤ Γ(3/4)a^{-3/4} - e^{-1999a}(4/3)1999^{3/4}`. -/
theorem sum_exp_rpow_quarter_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ n ∈ Finset.Ico 2000 N, Real.exp (-(a * n)) * (n : ℝ) ^ (-(1 / 4 : ℝ))
      ≤ (1 / a) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)
        - Real.exp (-(a * 1999)) * (4 / 3 * (1999 : ℝ) ^ (3 / 4 : ℝ)) := by
  set f : ℝ → ℝ := fun t => t ^ (-(1 / 4 : ℝ)) * Real.exp (-(a * t)) with hfdef
  rcases le_or_gt N 2000 with hN | hN
  · rw [Finset.Ico_eq_empty_of_le hN, Finset.sum_empty, sub_nonneg]
    refine le_trans (intervalIntegral_rpow_quarter_exp_ge ha.le (by norm_num)) ?_
    exact intervalIntegral_rpow_quarter_exp_le ha (by norm_num)
  -- the sum is `∑_{1999 ≤ i < N-1} f(i+1)`
  have hre : ∑ n ∈ Finset.Ico 2000 N, Real.exp (-(a * n)) * (n : ℝ) ^ (-(1 / 4 : ℝ))
      = ∑ i ∈ Finset.Ico 1999 (N - 1), f ((i + 1 : ℕ) : ℝ) := by
    rw [hfdef]
    refine Finset.sum_bij (fun n _ => n - 1) (fun n hn => ?_) (fun n hn n' hn' h => ?_)
      (fun i hi => ⟨i + 1, ?_, ?_⟩) (fun n hn => ?_)
    · simp only [Finset.mem_Ico] at hn ⊢; omega
    · simp only [Finset.mem_Ico] at hn hn'; omega
    · simp only [Finset.mem_Ico] at hi ⊢; omega
    · simp
    · simp only [Finset.mem_Ico] at hn
      rw [show n - 1 + 1 = n by omega]
      ring
  rw [hre]
  have hsum := AntitoneOn.sum_le_integral_Ico (f := f) (a := 1999) (b := N - 1) (by omega)
    (antitoneOn_rpow_quarter_exp ha.le (by norm_num))
  refine le_trans hsum ?_
  have hsplit : ∫ t in ((1999 : ℕ) : ℝ)..((N - 1 : ℕ) : ℝ), f t
      = (∫ t in (0 : ℝ)..((N - 1 : ℕ) : ℝ), f t) - ∫ t in (0 : ℝ)..((1999 : ℕ) : ℝ), f t := by
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_rpow_quarter_exp a _ _)
      (intervalIntegrable_rpow_quarter_exp a _ _)]
  rw [hsplit]
  have h1 := intervalIntegral_rpow_quarter_exp_le ha (Nat.cast_nonneg (N - 1))
  have h2 := intervalIntegral_rpow_quarter_exp_ge ha.le (by norm_num : (0 : ℝ) ≤ 1999)
  push_cast at h2 ⊢
  linarith

/-- `∑_{2000 ≤ n < N} n^{-1/4} ≤ (4/3)N^{3/4}`. -/
theorem sum_rpow_quarter_le (N : ℕ) :
    ∑ n ∈ Finset.Ico 2000 N, (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 4 / 3 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  set f : ℝ → ℝ := fun t => t ^ (-(1 / 4 : ℝ)) * Real.exp (-(0 * t)) with hfdef
  have hN0 : (0 : ℝ) ≤ 4 / 3 * (N : ℝ) ^ (3 / 4 : ℝ) := by positivity
  rcases le_or_gt N 2000 with hN | hN
  · rw [Finset.Ico_eq_empty_of_le hN, Finset.sum_empty]; exact hN0
  have hre : ∑ n ∈ Finset.Ico 2000 N, (n : ℝ) ^ (-(1 / 4 : ℝ))
      = ∑ i ∈ Finset.Ico 1999 (N - 1), f ((i + 1 : ℕ) : ℝ) := by
    rw [hfdef]
    refine Finset.sum_bij (fun n _ => n - 1) (fun n hn => ?_) (fun n hn n' hn' h => ?_)
      (fun i hi => ⟨i + 1, ?_, ?_⟩) (fun n hn => ?_)
    · simp only [Finset.mem_Ico] at hn ⊢; omega
    · simp only [Finset.mem_Ico] at hn hn'; omega
    · simp only [Finset.mem_Ico] at hi ⊢; omega
    · simp
    · simp only [Finset.mem_Ico] at hn
      rw [show n - 1 + 1 = n by omega]
      simp
  rw [hre]
  have hsum := AntitoneOn.sum_le_integral_Ico (f := f) (a := 1999) (b := N - 1) (by omega)
    (antitoneOn_rpow_quarter_exp le_rfl (by norm_num))
  refine le_trans hsum ?_
  have hsplit : ∫ t in ((1999 : ℕ) : ℝ)..((N - 1 : ℕ) : ℝ), f t
      = (∫ t in (0 : ℝ)..((N - 1 : ℕ) : ℝ), f t) - ∫ t in (0 : ℝ)..((1999 : ℕ) : ℝ), f t := by
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_rpow_quarter_exp 0 _ _)
      (intervalIntegrable_rpow_quarter_exp 0 _ _)]
  rw [hsplit]
  have hval : ∀ X : ℝ, 0 ≤ X → ∫ t in (0 : ℝ)..X, f t = 4 / 3 * X ^ (3 / 4 : ℝ) := by
    intro X hX
    rw [hfdef]
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
    rw [integral_rpow (Or.inl (by norm_num)), show -(1 / 4 : ℝ) + 1 = 3 / 4 by norm_num,
      Real.zero_rpow (by norm_num)]
    ring
  rw [hval _ (Nat.cast_nonneg _), hval _ (Nat.cast_nonneg _)]
  have h1 : ((N - 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le N 1) (by norm_num)
  have h2 : 0 ≤ ((1999 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by positivity
  linarith

/-- The profile past `2008` is at most `A(m-8)^{-1/4}`, and at least `A(m + t₁)^{-1/4}` everywhere
once `A^4 ≤ t₁`. -/
lemma chaosProf_le {A : ℝ} {m : ℕ} (hm : 2008 ≤ m) :
    chaosProf A m ≤ A * ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
  rw [chaosProf, if_pos hm]
  exact min_le_right _ _

lemma chaosProf_ge {A t₁ : ℝ} (hA : 0 ≤ A) (ht₁ : A ^ 4 ≤ t₁) (m : ℕ) :
    A * ((m : ℝ) + t₁) ^ (-(1 / 4 : ℝ)) ≤ chaosProf A m := by
  have ht₁0 : 0 ≤ t₁ := le_trans (by positivity) ht₁
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpos : 0 < (m : ℝ) + t₁ ∨ (m : ℝ) + t₁ = 0 := by
    rcases lt_or_eq_of_le (add_nonneg hm0 ht₁0) with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  -- `A(m + t₁)^{-1/4} ≤ 1`
  have hle1 : A * ((m : ℝ) + t₁) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    rcases hpos with hpos | h0
    · have h4 : A ^ 4 ≤ (m : ℝ) + t₁ := by linarith
      have hA4 : A = (A ^ 4) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA]; norm_num
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hpos _)]
      rw [hA4]
      exact Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    · rw [h0, Real.zero_rpow (by norm_num), mul_zero]; exact zero_le_one
  rw [chaosProf]
  split_ifs with hm
  · refine le_min hle1 (mul_le_mul_of_nonneg_left ?_ hA)
    have h8 : (0 : ℝ) < ((m - 8 : ℕ) : ℝ) := by
      have : 0 < m - 8 := by omega
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos h8 (by push_cast [Nat.cast_sub (by omega : 8 ≤ m)]; linarith)
      (by norm_num)
  · exact hle1

/-! ### The profile sums -/

/-- **The profile sum by the Gamma integral**: for `a > 0`, `A ≥ 0` and every `J`,
`profSum a A J ≤ ∑_{1≤m<2008} e^{-am} + A(Γ(3/4)a^{-3/4} - e^{-1999a}(4/3)1999^{3/4})`. -/
theorem profSum_le_gamma {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (J : ℕ) :
    profSum a A J ≤ ∑ m ∈ Finset.Ico (1 : ℕ) 2008, Real.exp (-(a * (m : ℝ)))
      + A * ((1 / a) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)
        - Real.exp (-(a * 1999)) * (4 / 3 * (1999 : ℝ) ^ (3 / 4 : ℝ))) := by
  refine le_trans (profSum_mono hA (le_max_left J 2008)) ?_
  rw [profSum, ← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 2008) (le_max_right J 2008)]
  refine add_le_add (Finset.sum_le_sum fun m _ => ?_) ?_
  · exact mul_le_of_le_one_right (Real.exp_pos _).le (chaosProf_le_one A m)
  -- the chaos part, shifted by `8`
  have hterm : ∀ m ∈ Finset.Ico 2008 (max J 2008), Real.exp (-(a * m)) * chaosProf A m
      ≤ A * (Real.exp (-(a * ((m - 8 : ℕ) : ℝ))) * ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) := by
    intro m hm
    have hm' := (Finset.mem_Ico.1 hm).1
    have h1 : Real.exp (-(a * m)) ≤ Real.exp (-(a * ((m - 8 : ℕ) : ℝ))) := by
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ ha.le))
      exact_mod_cast Nat.sub_le m 8
    have h2 := chaosProf_le (A := A) hm'
    have h3 : 0 ≤ chaosProf A m := chaosProf_nonneg hA m
    calc Real.exp (-(a * m)) * chaosProf A m
        ≤ Real.exp (-(a * ((m - 8 : ℕ) : ℝ))) * (A * ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul h1 h2 h3 (Real.exp_pos _).le
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hre : ∑ m ∈ Finset.Ico 2008 (max J 2008),
      Real.exp (-(a * ((m - 8 : ℕ) : ℝ))) * ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
      = ∑ n ∈ Finset.Ico 2000 (max J 2008 - 8),
        Real.exp (-(a * n)) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    refine Finset.sum_bij (fun m _ => m - 8) (fun m hm => ?_) (fun m hm m' hm' h => ?_)
      (fun n hn => ⟨n + 8, ?_, ?_⟩) (fun m hm => rfl)
    · simp only [Finset.mem_Ico] at hm ⊢; omega
    · simp only [Finset.mem_Ico] at hm hm'; omega
    · simp only [Finset.mem_Ico] at hn ⊢; omega
    · simp
  rw [hre]
  exact sum_exp_rpow_quarter_le ha _

/-- **A short level's profile sum**: `profSum a A J ≤ 2007 + A(4/3)J^{3/4}` for `a ≥ 0`. -/
theorem profSum_le_small {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (J : ℕ) :
    profSum a A J ≤ 2007 + A * (4 / 3 * (J : ℝ) ^ (3 / 4 : ℝ)) := by
  refine le_trans (profSum_mono hA (le_max_left J 2008)) ?_
  rw [profSum, ← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 2008) (le_max_right J 2008)]
  refine add_le_add ?_ ?_
  · calc ∑ m ∈ Finset.Ico (1 : ℕ) 2008, Real.exp (-(a * (m : ℝ))) * chaosProf A m
        ≤ ∑ m ∈ Finset.Ico (1 : ℕ) 2008, (1 : ℝ) := Finset.sum_le_sum fun m _ => by
          have h1 : Real.exp (-(a * (m : ℝ))) ≤ 1 :=
            Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) m; nlinarith)
          exact le_trans (mul_le_of_le_one_right (Real.exp_pos _).le (chaosProf_le_one A m)) h1
      _ = 2007 := by rw [Finset.sum_const, Nat.card_Ico]; norm_num
  rcases le_or_gt J 2008 with hJ | hJ
  · rw [max_eq_right hJ, Finset.Ico_self, Finset.sum_empty]; positivity
  rw [max_eq_left hJ.le]
  have hterm : ∀ m ∈ Finset.Ico 2008 J, Real.exp (-(a * m)) * chaosProf A m
      ≤ A * ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro m hm
    have hm' := (Finset.mem_Ico.1 hm).1
    have h1 : Real.exp (-(a * m)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) m; nlinarith)
    exact le_trans (mul_le_of_le_one_left (chaosProf_nonneg hA m) h1) (chaosProf_le hm')
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hre : ∑ m ∈ Finset.Ico 2008 J, ((m - 8 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))
      = ∑ n ∈ Finset.Ico 2000 (J - 8), (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    refine Finset.sum_bij (fun m _ => m - 8) (fun m hm => ?_) (fun m hm m' hm' h => ?_)
      (fun n hn => ⟨n + 8, ?_, ?_⟩) (fun m hm => rfl)
    · simp only [Finset.mem_Ico] at hm ⊢; omega
    · simp only [Finset.mem_Ico] at hm hm'; omega
    · simp only [Finset.mem_Ico] at hn ⊢; omega
    · simp
  rw [hre]
  refine le_trans (sum_rpow_quarter_le _) ?_
  have : ((J - 8 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ (J : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le J 8) (by norm_num)
  linarith

/-! ### A level's tail, from below -/

/-- `∫_s^t e^{-ax}dx = (e^{-as} - e^{-at})/a`. -/
lemma integral_exp_neg_mul {a : ℝ} (ha : a ≠ 0) (s t : ℝ) :
    ∫ x in s..t, Real.exp (-(a * x)) = (Real.exp (-(a * s)) - Real.exp (-(a * t))) / a := by
  have h := intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (neg_ne_zero.2 ha)
    (a := s) (b := t)
  simp only [neg_mul] at h
  rw [h, integral_exp, smul_eq_mul]
  field_simp
  ring

/-- **A piece of a tail's integral**: for `a > 0`, `t₁ > 0` and `0 ≤ s ≤ t`,
`∫_s^t e^{-ax}(x + t₁)^{-1/4}dx ≥ (t + t₁)^{-1/4}(e^{-as} - e^{-at})/a`. -/
lemma integral_piece_ge {a t₁ s t : ℝ} (ha : 0 < a) (ht₁ : 0 < t₁) (hs : 0 ≤ s) (hst : s ≤ t) :
    (t + t₁) ^ (-(1 / 4 : ℝ)) * ((Real.exp (-(a * s)) - Real.exp (-(a * t))) / a)
      ≤ ∫ x in s..t, Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) := by
  rw [← integral_exp_neg_mul ha.ne', ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hst ?_ ?_ fun x hx => ?_
  · exact (Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _ |>.const_mul _
  · refine ContinuousOn.intervalIntegrable ?_
    refine (Real.continuous_exp.comp (by fun_prop)).continuousOn.mul ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun y hy => Or.inl ?_
    rw [Set.uIcc_of_le hst] at hy
    exact (by linarith [hy.1] : (0 : ℝ) < y + t₁).ne'
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith [hx.1])
      (by linarith [hx.2]) (by norm_num)) (Real.exp_pos _).le

lemma continuousOn_exp_mul_rpow_quarter {a t₁ s t : ℝ} (ht₁ : 0 < t₁) (hs : 0 ≤ s) :
    ContinuousOn (fun x : ℝ => Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ))) (Icc s t) := by
  refine (Real.continuous_exp.comp (by fun_prop)).continuousOn.mul ?_
  exact ContinuousOn.rpow_const (by fun_prop) fun y hy =>
    Or.inl (by linarith [hy.1] : (0 : ℝ) < y + t₁).ne'

lemma intervalIntegrable_exp_mul_rpow_quarter {a t₁ s t : ℝ} (ht₁ : 0 < t₁) (hs : 0 ≤ s)
    (hst : s ≤ t) :
    IntervalIntegrable (fun x : ℝ => Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ))) volume s t :=
  (continuousOn_exp_mul_rpow_quarter ht₁ hs).intervalIntegrable_of_Icc hst

/-- **A level's tail from below.**  For `a > 0`, `A ≥ 0` with `A^4 ≤ t₁`, `t₁ > 0` and
`N + 1 ≤ M`: `∑_{N+1 ≤ m < M} e^{-am}·chaosProf A m ≥ A∫_{N+1}^{M} e^{-ax}(x + t₁)^{-1/4}dx`
(`RMF.chaosProf_ge`, the integral below the sum of a decreasing function). -/
theorem tail_profSum_ge_integral {a A t₁ : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht₁ : 0 < t₁)
    (hAt : A ^ 4 ≤ t₁) {N M : ℕ} (hNM : N + 1 ≤ M) :
    A * ∫ x in ((N + 1 : ℕ) : ℝ)..(M : ℝ), Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ))
      ≤ ∑ m ∈ Finset.Ico (N + 1) M, Real.exp (-(a * m)) * chaosProf A m := by
  set g : ℝ → ℝ := fun x => Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) with hgdef
  have hanti : AntitoneOn g (Icc ((N + 1 : ℕ) : ℝ) (M : ℝ)) := by
    intro s hs t ht hst
    have hs0 : 0 < s + t₁ := by
      have : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [hs.1]
    exact mul_le_mul (Real.exp_le_exp.2 (by nlinarith))
      (Real.rpow_le_rpow_of_nonpos hs0 (by linarith) (by norm_num))
      (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  have h := AntitoneOn.integral_le_sum_Ico hNM hanti
  refine le_trans (mul_le_mul_of_nonneg_left h hA) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [hgdef]
  have := chaosProf_ge hA hAt m
  calc A * (Real.exp (-(a * (m : ℝ))) * ((m : ℝ) + t₁) ^ (-(1 / 4 : ℝ)))
      = Real.exp (-(a * (m : ℝ))) * (A * ((m : ℝ) + t₁) ^ (-(1 / 4 : ℝ))) := by ring
    _ ≤ Real.exp (-(a * (m : ℝ))) * chaosProf A m :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

/-- **The profile sum below a level's end, by its tail**: for `a > 0`, `A ≥ 0` with
`A^4 ≤ t₁`, `t₁ > 0`, a bound `B` on every profile sum and a real `X ≥ N + 1`:
`profSum a A (N + 1) ≤ B - A∫_{N+1}^{X} e^{-ax}(x + t₁)^{-1/4}dx`. -/
theorem profSum_le_sub_tail {a A t₁ B : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht₁ : 0 < t₁)
    (hAt : A ^ 4 ≤ t₁) (hB : ∀ J, profSum a A J ≤ B) (N : ℕ) {X : ℝ}
    (hX : ((N + 1 : ℕ) : ℝ) ≤ X) :
    profSum a A (N + 1)
      ≤ B - A * ∫ x in ((N + 1 : ℕ) : ℝ)..X, Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) := by
  set M := ⌈X⌉₊ with hMdef
  have hXM : X ≤ M := Nat.le_ceil X
  have hNM : N + 1 ≤ M := by
    have : ((N + 1 : ℕ) : ℝ) ≤ M := le_trans hX hXM
    exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsplit : profSum a A M = profSum a A (N + 1)
      + ∑ m ∈ Finset.Ico (N + 1) M, Real.exp (-(a * m)) * chaosProf A m := by
    rw [profSum, profSum, Finset.sum_Ico_consecutive _ (by omega : 1 ≤ N + 1) hNM]
  have htail := tail_profSum_ge_integral ha hA ht₁ hAt hNM
  -- the integral to `X` is at most the one to `M`
  have hmono : ∫ x in ((N + 1 : ℕ) : ℝ)..X, Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ))
      ≤ ∫ x in ((N + 1 : ℕ) : ℝ)..(M : ℝ), Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_mul_rpow_quarter ht₁ hN0 hX)
      (intervalIntegrable_exp_mul_rpow_quarter ht₁ (le_trans hN0 hX) hXM)]
    have : 0 ≤ ∫ x in X..(M : ℝ), Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) :=
      intervalIntegral.integral_nonneg hXM fun x hx =>
        mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith [hx.1]) _)
    linarith
  have := hB M
  nlinarith [mul_le_mul_of_nonneg_left hmono hA]

/-- **A tail's integral on a grid**: for `a > 0`, `t₁ > 0`, `s ≥ 0` and a monotone grid `w` with
`w 0 = 0`, at the points `t_k = s + w_k/a`:
`∫_s^{s + w_K/a} e^{-ax}(x + t₁)^{-1/4}dx
  ≥ ∑_{k<K} (t_{k+1} + t₁)^{-1/4}(e^{-at_k} - e^{-at_{k+1}})/a`. -/
theorem integral_ge_grid {a t₁ s : ℝ} (ha : 0 < a) (ht₁ : 0 < t₁) (hs : 0 ≤ s) {w : ℕ → ℝ}
    (hw0 : w 0 = 0) (hw : Monotone w) (K : ℕ) :
    ∑ k ∈ Finset.range K, (s + w (k + 1) / a + t₁) ^ (-(1 / 4 : ℝ))
        * ((Real.exp (-(a * (s + w k / a))) - Real.exp (-(a * (s + w (k + 1) / a)))) / a)
      ≤ ∫ x in s..(s + w K / a), Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) := by
  have hwnn : ∀ k, 0 ≤ w k := fun k => by rw [← hw0]; exact hw (Nat.zero_le k)
  have hpt : ∀ k, s ≤ s + w k / a := fun k => le_add_of_nonneg_right (div_nonneg (hwnn k) ha.le)
  have hstep : ∀ k, s + w k / a ≤ s + w (k + 1) / a := fun k =>
    by have := div_le_div_of_nonneg_right (hw (Nat.le_succ k)) ha.le; linarith
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)))
    (a := fun k => s + w k / a) (n := K) (μ := volume)
    fun k _ => intervalIntegrable_exp_mul_rpow_quarter ht₁ (le_trans hs (hpt k)) (hstep k)
  simp only [hw0, zero_div, add_zero] at hsum
  rw [← hsum]
  exact Finset.sum_le_sum fun k _ =>
    integral_piece_ge ha ht₁ (le_trans hs (hpt k)) (hstep k)

/-! ### `Γ(3/4)` -/

/-- **`Γ(3/4) ≤ 1.2302`**: log-convexity at `35/4 = (17/2 + 9)/2`
(`Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`), `Γ(9) = 8!`,
`Γ(17/2) = (2027025/256)√π` and `Γ(35/4) = (1267389585/65536)Γ(3/4)` by the recursion. -/
theorem gamma_three_quarters_le : Real.Gamma (3 / 4) ≤ 1.2302 := by
  have hrec : ∀ s : ℝ, 0 < s → Real.Gamma (s + 1) = s * Real.Gamma s :=
    fun s hs => Real.Gamma_add_one hs.ne'
  have hH := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := 17 / 2) (t := 9)
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (1 / 2 : ℝ) * (17 / 2) + 1 / 2 * 9 = 35 / 4 by norm_num] at hH
  -- the recursions
  have hq : Real.Gamma (35 / 4) = 1267389585 / 65536 * Real.Gamma (3 / 4) := by
    have s7 : Real.Gamma (35 / 4) = 31 / 4 * Real.Gamma (31 / 4) := by
      rw [show (35 / 4 : ℝ) = 31 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s6 : Real.Gamma (31 / 4) = 27 / 4 * Real.Gamma (27 / 4) := by
      rw [show (31 / 4 : ℝ) = 27 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s5 : Real.Gamma (27 / 4) = 23 / 4 * Real.Gamma (23 / 4) := by
      rw [show (27 / 4 : ℝ) = 23 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s4 : Real.Gamma (23 / 4) = 19 / 4 * Real.Gamma (19 / 4) := by
      rw [show (23 / 4 : ℝ) = 19 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s3 : Real.Gamma (19 / 4) = 15 / 4 * Real.Gamma (15 / 4) := by
      rw [show (19 / 4 : ℝ) = 15 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s2 : Real.Gamma (15 / 4) = 11 / 4 * Real.Gamma (11 / 4) := by
      rw [show (15 / 4 : ℝ) = 11 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s1 : Real.Gamma (11 / 4) = 7 / 4 * Real.Gamma (7 / 4) := by
      rw [show (11 / 4 : ℝ) = 7 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s0 : Real.Gamma (7 / 4) = 3 / 4 * Real.Gamma (3 / 4) := by
      rw [show (7 / 4 : ℝ) = 3 / 4 + 1 by norm_num]; exact hrec _ (by norm_num)
    rw [s7, s6, s5, s4, s3, s2, s1, s0]
    ring
  have hh : Real.Gamma (17 / 2) = 2027025 / 256 * Real.sqrt Real.pi := by
    have s7 : Real.Gamma (17 / 2) = 15 / 2 * Real.Gamma (15 / 2) := by
      rw [show (17 / 2 : ℝ) = 15 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s6 : Real.Gamma (15 / 2) = 13 / 2 * Real.Gamma (13 / 2) := by
      rw [show (15 / 2 : ℝ) = 13 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s5 : Real.Gamma (13 / 2) = 11 / 2 * Real.Gamma (11 / 2) := by
      rw [show (13 / 2 : ℝ) = 11 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s4 : Real.Gamma (11 / 2) = 9 / 2 * Real.Gamma (9 / 2) := by
      rw [show (11 / 2 : ℝ) = 9 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s3 : Real.Gamma (9 / 2) = 7 / 2 * Real.Gamma (7 / 2) := by
      rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s2 : Real.Gamma (7 / 2) = 5 / 2 * Real.Gamma (5 / 2) := by
      rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s1 : Real.Gamma (5 / 2) = 3 / 2 * Real.Gamma (3 / 2) := by
      rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    have s0 : Real.Gamma (3 / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num]; exact hrec _ (by norm_num)
    rw [s7, s6, s5, s4, s3, s2, s1, s0, Real.Gamma_one_half_eq]
    ring
  have h9 : Real.Gamma 9 = 40320 := by
    have := Real.Gamma_nat_eq_factorial 8
    rw [show ((8 : ℕ) : ℝ) + 1 = 9 by norm_num] at this
    rw [this]
    norm_num [Nat.factorial]
  rw [hq, hh, h9] at hH
  -- square the Hölder bound
  have hpi : Real.sqrt Real.pi ≤ 1.77246 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_d4
    nlinarith
  have hG0 : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hA : 0 ≤ 2027025 / 256 * Real.sqrt Real.pi := by positivity
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hA] at hH
  have hsq := (Real.le_sqrt (by positivity) (by positivity)).1 hH
  nlinarith [mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 2027025 / 256 * 40320)]

end RMF
