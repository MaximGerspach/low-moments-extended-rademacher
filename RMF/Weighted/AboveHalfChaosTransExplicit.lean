/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfChaosChainExplicit
import RMF.Weighted.TenNumeralExplicit
import RMF.Weighted.HalfNumeralExplicit
import RMF.Reduction.UpperAveragedLeaves

/-!
# The chaos regime's transition above `q = ½`

The chain of levels (`RMF.chain_windows_le`) prices the partner level with the main one by a bound
`T` on `profSum(N) + e^{1.001a'}e^{-a'N}B` for every `N`.  Past `N = 0` the level's sum is below
`B` by at least its tail, the profile's integral (`RMF.profSum_le_sub_tail`) on a grid
(`RMF.integral_ge_grid`): in `u = aN` that is `A a^{-3/4}e^{-u}RMF.chaosS u (at₁)`
(`RMF.profSum_le_chaosS`).  So `T = A a^{-3/4}τ` once `B ≤ A a^{-3/4}G` (`RMF.profSum_gamma_le`)
and `G + e^{-u}(Ge^{c + (1-r)u} - S(u)) ≤ τ` on a grid of `u` (`RMF.chaos_transition`), uniformly
in `a ≤ a_u`.  The chaos profile's constant `RMF.chaosAhat` is at least `√41.2`
(`RMF.chaosAhat_ge`) and, near `q = ½`, at most `6.4233` (`RMF.chaosAhat_le_num`).
-/

open MeasureTheory

namespace RMF

/-! ### The tail on a grid -/

/-- The grid of the tail's integral: `0, 1/4, 1/2, 3/4, 1, 3/2, 2, 3, 4, 6, 9, 14, 25`, then
`25`. -/
noncomputable def chaosWGrid : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 1 / 2
  | 3 => 3 / 4
  | 4 => 1
  | 5 => 3 / 2
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 6
  | 10 => 9
  | 11 => 14
  | _ => 25

lemma chaosWGrid_mono : Monotone chaosWGrid := by
  refine monotone_nat_of_le_succ fun n => ?_
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => norm_num [chaosWGrid]
  | n + 12 => exact le_of_eq rfl

lemma chaosWGrid_nonneg (k : ℕ) : 0 ≤ chaosWGrid k := by
  have := chaosWGrid_mono (Nat.zero_le k)
  simpa [chaosWGrid] using this

/-- The tail's grid sum at `v = aN`, `t = at₁`:
`∑_{k<12} (v + w_{k+1} + t)^{-1/4}(e^{-w_k} - e^{-w_{k+1}})`, `w = RMF.chaosWGrid`. -/
noncomputable def chaosS (v t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 12, (v + chaosWGrid (k + 1) + t) ^ (-(1 / 4 : ℝ))
    * (Real.exp (-chaosWGrid k) - Real.exp (-chaosWGrid (k + 1)))

lemma chaosS_nonneg {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ chaosS v t := by
  refine Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (by
    have := chaosWGrid_nonneg (k + 1); linarith) _) (sub_nonneg.2 (Real.exp_le_exp.2 ?_))
  exact neg_le_neg (chaosWGrid_mono (Nat.le_succ k))

/-- `RMF.chaosS` decreases in both arguments. -/
lemma chaosS_anti {v v' t t' : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) (hvv : v ≤ v') (htt : t ≤ t') :
    chaosS v' t' ≤ chaosS v t := by
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_
    (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg (chaosWGrid_mono (Nat.le_succ k)))))
  have hw : (1 / 4 : ℝ) ≤ chaosWGrid (k + 1) := by
    have := chaosWGrid_mono (show 1 ≤ k + 1 by omega)
    simpa [chaosWGrid] using this
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)

/-- **A level's sum below its bound, by the tail on the grid**: for `a > 0`, `A ≥ 0` with
`A^4 ≤ t₁`, `t₁ > 0`, a bound `B` on every profile sum and `N ≥ 1`:
`profSum a A N ≤ B - A a^{-3/4}e^{-aN}RMF.chaosS (aN) (at₁)`. -/
theorem profSum_le_chaosS {a A t₁ B : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht₁ : 0 < t₁)
    (hAt : A ^ 4 ≤ t₁) (hB : ∀ J, profSum a A J ≤ B) {N : ℕ} (hN : 1 ≤ N) :
    profSum a A N
      ≤ B - A * (a ^ (-(3 / 4 : ℝ)) * (Real.exp (-(a * N)) * chaosS (a * N) (a * t₁))) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set s : ℝ := ((M + 1 : ℕ) : ℝ) with hsdef
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hw12 : 0 ≤ chaosWGrid 12 / a := div_nonneg (chaosWGrid_nonneg 12) ha.le
  have htail := profSum_le_sub_tail ha hA ht₁ hAt hB M (X := s + chaosWGrid 12 / a)
    (by linarith)
  have hgrid := integral_ge_grid ha ht₁ hs0 (w := chaosWGrid) rfl chaosWGrid_mono 12
  have heq : ∑ k ∈ Finset.range 12, (s + chaosWGrid (k + 1) / a + t₁) ^ (-(1 / 4 : ℝ))
        * ((Real.exp (-(a * (s + chaosWGrid k / a)))
          - Real.exp (-(a * (s + chaosWGrid (k + 1) / a)))) / a)
      = a ^ (-(3 / 4 : ℝ)) * (Real.exp (-(a * s)) * chaosS (a * s) (a * t₁)) := by
    rw [chaosS, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hwk := chaosWGrid_nonneg (k + 1)
    have hpos : 0 < a * s + chaosWGrid (k + 1) + a * t₁ := by positivity
    have hbase : s + chaosWGrid (k + 1) / a + t₁
        = (a * s + chaosWGrid (k + 1) + a * t₁) * a⁻¹ := by
      field_simp
    have e1 : ∀ j : ℕ, Real.exp (-(a * (s + chaosWGrid j / a)))
        = Real.exp (-(a * s)) * Real.exp (-chaosWGrid j) := by
      intro j
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have e3 : a ^ (-(3 / 4 : ℝ)) = a ^ (1 / 4 : ℝ) / a := by
      rw [← Real.rpow_sub_one ha.ne']
      norm_num
    rw [hbase, Real.mul_rpow hpos.le (inv_nonneg.2 ha.le), Real.inv_rpow ha.le,
      ← Real.rpow_neg ha.le, e1 k, e1 (k + 1), e3, neg_neg]
    field_simp
  calc profSum a A (M + 1)
      ≤ B - A * ∫ x in s..(s + chaosWGrid 12 / a),
          Real.exp (-(a * x)) * (x + t₁) ^ (-(1 / 4 : ℝ)) := htail
    _ ≤ B - A * (a ^ (-(3 / 4 : ℝ)) * (Real.exp (-(a * s)) * chaosS (a * s) (a * t₁))) := by
        rw [← heq]
        have := mul_le_mul_of_nonneg_left hgrid hA
        linarith

/-! ### The profile's bound, normalised -/

/-- **The Gamma bound in units of `A a^{-3/4}`**: for `0 < a ≤ a_u` and `A ≥ 6.4187`,
`RMF.profSum_le_gamma`'s bound is at most `A a^{-3/4}G` once
`2007/6.4187 - (4/3)1999^{3/4}e^{-1999a_u} ≤ c_u`, `c_u ≥ 0` and `1.2302 + a_u^{3/4}c_u ≤ G`. -/
theorem profSum_gamma_le {a A G au cu : ℝ} (ha : 0 < a) (hau : a ≤ au) (hA : 6.4187 ≤ A)
    (hcu : 2007 / 6.4187 - 4 / 3 * Real.exp (3 / 4 * Real.log 1999) * Real.exp (-(1999 * au))
      ≤ cu) (hcu0 : 0 ≤ cu) (hG : 1.2302 + Real.exp (3 / 4 * Real.log au) * cu ≤ G) :
    ∑ m ∈ Finset.Ico (1 : ℕ) 2008, Real.exp (-(a * (m : ℝ)))
      + A * ((1 / a) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)
        - Real.exp (-(a * 1999)) * (4 / 3 * (1999 : ℝ) ^ (3 / 4 : ℝ)))
      ≤ A * (a ^ (-(3 / 4 : ℝ)) * G) := by
  have hA0 : 0 < A := by linarith
  have hsum : ∑ m ∈ Finset.Ico (1 : ℕ) 2008, Real.exp (-(a * (m : ℝ))) ≤ 2007 := by
    calc ∑ m ∈ Finset.Ico (1 : ℕ) 2008, Real.exp (-(a * (m : ℝ)))
        ≤ ∑ m ∈ Finset.Ico (1 : ℕ) 2008, (1 : ℝ) := Finset.sum_le_sum fun m _ =>
          Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) m; nlinarith)
      _ = 2007 := by rw [Finset.sum_const, Nat.card_Ico]; norm_num
  have hΓ := gamma_three_quarters_le
  set p := a ^ (3 / 4 : ℝ) with hpdef
  set ip := a ^ (-(3 / 4 : ℝ)) with hipdef
  have hp0 : 0 < p := Real.rpow_pos_of_pos ha _
  have hip0 : 0 < ip := Real.rpow_pos_of_pos ha _
  have hpip : p * ip = 1 := by
    rw [hpdef, hipdef, ← Real.rpow_add ha]; norm_num
  have hinv : (1 / a) ^ (3 / 4 : ℝ) = ip := by
    rw [one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
  have hE : (1999 : ℝ) ^ (3 / 4 : ℝ) = Real.exp (3 / 4 * Real.log 1999) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hpu : p ≤ Real.exp (3 / 4 * Real.log au) := by
    rw [hpdef, Real.rpow_def_of_pos ha, mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.log_le_log ha hau) (by norm_num))
  have hexp : Real.exp (-(1999 * au)) ≤ Real.exp (-(a * 1999)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hE0 : 0 ≤ Real.exp (3 / 4 * Real.log 1999) := (Real.exp_pos _).le
  -- `2007 ≤ A·(2007/6.4187)·p·ip`
  have h1 : (2007 : ℝ) ≤ A * (2007 / 6.4187) * (p * ip) := by
    rw [hpip, mul_one]
    have : (2007 : ℝ) = 6.4187 * (2007 / 6.4187) := by norm_num
    nlinarith
  -- the Gamma term and the subtracted one, in units of `A ip`
  have h2 : A * (Real.exp (-(a * 1999)) * (4 / 3 * Real.exp (3 / 4 * Real.log 1999)))
      ≥ A * (4 / 3 * Real.exp (3 / 4 * Real.log 1999) * Real.exp (-(1999 * au))) * (p * ip) := by
    rw [hpip, mul_one]
    have := mul_le_mul_of_nonneg_left hexp (by positivity :
      (0 : ℝ) ≤ A * (4 / 3 * Real.exp (3 / 4 * Real.log 1999)))
    nlinarith
  have hbr : p * (2007 / 6.4187 - 4 / 3 * Real.exp (3 / 4 * Real.log 1999)
      * Real.exp (-(1999 * au))) ≤ Real.exp (3 / 4 * Real.log au) * cu :=
    le_trans (mul_le_mul_of_nonneg_left hcu hp0.le) (mul_le_mul_of_nonneg_right hpu hcu0)
  rw [hinv, hE]
  have hAip : 0 ≤ A * ip := by positivity
  have key : 2007 + A * (ip * Real.Gamma (3 / 4)
        - Real.exp (-(a * 1999)) * (4 / 3 * Real.exp (3 / 4 * Real.log 1999)))
      ≤ A * ip * (1.2302 + p * (2007 / 6.4187 - 4 / 3 * Real.exp (3 / 4 * Real.log 1999)
        * Real.exp (-(1999 * au)))) := by
    have hG' := mul_le_mul_of_nonneg_left hΓ hAip
    nlinarith
  have := mul_le_mul_of_nonneg_left (le_trans (add_le_add le_rfl hbr) hG) hAip
  nlinarith

/-! ### The transition on a grid of `u = aN` -/

/-- **The transition**: for `0 < a ≤ a_u`, `ra ≤ a' ≤ a_u` (`0 ≤ r ≤ 1`), `A ≥ 0` with
`A^4 ≤ t₁`, a bound `B ≤ A a^{-3/4}G` on every profile sum and a grid `u_0 = 0, u_1, …, u_n` of
`u = aN` with `D_j = Ge^{1.001a_u + (1-r)u_{j+1}} - RMF.chaosS u_{j+1} (a_u t₁) ≥ 0`,
`G + e^{-u_j}D_j ≤ τ`, `G(1 + e^{1.001a_u - ru_n}) ≤ τ` and `e^{1.001a_u}G ≤ τ`:

`profSum(N) + e^{1.001a'}e^{-a'N}B ≤ A a^{-3/4}τ` for every `N`. -/
theorem chaos_transition {a a' A t₁ B G τ au r : ℝ} (ha : 0 < a) (hau : a ≤ au)
    (hra : r * a ≤ a') (ha'u : a' ≤ au) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA : 0 ≤ A) (ht₁ : 0 < t₁)
    (hAt : A ^ 4 ≤ t₁) (hB : ∀ J, profSum a A J ≤ B) (hBG : B ≤ A * (a ^ (-(3 / 4 : ℝ)) * G))
    (hG0 : 0 ≤ G) {ug : ℕ → ℝ} (hug0 : ug 0 = 0) {n : ℕ}
    (hD : ∀ j < n, 0 ≤ G * Real.exp (1.001 * au + (1 - r) * ug (j + 1))
      - chaosS (ug (j + 1)) (au * t₁))
    (hcell : ∀ j < n, G + Real.exp (-ug j) * (G * Real.exp (1.001 * au + (1 - r) * ug (j + 1))
      - chaosS (ug (j + 1)) (au * t₁)) ≤ τ)
    (htop : G * (1 + Real.exp (1.001 * au - r * ug n)) ≤ τ)
    (hzero : Real.exp (1.001 * au) * G ≤ τ) :
    ∀ N : ℕ, profSum a A N + Real.exp (1.001 * a') * Real.exp (-(a' * N)) * B
      ≤ A * (a ^ (-(3 / 4 : ℝ)) * τ) := by
  classical
  intro N
  have hB0 : 0 ≤ B := le_trans (profSum_nonneg hA 0) (hB 0)
  set ip := a ^ (-(3 / 4 : ℝ)) with hipdef
  have hip0 : 0 < ip := Real.rpow_pos_of_pos ha _
  have hK0 : 0 ≤ A * ip := mul_nonneg hA hip0.le
  rcases Nat.eq_zero_or_pos N with hN0 | hN1
  · subst hN0
    have hP0 : profSum a A 0 = 0 := by simp [profSum]
    rw [hP0, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add]
    have h1 : Real.exp (1.001 * a') ≤ Real.exp (1.001 * au) :=
      Real.exp_le_exp.2 (by linarith)
    calc Real.exp (1.001 * a') * B ≤ Real.exp (1.001 * au) * (A * (ip * G)) :=
          mul_le_mul h1 hBG hB0 (Real.exp_pos _).le
      _ = A * ip * (Real.exp (1.001 * au) * G) := by ring
      _ ≤ A * ip * τ := mul_le_mul_of_nonneg_left hzero hK0
      _ = A * (ip * τ) := by ring
  -- `N ≥ 1`: the tail below `B`
  set u : ℝ := a * N with hudef
  have hu0 : 0 < u := mul_pos ha (by exact_mod_cast hN1)
  have hP := profSum_le_chaosS ha hA ht₁ hAt hB hN1
  rw [← hudef, ← hipdef] at hP
  have hat : a * t₁ ≤ au * t₁ := mul_le_mul_of_nonneg_right hau ht₁.le
  have hat0 : 0 ≤ a * t₁ := by positivity
  -- the partner's weight
  have hE : Real.exp (1.001 * a') * Real.exp (-(a' * N))
      ≤ Real.exp (-u) * Real.exp (1.001 * au + (1 - r) * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : r * u ≤ a' * N := by rw [hudef, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hra hN0
    linarith
  have hS0 := chaosS_nonneg hu0.le hat0
  -- the bracket: `G + e^{-u}(Ge^{1.001a_u + (1-r)u} - S(u))`
  have hmain : profSum a A N + Real.exp (1.001 * a') * Real.exp (-(a' * N)) * B
      ≤ A * ip * (G + Real.exp (-u) * (G * Real.exp (1.001 * au + (1 - r) * u)
        - chaosS u (a * t₁))) := by
    have h1 := mul_le_mul hE hBG hB0 (by positivity)
    have e1 : Real.exp (-u) * Real.exp (1.001 * au + (1 - r) * u) * (A * (ip * G))
        = A * ip * (Real.exp (-u) * (G * Real.exp (1.001 * au + (1 - r) * u))) := by ring
    rw [e1] at h1
    have e2 : A * (ip * (Real.exp (-u) * chaosS u (a * t₁)))
        = A * ip * (Real.exp (-u) * chaosS u (a * t₁)) := by ring
    rw [e2] at hP
    have e3 : A * (ip * G) = A * ip * G := by ring
    rw [e3] at hBG
    nlinarith
  refine le_trans hmain ?_
  rw [show A * (ip * τ) = A * ip * τ by ring]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  by_cases htopc : ug n ≤ u
  · -- past the grid
    have h1 : Real.exp (-u) * (G * Real.exp (1.001 * au + (1 - r) * u) - chaosS u (a * t₁))
        ≤ G * Real.exp (1.001 * au - r * ug n) := by
      have e : Real.exp (-u) * (G * Real.exp (1.001 * au + (1 - r) * u))
          = G * Real.exp (1.001 * au - r * u) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      have h2 : Real.exp (1.001 * au - r * u) ≤ Real.exp (1.001 * au - r * ug n) :=
        Real.exp_le_exp.2 (by nlinarith)
      have h3 := mul_nonneg (Real.exp_pos (-u)).le hS0
      nlinarith [mul_le_mul_of_nonneg_left h2 hG0]
    nlinarith
  · -- in the grid: the cell `u_j ≤ u ≤ u_{j+1}`
    push Not at htopc
    have hn : n ≠ 0 := by
      rintro rfl
      rw [hug0] at htopc
      linarith
    have hex : ∃ j, u < ug (j + 1) := ⟨n - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
    set j := Nat.find hex with hjdef
    have hj1 : u < ug (j + 1) := Nat.find_spec hex
    have hjn : j < n := by
      have := Nat.find_min' hex (show u < ug (n - 1 + 1) by
        rwa [Nat.sub_add_cancel (by omega)])
      omega
    have hj0 : ug j ≤ u := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, hug0]; exact hu0.le
      · obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have := Nat.find_min hex (show i < Nat.find hex by omega)
        push Not at this
        rw [hi]; exact this
    have hS := chaosS_anti hu0.le hat0 hj1.le hat
    have hexp : Real.exp (1.001 * au + (1 - r) * u)
        ≤ Real.exp (1.001 * au + (1 - r) * ug (j + 1)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hDu : G * Real.exp (1.001 * au + (1 - r) * u) - chaosS u (a * t₁)
        ≤ G * Real.exp (1.001 * au + (1 - r) * ug (j + 1)) - chaosS (ug (j + 1)) (au * t₁) := by
      nlinarith [mul_le_mul_of_nonneg_left hexp hG0]
    have hDj := hD j hjn
    have he : Real.exp (-u) ≤ Real.exp (-ug j) := Real.exp_le_exp.2 (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hDu (Real.exp_pos (-u)).le
    have h2 := mul_le_mul_of_nonneg_right he hDj
    have := hcell j hjn
    linarith

/-! ### The chaos profile's constant near `q = ½` -/

/-- **`RMF.chaosAhat q ≥ √41.2 ≥ 6.4187`** for `½ ≤ q < 1`: the Jensen branch of the chaos
constant is `20.6^q`, and `(1-q)^{-q} ≥ 2^q`. -/
lemma chaosAhat_ge {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1) : 6.4187 ≤ chaosAhat q := by
  have h1 : (20.6 : ℝ) ^ q ≤ chaosAbove q := by
    rw [chaosAbove, shiftMomentConst]
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    norm_num
  have h2 : (2 : ℝ) ^ q ≤ (1 - q) ^ (-q) := by
    rw [Real.rpow_neg (by linarith), ← Real.inv_rpow (by linarith)]
    refine Real.rpow_le_rpow (by norm_num) ?_ (by linarith)
    rw [le_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  have h3 : (20.6 : ℝ) ^ (1 / 2 : ℝ) ≤ (20.6 : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq0
  have h4 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq0
  have h5 : (6.4187 : ℝ) ≤ (20.6 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  rw [chaosAhat]
  have h60 : (0 : ℝ) ≤ (20.6 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc (6.4187 : ℝ) ≤ (20.6 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) := h5
    _ ≤ chaosAbove q * (1 - q) ^ (-q) :=
        mul_le_mul (le_trans h3 h1) (le_trans h4 h2) h20 (le_trans h60 (le_trans h3 h1))

/-- **The chaos profile's constant from above**: for `½ ≤ q ≤ q_u < 1`, `RMF.chaosAhat q` is at
most `RMF.shiftMomentConst_le_exp`'s bound at `q_u` times `(1-q_u)^{-q_u}`, in exponential form. -/
lemma chaosAhat_le {q qu : ℝ} (hq0 : 1 / 2 ≤ q) (hqu : q ≤ qu) (hqu1 : qu < 1) :
    chaosAhat q
      ≤ max (Real.exp (qu * Real.log 20.6))
          (Real.exp (qu * Real.log ((1 + 5 / 98) * (10102 / 10000) * (12285 / 10000)))
              * (Real.exp (qu * Real.log (155345 / 10000))
                + Real.exp ((1 - qu) * (2528 / 100 - 36))
                  * (Real.exp (qu * Real.log (165345 / 10000)) * (1156519 / 1000000)
                    + 181016 / 1000000))
            + 135336 / 1000000 * Real.exp ((1 - qu) * (2528 / 100 - 36)))
        * Real.exp (-(qu * Real.log (1 - qu))) := by
  have hq1 : q ≤ 1 := by linarith
  have hE₀ : (0 : ℝ) ≤ 1 / 160000 := by norm_num
  have hCi := radAveragedConst_le_B hE₀ le_rfl
  have hCi0 : 0 ≤ radAveragedConst (1 / 160000) (11 / 20) 30 8 := by
    have := one_le_radAveragedConst hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
      (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
    linarith
  have hs := radAveragedShift_le_B hE₀ le_rfl
  have hs0 := radAveragedShift_nonneg hE₀ (by norm_num : (0 : ℝ) ≤ 11 / 20) (by norm_num)
    (by norm_num : (4 : ℝ) < 30) (by norm_num : (1 : ℝ) ≤ 8)
  have hCb : radBlockBadConst (1 / 160000) (11 / 20) * Real.exp 7 ≤ Real.exp (2528 / 100) := by
    have h := radBlockBadConst_mul_le_B (E₀ := 1 / 160000) le_rfl
    have e : radBlockBadConst (1 / 160000) (11 / 20) * Real.exp 7
        = radBlockBadConst (1 / 160000) (11 / 20) * Real.exp 8 * Real.exp (-1) := by
      rw [mul_assoc, ← Real.exp_add]; norm_num
    rw [e, show (2528 / 100 : ℝ) = 2628 / 100 + -1 by norm_num, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hCb0 : 0 ≤ radBlockBadConst (1 / 160000) (11 / 20) * Real.exp 7 :=
    mul_nonneg (radBlockBadConst_pos _ (by norm_num)).le (Real.exp_pos _).le
  have hAs : (0 : ℝ) ≤ 18 + radAveragedShift (1 / 160000) (11 / 20) 30 8 := by linarith
  have hU : (18 + radAveragedShift (1 / 160000) (11 / 20) 30 8) * (1 - q) ≤ 155345 / 10000 := by
    nlinarith
  have h := shiftMomentConst_le_exp (C₁ := 1) (N := 1)
    (Ci := radAveragedConst (1 / 160000) (11 / 20) 30 8) (Ci' := 12285 / 10000)
    (Cb := radBlockBadConst (1 / 160000) (11 / 20) * Real.exp 7) (LB := 2528 / 100)
    (s := radAveragedShift (1 / 160000) (11 / 20) 30 8) (U := 155345 / 10000)
    (IS := 10102 / 10000) (S1 := 1156519 / 1000000) (S2 := 181016 / 1000000)
    (EM2 := 135336 / 1000000) (A := 18) (lam := 98 / 5) (δ := 1 / 50) (q := q) (by linarith)
    hq1 zero_le_one le_rfl hCi0 hCi hCb0 hCb hAs hU (by norm_num) (by norm_num)
    inv_sqrt_one_sub_fiftieth_le inv_one_sub_exp_neg_two_le exp_neg_two_mul_inv_sq_le
    exp_neg_two_le_cert
  have hA : chaosAbove q ≤ max (Real.exp (qu * Real.log 20.6))
      (Real.exp (qu * Real.log ((1 + 5 / 98) * (10102 / 10000) * (12285 / 10000)))
          * (Real.exp (qu * Real.log (155345 / 10000))
            + Real.exp ((1 - qu) * (2528 / 100 - 36))
              * (Real.exp (qu * Real.log (165345 / 10000)) * (1156519 / 1000000)
                + 181016 / 1000000))
        + 135336 / 1000000 * Real.exp ((1 - qu) * (2528 / 100 - 36))) := by
    refine le_trans h (max_le_max ?_ ?_)
    · rw [show (1 : ℝ) * (1 + 98 / 5) = 20.6 by norm_num]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqu (Real.log_nonneg (by norm_num)))
    · have hl1 : 0 ≤ Real.log ((1 + 1 / (98 / 5)) * (10102 / 10000) * (12285 / 10000)) :=
        Real.log_nonneg (by norm_num)
      have e1 : (1 + 1 / (98 / 5) : ℝ) = 1 + 5 / 98 := by norm_num
      have hU1 : 0 ≤ Real.log (155345 / 10000 : ℝ) := Real.log_nonneg (by norm_num)
      have hU2 : 0 ≤ Real.log (155345 / 10000 + 1 : ℝ) := Real.log_nonneg (by norm_num)
      have e2 : (155345 / 10000 + 1 : ℝ) = 165345 / 10000 := by norm_num
      have hE1 : Real.exp ((1 - q) * (2528 / 100 - 2 * 18))
          ≤ Real.exp ((1 - qu) * (2528 / 100 - 36)) :=
        Real.exp_le_exp.2 (by nlinarith)
      have hq01 : Real.exp (q * Real.log 1) = 1 := by simp
      rw [hq01, mul_one, ← e1, ← e2]
      have t1 : Real.exp (q * Real.log ((1 + 1 / (98 / 5)) * (10102 / 10000) * (12285 / 10000)))
          ≤ Real.exp (qu * Real.log ((1 + 1 / (98 / 5)) * (10102 / 10000) * (12285 / 10000))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqu hl1)
      have t2 : Real.exp (q * Real.log (155345 / 10000))
          ≤ Real.exp (qu * Real.log (155345 / 10000)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqu hU1)
      have t3 : Real.exp (q * Real.log (155345 / 10000 + 1))
          ≤ Real.exp (qu * Real.log (155345 / 10000 + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hqu hU2)
      have hEq : Real.exp ((1 - q) * (2528 / 100 - 2 * 18))
          = Real.exp ((1 - q) * (2528 / 100 - 36)) := by norm_num
      rw [hEq] at hE1 ⊢
      gcongr
  have hB : (1 - q) ^ (-q) ≤ Real.exp (-(qu * Real.log (1 - qu))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    refine Real.exp_le_exp.2 ?_
    have hl : Real.log (1 - qu) ≤ Real.log (1 - q) := Real.log_le_log (by linarith) (by linarith)
    have hl0 : Real.log (1 - q) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    nlinarith
  rw [chaosAhat]
  exact mul_le_mul hA hB (Real.rpow_nonneg (by linarith) _)
    (le_trans (chaosAbove_nonneg q) hA)

end RMF
