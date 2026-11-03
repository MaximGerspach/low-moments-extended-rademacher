/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfCleanExplicit
import LeanCert.Tactic.IntervalAuto

/-!
# The tower above `q = ½`

The hierarchy (`RMF.rpow_inv_integral_rpow_weightedRademacherSum_le_aboveHierarchy`) at its depth
`RMF.aboveDepth Λ` (the first `ℓ` with `3 log V_ℓ < 10`), every level cleaned and normalised by
`(log x)^{q(2q-1)}`: a band is `RMF.bandPhi` at its `V_{ℓ+1}` plus a window term that telescopes,
the bottom is `RMF.botPhi`, the top `RMF.topPhi`.  Along the tower `V_{L-j} ≥ r_j`
(`RMF.towerR`, `r_{j+1} = e^{r_j/3}`), so the bands' overheads sum to their first four ranges and
a super-exponentially small tail (`RMF.sum_tower_le`); the windows' deep part is summed the same
way and the last four with the bottom's by the power mean.

`RMF.integral_rpow_weightedRademacherSum_le_aboveTower`:
`E|S(x)|^{2q} ≤ (log x)^{q(2q-1)}·RMF.aboveTowerF q η' ε Λ TS^{2q}` for `Λ ≥ 11.5`, a closed form
in `q`, `Λ` and a bound `TS` on the bottom's nine top windows.
-/

open MeasureTheory

namespace RMF

/-! ### The depth of the hierarchy -/

lemma log_ten_lt : Real.log 10 < 2.4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : Real.exp 2.4 = Real.exp 1 * Real.exp 1 * Real.exp 0.4 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h2 : (1.4 : ℝ) + 0.4 ^ 2 / 2 ≤ Real.exp 0.4 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.4)
    linarith
  have h3 := Real.exp_one_gt_d9
  rw [h1]
  have h4 : (7.389 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
  nlinarith

/-- `3 log v ≤ v - 2.4` for `v ≥ 10`. -/
lemma three_mul_log_le_sub {v : ℝ} (hv : 10 ≤ v) : 3 * Real.log v ≤ v - 2.4 := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < v / 10)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have := log_ten_lt
  linarith

lemma exists_aboveV_lt {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) : ∃ ℓ, 3 * Real.log (aboveV Λ ℓ) < 10 := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hV : ∀ ℓ, 10 ≤ aboveV Λ ℓ := by
    intro ℓ
    cases ℓ with
    | zero => rw [aboveV_zero]; exact hΛ
    | succ n => rw [aboveV_succ]; exact hcon n
  have hdec : ∀ ℓ : ℕ, aboveV Λ ℓ ≤ 3 * Λ - 2.4 * ℓ := by
    intro ℓ
    induction ℓ with
    | zero => rw [aboveV_zero]; simp
    | succ n ih =>
      rw [aboveV_succ]
      have := three_mul_log_le_sub (hV n)
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * Λ / 2.4)
  have h1 := hdec n
  have h2 := hV n
  have h3 : 3 * Λ < 2.4 * n := by
    rw [div_lt_iff₀ (by norm_num)] at hn
    linarith
  linarith

open Classical in
/-- The depth of the hierarchy: the first `ℓ` with `3 log V_ℓ < 10`. -/
noncomputable def aboveDepth (Λ : ℝ) : ℕ :=
  if h : ∃ ℓ, 3 * Real.log (aboveV Λ ℓ) < 10 then Nat.find h else 0

/-- **The depth's facts**: for `3Λ ≥ 10`, `V_ℓ ≥ 10` up to the depth `L`, and `3 log V_L < 10`. -/
lemma aboveDepth_spec {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) :
    3 * Real.log (aboveV Λ (aboveDepth Λ)) < 10 ∧ ∀ ℓ ≤ aboveDepth Λ, 10 ≤ aboveV Λ ℓ := by
  classical
  have hex := exists_aboveV_lt hΛ
  have hL : aboveDepth Λ = Nat.find hex := by
    rw [aboveDepth, dif_pos hex]
  refine ⟨?_, fun ℓ hℓ => ?_⟩
  · rw [hL]; exact Nat.find_spec hex
  · cases ℓ with
    | zero => rw [aboveV_zero]; exact hΛ
    | succ n =>
      rw [aboveV_succ]
      have hn : n < Nat.find hex := by rw [← hL]; omega
      have := Nat.find_min hex hn
      exact le_of_not_gt this

/-! ### The tower's ranges -/

/-- The lower ends of the tower's ranges: `r₀ = 10`, `r_{j+1} = e^{r_j/3}`. -/
noncomputable def towerR : ℕ → ℝ
  | 0 => 10
  | j + 1 => Real.exp (towerR j / 3)

lemma towerR_ten_le (j : ℕ) : 10 ≤ towerR j := by
  induction j with
  | zero => simp [towerR]
  | succ n ih =>
    rw [towerR]
    have h1 := Real.add_one_le_exp (towerR n / 3)
    have h2 : Real.exp (towerR n / 3) = Real.exp (10 / 3) * Real.exp ((towerR n - 10) / 3) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : (1 : ℝ) ≤ Real.exp ((towerR n - 10) / 3) := Real.one_le_exp (by linarith)
    have h4 : (10 : ℝ) ≤ Real.exp (10 / 3) := by interval_decide (trust := kernel)
    nlinarith

/-- `e^{s/3} ≥ 2s` for `s ≥ 10`. -/
lemma two_mul_le_exp_div_three {s : ℝ} (hs : 10 ≤ s) : 2 * s ≤ Real.exp (s / 3) := by
  have h1 : Real.exp (s / 3) = Real.exp (10 / 3) * Real.exp ((s - 10) / 3) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : (26 : ℝ) ≤ Real.exp (10 / 3) := by interval_decide (trust := kernel)
  have h3 := Real.add_one_le_exp ((s - 10) / 3)
  have h4 : 0 ≤ (s - 10) / 3 := by linarith
  rw [h1]
  nlinarith

lemma towerR_succ_ge (j : ℕ) : 2 * towerR j ≤ towerR (j + 1) :=
  two_mul_le_exp_div_three (towerR_ten_le j)

/-- **The tower's lower bounds**: `V_{L-j} ≥ r_j` for `j ≤ L`, `L` the depth. -/
lemma aboveV_ge_towerR {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) {j : ℕ} (hj : j ≤ aboveDepth Λ) :
    towerR j ≤ aboveV Λ (aboveDepth Λ - j) := by
  obtain ⟨-, hV⟩ := aboveDepth_spec hΛ
  induction j with
  | zero => rw [towerR, Nat.sub_zero]; exact hV _ le_rfl
  | succ n ih =>
    have ih' := ih (by omega)
    have hsucc : aboveDepth Λ - n = (aboveDepth Λ - (n + 1)) + 1 := by omega
    rw [hsucc, aboveV_succ] at ih'
    have hpos : 0 < aboveV Λ (aboveDepth Λ - (n + 1)) := by
      have := hV (aboveDepth Λ - (n + 1)) (by omega)
      linarith
    rw [towerR]
    calc Real.exp (towerR n / 3)
          ≤ Real.exp (3 * Real.log (aboveV Λ (aboveDepth Λ - (n + 1))) / 3) :=
          Real.exp_le_exp.2 (by linarith)
      _ = aboveV Λ (aboveDepth Λ - (n + 1)) := by
          rw [mul_div_cancel_left₀ _ (by norm_num), Real.exp_log hpos]

/-! ### Sums along the tower -/

/-- `r_{4+i} ≥ 2^i r_4`. -/
lemma towerR_add_ge (i : ℕ) : 2 ^ i * towerR 4 ≤ towerR (4 + i) := by
  induction i with
  | zero => simp
  | succ n ih =>
    have := towerR_succ_ge (4 + n)
    rw [pow_succ, show 4 + (n + 1) = 4 + n + 1 by omega]
    nlinarith

/-- **The deep tail**: `∑_{4 ≤ j < M} c r_j^{-γ} ≤ c r_4^{-γ}/(1 - 2^{-γ})` for `γ > 0`. -/
lemma sum_Ico_towerR_rpow_le {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (M : ℕ) :
    ∑ j ∈ Finset.Ico 4 M, c * towerR j ^ (-γ)
      ≤ c * towerR 4 ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by
  have hr4 : 0 < towerR 4 := by linarith [towerR_ten_le 4]
  have h2 : (2 : ℝ) ^ (-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h20 : 0 ≤ (2 : ℝ) ^ (-γ) := Real.rpow_nonneg (by norm_num) _
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (M - 4), c * towerR (4 + i) ^ (-γ)
      ≤ c * towerR 4 ^ (-γ) * ((2 : ℝ) ^ (-γ)) ^ i := by
    intro i _
    have h1 := towerR_add_ge i
    have hpos : 0 < 2 ^ i * towerR 4 := by positivity
    have h3 : towerR (4 + i) ^ (-γ) ≤ (2 ^ i * towerR 4) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)
    rw [Real.mul_rpow (by positivity) hr4.le, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), mul_comm (i : ℝ) (-γ), Real.rpow_mul (by norm_num),
      Real.rpow_natCast] at h3
    calc c * towerR (4 + i) ^ (-γ) ≤ c * (((2 : ℝ) ^ (-γ)) ^ i * towerR 4 ^ (-γ)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc (Real.rpow_nonneg hr4.le _))
  have h1r : 0 < 1 - (2 : ℝ) ^ (-γ) := by linarith
  have hgeq : ∑ i ∈ Finset.range (M - 4), ((2 : ℝ) ^ (-γ)) ^ i
      = (1 - ((2 : ℝ) ^ (-γ)) ^ (M - 4)) / (1 - (2 : ℝ) ^ (-γ)) := by
    rw [geom_sum_eq (ne_of_lt h2), ← neg_div_neg_eq]
    ring_nf
  rw [hgeq, inv_eq_one_div]
  refine div_le_div_of_nonneg_right ?_ h1r.le
  have := pow_nonneg h20 (M - 4)
  linarith

/-- **A sum over the bands of the tower**: if each band's term is at most `Φ(V_{ℓ+1})` with `Φ`
antitone and nonnegative on `[10, ∞)`, and `Φ(s) ≤ c s^{-γ}` from `r_4` on, then
`∑_{ℓ<L} g ℓ ≤ ∑_{j<4} Φ(r_j) + c r_4^{-γ}/(1 - 2^{-γ})`, `L` the depth. -/
lemma sum_tower_le {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) {g : ℕ → ℝ} {Φ : ℝ → ℝ}
    (hΦ : AntitoneOn Φ (Set.Ici 10)) (hΦ0 : ∀ s, 10 ≤ s → 0 ≤ Φ s)
    (hg : ∀ ℓ < aboveDepth Λ, g ℓ ≤ Φ (aboveV Λ (ℓ + 1)))
    {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (htail : ∀ s, towerR 4 ≤ s → Φ s ≤ c * s ^ (-γ)) :
    ∑ ℓ ∈ Finset.range (aboveDepth Λ), g ℓ
      ≤ ∑ j ∈ Finset.range 4, Φ (towerR j) + c * towerR 4 ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by
  set L := aboveDepth Λ with hLdef
  -- each band at its range's lower end
  have h1 : ∑ ℓ ∈ Finset.range L, g ℓ ≤ ∑ ℓ ∈ Finset.range L, Φ (towerR (L - 1 - ℓ)) := by
    refine Finset.sum_le_sum fun ℓ hℓ => le_trans (hg ℓ (Finset.mem_range.1 hℓ)) ?_
    have hℓL := Finset.mem_range.1 hℓ
    have hge := aboveV_ge_towerR hΛ (j := L - 1 - ℓ) (by omega)
    rw [← hLdef, show L - (L - 1 - ℓ) = ℓ + 1 by omega] at hge
    exact hΦ (Set.mem_Ici.2 (towerR_ten_le _)) (Set.mem_Ici.2 (le_trans (towerR_ten_le _) hge))
      hge
  have h2 : ∑ ℓ ∈ Finset.range L, Φ (towerR (L - 1 - ℓ)) = ∑ j ∈ Finset.range L, Φ (towerR j) :=
    Finset.sum_range_reflect (fun j => Φ (towerR j)) L
  have hnn : ∀ j, 0 ≤ Φ (towerR j) := fun j => hΦ0 _ (towerR_ten_le j)
  -- pad to `max L 4` and split at `4`
  have h3 : ∑ j ∈ Finset.range L, Φ (towerR j) ≤ ∑ j ∈ Finset.range (max L 4), Φ (towerR j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left _ _))
      fun j _ _ => hnn j
  have h4 : ∑ j ∈ Finset.range (max L 4), Φ (towerR j)
      = ∑ j ∈ Finset.range 4, Φ (towerR j) + ∑ j ∈ Finset.Ico 4 (max L 4), Φ (towerR j) :=
    (Finset.sum_range_add_sum_Ico _ (le_max_right _ _)).symm
  have h5 : ∑ j ∈ Finset.Ico 4 (max L 4), Φ (towerR j)
      ≤ ∑ j ∈ Finset.Ico 4 (max L 4), c * towerR j ^ (-γ) := by
    refine Finset.sum_le_sum fun j hj => htail _ ?_
    have hj4 := (Finset.mem_Ico.1 hj).1
    obtain ⟨i, rfl⟩ : ∃ i, j = 4 + i := ⟨j - 4, by omega⟩
    have := towerR_add_ge i
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have := towerR_ten_le 4
    nlinarith
  have h6 := sum_Ico_towerR_rpow_le hc hγ (max L 4)
  linarith

/-- **Power means over at most `n` terms**: for `0 < p ≤ 1` and nonnegative `x`,
`∑_{i∈S} x_i^p ≤ n^{1-p}(∑_{i∈S} x_i)^p` when `#S ≤ n`. -/
lemma sum_rpow_le_card_rpow {ι : Type*} (S : Finset ι) {x : ι → ℝ} (hx : ∀ i ∈ S, 0 ≤ x i)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {n : ℝ} (hn : (S.card : ℝ) ≤ n) :
    ∑ i ∈ S, x i ^ p ≤ n ^ (1 - p) * (∑ i ∈ S, x i) ^ p := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp [Real.zero_rpow hp0.ne']
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hy : ∀ i ∈ S, 0 ≤ x i ^ p := fun i hi => Real.rpow_nonneg (hx i hi) _
  have hP : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := S) (f := fun i => x i ^ p) hP hy
  have hback : ∀ i ∈ S, (x i ^ p) ^ (1 / p) = x i := fun i hi => by
    rw [← Real.rpow_mul (hx i hi), mul_one_div_cancel hp0.ne', Real.rpow_one]
  rw [Finset.sum_congr rfl hback] at h
  have hsum0 : 0 ≤ ∑ i ∈ S, x i ^ p := Finset.sum_nonneg hy
  have hX0 : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg hx
  -- take `p`-th powers
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hsum0 _) h hp0.le
  rw [← Real.rpow_mul hsum0, one_div_mul_cancel hp0.ne', Real.rpow_one,
    Real.mul_rpow (Real.rpow_nonneg hcard.le _) hX0, ← Real.rpow_mul hcard.le] at h'
  refine le_trans h' (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hX0 _))
  have hexp : (1 / p - 1) * p = 1 - p := by field_simp
  rw [hexp]
  exact Real.rpow_le_rpow hcard.le hn (by linarith)

/-! ### The levels' scales -/

/-- `e^Λ ≥ 482.8Λ² + 71.1Λ` for `Λ ≥ 11`. -/
lemma exp_ge_poly_eleven {Λ : ℝ} (hΛ : 11 ≤ Λ) : 482.8 * Λ ^ 2 + 71.1 * Λ ≤ Real.exp Λ := by
  have h11 : (59874 : ℝ) ≤ Real.exp 11 := by interval_decide (trust := kernel)
  set t := Λ - 11 with htdef
  have ht : 0 ≤ t := by linarith
  have h1 : Real.exp Λ = Real.exp 11 * Real.exp t := by rw [← Real.exp_add, htdef]; ring_nf
  have h2 := Real.quadratic_le_exp_of_nonneg ht
  have h3 : 59874 * (1 + t + t ^ 2 / 2) ≤ Real.exp Λ := by
    rw [h1]
    exact mul_le_mul h11 h2 (by positivity) (Real.exp_pos _).le
  have hΛt : Λ = 11 + t := by rw [htdef]; ring
  have h4 : 482.8 * Λ ^ 2 + 71.1 * Λ ≤ 59874 * (1 + t + t ^ 2 / 2) := by
    rw [hΛt]
    nlinarith [sq_nonneg t]
  linarith

/-- `e^Λ ≥ 5400Λ` for `Λ ≥ 11`. -/
lemma exp_ge_lin_eleven {Λ : ℝ} (hΛ : 11 ≤ Λ) : 5400 * Λ ≤ Real.exp Λ := by
  have h11 : (59874 : ℝ) ≤ Real.exp 11 := by interval_decide (trust := kernel)
  have h1 : Real.exp Λ = Real.exp 11 * Real.exp (Λ - 11) := by rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (Λ - 11)
  have h3 : 59874 * (Λ - 11 + 1) ≤ Real.exp Λ := by
    rw [h1]
    exact mul_le_mul h11 h2 (by linarith) (Real.exp_pos _).le
  nlinarith

/-- **The levels' scales**: for `x ≥ 3` with `Λ = log log x ≥ 11` and `ℓ ≤ L` (the depth),
`10 ≤ V_ℓ ≤ 3Λ`, `log x/V_ℓ - log 2 ≤ log z_ℓ ≤ log x/V_ℓ`, `log z_ℓ ≥ 1799` and
`7Λ + 1 ≤ 0.0435 log z_ℓ`. -/
lemma aboveZ_log_facts {x : ℝ} (hx3 : 3 ≤ x) (hΛ : 11 ≤ Real.log (Real.log x)) {ℓ : ℕ}
    (hℓ : ℓ ≤ aboveDepth (Real.log (Real.log x))) :
    10 ≤ aboveV (Real.log (Real.log x)) ℓ
      ∧ aboveV (Real.log (Real.log x)) ℓ ≤ 3 * Real.log (Real.log x)
      ∧ Real.log x / aboveV (Real.log (Real.log x)) ℓ - Real.log 2 ≤ Real.log (aboveZ x ℓ)
      ∧ Real.log (aboveZ x ℓ) ≤ Real.log x / aboveV (Real.log (Real.log x)) ℓ
      ∧ 1799 ≤ Real.log x / aboveV (Real.log (Real.log x)) ℓ - Real.log 2
      ∧ 7 * Real.log (Real.log x) + 1 ≤ 0.0435 * Real.log (aboveZ x ℓ) := by
  set Λ := Real.log (Real.log x) with hΛdef
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx : Real.log x = Real.exp Λ := by rw [hΛdef, Real.exp_log hlx0]
  obtain ⟨-, hV10⟩ := aboveDepth_spec (by linarith : 10 ≤ 3 * Λ)
  have hV := hV10 ℓ hℓ
  have hL8 : ∀ k ≤ aboveDepth Λ, 8 ≤ aboveV Λ k := fun k hk => by linarith [hV10 k hk]
  have hV3 := aboveV_le hL8 ℓ hℓ
  have hVpos : 0 < aboveV Λ ℓ := by linarith
  set u := Real.log x / aboveV Λ ℓ with hudef
  have hpoly := exp_ge_poly_eleven hΛ
  have hΛ0 : 0 < Λ := by linarith
  -- `u ≥ e^Λ/(3Λ)`
  have hu3 : Real.exp Λ / (3 * Λ) ≤ u := by
    rw [hudef, hlx]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hVpos hV3
  have hlog2 := Real.log_two_lt_d9
  have hlin := exp_ge_lin_eleven hΛ
  have hu : 1800 ≤ u := by
    refine le_trans ?_ hu3
    rw [le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨hl1, hl2⟩ := log_floor_exp_bounds (by linarith : (1 : ℝ) ≤ u)
  have hz : aboveZ x ℓ = ⌊Real.exp u⌋₊ := rfl
  rw [← hz] at hl1 hl2
  refine ⟨hV, hV3, hl1, hl2, by linarith, ?_⟩
  -- `7Λ + 1 ≤ 0.0435 (e^Λ/(3Λ) - 0.7)`
  have h1 : 7 * Λ + 1 ≤ 0.0435 * (Real.exp Λ / (3 * Λ) - 0.7) := by
    have h2 : Real.exp Λ / (3 * Λ) ≥ (482.8 * Λ ^ 2 + 71.1 * Λ) / (3 * Λ) :=
      div_le_div_of_nonneg_right hpoly (by positivity)
    have h3 : (482.8 * Λ ^ 2 + 71.1 * Λ) / (3 * Λ) = 482.8 / 3 * Λ + 23.7 := by
      field_simp
      ring
    linarith
  linarith

/-- **The truncation bound's constant along the tower** at `ε`, for `Λ ≥ 11` and `ℓ ≤ L`:
`K ≤ 2.0913(1+ε)`. -/
lemma aboveZ_lemmaTConst_le {x ε : ℝ} (hε : 0 < ε) (hx3 : 3 ≤ x)
    (hΛ : 11 ≤ Real.log (Real.log x)) {ℓ : ℕ} (hℓ : ℓ ≤ aboveDepth (Real.log (Real.log x))) :
    lemmaTConst (aboveZ x ℓ) (sieveLevel x (aboveZ x ℓ)) (Real.log x ^ 2)⁻¹ ε
        * Real.exp (2 * (Real.log x)⁻¹) ≤ 2.0913 * (1 + ε) := by
  obtain ⟨hV10, -, -, -, -, hρ⟩ := aboveZ_log_facts hx3 hΛ hℓ
  have hL8 : ∀ k ≤ aboveDepth (Real.log (Real.log x)), 8 ≤ aboveV (Real.log (Real.log x)) k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ hk).1]
  obtain ⟨hlx1, hz, -⟩ := aboveZ_facts hx3 hΛ hL8
  obtain ⟨-, hzx, hz'⟩ := hz ℓ hℓ
  have hlx0 : 0 < Real.log x := by linarith
  have hlx : 59874 ≤ Real.log x := by
    have h11 : (59874 : ℝ) ≤ Real.exp 11 := by interval_decide (trust := kernel)
    have := Real.exp_le_exp.2 hΛ
    rw [Real.exp_log hlx0] at this
    linarith
  refine le_trans (lemmaTConst_mul_exp_le hε (by linarith) hzx hz' (by norm_num) hρ) ?_
  -- the factors at `log x ≥ 59874`
  have h1 : 6 / Real.log x ≤ 0.00011 := by rw [div_le_iff₀ hlx0]; linarith
  have h2 : (Real.log x ^ 2)⁻¹ ≤ 1 / 10 ^ 9 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have h5 : (Real.log x ^ 5)⁻¹ ≤ 1 / 10 ^ 9 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    have : (59874 : ℝ) ^ 5 ≤ Real.log x ^ 5 := pow_le_pow_left₀ (by norm_num) hlx 5
    nlinarith
  have he : Real.exp (2 * (Real.log x)⁻¹) ≤ 1.00004 := by
    have h3 : 2 * (Real.log x)⁻¹ ≤ 0.0000335 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hlx0]; linarith
    have := Real.exp_bound_div_one_sub_of_interval (x := 2 * (Real.log x)⁻¹) (by positivity)
      (by linarith)
    refine le_trans this ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hA : 2 / (1 - 0.0435) + 6 / Real.log x ≤ 2.09108 := by norm_num; linarith
  have hB : (1 + (Real.log x ^ 2)⁻¹) * (1 + (Real.log x ^ 5)⁻¹) * Real.exp (2 * (Real.log x)⁻¹)
      ≤ 1.00005 := by
    have h0 : 0 ≤ (Real.log x ^ 2)⁻¹ := by positivity
    have h0' : 0 ≤ (Real.log x ^ 5)⁻¹ := by positivity
    have := mul_le_mul (mul_le_mul (by linarith : 1 + (Real.log x ^ 2)⁻¹ ≤ 1 + 1 / 10 ^ 9)
      (by linarith : 1 + (Real.log x ^ 5)⁻¹ ≤ 1 + 1 / 10 ^ 9) (by positivity) (by positivity)) he
      (Real.exp_pos _).le (by positivity)
    refine le_trans this ?_
    norm_num
  have hAp : 0 ≤ 2 / (1 - 0.0435) + 6 / Real.log x := by positivity
  calc (1 + ε) * (2 / (1 - 0.0435) + 6 / Real.log x) * (1 + (Real.log x ^ 2)⁻¹)
        * (1 + (Real.log x ^ 5)⁻¹) * Real.exp (2 * (Real.log x)⁻¹)
      = (1 + ε) * (2 / (1 - 0.0435) + 6 / Real.log x) * ((1 + (Real.log x ^ 2)⁻¹)
        * (1 + (Real.log x ^ 5)⁻¹) * Real.exp (2 * (Real.log x)⁻¹)) := by ring
    _ ≤ (1 + ε) * 2.09108 * 1.00005 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hA (by linarith)) hB (by positivity)
          (by positivity)
    _ ≤ 2.0913 * (1 + ε) := by nlinarith

/-- **The truncation bound's error along the tower** at `ε`, for `Λ ≥ 11` and `ℓ ≤ L`:
`E ≤ 0.0012(1 + 1/ε)`. -/
lemma aboveZ_smallQReductionErr_le {x ε : ℝ} (hε : 0 < ε) (hx3 : 3 ≤ x)
    (hΛ : 11 ≤ Real.log (Real.log x)) {ℓ : ℕ} (hℓ : ℓ ≤ aboveDepth (Real.log (Real.log x))) :
    smallQReductionErr x (sieveLevel x (aboveZ x ℓ)) (Real.log x ^ 2)⁻¹ ε
      ≤ 0.0012 * (1 + 1 / ε) := by
  obtain ⟨-, -, hl1, -, hlz, hρ⟩ := aboveZ_log_facts hx3 hΛ hℓ
  have hL8 : ∀ k ≤ aboveDepth (Real.log (Real.log x)), 8 ≤ aboveV (Real.log (Real.log x)) k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ hk).1]
  obtain ⟨hlx1, hz, -⟩ := aboveZ_facts hx3 hΛ hL8
  obtain ⟨-, hzx, hz'⟩ := hz ℓ hℓ
  have hlx0 : 0 < Real.log x := by linarith
  have hlx : 59874 ≤ Real.log x := by
    have h11 : (59874 : ℝ) ≤ Real.exp 11 := by interval_decide (trust := kernel)
    have := Real.exp_le_exp.2 hΛ
    rw [Real.exp_log hlx0] at this
    linarith
  refine le_trans (smallQReductionErr_le hε (by linarith) hzx hz' (by norm_num) hρ) ?_
  have hlz' : 1799 ≤ Real.log (aboveZ x ℓ) := le_trans hlz hl1
  have h1 : 1.003 / Real.log x ≤ 0.0000168 := by rw [div_le_iff₀ hlx0]; linarith
  have h2 : 2.0001 / ((1 - 0.0435) * Real.log (aboveZ x ℓ)) ≤ 0.00117 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hε1 : 0 ≤ 1 + 1 / ε := by positivity
  calc (1 + 1 / ε) * (1.003 / Real.log x + 2.0001 / ((1 - 0.0435) * Real.log (aboveZ x ℓ)))
      ≤ (1 + 1 / ε) * 0.0012 := mul_le_mul_of_nonneg_left (by linarith) hε1
    _ = 0.0012 * (1 + 1 / ε) := by ring

/-! ### A band, normalised -/

/-- The window constant of the hierarchy at `K_c`, `η'`:
`C_W = K_c^q(1+η')^q·pfC1·ω·1.5^a·e^{-a}/(1-e^{-a})`, `a = q(2q-1)`. -/
noncomputable def winConstW (q η' Kc : ℝ) : ℝ :=
  Kc ^ q * (1 + η') ^ q * pfC1 q * omegaClean q * (3 / 2) ^ (q * (2 * q - 1))
    * (Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1)))))

/-- A band's overheads at `V_{ℓ+1} = s`, per unit `(log x)^a`:
`s^{-a}pfC2(K_c^q(cen^q + coh^q) + (4·10⁻¹³K_c)^q) + e^{-as/3}pfC1(K_c^q(1+η')^q(J₀ + far) + E_c^q)
  + pfC1(1.001e^{0.0181})^{eq}e^{-s(q(1-e/3) + a/3) - eq log s}`. -/
noncomputable def bandPhi (q η' Kc Ec s : ℝ) : ℝ :=
  s ^ (-(q * (2 * q - 1))) * (pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
      + (Kc * 4e-13) ^ q))
  + Real.exp (-(q * (2 * q - 1) * s / 3)) * (pfC1 q * (Kc ^ q * (1 + η') ^ q
      * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q + (Real.exp 0.0181 / Real.pi) ^ q)
      + Ec ^ q))
  + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
    * Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3))
      - Real.exp 1 * q * Real.log s)

set_option maxHeartbeats 400000 in
-- one band's cleaned bound, rewritten in the tower's scales
/-- **A band of the hierarchy with supplied windows, normalised.**  For `½ < q ≤ 1`,
`η', ε > 0`, `x ≥ 3` with `Λ = log log x ≥ 11` and a band `ℓ < L` (the depth), with
`K_c = 2.0913(1+ε)`, `E_c = 0.0012(1+1/ε)`:

`pfFull(z_ℓ)·bandLevelW(z_ℓ, z_{ℓ+1}, w) ≤ (log x)^a·bandPhi(V_{ℓ+1}) + K_c^q(1+η')^q pfC1·W_B`
for windows `w` with the hypothesis of `RMF.pfFull_mul_bandLevelW_le_clean`. -/
theorem pfFull_mul_bandLevelW_le_bandPhi {q η' ε x WB : ℝ} {w : ℕ → ℝ} (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x)
    (hΛ : 11 ≤ Real.log (Real.log x)) {ℓ : ℕ} (hℓ : ℓ < aboveDepth (Real.log (Real.log x)))
    (hw0 : ∀ k, 0 ≤ w k)
    (hWin : pfFull q (aboveZ x ℓ) * (∑ k ∈ Finset.range (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))),
        w k + (mBand (aboveZ x ℓ) (aboveZ x (ℓ + 1))
          / (Real.pi * 1 * Real.exp (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))))) ^ q)
      ≤ Real.log (aboveZ x (ℓ + 1)) ^ (q * (2 * q - 1))
          * ((Real.log (aboveZ x ℓ) / Real.log (aboveZ x (ℓ + 1))) ^ (q * (2 * q - 1))
            * pfC1 q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
              + (Real.exp 0.0181 / Real.pi) ^ q))
        + pfC1 q * WB) :
    pfFull q (aboveZ x ℓ) * bandLevelW q 1 η' ε x (aboveZ x ℓ) (aboveZ x (ℓ + 1)) w
      ≤ Real.log x ^ (q * (2 * q - 1))
          * bandPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε))
            (aboveV (Real.log (Real.log x)) (ℓ + 1))
        + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q * pfC1 q * WB := by
  set Λ := Real.log (Real.log x) with hΛdef
  set a := q * (2 * q - 1) with hadef
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ a := mul_nonneg hq0' (by linarith)
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  -- the scales
  obtain ⟨hVl, hVl3, hl1, hl2, hlz, -⟩ := aboveZ_log_facts hx3 hΛ hℓ.le
  obtain ⟨hVs, hVs3, hs1, hs2, hsz, -⟩ := aboveZ_log_facts hx3 hΛ (Nat.succ_le_of_lt hℓ)
  have hL8 : ∀ k ≤ aboveDepth Λ, 8 ≤ aboveV Λ k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ hk).1]
  obtain ⟨-, hz, hmono⟩ := aboveZ_facts hx3 hΛ hL8
  obtain ⟨hy2, -, -⟩ := hz ℓ hℓ.le
  obtain ⟨-, hzx, hz'⟩ := hz (ℓ + 1) hℓ
  set y := aboveZ x ℓ with hydef
  set z := aboveZ x (ℓ + 1) with hzdef
  set Vy := aboveV Λ ℓ with hVydef
  set s := aboveV Λ (ℓ + 1) with hsdef
  have hVy0 : 0 < Vy := by linarith
  have hs0 : 0 < s := by linarith
  have hsVy : s = 3 * Real.log Vy := by rw [hsdef, aboveV_succ]
  have hVye : Vy = Real.exp (s / 3) := by
    rw [hsVy, mul_div_cancel_left₀ _ (by norm_num), Real.exp_log hVy0]
  have hlog2 := Real.log_two_lt_d9
  have hly0 : 0 < Real.log y := by linarith
  have hlz0 : 0 < Real.log z := by linarith
  have hly1000 : 1000 ≤ Real.log y := by linarith
  have hlx50000 : 50000 ≤ Real.log x := by
    have h1 : (1799 : ℝ) + Real.log 2 ≤ Real.log x / Vy := by linarith
    have h2 : Real.log x / Vy ≤ Real.log x / 10 := div_le_div_of_nonneg_left hlx0.le (by norm_num)
      hVl
    have h3 : (59874 : ℝ) ≤ Real.log x := by
      have h11 : (59874 : ℝ) ≤ Real.exp 11 := by interval_decide (trust := kernel)
      have := Real.exp_le_exp.2 hΛ
      rw [hΛdef, Real.exp_log hlx0] at this
      linarith
    linarith
  -- the cleaned band
  have hK := aboveZ_lemmaTConst_le hε hx3 hΛ (Nat.succ_le_of_lt hℓ)
  have hE := aboveZ_smallQReductionErr_le hε hx3 hΛ (Nat.succ_le_of_lt hℓ)
  have hclean := pfFull_mul_bandLevelW_le_clean hq0 hq1 hη' hε hy2 (hmono ℓ hℓ) hzx hly1000
    hlx50000 hz' hK hE hw0 hWin
  rw [← hadef] at hclean
  refine le_trans hclean ?_
  set Kc := 2.0913 * (1 + ε) with hKcdef
  set Ec := 0.0012 * (1 + 1 / ε) with hEcdef
  have hKc0 : 0 ≤ Kc := by positivity
  have hEc0 : 0 ≤ Ec := by positivity
  -- the scale relations
  have hA1 : (Real.log z / Real.log x) ^ a ≤ s ^ (-a) := by
    rw [Real.rpow_neg hs0.le, ← Real.inv_rpow hs0.le]
    refine Real.rpow_le_rpow (div_nonneg hlz0.le hlx0.le) ?_ ha
    rw [div_le_iff₀ hlx0, inv_mul_eq_div]
    exact hs2
  have hA2 : (Real.log y / Real.log x) ^ a ≤ Real.exp (-(a * s / 3)) := by
    have h1 : Real.log y / Real.log x ≤ Real.exp (-(s / 3)) := by
      rw [div_le_iff₀ hlx0, Real.exp_neg, ← hVye, inv_mul_eq_div]
      exact hl2
    calc (Real.log y / Real.log x) ^ a ≤ Real.exp (-(s / 3)) ^ a :=
          Real.rpow_le_rpow (div_nonneg hly0.le hlx0.le) h1 ha
      _ = Real.exp (-(a * s / 3)) := by rw [← Real.exp_mul]; ring_nf
  have hA3 : s ≤ Real.log x / Real.log z := by
    rw [le_div_iff₀ hlz0]
    have := mul_le_mul_of_nonneg_left hs2 hs0.le
    rw [mul_div_cancel₀ _ hs0.ne'] at this
    linarith
  have hκ : Real.log z / Real.log y ≤ 1.001 * Real.exp (s / 3) / s := by
    rw [div_le_div_iff₀ hly0 hs0]
    have h1 : Real.log z * s ≤ Real.log x := by
      have := mul_le_mul_of_nonneg_right hs2 hs0.le
      rwa [div_mul_cancel₀ _ hs0.ne'] at this
    have h2 : Real.log x ≤ 1.001 * Real.exp (s / 3) * Real.log y := by
      have h3 : Real.log x / Vy ≤ 1.001 * Real.log y := by
        have : Real.log 2 ≤ 0.001 * (Real.log x / Vy - Real.log 2) := by linarith
        linarith
      rw [div_le_iff₀ hVy0, hVye] at h3
      linarith
    linarith
  have hJF0 : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
      + (Real.exp 0.0181 / Real.pi) ^ q := by
    have : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    positivity
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hc2 : 0 ≤ pfC2 q := (Real.exp_pos _).le
  have hcen0 : 0 ≤ cenClean q := by
    rw [cenClean]
    have : 0 ≤ Real.exp (2 * (1 - q) * 0.5158) - 1 :=
      sub_nonneg.2 (Real.one_le_exp (by nlinarith))
    positivity
  -- the pieces, per unit `(log x)^a`
  have hlxa : 0 < Real.log x ^ a := Real.rpow_pos_of_pos hlx0 _
  have hsplitz : Real.log z ^ a = Real.log x ^ a * (Real.log z / Real.log x) ^ a := by
    rw [← Real.mul_rpow hlx0.le (div_nonneg hlz0.le hlx0.le)]
    congr 1
    field_simp
  have hsplity : Real.log y ^ a = Real.log x ^ a * (Real.log y / Real.log x) ^ a := by
    rw [← Real.mul_rpow hlx0.le (div_nonneg hly0.le hlx0.le)]
    congr 1
    field_simp
  have hyz : Real.log z ^ a * (Real.log y / Real.log z) ^ a = Real.log y ^ a := by
    rw [← Real.mul_rpow hlz0.le (div_nonneg hly0.le hlz0.le)]
    congr 1
    field_simp
  -- the lx-error
  have hlxerr : (Kc / (1000 * Real.log x ^ 2)) ^ q ≤ (Kc * 4e-13) ^ q := by
    refine Real.rpow_le_rpow (by positivity) ?_ hq0'
    rw [div_le_iff₀ (by positivity)]
    have h4 := mul_le_mul hlx50000 hlx50000 (by norm_num) hlx0.le
    have h5 : 1 ≤ 4e-13 * (1000 * Real.log x ^ 2) := by rw [sq]; linarith
    calc Kc = Kc * 1 := (mul_one _).symm
      _ ≤ Kc * (4e-13 * (1000 * Real.log x ^ 2)) := mul_le_mul_of_nonneg_left h5 hKc0
      _ = Kc * 4e-13 * (1000 * Real.log x ^ 2) := by ring
  -- the atom
  have hatom : Real.log y ^ a * (Real.exp (-(q * (Real.log x / Real.log z)))
      * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q))
      ≤ Real.log x ^ a * ((1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
        * Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + a / 3)) - Real.exp 1 * q * Real.log s)) := by
    have heq0 : 0 ≤ Real.exp 1 * q := mul_nonneg (Real.exp_pos 1).le hq0'
    have h1 : Real.exp (-(q * (Real.log x / Real.log z))) ≤ Real.exp (-(q * s)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hA3 hq0'))
    have h2 : (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q)
        ≤ (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
          * (Real.exp (s / 3) / s) ^ (Real.exp 1 * q) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ heq0
      calc Real.log z / Real.log y * Real.exp 0.0181
          ≤ 1.001 * Real.exp (s / 3) / s * Real.exp 0.0181 :=
            mul_le_mul_of_nonneg_right hκ (Real.exp_pos _).le
        _ = 1.001 * Real.exp 0.0181 * (Real.exp (s / 3) / s) := by ring
    have h3 : (Real.exp (s / 3) / s) ^ (Real.exp 1 * q)
        = Real.exp (Real.exp 1 * q * (s / 3) - Real.exp 1 * q * Real.log s) := by
      rw [Real.div_rpow (Real.exp_pos _).le hs0.le, ← Real.exp_mul,
        Real.rpow_def_of_pos hs0, ← Real.exp_sub]
      ring_nf
    have h4 : Real.log y ^ a ≤ Real.log x ^ a * Real.exp (-(a * s / 3)) := by
      rw [hsplity]
      exact mul_le_mul_of_nonneg_left hA2 hlxa.le
    have hB0 : 0 ≤ Real.exp (-(q * (Real.log x / Real.log z)))
        * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q) := by positivity
    calc Real.log y ^ a * (Real.exp (-(q * (Real.log x / Real.log z)))
          * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q))
        ≤ (Real.log x ^ a * Real.exp (-(a * s / 3))) * (Real.exp (-(q * s))
          * ((1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
            * Real.exp (Real.exp 1 * q * (s / 3) - Real.exp 1 * q * Real.log s))) := by
          rw [← h3]
          exact mul_le_mul h4 (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le) hB0
            (by positivity)
      _ = Real.log x ^ a * ((1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
          * (Real.exp (-(a * s / 3)) * Real.exp (-(q * s))
            * Real.exp (Real.exp 1 * q * (s / 3) - Real.exp 1 * q * Real.log s))) := by ring
      _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
  -- assemble
  have hP1 : Real.log z ^ a * (pfC2 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc / (1000 * Real.log x ^ 2)) ^ q))
      ≤ Real.log x ^ a * (s ^ (-a) * (pfC2 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q))) := by
    rw [hsplitz, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hA1 (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hlxerr) hc2) (by positivity) (Real.rpow_nonneg hs0.le _)) hlxa.le
  have hP2 : Real.log z ^ a * (pfC1 q * (Real.log y / Real.log z) ^ a
        * (Kc ^ q * (1 + η') ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q)
        + Real.exp (-(q * (Real.log x / Real.log z)))
          * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q)
        + Ec ^ q))
      ≤ Real.log x ^ a * (Real.exp (-(a * s / 3)) * (pfC1 q * (Kc ^ q * (1 + η') ^ q
          * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q))
        + pfC1 q * ((1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
          * Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + a / 3))
            - Real.exp 1 * q * Real.log s))) := by
    have e1 : Real.log z ^ a * (pfC1 q * (Real.log y / Real.log z) ^ a
        * (Kc ^ q * (1 + η') ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q)
        + Real.exp (-(q * (Real.log x / Real.log z)))
          * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q)
        + Ec ^ q))
        = pfC1 q * (Real.log y ^ a * (Kc ^ q * (1 + η') ^ q
            * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
              + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q))
          + pfC1 q * (Real.log y ^ a * (Real.exp (-(q * (Real.log x / Real.log z)))
            * (Real.log z / Real.log y * Real.exp 0.0181) ^ (Real.exp 1 * q))) := by
      rw [← hyz]; ring
    rw [e1]
    have f1 : Real.log y ^ a * (Kc ^ q * (1 + η') ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q)
        ≤ Real.log x ^ a * Real.exp (-(a * s / 3)) * (Kc ^ q * (1 + η') ^ q
          * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q) := by
      rw [hsplity]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 hlxa.le) (by positivity)
    have f2 := mul_le_mul_of_nonneg_left hatom hc1
    have f1' := mul_le_mul_of_nonneg_left f1 hc1
    refine le_trans (add_le_add f1' f2) (le_of_eq ?_)
    ring
  have hfin := add_le_add hP1 hP2
  rw [bandPhi, ← hadef]
  have e2 : Real.log x ^ a * (s ^ (-a) * (pfC2 q * (Kc ^ q * (cenClean q ^ q
      + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q))
      + Real.exp (-(a * s / 3)) * (pfC1 q * (Kc ^ q * (1 + η') ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q))
      + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
        * Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + a / 3)) - Real.exp 1 * q * Real.log s))
      = Real.log x ^ a * (s ^ (-a) * (pfC2 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q)))
        + Real.log x ^ a * (Real.exp (-(a * s / 3)) * (pfC1 q * (Kc ^ q * (1 + η') ^ q
          * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q))
          + pfC1 q * ((1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)
            * Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + a / 3))
              - Real.exp 1 * q * Real.log s))) := by ring
  rw [e2]
  linarith

/-- **A band of the hierarchy, normalised.**  For `½ < q ≤ 1`, `η', ε > 0`, `x ≥ 3` with
`Λ = log log x ≥ 11` and a band `ℓ < L` (the depth), with `K_c = 2.0913(1+ε)`,
`E_c = 0.0012(1+1/ε)`:

`pfFull(z_ℓ)·bandLevel(z_ℓ, z_{ℓ+1}) ≤ (log x)^a·(bandPhi(V_{ℓ+1})
  + C_W((log z_{ℓ+1}/log x)^a - (log z_ℓ/log x)^a))`. -/
theorem pfFull_mul_bandLevel_le_bandPhi {q η' ε x : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 11 ≤ Real.log (Real.log x)) {ℓ : ℕ}
    (hℓ : ℓ < aboveDepth (Real.log (Real.log x))) :
    pfFull q (aboveZ x ℓ) * bandLevel q 1 η' ε (3 / 2) x (aboveZ x ℓ) (aboveZ x (ℓ + 1))
      ≤ Real.log x ^ (q * (2 * q - 1))
        * (bandPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε))
            (aboveV (Real.log (Real.log x)) (ℓ + 1))
          + winConstW q η' (2.0913 * (1 + ε))
            * ((Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ (q * (2 * q - 1))
              - (Real.log (aboveZ x ℓ) / Real.log x) ^ (q * (2 * q - 1)))) := by
  have hL8 : ∀ k ≤ aboveDepth (Real.log (Real.log x)), 8 ≤ aboveV (Real.log (Real.log x)) k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ hk).1]
  obtain ⟨hlx1, hz, hmono⟩ := aboveZ_facts hx3 hΛ hL8
  obtain ⟨hy2, -, -⟩ := hz ℓ hℓ.le
  obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ hℓ.le
  obtain ⟨hw0, hWin⟩ := bandWindows_jensen_clean hq0 hq1 hy2 (hmono ℓ hℓ) (by linarith)
  have h := pfFull_mul_bandLevelW_le_bandPhi hq0 hq1 hη' hε hx3 hΛ hℓ hw0 hWin
  rw [bandLevel_eq_bandLevelW]
  refine le_trans h (le_of_eq ?_)
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hly0 : 0 < Real.log (aboveZ x ℓ) := by linarith
  have hlz0 : 0 < Real.log (aboveZ x (ℓ + 1)) := by
    have := Real.log_le_log (by positivity) (by exact_mod_cast hmono ℓ hℓ :
      ((aboveZ x ℓ : ℕ) : ℝ) ≤ aboveZ x (ℓ + 1))
    linarith
  rw [winConstW, Real.div_rpow hlz0.le hlx0.le, Real.div_rpow hly0.le hlx0.le]
  field_simp

lemma cenClean_nonneg {q : ℝ} (hq1 : q ≤ 1) : 0 ≤ cenClean q := by
  rw [cenClean]
  have : 0 ≤ Real.exp (2 * (1 - q) * 0.5158) - 1 :=
    sub_nonneg.2 (Real.one_le_exp (by nlinarith))
  positivity

lemma omegaClean_nonneg {q : ℝ} (hq1 : q ≤ 1) : 0 ≤ omegaClean q := by
  rw [omegaClean]
  have : 0 ≤ taylorWindowW ((1 - q) * 2.33) :=
    taylorWindowW_nonneg (mul_nonneg (by linarith) (by norm_num))
  positivity

lemma winConstW_nonneg {q η' Kc : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hKc : 0 ≤ Kc) : 0 ≤ winConstW q η' Kc := by
  rw [winConstW]
  have ha : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hr : Real.exp (-(q * (2 * q - 1))) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have : 0 ≤ Real.exp (-(q * (2 * q - 1))) / (1 - Real.exp (-(q * (2 * q - 1)))) :=
    div_nonneg (Real.exp_pos _).le (by linarith)
  have := omegaClean_nonneg hq1
  have : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
  have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc _
  positivity

/-- The three pieces of `RMF.bandPhi`, each nonnegative and antitone in `s > 0`. -/
lemma bandPhi_antitoneOn {q η' Kc Ec : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hKc : 0 ≤ Kc) (hEc : 0 ≤ Ec) :
    AntitoneOn (bandPhi q η' Kc Ec) (Set.Ici 10) ∧ ∀ s, 10 ≤ s → 0 ≤ bandPhi q η' Kc Ec s := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  have hA2 : 0 ≤ pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
      + (Kc * 4e-13) ^ q) := by
    have := cenClean_nonneg hq1
    have : 0 ≤ (pfC2 q) := (Real.exp_pos _).le
    have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc _
    have : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg hq1) _
    have : 0 ≤ ((1 + 1 / η') / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ (Kc * 4e-13) ^ q := Real.rpow_nonneg (by positivity) _
    positivity
  have hA1 : 0 ≤ pfC1 q * (Kc ^ q * (1 + η') ^ q
      * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q + (Real.exp 0.0181 / Real.pi) ^ q)
      + Ec ^ q) := by
    have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : 0 ≤ pfC1 q := (Real.exp_pos _).le
    have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc _
    have : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q :=
      Real.rpow_nonneg (by positivity) _
    have : 0 ≤ (Real.exp 0.0181 / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ Ec ^ q := Real.rpow_nonneg hEc _
    positivity
  have hB : 0 ≤ pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
  have hc1 : 0 ≤ q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3 := by
    have := Real.exp_one_lt_d9
    have : 0 ≤ 1 - Real.exp 1 / 3 := by linarith
    positivity
  refine ⟨fun s hs t ht hst => ?_, fun s hs => ?_⟩
  · have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (Set.mem_Ici.1 hs)
    have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
    rw [bandPhi, bandPhi]
    have h1 : t ^ (-(q * (2 * q - 1))) ≤ s ^ (-(q * (2 * q - 1))) :=
      Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
    have h2 : Real.exp (-(q * (2 * q - 1) * t / 3)) ≤ Real.exp (-(q * (2 * q - 1) * s / 3)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (-(t * (q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3))
          - Real.exp 1 * q * Real.log t)
        ≤ Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3))
          - Real.exp 1 * q * Real.log s) := by
      refine Real.exp_le_exp.2 ?_
      have hl : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
      have heq : 0 ≤ Real.exp 1 * q := mul_nonneg (Real.exp_pos 1).le hq0'
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 hA2
    have := mul_le_mul_of_nonneg_right h2 hA1
    have := mul_le_mul_of_nonneg_left h3 hB
    linarith
  · rw [bandPhi]
    have hs0 : 0 < s := by linarith
    have : 0 ≤ s ^ (-(q * (2 * q - 1))) := Real.rpow_nonneg hs0.le _
    positivity

/-- `RMF.bandPhi` from `s ≥ 10` on is at most `C s^{-a}`, `C` the sum of its three constants. -/
lemma bandPhi_le_rpow {q η' Kc Ec s : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hKc : 0 ≤ Kc) (hEc : 0 ≤ Ec) (hs : 10 ≤ s) :
    bandPhi q η' Kc Ec s
      ≤ (pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q)
        + pfC1 q * (Kc ^ q * (1 + η') ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q)
        + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)) * s ^ (-(q * (2 * q - 1))) := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ q * (2 * q - 1) := mul_nonneg hq0' (by linarith)
  have hs0 : 0 < s := by linarith
  obtain ⟨-, hnn⟩ := bandPhi_antitoneOn hq0 hq1 hη' hKc hEc
  -- `e^{-as/3} ≤ s^{-a}`
  have h1 : Real.exp (-(q * (2 * q - 1) * s / 3)) ≤ s ^ (-(q * (2 * q - 1))) := by
    have h2 := two_mul_le_exp_div_three hs
    rw [Real.rpow_def_of_pos hs0]
    refine Real.exp_le_exp.2 ?_
    have h3 : Real.log s ≤ s / 3 := by
      have := Real.log_le_log hs0 (show s ≤ Real.exp (s / 3) by linarith)
      rwa [Real.log_exp] at this
    nlinarith
  -- `e^{-sc₁ - eq log s} ≤ s^{-a}`
  have h4 : Real.exp (-(s * (q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3))
      - Real.exp 1 * q * Real.log s) ≤ s ^ (-(q * (2 * q - 1))) := by
    rw [Real.rpow_def_of_pos hs0]
    refine Real.exp_le_exp.2 ?_
    have hc1 : 0 ≤ q * (1 - Real.exp 1 / 3) + q * (2 * q - 1) / 3 := by
      have := Real.exp_one_lt_d9
      have : 0 ≤ 1 - Real.exp 1 / 3 := by linarith
      positivity
    have hl : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    have hea : q * (2 * q - 1) ≤ Real.exp 1 * q := by
      have := Real.exp_one_gt_d9
      nlinarith
    nlinarith
  rw [bandPhi]
  have hA2 : 0 ≤ pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
      + (Kc * 4e-13) ^ q) := by
    have : 0 ≤ (pfC2 q) := (Real.exp_pos _).le
    have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc _
    have : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg hq1) _
    have : 0 ≤ ((1 + 1 / η') / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ (Kc * 4e-13) ^ q := Real.rpow_nonneg (by positivity) _
    positivity
  have hA1 : 0 ≤ pfC1 q * (Kc ^ q * (1 + η') ^ q
      * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q + (Real.exp 0.0181 / Real.pi) ^ q)
      + Ec ^ q) := by
    have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : 0 ≤ pfC1 q := (Real.exp_pos _).le
    have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc _
    have : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q :=
      Real.rpow_nonneg (by positivity) _
    have : 0 ≤ (Real.exp 0.0181 / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ Ec ^ q := Real.rpow_nonneg hEc _
    positivity
  have hB : 0 ≤ pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
  have e1 := mul_le_mul_of_nonneg_right h1 hA1
  have e2 := mul_le_mul_of_nonneg_left h4 hB
  have e3 : Real.exp (-(q * (2 * q - 1) * s / 3)) * (pfC1 q * (Kc ^ q * (1 + η') ^ q
      * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q + (Real.exp 0.0181 / Real.pi) ^ q)
      + Ec ^ q)) ≤ s ^ (-(q * (2 * q - 1))) * (pfC1 q * (Kc ^ q * (1 + η') ^ q
      * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q + (Real.exp 0.0181 / Real.pi) ^ q)
      + Ec ^ q)) := e1
  linarith

/-! ### The bottom and the top, normalised -/

/-- The bottom's overheads at `Λ` per unit `(log x)^a`, its nine top windows bounded by `TS`:
`(3Λ)^{-a}pfC1(K_c^q(cen^q + coh^q) + (4·10⁻¹³K_c)^q) + e^{-Λ(q(3-e) + a) - eq log(3Λ) + 0.2732eq}
  + e^{-aΛ}(E_c^q + K_c^q(1+η')^q(TS + (e^{0.2732}/(2π))^q))`. -/
noncomputable def botPhi (q η' Kc Ec Λ TS : ℝ) : ℝ :=
  (3 * Λ) ^ (-(q * (2 * q - 1))) * (pfC1 q * (Kc ^ q * (cenClean q ^ q
      + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q))
  + Real.exp (-(Λ * (q * (3 - Real.exp 1) + q * (2 * q - 1)))
      - Real.exp 1 * q * Real.log (3 * Λ) + 0.2732 * (Real.exp 1 * q))
  + Real.exp (-(q * (2 * q - 1) * Λ))
    * (Ec ^ q + Kc ^ q * (1 + η') ^ q * (TS + (Real.exp 0.2732 / (2 * Real.pi)) ^ q))

/-- The bottom's nine top windows at `q`, `z`. -/
noncomputable def botTopSum (q : ℝ) (z : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 9, min (winNoSplitFull q (bottomT 1 2 z k) z)
    (winSplitFull q (bottomT 1 2 z k) (splitPt (3 / 2) (bottomT 1 2 z k) 2 z) z)

/-- `e^Λ ≥ 6903Λ` for `Λ ≥ 11.5`, so the bottom's `log z₀ ≥ 2300`. -/
lemma exp_ge_lin_eleven_half {Λ : ℝ} (hΛ : 11.5 ≤ Λ) : 6903 * Λ ≤ Real.exp Λ := by
  have h11 : (98715 : ℝ) ≤ Real.exp 11.5 := by interval_decide (trust := kernel)
  have h1 : Real.exp Λ = Real.exp 11.5 * Real.exp (Λ - 11.5) := by rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (Λ - 11.5)
  have h3 : 98715 * (Λ - 11.5 + 1) ≤ Real.exp Λ := by
    rw [h1]
    exact mul_le_mul h11 h2 (by linarith) (Real.exp_pos _).le
  nlinarith

set_option maxHeartbeats 400000 in
-- the bottom's cleaned bound, rewritten in the tower's scales
/-- **The bottom of the hierarchy with supplied windows, normalised.**  For `½ < q ≤ 1`,
`η', ε > 0`, `x ≥ 3` with `Λ = log log x ≥ 11.5`, `K_c = 2.0913(1+ε)`, `E_c = 0.0012(1+1/ε)`:

`bottomLevelW(z₀, w) ≤ (log x)^a·botPhi(Λ, TS) + K_c^q(1+η')^q·W_B` for windows `w ≥ 0`
with `∑_{k<9} w k ≤ TS` and `∑_{9≤k<J} w k ≤ W_B`. -/
theorem bottomLevelW_le_botPhi {q η' ε x TS WB : ℝ} {w : ℕ → ℝ} (hq0 : 1 / 2 < q)
    (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 11.5 ≤ Real.log (Real.log x))
    (hw0 : ∀ k, 0 ≤ w k) (hw9 : ∑ k ∈ Finset.range 9, w k ≤ TS)
    (hTail : ∑ k ∈ Finset.Ico 9 (bottomJ 1 2 (aboveZ x 0)), w k ≤ WB) :
    bottomLevelW q 1 η' ε 2 x (aboveZ x 0) w
      ≤ Real.log x ^ (q * (2 * q - 1))
          * botPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) (Real.log (Real.log x)) TS
        + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q * WB := by
  set Λ := Real.log (Real.log x) with hΛdef
  set a := q * (2 * q - 1) with hadef
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 ≤ a := mul_nonneg hq0' (by linarith)
  have hΛ11 : 11 ≤ Λ := by linarith
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx : Real.log x = Real.exp Λ := by rw [hΛdef, Real.exp_log hlx0]
  obtain ⟨hV0, -, hl1, hl2, hlz, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.zero_le _)
  have hL8 : ∀ k ≤ aboveDepth Λ, 8 ≤ aboveV Λ k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ11 hk).1]
  obtain ⟨-, hz, -⟩ := aboveZ_facts hx3 hΛ11 hL8
  obtain ⟨hz2, hzx, hz'⟩ := hz 0 (Nat.zero_le _)
  set z := aboveZ x 0 with hzdef
  have hV0e : aboveV Λ 0 = 3 * Λ := aboveV_zero Λ
  rw [hV0e] at hl1 hl2 hlz
  have hΛ0 : 0 < Λ := by linarith
  have hlog2 := Real.log_two_lt_d9
  have hlz0 : 0 < Real.log z := by linarith
  -- `log z ≥ 2300`
  have hlz2300 : 2300 ≤ Real.log z := by
    have h1 := exp_ge_lin_eleven_half hΛ
    have h2 : 2301 ≤ Real.log x / (3 * Λ) := by
      rw [le_div_iff₀ (by positivity), hlx]; linarith
    linarith
  have hlx50000 : 50000 ≤ Real.log x := by
    have h1 := exp_ge_lin_eleven_half hΛ
    rw [hlx]; nlinarith
  have hK := aboveZ_lemmaTConst_le hε hx3 hΛ11 (Nat.zero_le _)
  have hE := aboveZ_smallQReductionErr_le hε hx3 hΛ11 (Nat.zero_le _)
  have hclean := bottomLevelW_le_clean hq0 hq1 hη' hε hz2 hzx (by linarith) hlx50000 hz' hK hE
    hw0 hTail
  rw [← hadef] at hclean
  refine le_trans hclean ?_
  set Kc := 2.0913 * (1 + ε) with hKcdef
  set Ec := 0.0012 * (1 + 1 / ε) with hEcdef
  have hKc0 : 0 ≤ Kc := by positivity
  have hEc0 : 0 ≤ Ec := by positivity
  have hlxa : 0 < Real.log x ^ a := Real.rpow_pos_of_pos hlx0 _
  have hsplitz : Real.log z ^ a = Real.log x ^ a * (Real.log z / Real.log x) ^ a := by
    rw [← Real.mul_rpow hlx0.le (div_nonneg hlz0.le hlx0.le)]
    congr 1
    field_simp
  have hA1 : (Real.log z / Real.log x) ^ a ≤ (3 * Λ) ^ (-a) := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    refine Real.rpow_le_rpow (div_nonneg hlz0.le hlx0.le) ?_ ha
    rw [div_le_iff₀ hlx0, inv_mul_eq_div]
    exact hl2
  have hlxerr : (Kc / (1000 * Real.log x ^ 2)) ^ q ≤ (Kc * 4e-13) ^ q := by
    refine Real.rpow_le_rpow (by positivity) ?_ hq0'
    rw [div_le_iff₀ (by positivity)]
    have h4 := mul_le_mul hlx50000 hlx50000 (by norm_num) hlx0.le
    have h5 : 1 ≤ 4e-13 * (1000 * Real.log x ^ 2) := by rw [sq]; linarith
    calc Kc = Kc * 1 := (mul_one _).symm
      _ ≤ Kc * (4e-13 * (1000 * Real.log x ^ 2)) := mul_le_mul_of_nonneg_left h5 hKc0
      _ = Kc * 4e-13 * (1000 * Real.log x ^ 2) := by ring
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  -- the atom, per unit `(log x)^a`
  have hatom : Real.exp (-(q * (Real.log x / Real.log z)))
      * (Real.log z * Real.exp 0.2732) ^ (Real.exp 1 * q)
      ≤ Real.log x ^ a * Real.exp (-(Λ * (q * (3 - Real.exp 1) + a))
        - Real.exp 1 * q * Real.log (3 * Λ) + 0.2732 * (Real.exp 1 * q)) := by
    have heq0 : 0 ≤ Real.exp 1 * q := mul_nonneg (Real.exp_pos 1).le hq0'
    have h1 : Real.exp (-(q * (Real.log x / Real.log z))) ≤ Real.exp (-(q * (3 * Λ))) := by
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hq0'))
      rw [le_div_iff₀ hlz0]
      have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ 3 * Λ)
      rw [mul_div_cancel₀ _ (by positivity)] at this
      linarith
    have h2 : (Real.log z * Real.exp 0.2732) ^ (Real.exp 1 * q)
        ≤ (Real.exp Λ / (3 * Λ) * Real.exp 0.2732) ^ (Real.exp 1 * q) := by
      refine Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right ?_
        (Real.exp_pos _).le) heq0
      rw [← hlx]; exact hl2
    have h3 : (Real.exp Λ / (3 * Λ) * Real.exp 0.2732) ^ (Real.exp 1 * q)
        = Real.exp (Real.exp 1 * q * (Λ - Real.log (3 * Λ) + 0.2732)) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_exp]
      ring_nf
    have h4 : Real.log x ^ a = Real.exp (a * Λ) := by
      rw [hlx, ← Real.exp_mul]; ring_nf
    rw [h4, ← Real.exp_add]
    calc Real.exp (-(q * (Real.log x / Real.log z)))
          * (Real.log z * Real.exp 0.2732) ^ (Real.exp 1 * q)
        ≤ Real.exp (-(q * (3 * Λ))) * Real.exp (Real.exp 1 * q * (Λ - Real.log (3 * Λ)
          + 0.2732)) := by
          rw [← h3]
          exact mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
      _ = Real.exp (a * Λ + (-(Λ * (q * (3 - Real.exp 1) + a))
          - Real.exp 1 * q * Real.log (3 * Λ) + 0.2732 * (Real.exp 1 * q))) := by
          rw [← Real.exp_add]; ring_nf
  -- the absolute pieces, per unit `(log x)^a`
  have hunit : Real.log x ^ a * Real.exp (-(a * Λ)) = 1 := by
    rw [hlx, ← Real.exp_mul, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hTSz := hw9
  have hTS0 : 0 ≤ ∑ k ∈ Finset.range 9, w k := Finset.sum_nonneg fun k _ => hw0 k
  have hKq0 : 0 ≤ Kc ^ q * (1 + η') ^ q :=
    mul_nonneg (Real.rpow_nonneg hKc0 _) (Real.rpow_nonneg (by linarith) _)
  have habs : Ec ^ q + Kc ^ q * (1 + η') ^ q * (∑ k ∈ Finset.range 9, w k
        + (Real.exp 0.2732 / (2 * Real.pi)) ^ q)
      ≤ Real.log x ^ a * (Real.exp (-(a * Λ)) * (Ec ^ q + Kc ^ q * (1 + η') ^ q
        * (TS + (Real.exp 0.2732 / (2 * Real.pi)) ^ q))) := by
    rw [← mul_assoc, hunit, one_mul]
    have : ∑ k ∈ Finset.range 9, w k ≤ TS := hTSz
    have := mul_le_mul_of_nonneg_left (add_le_add_right this
      ((Real.exp 0.2732 / (2 * Real.pi)) ^ q)) hKq0
    linarith
  -- assemble
  have hP1 : Real.log z ^ a * (pfC1 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc / (1000 * Real.log x ^ 2)) ^ q))
      ≤ Real.log x ^ a * ((3 * Λ) ^ (-a) * (pfC1 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q))) := by
    rw [hsplitz, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hA1 (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hlxerr) hc1) (by
        have := cenClean_nonneg hq1
        have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc0 _
        have : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg hq1) _
        have : 0 ≤ ((1 + 1 / η') / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
        have : 0 ≤ (Kc / (1000 * Real.log x ^ 2)) ^ q := Real.rpow_nonneg (by positivity) _
        positivity) (Real.rpow_nonneg (by positivity) _)) hlxa.le
  rw [botPhi, ← hadef]
  have e2 : Real.log x ^ a * ((3 * Λ) ^ (-a) * (pfC1 q * (Kc ^ q * (cenClean q ^ q
      + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q))
      + Real.exp (-(Λ * (q * (3 - Real.exp 1) + a))
        - Real.exp 1 * q * Real.log (3 * Λ) + 0.2732 * (Real.exp 1 * q))
      + Real.exp (-(a * Λ)) * (Ec ^ q + Kc ^ q * (1 + η') ^ q
        * (TS + (Real.exp 0.2732 / (2 * Real.pi)) ^ q)))
      = Real.log x ^ a * ((3 * Λ) ^ (-a) * (pfC1 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q)))
        + Real.log x ^ a * Real.exp (-(Λ * (q * (3 - Real.exp 1) + a))
          - Real.exp 1 * q * Real.log (3 * Λ) + 0.2732 * (Real.exp 1 * q))
        + Real.log x ^ a * (Real.exp (-(a * Λ)) * (Ec ^ q + Kc ^ q * (1 + η') ^ q
          * (TS + (Real.exp 0.2732 / (2 * Real.pi)) ^ q))) := by ring
  rw [e2]
  have e3 : Real.log z ^ a * (pfC1 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc / (1000 * Real.log x ^ 2)) ^ q))
      + (Real.exp (-(q * (Real.log x / Real.log z)))
        * (Real.log z * Real.exp 0.2732) ^ (Real.exp 1 * q) + Ec ^ q)
      + Kc ^ q * (1 + η') ^ q * (∑ k ∈ Finset.range 9, w k
        + (Real.exp 0.2732 / (2 * Real.pi)) ^ q)
      = Real.log z ^ a * (pfC1 q * (Kc ^ q * (cenClean q ^ q
        + ((1 + 1 / η') / Real.pi) ^ q) + (Kc / (1000 * Real.log x ^ 2)) ^ q))
        + Real.exp (-(q * (Real.log x / Real.log z)))
          * (Real.log z * Real.exp 0.2732) ^ (Real.exp 1 * q)
        + (Ec ^ q + Kc ^ q * (1 + η') ^ q * (∑ k ∈ Finset.range 9, w k
        + (Real.exp 0.2732 / (2 * Real.pi)) ^ q)) := by ring
  rw [e3]
  linarith

set_option maxHeartbeats 400000 in
-- the bottom's cleaned bound, rewritten in the tower's scales
/-- **The bottom of the hierarchy, normalised.**  For `½ < q ≤ 1`, `η', ε > 0`, `x ≥ 3`
with `Λ = log log x ≥ 11.5`, `K_c = 2.0913(1+ε)`, `E_c = 0.0012(1+1/ε)` and a bound `TS` on the
nine top windows at every `z` with `log z ≥ 2300`:

`bottomLevel(z₀) ≤ (log x)^a·(botPhi(Λ, TS) + C_W(log z₀/log x)^a)`. -/
theorem bottomLevel_le_botPhi {q η' ε x TS : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 11.5 ≤ Real.log (Real.log x))
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS) :
    bottomLevel q 1 η' ε (3 / 2) 2 x (aboveZ x 0)
      ≤ Real.log x ^ (q * (2 * q - 1))
        * (botPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) (Real.log (Real.log x)) TS
          + winConstW q η' (2.0913 * (1 + ε))
            * (Real.log (aboveZ x 0) / Real.log x) ^ (q * (2 * q - 1))) := by
  have hΛ11 : 11 ≤ Real.log (Real.log x) := by linarith
  obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.zero_le _)
  have hL8 : ∀ k ≤ aboveDepth (Real.log (Real.log x)), 8 ≤ aboveV (Real.log (Real.log x)) k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ11 hk).1]
  obtain ⟨-, hz, -⟩ := aboveZ_facts hx3 hΛ11 hL8
  obtain ⟨hz2, -, -⟩ := hz 0 (Nat.zero_le _)
  have hlz0 : 0 < Real.log (aboveZ x 0) := by linarith
  -- `log z₀ ≥ 2300`
  have hlz2300 : 2300 ≤ Real.log (aboveZ x 0) := by
    have hx0 : 0 < x := by linarith
    have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
    have h1 := exp_ge_lin_eleven_half hΛ
    have hV0 : aboveV (Real.log (Real.log x)) 0 = 3 * Real.log (Real.log x) := aboveV_zero _
    rw [hV0] at hl1
    have hlx : Real.exp (Real.log (Real.log x)) = Real.log x := Real.exp_log hlx0
    have h2 : 2301 ≤ Real.log x / (3 * Real.log (Real.log x)) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hlog2 := Real.log_two_lt_d9
    linarith
  obtain ⟨hw0, hTail⟩ := bottomWindows_jensen_clean hq0 hq1 hz2 (by linarith)
  have h := bottomLevelW_le_botPhi hq0 hq1 hη' hε hx3 hΛ hw0 (hTS _ hlz2300) hTail
  rw [bottomLevel_eq_bottomLevelW]
  refine le_trans h (le_of_eq ?_)
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  rw [winConstW, Real.div_rpow hlz0.le hlx0.le]
  field_simp

/-- The top's constant: `pfC1^{1/(2q)}(1.001e^{10/3})^{1-q}·1.0052`. -/
noncomputable def topPhi (q : ℝ) : ℝ :=
  pfC1 q ^ (2 * q)⁻¹ * (1.001 * Real.exp (10 / 3)) ^ (1 - q) * 1.0052

/-- **The top, normalised**: for `½ ≤ q ≤ 1`, `x ≥ 3` with `Λ ≥ 11` and `L` the depth,
`pfFull(z_L)^{1/(2q)}((log x/log z_L)e^{18.0056/log z_L})^{1/2}
  ≤ (log x)^{a/(2q)}·topPhi q`. -/
lemma top_le_topPhi {q x : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hx3 : 3 ≤ x)
    (hΛ : 11 ≤ Real.log (Real.log x)) :
    pfFull q (aboveZ x (aboveDepth (Real.log (Real.log x)))) ^ (2 * q)⁻¹
        * (Real.log x / Real.log (aboveZ x (aboveDepth (Real.log (Real.log x))))
          * Real.exp (18.0056 / Real.log (aboveZ x (aboveDepth (Real.log (Real.log x))))))
          ^ (2 : ℝ)⁻¹
      ≤ (Real.log x ^ (q * (2 * q - 1))) ^ (2 * q)⁻¹ * topPhi q := by
  set Λ := Real.log (Real.log x) with hΛdef
  set L := aboveDepth Λ with hLdef
  set a := q * (2 * q - 1) with hadef
  set P := (2 * q)⁻¹ with hPdef
  have hq0' : (0 : ℝ) < q := by linarith
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have ha : 0 ≤ a := mul_nonneg hq0'.le (by linarith)
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨hVL, -, hl1, hl2, hlz, -⟩ := aboveZ_log_facts hx3 hΛ (le_refl L)
  obtain ⟨hstop, -⟩ := aboveDepth_spec (by linarith : 10 ≤ 3 * Λ)
  rw [← hLdef] at hstop
  set z := aboveZ x L with hzdef
  set V := aboveV Λ L with hVdef
  have hV0 : 0 < V := by linarith
  have hlog2 := Real.log_two_lt_d9
  have hlz0 : 0 < Real.log z := by linarith
  have hVe : V < Real.exp (10 / 3) := by
    have : Real.log V < 10 / 3 := by linarith
    calc V = Real.exp (Real.log V) := (Real.exp_log hV0).symm
      _ < Real.exp (10 / 3) := Real.exp_lt_exp.2 this
  -- `log x/log z ≤ 1.001 V`
  have hratio : Real.log x / Real.log z ≤ 1.001 * V := by
    rw [div_le_iff₀ hlz0]
    have h1 : Real.log x / V ≤ 1.001 * Real.log z := by
      have : Real.log 2 ≤ 0.001 * (Real.log x / V - Real.log 2) := by linarith
      linarith
    rw [div_le_iff₀ hV0] at h1
    linarith
  have hratio1 : 1 ≤ Real.log x / Real.log z := by
    rw [le_div_iff₀ hlz0, one_mul]
    have := div_le_self hlx0.le (show (1 : ℝ) ≤ V by linarith)
    linarith
  have hPF := pfFull_le_pfC1 hq0 (y := z) (by linarith)
  have hPF0 : 0 ≤ pfFull q z := by rw [pfFull]; positivity
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  -- the factors
  have h1 : pfFull q z ^ P ≤ Real.log z ^ (a * P) * pfC1 q ^ P := by
    calc pfFull q z ^ P ≤ (Real.log z ^ a * pfC1 q) ^ P := Real.rpow_le_rpow hPF0 hPF hP0.le
      _ = Real.log z ^ (a * P) * pfC1 q ^ P := by
          rw [Real.mul_rpow (Real.rpow_nonneg hlz0.le _) hc1, ← Real.rpow_mul hlz0.le]
  have h2 : (Real.log x / Real.log z * Real.exp (18.0056 / Real.log z)) ^ (2 : ℝ)⁻¹
      ≤ (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹ * 1.0052 := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
    rw [← Real.exp_mul]
    have h3 : 18.0056 / Real.log z * (2 : ℝ)⁻¹ ≤ 0.00501 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hlz0]; norm_num; linarith
    refine le_trans (Real.exp_le_exp.2 h3) ?_
    have := Real.exp_bound_div_one_sub_of_interval (x := 0.00501) (by norm_num) (by norm_num)
    refine le_trans this ?_
    norm_num
  -- `log z^{aP}(log x/log z)^{1/2} = (log x)^{aP}(log x/log z)^{1-q}`
  have haP : a * P = 1 / 2 - (1 - q) := by
    rw [hadef, hPdef]; field_simp; ring
  have h4 : Real.log z ^ (a * P) * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹
      = Real.log x ^ (a * P) * (Real.log x / Real.log z) ^ (1 - q) := by
    have hr : 0 < Real.log x / Real.log z := by positivity
    have e1 : Real.log z = Real.log x / (Real.log x / Real.log z) := by field_simp
    have e2 : Real.log z ^ (a * P)
        = Real.log x ^ (a * P) * (Real.log x / Real.log z) ^ (-(a * P)) := by
      nth_rewrite 1 [e1]
      rw [Real.div_rpow hlx0.le hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le]
    rw [e2, mul_assoc, ← Real.rpow_add hr, haP]
    congr 2
    ring
  have h5 : (Real.log x / Real.log z) ^ (1 - q) ≤ (1.001 * Real.exp (10 / 3)) ^ (1 - q) :=
    Real.rpow_le_rpow (by linarith) (by nlinarith) (by linarith)
  have hlxa : (Real.log x ^ a) ^ P = Real.log x ^ (a * P) := by
    rw [← Real.rpow_mul hlx0.le]
  rw [hlxa, topPhi]
  calc pfFull q z ^ P * (Real.log x / Real.log z * Real.exp (18.0056 / Real.log z)) ^ (2 : ℝ)⁻¹
      ≤ (Real.log z ^ (a * P) * pfC1 q ^ P) * ((Real.log x / Real.log z) ^ (2 : ℝ)⁻¹ * 1.0052) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = pfC1 q ^ P * (Real.log z ^ (a * P) * (Real.log x / Real.log z) ^ (2 : ℝ)⁻¹) * 1.0052 := by
        ring
    _ = pfC1 q ^ P * (Real.log x ^ (a * P) * (Real.log x / Real.log z) ^ (1 - q)) * 1.0052 := by
        rw [h4]
    _ ≤ pfC1 q ^ P * (Real.log x ^ (a * P) * (1.001 * Real.exp (10 / 3)) ^ (1 - q)) * 1.0052 := by
        gcongr
    _ = Real.log x ^ (a * P) * (pfC1 q ^ P * (1.001 * Real.exp (10 / 3)) ^ (1 - q) * 1.0052) := by
        ring

/-- **The deep bands**: if `g ℓ ≤ c V_{ℓ+1}^{-γ}` for `ℓ < L - 4`, then
`∑_{ℓ<L-4} g ℓ ≤ c r_4^{-γ}/(1 - 2^{-γ})`. -/
lemma sum_tower_deep_le {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) {g : ℕ → ℝ} {c γ : ℝ} (hc : 0 ≤ c)
    (hγ : 0 < γ) (hg : ∀ ℓ < aboveDepth Λ - 4, g ℓ ≤ c * aboveV Λ (ℓ + 1) ^ (-γ)) :
    ∑ ℓ ∈ Finset.range (aboveDepth Λ - 4), g ℓ
      ≤ c * towerR 4 ^ (-γ) / (1 - (2 : ℝ) ^ (-γ)) := by
  set L := aboveDepth Λ with hLdef
  have h1 : ∑ ℓ ∈ Finset.range (L - 4), g ℓ
      ≤ ∑ ℓ ∈ Finset.range (L - 4), c * towerR (4 + (L - 4 - 1 - ℓ)) ^ (-γ) := by
    refine Finset.sum_le_sum fun ℓ hℓ => le_trans (hg ℓ (Finset.mem_range.1 hℓ)) ?_
    have hℓL := Finset.mem_range.1 hℓ
    have hge := aboveV_ge_towerR hΛ (j := L - 1 - ℓ) (by omega)
    rw [← hLdef, show L - (L - 1 - ℓ) = ℓ + 1 by omega] at hge
    rw [show 4 + (L - 4 - 1 - ℓ) = L - 1 - ℓ by omega]
    have hr0 : 0 < towerR (L - 1 - ℓ) := by linarith [towerR_ten_le (L - 1 - ℓ)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr0 hge (by linarith)) hc
  have h2 : ∑ ℓ ∈ Finset.range (L - 4), c * towerR (4 + (L - 4 - 1 - ℓ)) ^ (-γ)
      = ∑ i ∈ Finset.range (L - 4), c * towerR (4 + i) ^ (-γ) :=
    Finset.sum_range_reflect (fun i => c * towerR (4 + i) ^ (-γ)) (L - 4)
  have h3 : ∑ i ∈ Finset.range (L - 4), c * towerR (4 + i) ^ (-γ)
      = ∑ j ∈ Finset.Ico 4 (4 + (L - 4)), c * towerR j ^ (-γ) := by
    rw [Finset.sum_Ico_eq_sum_range, show 4 + (L - 4) - 4 = L - 4 by omega]
  rw [h2, h3] at h1
  exact le_trans h1 (sum_Ico_towerR_rpow_le hc hγ _)

/-- The Jensen regime's total: `topPhi + ∑_{j<4} bandPhi(r_j)^p + C_b^p r_4^{-ap}/(1-2^{-ap})
+ botPhi^p + 5^{1-p}(C_W 10^{-a})^p + C_W^p r_4^{-ap}/(1-2^{-ap})`, `p = 1/(2q)`,
`K_c = 2.0913(1+ε)`, `E_c = 0.0012(1+1/ε)`, `C_b` the constant of `RMF.bandPhi_le_rpow`. -/
noncomputable def aboveTowerF (q η' ε Λ TS : ℝ) : ℝ :=
  topPhi q
  + ∑ j ∈ Finset.range 4,
      bandPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) (towerR j) ^ (2 * q)⁻¹
  + (pfC2 q * ((2.0913 * (1 + ε)) ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
        + (2.0913 * (1 + ε) * 4e-13) ^ q)
      + pfC1 q * ((2.0913 * (1 + ε)) ^ q * (1 + η') ^ q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) + (0.0012 * (1 + 1 / ε)) ^ q)
      + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)) ^ (2 * q)⁻¹
    * towerR 4 ^ (-(q * (2 * q - 1) * (2 * q)⁻¹))
    / (1 - (2 : ℝ) ^ (-(q * (2 * q - 1) * (2 * q)⁻¹)))
  + botPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) Λ TS ^ (2 * q)⁻¹
  + 5 ^ (1 - (2 * q)⁻¹)
    * (winConstW q η' (2.0913 * (1 + ε)) * 10 ^ (-(q * (2 * q - 1)))) ^ (2 * q)⁻¹
  + winConstW q η' (2.0913 * (1 + ε)) ^ (2 * q)⁻¹
    * towerR 4 ^ (-(q * (2 * q - 1) * (2 * q)⁻¹))
    / (1 - (2 : ℝ) ^ (-(q * (2 * q - 1) * (2 * q)⁻¹)))

lemma botPhi_nonneg {q η' Kc Ec Λ TS : ℝ} (hq1 : q ≤ 1) (hη' : 0 < η') (hKc : 0 ≤ Kc)
    (hEc : 0 ≤ Ec) (hΛ : 0 < Λ) (hTS : 0 ≤ TS) : 0 ≤ botPhi q η' Kc Ec Λ TS := by
  rw [botPhi]
  have : 0 ≤ cenClean q ^ q := Real.rpow_nonneg (cenClean_nonneg hq1) _
  have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc _
  have : 0 ≤ ((1 + 1 / η') / Real.pi) ^ q := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ (Kc * 4e-13) ^ q := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ Ec ^ q := Real.rpow_nonneg hEc _
  have : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
  have : 0 ≤ (Real.exp 0.2732 / (2 * Real.pi)) ^ q := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ (3 * Λ) ^ (-(q * (2 * q - 1))) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ pfC1 q := (Real.exp_pos _).le
  positivity

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
-- the hierarchy, the cleaned levels, the tower sums and the windows' Hölder in one proof
/-- **The Jensen regime above `½`.**  For `½ < q ≤ 1`, `η', ε > 0`, `x ≥ 3` with
`Λ = log log x ≥ 11.5` and a bound `TS` on the bottom's nine top windows at every `z` with
`log z ≥ 2300`:

`E|S(x)|^{2q} ≤ (log x)^{q(2q-1)}·RMF.aboveTowerF q η' ε Λ TS^{2q}`:

the hierarchy (`RMF.rpow_inv_integral_rpow_weightedRademacherSum_le_aboveHierarchy`) at the
depth `RMF.aboveDepth Λ`, the normalised levels (`RMF.pfFull_mul_bandLevel_le_bandPhi`,
`RMF.bottomLevel_le_botPhi`, `RMF.top_le_topPhi`), the bands' overheads summed along the tower
(`RMF.sum_tower_le`), and the windows telescoped, the deep ones summed
(`RMF.sum_tower_deep_le`) and the last four with the bottom by the power mean
(`RMF.sum_rpow_le_card_rpow`). -/
theorem integral_rpow_weightedRademacherSum_le_aboveTower {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q η' ε x TS : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 11.5 ≤ Real.log (Real.log x))
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ Real.log x ^ (q * (2 * q - 1))
        * aboveTowerF q η' ε (Real.log (Real.log x)) TS ^ (2 * q) := by
  haveI := hX.isProbabilityMeasure
  set Λ := Real.log (Real.log x) with hΛdef
  set L := aboveDepth Λ with hLdef
  set a := q * (2 * q - 1) with hadef
  set P := (2 * q)⁻¹ with hPdef
  set Kc := 2.0913 * (1 + ε) with hKcdef
  set Ec := 0.0012 * (1 + 1 / ε) with hEcdef
  set C := winConstW q η' Kc with hCdef
  have hq0' : (0 : ℝ) < q := by linarith
  have ha0 : 0 < a := mul_pos hq0' (by linarith)
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have hP1 : P ≤ 1 := by rw [hPdef, inv_le_one₀ (by positivity)]; linarith
  have haP : 0 < a * P := mul_pos ha0 hP0
  have hKc0 : 0 ≤ Kc := by positivity
  have hEc0 : 0 ≤ Ec := by positivity
  have hC0 : 0 ≤ C := winConstW_nonneg hq0 hq1 hη' hKc0
  have hΛ11 : 11 ≤ Λ := by linarith
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hL8 : ∀ ℓ ≤ L, 8 ≤ aboveV Λ ℓ :=
    fun ℓ hℓ => by linarith [(aboveZ_log_facts hx3 hΛ11 hℓ).1]
  obtain ⟨hlx1, hz, hmono⟩ := aboveZ_facts hx3 hΛ11 hL8
  -- the scales' logarithms, normalised
  set u : ℕ → ℝ := fun ℓ => (Real.log (aboveZ x ℓ) / Real.log x) ^ a with hudef
  have hlz0 : ∀ ℓ ≤ L, 0 < Real.log (aboveZ x ℓ) := fun ℓ hℓ => by
    obtain ⟨-, -, hl1, -, hlz, -⟩ := aboveZ_log_facts hx3 hΛ11 hℓ
    linarith
  have hu_mono : ∀ ℓ ℓ', ℓ ≤ ℓ' → ℓ' ≤ L → u ℓ ≤ u ℓ' := by
    intro ℓ ℓ' hle hℓ'
    induction ℓ' with
    | zero =>
      rw [Nat.le_zero.1 hle]
    | succ n ih =>
      rcases Nat.lt_or_ge ℓ (n + 1) with h | h
      · refine le_trans (ih (by omega) (by omega)) ?_
        have hzz : (aboveZ x n : ℝ) ≤ aboveZ x (n + 1) := by exact_mod_cast hmono n (by omega)
        refine Real.rpow_le_rpow (div_nonneg (hlz0 n (by omega)).le hlx0.le)
          (div_le_div_of_nonneg_right (Real.log_le_log (by
            have := (hz n (by omega)).1
            have : (2 : ℝ) ≤ aboveZ x n := by exact_mod_cast this
            linarith) hzz) hlx0.le) ha0.le
      · rw [show ℓ = n + 1 by omega]
  have hu_le : ∀ ℓ ≤ L, u ℓ ≤ aboveV Λ ℓ ^ (-a) := by
    intro ℓ hℓ
    obtain ⟨hV, -, -, hl2, -, -⟩ := aboveZ_log_facts hx3 hΛ11 hℓ
    have hV0 : 0 < aboveV Λ ℓ := by linarith
    change (Real.log (aboveZ x ℓ) / Real.log x) ^ a ≤ aboveV Λ ℓ ^ (-a)
    rw [Real.rpow_neg hV0.le, ← Real.inv_rpow hV0.le]
    refine Real.rpow_le_rpow (div_nonneg (hlz0 ℓ hℓ).le hlx0.le) ?_ ha0.le
    rw [div_le_iff₀ hlx0, inv_mul_eq_div]
    exact hl2
  have hu0 : ∀ ℓ, 0 ≤ u ℓ := fun ℓ => by
    change 0 ≤ (Real.log (aboveZ x ℓ) / Real.log x) ^ a
    exact Real.rpow_nonneg (div_nonneg (Real.log_natCast_nonneg _) hlx0.le) _
  have hlxP : 0 ≤ (Real.log x ^ a) ^ P := Real.rpow_nonneg (Real.rpow_nonneg hlx0.le _) _
  -- the hierarchy
  have hier := rpow_inv_integral_rpow_weightedRademacherSum_le_aboveHierarchy hX
    (θ := 1) (cs := 3 / 2) (Tm := 2) (L := L) hq0.le hq1 one_pos hη' hε hx3 hΛ11 hL8
  rw [← hPdef] at hier
  -- the top
  have htop := top_le_topPhi hq0.le hq1 hx3 hΛ11
  rw [← hLdef, ← hadef, ← hPdef] at htop
  -- the bands
  have hband : ∀ ℓ < L, (pfFull q (aboveZ x ℓ)
      * bandLevel q 1 η' ε (3 / 2) x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ P
      ≤ (Real.log x ^ a) ^ P * (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) ^ P
        + (C * (u (ℓ + 1) - u ℓ)) ^ P) := by
    intro ℓ hℓ
    have h := pfFull_mul_bandLevel_le_bandPhi hq0 hq1 hη' hε hx3 hΛ11 hℓ
    rw [← hadef, ← hKcdef, ← hEcdef, ← hCdef] at h
    obtain ⟨hy2, -, -⟩ := hz ℓ hℓ.le
    obtain ⟨-, hzx, hz'⟩ := hz (ℓ + 1) hℓ
    have hlev := integral_rpow_norm_blockTruncationTail_le_bandLevel hX (cs := 3 / 2)
      hq0.le hq1 one_pos hη' hε hy2 (hmono ℓ hℓ) hzx hlx1 hz'
    have hlev0 : 0 ≤ bandLevel q 1 η' ε (3 / 2) x (aboveZ x ℓ) (aboveZ x (ℓ + 1)) :=
      le_trans (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hlev
    have hpf0 : 0 ≤ pfFull q (aboveZ x ℓ) := by rw [pfFull]; positivity
    have hb0 : 0 ≤ bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) :=
      (bandPhi_antitoneOn hq0 hq1 hη' hKc0 hEc0).2 _ (aboveZ_log_facts hx3 hΛ11
        (Nat.succ_le_of_lt hℓ)).1
    have hw0 : 0 ≤ C * (u (ℓ + 1) - u ℓ) :=
      mul_nonneg hC0 (sub_nonneg.2 (hu_mono ℓ (ℓ + 1) (by omega) (by omega)))
    calc (pfFull q (aboveZ x ℓ) * bandLevel q 1 η' ε (3 / 2) x (aboveZ x ℓ)
          (aboveZ x (ℓ + 1))) ^ P
        ≤ (Real.log x ^ a * (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C * (u (ℓ + 1) - u ℓ))) ^ P :=
          Real.rpow_le_rpow (mul_nonneg hpf0 hlev0) h hP0.le
      _ = (Real.log x ^ a) ^ P * (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C * (u (ℓ + 1) - u ℓ)) ^ P :=
          Real.mul_rpow (Real.rpow_nonneg hlx0.le _) (add_nonneg hb0 hw0)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow hb0 hw0 hP0.le hP1) hlxP
  have hbands : ∑ ℓ ∈ Finset.range L, (pfFull q (aboveZ x ℓ)
      * bandLevel q 1 η' ε (3 / 2) x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ P
      ≤ (Real.log x ^ a) ^ P * (∑ ℓ ∈ Finset.range L, bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) ^ P
        + ∑ ℓ ∈ Finset.range L, (C * (u (ℓ + 1) - u ℓ)) ^ P) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ hℓ => hband ℓ (Finset.mem_range.1 hℓ)
  -- the bands' overheads along the tower
  set Cb := pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q)
      + (Kc * 4e-13) ^ q)
    + pfC1 q * (Kc ^ q * (1 + η') ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
      + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q)
    + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q) with hCbdef
  have hCb0 : 0 ≤ Cb := by
    have h := bandPhi_le_rpow hq0 hq1 hη' hKc0 hEc0 (le_refl (10 : ℝ))
    have h0 := (bandPhi_antitoneOn hq0 hq1 hη' hKc0 hEc0).2 10 le_rfl
    rw [← hCbdef] at h
    have h10 : 0 < (10 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    push Not at hneg
    have : Cb * (10 : ℝ) ^ (-a) < 0 := mul_neg_of_neg_of_pos hneg h10
    linarith
  obtain ⟨hanti, hnn⟩ := bandPhi_antitoneOn hq0 hq1 hη' hKc0 hEc0
  have hover := sum_tower_le (by linarith : 10 ≤ 3 * Λ)
    (g := fun ℓ => bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) ^ P)
    (Φ := fun s => bandPhi q η' Kc Ec s ^ P)
    (fun s hs t ht hst => Real.rpow_le_rpow (hnn t ht) (hanti hs ht hst) hP0.le)
    (fun s hs => Real.rpow_nonneg (hnn s hs) _) (fun ℓ _ => le_rfl)
    (c := Cb ^ P) (γ := a * P) (Real.rpow_nonneg hCb0 _) haP
    (fun s hs => by
      have hs10 : 10 ≤ s := le_trans (towerR_ten_le 4) hs
      have h := bandPhi_le_rpow hq0 hq1 hη' hKc0 hEc0 hs10
      rw [← hCbdef, ← hadef] at h
      calc bandPhi q η' Kc Ec s ^ P ≤ (Cb * s ^ (-a)) ^ P :=
            Real.rpow_le_rpow (hnn s hs10) h hP0.le
        _ = Cb ^ P * s ^ (-(a * P)) := by
            rw [Real.mul_rpow hCb0 (Real.rpow_nonneg (by linarith) _),
              ← Real.rpow_mul (by linarith)]
            ring_nf)
  -- the bottom
  have hbot := bottomLevel_le_botPhi hq0 hq1 hη' hε hx3 hΛ hTS
  rw [← hadef, ← hKcdef, ← hEcdef, ← hCdef] at hbot
  have hTS0 : 0 ≤ TS := by
    have hlz2300 : 2300 ≤ Real.log (aboveZ x 0) := by
      have h1 := exp_ge_lin_eleven_half hΛ
      obtain ⟨-, -, hl1, -, -, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.zero_le L)
      rw [aboveV_zero] at hl1
      have hlx : Real.log x = Real.exp Λ := by rw [hΛdef, Real.exp_log hlx0]
      have h2 : 2301 ≤ Real.log x / (3 * Λ) := by
        rw [le_div_iff₀ (by positivity), hlx]; linarith
      linarith [Real.log_two_lt_d9]
    refine le_trans ?_ (hTS _ hlz2300)
    rw [botTopSum]
    refine Finset.sum_nonneg fun k _ => le_min ?_ ?_
    · rw [winNoSplitFull]
      exact Real.rpow_nonneg (by
        have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have hT0 : 0 ≤ bottomT 1 2 (aboveZ x 0) k := by rw [bottomT]; positivity
        have hmF0 : 0 ≤ mFull (aboveZ x 0) := by
          rw [mFull]; have := hlz0 0 (Nat.zero_le _); positivity
        have := hlz0 0 (Nat.zero_le _)
        positivity) _
    · rw [winSplitFull, pfFull]
      have : 0 ≤ taylorWindowW (2 * (1 - q) * (Real.log ((splitPt (3 / 2)
          (bottomT 1 2 (aboveZ x 0) k) 2 (aboveZ x 0) + 1 : ℕ) : ℝ) ^ 2 / 2
          + 15.003 * Real.log ((splitPt (3 / 2) (bottomT 1 2 (aboveZ x 0) k) 2 (aboveZ x 0)
          + 1 : ℕ) : ℝ) + 34) * bottomT 1 2 (aboveZ x 0) k ^ 2) := by
        refine taylorWindowW_nonneg ?_
        have : 0 ≤ Real.log ((splitPt (3 / 2) (bottomT 1 2 (aboveZ x 0) k) 2 (aboveZ x 0)
          + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
        have : 0 ≤ 1 - q := by linarith
        positivity
      have : 0 ≤ mBand (splitPt (3 / 2) (bottomT 1 2 (aboveZ x 0) k) 2 (aboveZ x 0))
          (aboveZ x 0) := by rw [mBand]; positivity
      have : 0 ≤ bottomT 1 2 (aboveZ x 0) k := by rw [bottomT]; positivity
      have : 0 ≤ Real.log (splitPt (3 / 2) (bottomT 1 2 (aboveZ x 0) k) 2 (aboveZ x 0) : ℝ) :=
        Real.log_natCast_nonneg _
      positivity
  have hbot0 : 0 ≤ botPhi q η' Kc Ec Λ TS :=
    botPhi_nonneg hq1 hη' hKc0 hEc0 (by linarith) hTS0
  have hbotP : bottomLevel q 1 η' ε (3 / 2) 2 x (aboveZ x 0) ^ P
      ≤ (Real.log x ^ a) ^ P * (botPhi q η' Kc Ec Λ TS ^ P + (C * u 0) ^ P) := by
    obtain ⟨hz2, hzx, hz'⟩ := hz 0 (Nat.zero_le L)
    have hlev := integral_rpow_norm_truncationTail_le_bottomLevel hX (cs := 3 / 2) (Tm := 2)
      hq0.le hq1 one_pos hη' hε hz2 hzx hlx1 hz'
    have hlev0 : 0 ≤ bottomLevel q 1 η' ε (3 / 2) 2 x (aboveZ x 0) :=
      le_trans (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hlev
    have hw0 : 0 ≤ C * u 0 := mul_nonneg hC0 (hu0 0)
    calc bottomLevel q 1 η' ε (3 / 2) 2 x (aboveZ x 0) ^ P
        ≤ (Real.log x ^ a * (botPhi q η' Kc Ec Λ TS + C * u 0)) ^ P :=
          Real.rpow_le_rpow hlev0 hbot hP0.le
      _ = (Real.log x ^ a) ^ P * (botPhi q η' Kc Ec Λ TS + C * u 0) ^ P :=
          Real.mul_rpow (Real.rpow_nonneg hlx0.le _) (add_nonneg hbot0 hw0)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow hbot0 hw0 hP0.le hP1) hlxP
  -- the windows
  have hwin : ∑ ℓ ∈ Finset.range L, (C * (u (ℓ + 1) - u ℓ)) ^ P + (C * u 0) ^ P
      ≤ 5 ^ (1 - P) * (C * 10 ^ (-a)) ^ P
        + C ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))) := by
    have hsplit := (Finset.sum_range_add_sum_Ico (fun ℓ => (C * (u (ℓ + 1) - u ℓ)) ^ P)
      (Nat.sub_le L 4)).symm
    rw [hsplit]
    -- the deep windows
    have hdeep : ∑ ℓ ∈ Finset.range (L - 4), (C * (u (ℓ + 1) - u ℓ)) ^ P
        ≤ C ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))) := by
      refine sum_tower_deep_le (by linarith : 10 ≤ 3 * Λ) (Real.rpow_nonneg hC0 _) haP
        fun ℓ hℓ => ?_
      have hℓL : ℓ + 1 ≤ L := by omega
      have hV := (aboveZ_log_facts hx3 hΛ11 hℓL).1
      have hw0 : 0 ≤ C * (u (ℓ + 1) - u ℓ) :=
        mul_nonneg hC0 (sub_nonneg.2 (hu_mono ℓ (ℓ + 1) (by omega) hℓL))
      calc (C * (u (ℓ + 1) - u ℓ)) ^ P ≤ (C * aboveV Λ (ℓ + 1) ^ (-a)) ^ P := by
            refine Real.rpow_le_rpow hw0 (mul_le_mul_of_nonneg_left ?_ hC0) hP0.le
            linarith [hu0 ℓ, hu_le (ℓ + 1) hℓL]
        _ = C ^ P * aboveV Λ (ℓ + 1) ^ (-(a * P)) := by
            rw [Real.mul_rpow hC0 (Real.rpow_nonneg (by linarith) _),
              ← Real.rpow_mul (by linarith)]
            ring_nf
    -- the last four with the bottom
    set f : ℕ → ℝ := fun ℓ => if ℓ < L then C * (u (ℓ + 1) - u ℓ) else C * u 0 with hfdef
    have hf0 : ∀ ℓ ∈ Finset.Ico (L - 4) (L + 1), 0 ≤ f ℓ := by
      intro ℓ hℓ
      simp only [hfdef]
      split_ifs with h
      · exact mul_nonneg hC0 (sub_nonneg.2 (hu_mono ℓ (ℓ + 1) (by omega) (by omega)))
      · exact mul_nonneg hC0 (hu0 0)
    have hshallow : ∑ ℓ ∈ Finset.Ico (L - 4) L, (C * (u (ℓ + 1) - u ℓ)) ^ P + (C * u 0) ^ P
        = ∑ ℓ ∈ Finset.Ico (L - 4) (L + 1), f ℓ ^ P := by
      rw [Finset.sum_Ico_succ_top (Nat.sub_le L 4)]
      congr 1
      · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        simp only [hfdef, if_pos (Finset.mem_Ico.1 hℓ).2]
      · simp only [hfdef, if_neg (lt_irrefl L)]
    have hcard : ((Finset.Ico (L - 4) (L + 1)).card : ℝ) ≤ 5 := by
      rw [Nat.card_Ico]
      exact_mod_cast (by omega : L + 1 - (L - 4) ≤ 5)
    have hpm := sum_rpow_le_card_rpow (Finset.Ico (L - 4) (L + 1)) hf0 hP0 hP1 hcard
    have hsumf : ∑ ℓ ∈ Finset.Ico (L - 4) (L + 1), f ℓ ≤ C * 10 ^ (-a) := by
      rw [Finset.sum_Ico_succ_top (Nat.sub_le L 4)]
      have h1 : ∑ ℓ ∈ Finset.Ico (L - 4) L, f ℓ = C * (u L - u (L - 4)) := by
        have : ∀ ℓ ∈ Finset.Ico (L - 4) L, f ℓ = C * (u (ℓ + 1) - u ℓ) := fun ℓ hℓ => by
          simp only [hfdef, if_pos (Finset.mem_Ico.1 hℓ).2]
        rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_Ico_sub u (Nat.sub_le L 4)]
      have h2 : f L = C * u 0 := by simp only [hfdef, if_neg (lt_irrefl L)]
      rw [h1, h2]
      have h3 : u 0 ≤ u (L - 4) := hu_mono 0 (L - 4) (Nat.zero_le _) (Nat.sub_le L 4)
      have h4 : u L ≤ 10 ^ (-a) := by
        refine le_trans (hu_le L le_rfl) ?_
        have hV := (aboveZ_log_facts hx3 hΛ11 (le_refl L)).1
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hV (by linarith)
      have h5 := mul_le_mul_of_nonneg_left h3 hC0
      have h6 := mul_le_mul_of_nonneg_left h4 hC0
      linarith
    have hsum0 : 0 ≤ ∑ ℓ ∈ Finset.Ico (L - 4) (L + 1), f ℓ := Finset.sum_nonneg hf0
    have hlast : ∑ ℓ ∈ Finset.Ico (L - 4) (L + 1), f ℓ ^ P ≤ 5 ^ (1 - P) * (C * 10 ^ (-a)) ^ P :=
      le_trans hpm (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsum0 hsumf hP0.le)
        (Real.rpow_nonneg (by norm_num) _))
    linarith
  -- assemble the norm
  have hnorm : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ) ^ P ≤ (Real.log x ^ a) ^ P * aboveTowerF q η' ε Λ TS := by
    refine le_trans hier ?_
    have hF : aboveTowerF q η' ε Λ TS = topPhi q
        + ∑ j ∈ Finset.range 4, bandPhi q η' Kc Ec (towerR j) ^ P
        + Cb ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))
        + botPhi q η' Kc Ec Λ TS ^ P
        + 5 ^ (1 - P) * (C * 10 ^ (-a)) ^ P
        + C ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))) := by
      rw [aboveTowerF]
    rw [hF]
    have e1 : (Real.log x ^ a) ^ P * (topPhi q
        + ∑ j ∈ Finset.range 4, bandPhi q η' Kc Ec (towerR j) ^ P
        + Cb ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P)))
        + botPhi q η' Kc Ec Λ TS ^ P
        + 5 ^ (1 - P) * (C * 10 ^ (-a)) ^ P
        + C ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))))
        = (Real.log x ^ a) ^ P * topPhi q
          + (Real.log x ^ a) ^ P * ((∑ j ∈ Finset.range 4, bandPhi q η' Kc Ec (towerR j) ^ P
            + Cb ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))))
            + (5 ^ (1 - P) * (C * 10 ^ (-a)) ^ P
            + C ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))))
            + botPhi q η' Kc Ec Λ TS ^ P) := by ring
    rw [e1]
    have hmid := add_le_add (add_le_add hover hwin) (le_refl (botPhi q η' Kc Ec Λ TS ^ P))
    have hmid' := mul_le_mul_of_nonneg_left hmid hlxP
    have htot : ∑ ℓ ∈ Finset.range L, (pfFull q (aboveZ x ℓ)
        * bandLevel q 1 η' ε (3 / 2) x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ P
        + bottomLevel q 1 η' ε (3 / 2) 2 x (aboveZ x 0) ^ P
        ≤ (Real.log x ^ a) ^ P * ((∑ ℓ ∈ Finset.range L,
            bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) ^ P
          + (∑ ℓ ∈ Finset.range L, (C * (u (ℓ + 1) - u ℓ)) ^ P + (C * u 0) ^ P))
          + botPhi q η' Kc Ec Λ TS ^ P) := by
      have := add_le_add hbands hbotP
      refine le_trans this (le_of_eq ?_)
      ring
    have hS : (∑ ℓ ∈ Finset.range L, bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) ^ P
          + (∑ ℓ ∈ Finset.range L, (C * (u (ℓ + 1) - u ℓ)) ^ P + (C * u 0) ^ P))
          + botPhi q η' Kc Ec Λ TS ^ P
        ≤ (∑ j ∈ Finset.range 4, bandPhi q η' Kc Ec (towerR j) ^ P
            + Cb ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))))
          + (5 ^ (1 - P) * (C * 10 ^ (-a)) ^ P
            + C ^ P * towerR 4 ^ (-(a * P)) / (1 - (2 : ℝ) ^ (-(a * P))))
          + botPhi q η' Kc Ec Λ TS ^ P := hmid
    have hS' := mul_le_mul_of_nonneg_left hS hlxP
    linarith
  -- raise to `2q`
  have hint0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hF0 : 0 ≤ (Real.log x ^ a) ^ P * aboveTowerF q η' ε Λ TS :=
    le_trans (Real.rpow_nonneg hint0 _) hnorm
  have h2q : 0 < 2 * q := by linarith
  calc (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ)
      = ((∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ) ^ P) ^ (2 * q) := by
        rw [← Real.rpow_mul hint0, hPdef, inv_mul_cancel₀ h2q.ne', Real.rpow_one]
    _ ≤ ((Real.log x ^ a) ^ P * aboveTowerF q η' ε Λ TS) ^ (2 * q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hint0 _) hnorm h2q.le
    _ = Real.log x ^ a * aboveTowerF q η' ε Λ TS ^ (2 * q) := by
        have hFt : 0 ≤ aboveTowerF q η' ε Λ TS := by
          by_contra hneg
          push Not at hneg
          have hl : 0 < (Real.log x ^ a) ^ P :=
            Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hlx0 _) _
          have : (Real.log x ^ a) ^ P * aboveTowerF q η' ε Λ TS < 0 := mul_neg_of_pos_of_neg hl hneg
          linarith
        rw [Real.mul_rpow hlxP hFt, ← Real.rpow_mul (Real.rpow_nonneg hlx0.le _), hPdef,
          inv_mul_cancel₀ h2q.ne', Real.rpow_one]

end RMF
