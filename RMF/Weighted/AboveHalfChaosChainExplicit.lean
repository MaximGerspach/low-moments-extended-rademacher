/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfChaosTowerExplicit
import RMF.Weighted.AboveHalfChaosSumsExplicit

/-!
# The chaos windows along the tower above `q = ½`

The chaos factor of an eligible window is at most the profile `RMF.chaosProf (RMF.chaosAhat q)`, so
a band's windows sum to at most `RMF.profSum` (`RMF.chaosWinSum_le_profSum`).  The levels' powers
`1/(2q)` are summed by Hölder against the weights `V^{-1/1000}` (`RMF.sum_rpow_le_weighted`), and
along the tower the counts of levels below a height are logarithmic
(`RMF.depth_sub_le_of_log_lt`).
-/

open MeasureTheory

namespace RMF

/-! ### The profile of the chaos factor -/

/-- The chaos profile's constant at `q`: `RMF.chaosAbove q·(1-q)^{-q}`. -/
noncomputable def chaosAhat (q : ℝ) : ℝ := chaosAbove q * (1 - q) ^ (-q)

lemma chaosAhat_nonneg {q : ℝ} (hq1 : q < 1) : 0 ≤ chaosAhat q :=
  mul_nonneg (chaosAbove_nonneg q) (Real.rpow_nonneg (by linarith) _)

/-- **An eligible window's chaos factor is at most the profile**: for `½ ≤ q < 1`, the chaos
factor `min 1 (A(1 + (1-q)√n)^{-q})`, `n = m - 8 ≥ 2000`, is at most
`min 1 (A(1-q)^{-q}n^{-1/4})`. -/
lemma chaosMult_le_chaosProf {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1) {m z : ℕ}
    (hel : 2008 ≤ m → (m : ℝ) + 97 ≤ Real.log (Real.log z)) :
    chaosMult q m z ≤ chaosProf (chaosAhat q) m := by
  rw [chaosMult, chaosProf]
  by_cases hm : 2008 ≤ m
  · rw [if_pos ⟨hm, hel hm⟩, if_pos hm]
    refine min_le_min le_rfl ?_
    have h1q : 0 < 1 - q := by linarith
    have hn1 : (1 : ℝ) ≤ ((m - 8 : ℕ) : ℝ) := by
      have : 1 ≤ m - 8 := by omega
      exact_mod_cast this
    set n : ℝ := ((m - 8 : ℕ) : ℝ) with hndef
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    have hA0 := chaosAbove_nonneg q
    calc chaosAbove q * (1 + (1 - q) * Real.sqrt n) ^ (-q)
        ≤ chaosAbove q * ((1 - q) * Real.sqrt n) ^ (-q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
            (by linarith) (by linarith)) hA0
      _ = chaosAbove q * ((1 - q) ^ (-q) * Real.sqrt n ^ (-q)) := by
          rw [Real.mul_rpow h1q.le hsq.le]
      _ ≤ chaosAbove q * ((1 - q) ^ (-q) * n ^ (-(1 / 4 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
            (Real.rpow_nonneg h1q.le _)) hA0
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = chaosAhat q * n ^ (-(1 / 4 : ℝ)) := by rw [chaosAhat]; ring
  · rw [if_neg (fun h => hm h.1), if_neg hm]

/-- **A level's chaos-weighted sum by the profile**: when every window `2008 ≤ m < J` is
eligible, `chaosWinSum q J z ≤ profSum a (chaosAhat q) J`, `a = q(2q-1)`. -/
theorem chaosWinSum_le_profSum {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1) {J z : ℕ}
    (hel : ∀ m, m < J → 2008 ≤ m → (m : ℝ) + 97 ≤ Real.log (Real.log z)) :
    chaosWinSum q J z ≤ profSum (q * (2 * q - 1)) (chaosAhat q) J := by
  rw [chaosWinSum, profSum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmJ := (Finset.mem_Ico.1 hm).2
  exact mul_le_mul_of_nonneg_left (chaosMult_le_chaosProf hq0 hq1 (hel m hmJ))
    (Real.exp_pos _).le

/-- **The bottom's chaos-weighted sum by the profile**: the windows past `M₀` may be ineligible,
and there the chaos factor is at most `1`, so
`chaosWinSum q N z ≤ profSum a (chaosAhat q) N + ∑_{M₀ ≤ m < N} e^{-am}` when every window
`2008 ≤ m < M₀` is eligible. -/
theorem chaosWinSum_le_profSum_add {q : ℝ} (hq0 : 1 / 2 ≤ q) (hq1 : q < 1) {N M₀ z : ℕ}
    (hel : ∀ m, m < M₀ → 2008 ≤ m → (m : ℝ) + 97 ≤ Real.log (Real.log z)) :
    chaosWinSum q N z ≤ profSum (q * (2 * q - 1)) (chaosAhat q) N
      + ∑ m ∈ Finset.Ico M₀ N, Real.exp (-(q * (2 * q - 1) * m)) := by
  have hA := chaosAhat_nonneg hq1
  rw [chaosWinSum, profSum]
  have hterm : ∀ m ∈ Finset.Ico 1 N, Real.exp (-(q * (2 * q - 1) * m)) * chaosMult q m z
      ≤ Real.exp (-(q * (2 * q - 1) * m)) * chaosProf (chaosAhat q) m
        + (if M₀ ≤ m then Real.exp (-(q * (2 * q - 1) * m)) else 0) := by
    intro m _
    by_cases hm : M₀ ≤ m
    · rw [if_pos hm]
      have h1 := chaosMult_le_one q m z
      have h2 := chaosProf_nonneg hA m
      have he := (Real.exp_pos (-(q * (2 * q - 1) * m))).le
      nlinarith [mul_le_mul_of_nonneg_left h1 he]
    · rw [if_neg hm, add_zero]
      exact mul_le_mul_of_nonneg_left (chaosMult_le_chaosProf hq0 hq1
        (hel m (by omega))) (Real.exp_pos _).le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (le_of_eq ?_) ?_
  · rfl
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => (Real.exp_pos _).le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Ico] at hm ⊢
  omega

/-! ### Hölder against weights -/

/-- **Hölder against weights**: for `0 < P < 1`, `y ≥ 0` and `ρ > 0` on a finite set,
`∑ y^P ≤ (∑ y ρ^{-(1-P)/P})^P (∑ ρ)^{1-P}`. -/
theorem sum_rpow_le_weighted {ι : Type*} (s : Finset ι) {y ρ : ι → ℝ} {P : ℝ} (hP0 : 0 < P)
    (hP1 : P < 1) (hy : ∀ i ∈ s, 0 ≤ y i) (hρ : ∀ i ∈ s, 0 < ρ i) :
    ∑ i ∈ s, y i ^ P
      ≤ (∑ i ∈ s, y i * ρ i ^ (-((1 - P) / P))) ^ P * (∑ i ∈ s, ρ i) ^ (1 - P) := by
  have hpq := Real.HolderConjugate.inv_one_sub_inv hP0 hP1
  have hf : ∀ i ∈ s, 0 ≤ (y i * ρ i ^ (-((1 - P) / P))) ^ P := fun i hi =>
    Real.rpow_nonneg (mul_nonneg (hy i hi) (Real.rpow_nonneg (hρ i hi).le _)) _
  have hg : ∀ i ∈ s, 0 ≤ ρ i ^ (1 - P) := fun i hi => Real.rpow_nonneg (hρ i hi).le _
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq hf hg
  have e1 : ∀ i ∈ s, (y i * ρ i ^ (-((1 - P) / P))) ^ P * ρ i ^ (1 - P) = y i ^ P := by
    intro i hi
    have hρ0 := hρ i hi
    rw [Real.mul_rpow (hy i hi) (Real.rpow_nonneg hρ0.le _), ← Real.rpow_mul hρ0.le,
      mul_assoc, ← Real.rpow_add hρ0]
    have : -((1 - P) / P) * P + (1 - P) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero, mul_one]
  have e2 : ∀ i ∈ s, ((y i * ρ i ^ (-((1 - P) / P))) ^ P) ^ P⁻¹
      = y i * ρ i ^ (-((1 - P) / P)) := by
    intro i hi
    rw [← Real.rpow_mul (mul_nonneg (hy i hi) (Real.rpow_nonneg (hρ i hi).le _)),
      mul_inv_cancel₀ hP0.ne', Real.rpow_one]
  have e3 : ∀ i ∈ s, (ρ i ^ (1 - P)) ^ (1 - P)⁻¹ = ρ i := by
    intro i hi
    rw [← Real.rpow_mul (hρ i hi).le, mul_inv_cancel₀ (by linarith), Real.rpow_one]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  simpa only [one_div, inv_inv] using h

/-! ### Counting along the tower -/

/-- `log r_{j+1} ≥ 2 log r_j` past the first step, `r` the tower `RMF.towerR`. -/
lemma log_towerR_succ_ge {j : ℕ} (hj : 1 ≤ j) :
    2 * Real.log (towerR j) ≤ Real.log (towerR (j + 1)) := by
  have h20 : 20 ≤ towerR j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 := towerR_ten_le i
    change 20 ≤ Real.exp (towerR i / 3)
    have : Real.exp (10 / 3) ≤ Real.exp (towerR i / 3) := Real.exp_le_exp.2 (by linarith)
    have h3 : (20 : ℝ) ≤ Real.exp (10 / 3) := by
      have he3 : (20 : ℝ) ≤ Real.exp 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_gt_d9
        have h4 : (2.718 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 3
        linarith [show (20 : ℝ) ≤ 2.718 ^ 3 by norm_num]
      linarith [Real.exp_le_exp.2 (by norm_num : (3 : ℝ) ≤ 10 / 3)]
    linarith
  change 2 * Real.log (towerR j) ≤ Real.log (Real.exp (towerR j / 3))
  rw [Real.log_exp]
  have hr : 0 < towerR j := by linarith
  have := Real.log_le_sub_one_of_pos (show 0 < towerR j / 20 by positivity)
  rw [Real.log_div hr.ne' (by norm_num)] at this
  have hl20 : Real.log 20 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      ← Real.exp_one_pow]
    have := Real.exp_one_gt_d9
    have h4 : (2.7182818 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 3
    linarith [show (20 : ℝ) < 2.7182818 ^ 3 by norm_num]
  linarith

/-- `log r_j ≥ (10/3)·2^{j-1}` for `j ≥ 1`. -/
lemma log_towerR_ge {j : ℕ} (hj : 1 ≤ j) : 10 / 3 * 2 ^ (j - 1) ≤ Real.log (towerR j) := by
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      change 10 / 3 * 2 ^ 0 ≤ Real.log (Real.exp (towerR 0 / 3))
      rw [Real.log_exp]; simp [towerR]
    · have h1 := ih hn
      have h2 := log_towerR_succ_ge hn
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
      linarith

/-- **`∑ e^{-c2^j}` is at most `k + 1`** once `c2^k ≥ 1`: the first `k` terms are at most `1`,
the rest at most `e^{-(j-k+1)}`. -/
lemma sum_exp_neg_mul_two_pow_le {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ c * 2 ^ k) (n : ℕ) :
    ∑ j ∈ Finset.range n, Real.exp (-(c * 2 ^ j)) ≤ k + 1 := by
  set r := Real.exp (-1) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hterm : ∀ j ∈ Finset.range n, Real.exp (-(c * 2 ^ j))
      ≤ (if j < k then 1 else 0) + Real.exp (k - 1) * r ^ j * (if j < k then 0 else 1) := by
    intro j _
    by_cases hj : j < k
    · rw [if_pos hj, if_pos hj, mul_zero, add_zero]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    · rw [if_neg hj, if_neg hj, zero_add, mul_one, hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h2 : ((j - k : ℕ) : ℝ) + 1 ≤ 2 ^ (j - k) := by
        have := Nat.lt_two_pow_self (n := j - k)
        exact_mod_cast this
      have h3 : c * 2 ^ j = (c * 2 ^ k) * 2 ^ (j - k) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
      have h4 : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by rw [Nat.cast_sub (by omega)]
      rw [h3]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (j - k)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.range n, (if j < k then (1 : ℝ) else 0) ≤ k := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.filter (fun j => j < k) (Finset.range n)).card ≤ k := by
      calc (Finset.filter (fun j => j < k) (Finset.range n)).card
          ≤ (Finset.range k).card := Finset.card_le_card fun j hj => by
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; exact hj.2
        _ = k := Finset.card_range k
    exact_mod_cast this
  have h2 : ∑ j ∈ Finset.range n, Real.exp (k - 1) * r ^ j * (if j < k then (0 : ℝ) else 1)
      ≤ 1 := by
    have hsub : ∑ j ∈ Finset.range n, Real.exp (k - 1) * r ^ j * (if j < k then (0 : ℝ) else 1)
        ≤ ∑ j ∈ Finset.Ico k (max n k), Real.exp (k - 1) * r ^ j := by
      have e : ∑ j ∈ Finset.range n, Real.exp (k - 1) * r ^ j * (if j < k then (0 : ℝ) else 1)
          = ∑ j ∈ Finset.filter (fun j => ¬ j < k) (Finset.range n), Real.exp (k - 1) * r ^ j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [e]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ =>
        mul_nonneg (Real.exp_pos _).le (pow_nonneg hr0 j)
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hj ⊢
      omega
    refine le_trans hsub ?_
    rw [← Finset.mul_sum]
    have hg := geom_sum_Ico_le_of_lt_one (m := k) (n := max n k) hr0 hr1
    have hrk : Real.exp (k - 1) * r ^ k = r := by
      rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have hr2 : r ≤ 1 / 2 := by
      rw [hrdef, Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9
      linarith
    calc Real.exp (k - 1) * ∑ j ∈ Finset.Ico k (max n k), r ^ j
        ≤ Real.exp (k - 1) * (r ^ k / (1 - r)) :=
          mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = r / (1 - r) := by rw [← mul_div_assoc, hrk]
      _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

/-! ### The tower's levels, counted -/

/-- **The tower's logarithms double**: `log V_{L-j} ≥ (10/3)2^{j-1}` for `1 ≤ j ≤ L`. -/
lemma log_aboveV_ge {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjL : j ≤ aboveDepth Λ) :
    10 / 3 * 2 ^ (j - 1) ≤ Real.log (aboveV Λ (aboveDepth Λ - j)) := by
  have h := aboveV_ge_towerR hΛ hjL
  have h0 : 0 < towerR j := by linarith [towerR_ten_le j]
  exact le_trans (log_towerR_ge hj1) (Real.log_le_log h0 h)

/-- **Few levels are low**: if `log V_ℓ < (10/3)2^n` then `L - ℓ ≤ n`. -/
lemma depth_sub_le_of_log_lt {Λ : ℝ} (hΛ : 10 ≤ 3 * Λ) {ℓ n : ℕ} (hℓ : ℓ ≤ aboveDepth Λ)
    (h : Real.log (aboveV Λ ℓ) < 10 / 3 * 2 ^ n) : aboveDepth Λ - ℓ ≤ n := by
  by_contra hcon
  push Not at hcon
  have hj1 : 1 ≤ aboveDepth Λ - ℓ := by omega
  have := log_aboveV_ge hΛ hj1 (Nat.sub_le _ _)
  rw [show aboveDepth Λ - (aboveDepth Λ - ℓ) = ℓ by omega] at this
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ (aboveDepth Λ - ℓ - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- **The tower's weights sum**: for `b > 0` and `k` with `(10/3)b·2^k ≥ 1`,
`∑_{ℓ<L} V_{ℓ+1}^{-b} ≤ k + 2`. -/
theorem sum_aboveV_rpow_le {Λ b : ℝ} (hΛ : 10 ≤ 3 * Λ) (hb : 0 < b) {k : ℕ}
    (hk : 1 ≤ 10 / 3 * b * 2 ^ k) :
    ∑ ℓ ∈ Finset.range (aboveDepth Λ), aboveV Λ (ℓ + 1) ^ (-b) ≤ k + 2 := by
  set L := aboveDepth Λ with hLdef
  obtain ⟨-, hV⟩ := aboveDepth_spec hΛ
  -- reindex from the top: `ℓ + 1 = L - j`
  have hre : ∑ ℓ ∈ Finset.range L, aboveV Λ (ℓ + 1) ^ (-b)
      = ∑ j ∈ Finset.range L, aboveV Λ (L - j) ^ (-b) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show L - 1 - j + 1 = L - j by omega]
  rw [hre]
  -- each term: `V_{L-j}^{-b} ≤ e^{-b(10/3)2^{j-1}}` for `j ≥ 1`, and `≤ 1` at `j = 0`
  have hterm : ∀ j ∈ Finset.range L, aboveV Λ (L - j) ^ (-b)
      ≤ (if j = 0 then 1 else Real.exp (-(10 / 3 * b * 2 ^ (j - 1)))) := by
    intro j hj
    have hjL := (Finset.mem_range.1 hj).le
    have hV10 := hV (L - j) (Nat.sub_le L j)
    have hVpos : 0 < aboveV Λ (L - j) := by linarith
    split_ifs with h0
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    · rw [Real.rpow_def_of_pos hVpos]
      refine Real.exp_le_exp.2 ?_
      have := log_aboveV_ge hΛ (by omega) hjL
      nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · rw [hL0, Finset.sum_range_zero]; positivity
  rw [show L = (L - 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, if_pos, Nat.succ_ne_zero, if_false]
  have := sum_exp_neg_mul_two_pow_le (c := 10 / 3 * b) (by positivity) hk (L - 1)
  linarith

/-- **`∑ e^{-c2^m} ≤ 2e^{-c}`** for `c ≥ 1`. -/
lemma sum_exp_neg_mul_two_pow_le_two {c : ℝ} (hc : 1 ≤ c) (n : ℕ) :
    ∑ m ∈ Finset.range n, Real.exp (-(c * 2 ^ m)) ≤ 2 * Real.exp (-c) := by
  set r := Real.exp (-1) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hterm : ∀ m ∈ Finset.range n, Real.exp (-(c * 2 ^ m)) ≤ Real.exp (-c) * r ^ m := by
    intro m _
    rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((m : ℕ) : ℝ) + 1 ≤ 2 ^ m := by
      have := Nat.lt_two_pow_self (n := m)
      exact_mod_cast this
    nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hg : ∑ m ∈ Finset.range n, r ^ m ≤ 1 / (1 - r) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    exact h
  have hr2 : 1 / (1 - r) ≤ 2 := by
    have : r ≤ 1 / 2 := by
      rw [hrdef, Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9
      linarith
    rw [div_le_iff₀ (by linarith)]; linarith
  have := mul_le_mul_of_nonneg_left (le_trans hg hr2) (Real.exp_pos (-c)).le
  linarith

/-- `2 log v ≤ v/3` for `v ≥ 20`. -/
lemma two_log_le_div_three {v : ℝ} (hv : 20 ≤ v) : 2 * Real.log v ≤ v / 3 := by
  have hv0 : 0 < v := by linarith
  have := Real.log_le_sub_one_of_pos (show 0 < v / 20 by positivity)
  rw [Real.log_div hv0.ne' (by norm_num)] at this
  have hl20 : Real.log 20 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      ← Real.exp_one_pow]
    have := Real.exp_one_gt_d9
    have h4 : (2.7182818 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 3
    linarith [show (20 : ℝ) < 2.7182818 ^ 3 by norm_num]
  linarith

/-- **The chain of levels.**  Along the tower (`Λ ≥ 12`, depth `L`), for window sums
`profSum a A (J_ℓ)` with `J_ℓ ≤ log V_ℓ - log V_{ℓ+1} + 1.001`, a bound `B` on every profile sum,
a height `X ≥ 5`, `n₀` with `log(3X) < (10/3)2^{n₀}`, `a'e^X/3 ≥ 1` and a bound `T` on
`profSum(N) + e^{1.001a'}e^{-a'N}B` for every `N`:

`∑_{ℓ<L} V_{ℓ+1}^{-a'}profSum(J_ℓ) + V₀^{-a'}B
  ≤ min(X + 1.001, 2007) + A(4/3)(X + 1.001)^{3/4} + n₀(log(3X) + 1.001) + T
    + 2e^{-a'e^X/3}B`:

the levels starting below `X` (the last of them the main one, the others short), the next one
(its partner, priced with the main one by `T`) and the rest, suppressed. -/
theorem chain_windows_le {Λ a a' A X B T : ℝ} (hΛ : 12 ≤ Λ) (ha : 0 ≤ a) (ha' : 0 < a')
    (hA : 0 ≤ A) (hX : 5 ≤ X) (hB : ∀ N, profSum a A N ≤ B) {J : ℕ → ℕ}
    (hJ : ∀ ℓ < aboveDepth Λ,
      (J ℓ : ℝ) ≤ Real.log (aboveV Λ ℓ) - Real.log (aboveV Λ (ℓ + 1)) + 1.001)
    {n₀ : ℕ} (hn₀ : Real.log (3 * X) < 10 / 3 * 2 ^ n₀)
    (hfar : 1 ≤ a' * (Real.exp X / 3))
    (hT : ∀ N : ℕ, profSum a A N + Real.exp (1.001 * a') * Real.exp (-(a' * N)) * B ≤ T) :
    ∑ ℓ ∈ Finset.range (aboveDepth Λ), aboveV Λ (ℓ + 1) ^ (-a') * profSum a A (J ℓ)
        + aboveV Λ 0 ^ (-a') * B
      ≤ min (X + 1.001) 2007 + A * (4 / 3 * (X + 1.001) ^ (3 / 4 : ℝ))
        + n₀ * (Real.log (3 * X) + 1.001) + T + 2 * Real.exp (-(a' * (Real.exp X / 3))) * B := by
  classical
  have hΛ10 : 10 ≤ 3 * Λ := by linarith
  set L := aboveDepth Λ with hLdef
  set V := aboveV Λ with hVdef
  obtain ⟨hVL, hV10⟩ := aboveDepth_spec hΛ10
  rw [← hLdef, ← hVdef] at hVL hV10
  have hV8 : ∀ ℓ ≤ L, 8 ≤ V ℓ := fun ℓ hℓ => by linarith [hV10 ℓ hℓ]
  have hVpos : ∀ ℓ ≤ L, 0 < V ℓ := fun ℓ hℓ => by linarith [hV10 ℓ hℓ]
  have hVsucc : ∀ ℓ, V (ℓ + 1) = 3 * Real.log (V ℓ) := fun ℓ => aboveV_succ Λ ℓ
  have hVanti : ∀ i j, i ≤ j → j ≤ L → V j ≤ V i := by
    intro i j hij hjL
    induction j with
    | zero => rw [Nat.le_zero.1 hij]
    | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact le_trans (aboveV_succ_le hV8 (by omega)) (ih (by omega) (by omega))
      · rw [show i = n + 1 by omega]
  have hB0 : 0 ≤ B := le_trans (profSum_nonneg hA 0) (hB 0)
  have hS0 : ∀ N, 0 ≤ profSum a A N := profSum_nonneg hA
  have hT0 : B ≤ T := by
    have := hT 0
    rw [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    have h1 : 1 ≤ Real.exp (1.001 * a') := Real.one_le_exp (by positivity)
    nlinarith [hS0 0]
  have hw1 : ∀ ℓ ≤ L, V ℓ ^ (-a') ≤ 1 := fun ℓ hℓ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hV10 ℓ hℓ]) (by linarith)
  have hw0 : ∀ ℓ ≤ L, 0 ≤ V ℓ ^ (-a') := fun ℓ hℓ => Real.rpow_nonneg (hVpos ℓ hℓ).le _
  have hsmall0 : 0 ≤ min (X + 1.001) 2007 + A * (4 / 3 * (X + 1.001) ^ (3 / 4 : ℝ)) := by
    have : 0 ≤ min (X + 1.001) 2007 := le_min (by linarith) (by norm_num)
    positivity
  have hlog3X : 0 ≤ Real.log (3 * X) + 1.001 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 3 * X); linarith
  have hshort0 : 0 ≤ (n₀ : ℝ) * (Real.log (3 * X) + 1.001) := by positivity
  have hfar0 : 0 ≤ 2 * Real.exp (-(a' * (Real.exp X / 3))) * B := by positivity
  -- the case without bands
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · rw [hL0, Finset.sum_range_zero, zero_add]
    have := mul_le_mul_of_nonneg_right (hw1 0 (Nat.zero_le _)) hB0
    linarith
  -- the main level: the least `ℓ` starting below `X`
  have hE : ∃ ℓ, ℓ < L ∧ Real.log (V (ℓ + 1)) ≤ X := by
    refine ⟨L - 1, by omega, ?_⟩
    rw [show L - 1 + 1 = L by omega]
    linarith
  set ℓs := Nat.find hE with hℓsdef
  obtain ⟨hℓsL, hℓsX⟩ := Nat.find_spec hE
  rw [← hℓsdef] at hℓsL hℓsX
  have hbelow : ∀ ℓ < ℓs, X < Real.log (V (ℓ + 1)) := by
    intro ℓ hℓ
    have := Nat.find_min hE (hℓsdef ▸ hℓ)
    push Not at this
    exact this (by omega)
  -- the partner's weight
  have hlogV1 : ∀ ℓ ≤ L, 0 ≤ Real.log (V ℓ) := fun ℓ hℓ =>
    Real.log_nonneg (by linarith [hV10 ℓ hℓ])
  have hpartner : V ℓs ^ (-a') ≤ Real.exp (1.001 * a') * Real.exp (-(a' * (J ℓs : ℝ))) := by
    rw [Real.rpow_def_of_pos (hVpos ℓs hℓsL.le), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := hJ ℓs hℓsL
    have h2 := hlogV1 (ℓs + 1) hℓsL
    nlinarith
  have hmain := hT (J ℓs)
  -- the short levels past the main one
  have hshort : ∑ ℓ ∈ Finset.Ico (ℓs + 1) L, V (ℓ + 1) ^ (-a') * profSum a A (J ℓ)
      ≤ min (X + 1.001) 2007 + A * (4 / 3 * (X + 1.001) ^ (3 / 4 : ℝ))
        + n₀ * (Real.log (3 * X) + 1.001) := by
    rcases Nat.lt_or_ge (ℓs + 1) L with h1 | h1
    · rw [Finset.sum_eq_sum_Ico_succ_bot h1]
      refine add_le_add ?_ ?_
      · -- the next level: at most `X + 1.001` windows
        refine le_trans (mul_le_of_le_one_left (hS0 _) (hw1 _ (by omega))) ?_
        have hJX : (J (ℓs + 1) : ℝ) ≤ X + 1.001 := by
          have := hJ (ℓs + 1) h1
          have := hlogV1 (ℓs + 1 + 1) (by omega)
          linarith
        have hA0 : 0 ≤ A * (4 / 3 * (X + 1.001) ^ (3 / 4 : ℝ)) := by positivity
        have h2 : profSum a A (J (ℓs + 1)) ≤ 2007 + A * (4 / 3 * (X + 1.001) ^ (3 / 4 : ℝ)) :=
          le_trans (profSum_le_small ha hA _) (add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (z := 3 / 4) (Nat.cast_nonneg _) hJX
              (by norm_num)) (by norm_num : (0 : ℝ) ≤ 4 / 3)) hA))
        have h3 : profSum a A (J (ℓs + 1)) ≤ X + 1.001 := le_trans (profSum_le_card ha _) hJX
        rcases min_cases (X + 1.001) 2007 with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith
      · -- the others: at most `log(3X) + 1.001` windows each, and at most `n₀` of them
        have hV2 : V (ℓs + 2) ≤ 3 * X := by
          rw [show ℓs + 2 = ℓs + 1 + 1 by omega, hVsucc]; linarith
        have hterm : ∀ ℓ ∈ Finset.Ico (ℓs + 1 + 1) L, V (ℓ + 1) ^ (-a') * profSum a A (J ℓ)
            ≤ Real.log (3 * X) + 1.001 := by
          intro ℓ hℓ
          have hℓ' := Finset.mem_Ico.1 hℓ
          refine le_trans (mul_le_of_le_one_left (hS0 _) (hw1 _ (by omega))) ?_
          refine le_trans (profSum_le_card ha _) ?_
          have h2 := hJ ℓ hℓ'.2
          have h3 := hlogV1 (ℓ + 1) (by omega)
          have h4 : Real.log (V ℓ) ≤ Real.log (3 * X) :=
            Real.log_le_log (hVpos ℓ (by omega)) (le_trans (hVanti (ℓs + 2) ℓ (by omega)
              (by omega)) hV2)
          linarith
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hcount : L - (ℓs + 1 + 1) ≤ n₀ := by
          refine depth_sub_le_of_log_lt hΛ10 (by omega) ?_
          rw [show ℓs + 1 + 1 = ℓs + 2 by omega]
          exact lt_of_le_of_lt (Real.log_le_log (hVpos _ (by omega)) hV2) hn₀
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hlog3X
    · rw [Finset.Ico_eq_empty_of_le h1, Finset.sum_empty]
      linarith
  -- assemble: split the bands at the main level
  rw [← Finset.sum_range_add_sum_Ico _ hℓsL.le, Finset.sum_eq_sum_Ico_succ_bot hℓsL]
  have hmainterm : V (ℓs + 1) ^ (-a') * profSum a A (J ℓs) ≤ profSum a A (J ℓs) :=
    mul_le_of_le_one_left (hS0 _) (hw1 _ (by omega))
  rcases Nat.eq_zero_or_pos ℓs with h0 | hpos
  · -- the main level is the lowest band: its partner is the bottom
    rw [h0, Finset.sum_range_zero, zero_add]
    rw [h0] at hpartner hmain hmainterm hshort
    have hbot : V 0 ^ (-a') * B
        ≤ Real.exp (1.001 * a') * Real.exp (-(a' * (J 0 : ℝ))) * B :=
      mul_le_mul_of_nonneg_right hpartner hB0
    linarith
  · -- the partner is the band below, the rest are suppressed
    obtain ⟨m, hm⟩ : ∃ m, ℓs = m + 1 := ⟨ℓs - 1, by omega⟩
    rw [hm, Finset.sum_range_succ]
    rw [hm] at hpartner hmain hmainterm hshort hℓsL
    have hpart : V (m + 1) ^ (-a') * profSum a A (J m)
        ≤ Real.exp (1.001 * a') * Real.exp (-(a' * (J (m + 1) : ℝ))) * B :=
      le_trans (mul_le_mul_of_nonneg_left (hB _) (hw0 _ (by omega)))
        (mul_le_mul_of_nonneg_right hpartner hB0)
    -- the suppressed levels: `log V_i ≥ (e^X/3)2^{m-i}` for `i ≤ m`
    have hbase : Real.exp X / 3 ≤ Real.log (V m) := by
      have h1 : X < Real.log (V (m + 1)) := hbelow m (by omega)
      have h2 : Real.exp X ≤ V (m + 1) := by
        rw [← Real.exp_log (hVpos (m + 1) (by omega))]
        exact Real.exp_le_exp.2 h1.le
      rw [hVsucc m] at h2
      linarith
    have hX20 : (20 : ℝ) ≤ Real.exp X / 3 := by
      have h5 : (60 : ℝ) ≤ Real.exp 5 := by
        rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
        have := Real.exp_one_gt_d9
        have h4 : (2.718 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 5
        linarith [show (60 : ℝ) ≤ 2.718 ^ 5 by norm_num]
      have := Real.exp_le_exp.2 hX
      linarith
    have hlogs : ∀ d ≤ m, Real.exp X / 3 * 2 ^ d ≤ Real.log (V (m - d)) := by
      intro d hd
      induction d with
      | zero => simpa using hbase
      | succ d ih =>
        have ih' := ih (by omega)
        have hVd : 20 ≤ V (m - d) := by
          have h1 : V m ≤ V (m - d) := hVanti (m - d) m (by omega) (by omega)
          have h2 : Real.log (V m) + 1 ≤ V m := by
            have := Real.add_one_le_exp (Real.log (V m))
            rwa [Real.exp_log (hVpos m (by omega))] at this
          linarith
        have hs : V (m - d) = 3 * Real.log (V (m - (d + 1))) := by
          rw [show m - d = m - (d + 1) + 1 by omega]; exact hVsucc _
        have := two_log_le_div_three hVd
        rw [pow_succ]
        nlinarith
    -- the suppressed levels
    have hsupp : ∑ ℓ ∈ Finset.range m, V (ℓ + 1) ^ (-a') * profSum a A (J ℓ) + V 0 ^ (-a') * B
        ≤ 2 * Real.exp (-(a' * (Real.exp X / 3))) * B := by
      have h1 : ∑ ℓ ∈ Finset.range m, V (ℓ + 1) ^ (-a') * profSum a A (J ℓ) + V 0 ^ (-a') * B
          ≤ (∑ ℓ ∈ Finset.range m, V (ℓ + 1) ^ (-a') + V 0 ^ (-a')) * B := by
        rw [add_mul, Finset.sum_mul]
        refine add_le_add (Finset.sum_le_sum fun ℓ hℓ => mul_le_mul_of_nonneg_left (hB _)
          (hw0 _ (by have := Finset.mem_range.1 hℓ; omega))) le_rfl
      have h2 : ∑ ℓ ∈ Finset.range m, V (ℓ + 1) ^ (-a') + V 0 ^ (-a')
          = ∑ i ∈ Finset.range (m + 1), V i ^ (-a') := by
        rw [Finset.sum_range_succ']
      have h3 : ∑ i ∈ Finset.range (m + 1), V i ^ (-a')
          ≤ ∑ d ∈ Finset.range (m + 1), Real.exp (-(a' * (Real.exp X / 3) * 2 ^ d)) := by
        rw [← Finset.sum_range_reflect (fun d => Real.exp (-(a' * (Real.exp X / 3) * 2 ^ d)))
          (m + 1)]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [Real.rpow_def_of_pos (hVpos i (by omega))]
        refine Real.exp_le_exp.2 ?_
        have := hlogs (m - i) (by omega)
        rw [show m - (m - i) = i by omega] at this
        rw [show m + 1 - 1 - i = m - i by omega]
        nlinarith
      have h4 := sum_exp_neg_mul_two_pow_le_two hfar (m + 1)
      rw [h2] at h1
      have h5 : ∑ d ∈ Finset.range (m + 1), Real.exp (-(a' * (Real.exp X / 3) * 2 ^ d))
          ≤ 2 * Real.exp (-(a' * (Real.exp X / 3))) := h4
      exact le_trans h1 (mul_le_mul_of_nonneg_right (le_trans h3 h5) hB0)
    linarith

/-! ### The powers `1/(2q)` along the tower -/

/-- `u^P ≤ u + (1 - P)` for `u ≥ 0`, `0 ≤ P ≤ 1` (the tangent at `1`). -/
lemma rpow_le_add_one_sub {u P : ℝ} (hu : 0 ≤ u) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    u ^ P ≤ u + (1 - P) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hP0 (by linarith : 0 ≤ 1 - P) hu zero_le_one
    (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at h
  nlinarith

/-- **The levels' powers, summed**: for `0 < P < 1`, `y_ℓ ≥ 0` on the bands with weights `ρ_ℓ > 0`
of total at most `11`, and `y_b ≥ 0`:
`∑ y_ℓ^P + y_b^P ≤ 12^{1-P}(∑ y_ℓρ_ℓ^{-(1-P)/P} + y_b + 2(1 - P))`. -/
theorem sum_rpow_add_le {n : ℕ} {y ρ : ℕ → ℝ} {yb P : ℝ} (hP0 : 0 < P) (hP1 : P < 1)
    (hy : ∀ ℓ ∈ Finset.range n, 0 ≤ y ℓ) (hρ : ∀ ℓ ∈ Finset.range n, 0 < ρ ℓ)
    (hρsum : ∑ ℓ ∈ Finset.range n, ρ ℓ ≤ 11) (hyb : 0 ≤ yb) :
    ∑ ℓ ∈ Finset.range n, y ℓ ^ P + yb ^ P
      ≤ (12 : ℝ) ^ (1 - P) * (∑ ℓ ∈ Finset.range n, y ℓ * ρ ℓ ^ (-((1 - P) / P)) + yb
        + 2 * (1 - P)) := by
  have hH := sum_rpow_le_weighted (Finset.range n) hP0 hP1 hy hρ
  set S := ∑ ℓ ∈ Finset.range n, y ℓ * ρ ℓ ^ (-((1 - P) / P)) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun ℓ hℓ =>
    mul_nonneg (hy ℓ hℓ) (Real.rpow_nonneg (hρ ℓ hℓ).le _)
  have hρ0 : 0 ≤ ∑ ℓ ∈ Finset.range n, ρ ℓ := Finset.sum_nonneg fun ℓ hℓ => (hρ ℓ hℓ).le
  have h1 : (∑ ℓ ∈ Finset.range n, ρ ℓ) ^ (1 - P) ≤ (12 : ℝ) ^ (1 - P) :=
    Real.rpow_le_rpow hρ0 (by linarith) (by linarith)
  have h12 : 1 ≤ (12 : ℝ) ^ (1 - P) := Real.one_le_rpow (by norm_num) (by linarith)
  have hSP := rpow_le_add_one_sub hS0 hP0.le hP1.le
  have hbP := rpow_le_add_one_sub hyb hP0.le hP1.le
  have hSP0 : 0 ≤ S ^ P := Real.rpow_nonneg hS0 _
  calc ∑ ℓ ∈ Finset.range n, y ℓ ^ P + yb ^ P
      ≤ S ^ P * (∑ ℓ ∈ Finset.range n, ρ ℓ) ^ (1 - P) + yb ^ P := by linarith
    _ ≤ (S + (1 - P)) * (12 : ℝ) ^ (1 - P) + (yb + (1 - P)) * (12 : ℝ) ^ (1 - P) := by
        refine add_le_add (mul_le_mul hSP h1 (Real.rpow_nonneg hρ0 _) (by linarith)) ?_
        nlinarith
    _ = _ := by ring

/-! ### The scales at `Λ ≥ 200` -/

/-- `log x ≥ 3000Λ` for `Λ = log log x ≥ 200`, so the scales' logarithms lose at most `0.1%` to the
floor. -/
lemma log_ge_of_loglog {x : ℝ} (hx3 : 3 ≤ x) (hΛ : 200 ≤ Real.log (Real.log x)) :
    3000 * Real.log (Real.log x) ≤ Real.log x := by
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := exp_ge_lin_eleven (by linarith : (11 : ℝ) ≤ Real.log (Real.log x))
  have h2 : Real.exp (Real.log (Real.log x)) = Real.log x := Real.exp_log hlx0
  have h3 : 0 ≤ Real.log (Real.log x) := by linarith
  linarith

/-- **A band's window count along the tower**: `J_ℓ ≤ log V_ℓ - log V_{ℓ+1} + 1.001` at
`Λ ≥ 200`. -/
lemma bandJ_aboveZ_le {x : ℝ} (hx3 : 3 ≤ x) (hΛ : 200 ≤ Real.log (Real.log x)) {ℓ : ℕ}
    (hℓ : ℓ < aboveDepth (Real.log (Real.log x))) :
    (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)) : ℝ)
      ≤ Real.log (aboveV (Real.log (Real.log x)) ℓ)
        - Real.log (aboveV (Real.log (Real.log x)) (ℓ + 1)) + 1.001 := by
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ11 : 11 ≤ Λ := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨hVl, hVl3, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ11 hℓ.le
  obtain ⟨hVs, -, hs1, hs2, hs5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.succ_le_of_lt hℓ)
  have hlog2 := Real.log_two_lt_d9
  have hly0 : 0 < Real.log (aboveZ x ℓ) := by linarith
  have hlz0 : 0 < Real.log (aboveZ x (ℓ + 1)) := by linarith
  have hVl0 : 0 < aboveV Λ ℓ := by linarith
  have hVs0 : 0 < aboveV Λ (ℓ + 1) := by linarith
  have hbig := log_ge_of_loglog hx3 hΛ
  -- `log z/log y ≤ 1.001 V_ℓ/V_{ℓ+1}`
  have hratio : Real.log (aboveZ x (ℓ + 1)) / Real.log (aboveZ x ℓ)
      ≤ 1.001 * (aboveV Λ ℓ / aboveV Λ (ℓ + 1)) := by
    rw [div_le_iff₀ hly0]
    have h1 : Real.log x / aboveV Λ (ℓ + 1)
        ≤ 1.001 * (aboveV Λ ℓ / aboveV Λ (ℓ + 1)) * (Real.log x / aboveV Λ ℓ - Real.log 2) := by
      rw [show 1.001 * (aboveV Λ ℓ / aboveV Λ (ℓ + 1)) * (Real.log x / aboveV Λ ℓ - Real.log 2)
          = (1.001 * Real.log x - 1.001 * aboveV Λ ℓ * Real.log 2) / aboveV Λ (ℓ + 1) by
        field_simp]
      refine div_le_div_of_nonneg_right ?_ hVs0.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hl1 (by positivity :
      (0 : ℝ) ≤ 1.001 * (aboveV Λ ℓ / aboveV Λ (ℓ + 1)))
    linarith
  have hκ1 : 1 ≤ Real.log (aboveZ x (ℓ + 1)) / Real.log (aboveZ x ℓ) := by
    have hmono : (aboveZ x ℓ : ℝ) ≤ aboveZ x (ℓ + 1) := by
      have hL8 : ∀ k ≤ aboveDepth Λ, 8 ≤ aboveV Λ k :=
        fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ11 hk).1]
      exact_mod_cast (aboveZ_facts hx3 hΛ11 hL8).2.2 ℓ hℓ
    rw [le_div_iff₀ hly0, one_mul]
    exact Real.log_le_log (by
      have := (aboveZ_log_facts hx3 hΛ11 hℓ.le).2.2.1
      have : (1 : ℝ) < aboveZ x ℓ := by
        by_contra hc; push Not at hc
        have : Real.log (aboveZ x ℓ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc
        linarith
      linarith) hmono
  have hJ2 : (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)) : ℝ)
      < Real.log (Real.log (aboveZ x (ℓ + 1)) / Real.log (aboveZ x ℓ)) + 1 := by
    rw [bandJ, one_mul]
    exact Nat.ceil_lt_add_one (Real.log_nonneg hκ1)
  have hlog : Real.log (Real.log (aboveZ x (ℓ + 1)) / Real.log (aboveZ x ℓ))
      ≤ Real.log (aboveV Λ ℓ) - Real.log (aboveV Λ (ℓ + 1)) + 0.001 := by
    have h1 := Real.log_le_log (by linarith) hratio
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hVl0.ne' hVs0.ne'] at h1
    have h2 : Real.log 1.001 ≤ 0.001 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.001); linarith
    linarith
  linarith

/-- **A band's windows are eligible for the chaos** at `Λ ≥ 200`: every `m < J_ℓ` has
`m + 97 ≤ log log z_{ℓ+1}`. -/
lemma band_windows_eligible {x : ℝ} (hx3 : 3 ≤ x) (hΛ : 200 ≤ Real.log (Real.log x)) {ℓ : ℕ}
    (hℓ : ℓ < aboveDepth (Real.log (Real.log x))) :
    ∀ m, m < bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)) → 2008 ≤ m →
      (m : ℝ) + 97 ≤ Real.log (Real.log (aboveZ x (ℓ + 1))) := by
  intro m hm _
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ11 : 11 ≤ Λ := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hJ := bandJ_aboveZ_le hx3 hΛ hℓ
  rw [← hΛdef] at hJ
  obtain ⟨hVl, hVl3, -, -, -, -⟩ := aboveZ_log_facts hx3 hΛ11 hℓ.le
  obtain ⟨hVs, -, hs1, -, hs5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.succ_le_of_lt hℓ)
  have hVs0 : 0 < aboveV Λ (ℓ + 1) := by linarith
  have hbig := log_ge_of_loglog hx3 hΛ
  have hlog2 := Real.log_two_lt_d9
  have hm' : (m : ℝ) + 1 ≤ bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)) := by exact_mod_cast hm
  -- `log log z_{ℓ+1} ≥ Λ - log V_{ℓ+1} - 0.001`
  have hlz : Real.log x / aboveV Λ (ℓ + 1) * 0.999 ≤ Real.log (aboveZ x (ℓ + 1)) := by
    have : Real.log 2 ≤ 0.001 * (Real.log x / aboveV Λ (ℓ + 1)) := by linarith
    linarith
  have hll : Λ - Real.log (aboveV Λ (ℓ + 1)) + Real.log 0.999
      ≤ Real.log (Real.log (aboveZ x (ℓ + 1))) := by
    have h1 := Real.log_le_log (by positivity) hlz
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_div hlx0.ne' hVs0.ne'] at h1
    linarith
  have h999 : -0.0011 ≤ Real.log 0.999 := by
    have := Real.add_one_le_exp (-0.0011 : ℝ)
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h2 : Real.exp (-0.0011) ≤ 1 / (1 + 0.0011) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (0.0011 : ℝ)])
    linarith [show (1 : ℝ) / (1 + 0.0011) ≤ 0.999 by norm_num]
  -- `log V_ℓ + 98 ≤ Λ`
  have hV3 : Real.log (aboveV Λ ℓ) ≤ Real.log (3 * Λ) :=
    Real.log_le_log (by linarith) hVl3
  have h3Λ : Real.log (3 * Λ) + 99 ≤ Λ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 3 * Λ / 600 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at this
    have h600 : Real.log 600 < 7 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num), show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num,
        ← Real.exp_one_pow]
      have := Real.exp_one_gt_d9
      have h4 : (2.718 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 7
      linarith [show (600 : ℝ) < 2.718 ^ 7 by norm_num]
    linarith
  linarith

/-- **A level's scale, normalised**: `(3/2·log z_ℓ/log x)^a ≤ 1.5^a V_ℓ^{-a}` for `a ≥ 0`. -/
lemma scale_rpow_le {x a : ℝ} (hx3 : 3 ≤ x) (hΛ : 11 ≤ Real.log (Real.log x)) (ha : 0 ≤ a)
    {ℓ : ℕ} (hℓ : ℓ ≤ aboveDepth (Real.log (Real.log x))) :
    (3 / 2 * Real.log (aboveZ x ℓ) / Real.log x) ^ a
      ≤ (3 / 2 : ℝ) ^ a * aboveV (Real.log (Real.log x)) ℓ ^ (-a) := by
  obtain ⟨hV, -, hl1, hl2, hl5, -⟩ := aboveZ_log_facts hx3 hΛ hℓ
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hV0 : 0 < aboveV (Real.log (Real.log x)) ℓ := by linarith
  have hlz0 : 0 ≤ Real.log (aboveZ x ℓ) := by linarith
  have h1 : 3 / 2 * Real.log (aboveZ x ℓ) / Real.log x
      ≤ 3 / 2 * (aboveV (Real.log (Real.log x)) ℓ)⁻¹ := by
    rw [div_le_iff₀ hlx0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [inv_mul_eq_div]
    exact hl2
  calc (3 / 2 * Real.log (aboveZ x ℓ) / Real.log x) ^ a
      ≤ (3 / 2 * (aboveV (Real.log (Real.log x)) ℓ)⁻¹) ^ a :=
        Real.rpow_le_rpow (by positivity) h1 ha
    _ = (3 / 2 : ℝ) ^ a * aboveV (Real.log (Real.log x)) ℓ ^ (-a) := by
        rw [Real.mul_rpow (by norm_num) (inv_nonneg.2 hV0.le), Real.inv_rpow hV0.le,
          Real.rpow_neg hV0.le]

/-- The bottom's last eligible window: `M₀ = ⌊log log z⌋ - 96`. -/
noncomputable def botM₀ (z : ℕ) : ℕ := ⌊Real.log (Real.log z)⌋₊ - 96

/-- **The bottom's windows below `M₀` are eligible**. -/
lemma bottom_windows_eligible (z : ℕ) :
    ∀ m, m < botM₀ z → 2008 ≤ m → (m : ℝ) + 97 ≤ Real.log (Real.log z) := by
  intro m hm _
  rw [botM₀] at hm
  have h1 : m + 97 ≤ ⌊Real.log (Real.log z)⌋₊ := by omega
  have h2 : (0 : ℝ) < ⌊Real.log (Real.log z)⌋₊ := by
    have : 0 < ⌊Real.log (Real.log z)⌋₊ := by omega
    exact_mod_cast this
  have h3 : ((m + 97 : ℕ) : ℝ) ≤ Real.log (Real.log z) := by
    refine le_trans (by exact_mod_cast h1) (Nat.floor_le ?_)
    by_contra hc
    push Not at hc
    rw [Nat.floor_eq_zero.2 (lt_of_lt_of_le hc zero_le_one)] at h2
    norm_num at h2
  push_cast at h3
  exact h3

/-- **The bottom's ineligible windows are few and deep**: for `a ≥ 0` and `log z ≥ 1`,
`(3/2·log z/log x)^a ∑_{M₀ ≤ m < J_b} e^{-am} ≤ 91·1.5^a e^{97a}e^{-a log log x}`,
`J_b = RMF.bottomJ 1 2 z - 8`. -/
lemma bottom_tail_le {x a : ℝ} (hx : 1 < x) (ha : 0 ≤ a) {z : ℕ} (hz : 1 ≤ Real.log z) :
    (3 / 2 * Real.log z / Real.log x) ^ a
        * ∑ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8), Real.exp (-(a * m))
      ≤ 91 * (3 / 2 : ℝ) ^ a * Real.exp (97 * a) * Real.exp (-(a * Real.log (Real.log x))) := by
  have hlx0 : 0 < Real.log x := Real.log_pos hx
  have hlz0 : 0 < Real.log z := by linarith
  have hllz0 : 0 ≤ Real.log (Real.log z) := Real.log_nonneg hz
  -- `M₀ ≥ log log z - 97`
  have hM : Real.log (Real.log z) - 97 ≤ (botM₀ z : ℝ) := by
    rw [botM₀]
    rcases le_or_gt 96 ⌊Real.log (Real.log z)⌋₊ with h | h
    · rw [Nat.cast_sub h]
      have := Nat.lt_floor_add_one (Real.log (Real.log z))
      push_cast
      linarith
    · have h96 : Real.log (Real.log z) < 96 := by
        by_contra hc
        push Not at hc
        have := Nat.le_floor (show ((96 : ℕ) : ℝ) ≤ Real.log (Real.log z) by exact_mod_cast hc)
        omega
      have : (0 : ℝ) ≤ ((⌊Real.log (Real.log z)⌋₊ - 96 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  -- at most `91` windows
  have hcard : ((bottomJ 1 2 z - 8 : ℕ) : ℝ) < botM₀ z + 91 := by
    rcases le_or_gt 8 (bottomJ 1 2 z) with h | h
    · have hb : (bottomJ 1 2 z : ℝ) < Real.log (Real.log z) + 1.7 := by
        rw [bottomJ, div_one]
        have hlog2 := Real.log_two_lt_d9
        have h2 : Real.log (2 * Real.log z) = Real.log 2 + Real.log (Real.log z) :=
          Real.log_mul (by norm_num) hlz0.ne'
        have := Nat.ceil_lt_add_one (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Real.log z))
        linarith
      rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      have := Nat.cast_nonneg (α := ℝ) (botM₀ z)
      linarith
  have hcard' : (Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8)).card ≤ 91 := by
    rw [Nat.card_Ico]
    have : bottomJ 1 2 z - 8 < botM₀ z + 91 := by exact_mod_cast hcard
    omega
  have hterm : ∀ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8),
      Real.exp (-(a * m)) ≤ Real.exp (-(a * (Real.log (Real.log z) - 97))) := by
    intro m hm
    have hm' : (botM₀ z : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
    exact Real.exp_le_exp.2 (by nlinarith)
  have hsum : ∑ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8), Real.exp (-(a * m))
      ≤ 91 * Real.exp (-(a * (Real.log (Real.log z) - 97))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') (Real.exp_pos _).le
  have hbase : 0 < 3 / 2 * Real.log z / Real.log x := by positivity
  calc (3 / 2 * Real.log z / Real.log x) ^ a
        * ∑ m ∈ Finset.Ico (botM₀ z) (bottomJ 1 2 z - 8), Real.exp (-(a * m))
      ≤ (3 / 2 * Real.log z / Real.log x) ^ a
          * (91 * Real.exp (-(a * (Real.log (Real.log z) - 97)))) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hbase.le _)
    _ = 91 * Real.exp (Real.log (3 / 2 * Real.log z / Real.log x) * a
          + -(a * (Real.log (Real.log z) - 97))) := by
        rw [Real.rpow_def_of_pos hbase, Real.exp_add]; ring
    _ = 91 * Real.exp (Real.log (3 / 2) * a + 97 * a + -(a * Real.log (Real.log x))) := by
        rw [Real.log_div (by positivity) hlx0.ne', Real.log_mul (by norm_num) hlz0.ne']
        ring_nf
    _ = 91 * (3 / 2 : ℝ) ^ a * Real.exp (97 * a) * Real.exp (-(a * Real.log (Real.log x))) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2), Real.exp_add, Real.exp_add]
        ring

/-! ### The chaos regime's total -/

/-- The constant of `RMF.bandPhi_le_rpow`. -/
noncomputable def bandConst (q η' Kc Ec : ℝ) : ℝ :=
  pfC2 q * (Kc ^ q * (cenClean q ^ q + ((1 + 1 / η') / Real.pi) ^ q) + (Kc * 4e-13) ^ q)
    + pfC1 q * (Kc ^ q * (1 + η') ^ q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
      + (Real.exp 0.0181 / Real.pi) ^ q) + Ec ^ q)
    + pfC1 q * (1.001 * Real.exp 0.0181) ^ (Real.exp 1 * q)

/-- The chain's bound (`RMF.chain_windows_le`):
`min(X + 1.001, 2007) + A(4/3)(X + 1.001)^{3/4} + n₀(log(3X) + 1.001) + T + 2e^{-a'e^X/3}B`. -/
noncomputable def chainW (a' A X B T : ℝ) (n₀ : ℕ) : ℝ :=
  min (X + 1.001) 2007 + A * (4 / 3 * (X + 1.001) ^ (3 / 4 : ℝ))
    + n₀ * (Real.log (3 * X) + 1.001) + T + 2 * Real.exp (-(a' * (Real.exp X / 3))) * B

/-- The chaos regime's total per unit `(log x)^{a/(2q)}`, `a = q(2q-1)`, `P = 1/(2q)`,
`K_c = 2.0913(1+ε)`, `E_c = 0.0012(1+1/ε)`, `C₁ = K_c^q(1+η')^q·pfC1·ω`, `W` the windows' bound:
`topPhi + 12^{1-P}(C_b(k+2) + botPhi + C₁1.5^a(W + 91e^{97a}e^{-aΛ}) + 2(1-P))`. -/
noncomputable def chaosF (q η' ε Λ TS W : ℝ) (k : ℕ) : ℝ :=
  topPhi q + (12 : ℝ) ^ (1 - (2 * q)⁻¹)
    * (bandConst q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) * (k + 2)
      + botPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) Λ TS
      + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q * pfC1 q * omegaClean q
        * (3 / 2 : ℝ) ^ (q * (2 * q - 1))
        * (W + 91 * Real.exp (97 * (q * (2 * q - 1))) * Real.exp (-(q * (2 * q - 1) * Λ)))
      + 2 * (1 - (2 * q)⁻¹))

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
-- the tower's sums, each a short step
/-- **The chaos regime's bound.**  For `½ < q < 1` and `x ≥ 3` with `Λ = log log x ≥ 200`,
`TS ≥ 0` a bound on the bottom's top windows, `a = q(2q-1)`, `a' = a - (2q-1)/1000`,
`A = RMF.chaosAhat q`, a height `X ≥ 5`, `n₀` with `log(3X) < (10/3)2^{n₀}`, `a'e^X/3 ≥ 1`, `k`
with `(10/3)a'2^k ≥ 1`, a bound `B` on every `profSum a A N` and a bound `T` on every
`profSum a A N + e^{1.001a'}e^{-a'N}B`:

`E|S(x)|^{2q} ≤ (log x)^a F^{2q}`, `F = RMF.chaosF` with `W = RMF.chainW`:

the levels' powers `1/(2q)` summed by Hölder against `V_{ℓ+1}^{-1/1000}`, the bands' overheads
along the tower, their windows by the chain lemma, the bottom's ineligible windows by their
depth. -/
theorem integral_rpow_weightedRademacherSum_le_chaosF {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q η' ε x TS Xh B T : ℝ} {n₀ k : ℕ} (hq0 : 1 / 2 < q)
    (hq1 : q < 1) (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x)
    (hΛ : 200 ≤ Real.log (Real.log x)) (hTS0 : 0 ≤ TS)
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS) (hXh : 5 ≤ Xh)
    (hB : ∀ N, profSum (q * (2 * q - 1)) (chaosAhat q) N ≤ B)
    (hn₀ : Real.log (3 * Xh) < 10 / 3 * 2 ^ n₀)
    (hfar : 1 ≤ (q * (2 * q - 1) - (2 * q - 1) / 1000) * (Real.exp Xh / 3))
    (hk : 1 ≤ 10 / 3 * (q * (2 * q - 1) - (2 * q - 1) / 1000) * 2 ^ k)
    (hT : ∀ N : ℕ, profSum (q * (2 * q - 1)) (chaosAhat q) N
      + Real.exp (1.001 * (q * (2 * q - 1) - (2 * q - 1) / 1000))
        * Real.exp (-((q * (2 * q - 1) - (2 * q - 1) / 1000) * N)) * B ≤ T) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ Real.log x ^ (q * (2 * q - 1))
        * chaosF q η' ε (Real.log (Real.log x)) TS
          (chainW (q * (2 * q - 1) - (2 * q - 1) / 1000) (chaosAhat q) Xh B T n₀) k ^ (2 * q) := by
  have main := integral_rpow_weightedRademacherSum_le_chaosLevels hX hq0 hq1.le hη' hε hx3
    (by linarith) hTS
  set Λ := Real.log (Real.log x) with hΛdef
  set L := aboveDepth Λ with hLdef
  set a := q * (2 * q - 1) with hadef
  set P := (2 * q)⁻¹ with hPdef
  set Kc := 2.0913 * (1 + ε) with hKcdef
  set Ec := 0.0012 * (1 + 1 / ε) with hEcdef
  set C₁ := Kc ^ q * (1 + η') ^ q * pfC1 q * omegaClean q with hC₁def
  set a' := a - (2 * q - 1) / 1000 with ha'def
  set A := chaosAhat q with hAdef
  have hq0' : (0 : ℝ) < q := by linarith
  have hδ : 0 < 2 * q - 1 := by linarith
  have ha0 : 0 < a := mul_pos hq0' hδ
  have ha'0 : 0 < a' := by
    rw [ha'def, hadef]
    nlinarith [mul_pos hδ (show (0 : ℝ) < q - 1 / 1000 by linarith)]
  have ha'a : a' ≤ a := by rw [ha'def]; linarith
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have hP1 : P < 1 := by rw [hPdef, inv_lt_one₀ (by positivity)]; linarith
  have hPe : (1 - P) / P = 2 * q - 1 := by
    rw [sub_div, div_self hP0.ne', one_div, hPdef, inv_inv]
  have hKc0 : 0 ≤ Kc := by positivity
  have hEc0 : 0 ≤ Ec := by positivity
  have hC₁0 : 0 ≤ C₁ := by
    have := omegaClean_nonneg hq1.le
    have : 0 ≤ pfC1 q := (Real.exp_pos _).le
    have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc0 _
    have : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
    positivity
  have hA0 : 0 ≤ A := chaosAhat_nonneg hq1
  have hΛ11 : 11 ≤ Λ := by linarith
  have hΛ10 : 10 ≤ 3 * Λ := by linarith
  have hx1 : 1 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos hx1
  obtain ⟨-, hV10⟩ := aboveDepth_spec hΛ10
  rw [← hLdef] at hV10
  have h15 : 0 ≤ (3 / 2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have hB0 : 0 ≤ B := le_trans (profSum_nonneg hA0 0) (hB 0)
  -- the bands, weighted by `V_{ℓ+1}^{(2q-1)/1000}`
  have hband : ∀ ℓ ∈ Finset.range L,
      (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
        + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
          * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))
        * (aboveV Λ (ℓ + 1) ^ (-(1 / 1000 : ℝ))) ^ (-((1 - P) / P))
      ≤ bandConst q η' Kc Ec * aboveV Λ (ℓ + 1) ^ (-a')
        + C₁ * (3 / 2 : ℝ) ^ a * (aboveV Λ (ℓ + 1) ^ (-a')
          * profSum a A (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)))) := by
    intro ℓ hℓ
    have hℓ' := Finset.mem_range.1 hℓ
    have hV := hV10 (ℓ + 1) hℓ'
    have hVpos : 0 < aboveV Λ (ℓ + 1) := by linarith
    have hw : (aboveV Λ (ℓ + 1) ^ (-(1 / 1000 : ℝ))) ^ (-((1 - P) / P))
        = aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000) := by
      rw [← Real.rpow_mul hVpos.le, hPe]
      congr 1
      ring
    have hw0 : 0 ≤ aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000) := Real.rpow_nonneg hVpos.le _
    have hsplit : aboveV Λ (ℓ + 1) ^ (-a) * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000)
        = aboveV Λ (ℓ + 1) ^ (-a') := by
      rw [← Real.rpow_add hVpos, ha'def]
      congr 1
      ring
    have hb : bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
        ≤ bandConst q η' Kc Ec * aboveV Λ (ℓ + 1) ^ (-a) :=
      bandPhi_le_rpow hq0 hq1.le hη' hKc0 hEc0 hV
    have hs : (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
        ≤ (3 / 2 : ℝ) ^ a * aboveV Λ (ℓ + 1) ^ (-a) :=
      scale_rpow_le hx3 hΛ11 ha0.le (Nat.succ_le_of_lt hℓ')
    have hc : chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))
        ≤ profSum a A (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) :=
      chaosWinSum_le_profSum hq0.le hq1 (band_windows_eligible hx3 hΛ hℓ')
    have hc0 := chaosWinSum_nonneg hq1.le (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)))
      (aboveZ x (ℓ + 1))
    have hVa0 : 0 ≤ aboveV Λ (ℓ + 1) ^ (-a) := Real.rpow_nonneg hVpos.le _
    have h1 : bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000)
        ≤ bandConst q η' Kc Ec * aboveV Λ (ℓ + 1) ^ (-a)
          * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000) :=
      mul_le_mul_of_nonneg_right hb hw0
    have h2 : (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
          * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))
        ≤ ((3 / 2 : ℝ) ^ a * aboveV Λ (ℓ + 1) ^ (-a))
          * profSum a A (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) :=
      mul_le_mul hs hc hc0 (mul_nonneg h15 hVa0)
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC₁0) hw0
    rw [hw]
    calc (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))
          * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000)
        = bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000)
          + C₁ * ((3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))
            * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000) := by ring
      _ ≤ bandConst q η' Kc Ec * aboveV Λ (ℓ + 1) ^ (-a)
            * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000)
          + C₁ * (((3 / 2 : ℝ) ^ a * aboveV Λ (ℓ + 1) ^ (-a))
            * profSum a A (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))))
            * aboveV Λ (ℓ + 1) ^ ((2 * q - 1) / 1000) := add_le_add h1 h3
      _ = _ := by rw [← hsplit]; ring
  have hy : ∀ ℓ ∈ Finset.range L, 0 ≤ bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
      + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
        * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)) := by
    intro ℓ hℓ
    have hℓ' := Finset.mem_range.1 hℓ
    obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.succ_le_of_lt hℓ')
    have h1 := (bandPhi_antitoneOn hq0 hq1.le hη' hKc0 hEc0).2 _ (hV10 (ℓ + 1) hℓ')
    have h2 : 0 ≤ (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a :=
      Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) (by linarith)) hlx0.le) _
    have h3 := chaosWinSum_nonneg hq1.le (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)))
      (aboveZ x (ℓ + 1))
    have := mul_nonneg (mul_nonneg hC₁0 h2) h3
    linarith
  have hρ : ∀ ℓ ∈ Finset.range L, 0 < aboveV Λ (ℓ + 1) ^ (-(1 / 1000 : ℝ)) := fun ℓ hℓ =>
    Real.rpow_pos_of_pos (by linarith [hV10 (ℓ + 1) (Finset.mem_range.1 hℓ)]) _
  have hρsum : ∑ ℓ ∈ Finset.range L, aboveV Λ (ℓ + 1) ^ (-(1 / 1000 : ℝ)) ≤ 11 := by
    have := sum_aboveV_rpow_le hΛ10 (b := 1 / 1000) (by norm_num) (k := 9) (by norm_num)
    rw [← hLdef] at this
    push_cast at this
    linarith
  -- the bottom
  obtain ⟨-, -, hl01, -, hl05, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.zero_le L)
  have hlz0 : 1 ≤ Real.log (aboveZ x 0) := by linarith
  have hV0 := hV10 0 (Nat.zero_le _)
  have hV0pos : 0 < aboveV Λ 0 := by linarith
  have hub0 : 0 ≤ (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) (by linarith)) hlx0.le) _
  have hcb0 := chaosWinSum_nonneg hq1.le (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)
  have hyb : 0 ≤ botPhi q η' Kc Ec Λ TS
      + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
        * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0) := by
    have := botPhi_nonneg hq1.le hη' hKc0 hEc0 (by linarith) hTS0 (Λ := Λ)
    have := mul_nonneg (mul_nonneg hC₁0 hub0) hcb0
    linarith
  have hcb : chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)
      ≤ profSum a A (bottomJ 1 2 (aboveZ x 0) - 8)
        + ∑ m ∈ Finset.Ico (botM₀ (aboveZ x 0)) (bottomJ 1 2 (aboveZ x 0) - 8),
          Real.exp (-(a * m)) :=
    chaosWinSum_le_profSum_add hq0.le hq1 (bottom_windows_eligible _)
  have hsb : (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
      ≤ (3 / 2 : ℝ) ^ a * aboveV Λ 0 ^ (-a) :=
    scale_rpow_le hx3 hΛ11 ha0.le (Nat.zero_le _)
  have htail := bottom_tail_le hx1 ha0.le hlz0
  rw [← hΛdef] at htail
  have hVa' : aboveV Λ 0 ^ (-a) ≤ aboveV Λ 0 ^ (-a') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hyb_le : botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)
      ≤ botPhi q η' Kc Ec Λ TS + C₁ * (3 / 2 : ℝ) ^ a * (aboveV Λ 0 ^ (-a') * B)
        + C₁ * (91 * (3 / 2 : ℝ) ^ a * Real.exp (97 * a) * Real.exp (-(a * Λ))) := by
    have e2 : (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * profSum a A (bottomJ 1 2 (aboveZ x 0) - 8)
        ≤ (3 / 2 : ℝ) ^ a * (aboveV Λ 0 ^ (-a') * B) := by
      calc (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
            * profSum a A (bottomJ 1 2 (aboveZ x 0) - 8)
          ≤ ((3 / 2 : ℝ) ^ a * aboveV Λ 0 ^ (-a)) * B :=
            mul_le_mul hsb (hB _) (profSum_nonneg hA0 _)
              (mul_nonneg h15 (Real.rpow_nonneg hV0pos.le _))
        _ ≤ ((3 / 2 : ℝ) ^ a * aboveV Λ 0 ^ (-a')) * B :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVa' h15) hB0
        _ = (3 / 2 : ℝ) ^ a * (aboveV Λ 0 ^ (-a') * B) := by ring
    have e1 := mul_le_mul_of_nonneg_left hcb hub0
    rw [mul_add] at e1
    have h1 : (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)
        ≤ (3 / 2 : ℝ) ^ a * (aboveV Λ 0 ^ (-a') * B)
          + 91 * (3 / 2 : ℝ) ^ a * Real.exp (97 * a) * Real.exp (-(a * Λ)) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC₁0
    have e3 : C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)
        = C₁ * ((3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) := by ring
    rw [e3]
    linarith
  -- the chain of levels and the bands' overheads
  have hchain := chain_windows_le (Λ := Λ) (a := a) (a' := a') (A := A) (X := Xh) (B := B)
    (T := T) (by linarith) ha0.le ha'0 hA0 hXh hB
    (J := fun ℓ => bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1)))
    (fun ℓ hℓ => bandJ_aboveZ_le hx3 hΛ hℓ) hn₀ hfar hT
  rw [← hLdef] at hchain
  have hbsum : ∑ ℓ ∈ Finset.range L, aboveV Λ (ℓ + 1) ^ (-a') ≤ k + 2 := by
    have := sum_aboveV_rpow_le hΛ10 ha'0 hk
    rwa [← hLdef] at this
  have hS := Finset.sum_le_sum hband
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hS
  have hCb0 : 0 ≤ bandConst q η' Kc Ec := by
    have hle : bandPhi q η' Kc Ec 10 ≤ bandConst q η' Kc Ec * (10 : ℝ) ^ (-a) :=
      bandPhi_le_rpow hq0 hq1.le hη' hKc0 hEc0 (le_refl (10 : ℝ))
    have h0 := (bandPhi_antitoneOn hq0 hq1.le hη' hKc0 hEc0).2 10 le_rfl
    have h10 : 0 < (10 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hc
    push Not at hc
    have := mul_neg_of_neg_of_pos hc h10
    linarith
  have hover := mul_le_mul_of_nonneg_left hbsum hCb0
  have hwin := mul_le_mul_of_nonneg_left hchain (mul_nonneg hC₁0 h15)
  -- Hölder over the levels
  have hHol := sum_rpow_add_le (n := L)
    (y := fun ℓ => bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
      + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
        * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))
    (ρ := fun ℓ => aboveV Λ (ℓ + 1) ^ (-(1 / 1000 : ℝ)))
    (yb := botPhi q η' Kc Ec Λ TS
      + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
        * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) hP0 hP1 hy hρ hρsum hyb
  beta_reduce at hHol
  have h12 : 0 ≤ (12 : ℝ) ^ (1 - P) := Real.rpow_nonneg (by norm_num) _
  have hin : ∑ ℓ ∈ Finset.range L,
        (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))
          * (aboveV Λ (ℓ + 1) ^ (-(1 / 1000 : ℝ))) ^ (-((1 - P) / P))
      + (botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) + 2 * (1 - P)
      ≤ bandConst q η' Kc Ec * (k + 2) + botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 : ℝ) ^ a
          * (chainW a' A Xh B T n₀ + 91 * Real.exp (97 * a) * Real.exp (-(a * Λ)))
        + 2 * (1 - P) := by
    change _ ≤ bandConst q η' Kc Ec * (k + 2) + botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 : ℝ) ^ a
          * (min (Xh + 1.001) 2007 + A * (4 / 3 * (Xh + 1.001) ^ (3 / 4 : ℝ))
            + n₀ * (Real.log (3 * Xh) + 1.001) + T
            + 2 * Real.exp (-(a' * (Real.exp Xh / 3))) * B
            + 91 * Real.exp (97 * a) * Real.exp (-(a * Λ)))
        + 2 * (1 - P)
    linarith
  have hF : topPhi q
      + ∑ ℓ ∈ Finset.range L,
        (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))) ^ P
      + (botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) ^ P
      ≤ chaosF q η' ε Λ TS (chainW a' A Xh B T n₀) k := by
    change _ ≤ topPhi q + (12 : ℝ) ^ (1 - P)
      * (bandConst q η' Kc Ec * (k + 2) + botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 : ℝ) ^ a
          * (chainW a' A Xh B T n₀ + 91 * Real.exp (97 * a) * Real.exp (-(a * Λ)))
        + 2 * (1 - P))
    have := mul_le_mul_of_nonneg_left hin h12
    linarith
  have htop0 : 0 ≤ topPhi q := by
    rw [topPhi]
    have : 0 ≤ pfC1 q ^ (2 * q)⁻¹ := Real.rpow_nonneg (Real.exp_pos _).le _
    positivity
  have hbase0 : 0 ≤ topPhi q
      + ∑ ℓ ∈ Finset.range L,
        (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))) ^ P
      + (botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) ^ P := by
    have h1 := Finset.sum_nonneg fun ℓ hℓ => Real.rpow_nonneg (hy ℓ hℓ) P
    have h2 := Real.rpow_nonneg hyb P
    linarith
  refine le_trans main (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase0 hF (by linarith))
    (Real.rpow_nonneg hlx0.le _))

end RMF
