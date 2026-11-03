/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UJensenCellExplicit

/-!
# The first moment near `q = ½`: the windows past `Λ = 6000`

The windows of the assembly `RMF.integral_rpow_weightedRademacherSum_le_u_assembly` for
`q ∈ [0.49, ½)` and `Λ = log log x ≥ 6000`, bounded uniformly in `k` (with room by the chaos,
without it by Jensen, `RMF.uWindowBound_le_uniform`):

* `RMF.uLow_half_le`: the chaos regime's seven groups on `[4, ⌊Λ/4⌋)` in Abel's form, at any
  `a₁ ≥ q(1 - 2q)` and keeping the last group's upper end;
* `RMF.uHigh_groups_le`: `[⌊Λ/4⌋, k_8)` in eight groups `k_g = ⌊L''(1 - θ_g)⌋`,
  `θ_g = (3/4)(3/5)^g`, `L'' = Λ - log Λ - 9`, where `(Λ/n_k)^{1/4} ≤ (0.99θ_{g+1})^{-1/4}`;
* `RMF.uHigh_tail_le`: `[k_8, J₀)` by
  `∑ max(1, L'' - k)^{-1/4} ≤ (4/3)(L''θ_8 + 1)^{3/4} + log Λ + 11`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### Real-variable facts for the windows near `q = ½` -/

/-- `(1 - e^{-y})/y` decreases on `y > 0`: `e^{-y'} = e^{(y'/y)(-y)} ≤ 1 + (y'/y)(e^{-y} - 1)`. -/
lemma one_sub_exp_neg_div_anti {y y' : ℝ} (hy' : 0 < y') (hyy : y' ≤ y) :
    (1 - Real.exp (-y)) / y ≤ (1 - Real.exp (-y')) / y' := by
  have hy : 0 < y := lt_of_lt_of_le hy' hyy
  have hl0 : 0 ≤ y' / y := by positivity
  have hl1 : y' / y ≤ 1 := by rw [div_le_one hy]; exact hyy
  have h := exp_mul_le_one_add_mul (x := -y) hl0 hl1
  have e : y' / y * -y = -y' := by field_simp
  rw [e] at h
  have h3 : y * Real.exp (-y') ≤ y + y' * (Real.exp (-y) - 1) := by
    have := mul_le_mul_of_nonneg_left h hy.le
    rw [mul_add, mul_one, ← mul_assoc, mul_div_cancel₀ _ hy.ne'] at this
    exact this
  rw [div_le_div_iff₀ hy hy']
  linarith

/-- **`∫_s^t e^{-xu}du = (e^{-xs} - e^{-xt})/x` decreases in `x > 0`** for `0 ≤ s ≤ t`. -/
lemma exp_diff_div_anti {x x' s t : ℝ} (hx' : 0 < x') (hxx : x' ≤ x) (hs : 0 ≤ s)
    (hst : s ≤ t) :
    (Real.exp (-(x * s)) - Real.exp (-(x * t))) / x
      ≤ (Real.exp (-(x' * s)) - Real.exp (-(x' * t))) / x' := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx
  rcases eq_or_lt_of_le hst with h | h
  · subst h; simp
  have hd : 0 < t - s := by linarith
  have e1 : ∀ z : ℝ, Real.exp (-(z * s)) - Real.exp (-(z * t))
      = Real.exp (-(z * s)) * (1 - Real.exp (-(z * (t - s)))) := fun z => by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  rw [e1, e1, mul_div_assoc, mul_div_assoc]
  have h1 : Real.exp (-(x * s)) ≤ Real.exp (-(x' * s)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hxx hs))
  have h2 : (1 - Real.exp (-(x * (t - s)))) / x ≤ (1 - Real.exp (-(x' * (t - s)))) / x' := by
    have h0 := one_sub_exp_neg_div_anti (y := x * (t - s)) (y' := x' * (t - s))
      (mul_pos hx' hd) (mul_le_mul_of_nonneg_right hxx hd.le)
    have e2 : ∀ z : ℝ, 0 < z → (1 - Real.exp (-(z * (t - s)))) / z
        = (1 - Real.exp (-(z * (t - s)))) / (z * (t - s)) * (t - s) := fun z hz => by
      field_simp
    rw [e2 x hx, e2 x' hx']
    exact mul_le_mul_of_nonneg_right h0 hd.le
  have h3 : 0 ≤ (1 - Real.exp (-(x * (t - s)))) / x := by
    have : Real.exp (-(x * (t - s))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    exact div_nonneg (by linarith) hx.le
  exact mul_le_mul h1 h2 h3 (Real.exp_pos _).le

/-- A wider interval: `(e^{-xs} - e^{-xt})/x ≤ (e^{-xs'} - e^{-xt'})/x` for `s' ≤ s`, `t ≤ t'`. -/
lemma exp_diff_div_mono {x s t s' t' : ℝ} (hx : 0 < x) (hs : s' ≤ s) (ht : t ≤ t') :
    (Real.exp (-(x * s)) - Real.exp (-(x * t))) / x
      ≤ (Real.exp (-(x * s')) - Real.exp (-(x * t'))) / x := by
  refine div_le_div_of_nonneg_right ?_ hx.le
  have h1 : Real.exp (-(x * s)) ≤ Real.exp (-(x * s')) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hs hx.le))
  have h2 : Real.exp (-(x * t')) ≤ Real.exp (-(x * t)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ht hx.le))
  linarith

/-- `m^{-1/4} ≤ (4/3)(m^{3/4} - (m - 1)^{3/4})` for `m ≥ 1` (Bernoulli for `(1 - 1/m)^{3/4}`). -/
lemma rpow_neg_quarter_le_diff {m : ℝ} (hm : 1 ≤ m) :
    m ^ (-(1 / 4 : ℝ)) ≤ 4 / 3 * (m ^ (3 / 4 : ℝ) - (m - 1) ^ (3 / 4 : ℝ)) := by
  have hm0 : 0 < m := by linarith
  have hs : -1 ≤ -(1 / m) := by
    have : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs (p := 3 / 4) (by norm_num) (by norm_num)
  have h1m : 0 ≤ 1 + -(1 / m) := by linarith
  have e : (m - 1) ^ (3 / 4 : ℝ) = m ^ (3 / 4 : ℝ) * (1 + -(1 / m)) ^ (3 / 4 : ℝ) := by
    rw [← Real.mul_rpow hm0.le h1m]
    congr 1
    field_simp
    ring
  have e2 : m ^ (-(1 / 4 : ℝ)) = m ^ (3 / 4 : ℝ) / m := by
    rw [show -(1 / 4 : ℝ) = 3 / 4 - 1 by norm_num, Real.rpow_sub_one hm0.ne']
  rw [e, e2]
  have hm34 : 0 ≤ m ^ (3 / 4 : ℝ) := Real.rpow_nonneg hm0.le _
  have h := mul_le_mul_of_nonneg_left hb hm34
  have e3 : m ^ (3 / 4 : ℝ) * (1 + 3 / 4 * -(1 / m))
      = m ^ (3 / 4 : ℝ) - 3 / 4 * (m ^ (3 / 4 : ℝ) / m) := by ring
  rw [e3] at h
  linarith

/-- **`∑_{1≤n≤N} n^{-1/4} ≤ (4/3)N^{3/4}`**, by telescoping `RMF.rpow_neg_quarter_le_diff`. -/
lemma sum_rpow_neg_quarter_le (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) ≤ 4 / 3 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := rpow_neg_quarter_le_diff (m := (N : ℝ) + 1) (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith)
    rw [show (N : ℝ) + 1 - 1 = N by ring] at h
    push_cast
    linarith

/-- **Groups of windows in geometric form**: for boundaries `k_0 ≤ k_1 ≤ …` and a window bound
`w_k ≤ e^{-ak}c_g` on `[k_g, k_{g+1})`,
`(1 - e^{-a})∑_{k_0≤k<k_G} w_k ≤ ∑_g c_g(e^{-ak_g} - e^{-ak_{g+1}})`. -/
lemma sum_groups_geom_le {a : ℝ} (ha : 0 < a) {kb : ℕ → ℕ} (hkb : Monotone kb)
    {w : ℕ → ℝ} {c : ℕ → ℝ} (G : ℕ)
    (hw : ∀ g < G, ∀ k ∈ Finset.Ico (kb g) (kb (g + 1)), w k ≤ Real.exp (-(a * k)) * c g) :
    (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico (kb 0) (kb G), w k
      ≤ ∑ g ∈ Finset.range G,
          c g * (Real.exp (-(a * kb g)) - Real.exp (-(a * kb (g + 1)))) := by
  induction G with
  | zero => simp
  | succ G ih =>
    rw [← Finset.sum_Ico_consecutive _ (hkb (Nat.zero_le G)) (hkb (Nat.le_succ G)),
      mul_add, Finset.sum_range_succ]
    have h1 := ih fun g hg => hw g (by omega)
    have h2 := one_sub_exp_neg_mul_sum_le_group ha (hkb (Nat.le_succ G)) (hw G (by omega))
    linarith

/-- The blocks above any offset: `harperBlockCount D y ≥ log log y - 1 - D`. -/
lemma harperBlockCount_ge_sub (D : ℕ) (y : ℝ) :
    Real.log (Real.log y) - 1 - D ≤ (harperBlockCount D y : ℝ) := by
  unfold harperBlockCount
  have h2 := Nat.lt_floor_add_one (Real.log (Real.log y))
  rcases le_total D ⌊Real.log (Real.log y)⌋₊ with h | h
  · rw [Nat.cast_sub h]
    linarith
  · rw [Nat.sub_eq_zero_of_le h]
    have h1 : (⌊Real.log (Real.log y)⌋₊ : ℝ) ≤ D := by exact_mod_cast h
    push_cast
    linarith

/-- **One window by the chaos where it has room and by Jensen where it has not**: with
`(Λ/n_k)^{1/4} ≤ ρ` when `n_k > 0`, and `1 ≤ Λ^{-q/2}A(1-b)^{-b}ρ` when `n_k < N`,
`b_k ≤ e^{-q(1-2q)k}·((3/2)^{-q(1-2q)}Λ^{-q/2}·G·A·(1-b)^{-b}·ρ)`
(`RMF.uWindowBound_le_chaos`, `RMF.uWindowBound_le_jensen`). -/
lemma uWindowBound_le_uniform {x q a b G A ρ : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hq0 : 0 ≤ q) (haq : a ≤ q) (hqb : q ≤ b) (hb : b ≤ 1 / 2) {P : ℕ → WinChaos} {k k₁ : ℕ}
    (hk₁ : k₁ ≤ k) (hk : k ∈ Finset.Ico 4 (tenJ x)) (hPk : (P k).Valid)
    (hG : thetaWindowConstQ (3 / 2) a k₁ (halfY x) ^ b ≤ G)
    (hA : (P k).const (1 / (16 * Real.log (Real.log x))) q
      (Real.exp ((uOffset k : ℝ) - k)) ≤ A)
    (hρ1 : 1 ≤ ρ)
    (hρ : 0 < (harperBlockCount (uOffset k) (halfY x) : ℝ) →
      (Real.log (Real.log x) / harperBlockCount (uOffset k) (halfY x)) ^ (1 / 4 : ℝ) ≤ ρ)
    (hjen : harperBlockCount (uOffset k) (halfY x) < (P k).N →
      1 ≤ Real.log (Real.log x) ^ (-(q / 2)) * (A * (1 - b) ^ (-b) * ρ)) :
    uWindowBound P q x k ≤ Real.exp (-(q * (1 - 2 * q) * k))
      * ((3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
        * (G * A * (1 - b) ^ (-b) * ρ)) := by
  by_cases hroom : (P k).N ≤ harperBlockCount (uOffset k) (halfY x)
  · have hn : 0 < (harperBlockCount (uOffset k) (halfY x) : ℝ) := by
      have h1 : (2000 : ℝ) ≤ ((P k).N : ℝ) := by exact_mod_cast hPk.N
      have h2 : ((P k).N : ℝ) ≤ (harperBlockCount (uOffset k) (halfY x) : ℝ) := by
        exact_mod_cast hroom
      linarith
    exact uWindowBound_le_chaos hx hq0 haq hqb hb hk₁ hk hPk hroom hG hA hρ1 (hρ hn) hn
  · have hJ := uWindowBound_le_jensen hx hq0 haq hqb hb hk₁ hk hPk hG
    have h1 := hjen (lt_of_not_ge hroom)
    obtain ⟨-, hly⟩ := halfY_loglog_le hx
    have hG0 : 0 ≤ G := le_trans (Real.rpow_nonneg (le_trans zero_le_one
      (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) k₁ (halfY x))) _) hG
    have hTH : 0 ≤ (3 / 2 : ℝ) ^ (-(q * (1 - 2 * q))) := Real.rpow_nonneg (by norm_num) _
    refine le_trans hJ (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    calc (3 / 2 : ℝ) ^ (-(q * (1 - 2 * q))) * G = (3 / 2) ^ (-(q * (1 - 2 * q))) * G * 1 := by
          ring
      _ ≤ (3 / 2) ^ (-(q * (1 - 2 * q))) * G
          * (Real.log (Real.log x) ^ (-(q / 2)) * (A * (1 - b) ^ (-b) * ρ)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hTH hG0)
      _ = _ := by ring

/-- **The power sum past a real point**: for `a ≤ M = ⌊L⌋ ≤ b`,
`∑_{a≤k<b} max(1, L - k)^{-1/4} ≤ (4/3)(M - a)^{3/4} + (b - M)`. -/
lemma sum_max_rpow_neg_quarter_le {L : ℝ} {a b : ℕ} (hL : 0 ≤ L) (ha : a ≤ ⌊L⌋₊)
    (hb : ⌊L⌋₊ ≤ b) :
    ∑ k ∈ Finset.Ico a b, (max 1 (L - k)) ^ (-(1 / 4 : ℝ))
      ≤ 4 / 3 * ((⌊L⌋₊ - a : ℕ) : ℝ) ^ (3 / 4 : ℝ) + ((b - ⌊L⌋₊ : ℕ) : ℝ) := by
  set M := ⌊L⌋₊ with hMdef
  have hML : (M : ℝ) ≤ L := Nat.floor_le hL
  rw [← Finset.sum_Ico_consecutive _ ha hb]
  refine add_le_add ?_ ?_
  · -- `max(1, L - k) ≥ M - k ≥ 1` for `k < M`, then `n^{-1/4}` summed
    have h1 : ∑ k ∈ Finset.Ico a M, (max 1 (L - k)) ^ (-(1 / 4 : ℝ))
        ≤ ∑ k ∈ Finset.Ico a M, ((M - k : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hkM := (Finset.mem_Ico.1 hk).2
      have hc : ((M - k : ℕ) : ℝ) = (M : ℝ) - k := by rw [Nat.cast_sub hkM.le]
      have h1 : (1 : ℝ) ≤ ((M - k : ℕ) : ℝ) := by
        have : 1 ≤ M - k := by omega
        exact_mod_cast this
      refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by norm_num)
      rw [hc]
      exact le_trans (by linarith) (le_max_right _ _)
    refine le_trans h1 (le_of_eq_of_le ?_ (sum_rpow_neg_quarter_le (M - a)))
    rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have e : M - (a + (M - a - 1 - i)) = i + 1 := by omega
    rw [e]
    push_cast
    ring_nf
  · calc ∑ k ∈ Finset.Ico M b, (max 1 (L - k)) ^ (-(1 / 4 : ℝ))
        ≤ ∑ _k ∈ Finset.Ico M b, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ =>
            Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by norm_num)
      _ = ((b - M : ℕ) : ℝ) := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]

/-! ### The high windows near `q = ½` -/

/-- The high windows' group ends in `1 - k/L''`: `θ_g = (3/4)(3/5)^g`. -/
noncomputable def halfTheta (g : ℕ) : ℝ := 3 / 4 * (3 / 5) ^ g

/-- `L'' = Λ - log Λ - 9`, below `n_k + k` for the windows `k ≥ 97`. -/
noncomputable def halfLpp (x : ℝ) : ℝ :=
  Real.log (Real.log x) - Real.log (Real.log (Real.log x)) - 9

/-- The high groups' boundaries: `⌊Λ/4⌋`, then `⌊L''(1 - θ_g)⌋`. -/
noncomputable def halfKb (x : ℝ) (g : ℕ) : ℕ :=
  if g = 0 then ⌊Real.log (Real.log x) / 4⌋₊ else ⌊halfLpp x * (1 - halfTheta g)⌋₊

/-- The groups' `ρ`: `(0.99 θ_g)^{-1/4}`. -/
noncomputable def halfRho (g : ℕ) : ℝ := Real.exp (-(1 / 4 * Real.log (99 / 100 * halfTheta g)))

lemma halfTheta_pos (g : ℕ) : 0 < halfTheta g := by unfold halfTheta; positivity

lemma halfTheta_le (g : ℕ) : halfTheta g ≤ 3 / 4 := by
  unfold halfTheta
  have : (3 / 5 : ℝ) ^ g ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma halfTheta_anti : Antitone halfTheta := fun g g' h => by
  unfold halfTheta
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num) h
  linarith

/-- `0.99Λ ≤ L'' ≤ Λ` past `Λ = 6000`. -/
lemma halfLpp_bounds {x : ℝ} (hΛ : 6000 ≤ Real.log (Real.log x)) :
    99 / 100 * Real.log (Real.log x) ≤ halfLpp x ∧ halfLpp x ≤ Real.log (Real.log x) := by
  have hlog := log_le_div_four_hundred (by linarith : (4000 : ℝ) ≤ Real.log (Real.log x))
  have hl0 : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg (by linarith)
  unfold halfLpp
  constructor <;> linarith

/-- `n_k ≥ L'' - k` for the windows `k ≥ 97` (`n_k` the blocks above the window). -/
lemma halfLpp_sub_le {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) {k : ℕ} (hk : 97 ≤ k) :
    halfLpp x - k ≤ (harperBlockCount (uOffset k) (halfY x) : ℝ) := by
  have h := harperBlockCount_ge_sub (uOffset k) (halfY x)
  have hll := halfY_loglog_ge_sub hx
  rw [uOffset_of_ge hk] at h ⊢
  push_cast at h
  unfold halfLpp
  linarith

lemma halfKb_mono {x : ℝ} (hΛ : 6000 ≤ Real.log (Real.log x)) : Monotone (halfKb x) := by
  obtain ⟨hL1, -⟩ := halfLpp_bounds hΛ
  have hL0 : 0 ≤ halfLpp x := by linarith
  intro g g' h
  unfold halfKb
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · rcases Nat.eq_zero_or_pos g' with rfl | hg'
    · exact le_rfl
    · rw [if_pos rfl, if_neg hg'.ne']
      refine Nat.floor_le_floor ?_
      have := halfTheta_anti (show 1 ≤ g' by omega)
      have h1 : halfTheta 1 = 9 / 20 := by unfold halfTheta; norm_num
      have : halfLpp x * (1 - 9 / 20) ≤ halfLpp x * (1 - halfTheta g') :=
        mul_le_mul_of_nonneg_left (by linarith) hL0
      linarith
  · rw [if_neg hg.ne', if_neg (by omega)]
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left (by linarith [halfTheta_anti h]) hL0)

/-- The group ends below `L''`: `halfKb g ≤ L''(1 - θ_g)` for `g ≥ 1`, and `halfKb g ≤ ⌊L''⌋`. -/
lemma halfKb_le {x : ℝ} (hΛ : 6000 ≤ Real.log (Real.log x)) {g : ℕ} (hg : 1 ≤ g) :
    (halfKb x g : ℝ) ≤ halfLpp x * (1 - halfTheta g) ∧ halfKb x g ≤ ⌊halfLpp x⌋₊ := by
  obtain ⟨hL1, -⟩ := halfLpp_bounds hΛ
  have hL0 : 0 ≤ halfLpp x := by linarith
  have hθ := halfTheta_pos g
  have hθ1 := halfTheta_le g
  unfold halfKb
  rw [if_neg (by omega)]
  have h0 : 0 ≤ halfLpp x * (1 - halfTheta g) := mul_nonneg hL0 (by linarith)
  refine ⟨Nat.floor_le h0, Nat.floor_le_floor ?_⟩
  have := mul_le_mul_of_nonneg_left (by linarith : 1 - halfTheta g ≤ 1) hL0
  linarith

/-- The group starts from below: `halfKb g ≥ L''(1 - θ_g) - 1` for `g ≥ 1`. -/
lemma halfKb_ge {x : ℝ} (g : ℕ) (hg : 1 ≤ g) :
    halfLpp x * (1 - halfTheta g) - 1 ≤ (halfKb x g : ℝ) := by
  unfold halfKb
  rw [if_neg (by omega)]
  have := Nat.lt_floor_add_one (halfLpp x * (1 - halfTheta g))
  linarith

set_option maxHeartbeats 1000000 in
-- the four hypotheses of `RMF.uWindowBound_le_uniform`
/-- **A high window near `q = ½`**: for `k ≥ ⌊Λ/4⌋` with the parameters `c₇` (chaos constant `≤ A₇`
at level shift `e⁸`, window constant `≤ G₇`, `N ≤ (A₇(1-q_u)^{-q_u})⁴`),
`b_k ≤ e^{-ak}(3/2)^{-a}Λ^{-q/2}·G₇A₇(1-q_u)^{-q_u}·(Λ/max(1, L'' - k))^{1/4}`, with room or
without. -/
lemma uHighWindow_le {x q ql qu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hq0 : 0 ≤ q) (hqlq : ql ≤ q) (hqqu : q ≤ qu)
    (hqu : qu ≤ 1 / 2) {c₇ : WinChaos} (hv₇ : c₇.Valid) {P : ℕ → WinChaos}
    (hP : ∀ k, 97 ≤ k → P k = c₇) {A₇ G₇ : ℝ}
    (hA₇ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      c₇.const E₀ q K ≤ A₇)
    (hG₇ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 97 y ^ qu ≤ G₇)
    (hN : (c₇.N : ℝ) ≤ (A₇ * (1 - qu) ^ (-qu)) ^ 4) {k : ℕ}
    (hk : k ∈ Finset.Ico (halfKb x 0) (tenJ x)) :
    uWindowBound P q x k ≤ Real.exp (-(q * (1 - 2 * q) * k))
      * ((3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
        * (G₇ * A₇ * (1 - qu) ^ (-qu)
          * (Real.log (Real.log x) / max 1 (halfLpp x - k)) ^ (1 / 4 : ℝ))) := by
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hL1, hL2⟩ := halfLpp_bounds hΛ
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hk' := Finset.mem_Ico.1 hk
  have hK97 : 97 ≤ halfKb x 0 := by
    unfold halfKb
    rw [if_pos rfl]
    exact Nat.le_floor (by push_cast; linarith)
  have hk97 : 97 ≤ k := le_trans hK97 hk'.1
  have hkJ : k ∈ Finset.Ico 4 (tenJ x) := Finset.mem_Ico.2 ⟨by omega, hk'.2⟩
  have hPk : P k = c₇ := hP k hk97
  set m := max 1 (halfLpp x - k) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmΛ : m ≤ Λ := max_le (by linarith) (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  have hn := halfLpp_sub_le hx hk97
  have hA : (P k).const (1 / (16 * Λ)) q (Real.exp ((uOffset k : ℝ) - k)) ≤ A₇ := by
    rw [hPk]
    refine hA₇ _ (by positivity) ?_ _ (Real.exp_pos _).le (Real.exp_le_exp.2 ?_)
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    · rw [uOffset_of_ge hk97]; push_cast; linarith
  have hρ1 : 1 ≤ (Λ / m) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by rw [le_div_iff₀ (by linarith)]; linarith) (by norm_num)
  have hρ : 0 < (harperBlockCount (uOffset k) (halfY x) : ℝ) →
      (Λ / harperBlockCount (uOffset k) (halfY x)) ^ (1 / 4 : ℝ) ≤ (Λ / m) ^ (1 / 4 : ℝ) := by
    intro hn0
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    refine div_le_div_of_nonneg_left hΛ0.le (by linarith) (max_le ?_ hn)
    have : (1 : ℕ) ≤ harperBlockCount (uOffset k) (halfY x) := by
      have := hn0
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
        intro h0; rw [h0] at this; simp at this)
    exact_mod_cast this
  have hjen : harperBlockCount (uOffset k) (halfY x) < (P k).N →
      1 ≤ Λ ^ (-(q / 2)) * (A₇ * (1 - qu) ^ (-qu) * (Λ / m) ^ (1 / 4 : ℝ)) := by
    intro hlt
    rw [hPk] at hlt
    have hmN : m ≤ (c₇.N : ℝ) := by
      refine max_le ?_ ?_
      · have : (2000 : ℝ) ≤ c₇.N := by exact_mod_cast hv₇.N
        linarith
      · have : (harperBlockCount (uOffset k) (halfY x) : ℝ) ≤ c₇.N := by exact_mod_cast hlt.le
        linarith
    set A' := A₇ * (1 - qu) ^ (-qu) with hA'def
    have hA₇0 : 0 ≤ A₇ := by
      refine le_trans ?_ (hA₇ 0 le_rfl (by norm_num) 1 zero_le_one (Real.one_le_exp (by norm_num)))
      have hl := hv₇.lam
      unfold WinChaos.const shiftMomentConst
      exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
    have hA'0 : 0 ≤ A' := mul_nonneg hA₇0 (Real.rpow_nonneg (by linarith) _)
    have hm0 : 0 < m := by linarith
    -- `m^{1/4} ≤ A'`
    have h3 : m ^ (1 / 4 : ℝ) ≤ A' := by
      calc m ^ (1 / 4 : ℝ) ≤ (A' ^ 4) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow hm0.le (le_trans hmN hN) (by norm_num)
        _ = A' := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hA'0]
            norm_num
    have h4 : 1 ≤ A' * m ^ (-(1 / 4 : ℝ)) := by
      rw [Real.rpow_neg hm0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hm0 _)]
      linarith
    -- `Λ^{-q/2}(Λ/m)^{1/4} = Λ^{1/4-q/2}m^{-1/4}`, and `Λ^{1/4-q/2} ≥ 1`
    have e : Λ ^ (-(q / 2)) * (Λ / m) ^ (1 / 4 : ℝ)
        = Λ ^ (1 / 4 - q / 2 : ℝ) * m ^ (-(1 / 4 : ℝ)) := by
      rw [show (1 / 4 - q / 2 : ℝ) = -(q / 2) + 1 / 4 by ring, Real.rpow_add hΛ0,
        Real.div_rpow hΛ0.le hm0.le, Real.rpow_neg hm0.le]
      ring
    have h1 : 1 ≤ Λ ^ (1 / 4 - q / 2 : ℝ) := Real.one_le_rpow (by linarith) (by linarith)
    have h5 : A' * m ^ (-(1 / 4 : ℝ)) ≤ Λ ^ (-(q / 2)) * (A' * (Λ / m) ^ (1 / 4 : ℝ)) := by
      rw [show Λ ^ (-(q / 2)) * (A' * (Λ / m) ^ (1 / 4 : ℝ))
        = A' * (Λ ^ (-(q / 2)) * (Λ / m) ^ (1 / 4 : ℝ)) by ring, e]
      have h6 : 0 ≤ A' * m ^ (-(1 / 4 : ℝ)) := mul_nonneg hA'0 (Real.rpow_nonneg hm0.le _)
      calc A' * m ^ (-(1 / 4 : ℝ)) = A' * m ^ (-(1 / 4 : ℝ)) * 1 := by ring
        _ ≤ A' * m ^ (-(1 / 4 : ℝ)) * Λ ^ (1 / 4 - q / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left h1 h6
        _ = A' * (Λ ^ (1 / 4 - q / 2 : ℝ) * m ^ (-(1 / 4 : ℝ))) := by ring
    linarith
  have h := uWindowBound_le_uniform hx hq0 hqlq hqqu hqu hk97 hkJ (by rw [hPk]; exact hv₇)
    (hG₇ _ hly) hA hρ1 hρ hjen
  exact h

/-- **Seven groups on `[4, K)` keeping the upper end**: `RMF.sum_seven_groups_le_of` with the
last group's `-c₇e^{-aK} ≤ -c₇E` for `E ≤ e^{-aK}`. -/
lemma sum_seven_groups_le_top {a a₀ a₁ Et : ℝ} (ha : 0 < a) (ha₀ : a₀ ≤ a) (ha₁ : a ≤ a₁)
    {K : ℕ} (hK : 97 ≤ K) (hEt : Et ≤ Real.exp (-(a * K))) {w : ℕ → ℝ}
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : ℝ} (h12 : c₂ ≤ c₁) (h23 : c₃ ≤ c₂)
    (h34 : c₄ ≤ c₃) (h45 : c₅ ≤ c₄) (h56 : c₆ ≤ c₅) (h67 : c₇ ≤ c₆) (h7 : 0 ≤ c₇)
    (hw1 : ∀ k ∈ Finset.Ico 4 5, w k ≤ Real.exp (-(a * k)) * c₁)
    (hw2 : ∀ k ∈ Finset.Ico 5 6, w k ≤ Real.exp (-(a * k)) * c₂)
    (hw3 : ∀ k ∈ Finset.Ico 6 7, w k ≤ Real.exp (-(a * k)) * c₃)
    (hw4 : ∀ k ∈ Finset.Ico 7 31, w k ≤ Real.exp (-(a * k)) * c₄)
    (hw5 : ∀ k ∈ Finset.Ico 31 61, w k ≤ Real.exp (-(a * k)) * c₅)
    (hw6 : ∀ k ∈ Finset.Ico 61 97, w k ≤ Real.exp (-(a * k)) * c₆)
    (hw7 : ∀ k ∈ Finset.Ico 97 K, w k ≤ Real.exp (-(a * k)) * c₇) :
    (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico 4 K, w k
      ≤ c₁ * Real.exp (-(4 * a₀)) - (c₁ - c₂) * Real.exp (-(5 * a₁))
        - (c₂ - c₃) * Real.exp (-(6 * a₁)) - (c₃ - c₄) * Real.exp (-(7 * a₁))
        - (c₄ - c₅) * Real.exp (-(31 * a₁)) - (c₅ - c₆) * Real.exp (-(61 * a₁))
        - (c₆ - c₇) * Real.exp (-(97 * a₁)) - c₇ * Et := by
  have e1 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 4 ≤ 5) hw1
  have e2 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 5 ≤ 6) hw2
  have e3 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 6 ≤ 7) hw3
  have e4 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 7 ≤ 31) hw4
  have e5 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 31 ≤ 61) hw5
  have e6 := one_sub_exp_neg_mul_sum_le_group ha (by norm_num : 61 ≤ 97) hw6
  have e7 := one_sub_exp_neg_mul_sum_le_group ha hK hw7
  have hs : ∑ k ∈ Finset.Ico 4 K, w k = ∑ k ∈ Finset.Ico 4 5, w k + ∑ k ∈ Finset.Ico 5 6, w k
      + ∑ k ∈ Finset.Ico 6 7, w k + ∑ k ∈ Finset.Ico 7 31, w k + ∑ k ∈ Finset.Ico 31 61, w k
      + ∑ k ∈ Finset.Ico 61 97, w k + ∑ k ∈ Finset.Ico 97 K, w k := by
    rw [Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 5) (by norm_num : 5 ≤ 6),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 6) (by norm_num : 6 ≤ 7),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 7) (by norm_num : 7 ≤ 31),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 31) (by norm_num : 31 ≤ 61),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 61) (by norm_num : 61 ≤ 97),
      Finset.sum_Ico_consecutive _ (by norm_num : 4 ≤ 97) hK]
  have x4 : Real.exp (-(a * ((4 : ℕ) : ℝ))) ≤ Real.exp (-(4 * a₀)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  have hx : ∀ n : ℕ, Real.exp (-(n * a₁)) ≤ Real.exp (-(a * (n : ℝ))) := fun n =>
    Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have x5 := hx 5
  have x6 := hx 6
  have x7 := hx 7
  have x31 := hx 31
  have x61 := hx 61
  have x97 := hx 97
  push_cast at x4 x5 x6 x7 x31 x61 x97 e1 e2 e3 e4 e5 e6 e7 hEt ⊢
  rw [hs]
  have d12 : 0 ≤ c₁ - c₂ := by linarith
  have d23 : 0 ≤ c₂ - c₃ := by linarith
  have d34 : 0 ≤ c₃ - c₄ := by linarith
  have d45 : 0 ≤ c₄ - c₅ := by linarith
  have d56 : 0 ≤ c₅ - c₆ := by linarith
  have d67 : 0 ≤ c₆ - c₇ := by linarith
  have hc1 : 0 ≤ c₁ := by linarith
  have t1 := mul_le_mul_of_nonneg_left x4 hc1
  have t5 := mul_le_mul_of_nonneg_left x5 d12
  have t6 := mul_le_mul_of_nonneg_left x6 d23
  have t7 := mul_le_mul_of_nonneg_left x7 d34
  have t31 := mul_le_mul_of_nonneg_left x31 d45
  have t61 := mul_le_mul_of_nonneg_left x61 d56
  have t97 := mul_le_mul_of_nonneg_left x97 d67
  have tK := mul_le_mul_of_nonneg_left hEt h7
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  linarith

set_option maxHeartbeats 4000000 in
-- seven groups, each discharged by the same lemma
/-- **The low windows near `q = ½`**: the chaos regime's groups on `[4, ⌊Λ/4⌋)` in Abel's form at
any `a₁ ≥ a`, keeping the last group's upper end `-b₇E`, `E ≤ e^{-a⌊Λ/4⌋}` (`RMF.uMeso_chaos_le`'s
groups for `q < ½`). -/
theorem uLow_half_le {x q ql qu a₁ Et : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu)
    (hqu : qu ≤ 1 / 2) (hq : q < 1 / 2) (ha₁' : q * (1 - 2 * q) ≤ a₁)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} (hv₁ : c₁.Valid)
    (hv₂ : c₂.Valid)
    (hv₃ : c₃.Valid) (hv₄ : c₄.Valid) (hv₅ : c₅.Valid) (hv₆ : c₆.Valid) (hv₇ : c₇.Valid)
    (hN₁ : c₁.N ≤ 2980) (hN₂ : c₂.N ≤ 2980) (hN₃ : c₃.N ≤ 2980) (hN₄ : c₄.N ≤ 2980)
    (hN₅ : c₅.N ≤ 2980) (hN₆ : c₆.N ≤ 2980) (hN₇ : c₇.N ≤ 2980)
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ G₁ G₂ G₃ G₄ G₅ G₆ G₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℝ}
    (hA₁ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 101 →
      c₁.const E₀ q K ≤ A₁)
    (hA₂ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 100 →
      c₂.const E₀ q K ≤ A₂)
    (hA₃ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 99 →
      c₃.const E₀ q K ≤ A₃)
    (hA₄ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 98 →
      c₄.const E₀ q K ≤ A₄)
    (hA₅ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 74 →
      c₅.const E₀ q K ≤ A₅)
    (hA₆ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 44 →
      c₆.const E₀ q K ≤ A₆)
    (hA₇ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      c₇.const E₀ q K ≤ A₇)
    (hG₁ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 4 y ^ qu ≤ G₁)
    (hG₂ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 5 y ^ qu ≤ G₂)
    (hG₃ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 6 y ^ qu ≤ G₃)
    (hG₄ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 7 y ^ qu ≤ G₄)
    (hG₅ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 31 y ^ qu ≤ G₅)
    (hG₆ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 61 y ^ qu ≤ G₆)
    (hG₇ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 97 y ^ qu ≤ G₇)
    (hb₁ : G₁ * A₁ * (1 - qu) ^ (-qu) * (10075 / 10000) ≤ b₁)
    (hb₂ : G₂ * A₂ * (1 - qu) ^ (-qu) * (10075 / 10000) ≤ b₂)
    (hb₃ : G₃ * A₃ * (1 - qu) ^ (-qu) * (10075 / 10000) ≤ b₃)
    (hb₄ : G₄ * A₄ * (1 - qu) ^ (-qu) * (10075 / 10000) ≤ b₄)
    (hb₅ : G₅ * A₅ * (1 - qu) ^ (-qu) * (10075 / 10000) ≤ b₅)
    (hb₆ : G₆ * A₆ * (1 - qu) ^ (-qu) * (10075 / 10000) ≤ b₆)
    (hb₇ : G₇ * A₇ * (1 - qu) ^ (-qu) * (10763 / 10000) ≤ b₇)
    (h12 : b₂ ≤ b₁) (h23 : b₃ ≤ b₂) (h34 : b₄ ≤ b₃) (h45 : b₅ ≤ b₄) (h56 : b₆ ≤ b₅)
    (h67 : b₇ ≤ b₆)
    (hEt : Et ≤ Real.exp (-(q * (1 - 2 * q) * ⌊Real.log (Real.log x) / 4⌋₊))) :
    (1 - Real.exp (-(q * (1 - 2 * q))))
        * ∑ k ∈ Finset.Ico 4 ⌊Real.log (Real.log x) / 4⌋₊,
          uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
      ≤ (3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
          * (b₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
            - (b₁ - b₂) * Real.exp (-(5 * a₁))
            - (b₂ - b₃) * Real.exp (-(6 * a₁))
            - (b₃ - b₄) * Real.exp (-(7 * a₁))
            - (b₄ - b₅) * Real.exp (-(31 * a₁))
            - (b₅ - b₆) * Real.exp (-(61 * a₁))
            - (b₆ - b₇) * Real.exp (-(97 * a₁)) - b₇ * Et) := by
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  set Λ := Real.log (Real.log x) with hΛdef
  set a := q * (1 - 2 * q) with hadef
  have hq0 : 0 ≤ q := by linarith
  have ha : 0 < a := by
    have h1 : (0 : ℝ) < 1 - 2 * q := by linarith
    have h2 : (0 : ℝ) < q := by linarith
    exact mul_pos h2 h1
  have ha₀ : qu * (1 - 2 * qu) ≤ a := mul_one_sub_two_mul_anti (by linarith) hqqu
  have ha₁ : a ≤ a₁ := ha₁'
  set K4 := ⌊Λ / 4⌋₊ with hK4def
  have hK4R : (K4 : ℝ) ≤ Λ / 4 := Nat.floor_le (by linarith)
  have hK97 : 97 ≤ K4 := Nat.le_floor (by push_cast; linarith)
  set P := uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ with hPdef
  set C := (3 / 2 : ℝ) ^ (-a) * Λ ^ (-(q / 2)) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by linarith) _)
  -- nonnegativity of the last group's constants
  have hG₇0 : 0 ≤ G₇ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) 97 (halfY x))) _)
    (hG₇ _ hly)
  have hA₇0 : 0 ≤ A₇ := by
    refine le_trans ?_ (hA₇ 0 le_rfl (by norm_num) 1 zero_le_one (Real.one_le_exp (by norm_num)))
    have hl := hv₇.lam
    unfold WinChaos.const shiftMomentConst
    exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
  have hb₇0 : 0 ≤ b₇ := le_trans (by
    have : 0 ≤ (1 - qu) ^ (-qu) := Real.rpow_nonneg (by linarith) _
    positivity) hb₇
  -- the offsets and the blocks above the windows
  have hρlow : ∀ k : ℕ, k < 97 →
      Λ ≤ (10075 / 10000) ^ 4 * (harperBlockCount (uOffset k) (halfY x) : ℝ) := by
    intro k hk
    have hD : (uOffset k : ℝ) ≤ Λ / 2 := by rw [uOffset_of_lt hk]; push_cast; linarith
    have hn := harperBlockCount_halfY_ge hx hΛ hD
    rw [← hΛdef] at hn
    rw [uOffset_of_lt hk] at hn ⊢
    push_cast at hn
    exact rho_low hΛ hn
  have hρhigh : ∀ k : ℕ, 97 ≤ k → (k : ℝ) ≤ Λ / 4 →
      Λ ≤ (10763 / 10000) ^ 4 * (harperBlockCount (uOffset k) (halfY x) : ℝ) := by
    intro k hk hkΛ
    have hD : (uOffset k : ℝ) ≤ Λ / 2 := by rw [uOffset_of_ge hk]; push_cast; linarith
    have hn := harperBlockCount_halfY_ge hx hΛ hD
    rw [← hΛdef] at hn
    rw [uOffset_of_ge hk] at hn ⊢
    push_cast at hn
    exact rho_high hΛ (by linarith)
  -- one group at a time
  have grp : ∀ {c : WinChaos} {s t : ℕ} {ℓK A G ρ b : ℝ}, c.Valid → c.N ≤ 2980 → 4 ≤ s →
      (t : ℝ) ≤ Λ / 4 + 1 → (∀ k ∈ Finset.Ico s t, P k = c) →
      (∀ k ∈ Finset.Ico s t, (uOffset k : ℝ) - k ≤ ℓK) →
      (∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp ℓK →
        c.const E₀ q K ≤ A) →
      (∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql s y ^ qu ≤ G) →
      1 ≤ ρ → (∀ k ∈ Finset.Ico s t,
        Λ ≤ ρ ^ 4 * (harperBlockCount (uOffset k) (halfY x) : ℝ)) →
      G * A * (1 - qu) ^ (-qu) * ρ ≤ b →
      ∀ k ∈ Finset.Ico s t, uWindowBound P q x k ≤ Real.exp (-(a * k)) * (C * b) := by
    intro c s t ℓK A G ρ b hc hcN hs4 ht hP hK hA hG hρ1 hρ hb k hk
    have h := uWindow_group_le hx hΛ hq0 hqlq hqqu (by linarith) hc hcN hs4 ht hP hK hA hG hρ1
      hρ k hk
    have hG0 : 0 ≤ G := le_trans (Real.rpow_nonneg (le_trans zero_le_one
      (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) s (halfY x))) _)
      (hG _ hly)
    refine le_trans h ?_
    rw [← hadef] at h ⊢
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hb hC0
  have hPk : ∀ k : ℕ, P k = uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ k := fun k => rfl
  have w1 := grp (s := 4) (t := 5) (ℓK := 101) hv₁ hN₁ le_rfl (by push_cast; linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups; rw [if_pos (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_lt (by omega)]
      have : (4 : ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast; linarith)
    hA₁ hG₁ (by norm_num) (fun k hk => hρlow k (by rw [Finset.mem_Ico] at hk; omega)) hb₁
  have w2 := grp (s := 5) (t := 6) (ℓK := 100) hv₂ hN₂ (by norm_num) (by push_cast; linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_pos (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_lt (by omega)]
      have : (5 : ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast; linarith)
    hA₂ hG₂ (by norm_num) (fun k hk => hρlow k (by rw [Finset.mem_Ico] at hk; omega)) hb₂
  have w3 := grp (s := 6) (t := 7) (ℓK := 99) hv₃ hN₃ (by norm_num) (by push_cast; linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_lt (by omega)]
      have : (6 : ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast; linarith)
    hA₃ hG₃ (by norm_num) (fun k hk => hρlow k (by rw [Finset.mem_Ico] at hk; omega)) hb₃
  have w4 := grp (s := 7) (t := 31) (ℓK := 98) hv₄ hN₄ (by norm_num) (by push_cast; linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_lt (by omega)]
      have : (7 : ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast; linarith)
    hA₄ hG₄ (by norm_num) (fun k hk => hρlow k (by rw [Finset.mem_Ico] at hk; omega)) hb₄
  have w5 := grp (s := 31) (t := 61) (ℓK := 74) hv₅ hN₅ (by norm_num) (by push_cast; linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_lt (by omega)]
      have : (31 : ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast; linarith)
    hA₅ hG₅ (by norm_num) (fun k hk => hρlow k (by rw [Finset.mem_Ico] at hk; omega)) hb₅
  have w6 := grp (s := 61) (t := 97) (ℓK := 44) hv₆ hN₆ (by norm_num) (by push_cast; linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_lt (by omega)]
      have : (61 : ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast; linarith)
    hA₆ hG₆ (by norm_num) (fun k hk => hρlow k (by rw [Finset.mem_Ico] at hk; omega)) hb₆
  have w7 := grp (s := 97) (t := K4) (ℓK := 8) hv₇ hN₇ (by norm_num) (by linarith)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)])
    (fun k hk => by
      rw [Finset.mem_Ico] at hk; rw [uOffset_of_ge hk.1]; push_cast; linarith)
    hA₇ hG₇ (by norm_num)
    (fun k hk => by
      rw [Finset.mem_Ico] at hk
      refine hρhigh k hk.1 ?_
      have : ((k + 1 : ℕ) : ℝ) ≤ (K4 : ℝ) := by exact_mod_cast hk.2
      push_cast at this
      linarith) hb₇
  have hsum1 := sum_seven_groups_le_top ha ha₀ ha₁ hK97 hEt
    (w := fun k => uWindowBound P q x k)
    (mul_le_mul_of_nonneg_left h12 hC0) (mul_le_mul_of_nonneg_left h23 hC0)
    (mul_le_mul_of_nonneg_left h34 hC0) (mul_le_mul_of_nonneg_left h45 hC0)
    (mul_le_mul_of_nonneg_left h56 hC0) (mul_le_mul_of_nonneg_left h67 hC0)
    (mul_nonneg hC0 hb₇0) w1 w2 w3 w4 w5 w6 w7
  refine le_trans hsum1 (le_of_eq ?_)
  ring

/-- `⌊L''⌋ < J₀`: `J₀ > log log y + log(2/3) ≥ Λ - log Λ - 1/2 > L''`. -/
lemma floor_halfLpp_lt_tenJ {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) : ⌊halfLpp x⌋₊ < tenJ x := by
  obtain ⟨hL1, -⟩ := halfLpp_bounds hΛ
  have hll := halfY_loglog_ge_sub hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  have hlogy : 0 < Real.log (halfY x) := by linarith
  have hJ : Real.log (2 / 3 * Real.log (halfY x)) < ((tenJ x : ℕ) : ℝ) := by
    unfold tenJ; push_cast; exact Nat.lt_floor_add_one _
  have h23 : Real.log (2 / 3 * Real.log (halfY x))
      = Real.log (2 / 3) + Real.log (Real.log (halfY x)) :=
    Real.log_mul (by norm_num) hlogy.ne'
  have h32 : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have e32 : Real.log (2 / 3) = -Real.log (3 / 2) := by
    rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  have hfl : (⌊halfLpp x⌋₊ : ℝ) ≤ halfLpp x := Nat.floor_le (by linarith)
  have hLe : halfLpp x
      = Real.log (Real.log x) - Real.log (Real.log (Real.log x)) - 9 := rfl
  have : (⌊halfLpp x⌋₊ : ℝ) < ((tenJ x : ℕ) : ℝ) := by linarith
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
-- one window bound per group
/-- **The high groups near `q = ½`**: on `[⌊Λ/4⌋, ⌊L''(1 - θ_8)⌋)` in eight groups
`[k_g, k_{g+1})`, `k_g = ⌊L''(1 - θ_g)⌋` (`k_0 = ⌊Λ/4⌋`), where `max(1, L'' - k) ≥ 0.99Λθ_{g+1}`:
`(1 - e^{-a})∑ b_k ≤ ∑_g (3/2)^{-a}Λ^{-q/2}G₇A₇(1-q_u)^{-q_u}ρ_{g+1}(e^{-ak_g} - e^{-ak_{g+1}})`. -/
theorem uHigh_groups_le {x q ql qu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hq0 : 0 < q) (hq : q < 1 / 2) (hqlq : ql ≤ q)
    (hqqu : q ≤ qu) (hqu : qu ≤ 1 / 2) {c₇ : WinChaos} (hv₇ : c₇.Valid) {P : ℕ → WinChaos}
    (hP : ∀ k, 97 ≤ k → P k = c₇) {A₇ G₇ : ℝ}
    (hA₇ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      c₇.const E₀ q K ≤ A₇)
    (hG₇ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 97 y ^ qu ≤ G₇)
    (hN : (c₇.N : ℝ) ≤ (A₇ * (1 - qu) ^ (-qu)) ^ 4) :
    (1 - Real.exp (-(q * (1 - 2 * q))))
        * ∑ k ∈ Finset.Ico (halfKb x 0) (halfKb x 8), uWindowBound P q x k
      ≤ ∑ g ∈ Finset.range 8, (3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
          * (G₇ * A₇ * (1 - qu) ^ (-qu)) * halfRho (g + 1)
          * (Real.exp (-(q * (1 - 2 * q) * halfKb x g))
            - Real.exp (-(q * (1 - 2 * q) * halfKb x (g + 1)))) := by
  obtain ⟨-, -, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hL1, hL2⟩ := halfLpp_bounds hΛ
  have hJ := floor_halfLpp_lt_tenJ hx hΛ
  have hmono := halfKb_mono hΛ
  have hwin := fun k (hk : k ∈ Finset.Ico (halfKb x 0) (tenJ x)) =>
    uHighWindow_le hx hΛ hq0.le hqlq hqqu hqu hv₇ hP hA₇ hG₇ hN hk
  have hkbs : ∀ g, 1 ≤ g → (halfKb x g : ℝ) ≤ halfLpp x * (1 - halfTheta g)
      ∧ halfKb x g ≤ ⌊halfLpp x⌋₊ := fun g hg => halfKb_le hΛ hg
  have hG₇0 : 0 ≤ G₇ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) 97 (halfY x))) _)
    (hG₇ _ hly)
  have hA₇0 : 0 ≤ A₇ := by
    refine le_trans ?_ (hA₇ 0 le_rfl (by norm_num) 1 zero_le_one (Real.one_le_exp (by norm_num)))
    have hl := hv₇.lam
    unfold WinChaos.const shiftMomentConst
    exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha : 0 < a := mul_pos hq0 (by linarith)
  set C := (3 / 2 : ℝ) ^ (-a) * Λ ^ (-(q / 2)) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hΛ0.le _)
  set b := G₇ * A₇ * (1 - qu) ^ (-qu) with hbdef
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg hG₇0 hA₇0) (Real.rpow_nonneg (by linarith) _)
  refine sum_groups_geom_le (w := fun k => uWindowBound P q x k)
    (c := fun g => C * b * halfRho (g + 1)) ha hmono 8 fun g hg k hk => ?_
  show uWindowBound P q x k ≤ Real.exp (-(a * k)) * (C * b * halfRho (g + 1))
  have hk' := Finset.mem_Ico.1 hk
  obtain ⟨hkb, hkbL⟩ := hkbs (g + 1) (by omega)
  have hkJ : k ∈ Finset.Ico (halfKb x 0) (tenJ x) :=
    Finset.mem_Ico.2 ⟨le_trans (hmono (Nat.zero_le g)) hk'.1, by omega⟩
  have h := hwin k hkJ
  -- `max(1, L'' - k) ≥ 0.99Λθ_{g+1}`
  have hθ := halfTheta_pos (g + 1)
  have hkR : (k : ℝ) + 1 ≤ halfKb x (g + 1) := by exact_mod_cast hk'.2
  have hLθ : halfLpp x * (1 - halfTheta (g + 1))
      = halfLpp x - halfLpp x * halfTheta (g + 1) := by ring
  have hm : 99 / 100 * Λ * halfTheta (g + 1) ≤ max 1 (halfLpp x - k) := by
    refine le_trans ?_ (le_max_right _ _)
    have h1 : 99 / 100 * Λ * halfTheta (g + 1) ≤ halfLpp x * halfTheta (g + 1) :=
      mul_le_mul_of_nonneg_right hL1 hθ.le
    linarith
  have hpos : 0 < 99 / 100 * Λ * halfTheta (g + 1) := mul_pos (mul_pos (by norm_num) hΛ0) hθ
  have hρ : (Λ / max 1 (halfLpp x - k)) ^ (1 / 4 : ℝ) ≤ halfRho (g + 1) := by
    calc (Λ / max 1 (halfLpp x - k)) ^ (1 / 4 : ℝ)
        ≤ (Λ / (99 / 100 * Λ * halfTheta (g + 1))) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (div_nonneg hΛ0.le (le_trans zero_le_one (le_max_left _ _)))
            (div_le_div_of_nonneg_left hΛ0.le hpos hm) (by norm_num)
      _ = halfRho (g + 1) := by
          unfold halfRho
          rw [show 99 / 100 * Λ * halfTheta (g + 1) = Λ * (99 / 100 * halfTheta (g + 1)) by
            ring, div_mul_eq_div_div, div_self hΛ0.ne', one_div,
            Real.rpow_def_of_pos (inv_pos.2 (mul_pos (by norm_num) hθ)), Real.log_inv]
          congr 1
          ring
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc C * (b * (Λ / max 1 (halfLpp x - k)) ^ (1 / 4 : ℝ))
      = C * b * (Λ / max 1 (halfLpp x - k)) ^ (1 / 4 : ℝ) := by ring
    _ ≤ C * b * halfRho (g + 1) := mul_le_mul_of_nonneg_left hρ (mul_nonneg hC0 hb0)

set_option maxHeartbeats 1000000 in
-- the per-window bound and the power sum
/-- **The tail near `q = ½`**: on `[k_8, J₀)`, `e^{-ak} ≤ e^{-ak_8}` and
`∑ max(1, L'' - k)^{-1/4} ≤ (4/3)(L''θ_8 + 1)^{3/4} + log Λ + 11`
(`RMF.sum_max_rpow_neg_quarter_le`). -/
theorem uHigh_tail_le {x q ql qu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 6000 ≤ Real.log (Real.log x)) (hq0 : 0 < q) (hq : q < 1 / 2) (hqlq : ql ≤ q)
    (hqqu : q ≤ qu) (hqu : qu ≤ 1 / 2) {c₇ : WinChaos} (hv₇ : c₇.Valid) {P : ℕ → WinChaos}
    (hP : ∀ k, 97 ≤ k → P k = c₇) {A₇ G₇ : ℝ}
    (hA₇ : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp 8 →
      c₇.const E₀ q K ≤ A₇)
    (hG₇ : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql 97 y ^ qu ≤ G₇)
    (hN : (c₇.N : ℝ) ≤ (A₇ * (1 - qu) ^ (-qu)) ^ 4) :
    ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x), uWindowBound P q x k
      ≤ (3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
        * (G₇ * A₇ * (1 - qu) ^ (-qu)) * Real.exp (-(q * (1 - 2 * q) * halfKb x 8))
        * Real.log (Real.log x) ^ (1 / 4 : ℝ)
        * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ)
          + (Real.log (Real.log (Real.log x)) + 11)) := by
  obtain ⟨-, -, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hL1, hL2⟩ := halfLpp_bounds hΛ
  obtain ⟨-, hJΛ⟩ := seven_le_tenJ_le hx
  have hJ := floor_halfLpp_lt_tenJ hx hΛ
  have hmono := halfKb_mono hΛ
  obtain ⟨-, hk8L⟩ := halfKb_le hΛ (g := 8) (by norm_num)
  have hk8ge := halfKb_ge (x := x) 8 (by norm_num)
  have hwin := fun k (hk : k ∈ Finset.Ico (halfKb x 0) (tenJ x)) =>
    uHighWindow_le hx hΛ hq0.le hqlq hqqu hqu hv₇ hP hA₇ hG₇ hN hk
  have hG₇0 : 0 ≤ G₇ := le_trans (Real.rpow_nonneg (le_trans zero_le_one
    (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) 97 (halfY x))) _)
    (hG₇ _ hly)
  have hA₇0 : 0 ≤ A₇ := by
    refine le_trans ?_ (hA₇ 0 le_rfl (by norm_num) 1 zero_le_one (Real.one_le_exp (by norm_num)))
    have hl := hv₇.lam
    unfold WinChaos.const shiftMomentConst
    exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
  have hLe : halfLpp x
      = Real.log (Real.log x) - Real.log (Real.log (Real.log x)) - 9 := rfl
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha : 0 < a := mul_pos hq0 (by linarith)
  set C := (3 / 2 : ℝ) ^ (-a) * Λ ^ (-(q / 2)) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hΛ0.le _)
  set b := G₇ * A₇ * (1 - qu) ^ (-qu) with hbdef
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg hG₇0 hA₇0) (Real.rpow_nonneg (by linarith) _)
  set E8 := Real.exp (-(a * halfKb x 8)) with hE8def
  have hL0 : 0 ≤ halfLpp x := by linarith
  -- one window
  have hw : ∀ k ∈ Finset.Ico (halfKb x 8) (tenJ x), uWindowBound P q x k
      ≤ C * b * E8 * Λ ^ (1 / 4 : ℝ) * (max 1 (halfLpp x - k)) ^ (-(1 / 4 : ℝ)) := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    have hkJ : k ∈ Finset.Ico (halfKb x 0) (tenJ x) :=
      Finset.mem_Ico.2 ⟨le_trans (hmono (Nat.zero_le 8)) hk'.1, hk'.2⟩
    have h := hwin k hkJ
    have hm1 : (1 : ℝ) ≤ max 1 (halfLpp x - k) := le_max_left _ _
    have hm0 : 0 < max 1 (halfLpp x - k) := by linarith
    have e : (Λ / max 1 (halfLpp x - k)) ^ (1 / 4 : ℝ)
        = Λ ^ (1 / 4 : ℝ) * (max 1 (halfLpp x - k)) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.div_rpow hΛ0.le hm0.le, Real.rpow_neg hm0.le, div_eq_mul_inv]
    rw [e] at h
    have hek : Real.exp (-(a * k)) ≤ E8 := by
      rw [hE8def]
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ ha.le))
      exact_mod_cast hk'.1
    have hr0 : 0 ≤ Λ ^ (1 / 4 : ℝ) * (max 1 (halfLpp x - k)) ^ (-(1 / 4 : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hΛ0.le _) (Real.rpow_nonneg hm0.le _)
    calc uWindowBound P q x k
        ≤ Real.exp (-(a * k)) * (C * (b * (Λ ^ (1 / 4 : ℝ)
          * (max 1 (halfLpp x - k)) ^ (-(1 / 4 : ℝ))))) := h
      _ ≤ E8 * (C * (b * (Λ ^ (1 / 4 : ℝ) * (max 1 (halfLpp x - k)) ^ (-(1 / 4 : ℝ))))) :=
          mul_le_mul_of_nonneg_right hek (mul_nonneg hC0 (mul_nonneg hb0 hr0))
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hw
  rw [← Finset.mul_sum] at hsum
  have hmax := sum_max_rpow_neg_quarter_le (L := halfLpp x) (a := halfKb x 8) (b := tenJ x) hL0
    hk8L hJ.le
  -- the two counts
  have hN8 : (((⌊halfLpp x⌋₊ - halfKb x 8 : ℕ) : ℝ)) ≤ halfLpp x * halfTheta 8 + 1 := by
    rw [Nat.cast_sub hk8L]
    have hfl : (⌊halfLpp x⌋₊ : ℝ) ≤ halfLpp x := Nat.floor_le hL0
    have e8 : halfLpp x * (1 - halfTheta 8) = halfLpp x - halfLpp x * halfTheta 8 := by ring
    linarith
  have hNJ : (((tenJ x - ⌊halfLpp x⌋₊ : ℕ) : ℝ)) ≤ Real.log Λ + 11 := by
    rw [Nat.cast_sub hJ.le]
    have hfl := Nat.lt_floor_add_one (halfLpp x)
    linarith
  have hN80 : (0 : ℝ) ≤ (((⌊halfLpp x⌋₊ - halfKb x 8 : ℕ) : ℝ)) := Nat.cast_nonneg _
  have h34 : (((⌊halfLpp x⌋₊ - halfKb x 8 : ℕ) : ℝ)) ^ (3 / 4 : ℝ)
      ≤ (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hN80 hN8 (by norm_num)
  have hK0 : 0 ≤ C * b * E8 * Λ ^ (1 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hb0) (Real.exp_pos _).le) (Real.rpow_nonneg hΛ0.le _)
  calc ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x), uWindowBound P q x k
      ≤ C * b * E8 * Λ ^ (1 / 4 : ℝ)
        * ∑ k ∈ Finset.Ico (halfKb x 8) (tenJ x), (max 1 (halfLpp x - k)) ^ (-(1 / 4 : ℝ)) :=
        hsum
    _ ≤ C * b * E8 * Λ ^ (1 / 4 : ℝ)
        * (4 / 3 * (halfLpp x * halfTheta 8 + 1) ^ (3 / 4 : ℝ) + (Real.log Λ + 11)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hmax ?_) hK0
        linarith
    _ = _ := by ring

end RMF
