/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.UCertGenericExplicit

/-!
# The first moment below `q = ½`: one cell of the chaos regime

For `x` with `Λ = log log x ≥ 4000` and `q` in a cell `[q_l, q_u] ⊆ [0.41, 0.49]`,
`RMF.u_cell_chaos` reduces the bound (U), `E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`, to
numerals: the windows in seven groups (`RMF.uGroups`) with the chaos below `Λ/4` and Jensen above
(`RMF.uMeso_chaos_le`), the far range by chaos windows at fixed parameters (`RMF.uFarP`,
`RMF.uFarBound_uFarP_le`: `b_far ≤ Λ^{-q/2}·880^{3q/2}`), and the small pieces
(`RMF.uSmall_chaos_le`, `≤ τ/100` with `τ = (Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`). The cells' numerals are
in `RMF/Weighted/UCellsChaos*Explicit.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The large numbers past `Λ = 4000` -/

/-- `log Λ ≤ Λ/400` for `Λ ≥ 4000`: `e^t ≥ e^{10}(1 + (t - 10)) ≥ 400t` at `t = Λ/400 ≥ 10`. -/
lemma log_le_div_four_hundred {Λ : ℝ} (hΛ : 4000 ≤ Λ) : Real.log Λ ≤ Λ / 400 := by
  have hΛ0 : 0 < Λ := by linarith
  rw [Real.log_le_iff_le_exp hΛ0]
  have h10 : (22026 : ℝ) ≤ Real.exp 10 := by interval_decide (trust := kernel)
  have e : Real.exp (Λ / 400) = Real.exp 10 * Real.exp (Λ / 400 - 10) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : 1 + (Λ / 400 - 10) ≤ Real.exp (Λ / 400 - 10) := by
    linarith [Real.add_one_le_exp (Λ / 400 - 10)]
  have h2 : 0 ≤ 1 + (Λ / 400 - 10) := by linarith
  rw [e]
  have h3 : 22026 * (1 + (Λ / 400 - 10)) ≤ Real.exp 10 * Real.exp (Λ / 400 - 10) :=
    mul_le_mul h10 h1 h2 (Real.exp_pos _).le
  linarith

/-- `log log y ≥ Λ - log Λ` at the large range's parameters: `log y ≥ 2e^Λ/Λ - log 2 ≥ e^Λ/Λ`. -/
lemma halfY_loglog_ge_sub {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x) :
    Real.log (Real.log x) - Real.log (Real.log (Real.log x))
      ≤ Real.log (Real.log (halfY x)) := by
  obtain ⟨hx0, hL, hΛ, hexpΛ, -, -⟩ := half_params hx
  obtain ⟨-, -, -, hlogy_ge, -, -⟩ := halfY_facts hx
  have hΛ0 : 0 < Real.log (Real.log x) := by linarith
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  -- `e^Λ/Λ ≤ log y`
  have hA : halfA x = 2 * (Real.log x / Real.log (Real.log x)) := by
    rw [halfA]; ring
  have hq : 1 ≤ Real.log x / Real.log (Real.log x) := by
    rw [le_div_iff₀ hΛ0]
    have := Real.add_one_le_exp (Real.log (Real.log x))
    rw [hexpΛ] at this
    linarith
  have hy : Real.log x / Real.log (Real.log x) ≤ Real.log (halfY x) := by linarith
  have hq0 : 0 < Real.log x / Real.log (Real.log x) := by linarith
  have h := Real.log_le_log hq0 hy
  rw [Real.log_div hLpos.ne' hΛ0.ne'] at h
  linarith

/-- **The blocks above a window past `Λ = 4000`**: at an offset `D ≤ Λ/2`,
`harperBlockCount D y ≥ Λ(1 - 1/400) - D - 1`. -/
lemma harperBlockCount_halfY_ge {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) {D : ℕ} (hD : (D : ℝ) ≤ Real.log (Real.log x) / 2) :
    Real.log (Real.log x) * (399 / 400) - D - 1 ≤ (harperBlockCount D (halfY x) : ℝ) := by
  have hll := halfY_loglog_ge_sub hx
  have hlog := log_le_div_four_hundred hΛ
  have hfl : Real.log (Real.log (halfY x)) - 1 < (⌊Real.log (Real.log (halfY x))⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log (Real.log (halfY x)))
    linarith
  have hDfl : D ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊ := by
    refine Nat.le_floor ?_
    linarith
  rw [harperBlockCount, Nat.cast_sub hDfl]
  linarith

/-! ### The window groups of the chaos regime -/

/-- The windows' chaos parameters by group: `{4}, {5}, {6}, [7, 31), [31, 61), [61, 97)` and
`[97, ∞)`. -/
def uGroups (c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos) (k : ℕ) : WinChaos :=
  if k < 5 then c₁ else if k < 6 then c₂ else if k < 7 then c₃ else if k < 31 then c₄
  else if k < 61 then c₅ else if k < 97 then c₆ else c₇

/-- `a(q) = q(1-2q)` is decreasing on `[1/4, 1/2]`. -/
lemma mul_one_sub_two_mul_anti {q q' : ℝ} (hq : 1 / 4 ≤ q) (hqq : q ≤ q') :
    q' * (1 - 2 * q') ≤ q * (1 - 2 * q) := by nlinarith

/-- **Seven groups on `[4, K)`, Abel's form**: with `w_k ≤ e^{-ak}c_g` on the groups `{4}`, `{5}`,
`{6}`, `[7, 31)`, `[31, 61)`, `[61, 97)`, `[97, K)`, `c₁ ≥ … ≥ c₇ ≥ 0` and `a₀ ≤ a ≤ a₁`,
`(1 - e^{-a})∑_{4≤k<K} w_k ≤ c₁e^{-4a₀} - (c₁ - c₂)e^{-5a₁} - … - (c₆ - c₇)e^{-97a₁}`. -/
lemma sum_seven_groups_le_of {a a₀ a₁ : ℝ} (ha : 0 < a) (ha₀ : a₀ ≤ a) (ha₁ : a ≤ a₁) {K : ℕ}
    (hK : 97 ≤ K) {w : ℕ → ℝ} {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : ℝ} (h12 : c₂ ≤ c₁) (h23 : c₃ ≤ c₂)
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
        - (c₆ - c₇) * Real.exp (-(97 * a₁)) := by
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
  have xK : 0 ≤ Real.exp (-(a * (K : ℝ))) := (Real.exp_pos _).le
  push_cast at x4 x5 x6 x7 x31 x61 x97 e1 e2 e3 e4 e5 e6 e7 ⊢
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
  have tK := mul_nonneg h7 xK
  nlinarith

/-- `(Λ/n)^{1/4} ≤ ρ` from `Λ ≤ ρ⁴n`. -/
lemma div_rpow_quarter_le {Λ n ρ : ℝ} (hΛ : 0 ≤ Λ) (hn : 0 < n) (hρ : 0 ≤ ρ)
    (h : Λ ≤ ρ ^ 4 * n) : (Λ / n) ^ (1 / 4 : ℝ) ≤ ρ := by
  have h1 : Λ / n ≤ ρ ^ 4 := by rw [div_le_iff₀ hn]; linarith
  calc (Λ / n) ^ (1 / 4 : ℝ) ≤ (ρ ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (div_nonneg hΛ hn.le) h1 (by norm_num)
    _ = ρ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hρ]
        norm_num

/-- A window below `Λ/4` is below `J₀`, past `Λ = 4000`. -/
lemma lt_tenJ_of_le_quarter {x : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) {k : ℕ} (hk : (k : ℝ) ≤ Real.log (Real.log x) / 4) :
    k < tenJ x := by
  have hll := halfY_loglog_ge_sub hx
  have hlog := log_le_div_four_hundred hΛ
  obtain ⟨hy2, -, -, -, -, -⟩ := halfY_facts hx
  have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
  have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
  have hJ : Real.log (2 / 3 * Real.log (halfY x)) < ((tenJ x : ℕ) : ℝ) := by
    rw [tenJ]; push_cast; exact Nat.lt_floor_add_one _
  have h23 : Real.log (2 / 3 * Real.log (halfY x))
      = Real.log (2 / 3) + Real.log (Real.log (halfY x)) :=
    Real.log_mul (by norm_num) hlogy.ne'
  have hl23 : -(1 / 2 : ℝ) ≤ Real.log (2 / 3) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    interval_decide (trust := kernel)
  have : (k : ℝ) < ((tenJ x : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- **One group of chaos windows past `Λ = 4000`**: on `[s, t) ⊆ [4, Λ/4]` with parameters `c`
(room `≤ 2980`), level shifts `≤ e^{ℓK}`, the chaos constant `≤ A` for `q` and every tilt
`E₀ ≤ 1/33680`, the window constant `≤ G` and `Λ ≤ ρ⁴n_k`,
`b_k ≤ e^{-ak}·((3/2)^{-a}Λ^{-q/2}·G·A·(1-q_u)^{-q_u}·ρ)`. -/
lemma uWindow_group_le {x q ql qu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) (hq0 : 0 ≤ q) (hql : ql ≤ q) (hqu : q ≤ qu)
    (hqu2 : qu ≤ 1 / 2) {c : WinChaos} (hc : c.Valid) (hcN : c.N ≤ 2980) {P : ℕ → WinChaos}
    {s t : ℕ} (hs4 : 4 ≤ s) (ht : (t : ℝ) ≤ Real.log (Real.log x) / 4 + 1)
    (hP : ∀ k ∈ Finset.Ico s t, P k = c) {ℓK A G ρ : ℝ}
    (hK : ∀ k ∈ Finset.Ico s t, (uOffset k : ℝ) - k ≤ ℓK)
    (hA : ∀ E₀ : ℝ, 0 ≤ E₀ → E₀ ≤ 1 / 33680 → ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp ℓK →
      c.const E₀ q K ≤ A)
    (hG : ∀ y : ℕ, 22000 ≤ Real.log y → thetaWindowConstQ (3 / 2) ql s y ^ qu ≤ G)
    (hρ1 : 1 ≤ ρ)
    (hρ : ∀ k ∈ Finset.Ico s t,
      Real.log (Real.log x) ≤ ρ ^ 4 * (harperBlockCount (uOffset k) (halfY x) : ℝ)) :
    ∀ k ∈ Finset.Ico s t, uWindowBound P q x k
      ≤ Real.exp (-(q * (1 - 2 * q) * k))
        * ((3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
          * (G * A * (1 - qu) ^ (-qu) * ρ)) := by
  intro k hk
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  set Λ := Real.log (Real.log x) with hΛdef
  have hks : s ≤ k := (Finset.mem_Ico.1 hk).1
  have hkt : k < t := (Finset.mem_Ico.1 hk).2
  have hkR : (k : ℝ) + 1 ≤ Λ / 4 + 1 := by
    have : ((k + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt
    push_cast at this
    linarith
  -- the window is inside `[4, J₀)`
  have hkJ : k ∈ Finset.Ico 4 (tenJ x) := by
    refine Finset.mem_Ico.2 ⟨le_trans hs4 hks, ?_⟩
    have hll := halfY_loglog_ge_sub hx
    have hlog := log_le_div_four_hundred hΛ
    obtain ⟨hy2, -, -, -, -, -⟩ := halfY_facts hx
    have hy2R : (2 : ℝ) ≤ (halfY x : ℝ) := by exact_mod_cast hy2
    have hlogy : 0 < Real.log (halfY x) := Real.log_pos (by linarith)
    have hJ : Real.log (2 / 3 * Real.log (halfY x)) < ((tenJ x : ℕ) : ℝ) := by
      rw [tenJ]; push_cast; exact Nat.lt_floor_add_one _
    have h23 : Real.log (2 / 3 * Real.log (halfY x))
        = Real.log (2 / 3) + Real.log (Real.log (halfY x)) :=
      Real.log_mul (by norm_num) hlogy.ne'
    have hl23 : -(1 / 2 : ℝ) ≤ Real.log (2 / 3) := by
      have := Real.add_one_le_exp (-(1 / 2 : ℝ))
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by interval_decide (trust := kernel)
      exact h
    have : (k : ℝ) < ((tenJ x : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hPk : P k = c := hP k hk
  -- the offset and the blocks above the window
  have hD : (uOffset k : ℝ) ≤ Λ / 2 := by
    rw [uOffset]
    rcases le_total (k + 8) 105 with h | h
    · rw [max_eq_right h]; push_cast; linarith
    · rw [max_eq_left h]; push_cast; linarith
  have hn := harperBlockCount_halfY_ge hx hΛ hD
  have hDle : (uOffset k : ℝ) ≤ Λ / 4 + 8 := by
    rw [uOffset]
    rcases le_total (k + 8) 105 with h | h
    · rw [max_eq_right h]; push_cast; linarith
    · rw [max_eq_left h]; push_cast; linarith
  have hn2980 : (2980 : ℝ) ≤ (harperBlockCount (uOffset k) (halfY x) : ℝ) := by linarith
  have hroom : (P k).N ≤ harperBlockCount (uOffset k) (halfY x) := by
    rw [hPk]
    have : ((c.N : ℕ) : ℝ) ≤ (harperBlockCount (uOffset k) (halfY x) : ℝ) :=
      le_trans (by exact_mod_cast hcN) hn2980
    exact_mod_cast this
  have hn0 : 0 < (harperBlockCount (uOffset k) (halfY x) : ℝ) := by linarith
  -- the four bounds
  have hE₀ : 1 / (16 * Λ) ≤ 1 / 33680 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hAk : (P k).const (1 / (16 * Λ)) q (Real.exp ((uOffset k : ℝ) - k)) ≤ A := by
    rw [hPk]
    exact hA _ (by positivity) hE₀ _ (Real.exp_pos _).le (Real.exp_le_exp.2 (hK k hk))
  have hGk : thetaWindowConstQ (3 / 2) ql s (halfY x) ^ qu ≤ G := hG _ hly
  have hρk : (Λ / (harperBlockCount (uOffset k) (halfY x) : ℝ)) ^ (1 / 4 : ℝ) ≤ ρ :=
    div_rpow_quarter_le (by linarith) hn0 (by linarith) (hρ k hk)
  have hPv : (P k).Valid := by rw [hPk]; exact hc
  exact uWindowBound_le_chaos hx hq0 hql hqu hqu2 hks hkJ hPv hroom hGk hAk hρ1 hρk hn0

/-- The offset of a low window is the floor's `105`. -/
lemma uOffset_of_lt {k : ℕ} (hk : k < 97) : uOffset k = 105 := by
  rw [uOffset]; omega

/-- The offset of a high window is `k + 8`. -/
lemma uOffset_of_ge {k : ℕ} (hk : 97 ≤ k) : uOffset k = k + 8 := by
  rw [uOffset]; omega

/-- `(Λ/n)^{1/4}` for the low windows: `Λ ≤ 1.0075⁴·n` when `n ≥ 0.9975Λ - 106`, `Λ ≥ 4000`. -/
lemma rho_low {Λ n : ℝ} (hΛ : 4000 ≤ Λ) (hn : Λ * (399 / 400) - 105 - 1 ≤ n) :
    Λ ≤ (10075 / 10000) ^ 4 * n := by
  have h : (1030281 / 1000000 : ℝ) ≤ (10075 / 10000) ^ 4 := by norm_num
  have h0 : 0 ≤ n := by linarith
  nlinarith

/-- `(Λ/n)^{1/4}` for the high windows: `Λ ≤ 1.0763⁴·n` when `n ≥ 0.7475Λ - 8`, `Λ ≥ 4000`. -/
lemma rho_high {Λ n : ℝ} (hΛ : 4000 ≤ Λ) (hn : Λ * (399 / 400) - (Λ / 4 + 8) - 1 ≤ n) :
    Λ ≤ (10763 / 10000) ^ 4 * n := by
  have h : (1341940 / 1000000 : ℝ) ≤ (10763 / 10000) ^ 4 := by norm_num
  have h0 : 0 ≤ n := by linarith
  nlinarith

set_option maxHeartbeats 4000000 in
-- seven groups, each discharged by the same lemma
/-- **The chaos regime's windows, summed**: for `x` with `Λ ≥ 4000`,
`q ∈ [q_l, q_u] ⊆ [0.41, 0.49]`, the groups' parameters `c_g` (room `≤ 2980`) with chaos constants
`≤ A_g` and window constants `≤ G_g` on the cell, and group constants
`G_g A_g (1 - q_u)^{-q_u} ρ_g ≤ c̄_g` decreasing (`ρ = 1.0075` for the low groups, `1.0763` for
`[97, Λ/4)`):

`(1 - e^{-a})·∑_{4≤k<J₀} b_k ≤ (3/2)^{-a}Λ^{-q/2}·Abel(c̄) + (3/2)^{-a}G₇e^{-a⌊Λ/4⌋}`,

`a = q(1-2q)`, the windows past `Λ/4` by Jensen. -/
theorem uMeso_chaos_le {x q ql qu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu)
    (hqu : qu ≤ 49 / 100) {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} (hv₁ : c₁.Valid) (hv₂ : c₂.Valid)
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
    (h67 : b₇ ≤ b₆) :
    (1 - Real.exp (-(q * (1 - 2 * q))))
        * ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇) q x k
      ≤ (3 / 2) ^ (-(q * (1 - 2 * q))) * Real.log (Real.log x) ^ (-(q / 2))
          * (b₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
            - (b₁ - b₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
            - (b₂ - b₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
            - (b₃ - b₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
            - (b₄ - b₅) * Real.exp (-(31 * (ql * (1 - 2 * ql))))
            - (b₅ - b₆) * Real.exp (-(61 * (ql * (1 - 2 * ql))))
            - (b₆ - b₇) * Real.exp (-(97 * (ql * (1 - 2 * ql)))))
        + (3 / 2) ^ (-(q * (1 - 2 * q))) * G₇
          * Real.exp (-(q * (1 - 2 * q) * ⌊Real.log (Real.log x) / 4⌋₊)) := by
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
  have ha₁ : a ≤ ql * (1 - 2 * ql) := mul_one_sub_two_mul_anti (by linarith) hqlq
  set K4 := ⌊Λ / 4⌋₊ with hK4def
  have hK4R : (K4 : ℝ) ≤ Λ / 4 := Nat.floor_le (by linarith)
  have hK97 : 97 ≤ K4 := Nat.le_floor (by push_cast; linarith)
  have hK4J : K4 ≤ tenJ x := (lt_tenJ_of_le_quarter hx hΛ hK4R).le
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
  have hsum1 := sum_seven_groups_le_of ha ha₀ ha₁ hK97 (w := fun k => uWindowBound P q x k)
    (mul_le_mul_of_nonneg_left h12 hC0) (mul_le_mul_of_nonneg_left h23 hC0)
    (mul_le_mul_of_nonneg_left h34 hC0) (mul_le_mul_of_nonneg_left h45 hC0)
    (mul_le_mul_of_nonneg_left h56 hC0) (mul_le_mul_of_nonneg_left h67 hC0)
    (mul_nonneg hC0 hb₇0) w1 w2 w3 w4 w5 w6 w7
  -- the windows past `Λ/4` by Jensen
  have wJ : ∀ k ∈ Finset.Ico K4 (tenJ x),
      uWindowBound P q x k ≤ Real.exp (-(a * k)) * ((3 / 2) ^ (-a) * G₇) := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    have hk97 : 97 ≤ k := le_trans hK97 hk'.1
    have hkJ : k ∈ Finset.Ico 4 (tenJ x) := Finset.mem_Ico.2 ⟨by omega, hk'.2⟩
    have hPv : (P k).Valid := by
      rw [hPk]; unfold uGroups
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      exact hv₇
    have h := uWindowBound_le_jensen hx hq0 hqlq hqqu (by linarith) hk97 hkJ hPv (hG₇ _ hly)
    rw [← hadef] at h
    linarith
  have hsum2 := one_sub_exp_neg_mul_sum_le_group ha hK4J wJ
  have hsplit : ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k
      = ∑ k ∈ Finset.Ico 4 K4, uWindowBound P q x k
        + ∑ k ∈ Finset.Ico K4 (tenJ x), uWindowBound P q x k :=
    (Finset.sum_Ico_consecutive _ (by omega) hK4J).symm
  have hEJ : 0 ≤ Real.exp (-(a * ((tenJ x : ℕ) : ℝ))) := (Real.exp_pos _).le
  have hG0' : 0 ≤ (3 / 2 : ℝ) ^ (-a) * G₇ := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hG₇0
  have hsum2' : (1 - Real.exp (-a)) * ∑ k ∈ Finset.Ico K4 (tenJ x), uWindowBound P q x k
      ≤ (3 / 2) ^ (-a) * G₇ * Real.exp (-(a * K4)) := by
    have := mul_nonneg hG0' hEJ
    nlinarith
  rw [hsplit, mul_add]
  have e1 : C * b₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
      - (C * b₁ - C * b₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
      - (C * b₂ - C * b₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
      - (C * b₃ - C * b₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
      - (C * b₄ - C * b₅) * Real.exp (-(31 * (ql * (1 - 2 * ql))))
      - (C * b₅ - C * b₆) * Real.exp (-(61 * (ql * (1 - 2 * ql))))
      - (C * b₆ - C * b₇) * Real.exp (-(97 * (ql * (1 - 2 * ql))))
      = C * (b₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
        - (b₁ - b₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
        - (b₂ - b₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
        - (b₃ - b₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
        - (b₄ - b₅) * Real.exp (-(31 * (ql * (1 - 2 * ql))))
        - (b₅ - b₆) * Real.exp (-(61 * (ql * (1 - 2 * ql))))
        - (b₆ - b₇) * Real.exp (-(97 * (ql * (1 - 2 * ql))))) := by ring
  have e2 : (3 / 2 : ℝ) ^ (-a) * G₇ * Real.exp (-(a * K4))
      = (3 / 2) ^ (-a) * G₇ * Real.exp (-(a * ⌊Λ / 4⌋₊)) := rfl
  linarith

/-! ### The far range of the chaos regime -/

/-- The far windows' parameters of (U)'s chaos regime: `λ = 67/2`, `T = 50`, `κ = 16`, level
`67 + j`, room `3000 + 20j`. -/
noncomputable def uFarP : FarChaos := uFarParams (67 / 2) 50 16 67 3000

lemma uFarP_valid : uFarP.Valid := by
  refine uFarParams_valid (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  have hs : Real.sqrt ((3000 : ℕ) : ℝ) ≤ 5478 / 100 := by
    rw [show (5478 / 100 : ℝ) = Real.sqrt ((5478 / 100) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  push_cast at hs ⊢
  linarith

/-- **The far windows' constant, linear in the window**: `const_j ≤ 10.606 + 0.0927j` at every tilt
`E₀ ≤ 1/33680`. -/
lemma uFarP_const_le {E₀ : ℝ} (hE₀ : 0 ≤ E₀) (hE₀1 : E₀ ≤ 1 / 33680) (j : ℕ) :
    uFarP.const E₀ j ≤ 10606 / 1000 + 927 / 10000 * j := by
  have hCi := radAveragedConst_le_of hE₀ hE₀1 (Tr := 50) (κ := 16) (by norm_num) (by norm_num)
  have hℓκ : Real.log 16 ≤ 2772589 / 1000000 := by interval_decide (trust := kernel)
  have hℓKT : Real.log (116341 / 100000 * 50) ≤ 4063400 / 1000000 := by
    interval_decide (trust := kernel)
  have hs := radAveragedShift_le_of hE₀ hE₀1 (Tr := 50) (κ := 16) (by norm_num) hℓκ hℓKT
  refine uFarParams_const_le (Ci' := 11999 / 10000) (s' := 14376 / 1000) (c := 12484 / 10000)
    (U := 27126 / 1000) (E := 10829 / 1000000) hE₀ hE₀1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (le_trans hCi (by norm_num)) (le_trans hs (by norm_num)) (by norm_num)
    (by norm_num) ?_ ?_ ?_ ?_ j
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)
  · interval_decide (trust := kernel)

/-- `∑_{j<n} j r^j ≤ r/(1-r)²` for `0 ≤ r < 1`. -/
lemma sum_range_mul_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) * r ^ j ≤ r / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  rw [← tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  exact hs.sum_le_tsum _ fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hr0 j)

set_option maxHeartbeats 2000000 in
-- the far range's sum, bounded term by term
/-- **The far range of the chaos regime**: for `Λ ≥ 4000`, `0 < q ≤ ½` and the far windows up to
`e^{n-4}`, `n = ⌈log Λ⌉ + 4` (so `e^{n-4} ≥ Λ`), at the parameters `RMF.uFarP`,
`b_far ≤ Λ^{-q/2}·880^{3q/2}`: every far window has room, its constant is `≤ 10.606 + 0.0927j`, its
chaos factor `≤ 3^{2/3}(0.96Λ)^{-1/3}`, the weights `(2·1.195(e-1)e^{3-j})^{2/3} ≤ 18.95e^{-2j/3}`
sum to `≤ 18.95(10.606/(1-r) + 0.0927r/(1-r)²)`, `r = e^{-2/3}`, and the tail
`(2.39/e^{n-4})^{2/3} ≤ 0.114Λ^{-1/3}`. -/
theorem uFarBound_uFarP_le {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    uFarBound uFarP (⌈Real.log (Real.log (Real.log x))⌉₊ + 4) q x
      ≤ Real.log (Real.log x) ^ (-(q / 2)) * (880 : ℝ) ^ (3 / 2 * q) := by
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  set Λ := Real.log (Real.log x) with hΛdef
  set n := ⌈Real.log Λ⌉₊ + 4 with hndef
  have hΛ0 : 0 < Λ := by linarith
  have hlog := log_le_div_four_hundred hΛ
  have hlog0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
  have hceil : (⌈Real.log Λ⌉₊ : ℝ) < Real.log Λ + 1 := Nat.ceil_lt_add_one hlog0
  have hnR : (n : ℝ) ≤ Λ / 400 + 5 := by rw [hndef]; push_cast; linarith
  have hen : Λ ≤ Real.exp ((n : ℝ) - 4) := by
    have h1 : Real.log Λ ≤ (n : ℝ) - 4 := by
      rw [hndef]; push_cast; linarith [Nat.le_ceil (Real.log Λ)]
    calc Λ = Real.exp (Real.log Λ) := (Real.exp_log hΛ0).symm
      _ ≤ Real.exp ((n : ℝ) - 4) := Real.exp_le_exp.2 h1
  -- the blocks above every far window
  have hnj : ∀ j < n, Λ * (399 / 400) - (105 + j) - 1
      ≤ (harperBlockCount (105 + j) (halfY x) : ℝ) := by
    intro j hj
    have hjR : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    have hD : ((105 + j : ℕ) : ℝ) ≤ Λ / 2 := by push_cast; linarith
    have h := harperBlockCount_halfY_ge hx hΛ hD
    rw [← hΛdef] at h
    push_cast at h ⊢
    linarith
  have hroom2 : ∀ j < n, uFarP.N j ≤ harperBlockCount (105 + j) (halfY x) := by
    intro j hj
    have hjR : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    have h := hnj j hj
    have : ((uFarP.N j : ℕ) : ℝ) ≤ (harperBlockCount (105 + j) (halfY x) : ℝ) := by
      change ((3000 + 20 * j : ℕ) : ℝ) ≤ _
      push_cast
      linarith
    exact_mod_cast this
  have hroom1 : 105 + n ≤ ⌊Real.log (Real.log (halfY x : ℝ))⌋₊ := by
    have hll := halfY_loglog_ge_sub hx
    rw [← hΛdef] at hll
    refine Nat.le_floor ?_
    push_cast
    linarith
  -- the chaos branch
  unfold uFarBound
  rw [if_pos ⟨hroom1, hroom2⟩]
  refine le_trans (min_le_right _ _) ?_
  -- the terms
  have hE₀ : 1 / (16 * Λ) ≤ 1 / 33680 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set r := Real.exp (-(2 / 3 : ℝ)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hcw : (2 * 1.195 * (Real.exp 1 - 1) * Real.exp 3) ^ (2 / 3 : ℝ) ≤ 1895 / 100 := by
    have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [rpow_eq_exp_mul_log (mul_pos (mul_pos (by norm_num) he) (Real.exp_pos _))]
    interval_decide (trust := kernel)
  have hχ3 : (1 - 2 / 3 : ℝ) ^ (-(2 / 3 : ℝ)) * (96 / 100 : ℝ) ^ (-(1 / 3 : ℝ))
      ≤ 21086 / 10000 := by
    rw [rpow_eq_exp_mul_log (by norm_num), rpow_eq_exp_mul_log (by norm_num)]
    interval_decide (trust := kernel)
  have hΛ3 : 0 ≤ Λ ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hΛ0.le _
  have hterm : ∀ j ∈ Finset.range n,
      uFarP.const (1 / (16 * Λ)) j
        * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
        * (1 + (1 - 2 / 3) * Real.sqrt (harperBlockCount (105 + j) (halfY x) : ℝ)) ^ (-(2 / 3 : ℝ))
      ≤ (10606 / 1000 * r ^ j + 927 / 10000 * ((j : ℝ) * r ^ j))
        * (1895 / 100 * (21086 / 10000 * Λ ^ (-(1 / 3 : ℝ)))) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hjR : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj'
    have hC := uFarP_const_le (by positivity) hE₀ j
    have hC0 : 0 ≤ uFarP.const (1 / (16 * Λ)) j := by
      change 0 ≤ shiftMomentConst _ _ _ _ _ _ _ _
      unfold shiftMomentConst
      exact le_trans (Real.rpow_nonneg (by change (0 : ℝ) ≤ 1 * (1 + 67 / 2); norm_num) _)
        (le_max_left _ _)
    -- the weight
    have hw : (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
        ≤ 1895 / 100 * r ^ j := by
      have e1 : Real.exp (3 - (j : ℝ)) = Real.exp 3 * Real.exp (-(j : ℝ)) := by
        rw [← Real.exp_add]; ring_nf
      have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      rw [e1, ← mul_assoc, Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
      have e2 : Real.exp (-(j : ℝ) * (2 / 3)) = r ^ j := by
        rw [hrdef, exp_neg_pow]; congr 1; ring
      rw [e2]
      exact mul_le_mul_of_nonneg_right hcw (pow_nonneg hr0 j)
    have hw0 : 0 ≤ (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ) := by
      have := Real.add_one_le_exp (1 : ℝ)
      exact Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        (Real.exp_pos _).le) _
    -- the chaos factor
    have hn := hnj j hj'
    set m := (harperBlockCount (105 + j) (halfY x) : ℝ) with hmdef
    have hm : 96 / 100 * Λ ≤ m := by linarith
    have hm0 : 0 < m := by linarith
    have hχ : (1 + (1 - 2 / 3) * Real.sqrt m) ^ (-(2 / 3 : ℝ))
        ≤ 21086 / 10000 * Λ ^ (-(1 / 3 : ℝ)) := by
      refine le_trans (one_add_mul_sqrt_rpow_neg_le (by norm_num) (by norm_num) hm0) ?_
      have h1 : m ^ (-((2 / 3 : ℝ) / 2)) ≤ (96 / 100 * Λ) ^ (-(1 / 3 : ℝ)) := by
        rw [show -((2 / 3 : ℝ) / 2) = -(1 / 3) by norm_num]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hm (by norm_num)
      rw [Real.mul_rpow (by norm_num) hΛ0.le] at h1
      have h2 : 0 ≤ (1 - 2 / 3 : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by norm_num) _
      calc (1 - 2 / 3 : ℝ) ^ (-(2 / 3 : ℝ)) * m ^ (-((2 / 3 : ℝ) / 2))
          ≤ (1 - 2 / 3 : ℝ) ^ (-(2 / 3 : ℝ))
            * ((96 / 100 : ℝ) ^ (-(1 / 3 : ℝ)) * Λ ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (1 - 2 / 3 : ℝ) ^ (-(2 / 3 : ℝ)) * (96 / 100 : ℝ) ^ (-(1 / 3 : ℝ))
            * Λ ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ 21086 / 10000 * Λ ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hχ3 hΛ3
    have hχ0 : 0 ≤ (1 + (1 - 2 / 3) * Real.sqrt m) ^ (-(2 / 3 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have hr j' : 0 ≤ r ^ j' := pow_nonneg hr0 j'
    calc uFarP.const (1 / (16 * Λ)) j
          * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
          * (1 + (1 - 2 / 3) * Real.sqrt m) ^ (-(2 / 3 : ℝ))
        ≤ (10606 / 1000 + 927 / 10000 * j) * (1895 / 100 * r ^ j)
          * (21086 / 10000 * Λ ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul (mul_le_mul hC hw hw0 (by positivity)) hχ hχ0 (by positivity)
      _ = (10606 / 1000 * r ^ j + 927 / 10000 * ((j : ℝ) * r ^ j))
          * (1895 / 100 * (21086 / 10000 * Λ ^ (-(1 / 3 : ℝ)))) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hg0 : ∑ j ∈ Finset.range n, r ^ j ≤ 1 / (1 - r) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
    rw [Finset.range_eq_Ico]
    simpa using h
  have hg1 := sum_range_mul_geom_le hr0 hr1 n
  have hg0n : 1 / (1 - r) ≤ 205515 / 100000 := by
    rw [hrdef]; interval_decide (trust := kernel)
  have hg1n : r / (1 - r) ^ 2 ≤ 2169 / 1000 := by
    have hrn : r ≤ 5135 / 10000 := by rw [hrdef]; interval_decide (trust := kernel)
    have h1r : 0 < 1 - r := by linarith
    have e : r / (1 - r) ^ 2 = r * (1 / (1 - r)) * (1 / (1 - r)) := by field_simp
    rw [e]
    have hi0 : 0 ≤ 1 / (1 - r) := by positivity
    have := mul_le_mul (mul_le_mul hrn hg0n hi0 (by norm_num)) hg0n hi0 (by positivity)
    linarith
  -- the tail
  have htail : (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ (2 / 3 : ℝ)
      ≤ 114 / 1000 * Λ ^ (-(1 / 3 : ℝ)) := by
    have h1 : 2 * 1.195 / Real.exp ((n : ℝ) - 4) ≤ 2 * 1.195 / Λ :=
      div_le_div_of_nonneg_left (by norm_num) hΛ0 hen
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    refine le_trans h2 ?_
    rw [Real.div_rpow (by norm_num) hΛ0.le]
    have e : Λ ^ (2 / 3 : ℝ) = Λ ^ (1 / 3 : ℝ) * Λ ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hΛ0]; norm_num
    have h13 : (4000 : ℝ) ^ (1 / 3 : ℝ) ≤ Λ ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hΛ (by norm_num)
    have h13n : (1587 / 100 : ℝ) ≤ (4000 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [rpow_eq_exp_mul_log (by norm_num)]; interval_decide (trust := kernel)
    have hc : (2 * 1.195 : ℝ) ^ (2 / 3 : ℝ) ≤ 1789 / 1000 := by
      rw [rpow_eq_exp_mul_log (by norm_num)]; interval_decide (trust := kernel)
    have hL13 : 0 < Λ ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hΛ0 _
    rw [e, Real.rpow_neg hΛ0.le, div_le_iff₀ (by positivity)]
    rw [show 114 / 1000 * (Λ ^ (1 / 3 : ℝ))⁻¹ * (Λ ^ (1 / 3 : ℝ) * Λ ^ (1 / 3 : ℝ))
        = 114 / 1000 * Λ ^ (1 / 3 : ℝ) by field_simp]
    nlinarith
  -- together
  have hS : ∑ j ∈ Finset.range n, uFarP.const (1 / (16 * Λ)) j
        * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
        * (1 + (1 - 2 / 3) * Real.sqrt (harperBlockCount (105 + j) (halfY x) : ℝ))
          ^ (-(2 / 3 : ℝ))
      + (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ (2 / 3 : ℝ) ≤ 880 * Λ ^ (-(1 / 3 : ℝ)) := by
    have h1 : 10606 / 1000 * ∑ j ∈ Finset.range n, r ^ j
        + 927 / 10000 * ∑ j ∈ Finset.range n, (j : ℝ) * r ^ j
        ≤ 10606 / 1000 * (205515 / 100000) + 927 / 10000 * (2169 / 1000) := by
      have := le_trans hg0 hg0n
      have := le_trans hg1 hg1n
      nlinarith
    have hk : 0 ≤ 1895 / 100 * (21086 / 10000 * Λ ^ (-(1 / 3 : ℝ))) := by positivity
    have h2 := mul_le_mul_of_nonneg_right h1 hk
    nlinarith
  have hS0 : 0 ≤ ∑ j ∈ Finset.range n, uFarP.const (1 / (16 * Λ)) j
        * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
        * (1 + (1 - 2 / 3) * Real.sqrt (harperBlockCount (105 + j) (halfY x) : ℝ))
          ^ (-(2 / 3 : ℝ))
      + (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ (2 / 3 : ℝ) := by
    refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (Real.rpow_nonneg (by positivity) _)
    refine mul_nonneg (mul_nonneg ?_ (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg (by positivity) _)
    · change 0 ≤ shiftMomentConst _ _ _ _ _ _ _ _
      unfold shiftMomentConst
      exact le_trans (Real.rpow_nonneg (by change (0 : ℝ) ≤ 1 * (1 + 67 / 2); norm_num) _)
        (le_max_left _ _)
    · have := Real.add_one_le_exp (1 : ℝ)
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_pos _).le
  have hq23 : q / (2 / 3) = 3 / 2 * q := by ring
  rw [hq23]
  calc (∑ j ∈ Finset.range n, uFarP.const (1 / (16 * Λ)) j
        * (2 * 1.195 * (Real.exp 1 - 1) * Real.exp (3 - (j : ℝ))) ^ (2 / 3 : ℝ)
        * (1 + (1 - 2 / 3) * Real.sqrt (harperBlockCount (105 + j) (halfY x) : ℝ))
          ^ (-(2 / 3 : ℝ))
      + (2 * 1.195 / Real.exp ((n : ℝ) - 4)) ^ (2 / 3 : ℝ)) ^ (3 / 2 * q)
      ≤ (880 * Λ ^ (-(1 / 3 : ℝ))) ^ (3 / 2 * q) :=
        Real.rpow_le_rpow hS0 hS (by positivity)
    _ = Λ ^ (-(q / 2)) * (880 : ℝ) ^ (3 / 2 * q) := by
        rw [Real.mul_rpow (by norm_num) hΛ3, ← Real.rpow_mul hΛ0.le]
        rw [show -(1 / 3 : ℝ) * (3 / 2 * q) = -(q / 2) by ring]
        ring

/-! ### The small pieces of the chaos regime -/

/-- `a(q) = q(1-2q) ≥ 0.0098` on `[0.41, 0.49]`. -/
lemma q_mul_one_sub_ge {q : ℝ} (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    98 / 10000 ≤ q * (1 - 2 * q) := by nlinarith

set_option maxHeartbeats 2000000 in
-- many explicit bounds in one context
/-- **The small pieces past `Λ = 4000`**: for `q ∈ [0.41, 0.49]`, (PF) at `y`, the smooth tail, the
reduction's error and the central window together are `≤ (1/100)(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`: each is
`≤ e^{1.97 + Λ/800 - Λ/103}`, against `(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2} ≥ 5.54e^{-Λ/1600}`. -/
theorem uSmall_chaos_le {x q : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) (hq1 : 41 / 100 ≤ q) (hq2 : q ≤ 49 / 100) :
    uPFyAt q (halfY x) + halfTail x ^ q
        + smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x))
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
      ≤ 1 / 100 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  obtain ⟨hx0, hL, hΛ110, hexpΛ, -, -⟩ := half_params hx
  obtain ⟨hy2, -, -, -, -, -⟩ := halfY_facts hx
  obtain ⟨-, hly⟩ := halfY_loglog_le hx
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  have hll := halfY_loglog_ge_sub hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hlog := log_le_div_four_hundred hΛ
  have hq0 : 0 < q := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha := q_mul_one_sub_ge hq1 hq2
  have hlogy0 : 0 < Real.log (halfY x) := by linarith
  -- `(log y)^{-a} ≤ e^{-Λ/103}`
  have hLy : (Real.log (halfY x)) ^ (q * (2 * q - 1)) ≤ Real.exp (-(Λ / 103)) := by
    rw [rpow_eq_exp_mul_log hlogy0]
    refine Real.exp_le_exp.2 ?_
    have e : q * (2 * q - 1) * Real.log (Real.log (halfY x)) = -(a * Real.log (Real.log (halfY x)))
      := by rw [hadef]; ring
    rw [e]
    have h1 : a * (Λ * (399 / 400)) ≤ a * Real.log (Real.log (halfY x)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : 98 / 10000 * (Λ * (399 / 400)) ≤ a * (Λ * (399 / 400)) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    linarith
  -- (PF) at `y`
  have hPFy : uPFyAt q (halfY x) ≤ Real.exp (-(Λ / 103)) := by
    unfold uPFyAt
    have h1 : Real.exp (a * (9.0028 / Real.log (halfY x) - 3 / 20)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_)
      have : 9.0028 / Real.log (halfY x) ≤ 9.0028 / 22000 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
      linarith
    rw [← hadef]
    calc Real.exp (a * (9.0028 / Real.log (halfY x) - 3 / 20))
          * Real.log (halfY x) ^ (q * (2 * q - 1))
        ≤ 1 * Real.exp (-(Λ / 103)) :=
          mul_le_mul h1 hLy (Real.rpow_nonneg hlogy0.le _) zero_le_one
      _ = Real.exp (-(Λ / 103)) := one_mul _
  -- the central window's (PF)
  have hPFc : uPFcAt q (halfSigma x) (halfY x) ≤ Real.exp (-(Λ / 103)) := by
    unfold uPFcAt
    have hσy := halfSigma_mul_log_le hx
    have hσ0 : 0 ≤ halfSigma x := by rw [halfSigma]; positivity
    have hσ1 : halfSigma x ≤ 1 / 1000 := by
      have h16 : 1 / (16 * Λ) ≤ 1 / 64000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Real.log (halfY x)) hσ0
      linarith
    have hl4 : Real.log 4 ≤ 14 / 10 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h1 : Real.exp (a * (9.0028 / Real.log (halfY x)
        + 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4) - 3 / 20)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_)
      have t1 : 9.0028 / Real.log (halfY x) ≤ 9.0028 / 22000 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hly
      have t2 : 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4)
          ≤ 2 * (1 / 64000) + 2 * (1 / 1000) * (14 / 10 + 4) := by
        have h16 : 1 / (16 * Λ) ≤ 1 / 64000 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have h3 : 2 * halfSigma x * (Real.log 4 + 4) ≤ 2 * (1 / 1000) * (14 / 10 + 4) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
        have e : 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4)
            = 2 * (halfSigma x * Real.log (halfY x)) + 2 * halfSigma x * (Real.log 4 + 4) := by
          ring
        rw [e]
        linarith
      linarith
    rw [← hadef]
    calc Real.exp (a * (9.0028 / Real.log (halfY x)
          + 2 * halfSigma x * (Real.log (halfY x) + Real.log 4 + 4) - 3 / 20))
          * Real.log (halfY x) ^ (q * (2 * q - 1))
        ≤ 1 * Real.exp (-(Λ / 103)) :=
          mul_le_mul h1 hLy (Real.rpow_nonneg hlogy0.le _) zero_le_one
      _ = Real.exp (-(Λ / 103)) := one_mul _
  -- the central window's constant
  have hC0 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) := by
    unfold uCenAt
    have hσ : 0 < halfSigma x := by rw [halfSigma]; positivity
    have h2 : 0 ≤ Real.exp (2 * (1 - q)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2) - 1 := by
      have hl : 0 ≤ Real.log ((halfY x : ℝ) + 1) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ (halfY x : ℝ) := Nat.cast_nonneg _
        linarith)
      have : 0 ≤ 2 * (1 - q)
          * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
          * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2 := by
        have : 0 ≤ 1 - q := by linarith
        positivity
      linarith [Real.add_one_le_exp (2 * (1 - q)
        * (Real.log ((halfY x : ℝ) + 1) ^ 2 / 2 + 15.003 * Real.log ((halfY x : ℝ) + 1) + 34)
        * Real.exp (-((tenJ x : ℕ) : ℝ)) ^ 2)]
    positivity
  have hCen : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q ≤ Real.exp (197 / 100 + Λ / 800) := by
    have h1 := uCen_le hx hq0.le
    rw [← hΛdef] at h1
    have h51 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ≤ 51 * Λ := by linarith
    have h1Λ : (1 : ℝ) ≤ 51 * Λ := by linarith
    calc uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q ≤ (51 * Λ) ^ q :=
          Real.rpow_le_rpow hC0 h51 hq0.le
      _ ≤ (51 * Λ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1Λ (by linarith)
      _ = Real.exp (1 / 2 * Real.log (51 * Λ)) := rpow_eq_exp_mul_log (by positivity) _
      _ ≤ Real.exp (197 / 100 + Λ / 800) := by
          refine Real.exp_le_exp.2 ?_
          rw [Real.log_mul (by norm_num) hΛ0.ne']
          have h51l : Real.log 51 ≤ 394 / 100 := by interval_decide (trust := kernel)
          linarith
  -- the reduction's constant
  have hCR := halfCR_le hx
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  have hCR0 := (smallQReductionConst_pos hz2 hzy hη hε (c := 1 / 32)).le
  have hCRq : smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q ≤ 1 :=
    Real.rpow_le_one hCR0 (by linarith) hq0.le
  -- the smooth tail
  have hT := halfTail_le_decay hx
  rw [← hΛdef] at hT
  have hT0 : 0 ≤ halfTail x := by
    unfold halfTail
    exact Finset.sum_nonneg fun m _ => by positivity
  have hTq : halfTail x ^ q ≤ Real.exp (-(Λ / 103)) := by
    calc halfTail x ^ q ≤ Real.exp (142 / 100 - 4995 / 10000 * Λ) ^ q :=
          Real.rpow_le_rpow hT0 hT hq0.le
      _ = Real.exp ((142 / 100 - 4995 / 10000 * Λ) * q) := by rw [← Real.exp_mul]
      _ ≤ Real.exp (-(Λ / 103)) := by
          refine Real.exp_le_exp.2 ?_
          have hneg : 142 / 100 - 4995 / 10000 * Λ ≤ 0 := by linarith
          have := mul_le_mul_of_nonpos_left hq1 hneg
          linarith
  -- the error
  have hE := halfErr_le_decay hx
  obtain ⟨hs, -, -⟩ := half_big hx
  rw [← hΛdef] at hE hs
  have hE0 : 0 ≤ smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) := by
    unfold smallQReductionErr
    have hlogz : 0 < Real.log (halfZ x) := Real.log_pos (by
      have : (2 : ℝ) ≤ (halfZ x : ℝ) := by exact_mod_cast hz2
      linarith)
    have hL0 : 0 ≤ 1 + Real.log x := by linarith [Real.add_one_le_exp (110 : ℝ)]
    positivity
  have hE1 : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ≤ Real.exp (-(Λ / 4)) := by
    refine le_trans hE ?_
    rw [hs, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    have h7 : 7 * Λ ≤ Real.exp (Λ / 4) := by
      have h1 : Real.log (7 * Λ) ≤ Λ / 4 := by
        rw [Real.log_mul (by norm_num) hΛ0.ne']
        have h7l : Real.log 7 ≤ 2 := by interval_decide (trust := kernel)
        linarith
      calc 7 * Λ = Real.exp (Real.log (7 * Λ)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (Λ / 4) := Real.exp_le_exp.2 h1
    rw [show -(Λ / 4) + Λ / 2 = Λ / 4 by ring]
    exact h7
  have hEq : smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
      ≤ Real.exp (-(Λ / 103)) := by
    calc smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
        ≤ Real.exp (-(Λ / 4)) ^ q := Real.rpow_le_rpow hE0 hE1 hq0.le
      _ = Real.exp (-(Λ / 4) * q) := by rw [← Real.exp_mul]
      _ ≤ Real.exp (-(Λ / 103)) := by
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul_of_nonpos_left hq1 (by linarith : -(Λ / 4) ≤ 0)
          linarith
  -- the sum
  have hCen0 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q := Real.rpow_nonneg hC0 q
  have hPFc0 : 0 ≤ uPFcAt q (halfSigma x) (halfY x) := by
    unfold uPFcAt; exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hlogy0.le _)
  set E := Real.exp (197 / 100 + Λ / 800 - Λ / 103) with hEdef
  have hsmall : Real.exp (-(Λ / 103)) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hcen' : smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
      * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)) ≤ E := by
    have h1 : uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
        ≤ Real.exp (197 / 100 + Λ / 800) * Real.exp (-(Λ / 103)) :=
      mul_le_mul hCen hPFc hPFc0 (Real.exp_pos _).le
    have h2 : Real.exp (197 / 100 + Λ / 800) * Real.exp (-(Λ / 103)) = E := by
      rw [hEdef, ← Real.exp_add]; ring_nf
    have h3 : 0 ≤ uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
        * uPFcAt q (halfSigma x) (halfY x) := mul_nonneg hCen0 hPFc0
    calc smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
          * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x))
        ≤ 1 * E := mul_le_mul hCRq (by rw [← h2]; exact h1) h3 zero_le_one
      _ = E := one_mul E
  have hLHS : uPFyAt q (halfY x) + halfTail x ^ q
      + smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) ^ q
        * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x))
      + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q ≤ 4 * E := by linarith
  -- the target
  have hV : Λ⁻¹ + (1 - 2 * q) ≤ 18025 / 100000 := by
    have : Λ⁻¹ ≤ 1 / 4000 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΛ
    linarith
  have hV0 : 0 < Λ⁻¹ + (1 - 2 * q) := by
    have : 0 < Λ⁻¹ := inv_pos.2 hΛ0
    linarith
  have hΛq : Real.exp (-(Λ / 1600)) ≤ Λ ^ (-(q / 2)) := by
    rw [rpow_eq_exp_mul_log hΛ0]
    refine Real.exp_le_exp.2 ?_
    have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
    have := mul_le_mul_of_nonneg_right (by linarith : q / 2 ≤ 1 / 4) hl0
    linarith
  have hE5 : 4 * E ≤ 1 / 100 * (100000 / 18025) * Real.exp (-(Λ / 1600)) := by
    have h1 : E = Real.exp (197 / 100 + Λ / 800 - Λ / 103 + Λ / 1600) * Real.exp (-(Λ / 1600)) := by
      rw [hEdef, ← Real.exp_add]; ring_nf
    rw [h1]
    have h2 : Real.exp (197 / 100 + Λ / 800 - Λ / 103 + Λ / 1600) ≤ Real.exp (-5) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-5) ≤ 7 / 1000 := by interval_decide (trust := kernel)
    have h4 : 0 ≤ Real.exp (-(Λ / 1600)) := (Real.exp_pos _).le
    have h5 := mul_le_mul_of_nonneg_right (le_trans h2 h3) h4
    have h6 : 4 * (7 / 1000) ≤ 1 / 100 * (100000 / 18025 : ℝ) := by norm_num
    have h7 := mul_le_mul_of_nonneg_right h6 h4
    linarith
  have hinv : 100000 / 18025 ≤ (Λ⁻¹ + (1 - 2 * q))⁻¹ := by
    rw [← one_div, le_div_iff₀ hV0]
    have := mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 100000 / 18025)
    linarith
  calc _ ≤ 4 * E := hLHS
    _ ≤ 1 / 100 * (100000 / 18025) * Real.exp (-(Λ / 1600)) := hE5
    _ ≤ 1 / 100 * (Λ⁻¹ + (1 - 2 * q))⁻¹ * Λ ^ (-(q / 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hinv (by norm_num)) hΛq
          (Real.exp_pos _).le (by positivity)

/-! ### One cell of the chaos regime -/

/-- The windows' bounds are nonnegative. -/
lemma uWindowBound_nonneg {P : ℕ → WinChaos} (hP : ∀ k, (P k).Valid) {q x : ℝ} (_hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (k : ℕ) : 0 ≤ uWindowBound P q x k := by
  unfold uWindowBound
  refine mul_nonneg (mul_nonneg (thetaPF_nonneg _ _ _ _ (by norm_num))
    (Real.rpow_nonneg (thetaWindowConstQ_nonneg (by norm_num) hq1 k _) _)) ?_
  split_ifs
  · refine le_min zero_le_one (mul_nonneg ?_ ?_)
    · have hl := (hP k).lam
      unfold WinChaos.const shiftMomentConst
      exact le_trans (Real.rpow_nonneg (by nlinarith) _) (le_max_left _ _)
    · have : 0 ≤ 1 - q := by linarith
      exact Real.rpow_nonneg (by positivity) _
  · exact zero_le_one

lemma uGroups_valid {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} (hv₁ : c₁.Valid) (hv₂ : c₂.Valid)
    (hv₃ : c₃.Valid) (hv₄ : c₄.Valid) (hv₅ : c₅.Valid) (hv₆ : c₆.Valid) (hv₇ : c₇.Valid) (k : ℕ) :
    (uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ k).Valid := by
  unfold uGroups
  split_ifs <;> assumption

/-- `(Λ⁻¹ + v)/(1 - e^{-a}) ≤ Γ` on a cell: with `a = qv ≤ 1/8`, `1/(1-e^{-a}) ≤ 1/a + 1/2 + a/10`
(`RMF.inv_one_sub_exp_neg_le_taylor`). -/
lemma cell_geom_le {Λ q ql qu : ℝ} (hΛ : 4000 ≤ Λ) (hql : 0 < ql) (hqlq : ql ≤ q)
    (hqqu : q ≤ qu) (hqu : qu < 1 / 2) :
    (Λ⁻¹ + (1 - 2 * q)) / (1 - Real.exp (-(q * (1 - 2 * q))))
      ≤ 1 / ql + 1 / (ql * (1 - 2 * qu) * 4000)
        + (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) := by
  have hv0 : 0 < 1 - 2 * q := by linarith
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < q * (1 - 2 * q) := mul_pos hq0 hv0
  have ha8 : q * (1 - 2 * q) ≤ 1 / 8 := by nlinarith [sq_nonneg (q - 1 / 4)]
  have hinv := inv_one_sub_exp_neg_le_taylor ha0 ha8
  have hΛ0 : 0 < Λ := by linarith
  have hΛi : Λ⁻¹ ≤ 1 / 4000 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΛ
  have hΛi0 : 0 < Λ⁻¹ := inv_pos.2 hΛ0
  have hd : 0 < 1 - Real.exp (-(q * (1 - 2 * q))) := by
    have : Real.exp (-(q * (1 - 2 * q))) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  rw [div_eq_mul_inv]
  have hV0 : 0 ≤ Λ⁻¹ + (1 - 2 * q) := by linarith
  calc (Λ⁻¹ + (1 - 2 * q)) * (1 - Real.exp (-(q * (1 - 2 * q))))⁻¹
      ≤ (Λ⁻¹ + (1 - 2 * q)) * (1 / (q * (1 - 2 * q)) + 1 / 2 + q * (1 - 2 * q) / 10) :=
        mul_le_mul_of_nonneg_left hinv hV0
    _ = Λ⁻¹ / (q * (1 - 2 * q)) + 1 / q
        + (Λ⁻¹ + (1 - 2 * q)) * (1 / 2 + q * (1 - 2 * q) / 10) := by
        field_simp
        ring
    _ ≤ 1 / (ql * (1 - 2 * qu) * 4000) + 1 / ql
        + (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) := by
        have t1 : Λ⁻¹ / (q * (1 - 2 * q)) ≤ 1 / (ql * (1 - 2 * qu) * 4000) := by
          rw [div_le_div_iff₀ ha0 (by nlinarith)]
          have h1 : ql * (1 - 2 * qu) ≤ q * (1 - 2 * q) := by nlinarith
          have h2 : Λ⁻¹ * (ql * (1 - 2 * qu) * 4000) ≤ 1 * (ql * (1 - 2 * qu)) := by
            have := mul_le_mul_of_nonneg_right hΛi (by nlinarith : (0 : ℝ) ≤ ql * (1 - 2 * qu))
            nlinarith
          nlinarith
        have t2 : 1 / q ≤ 1 / ql := one_div_le_one_div_of_le hql hqlq
        have t3 : (Λ⁻¹ + (1 - 2 * q)) * (1 / 2 + q * (1 - 2 * q) / 10)
            ≤ (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) := by
          have h1 : Λ⁻¹ + (1 - 2 * q) ≤ 1 / 4000 + (1 - 2 * ql) := by linarith
          have h2 : 1 / 2 + q * (1 - 2 * q) / 10 ≤ 1 / 2 + qu * (1 - 2 * ql) / 10 := by
            have : q * (1 - 2 * q) ≤ qu * (1 - 2 * ql) := by nlinarith
            linarith
          exact mul_le_mul h1 h2 (by nlinarith) (by linarith)
        linarith
    _ = _ := by ring

set_option maxHeartbeats 16000000 in
-- the assembly and four bounds
/-- **One cell of the chaos regime**: for `x` with `Λ ≥ 4000` and `q ∈ [q_l, q_u] ⊆ [0.41, 0.49]`,
the windows' parameters and numerals of `RMF.uMeso_chaos_le`, and the certificate `hfin`,
`E|S(x)|^{2q} ≤ 25(Λ⁻¹ + 1 - 2q)⁻¹Λ^{-q/2}`. -/
theorem u_cell_chaos {X : ℕ → Ω → ℂ} {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ)
    {x q ql qu : ℝ} (hx : Real.exp (Real.exp 110) ≤ x)
    (hΛ : 4000 ≤ Real.log (Real.log x)) (hql : 41 / 100 ≤ ql) (hqlq : ql ≤ q) (hqqu : q ≤ qu)
    (hqu : qu ≤ 49 / 100) {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : WinChaos} (hv₁ : c₁.Valid) (hv₂ : c₂.Valid)
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
    (hfar : (1 - 2 * ql) * (3 / 2 * Real.log 880) ≤ 2)
    (hfin : 1 / 100
      + Real.exp (ql * Real.log (33885 / 100000)) * (1 + 1 / ((1 - 2 * qu) * 4000))
        * ((1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql))
      + Real.exp (ql * Real.log (33885 / 100000)) * (3 / 2) ^ (-(qu * (1 - 2 * qu)))
        * (1 / ql + 1 / (ql * (1 - 2 * qu) * 4000)
          + (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10))
        * ((b₁ * Real.exp (-(4 * (qu * (1 - 2 * qu))))
            - (b₁ - b₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
            - (b₂ - b₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
            - (b₃ - b₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
            - (b₄ - b₅) * Real.exp (-(31 * (ql * (1 - 2 * ql))))
            - (b₅ - b₆) * Real.exp (-(61 * (ql * (1 - 2 * ql))))
            - (b₆ - b₇) * Real.exp (-(97 * (ql * (1 - 2 * ql)))))
          + G₇ * Real.exp (qu * (1 - 2 * qu)
            - 4000 * (qu * (1 - 2 * qu) / 4 - 1 / 1600))) ≤ 25) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
        ∂μ)
      ≤ 25 * ((Real.log (Real.log x))⁻¹ + (1 - 2 * q))⁻¹
        * Real.log (Real.log x) ^ (-(q / 2)) := by
  haveI := hX.isProbabilityMeasure
  obtain ⟨-, hL, hΛ110, -, -, -⟩ := half_params hx
  obtain ⟨hy2, -, -, -, -, -⟩ := halfY_facts hx
  obtain ⟨hz2, hzy, -⟩ := halfZ_facts hx
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  set Λ := Real.log (Real.log x) with hΛdef
  have hΛ0 : 0 < Λ := by linarith
  have hq0 : 0 < q := by linarith
  have hq5 : q ≤ 1 / 2 := by linarith
  have hv0 : 0 < 1 - 2 * q := by linarith
  set a := q * (1 - 2 * q) with hadef
  have ha0 : 0 < a := mul_pos hq0 hv0
  set a₀ := qu * (1 - 2 * qu) with ha₀def
  have ha₀a : a₀ ≤ a := mul_one_sub_two_mul_anti (by linarith) hqqu
  have ha₀n : 98 / 10000 ≤ a₀ := q_mul_one_sub_ge (by linarith) hqu
  have hΛi : Λ⁻¹ ≤ 1 / 4000 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hΛ
  have hΛi0 : 0 < Λ⁻¹ := inv_pos.2 hΛ0
  set V := Λ⁻¹ + (1 - 2 * q) with hVdef
  have hV0 : 0 < V := by linarith
  have hΛq0 : 0 < Λ ^ (-(q / 2)) := Real.rpow_pos_of_pos hΛ0 _
  set P := uGroups c₁ c₂ c₃ c₄ c₅ c₆ c₇ with hPdef
  have hPv : ∀ k, (P k).Valid := uGroups_valid hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇
  -- the pieces
  have hasm := integral_rpow_weightedRademacherSum_le_u_assembly hX hx hq0 hq5 hPv uFarP_valid
    (⌈Real.log Λ⌉₊ + 4)
  have hsmall := uSmall_chaos_le (q := q) hx hΛ (by linarith) (by linarith)
  have hfarb := uFarBound_uFarP_le hx hΛ hq0 hq5
  have hmeso := uMeso_chaos_le hx hΛ hql hqlq hqqu hqu hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇ hN₁ hN₂ hN₃
    hN₄ hN₅ hN₆ hN₇ hA₁ hA₂ hA₃ hA₄ hA₅ hA₆ hA₇ hG₁ hG₂ hG₃ hG₄ hG₅ hG₆ hG₇ hb₁ hb₂ hb₃ hb₄
    hb₅ hb₆ hb₇ h12 h23 h34 h45 h56 h67
  rw [← hΛdef, ← hadef, ← hPdef] at hmeso
  rw [← hΛdef] at hsmall hfarb
  -- the reduction's constant
  have hη : 0 < halfEta x := by rw [halfEta]; positivity
  have hε : 0 < halfEps x := by rw [halfEps]; positivity
  set CR := smallQReductionConst (halfY x) (halfZ x) (halfEta x) (halfEps x) (1 / 32) with hCRdef
  have hCR0 : 0 ≤ CR := (smallQReductionConst_pos hz2 hzy hη hε).le
  have hCR1 : CR ≤ 33885 / 100000 := halfCR_le hx
  have hCRq0 : 0 ≤ CR ^ q := Real.rpow_nonneg hCR0 q
  have hCRq : CR ^ q ≤ Real.exp (ql * Real.log (33885 / 100000)) := by
    calc CR ^ q ≤ (33885 / 100000 : ℝ) ^ q := Real.rpow_le_rpow hCR0 hCR1 hq0.le
      _ ≤ (33885 / 100000 : ℝ) ^ ql :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hqlq
      _ = Real.exp (ql * Real.log (33885 / 100000)) := by
          rw [rpow_eq_exp_mul_log (by norm_num)]
  set CRn := Real.exp (ql * Real.log (33885 / 100000)) with hCRn
  have hCRn0 : 0 ≤ CRn := (Real.exp_pos _).le
  -- the far range
  set τ := V⁻¹ * Λ ^ (-(q / 2)) with hτdef
  have hτ0 : 0 < τ := mul_pos (inv_pos.2 hV0) hΛq0
  have hVv : V ≤ (1 + 1 / ((1 - 2 * qu) * 4000)) * (1 - 2 * q) := by
    have hvqu : 1 - 2 * qu ≤ 1 - 2 * q := by linarith
    have hvqu0 : 0 < 1 - 2 * qu := by linarith
    have : Λ⁻¹ ≤ 1 / ((1 - 2 * qu) * 4000) * (1 - 2 * q) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      have := mul_le_mul hΛi hvqu hvqu0.le (by norm_num)
      nlinarith
    rw [hVdef]
    linarith
  have hfar880 : (1 - 2 * q) * (880 : ℝ) ^ (3 / 2 * q) ≤ (1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql) :=
    one_sub_two_mul_rpow_le hqlq (by norm_num) hfar (by linarith)
  have hR_F : CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x
      ≤ τ * (CRn * (1 + 1 / ((1 - 2 * qu) * 4000))
        * ((1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql))) := by
    have h880 : 0 ≤ (880 : ℝ) ^ (3 / 2 * q) := Real.rpow_nonneg (by norm_num) _
    have h1 : Λ ^ (-(q / 2)) * (880 : ℝ) ^ (3 / 2 * q) = τ * (V * (880 : ℝ) ^ (3 / 2 * q)) := by
      rw [hτdef]; field_simp
    have h2 : V * (880 : ℝ) ^ (3 / 2 * q)
        ≤ (1 + 1 / ((1 - 2 * qu) * 4000)) * ((1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql)) := by
      have hk0 : 0 ≤ 1 + 1 / ((1 - 2 * qu) * 4000) := by
        have : 0 < 1 - 2 * qu := by linarith
        positivity
      calc V * (880 : ℝ) ^ (3 / 2 * q)
          ≤ (1 + 1 / ((1 - 2 * qu) * 4000)) * (1 - 2 * q) * (880 : ℝ) ^ (3 / 2 * q) :=
            mul_le_mul_of_nonneg_right hVv h880
        _ = (1 + 1 / ((1 - 2 * qu) * 4000)) * ((1 - 2 * q) * (880 : ℝ) ^ (3 / 2 * q)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hfar880 hk0
    have hF0 : 0 ≤ uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x := by
      unfold uFarBound
      split_ifs
      · exact le_min (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by
          refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (Real.rpow_nonneg (by positivity) _)
          refine mul_nonneg (mul_nonneg ?_ (Real.rpow_nonneg ?_ _))
            (Real.rpow_nonneg (by positivity) _)
          · change 0 ≤ shiftMomentConst _ _ _ _ _ _ _ _
            unfold shiftMomentConst
            exact le_trans (Real.rpow_nonneg (by change (0 : ℝ) ≤ 1 * (1 + 67 / 2); norm_num) _)
              (le_max_left _ _)
          · have := Real.add_one_le_exp (1 : ℝ)
            exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.exp_pos _).le) _)
      · exact Real.rpow_nonneg (by positivity) _
    calc CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x
        ≤ CRn * (Λ ^ (-(q / 2)) * (880 : ℝ) ^ (3 / 2 * q)) :=
          mul_le_mul hCRq hfarb hF0 hCRn0
      _ = τ * (CRn * (V * (880 : ℝ) ^ (3 / 2 * q))) := by rw [h1]; ring
      _ ≤ τ * (CRn * ((1 + 1 / ((1 - 2 * qu) * 4000))
          * ((1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCRn0) hτ0.le
      _ = _ := by ring
  -- the windows
  set Sw := ∑ k ∈ Finset.Ico 4 (tenJ x), uWindowBound P q x k with hSwdef
  have hSw0 : 0 ≤ Sw := Finset.sum_nonneg fun k _ => uWindowBound_nonneg hPv hq0.le (by linarith) k
  set K4 := ⌊Λ / 4⌋₊ with hK4def
  set Abel := b₁ * Real.exp (-(4 * a₀)) - (b₁ - b₂) * Real.exp (-(5 * (ql * (1 - 2 * ql))))
    - (b₂ - b₃) * Real.exp (-(6 * (ql * (1 - 2 * ql))))
    - (b₃ - b₄) * Real.exp (-(7 * (ql * (1 - 2 * ql))))
    - (b₄ - b₅) * Real.exp (-(31 * (ql * (1 - 2 * ql))))
    - (b₅ - b₆) * Real.exp (-(61 * (ql * (1 - 2 * ql))))
    - (b₆ - b₇) * Real.exp (-(97 * (ql * (1 - 2 * ql)))) with hAbel
  have hG₇0 : 0 ≤ G₇ := by
    obtain ⟨-, hly⟩ := halfY_loglog_le hx
    exact le_trans (Real.rpow_nonneg (le_trans zero_le_one
      (one_le_thetaWindowConstQ (by norm_num) (by norm_num) (by linarith) 97 (halfY x))) _)
      (hG₇ _ hly)
  have hd : 0 < 1 - Real.exp (-a) := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hTH : (3 / 2 : ℝ) ^ (-a) ≤ (3 / 2) ^ (-a₀) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hTH0 : 0 < (3 / 2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  -- the Jensen tail's factor
  have htailJ : Real.exp (-(a * K4)) * Λ ^ (q / 2)
      ≤ Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600)) := by
    have hK4 : Λ / 4 - 1 ≤ (K4 : ℝ) := by
      have := Nat.lt_floor_add_one (Λ / 4); rw [← hK4def] at this; linarith
    have h1 : Real.exp (-(a * K4)) ≤ Real.exp (-(a₀ * (Λ / 4 - 1))) := by
      refine Real.exp_le_exp.2 ?_
      have hK0 : 0 ≤ (K4 : ℝ) := Nat.cast_nonneg _
      have := mul_le_mul ha₀a hK4 (by linarith) ha0.le
      linarith
    have h2 : Λ ^ (q / 2) ≤ Real.exp (Λ / 1600) := by
      rw [rpow_eq_exp_mul_log hΛ0]
      refine Real.exp_le_exp.2 ?_
      have hl := log_le_div_four_hundred hΛ
      have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg (by linarith)
      have := mul_le_mul_of_nonneg_right (by linarith : q / 2 ≤ 1 / 4) hl0
      linarith
    calc Real.exp (-(a * K4)) * Λ ^ (q / 2)
        ≤ Real.exp (-(a₀ * (Λ / 4 - 1))) * Real.exp (Λ / 1600) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hΛ0.le _) (Real.exp_pos _).le
      _ = Real.exp (a₀ - Λ * (a₀ / 4 - 1 / 1600)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600)) := by
          refine Real.exp_le_exp.2 ?_
          have : 0 ≤ a₀ / 4 - 1 / 1600 := by linarith
          nlinarith
  -- the windows against `τ`
  have hgeom : V / (1 - Real.exp (-a)) ≤ 1 / ql + 1 / (ql * (1 - 2 * qu) * 4000)
      + (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) :=
    cell_geom_le hΛ (by linarith) hqlq hqqu (by linarith)
  set Γ := 1 / ql + 1 / (ql * (1 - 2 * qu) * 4000)
    + (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) with hΓdef
  have hR_M : CR ^ q * Sw
      ≤ τ * (CRn * (3 / 2) ^ (-a₀) * Γ
        * (Abel + G₇ * Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600)))) := by
    -- `Sw ≤ (3/2)^{-a}Λ^{-q/2}(Abel + G₇e^{-aK4}Λ^{q/2})/(1 - e^{-a})`
    have hrhs : (3 / 2) ^ (-a) * Λ ^ (-(q / 2)) * Abel
        + (3 / 2) ^ (-a) * G₇ * Real.exp (-(a * K4))
        = (3 / 2) ^ (-a) * Λ ^ (-(q / 2))
          * (Abel + G₇ * (Real.exp (-(a * K4)) * Λ ^ (q / 2))) := by
      have e : Λ ^ (-(q / 2)) * Λ ^ (q / 2) = 1 := by
        rw [← Real.rpow_add hΛ0]; simp
      linear_combination (3 / 2 : ℝ) ^ (-a) * G₇ * Real.exp (-(a * K4)) * e.symm
    rw [hrhs] at hmeso
    set Br := Abel + G₇ * (Real.exp (-(a * K4)) * Λ ^ (q / 2)) with hBr
    have hBr0 : 0 ≤ Br := by
      have h1 : 0 ≤ (1 - Real.exp (-a)) * Sw := mul_nonneg hd.le hSw0
      have h2 : 0 < (3 / 2 : ℝ) ^ (-a) * Λ ^ (-(q / 2)) := mul_pos hTH0 hΛq0
      by_contra hneg
      have := mul_neg_of_pos_of_neg h2 (lt_of_not_ge hneg)
      linarith
    have hBr1 : Br ≤ Abel + G₇ * Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600)) := by
      rw [hBr]
      have := mul_le_mul_of_nonneg_left htailJ hG₇0
      linarith
    have hSw1 : Sw ≤ (3 / 2) ^ (-a) * Λ ^ (-(q / 2)) * Br / (1 - Real.exp (-a)) := by
      rw [le_div_iff₀ hd]; linarith
    have e2 : (3 / 2 : ℝ) ^ (-a) * Λ ^ (-(q / 2)) * Br / (1 - Real.exp (-a))
        = τ * ((3 / 2) ^ (-a) * (V / (1 - Real.exp (-a))) * Br) := by
      rw [hτdef]; field_simp
    have hΓ0 : 0 ≤ Γ := by
      have h1 : 0 < 1 - 2 * qu := by linarith
      have h2 : 0 ≤ 1 - 2 * ql := by linarith
      have hql0 : 0 < ql := by linarith
      have t1 : 0 ≤ 1 / ql := by positivity
      have t2 : 0 ≤ 1 / (ql * (1 - 2 * qu) * 4000) := by positivity
      have t3 : 0 ≤ (1 / 4000 + (1 - 2 * ql)) * (1 / 2 + qu * (1 - 2 * ql) / 10) := by
        have : 0 ≤ qu := by linarith
        positivity
      rw [hΓdef]
      linarith
    have hVd0 : 0 ≤ V / (1 - Real.exp (-a)) := div_nonneg hV0.le hd.le
    calc CR ^ q * Sw ≤ CRn * (τ * ((3 / 2) ^ (-a) * (V / (1 - Real.exp (-a))) * Br)) := by
          rw [← e2]; exact mul_le_mul hCRq hSw1 hSw0 hCRn0
      _ ≤ CRn * (τ * ((3 / 2) ^ (-a₀) * Γ
          * (Abel + G₇ * Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hτ0.le) hCRn0
          exact mul_le_mul (mul_le_mul hTH hgeom hVd0 (Real.rpow_nonneg (by norm_num) _)) hBr1
            hBr0 (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hΓ0)
      _ = _ := by ring
  -- together
  have hfin' : 1 / 100
      + CRn * (1 + 1 / ((1 - 2 * qu) * 4000)) * ((1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql))
      + CRn * (3 / 2) ^ (-a₀) * Γ * (Abel + G₇ * Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600)))
      ≤ 25 := hfin
  have htot : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ) ≤ 1 / 100 * V⁻¹ * Λ ^ (-(q / 2))
        + CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + CR ^ q * Sw := by
    have e : uPFyAt q (halfY x) + halfTail x ^ q
        + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q * uPFcAt q (halfSigma x) (halfY x)
          + uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + Sw)
        + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q
        = (uPFyAt q (halfY x) + halfTail x ^ q
          + CR ^ q * (uCenAt q (halfSigma x) (halfY x) (tenJ x) ^ q
            * uPFcAt q (halfSigma x) (halfY x))
          + smallQReductionErr x (halfZ x) (halfEta x) (halfEps x) ^ q)
          + CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + CR ^ q * Sw := by ring
    rw [e] at hasm
    linarith
  calc _ ≤ 1 / 100 * V⁻¹ * Λ ^ (-(q / 2))
        + CR ^ q * uFarBound uFarP (⌈Real.log Λ⌉₊ + 4) q x + CR ^ q * Sw := htot
    _ ≤ τ * (1 / 100
        + CRn * (1 + 1 / ((1 - 2 * qu) * 4000)) * ((1 - 2 * ql) * (880 : ℝ) ^ (3 / 2 * ql))
        + CRn * (3 / 2) ^ (-a₀) * Γ
          * (Abel + G₇ * Real.exp (a₀ - 4000 * (a₀ / 4 - 1 / 1600)))) := by
        have e : 1 / 100 * V⁻¹ * Λ ^ (-(q / 2)) = τ * (1 / 100) := by rw [hτdef]; ring
        rw [e]
        nlinarith
    _ ≤ τ * 25 := mul_le_mul_of_nonneg_left hfin' hτ0.le
    _ = 25 * V⁻¹ * Λ ^ (-(q / 2)) := by rw [hτdef]; ring

end RMF
