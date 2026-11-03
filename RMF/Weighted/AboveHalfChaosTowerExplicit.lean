/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.AboveHalfChaosWindowExplicit
import RMF.Weighted.AboveHalfTowerExplicit

/-!
# The hierarchy above `q = ½` with the chaos

The levels with the chaos (`RMF.bandLevelCh`, `RMF.bottomLevelCh`) cleaned and normalised as the
Jensen ones, their windows kept as the chaos-weighted sums `RMF.chaosWinSum`
(`RMF.pfFull_mul_bandLevelCh_le`, `RMF.bottomLevelCh_le`), and the hierarchy with them
(`RMF.rpow_inv_integral_rpow_weightedRademacherSum_le_chaosHierarchy`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The windows' sums with the chaos -/

/-- The chaos-weighted window sum of a level with `J` windows below the top `z`:
`∑_{1 ≤ m < J} e^{-am}·RMF.chaosMult q m z`, `a = q(2q-1)`. -/
noncomputable def chaosWinSum (q : ℝ) (J z : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 J, Real.exp (-(q * (2 * q - 1) * m)) * chaosMult q m z

lemma chaosWinSum_nonneg {q : ℝ} (hq1 : q ≤ 1) (J z : ℕ) : 0 ≤ chaosWinSum q J z :=
  Finset.sum_nonneg fun m _ => mul_nonneg (Real.exp_pos _).le (chaosMult_nonneg hq1 m z)

/-- `∑_{k<n} f(n-k) = ∑_{1≤m<n+1} f(m)`. -/
lemma sum_range_sub_eq_sum_Ico (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, f (n - k) = ∑ m ∈ Finset.Ico 1 (n + 1), f m := by
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega,
    ← Finset.sum_range_reflect (fun j => f (1 + j)) n]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := Finset.mem_range.1 hk
  congr 1
  omega

lemma winNoSplit_nonneg {q T : ℝ} (hT : 0 < T) (y z : ℕ) : 0 ≤ winNoSplit q T y z := by
  rw [winNoSplit, mBand]
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : (0 : ℝ) ≤ Real.log z := Real.log_natCast_nonneg _
  have h2 : (0 : ℝ) ≤ Real.log y := Real.log_natCast_nonneg _
  exact Real.rpow_nonneg (by positivity) _

lemma winNoSplitFull_nonneg {q T : ℝ} (hT : 0 < T) (z : ℕ) : 0 ≤ winNoSplitFull q T z := by
  rw [winNoSplitFull, mFull]
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : (0 : ℝ) ≤ Real.log z := Real.log_natCast_nonneg _
  exact Real.rpow_nonneg (by positivity) _

lemma winBandCh_nonneg {q : ℝ} (hq1 : q ≤ 1) (y z k : ℕ) : 0 ≤ winBandCh q y z k :=
  le_min (winNoSplit_nonneg (bandT_pos k) y z)
    (mul_nonneg (winSplit_nonneg hq1 (bandT_pos k)) (chaosMult_nonneg hq1 _ z))

lemma winBotCh_nonneg {q : ℝ} (hq1 : q ≤ 1) (z k : ℕ) : 0 ≤ winBotCh q z k := by
  have hT : 0 < bottomT 1 2 z k := Real.exp_pos _
  exact le_min (winNoSplitFull_nonneg hT z)
    (mul_nonneg (winSplitFull_nonneg hq1 hT) (chaosMult_nonneg hq1 _ z))

/-! ### The windows, cleaned -/

/-- **A band's windows with the chaos, cleaned.**  For `½ < q ≤ 1` and `2 ≤ y ≤ z` with
`log y ≥ 1000`: the windows of `RMF.bandLevelCh` satisfy the windows' hypothesis of
`RMF.pfFull_mul_bandLevelW_le_clean` with `W_B = ω·(1.5 log z)^a·RMF.chaosWinSum q J z`: the top
window without a split, the others split (`RMF.winSplit_le_clean`) times their chaos factor. -/
theorem bandWindows_chaos_clean {q : ℝ} {y z : ℕ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hy : 2 ≤ y)
    (hyz : y ≤ z) (hly : 1000 ≤ Real.log y) :
    pfFull q y * (∑ k ∈ Finset.range (bandJ 1 y z), winBandCh q y z k
        + (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q)
      ≤ Real.log z ^ (q * (2 * q - 1)) * ((Real.log y / Real.log z) ^ (q * (2 * q - 1))
          * pfC1 q * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
            + (Real.exp 0.0181 / Real.pi) ^ q))
        + pfC1 q * (omegaClean q * (3 / 2 * Real.log z) ^ (q * (2 * q - 1))
          * chaosWinSum q (bandJ 1 y z) z) := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hyzR : (y : ℝ) ≤ z := by exact_mod_cast hyz
  have hly0 : 0 < Real.log y := by linarith
  have hlz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyzR
  have hlz0 : 0 < Real.log z := by linarith
  have hκ1 : 1 ≤ Real.log z / Real.log y := by rw [le_div_iff₀ hly0]; linarith
  have hκ0 : 0 < Real.log z / Real.log y := by linarith
  have hlogκ : 0 ≤ Real.log (Real.log z / Real.log y) := Real.log_nonneg hκ1
  have hJeq : bandJ 1 y z = ⌈Real.log (Real.log z / Real.log y)⌉₊ := by rw [bandJ, one_mul]
  have hJ1 : Real.log (Real.log z / Real.log y) ≤ (bandJ 1 y z : ℝ) := by
    rw [hJeq]; exact Nat.le_ceil _
  have hJ2 : (bandJ 1 y z : ℝ) < Real.log (Real.log z / Real.log y) + 1 := by
    rw [hJeq]; exact Nat.ceil_lt_add_one hlogκ
  have heJ : Real.log z / Real.log y ≤ Real.exp (bandJ 1 y z) := by
    calc Real.log z / Real.log y = Real.exp (Real.log (Real.log z / Real.log y)) :=
          (Real.exp_log hκ0).symm
      _ ≤ Real.exp (bandJ 1 y z) := Real.exp_le_exp.2 hJ1
  have hpf0 : 0 ≤ pfFull q y := by rw [pfFull]; positivity
  have hM : mBand y z ≤ Real.log z / Real.log y * Real.exp 0.0181 := by
    rw [mBand]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h1 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log y)
    have h2 := nine_div_le_of_le (by linarith : (999 : ℝ) ≤ Real.log z)
    linarith
  have hmB0 : 0 ≤ mBand y z := by rw [mBand]; positivity
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  -- the far range
  have hfar : (mBand y z / (Real.pi * 1 * Real.exp (bandJ 1 y z))) ^ q
      ≤ (Real.exp 0.0181 / Real.pi) ^ q := by
    refine Real.rpow_le_rpow (by positivity) ?_ hq0'
    rw [mul_one, div_le_div_iff₀ (by positivity) Real.pi_pos]
    have := mul_le_mul hM heJ hκ0.le (by positivity)
    nlinarith [Real.pi_pos, Real.exp_pos 0.0181, Real.exp_pos (bandJ 1 y z : ℝ)]
  set a := q * (2 * q - 1) with hadef
  set cy := Real.exp (a * (0.2641 + 9.0028 / Real.log y + (2 - 2 * q) / 3)) with hcydef
  have hcy : cy ≤ pfC1 q := by
    rw [hcydef, pfC1, ← hadef]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ha.le)
    have h1 : 9.0028 / Real.log y ≤ 0.0091 := by rw [div_le_iff₀ hly0]; linarith
    linarith
  have hcy0 : 0 ≤ cy := (Real.exp_pos _).le
  have hpfeq : pfFull q y = Real.log y ^ a * cy := by rw [pfFull, hcydef]
  have hlya : Real.log y ^ a = Real.log z ^ a * (Real.log y / Real.log z) ^ a := by
    rw [← Real.mul_rpow hlz0.le (div_nonneg hly0.le hlz0.le)]
    congr 1
    field_simp
  have hω : 0 ≤ omegaClean q := omegaClean_nonneg hq1
  have hJF : 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
      + (Real.exp 0.0181 / Real.pi) ^ q := by positivity
  have hS0 := chaosWinSum_nonneg hq1 (bandJ 1 y z) z
  -- the top window and the far range, by `(PF) ≤ log^a y·pfC1`
  have hPle : pfFull q y ≤ Real.log y ^ a * pfC1 q := by
    rw [hpfeq]; exact mul_le_mul_of_nonneg_left hcy (Real.rpow_nonneg hly0.le _)
  have hJFpart : pfFull q y * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + (Real.exp 0.0181 / Real.pi) ^ q)
      ≤ Real.log z ^ a * ((Real.log y / Real.log z) ^ a * pfC1 q
        * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q)) := by
    calc pfFull q y * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q)
        ≤ (Real.log y ^ a * pfC1 q) * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) := mul_le_mul_of_nonneg_right hPle hJF
      _ = _ := by rw [hlya]; ring
  -- the windows
  set J := bandJ 1 y z with hJdef
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · have hsum0 : ∑ k ∈ Finset.range J, winBandCh q y z k = 0 := by
      rw [hJ0, Finset.sum_range_zero]
    rw [hsum0, zero_add]
    have hfar' := mul_le_mul_of_nonneg_left hfar hpf0
    have h0 : pfFull q y * (Real.exp 0.0181 / Real.pi) ^ q
        ≤ pfFull q y * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
          + (Real.exp 0.0181 / Real.pi) ^ q) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.rpow_nonneg (by positivity :
        (0 : ℝ) ≤ (Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) q]) hpf0
    have hW0 : 0 ≤ pfC1 q * (omegaClean q * (3 / 2 * Real.log z) ^ a * chaosWinSum q J z) := by
      have : 0 ≤ pfC1 q := (Real.exp_pos _).le
      have : 0 ≤ (3 / 2 * Real.log z) ^ a := Real.rpow_nonneg (by positivity) _
      positivity
    linarith
  obtain ⟨n, hn⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  have hsum_split : ∑ k ∈ Finset.range J, winBandCh q y z k
      = ∑ k ∈ Finset.range n, winBandCh q y z (k + 1) + winBandCh q y z 0 := by
    rw [hn, Finset.sum_range_succ']
  rw [hsum_split]
  -- the top window, without a split
  have htop : winBandCh q y z 0 ≤ ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q := by
    refine le_trans (min_le_left _ _) ?_
    rw [bandT_one_eq (by linarith) 0, Nat.cast_zero, sub_zero, ← hJdef]
    refine le_trans (winNoSplit_le_clean hq0' hy hyz hly) (Real.rpow_le_rpow
      (by positivity) ?_ hq0')
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    have := mul_le_mul_of_nonneg_left heJ (mul_nonneg he1 (Real.exp_pos 0.0181).le)
    nlinarith [Real.pi_pos]
  -- the split windows, with their chaos factors
  have hsplit : ∀ k ∈ Finset.range n, winBandCh q y z (k + 1)
      ≤ (3 / 2 * (Real.log z / Real.log y)) ^ a * omegaClean q
        * (Real.exp (-(a * ((n - k : ℕ) : ℝ))) * chaosMult q (n - k) z) := by
    intro k hk
    have hkn := Finset.mem_range.1 hk
    refine le_trans (min_le_right _ _) ?_
    have hJk : bandJ 1 y z - (k + 1) = n - k := by rw [← hJdef, hn]; omega
    rw [hJk]
    have hm : ((J : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) := by
      rw [hn, Nat.cast_sub hkn.le]; push_cast; ring
    rw [bandT_one_eq (by linarith) (k + 1), ← hJdef, hm]
    have hnk : (1 : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
      have : 1 ≤ n - k := by omega
      exact_mod_cast this
    have hnκ : ((n - k : ℕ) : ℝ) < Real.log (Real.log z / Real.log y) := by
      have h1 : ((J : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hn]; push_cast; ring
      have h2 : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
      linarith
    have hexp : Real.exp ((n - k : ℕ) : ℝ) ≤ 3 / 2 * (Real.log z / Real.log y) := by
      have h1 : Real.exp ((n - k : ℕ) : ℝ) ≤ Real.exp (Real.log (Real.log z / Real.log y)) :=
        Real.exp_le_exp.2 hnκ.le
      rw [Real.exp_log hκ0] at h1
      linarith
    have hw := winSplit_le_clean hq0.le hq1 hy hyz hly hnk hexp
    have hχ0 := chaosMult_nonneg hq1 (n - k) z
    refine le_trans (mul_le_mul_of_nonneg_right hw hχ0) (le_of_eq ?_)
    rw [div_exp_rpow (by positivity)]
    ring
  have hS := Finset.sum_le_sum hsplit
  rw [← Finset.mul_sum] at hS
  have hre : ∑ k ∈ Finset.range n, Real.exp (-(a * ((n - k : ℕ) : ℝ))) * chaosMult q (n - k) z
      = chaosWinSum q J z := by
    rw [chaosWinSum, ← hadef, hn]
    exact sum_range_sub_eq_sum_Ico (fun m => Real.exp (-(a * (m : ℝ))) * chaosMult q m z) n
  rw [hre] at hS
  have hlzeq : Real.log y ^ a * (3 / 2 * (Real.log z / Real.log y)) ^ a
      = (3 / 2 * Real.log z) ^ a := by
    rw [← Real.mul_rpow hly0.le (by positivity)]
    congr 1
    field_simp
  have hsplit_tot : pfFull q y * ∑ k ∈ Finset.range n, winBandCh q y z (k + 1)
      ≤ pfC1 q * (omegaClean q * (3 / 2 * Real.log z) ^ a * chaosWinSum q J z) := by
    calc pfFull q y * ∑ k ∈ Finset.range n, winBandCh q y z (k + 1)
        ≤ (Real.log y ^ a * cy) * ((3 / 2 * (Real.log z / Real.log y)) ^ a * omegaClean q
          * chaosWinSum q J z) := by
          rw [← hpfeq]; exact mul_le_mul_of_nonneg_left hS hpf0
      _ = cy * (omegaClean q * (Real.log y ^ a * (3 / 2 * (Real.log z / Real.log y)) ^ a)
          * chaosWinSum q J z) := by ring
      _ = cy * (omegaClean q * (3 / 2 * Real.log z) ^ a * chaosWinSum q J z) := by rw [hlzeq]
      _ ≤ pfC1 q * (omegaClean q * (3 / 2 * Real.log z) ^ a * chaosWinSum q J z) := by
          have : 0 ≤ (3 / 2 * Real.log z) ^ a := Real.rpow_nonneg (by positivity) _
          exact mul_le_mul_of_nonneg_right hcy (by positivity)
  have htop' := mul_le_mul_of_nonneg_left htop hpf0
  have hfar' := mul_le_mul_of_nonneg_left hfar hpf0
  have e : pfFull q y * (∑ k ∈ Finset.range n, winBandCh q y z (k + 1) + winBandCh q y z 0
        + (mBand y z / (Real.pi * 1 * Real.exp (J : ℝ))) ^ q)
      = pfFull q y * ∑ k ∈ Finset.range n, winBandCh q y z (k + 1)
        + pfFull q y * winBandCh q y z 0
        + pfFull q y * (mBand y z / (Real.pi * 1 * Real.exp (J : ℝ))) ^ q := by ring
  rw [e]
  have e2 : pfFull q y * (((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + (Real.exp 0.0181 / Real.pi) ^ q)
      = pfFull q y * ((Real.exp 1 - 1) * Real.exp 0.0181 / Real.pi) ^ q
        + pfFull q y * (Real.exp 0.0181 / Real.pi) ^ q := by ring
  linarith

/-- **The bottom's windows with the chaos, cleaned.**  For `½ < q ≤ 1`, `2 ≤ z` with
`log z ≥ 1500`: the nine top windows of `RMF.bottomLevelCh` are at most the Jensen ones
(`RMF.botTopSum`), and the rest sum to at most `pfC1·ω·(1.5 log z)^a·RMF.chaosWinSum q (J-8) z`. -/
theorem bottomWindows_chaos_clean {q : ℝ} {z : ℕ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hz : 2 ≤ z)
    (hlz : 1500 ≤ Real.log z) :
    ∑ k ∈ Finset.range 9, winBotCh q z k ≤ botTopSum q z
    ∧ ∑ k ∈ Finset.Ico 9 (bottomJ 1 2 z), winBotCh q z k
      ≤ pfC1 q * omegaClean q * (3 / 2 * Real.log z) ^ (q * (2 * q - 1))
        * chaosWinSum q (bottomJ 1 2 z - 8) z := by
  have hq0' : (0 : ℝ) ≤ q := by linarith
  have ha' : 0 < q * (2 * q - 1) := mul_pos (by linarith) (by linarith)
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz0 : 0 < Real.log z := by linarith
  have hc1 : 0 ≤ pfC1 q := (Real.exp_pos _).le
  have hω : 0 ≤ omegaClean q := omegaClean_nonneg hq1
  refine ⟨Finset.sum_le_sum fun k _ => ?_, ?_⟩
  · rw [winBotCh]
    have hT : 0 < bottomT 1 2 z k := Real.exp_pos _
    exact min_le_min le_rfl (mul_le_of_le_one_right (winSplitFull_nonneg hq1 hT)
      (chaosMult_le_one _ _ _))
  set a := q * (2 * q - 1) with hadef
  set J := bottomJ 1 2 z with hJdef
  have hJ1 : Real.log (2 * Real.log z) ≤ (J : ℝ) := by
    have := Nat.le_ceil (Real.log (2 * Real.log z / 1))
    rw [div_one] at this
    rw [hJdef, bottomJ]
    simpa using this
  have hJ9 : 9 ≤ J := by
    have h8 : (8 : ℝ) < Real.log (2 * Real.log z) := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have := exp_eight_bounds.2
      linarith
    have : (8 : ℝ) < J := lt_of_lt_of_le h8 hJ1
    exact_mod_cast this
  have hT : ∀ k : ℕ, bottomT 1 2 z k = Real.exp ((J : ℝ) - k) / Real.log z := by
    intro k
    rw [bottomT, ← hJdef, show Real.log (1 / Real.log z) + (J : ℝ) - k
        = Real.log (1 / Real.log z) + ((J : ℝ) - k) by ring, Real.exp_add,
      Real.exp_log (by positivity)]
    field_simp
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (J - 9), winBotCh q z (9 + i)
      ≤ (3 / 2 * Real.log z) ^ a * pfC1 q * omegaClean q
        * (Real.exp (-(a * ((J - 9 - i : ℕ) : ℝ))) * chaosMult q (J - 9 - i) z) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    refine le_trans (min_le_right _ _) ?_
    have hJk : bottomJ 1 2 z - (9 + i) = J - 9 - i := by rw [← hJdef]; omega
    rw [hJk]
    have hTk := bottomT_mem (z := z) (by linarith) (9 + i)
    have hTpos : 0 < bottomT 1 2 z (9 + i) := lt_of_lt_of_le (by positivity) hTk.1
    have hTsmall : bottomT 1 2 z (9 + i) ≤ 0.0015 := by
      refine le_trans hTk.2.le ?_
      have h1 : Real.exp (1 - ((9 + i : ℕ) : ℝ)) ≤ Real.exp (-8) :=
        Real.exp_le_exp.2 (by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
      have h2 := exp_neg_eight_le
      linarith
    have hu1000 : 1000 ≤ 3 / 2 / bottomT 1 2 z (9 + i) := by
      rw [le_div_iff₀ hTpos]; linarith
    have huz : 3 / 2 / bottomT 1 2 z (9 + i) ≤ Real.log z := by
      rw [hT (9 + i), div_div_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
      have h1 : (1 : ℝ) ≤ (J : ℝ) - ((9 + i : ℕ) : ℝ) := by
        have : ((9 + i + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : 9 + i + 1 ≤ J)
        push_cast at this ⊢
        linarith
      have h2 : Real.exp 1 ≤ Real.exp ((J : ℝ) - ((9 + i : ℕ) : ℝ)) := Real.exp_le_exp.2 h1
      have h3 := Real.exp_one_gt_d9
      have h4 := mul_le_mul_of_nonneg_left
        (show (3 / 2 : ℝ) ≤ Real.exp ((J : ℝ) - ((9 + i : ℕ) : ℝ)) by linarith) hlz0.le
      linarith
    have hw := winSplitFull_le_clean hq0.le hq1 hTpos hu1000 huz
    refine le_trans (mul_le_mul_of_nonneg_right hw (chaosMult_nonneg hq1 _ z)) (le_of_eq ?_)
    rw [hT (9 + i), div_div_eq_mul_div, ← hadef]
    have hm : ((J : ℕ) : ℝ) - ((9 + i : ℕ) : ℝ) = (((J - 9 - i : ℕ) : ℝ)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hm, div_exp_rpow (by positivity)]
    ring
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [← Finset.mul_sum]
  have hre : ∑ i ∈ Finset.range (J - 9),
      Real.exp (-(a * ((J - 9 - i : ℕ) : ℝ))) * chaosMult q (J - 9 - i) z
      = chaosWinSum q (J - 8) z := by
    rw [chaosWinSum, ← hadef, show J - 8 = J - 9 + 1 by omega]
    exact sum_range_sub_eq_sum_Ico (fun m => Real.exp (-(a * (m : ℝ))) * chaosMult q m z) _
  rw [hre]
  ring

/-! ### The levels with the chaos, normalised -/

/-- **A band of the hierarchy with the chaos, normalised.**  For `½ < q ≤ 1`, `η', ε > 0`,
`x ≥ 3` with `Λ ≥ 12` and a band `ℓ < L`:

`pfFull(z_ℓ)·bandLevelCh(z_ℓ, z_{ℓ+1}) ≤ (log x)^a·bandPhi(V_{ℓ+1})
  + K_c^q(1+η')^q pfC1·ω(1.5 log z_{ℓ+1})^a·RMF.chaosWinSum q J_ℓ z_{ℓ+1}`,

`J_ℓ = bandJ 1 z_ℓ z_{ℓ+1}` (`RMF.pfFull_mul_bandLevelW_le_bandPhi`,
`RMF.bandWindows_chaos_clean`). -/
theorem pfFull_mul_bandLevelCh_le {q η' ε x : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 11 ≤ Real.log (Real.log x)) {ℓ : ℕ}
    (hℓ : ℓ < aboveDepth (Real.log (Real.log x))) :
    pfFull q (aboveZ x ℓ) * bandLevelCh q η' ε x (aboveZ x ℓ) (aboveZ x (ℓ + 1))
      ≤ Real.log x ^ (q * (2 * q - 1))
          * bandPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε))
            (aboveV (Real.log (Real.log x)) (ℓ + 1))
        + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q * pfC1 q
          * (omegaClean q * (3 / 2 * Real.log (aboveZ x (ℓ + 1))) ^ (q * (2 * q - 1))
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))) := by
  have hL8 : ∀ k ≤ aboveDepth (Real.log (Real.log x)), 8 ≤ aboveV (Real.log (Real.log x)) k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ hk).1]
  obtain ⟨-, hz, hmono⟩ := aboveZ_facts hx3 hΛ hL8
  obtain ⟨hy2, -, -⟩ := hz ℓ hℓ.le
  obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ hℓ.le
  exact pfFull_mul_bandLevelW_le_bandPhi hq0 hq1 hη' hε hx3 hΛ hℓ
    (winBandCh_nonneg hq1 _ _) (bandWindows_chaos_clean hq0 hq1 hy2 (hmono ℓ hℓ) (by linarith))

/-- **The bottom of the hierarchy with the chaos, normalised.**  For `½ < q ≤ 1`, `η', ε > 0`,
`x ≥ 3` with `Λ ≥ 11.5` and a bound `TS` on the nine top windows at every `z` with
`log z ≥ 2300`:

`bottomLevelCh(z₀) ≤ (log x)^a·botPhi(Λ, TS)
  + K_c^q(1+η')^q pfC1·ω(1.5 log z₀)^a·RMF.chaosWinSum q (J_b - 8) z₀`,

`J_b = bottomJ 1 2 z₀` (`RMF.bottomLevelW_le_botPhi`, `RMF.bottomWindows_chaos_clean`). -/
theorem bottomLevelCh_le {q η' ε x TS : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1) (hη' : 0 < η')
    (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 11.5 ≤ Real.log (Real.log x))
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS) :
    bottomLevelCh q η' ε x (aboveZ x 0)
      ≤ Real.log x ^ (q * (2 * q - 1))
          * botPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) (Real.log (Real.log x)) TS
        + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q
          * (pfC1 q * omegaClean q * (3 / 2 * Real.log (aboveZ x 0)) ^ (q * (2 * q - 1))
            * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) := by
  have hΛ11 : 11 ≤ Real.log (Real.log x) := by linarith
  obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.zero_le _)
  have hL8 : ∀ k ≤ aboveDepth (Real.log (Real.log x)), 8 ≤ aboveV (Real.log (Real.log x)) k :=
    fun k hk => by linarith [(aboveZ_log_facts hx3 hΛ11 hk).1]
  obtain ⟨-, hz, -⟩ := aboveZ_facts hx3 hΛ11 hL8
  obtain ⟨hz2, -, -⟩ := hz 0 (Nat.zero_le _)
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
  obtain ⟨h9, htail⟩ := bottomWindows_chaos_clean hq0 hq1 hz2 (by linarith)
  exact bottomLevelW_le_botPhi hq0 hq1 hη' hε hx3 hΛ (winBotCh_nonneg hq1 _)
    (le_trans h9 (hTS _ hlz2300)) htail

/-- **The hierarchy above `½` with the chaos.**  As
`RMF.rpow_inv_integral_rpow_weightedRademacherSum_le_aboveHierarchy` with the chaos levels, for
`½ ≤ q ≤ 1`, `η', ε > 0`, `x ≥ 3` with `Λ = log log x ≥ 12` and any `L` with `V_ℓ ≥ 8`:

`‖S(x)‖_{2q} ≤ pfFull(q, z_L)^{1/(2q)}((log x/log z_L)e^{18.0056/log z_L})^{1/2}
  + ∑_{ℓ<L}(pfFull(q, z_ℓ)·bandLevelCh(z_ℓ, z_{ℓ+1}))^{1/(2q)} + bottomLevelCh(z_0)^{1/(2q)}`. -/
theorem rpow_inv_integral_rpow_weightedRademacherSum_le_chaosHierarchy {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) {q η' ε x : ℝ} {L : ℕ}
    (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x)
    (hΛ : 12 ≤ Real.log (Real.log x))
    (hL : ∀ ℓ ≤ L, 8 ≤ aboveV (Real.log (Real.log x)) ℓ) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ^ (2 * q)⁻¹
      ≤ pfFull q (aboveZ x L) ^ (2 * q)⁻¹
          * (Real.log x / Real.log (aboveZ x L)
            * Real.exp (18.0056 / Real.log (aboveZ x L))) ^ (2 : ℝ)⁻¹
        + ∑ ℓ ∈ Finset.range L, (pfFull q (aboveZ x ℓ)
            * bandLevelCh q η' ε x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ (2 * q)⁻¹
        + bottomLevelCh q η' ε x (aboveZ x 0) ^ (2 * q)⁻¹ := by
  have hΛ11 : 11 ≤ Real.log (Real.log x) := by linarith
  have hlx : 160000 ≤ Real.log x := by
    have hx0 : 0 < x := by linarith
    have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
    have h12 : (160000 : ℝ) ≤ Real.exp 12 := by
      have h := Real.exp_one_gt_d9
      have e : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have h2 : (2.718 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 12
      linarith [show (160000 : ℝ) ≤ 2.718 ^ 12 by norm_num]
    have := Real.exp_le_exp.2 hΛ
    rw [Real.exp_log hlx0] at this
    linarith
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  obtain ⟨hlx1, hz, hmono⟩ := aboveZ_facts hx3 hΛ11 hL
  have hw0 : 0 ≤ (2 * q)⁻¹ := inv_nonneg.2 (by linarith)
  -- the layered identity, top-down
  have hY : ∀ k, 1 ≤ k → k < L + 1 → aboveZ x (L + 1 - (k + 1)) ≤ aboveZ x (L + 1 - k) := by
    intro k hk1 hkK
    rw [show L + 1 - (k + 1) = L - k by omega, show L + 1 - k = L - k + 1 by omega]
    exact hmono (L - k) (by omega)
  have hN := rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered hX hq0
    (Y := fun k => aboveZ x (L + 1 - k)) (K := L + 1) (by omega) hY x
  beta_reduce at hN
  rw [show L + 1 - 1 = L by omega, show L + 1 - (L + 1) = 0 by omega] at hN
  refine le_trans hN (add_le_add (add_le_add ?_ ?_) ?_)
  · -- the top level
    obtain ⟨hz2, hzx, -⟩ := hz L le_rfl
    exact rpow_inv_mul_rpow_inv_le_top_explicit hX hq0 hq1 hz2 hzx
  · -- the bands
    have hre : ∑ k ∈ Finset.Ico 1 (L + 1),
        (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (aboveZ x (L + 1 - (k + 1)) + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (aboveZ x (L + 1 - (k + 1))) (aboveZ x (L + 1 - k)) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
        = ∑ ℓ ∈ Finset.range L,
          (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            (aboveZ x ℓ + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹
          * (∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
              (aboveZ x ℓ) (aboveZ x (ℓ + 1)) x ω‖ ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range, show L + 1 - 1 = L by omega]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjL := Finset.mem_range.1 hj
      rw [show L + 1 - (1 + (L - 1 - j) + 1) = j by omega,
        show L + 1 - (1 + (L - 1 - j)) = j + 1 by omega]
    rw [hre]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    have hℓL := Finset.mem_range.1 hℓ
    obtain ⟨hy2, -, -⟩ := hz ℓ hℓL.le
    obtain ⟨-, hzx, hz'⟩ := hz (ℓ + 1) hℓL
    have hlev := integral_rpow_norm_blockTruncationTail_le_bandLevelCh hX hq0 hq1 hη' hε hy2
      (hmono ℓ hℓL) hzx hlx hz'
    have hF : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (aboveZ x ℓ + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ) ≤ pfFull q (aboveZ x ℓ) := by
      have h := hRa.integral_norm_randomEulerProduct_shift_rpow_le_above_half (σ := 0) le_rfl
        hq0 hq1 hy2
      have hs : (((1 / 2 + 0 : ℝ)) : ℂ) = 1 / 2 := by norm_num
      rw [hs] at h
      exact h
    have hF0 : 0 ≤ ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        (aboveZ x ℓ + 1) (1 / 2) ω‖ ^ (2 * q) ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
    have hT0 : 0 ≤ ∫ ω, ‖blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω)
        (aboveZ x ℓ) (aboveZ x (ℓ + 1)) x ω‖ ^ (2 * q) ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
    rw [← Real.mul_rpow hF0 hT0]
    exact Real.rpow_le_rpow (mul_nonneg hF0 hT0) (mul_le_mul hF hlev hT0 (le_trans hF0 hF)) hw0
  · -- the bottom level
    obtain ⟨hz2, hzx, hz'⟩ := hz 0 (Nat.zero_le L)
    have hbot := integral_rpow_norm_truncationTail_le_bottomLevelCh hX hq0 hq1 hη' hε hz2 hzx hlx
      hz'
    exact Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hbot hw0

/-! ### The levels with the chaos, assembled -/

set_option maxHeartbeats 1000000 in
-- the hierarchy and the normalised levels in one proof, as the Jensen tower
/-- **The hierarchy with the chaos, normalised.**  For `½ < q ≤ 1`, `η', ε > 0`, `x ≥ 3` with
`Λ = log log x ≥ 12` and a bound `TS` on the bottom's nine top windows at every `z` with
`log z ≥ 2300`, with `K_c = 2.0913(1+ε)`, `E_c = 0.0012(1+1/ε)`,
`C₁ = K_c^q(1+η')^q pfC1·ω` and `u'_ℓ = (1.5 log z_ℓ/log x)^a`:

`E|S(x)|^{2q} ≤ (log x)^a·(topPhi + ∑_{ℓ<L}(bandPhi(V_{ℓ+1}) + C₁u'_{ℓ+1}·chaosWinSum_ℓ)^{1/(2q)}
  + (botPhi(Λ, TS) + C₁u'_0·chaosWinSum_b)^{1/(2q)})^{2q}`,

`chaosWinSum_ℓ = RMF.chaosWinSum q (bandJ 1 z_ℓ z_{ℓ+1}) z_{ℓ+1}`,
`chaosWinSum_b = RMF.chaosWinSum q (bottomJ 1 2 z_0 - 8) z_0`. -/
theorem integral_rpow_weightedRademacherSum_le_chaosLevels {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {q η' ε x TS : ℝ} (hq0 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hη' : 0 < η') (hε : 0 < ε) (hx3 : 3 ≤ x) (hΛ : 12 ≤ Real.log (Real.log x))
    (hTS : ∀ z : ℕ, 2300 ≤ Real.log z → botTopSum q z ≤ TS) :
    (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
      ≤ Real.log x ^ (q * (2 * q - 1))
        * (topPhi q
          + ∑ ℓ ∈ Finset.range (aboveDepth (Real.log (Real.log x))),
            (bandPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε))
                (aboveV (Real.log (Real.log x)) (ℓ + 1))
              + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q * pfC1 q * omegaClean q
                * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ (q * (2 * q - 1))
                * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))
              ^ (2 * q)⁻¹
          + (botPhi q η' (2.0913 * (1 + ε)) (0.0012 * (1 + 1 / ε)) (Real.log (Real.log x)) TS
              + (2.0913 * (1 + ε)) ^ q * (1 + η') ^ q * pfC1 q * omegaClean q
                * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ (q * (2 * q - 1))
                * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) ^ (2 * q)⁻¹)
          ^ (2 * q) := by
  haveI := hX.isProbabilityMeasure
  set Λ := Real.log (Real.log x) with hΛdef
  set L := aboveDepth Λ with hLdef
  set a := q * (2 * q - 1) with hadef
  set P := (2 * q)⁻¹ with hPdef
  set Kc := 2.0913 * (1 + ε) with hKcdef
  set Ec := 0.0012 * (1 + 1 / ε) with hEcdef
  set C₁ := Kc ^ q * (1 + η') ^ q * pfC1 q * omegaClean q with hC₁def
  have hq0' : (0 : ℝ) < q := by linarith
  have ha0 : 0 < a := mul_pos hq0' (by linarith)
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have hP1 : P ≤ 1 := by rw [hPdef, inv_le_one₀ (by positivity)]; linarith
  have hKc0 : 0 ≤ Kc := by positivity
  have hEc0 : 0 ≤ Ec := by positivity
  have hC₁0 : 0 ≤ C₁ := by
    have := omegaClean_nonneg hq1
    have : 0 ≤ pfC1 q := (Real.exp_pos _).le
    have : 0 ≤ Kc ^ q := Real.rpow_nonneg hKc0 _
    have : 0 ≤ (1 + η') ^ q := Real.rpow_nonneg (by linarith) _
    positivity
  have hΛ11 : 11 ≤ Λ := by linarith
  have hΛ115 : 11.5 ≤ Λ := by linarith
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hL8 : ∀ ℓ ≤ L, 8 ≤ aboveV Λ ℓ :=
    fun ℓ hℓ => by linarith [(aboveZ_log_facts hx3 hΛ11 hℓ).1]
  obtain ⟨hlx1, hz, hmono⟩ := aboveZ_facts hx3 hΛ11 hL8
  have hlxP : 0 ≤ (Real.log x ^ a) ^ P := Real.rpow_nonneg (Real.rpow_nonneg hlx0.le _) _
  have hlxa0 : 0 < Real.log x ^ a := Real.rpow_pos_of_pos hlx0 _
  -- a window term, rewritten per unit `(log x)^a`
  have hwin_eq : ∀ z : ℕ, ∀ S : ℝ, 0 < Real.log z →
      Kc ^ q * (1 + η') ^ q * pfC1 q * (omegaClean q * (3 / 2 * Real.log z) ^ a * S)
        = Real.log x ^ a * (C₁ * (3 / 2 * Real.log z / Real.log x) ^ a * S) := by
    intro z S hlz
    rw [hC₁def, Real.div_rpow (by positivity) hlx0.le]
    field_simp
  -- the hierarchy
  have hier := rpow_inv_integral_rpow_weightedRademacherSum_le_chaosHierarchy hX (L := L)
    hq0.le hq1 hη' hε hx3 hΛ hL8
  rw [← hPdef] at hier
  -- the top
  have htop := top_le_topPhi hq0.le hq1 hx3 hΛ11
  rw [← hLdef, ← hadef, ← hPdef] at htop
  -- the bands
  have hband : ∀ ℓ < L, (pfFull q (aboveZ x ℓ)
      * bandLevelCh q η' ε x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ P
      ≤ (Real.log x ^ a) ^ P * (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
        + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
          * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))) ^ P := by
    intro ℓ hℓ
    have h := pfFull_mul_bandLevelCh_le hq0 hq1 hη' hε hx3 hΛ11 hℓ
    rw [← hadef, ← hKcdef, ← hEcdef] at h
    obtain ⟨hy2, -, -⟩ := hz ℓ hℓ.le
    obtain ⟨-, hzx, hz'⟩ := hz (ℓ + 1) hℓ
    have hlz : 0 < Real.log (aboveZ x (ℓ + 1)) := by
      obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.succ_le_of_lt hℓ)
      linarith
    rw [hwin_eq _ _ hlz, ← mul_add] at h
    have hlx160 : 160000 ≤ Real.log x := by
      have h12 : (160000 : ℝ) ≤ Real.exp 12 := by
        have h := Real.exp_one_gt_d9
        have e : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        have h2 : (2.718 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 12
        linarith [show (160000 : ℝ) ≤ 2.718 ^ 12 by norm_num]
      have := Real.exp_le_exp.2 hΛ
      rw [hΛdef, Real.exp_log hlx0] at this
      linarith
    have hlev := integral_rpow_norm_blockTruncationTail_le_bandLevelCh hX hq0.le hq1 hη' hε hy2
      (hmono ℓ hℓ) hzx hlx160 hz'
    have hlev0 : 0 ≤ bandLevelCh q η' ε x (aboveZ x ℓ) (aboveZ x (ℓ + 1)) :=
      le_trans (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hlev
    have hpf0 : 0 ≤ pfFull q (aboveZ x ℓ) := by rw [pfFull]; positivity
    have hb0 : 0 ≤ bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1)) :=
      (bandPhi_antitoneOn hq0 hq1 hη' hKc0 hEc0).2 _ (aboveZ_log_facts hx3 hΛ11
        (Nat.succ_le_of_lt hℓ)).1
    have hw0 : 0 ≤ C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
        * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)) :=
      mul_nonneg (mul_nonneg hC₁0 (Real.rpow_nonneg (by positivity) _))
        (chaosWinSum_nonneg hq1 _ _)
    calc (pfFull q (aboveZ x ℓ) * bandLevelCh q η' ε x (aboveZ x ℓ) (aboveZ x (ℓ + 1))) ^ P
        ≤ (Real.log x ^ a * (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1)))) ^ P :=
          Real.rpow_le_rpow (mul_nonneg hpf0 hlev0) h hP0.le
      _ = _ := Real.mul_rpow (Real.rpow_nonneg hlx0.le _) (add_nonneg hb0 hw0)
  -- the bottom
  have hbot := bottomLevelCh_le hq0 hq1 hη' hε hx3 hΛ115 hTS
  rw [← hadef, ← hKcdef, ← hEcdef] at hbot
  have hlz00 : 0 < Real.log (aboveZ x 0) := by
    obtain ⟨-, -, hl1, -, hl5, -⟩ := aboveZ_log_facts hx3 hΛ11 (Nat.zero_le L)
    linarith
  have e0 : Kc ^ q * (1 + η') ^ q * (pfC1 q * omegaClean q
      * (3 / 2 * Real.log (aboveZ x 0)) ^ a * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8)
        (aboveZ x 0))
      = Real.log x ^ a * (C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
        * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) := by
    rw [← hwin_eq _ _ hlz00]; ring
  rw [e0, ← mul_add] at hbot
  have hbotP : bottomLevelCh q η' ε x (aboveZ x 0) ^ P
      ≤ (Real.log x ^ a) ^ P * (botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) ^ P := by
    obtain ⟨hz2, hzx, hz'⟩ := hz 0 (Nat.zero_le L)
    have hlx160 : 160000 ≤ Real.log x := by
      have h12 : (160000 : ℝ) ≤ Real.exp 12 := by
        have h := Real.exp_one_gt_d9
        have e : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e]
        have h2 : (2.718 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 12
        linarith [show (160000 : ℝ) ≤ 2.718 ^ 12 by norm_num]
      have := Real.exp_le_exp.2 hΛ
      rw [hΛdef, Real.exp_log hlx0] at this
      linarith
    have hlev := integral_rpow_norm_truncationTail_le_bottomLevelCh hX hq0.le hq1 hη' hε hz2 hzx
      hlx160 hz'
    have hlev0 : 0 ≤ bottomLevelCh q η' ε x (aboveZ x 0) :=
      le_trans (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hlev
    have hsum0 : 0 ≤ botPhi q η' Kc Ec Λ TS
        + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
          * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0) := by
      have := mul_le_mul_of_nonneg_left (le_refl 0) hlxa0.le
      nlinarith [hlev0, hbot]
    calc bottomLevelCh q η' ε x (aboveZ x 0) ^ P
        ≤ (Real.log x ^ a * (botPhi q η' Kc Ec Λ TS
          + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
            * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0))) ^ P :=
          Real.rpow_le_rpow hlev0 hbot hP0.le
      _ = _ := Real.mul_rpow (Real.rpow_nonneg hlx0.le _) hsum0
  -- assemble
  have hsum := Finset.sum_le_sum fun ℓ hℓ => hband ℓ (Finset.mem_range.1 hℓ)
  rw [← Finset.mul_sum] at hsum
  have hN : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ) ^ P ≤ (Real.log x ^ a) ^ P * (topPhi q
        + ∑ ℓ ∈ Finset.range L, (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))) ^ P
        + (botPhi q η' Kc Ec Λ TS
          + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
            * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) ^ P) := by
    refine le_trans hier ?_
    rw [mul_add, mul_add]
    linarith
  have hI0 : 0 ≤ ∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
      ^ (2 * q) ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hF0 : 0 ≤ (Real.log x ^ a) ^ P * (topPhi q
        + ∑ ℓ ∈ Finset.range L, (bandPhi q η' Kc Ec (aboveV Λ (ℓ + 1))
          + C₁ * (3 / 2 * Real.log (aboveZ x (ℓ + 1)) / Real.log x) ^ a
            * chaosWinSum q (bandJ 1 (aboveZ x ℓ) (aboveZ x (ℓ + 1))) (aboveZ x (ℓ + 1))) ^ P
        + (botPhi q η' Kc Ec Λ TS
          + C₁ * (3 / 2 * Real.log (aboveZ x 0) / Real.log x) ^ a
            * chaosWinSum q (bottomJ 1 2 (aboveZ x 0) - 8) (aboveZ x 0)) ^ P) :=
    le_trans (Real.rpow_nonneg hI0 _) hN
  have h2q : P * (2 * q) = 1 := by rw [hPdef]; field_simp
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hN (by positivity : (0 : ℝ) ≤ 2 * q)
  rw [← Real.rpow_mul hI0, h2q, Real.rpow_one] at hpow
  refine le_trans hpow (le_of_eq ?_)
  rw [Real.mul_rpow hlxP (by
    have := hF0
    rcases (mul_nonneg_iff.1 this) with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · have : (Real.log x ^ a) ^ P = 0 := le_antisymm h1 hlxP
      rw [this, zero_mul] at hF0
      nlinarith [Real.rpow_pos_of_pos hlxa0 P])]
  rw [← Real.rpow_mul (Real.rpow_nonneg hlx0.le _), h2q, Real.rpow_one]

end RMF
