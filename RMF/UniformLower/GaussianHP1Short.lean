/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.HP1Certificate

/-!
# The window's first moment on short tubes, Gaussian side

`RMF.le_measure_windowEvent_gaussian_v2` needs `(a + A + 2B)² ≤ 2(n₀ - 2)v₋`, false below
`n₀ ≈ 116` at HP1's parameters, because it linearises the ballot (`RMF.ballotLinear`, slope
`1 - C²/(2(n₀ - 2)v₋)`).  Here the ballot `RMF.ballotLower` is kept per start row: from a start `u`
the height suffix has probability at least
`RMF.ballotLower v₋ v₊ (n - 2) (a - u) - K_rP_R(a - u) - αe^{-u} - γ`, and for `n ≥ n₀` the ballot
is at least `2(a - u)e^{-(a-u)²/(2(n₀-2)v₋)}/(√(2πv₊)√n)` (`RMF.ballotLower_ge_short`).

* **Twins without the linearisation**:
  `RMF.IsGaussianWalk.le_measure_barrierEvent_flat_depth_lower`,
  `RMF.IsGaussianWalk.le_measure_tube_inter_slope_lower`, `RMF.ofReal_suffixLow_short`,
  `RMF.ofReal_le_measure_hp1SuffixV2_short`.
* **The start with a general weight** `0 ≤ w ≤ min((a - u)⁺, C)` (`RMF.le_integral_startGoodW`, the
  main term `RMF.startMainW`), at `w = sw·e^{-sw²/(2(n₀-2)v₋)}` (`RMF.startWeightShort`,
  `RMF.startMainShort`, `RMF.hp1StartShort`).
* **The window lemma** `RMF.le_measure_windowEvent_gaussian_short`: v2's hypotheses without `hCn`,
  the bound `RMF.hp1LowerBoundShort … / √n` for every `n ≥ n₀`; the slope loss `K_rP_R(a - U₂)` is
  paid by `E[min((a - U₂)⁺, C)] ≤ a + √(V/(2π))` (`RMF.integral_startWeight_start_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace RMF

/-! ### The tube, the ballot kept -/

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **A flat ceiling and a floor at depth `D`, from below, the ballot kept**:
`RMF.IsGaussianWalk.le_measure_barrierEvent_flat_depth` with `RMF.ballotLower` in place of
`RMF.ballotLinear`. -/
theorem IsGaussianWalk.le_measure_barrierEvent_flat_depth_lower (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n : ℕ} (hn : 1 ≤ n) (z : ℝ)
    {lo : ℕ → ℝ} {D B : ℝ} (hD : 0 ≤ D) (hB : 2 * vmax < B)
    (hlo : ∀ i : ℕ, 1 ≤ i → lo i ≤ -D - B * (i : ℝ)) :
    ballotLower vmin vmax n z - floorLossDepth D B vmin vmax n z
      ≤ (μ (barrierEvent G n lo (fun _ => z))).toReal := by
  set A : Set Ω := {ω | ∀ j ≤ n, walk G j ω ≤ z} with hAdef
  have hdec := measure_le_barrierEvent_add_breaches (μ := μ) G n lo (fun _ => z) A
  have hceil : μ (A ∩ ceilBreach G n (fun _ => z)) = 0 := by
    have hempty : A ∩ ceilBreach G n (fun _ => z) = ∅ := by
      ext ω
      simp only [hAdef, ceilBreach, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and, not_exists]
      intro hA j hj1 hjn hlt
      exact absurd (hA j hjn) (not_le.2 hlt)
    rw [hempty, measure_empty]
  have hfloor : μ (A ∩ floorBreach G n lo)
      ≤ ENNReal.ofReal (floorLossDepth D B vmin vmax n z) :=
    h.measure_inter_floorBreach_le_depth hv hn z hD hB hlo
  have hA : ballotLower vmin vmax n z ≤ (μ A).toReal := by
    have h1 := h.explicit_le_barrierProb_posPart hv z hn
    rw [barrierProb] at h1
    exact h1
  have hfin1 : μ (barrierEvent G n lo fun _ => z) ≠ ⊤ := measure_ne_top _ _
  have hL0 := floorLossDepth_nonneg (D := D) (vmin := vmin) hB n z
  have hle : (μ A).toReal ≤ (μ (barrierEvent G n lo fun _ => z)).toReal
      + floorLossDepth D B vmin vmax n z := by
    have h2 : μ A ≤ μ (barrierEvent G n lo fun _ => z)
        + ENNReal.ofReal (floorLossDepth D B vmin vmax n z) := by
      calc μ A ≤ μ (barrierEvent G n lo fun _ => z) + μ (A ∩ ceilBreach G n fun _ => z)
            + μ (A ∩ floorBreach G n lo) := hdec
        _ ≤ μ (barrierEvent G n lo fun _ => z) + 0
            + ENNReal.ofReal (floorLossDepth D B vmin vmax n z) := by
            rw [hceil]
            gcongr
        _ = _ := by rw [add_zero]
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, ENNReal.ofReal_ne_top⟩) h2
    rwa [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hL0] at h3
  linarith

/-- **The tube with the slope walk paid, from below, the ballot kept**:
`RMF.IsGaussianWalk.le_measure_tube_inter_slope` with `RMF.ballotLower` in place of
`RMF.ballotLinear` (`RMF.IsGaussianWalk.le_measure_barrierEvent_flat_depth_lower`). -/
theorem IsGaussianWalk.le_measure_tube_inter_slope_lower (h : IsGaussianWalk G v μ)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax) {n m₀ : ℕ} (hm₀ : m₀ < n) (r : ℕ → ℝ)
    {lo Menv : ℕ → ℝ} {z D B L K σ2 x₀ : ℝ} (hz : 0 ≤ z) (hD : 0 ≤ D) (hB : 2 * vmax < B)
    (hlo : ∀ i : ℕ, 1 ≤ i → lo i ≤ -D - B * i) (hMenv0 : ∀ i, 0 ≤ Menv i)
    (hMenv : ∀ i, 1 ≤ i → i ≤ n → -Menv i ≤ x₀ + lo i ∧ x₀ + z ≤ Menv i)
    (hx₀ : |x₀| ≤ Menv 0)
    (hK : ∑ m ∈ Finset.Ico m₀ n, |r m| * (Menv m + Menv (m + 1)) ≤ K) (hKL : K ≤ L)
    (hσ : ∑ m ∈ Finset.range m₀, r m ^ 2 * (v m : ℝ) ≤ σ2) (hσ0 : 0 < σ2) :
    ballotLower vmin vmax n z - floorLossDepth D B vmin vmax n z
      - √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin)))
        * ((z + √(π * vmax / 2)) * Real.exp (-((L - K) ^ 2 / (2 * σ2)))
          + √(Real.exp (-((L - K) ^ 2 / (2 * σ2))) * ((m₀ : ℝ) * vmax)))
      ≤ (μ (barrierEvent G n lo (fun _ => z)
          ∩ {ω | ∀ i ≤ n, walk (fun m ω => r m * G m ω) i ω ≤ L})).toReal := by
  set T := barrierEvent G n lo (fun _ => z) with hT
  set R := {ω | ∀ i ≤ n, walk (fun m ω => r m * G m ω) i ω ≤ L} with hR
  set Bad : Set Ω := {ω | ∃ i ≤ m₀, L - K < walk (fun m ω => r m * G m ω) i ω} with hBad
  set Surv : Set Ω := {ω | ∀ j, m₀ ≤ j → j ≤ n → walk G j ω ≤ z} with hSurv
  set PR := Real.exp (-((L - K) ^ 2 / (2 * σ2))) with hPR
  set Kr := √(2 / (π * (((n - m₀ : ℕ) : ℝ) * vmin))) with hKr
  set c := √(π * vmax / 2) with hc
  have hrG := h.const_mul r
  have hn : 1 ≤ n := by omega
  have hK0 : 0 ≤ K := le_trans (Finset.sum_nonneg fun m _ =>
    mul_nonneg (abs_nonneg _) (add_nonneg (hMenv0 _) (hMenv0 _))) hK
  have hRm : MeasurableSet R := by
    have hrw : R = ⋂ i ∈ Set.Iic n, {ω | walk (fun m ω => r m * G m ω) i ω ≤ L} := by
      ext ω
      simp [hR]
    rw [hrw]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
      measurableSet_le (hrG.measurable_walk i) measurable_const
  -- the ballot, less the floor
  have hball := h.le_measure_barrierEvent_flat_depth_lower hv hn z hD hB hlo
  -- the envelope on the tube
  have henv : ∀ ω ∈ T, ∀ i ≤ n, |x₀ + walk G i ω| ≤ Menv i := by
    intro ω hω i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simpa [walk_zero] using hx₀
    · have hb := hω i hi1 hi
      rw [Set.mem_Icc] at hb
      obtain ⟨h1, h2⟩ := hMenv i hi1 hi
      rw [abs_le]
      constructor <;> linarith [hb.1, hb.2]
  have hinc : ∀ ω ∈ T, ∀ m, m < n → |G m ω| ≤ Menv m + Menv (m + 1) := by
    intro ω hω m hm
    have e : G m ω = (x₀ + walk G (m + 1) ω) - (x₀ + walk G m ω) := by
      rw [walk_succ, Pi.add_apply]
      ring
    rw [e]
    calc _ ≤ |x₀ + walk G (m + 1) ω| + |x₀ + walk G m ω| := abs_sub _ _
      _ ≤ Menv (m + 1) + Menv m := add_le_add (henv ω hω (m + 1) hm) (henv ω hω m hm.le)
      _ = _ := by ring
  -- past `m₀` the slope walk moves by at most `K` on the tube
  have hlate : ∀ ω ∈ T, ∀ i, m₀ ≤ i → i ≤ n →
      walk (fun m ω => r m * G m ω) i ω ≤ walk (fun m ω => r m * G m ω) m₀ ω + K := by
    intro ω hω i hi1 hin
    have hsub : walk (fun m ω => r m * G m ω) i ω - walk (fun m ω => r m * G m ω) m₀ ω
        = ∑ m ∈ Finset.Ico m₀ i, r m * G m ω := by
      have := congrFun (walk_sub_eq (fun m ω => r m * G m ω) hi1) ω
      simpa [Finset.sum_apply] using this
    have hbound : ∑ m ∈ Finset.Ico m₀ i, r m * G m ω ≤ K := by
      calc ∑ m ∈ Finset.Ico m₀ i, r m * G m ω
          ≤ ∑ m ∈ Finset.Ico m₀ i, |r m| * (Menv m + Menv (m + 1)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hm' := Finset.mem_Ico.1 hm
            calc r m * G m ω ≤ |r m * G m ω| := le_abs_self _
              _ = |r m| * |G m ω| := abs_mul _ _
              _ ≤ |r m| * (Menv m + Menv (m + 1)) :=
                  mul_le_mul_of_nonneg_left (hinc ω hω m (by omega)) (abs_nonneg _)
        _ ≤ ∑ m ∈ Finset.Ico m₀ n, |r m| * (Menv m + Menv (m + 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hin)
              fun m _ _ => mul_nonneg (abs_nonneg _) (add_nonneg (hMenv0 _) (hMenv0 _))
        _ ≤ K := hK
    linarith
  -- a slope failure on the tube is a prefix event followed by survival
  have hsub : T \ R ⊆ Bad ∩ Surv := by
    rintro ω ⟨hωT, hωR⟩
    refine ⟨?_, ?_⟩
    · simp only [hR, Set.mem_setOf_eq, not_forall, not_le] at hωR
      obtain ⟨i, hi, hiL⟩ := hωR
      rcases le_or_gt i m₀ with him | him
      · exact ⟨i, him, by linarith⟩
      · exact ⟨m₀, le_rfl, by linarith [hlate ω hωT i him.le hi]⟩
    · intro j hj1 hjn
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa [walk_zero] using hz
      · exact (hωT j hj hjn).2
  -- the prefix event has probability at most `P_R`
  have hBadR : μ.real Bad ≤ PR := by
    have hBadeq : Bad = (survivalSet (fun m ω => r m * G m ω)
        (fun j => (L - K) - driftSum (fun _ => 0) j) m₀)ᶜ := by
      ext ω
      simp only [hBad, survivalSet, driftSum, Finset.sum_const_zero, sub_zero,
        Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, exists_prop]
    have ht0 : 0 ≤ (L - K) / σ2 := div_nonneg (by linarith) hσ0.le
    have hexp := hrG.measureReal_survivalSet_compl_le_exp_sum (d := fun _ => 0) ht0
      (by linarith : 0 ≤ L - K) m₀
    rw [← hBadeq] at hexp
    have hsum : ∑ m ∈ Finset.range m₀, max 0 ((L - K) / σ2 * 0
        + ((L - K) / σ2) ^ 2 * ((⟨r m ^ 2, sq_nonneg _⟩ * v m : ℝ≥0) : ℝ) / 2)
        ≤ ((L - K) / σ2) ^ 2 * σ2 / 2 := by
      have hterm : ∀ m ∈ Finset.range m₀, max 0 ((L - K) / σ2 * 0
          + ((L - K) / σ2) ^ 2 * ((⟨r m ^ 2, sq_nonneg _⟩ * v m : ℝ≥0) : ℝ) / 2)
          = ((L - K) / σ2) ^ 2 / 2 * (r m ^ 2 * (v m : ℝ)) := by
        intro m _
        have hco : ((⟨r m ^ 2, sq_nonneg _⟩ * v m : ℝ≥0) : ℝ) = r m ^ 2 * (v m : ℝ) := by
          rw [NNReal.coe_mul]
          rfl
        rw [hco, max_eq_right (by positivity)]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      calc ((L - K) / σ2) ^ 2 / 2 * ∑ m ∈ Finset.range m₀, r m ^ 2 * (v m : ℝ)
          ≤ ((L - K) / σ2) ^ 2 / 2 * σ2 := mul_le_mul_of_nonneg_left hσ (by positivity)
        _ = ((L - K) / σ2) ^ 2 * σ2 / 2 := by ring
    refine le_trans hexp (Real.exp_le_exp.2 ?_)
    have hid : -((L - K) / σ2 * (L - K)) + ((L - K) / σ2) ^ 2 * σ2 / 2
        = -((L - K) ^ 2 / (2 * σ2)) := by
      field_simp
      ring
    linarith
  -- combine
  have hA := h.measureReal_prefix_inter_survive_le hv hm₀ r (L - K) hz
  have hmono : Kr * ((z + c) * μ.real Bad + √(μ.real Bad * ((m₀ : ℝ) * vmax)))
      ≤ Kr * ((z + c) * PR + √(PR * ((m₀ : ℝ) * vmax))) := by
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hvmax : 0 ≤ vmax := le_trans hv.pos.le (le_trans (hv.lo 0) (hv.hi 0))
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Real.sqrt_nonneg _)
    · exact mul_le_mul_of_nonneg_left hBadR (by linarith)
    · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hBadR (by positivity))
  have hdiff : μ.real (T \ R) ≤ Kr * ((z + c) * PR + √(PR * ((m₀ : ℝ) * vmax))) :=
    le_trans (measureReal_mono hsub) (le_trans hA hmono)
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := T) hRm
  have hTreal : (μ T).toReal = μ.real T := rfl
  change _ ≤ μ.real (T ∩ R)
  linarith

end Walk

/-! ### The ballot per start row -/

/-- `RMF.ballotLower` is continuous in the barrier level. -/
lemma continuous_ballotLower (vmin vmax : ℝ) (n : ℕ) :
    Continuous fun c => ballotLower vmin vmax n c := by
  unfold ballotLower
  fun_prop

/-- **The ballot at horizon `n - 2`, per start row**: for `c ≥ 0` and `3 ≤ n₀ ≤ n`,
`RMF.ballotLower v₋ v₊ (n - 2) c ≥ 2/(√(2πv₊)√n)·c·e^{-c²/(2(n₀-2)v₋)}`: the exponent is smaller at
the horizon `n₀ - 2`, and `√(2π(n-2)v₊) ≤ √(2πv₊)√n`. -/
lemma ballotLower_ge_short {n₀ n : ℕ} (hn₀ : 3 ≤ n₀) (hn : n₀ ≤ n) {vmin vmax c : ℝ}
    (hvmin : 0 < vmin) (hvmax : 0 < vmax) (hc : 0 ≤ c) :
    2 / √(2 * π * vmax) / √(n : ℝ) * (c * Real.exp (-(c ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)))))
      ≤ ballotLower vmin vmax (n - 2) c := by
  have hN : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hn₀' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < ((n₀ : ℝ) - 2) * vmin := mul_pos (by linarith) hvmin
  have hN1 : ((n₀ : ℝ) - 2) * vmin ≤ ((n - 2 : ℕ) : ℝ) * vmin := by
    rw [hN]
    exact mul_le_mul_of_nonneg_right (by linarith) hvmin.le
  have hexp : Real.exp (-(c ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))))
      ≤ Real.exp (-c ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin))) := by
    rw [neg_div]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    exact div_le_div_of_nonneg_left (sq_nonneg c) (by positivity) (by linarith)
  have hsq : √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) ≤ √(2 * π * vmax) * √(n : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [hN]
    nlinarith [Real.pi_pos]
  have hpos : 0 < √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) := by
    refine Real.sqrt_pos.2 ?_
    rw [hN]
    have : (1 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    positivity
  have hE0 : 0 ≤ Real.exp (-(c ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)))) := (Real.exp_pos _).le
  unfold ballotLower
  rw [max_eq_left hc]
  calc 2 / √(2 * π * vmax) / √(n : ℝ) * (c * Real.exp (-(c ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin)))))
      = 2 * c * Real.exp (-(c ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))))
          / (√(2 * π * vmax) * √(n : ℝ)) := by ring
    _ ≤ 2 * c * Real.exp (-(c ^ 2 / (2 * (((n₀ : ℝ) - 2) * vmin))))
          / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hsq
    _ ≤ 2 * c * Real.exp (-c ^ 2 / (2 * (((n - 2 : ℕ) : ℝ) * vmin)))
          / √(2 * π * (((n - 2 : ℕ) : ℝ) * vmax)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) hpos.le

/-! ### The suffixes from a start, the ballot kept -/

section Suffix

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
  {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **The height suffix from a start `u` of the box, the ballot kept.**  `RMF.ofReal_suffixLow_le`
without `(a + A + 2B)² ≤ 2(n - 2)v₋`: `RMF.IsGaussianWalk.le_measure_tube_inter_slope_lower` for the
walk from block `2`, the floor loss by `αe^{-u}` (`RMF.floorLossDepth_start_le`), and the slope loss
`K_r((a - u + c)P_R + √(P_R m₀v₊)) = K_rP_R(a - u) + γ`. -/
theorem ofReal_suffixLow_short (hZ : IsGaussianWalk Z v Q₁) (β : ℕ → ℝ) {n m₀ : ℕ}
    (hm₀ : m₀ + 3 ≤ n) {vmin vmax a A B L Klate σR2 u : ℝ} (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → vmin ≤ (v m : ℝ) ∧ (v m : ℝ) ≤ vmax) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hB : 2 * vmax < B)
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1)))
      ≤ Klate) (hKL : Klate ≤ L)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2), β m ^ 2 * (v m : ℝ) ≤ σR2) (hσR0 : 0 < σR2)
    (hu : u ∈ Set.Icc (-A - 2 * B) a) :
    ENNReal.ofReal (ballotLower vmin vmax (n - 2) (a - u)
        - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
          * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * (a - u)
        - Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (-u)
        - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
          * (√(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
            + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax))))
      ≤ Q₁ (barrierEvent (fun m => Z (m + 2)) (n - 2) (fun i => -A - B * ((i : ℝ) + 2) - u)
          (fun _ => a - u)
        ∩ {ω₁ | ∀ i ≤ n - 2, walk (fun m ω => β (m + 2) * Z (m + 2) ω) i ω₁ ≤ L}) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hvb 2 le_rfl).1 (hvb 2 le_rfl).2)
  have hB0 : 0 ≤ B := by linarith
  have hv : VarBracket (fun m => v (m + 2)) vmin vmax :=
    ⟨hvmin, fun i => (hvb (i + 2) (by omega)).1, fun i => (hvb (i + 2) (by omega)).2⟩
  have hMenv0 : ∀ i : ℕ, 0 ≤ a + A + B * ((i : ℝ) + 2) := fun i => by
    have : 0 ≤ B * ((i : ℝ) + 2) := mul_nonneg hB0 (by positivity)
    linarith
  have hKsum : ∑ m ∈ Finset.Ico m₀ (n - 2), |β (m + 2)|
      * ((a + A + B * ((m : ℝ) + 2)) + (a + A + B * (((m + 1 : ℕ) : ℝ) + 2))) ≤ Klate := by
    refine le_trans (le_of_eq ?_) hKlate
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show n - 2 - m₀ = n - (m₀ + 2) by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show m₀ + 2 + k = m₀ + k + 2 by omega]
    push_cast
    ring
  have hσsum : ∑ m ∈ Finset.range m₀, β (m + 2) ^ 2 * (v (m + 2) : ℝ) ≤ σR2 := by
    refine le_trans (le_of_eq ?_) hσR
    rw [Finset.sum_Ico_eq_sum_range, show m₀ + 2 - 2 = m₀ by omega]
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm k 2]
  have htube := (hZ.shift 2).le_measure_tube_inter_slope_lower hv (n := n - 2) (m₀ := m₀)
    (by omega) (fun m => β (m + 2)) (lo := fun i => -A - B * ((i : ℝ) + 2) - u)
    (Menv := fun i => a + A + B * ((i : ℝ) + 2)) (z := a - u) (D := A + 2 * B + u) (B := B)
    (L := L) (K := Klate) (σ2 := σR2) (x₀ := u) (by linarith) (by linarith) hB
    (fun i _ => by linarith) hMenv0
    (fun i _ _ => ⟨by linarith, by nlinarith [mul_nonneg hB0 (Nat.cast_nonneg (α := ℝ) i)]⟩)
    (by
      rw [abs_le]
      constructor <;> nlinarith)
    hKsum hKL hσsum hσR0
  refine (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (le_trans ?_ htube)
  have hfloor := floorLossDepth_start_le (vmin := vmin) (N := n - 2) hB hu1 hu2
  have hslope : √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
        * ((a - u + √(π * vmax / 2)) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
          + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax)))
      = √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
          * (a - u)
        + √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
          * (√(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
            + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax))) := by
    ring
  linarith

/-- **The suffix of HP1 v2 from a start `(u, y)`, from below, the ballot kept.**
`RMF.ofReal_le_measure_hp1SuffixV2` without `(a + A + 2B)² ≤ 2(n - 2)v₋`: the height suffix of
`RMF.ofReal_suffixLow_short` in place of `RMF.ofReal_suffixLow_le`, so
`((RMF.ballotLower v₋ v₊ (n - 2) (a - u) - K_rP_R(a - u)) - γ)·RMF.hp1ExitV2(y) - αe^{-u}` bounds
the probability of `RMF.hp1SuffixV2`; Harris, the exit factor and the floor paid once are v2's. -/
theorem ofReal_le_measure_hp1SuffixV2_short (hZ : IsGaussianWalk Z v Q₁)
    (hW : IsGaussianWalk W s Q₂) (β d : ℕ → ℝ) {n m₀ : ℕ} (hm₀ : m₀ + 3 ≤ n)
    {vmin vmax a A B L Klate σR2 t ρ Λ AW BW u y : ℝ} (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → vmin ≤ (v m : ℝ) ∧ (v m : ℝ) ≤ vmax) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hB : 2 * vmax < B)
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) n,
      |min (β m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate) (hKL : Klate ≤ L)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2), min (β m) 0 ^ 2 * (v m : ℝ) ≤ σR2) (hσR0 : 0 < σR2)
    (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hΛ : ∑ m ∈ Finset.Ico 2 n,
      max 0 (t * d m + t ^ 2 * (max (β m) 0 ^ 2 * (v m : ℝ) + s m) / 2) ≤ Λ)
    (hBW : ∀ m, 2 ≤ m → m < n → (s m : ℝ) / 2 - d m ≤ BW)
    (hu : u ∈ Set.Icc (-A - 2 * B) a) :
    ENNReal.ofReal ((ballotLower vmin vmax (n - 2) (a - u)
            - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
              * Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * (a - u)
          - √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin)))
            * (√(π * vmax / 2) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
              + √(Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) * ((m₀ : ℝ) * vmax))))
          * hp1ExitV2 t L ρ Λ AW y
        - Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (-u))
      ≤ (Q₁.prod Q₂) (hp1SuffixV2 Z W β d n a A B L ρ AW BW u y) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hvb 2 le_rfl).1 (hvb 2 le_rfl).2)
  have hB0 : 0 ≤ B := by linarith
  -- the constants
  set Kr := √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))) with hKr
  set PR := Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) with hPR
  set α := Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
    * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
    / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) with hα
  set γ := Kr * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) with hγ
  have hα0 : 0 ≤ α := by
    have hMx0 : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
      le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
    have hEb0 : 0 ≤ Real.exp ((B - 2 * vmax) / 2) - 1 := by
      have := Real.one_le_exp (show 0 ≤ (B - 2 * vmax) / 2 by linarith)
      linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (by have := Real.sqrt_nonneg (π * vmax / 2); linarith)) hMx0)
      (mul_nonneg (Real.sqrt_nonneg _) hEb0)
  -- the suffix walks
  set n' := n - 2 with hn'
  have hn'1 : 1 ≤ n' := by omega
  set G : ℕ → Ω₁ → ℝ := fun m => Z (m + 2) with hGdef
  have hG : IsGaussianWalk G (fun m => v (m + 2)) Q₁ := hZ.shift 2
  have hv : VarBracket (fun m => v (m + 2)) vmin vmax :=
    ⟨hvmin, fun i => (hvb (i + 2) (by omega)).1, fun i => (hvb (i + 2) (by omega)).2⟩
  set lo : ℕ → ℝ := fun i => -A - B * ((i : ℝ) + 2) - u with hlo
  set T : Set Ω₁ := barrierEvent G n' lo (fun _ => a - u) with hT
  set Rn : Set Ω₁ := {ω₁ | ∀ i ≤ n', walk (fun m ω => min (β (m + 2)) 0 * G m ω) i ω₁ ≤ L}
    with hRn
  set Tc : Set Ω₁ := {ω₁ | ∀ j ≤ n', walk G j ω₁ ≤ a - u} with hTc
  set fb : Set Ω₁ := floorBreach G n' lo with hfb
  set Ev : Set (Ω₁ × Ω₂) := {ω | (∀ i ≤ n', y + driftSum (fun m => d (m + 2)) i
      + walk (fun m => W (m + 2)) i ω.2 + walk (fun m ω => max (β (m + 2)) 0 * G m ω) i ω.1
        ≤ -L - ρ)
    ∧ ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω.2
      + driftSum (fun m => d (m + 2)) i} with hEv
  set Suf : Set (Ω₁ × Ω₂) := hp1SuffixV2 Z W β d n a A B L ρ AW BW u y with hSuf
  -- measurability
  have hwm : ∀ (c : ℕ → ℝ) j, Measurable (walk (fun m ω => c m * G m ω) j) := fun c j =>
    measurable_walk_of (fun m => (hG.measurable m).const_mul (c m)) j
  have hTm : MeasurableSet T := measurableSet_barrierEvent hG.measurable n' _ _
  have hRnm : MeasurableSet Rn := by
    have e : Rn = ⋂ i ∈ Set.Iic n',
        {ω₁ | walk (fun m ω => min (β (m + 2)) 0 * G m ω) i ω₁ ≤ L} := by
      ext ω₁
      simp [hRn]
    rw [e]
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
      measurableSet_le (hwm _ i) measurable_const
  have hTcm : MeasurableSet Tc := by
    have e : Tc = ⋂ j ∈ Set.Iic n', {ω₁ | walk G j ω₁ ≤ a - u} := by
      ext ω₁
      simp [hTc]
    rw [e]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      measurableSet_le (hG.measurable_walk j) measurable_const
  have hfbm : MeasurableSet fb := by
    have e : fb = ⋃ j ∈ Set.Icc 1 n', {ω₁ | walk G j ω₁ < lo j} := by
      ext ω₁
      simp only [hfb, floorBreach, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, exists_prop]
      constructor
      · rintro ⟨j, h1, h2, h3⟩
        exact ⟨j, ⟨h1, h2⟩, h3⟩
      · rintro ⟨j, ⟨h1, h2⟩, h3⟩
        exact ⟨j, h1, h2, h3⟩
    rw [e]
    exact MeasurableSet.biUnion (Set.to_countable _) fun j _ =>
      measurableSet_lt (hG.measurable_walk j) measurable_const
  -- (i) the height suffix, the ballot kept, with the slopes `min(β_m, 0)`
  have h1 := ofReal_suffixLow_short hZ (fun m => min (β m) 0) hm₀ hvmin hvb ha hA hB hKlate hKL
    hσR hσR0 ⟨hu1, hu2⟩ (Q₁ := Q₁)
  have hq : ballotLower vmin vmax (n - 2) (a - u) - Kr * PR * (a - u) - α * Real.exp (-u) - γ
      ≤ Q₁.real (T ∩ Rn) := by
    rcases le_or_gt (ballotLower vmin vmax (n - 2) (a - u) - Kr * PR * (a - u)
        - α * Real.exp (-u) - γ) 0 with hg | hg
    · exact le_trans hg measureReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h1
  -- (ii) the floor-breaching part
  have hfloorE : Q₁ (Tc ∩ fb) ≤ ENNReal.ofReal (floorLossDepth (A + 2 * B + u) B vmin vmax n'
      (a - u)) :=
    hG.measure_inter_floorBreach_le_depth hv hn'1 (a - u) (by linarith) hB fun i _ => by
      simp only [hlo]
      linarith
  have he : Q₁.real (Tc ∩ Rn ∩ fb) ≤ α * Real.exp (-u) := by
    have h2 : Q₁.real (Tc ∩ fb) ≤ floorLossDepth (A + 2 * B + u) B vmin vmax n' (a - u) :=
      ENNReal.toReal_le_of_le_ofReal (floorLossDepth_nonneg hB _ _) hfloorE
    have h3 := floorLossDepth_start_le (vmin := vmin) (N := n') hB hu1 hu2
    refine le_trans (measureReal_mono ?_) (le_trans h2 h3)
    rintro ω₁ ⟨⟨h4, -⟩, h5⟩
    exact ⟨h4, h5⟩
  -- (iii) `Q₁(T_c ∩ R⁻) ≥ Q₁(T ∩ R⁻) + e`
  have hTsub : T ⊆ Tc := by
    intro ω₁ hω j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · simp only [walk_zero, Pi.zero_apply]
      linarith
    · exact (hω j hj1 hj).2
  have hsplit : Q₁.real (T ∩ Rn) + Q₁.real (Tc ∩ Rn ∩ fb) ≤ Q₁.real (Tc ∩ Rn) := by
    have hdisj : Disjoint (T ∩ Rn) (Tc ∩ Rn ∩ fb) := by
      rw [Set.disjoint_left]
      rintro ω₁ ⟨hT', -⟩ ⟨-, j, hj1, hjn, hlt⟩
      have := (hT' j hj1 hjn).1
      linarith
    rw [← measureReal_union hdisj ((hTcm.inter hRnm).inter hfbm)]
    refine measureReal_mono (Set.union_subset ?_ ?_)
    · exact fun ω₁ hω => ⟨hTsub hω.1, hω.2⟩
    · exact fun ω₁ hω => hω.1
  -- (iv) the real event and Harris
  have hEvm : MeasurableSet Ev := by
    have e : Ev = (⋂ i ∈ Set.Iic n', {ω : Ω₁ × Ω₂ | y + driftSum (fun m => d (m + 2)) i
        + walk (fun m => W (m + 2)) i ω.2 + walk (fun m ω => max (β (m + 2)) 0 * G m ω) i ω.1
          ≤ -L - ρ})
        ∩ ⋂ i ∈ Set.Iic n', {ω : Ω₁ × Ω₂ | -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω.2
          + driftSum (fun m => d (m + 2)) i} := by
      ext ω
      simp [hEv]
    rw [e]
    have hWs := hW.shift 2
    refine (MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_).inter
      (MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_)
    · exact measurableSet_le (((measurable_const.add ((hWs.measurable_walk i).comp
        measurable_snd))).add ((hwm _ i).comp measurable_fst)) measurable_const
    · exact measurableSet_le measurable_const (((hWs.measurable_walk i).comp
        measurable_snd).add measurable_const)
  have hexit := le_measureReal_exitV2 hG (hW.shift 2) (fun m => β (m + 2)) (fun m => d (m + 2))
    n' (t := t) (L := L) (ρ := ρ) (y := y) ht hAW (by
      refine le_trans (le_of_eq ?_) hΛ
      rw [Finset.sum_Ico_eq_sum_range, show n - 2 = n' from rfl]
      exact Finset.sum_congr rfl fun k _ => by rw [add_comm k 2])
    (fun m hm => hBW (m + 2) (by omega) (by omega))
  have hharris := measureReal_mul_le_measureReal_inter_harrisV2 (Q₂ := Q₂) hG.measurable
    hG.indep (fun m => β (m + 2)) n' (a - u) L
    (h := fun i ω₂ => -L - ρ - y - driftSum (fun m => d (m + 2)) i
      - walk (fun m => W (m + 2)) i ω₂)
    (fun i => (measurable_const.sub ((hW.shift 2).measurable_walk i)))
    (F := {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
      + driftSum (fun m => d (m + 2)) i}) (by
        have e : {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
            + driftSum (fun m => d (m + 2)) i} = ⋂ i ∈ Set.Iic n', {ω₂ | -(AW + BW * i)
              ≤ walk (fun m => W (m + 2)) i ω₂ + driftSum (fun m => d (m + 2)) i} := by
          ext ω₂
          simp
        rw [e]
        exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
          measurableSet_le measurable_const (((hW.shift 2).measurable_walk i).add
            measurable_const))
  have eA : {ω₁ | (∀ j ≤ n', walk G j ω₁ ≤ a - u)
      ∧ ∀ j ≤ n', walk (fun m ω => min ((fun m => β (m + 2)) m) 0 * G m ω) j ω₁ ≤ L}
      = Tc ∩ Rn := rfl
  have eB : {ω : Ω₁ × Ω₂ | (∀ j ≤ n', walk (fun m ω => max ((fun m => β (m + 2)) m) 0 * G m ω)
      j ω.1 ≤ (fun i ω₂ => -L - ρ - y - driftSum (fun m => d (m + 2)) i
        - walk (fun m => W (m + 2)) i ω₂) j ω.2)
      ∧ ω.2 ∈ {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
        + driftSum (fun m => d (m + 2)) i}} = Ev := by
    ext ω
    simp only [hEv, Set.mem_setOf_eq]
    refine and_congr (forall_congr' fun i => forall_congr' fun hi => ?_) Iff.rfl
    constructor <;> intro hh <;> linarith
  have eAB : {ω : Ω₁ × Ω₂ | ((∀ j ≤ n', walk G j ω.1 ≤ a - u)
      ∧ ∀ j ≤ n', walk (fun m ω => min ((fun m => β (m + 2)) m) 0 * G m ω) j ω.1 ≤ L)
      ∧ (∀ j ≤ n', walk (fun m ω => max ((fun m => β (m + 2)) m) 0 * G m ω) j ω.1
        ≤ (fun i ω₂ => -L - ρ - y - driftSum (fun m => d (m + 2)) i
          - walk (fun m => W (m + 2)) i ω₂) j ω.2)
      ∧ ω.2 ∈ {ω₂ | ∀ i ≤ n', -(AW + BW * i) ≤ walk (fun m => W (m + 2)) i ω₂
        + driftSum (fun m => d (m + 2)) i}} = Prod.fst ⁻¹' (Tc ∩ Rn) ∩ Ev := by
    ext ω
    simp only [hEv, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, hTc, hRn]
    refine and_congr Iff.rfl (and_congr (forall_congr' fun i => forall_congr' fun hi => ?_)
      Iff.rfl)
    constructor <;> intro hh <;> linarith
  rw [eA, eB, eAB] at hharris
  -- (v) the event without the floor-breaching part lies in the suffix event
  have hcover : Prod.fst ⁻¹' (Tc ∩ Rn) ∩ Ev ⊆ Suf ∪ Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb) := by
    rintro ω ⟨⟨hTc', hRn'⟩, hEv'⟩
    by_cases hfb' : ω.1 ∈ fb
    · exact Or.inr ⟨⟨hTc', hRn'⟩, hfb'⟩
    · left
      refine ⟨fun j hj1 hjn => ⟨?_, hTc' j hjn⟩, hRn', hEv'.1, hEv'.2⟩
      by_contra hlt
      exact hfb' ⟨j, hj1, hjn, lt_of_not_ge hlt⟩
  have hSufm : MeasurableSet Suf := by
    have e : Suf = Prod.fst ⁻¹' (T ∩ Rn) ∩ Ev := by
      ext ω
      simp only [hSuf, hp1SuffixV2, hEv, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        hT, hRn]
      exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
    rw [e]
    exact (measurable_fst (hTm.inter hRnm)).inter hEvm
  have hfst : (Q₁.prod Q₂).real (Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb)) = Q₁.real (Tc ∩ Rn ∩ fb) := by
    have e : Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb) = (Tc ∩ Rn ∩ fb) ×ˢ (Set.univ : Set Ω₂) := by
      ext ω
      simp
    rw [e, measureReal_prod_prod, probReal_univ, mul_one]
  have hP : Q₁.real (Tc ∩ Rn) * (Q₁.prod Q₂).real Ev - Q₁.real (Tc ∩ Rn ∩ fb)
      ≤ (Q₁.prod Q₂).real Suf := by
    have h6 := le_trans hharris (measureReal_mono hcover)
    have h7 := measureReal_union_le (μ := Q₁.prod Q₂) Suf (Prod.fst ⁻¹' (Tc ∩ Rn ∩ fb))
    rw [hfst] at h7
    linarith
  -- (vi) the arithmetic
  have hfinal := hp1SuffixV2_arith hP hsplit hq he measureReal_nonneg measureReal_le_one hexit
    (hp1ExitV2_nonneg _ _ _ _ _ _) measureReal_nonneg (mul_nonneg hα0 (Real.exp_pos _).le)
  refine ENNReal.ofReal_le_of_le_toReal (le_trans (le_of_eq ?_) hfinal)
  ring

end Suffix

/-! ### The start with a general weight -/

/-- **The start's main term with a weight `w`**, `E[w(U₂)·RMF.hp1ExitV2(V₂)]` for
`(U₂, V₂ - D) ~ gaussianPairLaw 0 0 V S κ`, as the one-dimensional integral
`∫ w(u)·E[RMF.hp1ExitV2(D + β̄u + N(0, σ²))] dN(0, V)(u)`, `β̄ = κ/V`, `σ² = S - κ²/V`.
`RMF.startMainV2` is the weight `min((a - u)⁺, C)`. -/
noncomputable def startMainW (w : ℝ → ℝ) (V S κ D t L ρ Λ AW : ℝ) : ℝ :=
  ∫ u, w u * ∫ y, hp1ExitV2 t L ρ Λ AW (D + pairSlope V κ * u + y)
    ∂(gaussianReal 0 (pairResidVar V S κ).toNNReal) ∂(gaussianReal 0 V.toNNReal)

section StartW

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
  {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **The start of HP1 v2 with a general weight.**  `RMF.le_integral_startGoodV2` for any
measurable weight `0 ≤ w ≤ min((a - u)⁺, C)`, `C = a + A + 2B`: over the start box, `w(U₂)` times
the exit factor integrates to at least `RMF.startMainW w`, less the ceiling loss
`P(Z₀ > a)E[min((-Z₁)⁺, C)]` and `C` times the tails `RMF.startTails`; the main term by
`RMF.integral_mul_gaussianPairLaw_eq`. -/
theorem le_integral_startGoodW (hZ : IsGaussianWalk Z v Q₁) (hW : IsGaussianWalk W s Q₂)
    (β d : ℕ → ℝ) (hv0 : 0 < (v 0 : ℝ)) (hv1 : 0 < (v 1 : ℝ))
    {a A B M₁ K₂ t L ρ Λ AW : ℝ} (hAB : 0 ≤ A + B) (hB : 0 ≤ B) (hC : 0 ≤ a + A + 2 * B)
    (hM₁ : |d 0| ≤ M₁) (hK₂ : 0 ≤ K₂ + d 0 + d 1) {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ u, 0 ≤ w u) (hws : ∀ u, w u ≤ startWeight a (a + A + 2 * B) u) :
    startMainW w (v 0 + v 1) (β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1))
        (β 0 * v 0 + β 1 * v 1) (d 0 + d 1) t L ρ Λ AW
      - (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 (a + A + 2 * B) x ∂(gaussianReal 0 (v 1))
      - (a + A + 2 * B) * startTails (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) A B M₁ K₂
      ≤ ∫ ω, {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
            ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
            ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
            ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)}.indicator
          (fun ω => w (Z 0 ω.1 + Z 1 ω.1)
            * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2)
              + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))) ω ∂(Q₁.prod Q₂) := by
  set C : ℝ := a + A + 2 * B with hCdef
  set Vs : ℝ := (v 0 : ℝ) + v 1 with hVs
  set S1 : ℝ := β 0 ^ 2 * v 0 + s 0 with hS1
  set S2 : ℝ := β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1) with hS2
  set κ : ℝ := β 0 * v 0 + β 1 * v 1 with hκ
  have hz0 : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 := (hZ.measurable 0).comp measurable_fst
  have hz1 : Measurable fun ω : Ω₁ × Ω₂ => Z 1 ω.1 := (hZ.measurable 1).comp measurable_fst
  have hw0' : Measurable fun ω : Ω₁ × Ω₂ => W 0 ω.2 := (hW.measurable 0).comp measurable_snd
  have hw1' : Measurable fun ω : Ω₁ × Ω₂ => W 1 ω.2 := (hW.measurable 1).comp measurable_snd
  have hUm : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 + Z 1 ω.1 := hz0.add hz1
  have hX₀m : Measurable fun ω : Ω₁ × Ω₂ => β 0 * Z 0 ω.1 + W 0 ω.2 := (hz0.const_mul _).add hw0'
  have hYm : Measurable fun ω : Ω₁ × Ω₂ =>
      (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2) :=
    ((hz0.const_mul _).add hw0').add ((hz1.const_mul _).add hw1')
  have hV₂m : Measurable fun ω : Ω₁ × Ω₂ =>
      (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2) :=
    ((measurable_const.add (hz0.const_mul _)).add hw0').add
      ((measurable_const.add (hz1.const_mul _)).add hw1')
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  have hCS : κ ^ 2 ≤ Vs * S2 :=
    add_cauchy_schwarz (v 0).coe_nonneg hS10 (v 1).coe_nonneg (by positivity)
      (sq_mul_le_blockPair _ _ _) (sq_mul_le_blockPair _ _ _)
  -- the laws
  have hlawUY := map_startPair_eq hZ hW β hv0 hv1 (Q₁ := Q₁) (Q₂ := Q₂)
  have hlawU : (Q₁.prod Q₂).map (fun ω => Z 0 ω.1 + Z 1 ω.1) = gaussianReal 0 Vs.toNNReal := by
    have h := congrArg (Measure.map Prod.fst) hlawUY
    rw [Measure.map_map measurable_fst (hUm.prodMk hYm),
      map_fst_gaussianPairLaw (by positivity) hS20 hCS] at h
    exact h
  have hlawY : (Q₁.prod Q₂).map (fun ω => (β 0 * Z 0 ω.1 + W 0 ω.2)
      + (β 1 * Z 1 ω.1 + W 1 ω.2)) = gaussianReal 0 S2.toNNReal := by
    have h := congrArg (Measure.map Prod.snd) hlawUY
    rw [Measure.map_map measurable_snd (hUm.prodMk hYm),
      map_snd_gaussianPairLaw (by positivity) hS20 hCS] at h
    exact h
  have hlawX₀ : (Q₁.prod Q₂).map (fun ω => β 0 * Z 0 ω.1 + W 0 ω.2)
      = gaussianReal 0 S1.toNNReal := by
    have h := congrArg (Measure.map Prod.snd) (map_blockPair_eq hZ hW β hv0 (Q₁ := Q₁) (Q₂ := Q₂))
    rw [Measure.map_map measurable_snd (hz0.prodMk hX₀m),
      map_snd_gaussianPairLaw hv0.le hS10 (sq_mul_le_blockPair _ _ _)] at h
    exact h
  have hlawZ₀ : (Q₁.prod Q₂).map (fun ω => Z 0 ω.1) = gaussianReal 0 (v 0) := by
    rw [map_comp_fst_prod (hZ.measurable 0), hZ.map_eq 0]
  -- the sets
  set Good : Set (Ω₁ × Ω₂) := {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
      ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
      ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
      ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} with hGood
  set E1 : Set (Ω₁ × Ω₂) := {ω | a < Z 0 ω.1} with hE1
  set T1 : Set (Ω₁ × Ω₂) := {ω | Z 0 ω.1 ≤ 0 - (A + B)} with hT1
  set T2 : Set (Ω₁ × Ω₂) := {ω | Z 0 ω.1 + Z 1 ω.1 ≤ 0 - (A + 2 * B)} with hT2
  set T3a : Set (Ω₁ × Ω₂) := {ω | 0 + (M₁ - d 0) ≤ β 0 * Z 0 ω.1 + W 0 ω.2} with hT3a
  set T3b : Set (Ω₁ × Ω₂) := {ω | β 0 * Z 0 ω.1 + W 0 ω.2 ≤ 0 - (M₁ + d 0)} with hT3b
  set T4 : Set (Ω₁ × Ω₂) :=
    {ω | (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2) ≤ 0 - (K₂ + d 0 + d 1)} with hT4
  have hE1m : MeasurableSet E1 := measurableSet_lt measurable_const hz0
  have hT1m : MeasurableSet T1 := measurableSet_le hz0 measurable_const
  have hT2m : MeasurableSet T2 := measurableSet_le hUm measurable_const
  have hT3am : MeasurableSet T3a := measurableSet_le measurable_const hX₀m
  have hT3bm : MeasurableSet T3b := measurableSet_le hX₀m measurable_const
  have hT4m : MeasurableSet T4 := measurableSet_le hYm measurable_const
  have hGoodm : MeasurableSet Good := by
    have h1 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a} :=
      hz0 measurableSet_Icc
    have h2 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a} :=
      hUm measurableSet_Icc
    have h3 : MeasurableSet {ω : Ω₁ × Ω₂ | |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁} :=
      measurableSet_le ((measurable_const.add (hz0.const_mul _)).add hw0').abs measurable_const
    have h4 : MeasurableSet {ω : Ω₁ × Ω₂ | -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2)
        + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} :=
      measurableSet_le measurable_const hV₂m
    exact h1.inter (h2.inter (h3.inter h4))
  set F : Ω₁ × Ω₂ → ℝ := fun ω => w (Z 0 ω.1 + Z 1 ω.1)
    * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hF
  have hFm : Measurable F :=
    (hwm.comp hUm).mul ((measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m)
  have hFw : ∀ ω, F ω ≤ startWeight a C (Z 0 ω.1 + Z 1 ω.1) := fun ω =>
    le_trans (mul_le_of_le_one_right (hw0 _) (hp1ExitV2_le_one _ _ _ _ _ _)) (hws _)
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω =>
    mul_nonneg (hw0 _) (hp1ExitV2_nonneg _ _ _ _ _ _)
  have hFC : ∀ ω, F ω ≤ C := fun ω => le_trans (hFw ω) (startWeight_le _)
  -- pointwise
  set T : Ω₁ × Ω₂ → ℝ := fun ω => T1.indicator (fun _ => (1 : ℝ)) ω
    + T2.indicator (fun _ => (1 : ℝ)) ω + T3a.indicator (fun _ => (1 : ℝ)) ω
    + T3b.indicator (fun _ => (1 : ℝ)) ω + T4.indicator (fun _ => (1 : ℝ)) ω with hT
  have hpt : ∀ ω, F ω - E1.indicator F ω - C * T ω ≤ Good.indicator F ω := by
    intro ω
    have hi : ∀ T' : Set (Ω₁ × Ω₂), 0 ≤ T'.indicator (fun _ => (1 : ℝ)) ω :=
      fun T' => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hone : ∀ T' : Set (Ω₁ × Ω₂), ω ∈ T' → T'.indicator (fun _ => (1 : ℝ)) ω = 1 :=
      fun T' h => Set.indicator_of_mem h _
    have hT0 : 0 ≤ T ω := by
      simp only [hT]
      linarith [hi T1, hi T2, hi T3a, hi T3b, hi T4]
    have hCT : 0 ≤ C * T ω := mul_nonneg hC hT0
    have hE1nn : 0 ≤ E1.indicator F ω := Set.indicator_nonneg (fun ω _ => hF0 ω) ω
    have hbig : ∀ T' : Set (Ω₁ × Ω₂), ω ∈ T' → T'.indicator (fun _ => (1 : ℝ)) ω ≤ T ω →
        F ω ≤ C * T ω := by
      intro T' hm hle
      rw [hone T' hm] at hle
      nlinarith [hFC ω]
    by_cases hg : ω ∈ Good
    · rw [Set.indicator_of_mem hg]
      linarith
    · rw [Set.indicator_of_notMem hg]
      by_cases he1 : ω ∈ E1
      · rw [Set.indicator_of_mem he1]
        linarith
      · have key : F ω ≤ C * T ω := by
          by_cases h1 : ω ∈ T1
          · exact hbig T1 h1 (by simp only [hT]; linarith [hi T2, hi T3a, hi T3b, hi T4])
          by_cases h2 : ω ∈ T2
          · exact hbig T2 h2 (by simp only [hT]; linarith [hi T1, hi T3a, hi T3b, hi T4])
          by_cases h3 : ω ∈ T3a
          · exact hbig T3a h3 (by simp only [hT]; linarith [hi T1, hi T2, hi T3b, hi T4])
          by_cases h4 : ω ∈ T3b
          · exact hbig T3b h4 (by simp only [hT]; linarith [hi T1, hi T2, hi T3a, hi T4])
          by_cases h5 : ω ∈ T4
          · exact hbig T4 h5 (by simp only [hT]; linarith [hi T1, hi T2, hi T3a, hi T3b])
          by_cases hu : a ≤ Z 0 ω.1 + Z 1 ω.1
          · have h0 : F ω ≤ 0 := le_trans (hFw ω) (le_of_eq (startWeight_eq_zero hC hu))
            linarith
          exfalso
          apply hg
          simp only [hE1, hT1, hT2, hT3a, hT3b, hT4, Set.mem_setOf_eq, not_le,
            not_lt] at he1 h1 h2 h3 h4 h5 hu
          simp only [hGood, Set.mem_setOf_eq, Set.mem_Icc]
          refine ⟨⟨by linarith, he1⟩, ⟨by linarith, hu.le⟩, ?_, by linarith⟩
          rw [abs_le]
          constructor <;> linarith
        rw [Set.indicator_of_notMem he1]
        linarith
  -- the integrals
  have hbF : ∀ (E : Set (Ω₁ × Ω₂)), MeasurableSet E → Integrable (E.indicator F) (Q₁.prod Q₂) :=
    fun E hE => Integrable.of_bound (hFm.indicator hE).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ω _ => hF0 ω) ω)]
        exact le_trans (Set.indicator_le_self' (fun ω _ => hF0 ω) ω) (hFC ω))
  have hFint : Integrable F (Q₁.prod Q₂) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
      exact hFC ω)
  have hb1 : ∀ (E : Set (Ω₁ × Ω₂)), MeasurableSet E →
      Integrable (E.indicator (fun _ => (1 : ℝ))) (Q₁.prod Q₂) :=
    fun E hE => (integrable_const (1 : ℝ)).indicator hE
  have hTint : Integrable T (Q₁.prod Q₂) :=
    ((((hb1 T1 hT1m).add (hb1 T2 hT2m)).add (hb1 T3a hT3am)).add (hb1 T3b hT3bm)).add
      (hb1 T4 hT4m)
  have hIT : ∫ ω, T ω ∂(Q₁.prod Q₂) = (Q₁.prod Q₂).real T1 + (Q₁.prod Q₂).real T2
      + (Q₁.prod Q₂).real T3a + (Q₁.prod Q₂).real T3b + (Q₁.prod Q₂).real T4 := by
    have h4 := integral_add (((hb1 T1 hT1m).add (hb1 T2 hT2m)).add (hb1 T3a hT3am) |>.add
        (hb1 T3b hT3bm)) (hb1 T4 hT4m)
    have h3 := integral_add (((hb1 T1 hT1m).add (hb1 T2 hT2m)).add (hb1 T3a hT3am))
      (hb1 T3b hT3bm)
    have h2 := integral_add ((hb1 T1 hT1m).add (hb1 T2 hT2m)) (hb1 T3a hT3am)
    have h1 := integral_add (hb1 T1 hT1m) (hb1 T2 hT2m)
    simp only [Pi.add_apply] at h4 h3 h2 h1
    simp only [hT]
    rw [h4, h3, h2, h1, integral_indicator_const _ hT1m, integral_indicator_const _ hT2m,
      integral_indicator_const _ hT3am, integral_indicator_const _ hT3bm,
      integral_indicator_const _ hT4m]
    simp only [smul_eq_mul, mul_one]
  -- the tails
  have htail1 : (Q₁.prod Q₂).real T1 ≤ Real.exp (-((A + B) ^ 2 / (2 * v 0))) :=
    measureReal_le_sub_le_of_map_eq hz0 hlawZ₀ hAB
  have htail2 : (Q₁.prod Q₂).real T2 ≤ Real.exp (-((A + 2 * B) ^ 2 / (2 * Vs))) := by
    have h := measureReal_le_sub_le_of_map_eq hUm hlawU (by linarith : 0 ≤ A + 2 * B)
    rwa [Real.coe_toNNReal _ (by positivity)] at h
  have hM₁a : 0 ≤ M₁ - |d 0| := by linarith
  have htail3a : (Q₁.prod Q₂).real T3a ≤ Real.exp (-((M₁ - |d 0|) ^ 2 / (2 * S1))) := by
    have h := measureReal_add_le_le_of_map_eq hX₀m hlawX₀ (by
      have := le_abs_self (d 0); linarith : 0 ≤ M₁ - d 0)
    rw [Real.coe_toNNReal _ hS10] at h
    exact le_trans h (exp_neg_sq_div_le hS10 hM₁a (by linarith [le_abs_self (d 0)]))
  have htail3b : (Q₁.prod Q₂).real T3b ≤ Real.exp (-((M₁ - |d 0|) ^ 2 / (2 * S1))) := by
    have h := measureReal_le_sub_le_of_map_eq hX₀m hlawX₀ (by
      have := neg_abs_le (d 0); linarith : 0 ≤ M₁ + d 0)
    rw [Real.coe_toNNReal _ hS10] at h
    exact le_trans h (exp_neg_sq_div_le hS10 hM₁a (by linarith [neg_abs_le (d 0)]))
  have htail4 : (Q₁.prod Q₂).real T4 ≤ Real.exp (-((K₂ + d 0 + d 1) ^ 2 / (2 * S2))) := by
    have h := measureReal_le_sub_le_of_map_eq hYm hlawY hK₂
    rwa [Real.coe_toNNReal _ hS20] at h
  -- the main term
  have hmain : startMainW w Vs S2 κ (d 0 + d 1) t L ρ Λ AW = ∫ ω, F ω ∂(Q₁.prod Q₂) := by
    set G : ℝ × ℝ → ℝ := fun p => w p.1 * hp1ExitV2 t L ρ Λ AW (d 0 + d 1 + p.2)
      with hG
    have hGm : Measurable G := (hwm.comp measurable_fst).mul
      ((measurable_hp1ExitV2 t L ρ Λ AW).comp (measurable_const.add measurable_snd))
    have hpt0 : ∀ ω, F ω = G (Z 0 ω.1 + Z 1 ω.1,
        (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2)) := by
      intro ω
      simp only [hF, hG]
      congr 2
      ring
    have hmapint : ∫ p, G p ∂((Q₁.prod Q₂).map (fun ω => (Z 0 ω.1 + Z 1 ω.1,
        (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2))))
        = ∫ ω, G (Z 0 ω.1 + Z 1 ω.1, (β 0 * Z 0 ω.1 + W 0 ω.2) + (β 1 * Z 1 ω.1 + W 1 ω.2))
          ∂(Q₁.prod Q₂) :=
      integral_map (hUm.prodMk hYm).aemeasurable hGm.aestronglyMeasurable
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt0), ← hmapint, hlawUY]
    have hh : Measurable fun y => hp1ExitV2 t L ρ Λ AW (d 0 + d 1 + y) :=
      (measurable_hp1ExitV2 t L ρ Λ AW).comp (measurable_const.add measurable_id)
    have h := integral_mul_gaussianPairLaw_eq (V := Vs) (S := S2) (κ := κ) (Cf := C) (Ch := 1)
      (by positivity) hS20 hCS hwm hh
      (fun x => by rw [abs_of_nonneg (hw0 x)]; exact le_trans (hws x) (startWeight_le x))
      (fun x => by
        rw [abs_of_nonneg (hp1ExitV2_nonneg _ _ _ _ _ _)]
        exact hp1ExitV2_le_one _ _ _ _ _ _)
    rw [h, startMainW]
    simp only [add_assoc]
  have hceil := integral_indicator_startWeight_le hZ hC (Q₂ := Q₂) (a := a)
  have hE1le : ∫ ω, E1.indicator F ω ∂(Q₁.prod Q₂)
      ≤ (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 C x ∂(gaussianReal 0 (v 1)) := by
    refine le_trans (integral_mono (hbF E1 hE1m) ?_ fun ω => ?_) hceil
    · exact Integrable.of_bound (((measurable_startWeight a C).comp hUm).indicator
        hE1m).aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg
            (fun ω _ => startWeight_nonneg hC _) ω)]
          exact le_trans (Set.indicator_le_self' (fun ω _ => startWeight_nonneg hC _) ω)
            (startWeight_le _))
    · exact Set.indicator_le_indicator (hFw ω)
  -- assemble
  have hsum : ∫ ω, (F ω - E1.indicator F ω - C * T ω) ∂(Q₁.prod Q₂)
      ≤ ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂) :=
    integral_mono ((hFint.sub (hbF E1 hE1m)).sub (hTint.const_mul C)) (hbF Good hGoodm) hpt
  have i1 := integral_sub (hFint.sub (hbF E1 hE1m)) (hTint.const_mul C)
  have i2 := integral_sub hFint (hbF E1 hE1m)
  have i3 := integral_const_mul (μ := Q₁.prod Q₂) C T
  simp only [Pi.sub_apply] at i1 i2
  rw [hIT] at i3
  have htails : (Q₁.prod Q₂).real T1 + (Q₁.prod Q₂).real T2 + (Q₁.prod Q₂).real T3a
      + (Q₁.prod Q₂).real T3b + (Q₁.prod Q₂).real T4
      ≤ startTails (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) A B M₁ K₂ := by
    unfold startTails
    rw [← hS1, ← hS2, ← hVs]
    linarith
  have hCt := mul_le_mul_of_nonneg_left htails hC
  change _ ≤ ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂)
  linarith

/-- `min((a - u)⁺, C) ≤ a + min((-u)⁺, C)` for `a ≥ 0`. -/
lemma startWeight_le_add {a C : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    startWeight a C u ≤ a + startWeight 0 C u := by
  unfold startWeight
  have h1 : max (a - u) 0 ≤ a + max (0 - u) 0 :=
    max_le (by linarith [le_max_left (0 - u) 0]) (by linarith [le_max_right (0 - u) 0])
  calc min (max (a - u) 0) C ≤ min (a + max (0 - u) 0) (a + C) :=
        min_le_min h1 (by linarith)
    _ = a + min (max (0 - u) 0) C := min_add_add_left a _ _

/-- **The start's weight in mean**: `E[min((a - U₂)⁺, C)] ≤ a + √(V/(2π))` for the start's height
`U₂ = Z₀ + Z₁ ~ N(0, V)`, `V = v₀ + v₁` (`RMF.integral_startWeight_zero_le`). -/
lemma integral_startWeight_start_le (hZ : IsGaussianWalk Z v Q₁) {a C : ℝ} (ha : 0 ≤ a)
    (hC : 0 ≤ C) :
    ∫ ω, startWeight a C (Z 0 ω.1 + Z 1 ω.1) ∂(Q₁.prod Q₂)
      ≤ a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹ := by
  have hU : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 + Z 1 ω.1 :=
    ((hZ.measurable 0).comp measurable_fst).add ((hZ.measurable 1).comp measurable_fst)
  have hwalk : (fun ω₁ => Z 0 ω₁ + Z 1 ω₁) = walk Z 2 := by
    funext ω₁
    simp [walk_apply, Finset.sum_range_succ]
  have hV : ((v 0 : ℝ) + v 1).toNNReal = v 0 + v 1 := by
    rw [← NNReal.coe_add, Real.toNNReal_coe]
  have hlaw : (Q₁.prod Q₂).map (fun ω => Z 0 ω.1 + Z 1 ω.1)
      = gaussianReal 0 ((v 0 : ℝ) + v 1).toNNReal := by
    have h := map_comp_fst_prod (Q₁ := Q₁) (Q₂ := Q₂) (f := fun ω₁ => Z 0 ω₁ + Z 1 ω₁)
      ((hZ.measurable 0).add (hZ.measurable 1))
    rw [h, hwalk, hZ.map_walk 2, hV]
    simp [Finset.sum_range_succ]
  have hbd : ∀ a' : ℝ, Integrable (startWeight a' C) (gaussianReal 0 ((v 0 : ℝ) + v 1).toNNReal) :=
    fun a' => Integrable.of_bound (measurable_startWeight a' C).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (startWeight_nonneg hC x)]
        exact startWeight_le x)
  have hE := integral_startWeight_zero_le (v := (v 0 : ℝ) + v 1) (by positivity) hC
  rw [← integral_map hU.aemeasurable (measurable_startWeight a C).aestronglyMeasurable, hlaw]
  calc ∫ x, startWeight a C x ∂(gaussianReal 0 ((v 0 : ℝ) + v 1).toNNReal)
      ≤ ∫ x, (a + startWeight 0 C x) ∂(gaussianReal 0 ((v 0 : ℝ) + v 1).toNNReal) :=
        integral_mono (hbd a) ((integrable_const a).add (hbd 0)) (startWeight_le_add ha)
    _ = a + ∫ x, startWeight 0 C x ∂(gaussianReal 0 ((v 0 : ℝ) + v 1).toNNReal) := by
        rw [integral_add (integrable_const a) (hbd 0), integral_const, probReal_univ, one_smul]
    _ ≤ a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹ := by linarith

end StartW

/-! ### The window's first moment on short tubes, Gaussian side -/

/-- **The start's weight on short tubes**, `sw·e^{-sw²/(2N)}` with `sw = min((a - u)⁺, C)`: at
`N = (n₀ - 2)v₋` the ballot of `RMF.ballotLower_ge_short` at `c = a - u`, `√n` and `2/√(2πv₊)`
removed. -/
noncomputable def startWeightShort (Nv a C u : ℝ) : ℝ :=
  startWeight a C u * Real.exp (-(startWeight a C u ^ 2 / (2 * Nv)))

lemma startWeightShort_nonneg {Nv a C : ℝ} (hC : 0 ≤ C) (u : ℝ) :
    0 ≤ startWeightShort Nv a C u :=
  mul_nonneg (startWeight_nonneg hC u) (Real.exp_pos _).le

lemma startWeightShort_le {Nv a C : ℝ} (hC : 0 ≤ C) (hNv : 0 ≤ Nv) (u : ℝ) :
    startWeightShort Nv a C u ≤ startWeight a C u := by
  unfold startWeightShort
  refine mul_le_of_le_one_right (startWeight_nonneg hC u) (Real.exp_le_one_iff.2 ?_)
  have : 0 ≤ startWeight a C u ^ 2 / (2 * Nv) := div_nonneg (sq_nonneg _) (by linarith)
  linarith

lemma measurable_startWeightShort (Nv a C : ℝ) : Measurable (startWeightShort Nv a C) :=
  (measurable_startWeight a C).mul (Real.measurable_exp.comp
    (((measurable_startWeight a C).pow_const 2).div_const _).neg)

/-- On `[a - C, a]` the weight is `(a - u)e^{-(a-u)²/(2N)}`. -/
lemma startWeightShort_eq {Nv a C u : ℝ} (h1 : a - C ≤ u) (h2 : u ≤ a) :
    startWeightShort Nv a C u = (a - u) * Real.exp (-((a - u) ^ 2 / (2 * Nv))) := by
  rw [startWeightShort, startWeight_eq h1 h2]

/-- **The start's main term on short tubes**, `RMF.startMainW` at the weight
`RMF.startWeightShort N a C`:
`∫ sw·e^{-sw²/(2N)}·E[RMF.hp1ExitV2(D + β̄u + N(0, σ²))] dN(0, V)(u)`. -/
noncomputable def startMainShort (Nv a C V S κ D t L ρ Λ AW : ℝ) : ℝ :=
  startMainW (startWeightShort Nv a C) V S κ D t L ρ Λ AW

/-- The start term of `RMF.hp1LowerBoundShort`: `RMF.hp1StartV2` with the main term
`RMF.startMainShort` at `N = (n₀ - 2)v₋`, less the ceiling loss `P(Z₀ > a)E[min((-Z₁)⁺, C)]` and
`C` times the tails, `C = a + A + 2B`. -/
noncomputable def hp1StartShort (n₀ : ℕ) (vmin v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW : ℝ) :
    ℝ :=
  startMainShort (((n₀ : ℝ) - 2) * vmin) a (a + A + 2 * B) (v₀ + v₁)
      (β₀ ^ 2 * v₀ + s₀ + (β₁ ^ 2 * v₁ + s₁)) (β₀ * v₀ + β₁ * v₁) (d₀ + d₁) t L ρ Λ AW
    - (gaussianReal 0 v₀.toNNReal).real (Set.Ioi a)
      * ∫ x, startWeight 0 (a + A + 2 * B) x ∂(gaussianReal 0 v₁.toNNReal)
    - (a + A + 2 * B) * startTails v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ A B M₁ K₂

/-- **The window's first-moment lower bound on short tubes, Gaussian side**, `√n` removed:
`2/√(2πv₊)·RMF.hp1StartShort - K_r'P_R(a + √(V/(2π))) - RMF.hp1Loss`,
`K_r' = √(2n₀/(π(n₀-2-m₀)v₋))`, `P_R = e^{-(L-K)²/(2σ²)}`, `V = v₀ + v₁`. -/
noncomputable def hp1LowerBoundShort (n₀ m₀ : ℕ)
    (vmin vmax v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW Klate σR2 : ℝ) : ℝ :=
  2 / √(2 * π * vmax) * hp1StartShort n₀ vmin v₀ v₁ s₀ s₁ β₀ β₁ d₀ d₁ a A B M₁ K₂ ρ L t Λ AW
    - √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) * Real.exp (-((L - Klate) ^ 2 / (2 * σR2)))
      * (a + √(v₀ + v₁) * (√(2 * π))⁻¹)
    - hp1Loss n₀ m₀ vmin vmax (v₀ + v₁) a A B L Klate σR2

/-- The pointwise comparison of `RMF.le_measure_windowEvent_gaussian_short` on the start box, as
real arithmetic: from `kw ≤ b` and `E ≥ 0`, `k(wE) - K(sE) - γE - αe ≤ (b - Ks - γ)E - αe`. -/
lemma short_pointwise_arith {k w b s K γ E α e : ℝ} (hkw : k * w ≤ b) (hE : 0 ≤ E) :
    k * (w * E) - K * (s * E) - γ * E - α * e ≤ (b - K * s - γ) * E - α * e := by
  have h1 : k * (w * E) ≤ b * E := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hkw hE
  have e1 : (b - K * s - γ) * E - α * e = b * E - K * (s * E) - γ * E - α * e := by ring
  rw [e1]
  linarith

/-- The final comparison of `RMF.le_measure_windowEvent_gaussian_short`, as real arithmetic. -/
lemma short_final_arith {k X IF KP u₂ PR T IF₁ γ IEx α IEu EV Lo sn J : ℝ}
    (hJ : J = k / sn * IF - KP * IF₁ - γ * IEx - α * IEu) (hk : 0 ≤ k) (hsn : 0 < sn)
    (hX : X ≤ IF) (hKP0 : 0 ≤ KP) (hIF₁ : IF₁ ≤ T) (hKP : KP * T ≤ u₂ / sn * PR * T)
    (hγ : 0 ≤ γ) (hIEx : IEx ≤ 1) (hα : 0 ≤ α) (hIEu : IEu ≤ EV)
    (hLo : α * EV + γ ≤ Lo / sn) :
    (k * X - u₂ * PR * T - Lo) / sn ≤ J := by
  have h1 : k / sn * X ≤ k / sn * IF := mul_le_mul_of_nonneg_left hX (div_nonneg hk hsn.le)
  have h2 : KP * IF₁ ≤ KP * T := mul_le_mul_of_nonneg_left hIF₁ hKP0
  have h3 : γ * IEx ≤ γ * 1 := mul_le_mul_of_nonneg_left hIEx hγ
  have h4 : α * IEu ≤ α * EV := mul_le_mul_of_nonneg_left hIEu hα
  have e : (k * X - u₂ * PR * T - Lo) / sn = k / sn * X - u₂ / sn * PR * T - Lo / sn := by ring
  rw [e, hJ]
  linarith

section AssemblyShort

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
  {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {Z : ℕ → Ω₁ → ℝ} {W : ℕ → Ω₂ → ℝ} {v s : ℕ → ℝ≥0}

/-- **The window's first moment on short tubes, Gaussian side.**  In the setting of
`RMF.le_measure_windowEvent_gaussian_v2`, under its hypotheses without
`(a + A + 2B)² ≤ 2(n₀ - 2)v₋`, the two-sided window event has probability at least
`RMF.hp1LowerBoundShort … / √n` for every `n ≥ n₀`.

Given the start `(U₂, V₂)` the suffix is bounded by `RMF.ofReal_le_measure_hp1SuffixV2_short`, the
ballot kept; on the start box the ballot is at least `2/(√(2πv₊)√n)·RMF.startWeightShort(U₂)`
(`RMF.ballotLower_ge_short`), whose integral against the exit factor is
`RMF.le_integral_startGoodW`; the slope loss `K_rP_R(a - U₂)` is paid by
`RMF.integral_startWeight_start_le`, the floor loss and `γ` as in v2; they combine by conditioning
on the start (`RMF.lintegral_start_le_measureV2`). -/
theorem le_measure_windowEvent_gaussian_short (hZ : IsGaussianWalk Z v Q₁)
    (hW : IsGaussianWalk W s Q₂) (β d : ℕ → ℝ) {n₀ m₀ n : ℕ} (hn₀ : m₀ + 3 ≤ n₀) (hn : n₀ ≤ n)
    {vmin vmax a A B A' B' M₁ K₂ ρ L t Λ AW BW Klate KR σR2 : ℝ}
    (hv0 : 0 < (v 0 : ℝ)) (hv1 : 0 < (v 1 : ℝ)) (hvmin : 0 < vmin)
    (hvb : ∀ m, 2 ≤ m → vmin ≤ (v m : ℝ) ∧ (v m : ℝ) ≤ vmax)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 2 * vmax < B)
    (ht : 0 ≤ t) (hAW : 0 ≤ AW)
    (hΛ : ∑ m ∈ Finset.Ico 2 n,
      max 0 (t * d m + t ^ 2 * (max (β m) 0 ^ 2 * (v m : ℝ) + s m) / 2) ≤ Λ)
    (hBW : ∀ m, 2 ≤ m → m < n → (s m : ℝ) / 2 - d m ≤ BW)
    (hσR : ∑ m ∈ Finset.Ico 2 (m₀ + 2), min (β m) 0 ^ 2 * (v m : ℝ) ≤ σR2) (hσR0 : 0 < σR2)
    (hKlate : ∑ m ∈ Finset.Ico (m₀ + 2) n,
      |min (β m) 0| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ Klate) (hKL : Klate ≤ L)
    (hKR : ∑ m ∈ Finset.Ico 2 n, |β m| * ((a + A + B * m) + (a + A + B * (m + 1))) ≤ KR)
    (hM₁ : |d 0| ≤ M₁) (hK₂ : 0 ≤ K₂ + d 0 + d 1)
    (hA' : K₂ + KR + AW ≤ A') (hBW' : BW ≤ B') (hB'0 : 0 ≤ B') :
    hp1LowerBoundShort n₀ m₀ vmin vmax (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) a A B M₁
        K₂ ρ L t Λ AW Klate σR2 / √(n : ℝ)
      ≤ ((Q₁.prod Q₂) (barrierEventPair
          (fun m ω => ((Z m ω.1, d m + β m * Z m ω.1 + W m ω.2) : ℝ × ℝ)) n
          (fun j => -A - B * j) (fun _ => a)
          (fun j => if j = 1 then -M₁ else -A' - B' * j)
          (fun j => if j = 1 then M₁ else -ρ))).toReal := by
  -- basic facts
  have hvmax : 0 < vmax := lt_of_lt_of_le hvmin (le_trans (hvb 2 le_rfl).1 (hvb 2 le_rfl).2)
  have hB0 : 0 ≤ B := by linarith
  have hC0 : 0 ≤ a + A + 2 * B := by linarith
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀3 : (3 : ℝ) ≤ n₀ := by exact_mod_cast (show 3 ≤ n₀ by omega)
  have hNeq : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hNv : 0 < ((n₀ : ℝ) - 2) * vmin := mul_pos (by linarith) hvmin
  have hc0 : 0 ≤ √(π * vmax / 2) := Real.sqrt_nonneg _
  have hEb0 : 0 < Real.exp ((B - 2 * vmax) / 2) - 1 := by
    have : 0 < (B - 2 * vmax) / 2 := by linarith
    have := Real.add_one_lt_exp this.ne'
    linarith
  have hMx0 : 0 ≤ max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax))) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hPR0 : 0 ≤ Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) := (Real.exp_pos _).le
  -- the constants of the height suffix
  set Kr := √(2 / (π * (((n - 2 - m₀ : ℕ) : ℝ) * vmin))) with hKr
  set PR := Real.exp (-((L - Klate) ^ 2 / (2 * σR2))) with hPR
  set α := Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
    * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
    / (√((n - 2 : ℕ) : ℝ) * (Real.exp ((B - 2 * vmax) / 2) - 1)) with hα
  set γ := Kr * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) with hγ
  have hα0 : 0 ≤ α := div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
    hMx0) (mul_nonneg (Real.sqrt_nonneg _) hEb0.le)
  have hγ0 : 0 ≤ γ := mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hc0 hPR0)
    (Real.sqrt_nonneg _))
  set g : ℝ × ℝ → ℝ := fun p => (ballotLower vmin vmax (n - 2) (a - p.1) - Kr * PR * (a - p.1)
      - γ) * hp1ExitV2 t L ρ Λ AW p.2 - α * Real.exp (-p.1) with hgdef
  have hgm : Measurable g :=
    (((((continuous_ballotLower vmin vmax (n - 2)).measurable.comp
      (measurable_const.sub measurable_fst)).sub
        (measurable_const.mul (measurable_const.sub measurable_fst))).sub measurable_const).mul
      ((measurable_hp1ExitV2 t L ρ Λ AW).comp measurable_snd)).sub
      (measurable_const.mul (Real.measurable_exp.comp measurable_fst.neg))
  -- the suffix from each start of the box
  have hsuf : ∀ u ∈ Set.Icc (-A - 2 * B) a, ∀ y, ENNReal.ofReal (g (u, y))
      ≤ (Q₁.prod Q₂) (hp1SuffixV2 Z W β d n a A B L ρ AW BW u y) :=
    fun u hu y => ofReal_le_measure_hp1SuffixV2_short hZ hW β d (by omega) hvmin hvb ha hA hB
      hKlate hKL hσR hσR0 ht hAW hΛ hBW hu
  -- conditioning on the start
  have hcond := lintegral_start_le_measureV2 hZ hW β d (n := n) (by omega) ha hA hB0 hKR hA'
    hBW' hB'0 hgm hsuf (M₁ := M₁) (K₂ := K₂)
  -- the start integral
  have hz0 : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 := (hZ.measurable 0).comp measurable_fst
  have hz1 : Measurable fun ω : Ω₁ × Ω₂ => Z 1 ω.1 := (hZ.measurable 1).comp measurable_fst
  have hw0 : Measurable fun ω : Ω₁ × Ω₂ => W 0 ω.2 := (hW.measurable 0).comp measurable_snd
  have hw1 : Measurable fun ω : Ω₁ × Ω₂ => W 1 ω.2 := (hW.measurable 1).comp measurable_snd
  have hUm : Measurable fun ω : Ω₁ × Ω₂ => Z 0 ω.1 + Z 1 ω.1 := hz0.add hz1
  have hV₂m : Measurable fun ω : Ω₁ × Ω₂ =>
      (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2) :=
    ((measurable_const.add (hz0.const_mul _)).add hw0).add
      ((measurable_const.add (hz1.const_mul _)).add hw1)
  set Good : Set (Ω₁ × Ω₂) := {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a
      ∧ Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a
      ∧ |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁
      ∧ -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} with hGood
  have hGoodm : MeasurableSet Good := by
    have e1 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 ∈ Set.Icc (-A - B) a} :=
      hz0 measurableSet_Icc
    have e2 : MeasurableSet {ω : Ω₁ × Ω₂ | Z 0 ω.1 + Z 1 ω.1 ∈ Set.Icc (-A - 2 * B) a} :=
      hUm measurableSet_Icc
    have e3 : MeasurableSet {ω : Ω₁ × Ω₂ | |d 0 + β 0 * Z 0 ω.1 + W 0 ω.2| ≤ M₁} :=
      measurableSet_le ((measurable_const.add (hz0.const_mul _)).add hw0).abs measurable_const
    have e4 : MeasurableSet {ω : Ω₁ × Ω₂ | -K₂ ≤ (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2)
        + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)} :=
      measurableSet_le measurable_const hV₂m
    exact e1.inter (e2.inter (e3.inter e4))
  have hstart := le_integral_startGoodW hZ hW β d hv0 hv1 (by linarith) hB0 hC0 hM₁ hK₂
    (t := t) (L := L) (ρ := ρ) (Λ := Λ) (AW := AW) (Q₁ := Q₁) (Q₂ := Q₂)
    (w := startWeightShort (((n₀ : ℝ) - 2) * vmin) a (a + A + 2 * B))
    (measurable_startWeightShort _ _ _) (startWeightShort_nonneg hC0)
    (startWeightShort_le hC0 hNv.le)
  set X := hp1StartShort n₀ vmin (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) a A B M₁ K₂ ρ L
    t Λ AW with hX
  have hXeq : X = startMainShort (((n₀ : ℝ) - 2) * vmin) a (a + A + 2 * B) ((v 0 : ℝ) + v 1)
        (β 0 ^ 2 * v 0 + s 0 + (β 1 ^ 2 * v 1 + s 1)) (β 0 * v 0 + β 1 * v 1) (d 0 + d 1)
        t L ρ Λ AW
      - (gaussianReal 0 (v 0)).real (Set.Ioi a)
        * ∫ x, startWeight 0 (a + A + 2 * B) x ∂(gaussianReal 0 (v 1))
      - (a + A + 2 * B)
        * startTails (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) A B M₁ K₂ := by
    rw [hX, hp1StartShort, Real.toNNReal_coe, Real.toNNReal_coe]
  -- the integrands on the box: the short weight, the plain weight, the exit factor, `e^{-U₂}`
  set F : Ω₁ × Ω₂ → ℝ := fun ω => startWeightShort (((n₀ : ℝ) - 2) * vmin) a (a + A + 2 * B)
      (Z 0 ω.1 + Z 1 ω.1)
    * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hF
  set F₁ : Ω₁ × Ω₂ → ℝ := fun ω => startWeight a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1)
    * hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hF₁
  set Ex : Ω₁ × Ω₂ → ℝ := fun ω =>
    hp1ExitV2 t L ρ Λ AW ((d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2))
    with hEx
  have hFm : Measurable F :=
    ((measurable_startWeightShort _ _ _).comp hUm).mul
      ((measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m)
  have hF₁m : Measurable F₁ :=
    ((measurable_startWeight a _).comp hUm).mul ((measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m)
  have hExm : Measurable Ex := (measurable_hp1ExitV2 t L ρ Λ AW).comp hV₂m
  have hexp := integral_exp_neg_start hZ (Q₂ := Q₂)
  have hbnd : ∀ (f : Ω₁ × Ω₂ → ℝ) (K : ℝ), Measurable f → (∀ ω, 0 ≤ f ω) → (∀ ω, f ω ≤ K) →
      Integrable (Good.indicator f) (Q₁.prod Q₂) := by
    intro f K hfm hf0 hfK
    refine Integrable.of_bound (hfm.indicator hGoodm).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ω _ => hf0 ω) ω)]
    exact le_trans (Set.indicator_le_self' (fun ω _ => hf0 ω) ω) (hfK ω)
  have hiF : Integrable (Good.indicator F) (Q₁.prod Q₂) :=
    hbnd F (a + A + 2 * B) hFm
      (fun ω => mul_nonneg (startWeightShort_nonneg hC0 _) (hp1ExitV2_nonneg _ _ _ _ _ _))
      (fun ω => le_trans (mul_le_of_le_one_right (startWeightShort_nonneg hC0 _)
        (hp1ExitV2_le_one _ _ _ _ _ _)) (le_trans (startWeightShort_le hC0 hNv.le _)
          (startWeight_le _)))
  have hiF₁ : Integrable (Good.indicator F₁) (Q₁.prod Q₂) :=
    hbnd F₁ (a + A + 2 * B) hF₁m
      (fun ω => mul_nonneg (startWeight_nonneg hC0 _) (hp1ExitV2_nonneg _ _ _ _ _ _))
      (fun ω => le_trans (mul_le_of_le_one_right (startWeight_nonneg hC0 _)
        (hp1ExitV2_le_one _ _ _ _ _ _)) (startWeight_le _))
  have hiEx : Integrable (Good.indicator Ex) (Q₁.prod Q₂) :=
    hbnd Ex 1 hExm (fun ω => hp1ExitV2_nonneg _ _ _ _ _ _)
      (fun ω => hp1ExitV2_le_one _ _ _ _ _ _)
  have hiE : Integrable (Good.indicator fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1)))
      (Q₁.prod Q₂) := hexp.1.indicator hGoodm
  -- the lower integrand `J`, pointwise below `g(U₂, V₂)` on the box
  have hiJ : Integrable (fun ω => 2 / √(2 * π * vmax) / √(n : ℝ) * Good.indicator F ω
      - Kr * PR * Good.indicator F₁ ω - γ * Good.indicator Ex ω
      - α * Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω) (Q₁.prod Q₂) :=
    ((((hiF.const_mul (2 / √(2 * π * vmax) / √(n : ℝ))).sub (hiF₁.const_mul (Kr * PR))).sub
      (hiEx.const_mul γ)).sub (hiE.const_mul α)).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have hJ : ∫ ω, (2 / √(2 * π * vmax) / √(n : ℝ) * Good.indicator F ω
      - Kr * PR * Good.indicator F₁ ω - γ * Good.indicator Ex ω
      - α * Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω) ∂(Q₁.prod Q₂)
      = 2 / √(2 * π * vmax) / √(n : ℝ) * ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂)
        - Kr * PR * ∫ ω, Good.indicator F₁ ω ∂(Q₁.prod Q₂)
        - γ * ∫ ω, Good.indicator Ex ω ∂(Q₁.prod Q₂)
        - α * ∫ ω, Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω
          ∂(Q₁.prod Q₂) := by
    have i1 := integral_sub (((hiF.const_mul (2 / √(2 * π * vmax) / √(n : ℝ))).sub
      (hiF₁.const_mul (Kr * PR))).sub (hiEx.const_mul γ)) (hiE.const_mul α)
    have i2 := integral_sub ((hiF.const_mul (2 / √(2 * π * vmax) / √(n : ℝ))).sub
      (hiF₁.const_mul (Kr * PR))) (hiEx.const_mul γ)
    have i3 := integral_sub (hiF.const_mul (2 / √(2 * π * vmax) / √(n : ℝ)))
      (hiF₁.const_mul (Kr * PR))
    simp only [Pi.sub_apply] at i1 i2 i3
    rw [i1, i2, i3, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hpt : ∀ ω, ENNReal.ofReal (2 / √(2 * π * vmax) / √(n : ℝ) * Good.indicator F ω
      - Kr * PR * Good.indicator F₁ ω - γ * Good.indicator Ex ω
      - α * Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω)
      ≤ Good.indicator (fun ω => ENNReal.ofReal (g (Z 0 ω.1 + Z 1 ω.1,
        (d 0 + β 0 * Z 0 ω.1 + W 0 ω.2) + (d 1 + β 1 * Z 1 ω.1 + W 1 ω.2)))) ω := by
    intro ω
    by_cases hω : ω ∈ Good
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      refine ENNReal.ofReal_le_ofReal ?_
      have hu := hω.2.1
      rw [Set.mem_Icc] at hu
      have hsw : startWeight a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1) = a - (Z 0 ω.1 + Z 1 ω.1) :=
        startWeight_eq (by linarith) hu.2
      have hbl : 2 / √(2 * π * vmax) / √(n : ℝ)
          * startWeightShort (((n₀ : ℝ) - 2) * vmin) a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1)
          ≤ ballotLower vmin vmax (n - 2) (a - (Z 0 ω.1 + Z 1 ω.1)) := by
        rw [startWeightShort_eq (by linarith) hu.2]
        exact ballotLower_ge_short (by omega) hn hvmin hvmax (by linarith)
      simp only [hF, hF₁, hEx, hgdef]
      rw [hsw]
      exact short_pointwise_arith hbl (hp1ExitV2_nonneg _ _ _ _ _ _)
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
        Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      simp
  -- the window event from below
  have hlint := le_trans (ofReal_integral_le_lintegral_ofReal hiJ) (lintegral_mono hpt)
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) (le_trans hlint hcond)
  rw [ENNReal.toReal_ofReal'] at hreal
  -- the four integrals
  have hFX : X ≤ ∫ ω, Good.indicator F ω ∂(Q₁.prod Q₂) := by
    rw [hXeq]
    exact hstart
  have hisw : Integrable (fun ω : Ω₁ × Ω₂ => startWeight a (a + A + 2 * B) (Z 0 ω.1 + Z 1 ω.1))
      (Q₁.prod Q₂) :=
    Integrable.of_bound ((measurable_startWeight a _).comp hUm).aestronglyMeasurable
      (a + A + 2 * B) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (startWeight_nonneg hC0 _)]
        exact startWeight_le _)
  have hF₁le : ∫ ω, Good.indicator F₁ ω ∂(Q₁.prod Q₂)
      ≤ a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹ := by
    refine le_trans (integral_mono hiF₁ hisw fun ω => ?_) (integral_startWeight_start_le hZ ha hC0)
    by_cases hω : ω ∈ Good
    · rw [Set.indicator_of_mem hω]
      exact mul_le_of_le_one_right (startWeight_nonneg hC0 _) (hp1ExitV2_le_one _ _ _ _ _ _)
    · rw [Set.indicator_of_notMem hω]
      exact startWeight_nonneg hC0 _
  have hExle : ∫ ω, Good.indicator Ex ω ∂(Q₁.prod Q₂) ≤ 1 := by
    calc ∫ ω, Good.indicator Ex ω ∂(Q₁.prod Q₂)
        ≤ ∫ _ : Ω₁ × Ω₂, (1 : ℝ) ∂(Q₁.prod Q₂) :=
          integral_mono hiEx (integrable_const 1) fun ω => by
            by_cases hω : ω ∈ Good
            · rw [Set.indicator_of_mem hω]
              exact hp1ExitV2_le_one _ _ _ _ _ _
            · rw [Set.indicator_of_notMem hω]
              exact zero_le_one
      _ = 1 := by simp
  have hEle : ∫ ω, Good.indicator (fun ω => Real.exp (-(Z 0 ω.1 + Z 1 ω.1))) ω ∂(Q₁.prod Q₂)
      ≤ Real.exp (((v 0 : ℝ) + v 1) / 2) := by
    rw [← hexp.2]
    exact integral_mono hiE hexp.1 fun ω =>
      Set.indicator_le_self' (fun ω _ => (Real.exp_pos _).le) ω
  -- the scaling in `n`
  have hsqn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hKrn := sqrt_slopeLoss_le hn₀ hn hvmin
  have hα' : α ≤ √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
      * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
        * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
        / (Real.exp ((B - 2 * vmax) / 2) - 1)) / √(n : ℝ) := by
    have h1 := sqrt_div_natSub_le (c := 1) zero_le_one (k := 2) (n₀ := n₀) (n := n)
      (by omega) hn
    rw [one_mul] at h1
    set K1 := Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
      * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
      / (Real.exp ((B - 2 * vmax) / 2) - 1) with hK1
    have hK10 : 0 ≤ K1 := div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
      hMx0) hEb0.le
    have hNpos : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by rw [hNeq]; linarith
    have e1 : α = K1 * √(1 / ((n - 2 : ℕ) : ℝ)) := by
      rw [hα, hK1, Real.sqrt_div' _ hNpos.le, Real.sqrt_one]
      field_simp
    rw [e1]
    calc K1 * √(1 / ((n - 2 : ℕ) : ℝ)) ≤ K1 * (√((n₀ : ℝ) / ((n₀ : ℝ) - 2)) / √(n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK10
          simpa using h1
      _ = √((n₀ : ℝ) / ((n₀ : ℝ) - 2)) * K1 / √(n : ℝ) := by ring
  have hγ' : γ ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin)))
      * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) / √(n : ℝ) := by
    have hQ0 : 0 ≤ √(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax)) :=
      add_nonneg (mul_nonneg hc0 hPR0) (Real.sqrt_nonneg _)
    rw [hγ]
    calc Kr * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax)))
        ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) / √(n : ℝ)
          * (√(π * vmax / 2) * PR + √(PR * ((m₀ : ℝ) * vmax))) :=
          mul_le_mul_of_nonneg_right hKrn hQ0
      _ = _ := by ring
  have hloss : α * Real.exp (((v 0 : ℝ) + v 1) / 2) + γ
      ≤ hp1Loss n₀ m₀ vmin vmax ((v 0 : ℝ) + v 1) a A B L Klate σR2 / √(n : ℝ) := by
    have hE0 : 0 ≤ Real.exp (((v 0 : ℝ) + v 1) / 2) := (Real.exp_pos _).le
    have h2 := mul_le_mul_of_nonneg_right hα' hE0
    have e : √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
          * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (Real.exp ((B - 2 * vmax) / 2) - 1)) / √(n : ℝ)
          * Real.exp (((v 0 : ℝ) + v 1) / 2)
        = √((n₀ : ℝ) / ((n₀ : ℝ) - 2))
          * (Real.exp (-(A + 2 * B)) * (a + A + 2 * B + √(π * vmax / 2) + 2)
            * max √(4 / (π * vmin)) √(2 / (Real.exp 1 * (B - 2 * vmax)))
            / (Real.exp ((B - 2 * vmax) / 2) - 1)) * Real.exp (((v 0 : ℝ) + v 1) / 2)
          / √(n : ℝ) := by ring
    rw [e] at h2
    refine le_trans (add_le_add h2 hγ') (le_of_eq ?_)
    rw [hp1Loss, ← add_div]
  have hT0 : 0 ≤ a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹ :=
    add_nonneg ha (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _)))
  have hKP : Kr * PR * (a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹)
      ≤ √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) / √(n : ℝ) * PR
        * (a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKrn hPR0) hT0
  -- conclude
  have hLB : hp1LowerBoundShort n₀ m₀ vmin vmax (v 0) (v 1) (s 0) (s 1) (β 0) (β 1) (d 0) (d 1) a A
      B M₁ K₂ ρ L t Λ AW Klate σR2
      = 2 / √(2 * π * vmax) * X - √(2 * n₀ / (π * (((n₀ : ℝ) - 2 - m₀) * vmin))) * PR
          * (a + √((v 0 : ℝ) + v 1) * (√(2 * π))⁻¹)
        - hp1Loss n₀ m₀ vmin vmax ((v 0 : ℝ) + v 1) a A B L Klate σR2 := rfl
  rw [hLB]
  refine le_trans (short_final_arith hJ (div_nonneg zero_le_two (Real.sqrt_nonneg _)) hsqn hFX
    (mul_nonneg (Real.sqrt_nonneg _) hPR0) hF₁le hKP hγ0 hExle hα0 hEle hloss)
    (le_trans (le_max_left _ _) hreal)

end AssemblyShort

end RMF
