/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.PerScale
import RMF.UniformLower.HP1CertShort
import RMF.UniformLower.HP2WindowShort

/-!
# Per scale on short tubes

`RMF/UniformLower/PerScale.lean`'s per-scale value and main term on tubes of `r ≥ 35` blocks, with
HP1 and HP2 at the tube's length.

* **The per-scale constant** `RMF.perScaleConstShort q K r = c₃^{2-q}C₂^{-(1-q)}2^{-q}·
  ((1 - e^{-100})P₁(r))^{2-q}Q(r)^{-(1-q)}`, `P₁ = RMF.hp1P1Short` (at least `0.28668` from
  `r = 35`), `Q = RMF.hp2QShort`: positive from `r = 35` and nondecreasing in `r`
  (`RMF.monotone_perScaleConstShort`).
* **The per-scale value** (`RMF.le_integral_indicator_rpow_headWindowMass_short`): the general
  `RMF.le_integral_indicator_rpow_headWindowMass` with HP1 on short tubes
  (`RMF.le_integral_hp1Tube_inter_hp1After_window_short`) and HP2 per tube length
  (`RMF.integral_integral_pair_rest_le_short`).
* **The main term** at the maximal block counts `r = T - k` for the scales `k + 35 ≤ T`:
  `RMF.le_integral_rpow_integral_lineDiv_short`,
  `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_short` and, with `N_q` explicit,
  `RMF.le_rpow_mul_integral_rpow_integral_lineDiv_explicit_short`.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

/-! ### The per-scale constant on short tubes -/

/-- **HP1's certified constant on tubes of `r ≥ 35` blocks from below**: the rung `35`'s `0.28668`
(`RMF.monotone_hp1P1Short`). -/
lemma hp1P1Short_ge {r : ℕ} (hr : 35 ≤ r) : 0.28668 ≤ hp1P1Short r := by
  have h35 : hp1P1Short 35 = 0.28668 := by
    norm_num [hp1P1Short, hp1RungShort, hp1P1ShortRung]
  exact h35.symm.trans_le (monotone_hp1P1Short hr)

/-- HP1's certified constant is positive on tubes of `r ≥ 35` blocks. -/
lemma hp1P1Short_pos {r : ℕ} (hr : 35 ≤ r) : 0 < hp1P1Short r :=
  lt_of_lt_of_le (by norm_num) (hp1P1Short_ge hr)

/-- HP1's certified constant is nonnegative (`0` below `35`). -/
lemma hp1P1Short_nonneg (r : ℕ) : 0 ≤ hp1P1Short r := by
  rcases lt_or_ge r 35 with h | h
  · have h0 : hp1P1Short r = 0 := by
      unfold hp1P1Short
      rw [if_neg (by omega)]
    exact h0.symm.le
  · exact (hp1P1Short_pos h).le

/-- **The per-scale constant on short tubes** at the producers' numerals, ladder length `K` and
tube length `r`: `Γ(q, K, r) = c₃^{2-q}C₂^{-(1-q)}2^{-q}((1 - e^{-100})P₁(r))^{2-q}Q(r)^{-(1-q)}`
with `c₃ = c3FloorK q K`, `C₂ = e^{2(1-q)+0.50001}`, `P₁(r) = RMF.hp1P1Short r` and
`Q(r) = RMF.hp2QShort r`. -/
noncomputable def perScaleConstShort (q : ℝ) (K r : ℕ) : ℝ :=
  c3FloorK q K ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
    * ((1 - Real.exp (-100)) * hp1P1Short r) ^ (2 - q) * hp2QShort r ^ (-(1 - q))

/-- `RMF.perScaleConstShort q K r ≥ 0` for `0 ≤ q ≤ 11/20`. -/
lemma perScaleConstShort_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11 / 20) (K r : ℕ) :
    0 ≤ perScaleConstShort q K r := by
  have hc3 := c3FloorK_pos hq0 hq1 K
  have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
  have hP₁ := hp1P1Short_nonneg r
  have hQ := hp2QShort_pos r
  unfold perScaleConstShort
  positivity

/-- **`RMF.perScaleConstShort` is nondecreasing in the tube's length** for `0 ≤ q ≤ 11/20`: `P₁`
is nondecreasing (`RMF.monotone_hp1P1Short`), `Q` nonincreasing (`RMF.antitone_hp2QShort`), and
below `35` the constant is `0`. -/
theorem monotone_perScaleConstShort {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 11 / 20) (K : ℕ) :
    Monotone (perScaleConstShort q K) := by
  intro a b hab
  rcases lt_or_ge a 35 with ha | ha
  · -- below `35`, `P₁(a) = 0`
    have h0 : hp1P1Short a = 0 := by
      unfold hp1P1Short
      rw [if_neg (by omega)]
    have hne : (2 : ℝ) - q ≠ 0 := (sub_pos.2 (by linarith)).ne'
    have hz : perScaleConstShort q K a = 0 := by
      simp only [perScaleConstShort, h0, mul_zero, Real.zero_rpow hne, zero_mul]
    rw [hz]
    exact perScaleConstShort_nonneg hq0 hq1 K b
  · have hc3 := c3FloorK_pos hq0 hq1 K
    have hP : 0 < 1 - Real.exp (-100) := by linarith [exp_neg_hundred_le_half]
    have hPa := hp1P1Short_pos ha
    have hPb := hp1P1Short_pos (ha.trans hab)
    have hQa := hp2QShort_pos a
    have hQb := hp2QShort_pos b
    have h1 : ((1 - Real.exp (-100)) * hp1P1Short a) ^ (2 - q)
        ≤ ((1 - Real.exp (-100)) * hp1P1Short b) ^ (2 - q) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_left (monotone_hp1P1Short hab) hP.le) (by linarith)
    have h2 : hp2QShort a ^ (-(1 - q)) ≤ hp2QShort b ^ (-(1 - q)) :=
      Real.rpow_le_rpow_of_nonpos hQb (antitone_hp2QShort hab) (by linarith)
    have hA : 0 ≤ c3FloorK q K ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q))
        * 2 ^ (-q) := by positivity
    unfold perScaleConstShort
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (by positivity) (by positivity)

/-! ### The per-scale value with the producers on short tubes -/

section Numerals

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The per-scale value on short tubes with every producer plugged in**: for `k₀ ≥ 20`,
`k₀ < k`, `0 < q ≤ ½ + 1/20` (and `k - k₀ ≤ K_max(q)` below `½`), tubes of `r ≥ 35` blocks
maximal for the damping `σe^{k+r} ≤ 1/200 < σe^{k+r+1}` and the cutoff `y ≥ c_{k+r}`:
`E[1_{E(k)}mass_k^q] ≥ c₃^{2-q}C₂^{-(1-q)}2^{-q}((1 - e^{-100})P₁(r))^{2-q}Q(r)^{-(1-q)}·N_q(k)·
(E‖F_{[c_k,y)}(s_σ)‖²e^k/√r)^q` with `c₃ = c3FloorK q (k - k₀)`, `C₂ = e^{2(1-q)+0.50001}`,
`P₁ = RMF.hp1P1Short`, `Q = RMF.hp2QShort` (`RMF.le_integral_indicator_rpow_headWindowMass_numeral`
with HP1 on short tubes and HP2 per tube length). -/
theorem le_integral_indicator_rpow_headWindowMass_short (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 ≤ σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {k₀ k r y : ℕ}
    (hk₀ : 20 ≤ k₀) (hk : k₀ < k) (hK : q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    (hσr : σ * Real.exp ((k : ℝ) + r) ≤ 1 / 200)
    (hσr' : 1 / 200 < σ * Real.exp ((k : ℝ) + r + 1))
    (hyr : ⌊blockScale k r⌋₊ + 1 ≤ y) (hr : 35 ≤ r) :
    c3FloorK q (k - k₀) ^ (2 - q) * Real.exp (2 * (1 - q) + 0.50001) ^ (-(1 - q)) * 2 ^ (-q)
        * ((1 - Real.exp (-100)) * hp1P1Short r) ^ (2 - q) * hp2QShort r ^ (-(1 - q))
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ) / √(r : ℝ)) ^ q
      ≤ ∫ ω, (halfLadder X σ k₀ k ∩ hp1After X σ k r).indicator
          (fun ω => headWindowMass X μ σ k r y ω ^ q) ω ∂μ := by
  have hk20 : 20 ≤ k := by omega
  have hy := primeBlockSub_subset_of_cut_le hyr
  have hση : σ * Real.exp k ≤ 1 / 200 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (by linarith [Nat.cast_nonneg (α := ℝ) r])) hσ) hσr
  refine le_integral_indicator_rpow_headWindowMass hX hσ hq0 (by linarith) hk.le (by omega) hyr
    (c3FloorK_pos hq0.le (by linarith) _) (Real.exp_pos _) (hp1P1Short_pos hr) (hp2QShort_pos r)
    ?_ ?_ ?_ ?_
  · intro h hh
    exact le_setIntegral_halfLadder_twistQ_c3FloorK hX (Nat.zero_le _) hk₀ hk hσ hση hq0.le hq1
      hK hh
  · exact le_integral_hp1Tube_inter_hp1After_window_short hX hk20 hσ hσr hy hr
  · intro h₁ hh₁ h₂ hh₂
    exact integral_twistQ_pair_le_sharp hX hk20 hσ hq0.le (by linarith)
      (le_trans (Real.exp_pos _).le hh₁.1) hh₁.2 (le_trans (Real.exp_pos _).le hh₂.1) hh₂.2
  · exact integral_integral_pair_rest_le_short hX hk20 hσr hσr' hyr hr

end Numerals

/-! ### The main term on short tubes -/

section MainTerm

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The sum over scales on short tubes with every producer plugged in**: for `0 < q ≤ ½ + 1/20`,
the ladder bottom `k₀ ≥ 20`, `T` maximal for the damping (`σe^T ≤ 1/200 < σe^{T+1}`), the cutoff
`y ≥ c_{T+7}`, scales `k ∈ K` in `(k₀, T - 35]` (and `k - k₀ ≤ K_max(q)` below `½`), and the
maximal block counts `r = T - k`, with the Rademacher symmetry:
`2^{2q-1}∑_{k ∈ K} Γ(q, k - k₀, T - k)·N_q(k)·(E‖F_{[c_k,y)}(s_σ)‖²e^k/√(T - k))^q
  ≤ E[(∫_ℝ ‖F_{[0,y)}(½+σ+it)/(σ+it)‖² dt)^q]`, `Γ = RMF.perScaleConstShort`. -/
theorem le_integral_rpow_integral_lineDiv_short (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 35 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q) :
    2 ^ (2 * q - 1) * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q
      ≤ ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) y
          (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  have hy3 : 3 ≤ y := by
    have h5 : 5 ≤ scaleCut ((T : ℝ) + 7) :=
      five_le_scaleCut (by linarith [Nat.cast_nonneg (α := ℝ) T])
    omega
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  refine le_integral_rpow_integral_lineDiv_head_symm hX hσ hy3 hq0.le (by linarith) (k₀ := k₀)
    (r := fun k => T - k) (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.2.2.2.2)
    (fun k hk => (hK k hk).1.le) (fun k₁ _ k₂ hk₂ _ => by have := hkT k₂ hk₂; omega)
    (fun k hk => (scale_data_of_le hσ hσT hσT' hyT (hkT k hk)).2.2.1) fun k hk => ?_
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
  exact le_integral_indicator_rpow_headWindowMass_short hX hσ.le hq0 hq1 hk₀ (hK k hk).1
    (hKq k hk) h1 h2 h3 (by have := (hK k hk).2; omega)

/-- **The main term on short tubes with `E‖F_high‖²e^k` explicit**: under the hypotheses of
`RMF.le_integral_rpow_integral_lineDiv_short` and `σL = V` (`L = log x`, `σ = V/log x`),
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀, T - k)·N_q(k)·(T - k)^{-q/2}
  ≤ L^{-q}E[(∫_ℝ ‖F_{[0,y)}(½+σ+it)/(σ+it)‖² dt)^q]`, `G = e^{-0.592}/2`
(`RMF.le_integral_normSq_high_mul_exp`), `Γ = RMF.perScaleConstShort`. -/
theorem le_rpow_mul_integral_rpow_integral_lineDiv_short (hX : IsRademacherPrimeValues X μ)
    {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2 + 1 / 20) {T k₀ y : ℕ}
    {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 35 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          y (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  have hkT : ∀ k ∈ K, k ≤ T := fun k hk => by have := (hK k hk).2; omega
  have hmain := le_integral_rpow_integral_lineDiv_short hX hσ hq0 hq1 hk₀ hσT hσT' hyT hK hKq
  have hV : 0 < V := by rw [← hσV]; positivity
  set G : ℝ := Real.exp (-0.592) / 2 with hG
  have hG0 : 0 < G := by positivity
  have hLq : 0 < L ^ (-q) := Real.rpow_pos_of_pos hL _
  -- per scale: `(E‖F_high‖²e^k/√r)^q ≥ (G/σ)^q r^{-q/2}`
  have hper : ∀ k ∈ K, (G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    intro k hk
    obtain ⟨-, -, -, h4, h5, h6, -⟩ := scale_data_of_le hσ hσT hσT' hyT (hkT k hk)
    have hk20 : 20 ≤ k := by have := (hK k hk).1; omega
    have hE := le_integral_normSq_high_mul_exp hX hσ hk20 h4 h5 h6
    have hr0 : (0 : ℝ) < ((T - k : ℕ) : ℝ) := by
      have := (hK k hk).2
      exact_mod_cast (by omega : 0 < T - k)
    have hsq : 0 < √((T - k : ℕ) : ℝ) := Real.sqrt_pos.2 hr0
    have hG2 : G / σ = Real.exp (-0.592) / (2 * σ) := by rw [hG]; field_simp
    have hmono : G / σ / √((T - k : ℕ) : ℝ)
        ≤ (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by rw [hG2]; exact hE) hsq.le
    have hrpow := Real.rpow_le_rpow (by positivity) hmono hq0.le
    refine le_trans (le_of_eq ?_) hrpow
    rw [Real.div_rpow (by positivity) hsq.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le,
      Real.rpow_neg hr0.le, div_eq_mul_inv]
    congr 2
    ring_nf
  have hN0 : ∀ k ∈ K, 0 ≤ perScaleConstShort q (k - k₀) (T - k)
      * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ) := fun k _ =>
    mul_nonneg (perScaleConstShort_nonneg hq0.le (by linarith) _ _)
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
  have hsum : (G / σ) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    calc (G / σ) ^ q * (perScaleConstShort q (k - k₀) (T - k)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))
        = perScaleConstShort q (k - k₀) (T - k)
            * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
            * ((G / σ) ^ q * ((T - k : ℕ) : ℝ) ^ (-(q / 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hper k hk) (hN0 k hk)
  have hGV : L ^ (-q) * (G / σ) ^ q = (G / V) ^ q := by
    rw [← hσV, Real.rpow_neg hL.le, ← Real.inv_rpow hL.le,
      ← Real.mul_rpow (inv_nonneg.2 hL.le) (by positivity)]
    congr 1
    field_simp
  have h2 : (0 : ℝ) < 2 ^ (2 * q - 1) := by positivity
  calc 2 ^ (2 * q - 1) * (G / V) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      = L ^ (-q) * (2 ^ (2 * q - 1) * ((G / σ) ^ q * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2)))) := by
        rw [← hGV]; ring
    _ ≤ L ^ (-q) * (2 ^ (2 * q - 1) * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) 0
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            (scaleCut (k : ℝ)) y (shiftLine σ 0) ω‖ ^ 2 ∂μ) * Real.exp (k : ℝ)
          / √((T - k : ℕ) : ℝ)) ^ q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum h2.le) hLq.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain hLq.le

/-- **The main term on short tubes, fully explicit, `0 < q ≤ ½`**: `N_q(k) ≥ exp(-q(1-2q)(k + 0.7866
+ 9.003e^{-k}))` (`RMF.le_integral_rpow_norm_low`) in
`RMF.le_rpow_mul_integral_rpow_integral_lineDiv_short`:
`2^{2q-1}(G/V)^q∑_{k ∈ K} Γ(q, k - k₀, T - k)e^{-q(1-2q)(k + 0.7866 + 9.003e^{-k})}(T - k)^{-q/2}
  ≤ L^{-q}E[(∫_ℝ ‖F_{[0,y)}(½+σ+it)/(σ+it)‖² dt)^q]`, `G = e^{-0.592}/2`,
`Γ = RMF.perScaleConstShort`. -/
theorem le_rpow_mul_integral_rpow_integral_lineDiv_explicit_short
    (hX : IsRademacherPrimeValues X μ) {σ q : ℝ} (hσ : 0 < σ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    {T k₀ y : ℕ} {K : Finset ℕ} (hk₀ : 20 ≤ k₀) (hσT : σ * Real.exp (T : ℝ) ≤ 1 / 200)
    (hσT' : 1 / 200 < σ * Real.exp ((T : ℝ) + 1)) (hyT : scaleCut ((T : ℝ) + 7) ≤ y)
    (hK : ∀ k ∈ K, k₀ < k ∧ k + 35 ≤ T) (hKq : ∀ k ∈ K, q < 1 / 2 → k - k₀ ≤ c3Kmax q)
    {L V : ℝ} (hL : 0 < L) (hσV : σ * L = V) :
    2 ^ (2 * q - 1) * (Real.exp (-0.592) / 2 / V) ^ q
        * ∑ k ∈ K, perScaleConstShort q (k - k₀) (T - k)
        * Real.exp (-(q * (1 - 2 * q)) * ((k : ℝ) + 0.7866 + 9.003 / Real.exp (k : ℝ)))
        * ((T - k : ℕ) : ℝ) ^ (-(q / 2))
      ≤ L ^ (-q) * ∫ ω, (∫ u : ℝ, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
          y (shiftLine σ u) ω / ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ := by
  refine le_trans ?_ (le_rpow_mul_integral_rpow_integral_lineDiv_short hX hσ hq0
    (by linarith) hk₀ hσT hσT' hyT hK hKq hL hσV)
  have hV : 0 < V := by rw [← hσV]; positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by positivity)
  have hΓ := perScaleConstShort_nonneg hq0.le (by linarith) (k - k₀) (T - k)
  have hN := le_integral_rpow_norm_low (X := X) (μ := μ) hX hσ.le hq0.le hq1 k
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hΓ) ?_
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end MainTerm

end RMF
