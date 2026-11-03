/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.SharpLevels
import RMF.Analysis.HierarchyScales
import RMF.Analysis.LogHierarchy
import RMF.Weighted.FixedQUniformExplicit
import RMF.Weighted.CoordinateMoments

/-!
# The sharp bound above `q = 1/2`

For `½ < q ≤ 1` there are `C` and `x₀`, independent of the probability space, `q` and `x`, such
that

`E|S(x)|^{2q} ≤ C·(log x)^{q(2q-1)}·b(m)`,  `m = min{1/(2q-1), log log x}`,

for every Rademacher `X`, every `½ < q ≤ 1` and every `x ≥ x₀`
(`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp`), and so for every `x ≥ e^e`
(`RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp_of_exp_exp_le`): below `x₀`
the second moment gives `E|S(x)|^{2q} ≤ 2 + log x`, while `b(m) ≥ ½` and
`(log x)^{q(2q-1)} ≥ 1`.  `q = ½` is not covered; its order is
`RMF.exists_integral_weightedRademacherSum_asymp_half`.

The proof is a sum over levels.  The layered identity in `L^{2q}`
(`RMF.rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered`) at the scales of
`RMF/Analysis/HierarchyScales.lean`, taken top-down (`Y k = z_{L+1-k}`), bounds `‖S(x)‖_{2q}` by
the levels of `RMF/Weighted/SharpLevels.lean`.  With `G = (log x)^{(2q-1)/2}·b(m)^{1/(2q)}`:

* the top level is `≪ (log x)^{(2q-1)/2}·(6e²)^{1/2} ≤ 2(6e²)^{1/2}·G`, since `b(m) ≥ ½`;
* the level at `z_{ℓ-1} < z_ℓ`, with `t = log_ℓ Λ`, is `≪ G·t^{-(2q-1)/2}·(m_ℓ/m)^{1/4}`, by
  `log z_ℓ ≤ log x/(3t)` (`RMF.rpow_le_rpow_mul_rpow_neg_of_le_div`) and the ratio bound for `b`
  (`RMF.ballotFactor_rpow_inv_le`); and
  `t^{-(2q-1)/2}·(m_ℓ/m)^{1/4} ≤ (t/Λ)^{1/4} + t^{-(2q-1)/2}·min{1, (2q-1)t}^{1/4}`
  (`RMF.rpow_neg_mul_min_div_min_rpow_le`), whose sums over `ℓ` are
  `RMF.sum_iterLog_div_quarter_le` and `RMF.sum_iterLog_damped_le`;
* the bottom level is `≪ G`, `b` being increasing.

So `‖S(x)‖_{2q} ≤ K·G` with `K` absolute, and the power `2q` gives the theorem
(`RMF.le_max_one_sq_mul_of_rpow_inv_le`), on the coordinate model; the moment transfer
`RMF.IsIIDPrimeValues.integral_rpow_weightedRademacherSum_squarefreeExtension_eq` carries it to
every probability space.
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A level's share of the sum over the levels.**  For `0 < δ ≤ 1` and `1 ≤ l ≤ t ≤ Λ`, with
`m' = min{1/δ, l}` and `m = min{1/δ, Λ}`,

`t^{-δ/2}·(m'/m)^{1/4} ≤ (t/Λ)^{1/4} + t^{-δ/2}·min{1, δt}^{1/4}`:

if `m = Λ` then `m'/m ≤ t/Λ` and `t^{-δ/2} ≤ 1`; if `m = 1/δ` then `m'/m = δm' ≤ min{1, δt}`. -/
lemma rpow_neg_mul_min_div_min_rpow_le {δ t Λ l : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht1 : 1 ≤ t)
    (htΛ : t ≤ Λ) (hl1 : 1 ≤ l) (hlt : l ≤ t) :
    t ^ (-(δ / 2)) * (min δ⁻¹ l / min δ⁻¹ Λ) ^ (1 / 4 : ℝ)
      ≤ (t / Λ) ^ (1 / 4 : ℝ) + t ^ (-(δ / 2)) * min 1 (δ * t) ^ (1 / 4 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).2 hδ1
  have ha0 : 0 ≤ t ^ (-(δ / 2)) := Real.rpow_nonneg ht0.le _
  have ha1 : t ^ (-(δ / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
  have hm'0 : 0 ≤ min δ⁻¹ l := le_min (by linarith) (by linarith)
  have hs1 : 0 ≤ (t / Λ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (div_nonneg ht0.le hΛ0.le) _
  have hs2 : 0 ≤ t ^ (-(δ / 2)) * min 1 (δ * t) ^ (1 / 4 : ℝ) :=
    mul_nonneg ha0 (Real.rpow_nonneg (le_min zero_le_one (mul_nonneg hδ0.le ht0.le)) _)
  rcases le_total Λ δ⁻¹ with h | h
  · rw [min_eq_right h]
    have hr : min δ⁻¹ l / Λ ≤ t / Λ :=
      div_le_div_of_nonneg_right (le_trans (min_le_right _ _) hlt) hΛ0.le
    have hr' := Real.rpow_le_rpow (div_nonneg hm'0 hΛ0.le) hr (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc t ^ (-(δ / 2)) * (min δ⁻¹ l / Λ) ^ (1 / 4 : ℝ) ≤ 1 * (t / Λ) ^ (1 / 4 : ℝ) :=
          mul_le_mul ha1 hr' (Real.rpow_nonneg (div_nonneg hm'0 hΛ0.le) _) zero_le_one
      _ ≤ (t / Λ) ^ (1 / 4 : ℝ) + t ^ (-(δ / 2)) * min 1 (δ * t) ^ (1 / 4 : ℝ) := by linarith
  · rw [min_eq_left h, div_inv_eq_mul]
    have hr : min δ⁻¹ l * δ ≤ min 1 (δ * t) := by
      refine le_min ?_ ?_
      · calc min δ⁻¹ l * δ ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_right (min_le_left _ _) hδ0.le
          _ = 1 := inv_mul_cancel₀ hδ0.ne'
      · calc min δ⁻¹ l * δ ≤ t * δ :=
            mul_le_mul_of_nonneg_right (le_trans (min_le_right _ _) hlt) hδ0.le
          _ = δ * t := mul_comm _ _
    have hr' := Real.rpow_le_rpow (mul_nonneg hm'0 hδ0.le) hr (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc t ^ (-(δ / 2)) * (min δ⁻¹ l * δ) ^ (1 / 4 : ℝ)
        ≤ t ^ (-(δ / 2)) * min 1 (δ * t) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hr' ha0
      _ ≤ (t / Λ) ^ (1 / 4 : ℝ) + t ^ (-(δ / 2)) * min 1 (δ * t) ^ (1 / 4 : ℝ) := by linarith

/-- **A level's power of `log`, normalised.**  For `δ ≥ 0`, `t ≥ 1` and `0 ≤ a ≤ c/(3t)`,
`a^{δ/2} ≤ c^{δ/2}·t^{-δ/2}`. -/
lemma rpow_le_rpow_mul_rpow_neg_of_le_div {δ t a c : ℝ} (hδ : 0 ≤ δ) (ht : 1 ≤ t) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (h : a ≤ c / (3 * t)) : a ^ (δ / 2) ≤ c ^ (δ / 2) * t ^ (-(δ / 2)) := by
  have ht0 : 0 < t := by linarith
  have h3t : (0 : ℝ) ≤ 3 * t := by linarith
  calc a ^ (δ / 2) ≤ (c / (3 * t)) ^ (δ / 2) := Real.rpow_le_rpow ha h (by linarith)
    _ = c ^ (δ / 2) * (3 * t) ^ (-(δ / 2)) := by
        rw [Real.div_rpow hc h3t, Real.rpow_neg h3t, div_eq_mul_inv]
    _ ≤ c ^ (δ / 2) * t ^ (-(δ / 2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith))
          (Real.rpow_nonneg hc _)

/-- **From the norm to the moment.**  For `½ < q ≤ 1` and nonnegative `E, K, a, b`: if
`E^{1/(2q)} ≤ K·a^{(2q-1)/2}·b^{1/(2q)}`, then `E ≤ max{1, K}²·a^{q(2q-1)}·b`. -/
lemma le_max_one_sq_mul_of_rpow_inv_le {E K a b q : ℝ} (hq2 : 1 / 2 < q) (hq1 : q ≤ 1)
    (hE : 0 ≤ E) (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : E ^ (2 * q)⁻¹ ≤ K * (a ^ ((2 * q - 1) / 2) * b ^ (2 * q)⁻¹)) :
    E ≤ max 1 K ^ 2 * (a ^ (q * (2 * q - 1)) * b) := by
  have h2q : (0 : ℝ) < 2 * q := by linarith
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hE _) h h2q.le
  rw [Real.rpow_inv_rpow hE h2q.ne',
    Real.mul_rpow hK (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)),
    Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _), ← Real.rpow_mul ha,
    ← Real.rpow_mul hb, inv_mul_cancel₀ h2q.ne', Real.rpow_one] at h1
  have hexp : (2 * q - 1) / 2 * (2 * q) = q * (2 * q - 1) := by ring
  rw [hexp] at h1
  have hKmax : K ^ (2 * q) ≤ max 1 K ^ 2 := by
    calc K ^ (2 * q) ≤ max 1 K ^ (2 * q) := Real.rpow_le_rpow hK (le_max_right 1 K) h2q.le
      _ ≤ max 1 K ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left 1 K) (by linarith)
      _ = max 1 K ^ 2 := Real.rpow_two _
  exact le_trans h1 (mul_le_mul_of_nonneg_right hKmax (mul_nonneg (Real.rpow_nonneg ha _) hb))

/-- **The sharp bound above `q = ½`**, for `½ < q ≤ 1`.  There are `C` and `x₀`, independent of
the probability space, `q` and `x`, such that, for every Rademacher `X`, every `½ < q ≤ 1` and
every `x ≥ x₀`,

`E|S(x)|^{2q} ≤ C·(log x)^{q(2q-1)}·b(min{1/(2q-1), log log x})`.

The proof takes `x₀ = e^{576}`, which gives `Λ = log log x ≥ 2` and `12Λ ≤ log x`, the hypotheses
of the scales (`RMF.exists_hierarchyScales`).  The layered identity at the scales taken top-down,
the levels of `RMF/Weighted/SharpLevels.lean`, the ratio bound for `b`
(`RMF.ballotFactor_rpow_inv_le`) and the level sums (`RMF.sum_iterLog_div_quarter_le`,
`RMF.sum_iterLog_damped_le`), then the power `2q`, on the coordinate model;
`RMF.IsIIDPrimeValues.integral_rpow_weightedRademacherSum_squarefreeExtension_eq` carries it to
every space. -/
theorem exists_integral_rpow_norm_weightedRademacherSum_le_sharp :
    ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
      ∀ (q x : ℝ), 1 / 2 < q → q ≤ 1 → x₀ ≤ x →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * (Real.log x ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x)))) := by
  obtain ⟨C, x₀, hC, H⟩ : ∃ C x₀ : ℝ, 0 < C ∧
      ∀ (X : ℕ → (Nat.Primes → ℂ) → ℂ) (μ : Measure (Nat.Primes → ℂ)),
      IsRademacherPrimeValues X μ →
      ∀ (q x : ℝ), 1 / 2 < q → q ≤ 1 → x₀ ≤ x →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * (Real.log x ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x)))) := by
    obtain ⟨A₁, hA₁, hmid⟩ := exists_rpow_inv_mul_rpow_inv_le_band (Ω := Nat.Primes → ℂ)
    obtain ⟨A₀, hA₀, hbot⟩ :=
      exists_rpow_inv_integral_rpow_norm_truncationTail_le (Ω := Nat.Primes → ℂ)
    obtain ⟨K, hK⟩ : ∃ K : ℝ,
        K = 2 * (Real.exp 21 * Real.exp 1.86) * (6 * Real.exp 2) ^ (2 : ℝ)⁻¹
          + A₁ * (8 * Real.exp (1 / 4) + 3) + A₀ := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by
      rw [hK]
      exact add_nonneg (add_nonneg (by positivity) (mul_nonneg hA₁.le (by positivity))) hA₀.le
    refine ⟨max 1 K ^ 2, Real.exp 576, pow_pos (lt_of_lt_of_le one_pos (le_max_left 1 K)) 2, ?_⟩
    intro X μ hX q x hq2 hq1 hx
    -- the range of `x`
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 576) hx
    have hlogx : 576 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
    have hlx0 : 0 ≤ Real.log x := by linarith
    have hΛ2 : 2 ≤ Real.log (Real.log x) := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < Real.log x)]
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have h1 := Real.exp_one_lt_d9
      have h0 := Real.exp_pos 1
      nlinarith [mul_pos h0 (sub_pos.2 h1)]
    have h12 : 12 * Real.log (Real.log x) ≤ Real.log x := by
      have hsq := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith : (0 : ℝ) < Real.log x))
      rw [Real.log_sqrt hlx0] at hsq
      have h24 : (24 : ℝ) ≤ Real.sqrt (Real.log x) := by
        rw [show (24 : ℝ) = Real.sqrt (24 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num; linarith)
      nlinarith [mul_le_mul_of_nonneg_left h24 (Real.sqrt_nonneg (Real.log x)),
        Real.mul_self_sqrt hlx0]
    -- the scales
    obtain ⟨L, z, hgood, hevery, hcons, hbot0, hbotV, hbotΛ, htop⟩ :=
      exists_hierarchyScales hx0 hΛ2 h12
    obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Real.log (Real.log x) := ⟨_, rfl⟩
    rw [← hΛdef] at hgood hevery hcons hbotΛ ⊢
    -- the exponents, and `b(m)`
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (2 * q - 1)⁻¹ Λ := ⟨_, rfl⟩
    rw [← hm]
    have hδ0 : 0 < 2 * q - 1 := by linarith
    have hδ1 : 2 * q - 1 ≤ 1 := by linarith
    have hw0 : 0 < (2 * q)⁻¹ := inv_pos.2 (by linarith)
    have hw1 : (2 * q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hm1 : 1 ≤ m := by
      rw [hm]
      exact le_min ((one_le_inv₀ hδ0).2 hδ1) (by linarith)
    have hb2 := half_le_ballotFactor (by linarith) hq1 hm1
    have hb0 : 0 ≤ ballotFactor q m := le_trans (by norm_num) hb2
    have hbw : (1 / 2 : ℝ) ≤ ballotFactor q m ^ (2 * q)⁻¹ := by
      calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 2) ^ (2 * q)⁻¹ := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hw1
        _ ≤ ballotFactor q m ^ (2 * q)⁻¹ := Real.rpow_le_rpow (by norm_num) hb2 hw0.le
    obtain ⟨G, hG⟩ : ∃ G : ℝ,
        G = Real.log x ^ ((2 * q - 1) / 2) * ballotFactor q m ^ (2 * q)⁻¹ := ⟨_, rfl⟩
    have hG0 : 0 ≤ G := by
      rw [hG]
      exact mul_nonneg (Real.rpow_nonneg hlx0 _) (Real.rpow_nonneg hb0 _)
    -- the layered identity at the scales, top-down
    have hY : ∀ k, 1 ≤ k → k < L + 1 → z (L + 1 - (k + 1)) ≤ z (L + 1 - k) := by
      intro k hk1 hkK
      rw [show L + 1 - (k + 1) = L - k by omega, show L + 1 - k = L - k + 1 by omega]
      exact (hcons (L - k) (by omega)).1
    have hN3 := rpow_inv_integral_rpow_norm_weightedRademacherSum_le_layered hX hq2.le
      (Y := fun k => z (L + 1 - k)) (K := L + 1) (by omega) hY x
    beta_reduce at hN3
    rw [show L + 1 - 1 = L by omega, show L + 1 - (L + 1) = 0 by omega] at hN3
    have hnorm : (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
        ^ (2 * q) ∂μ) ^ (2 * q)⁻¹ ≤ K * G := by
      refine le_trans hN3 ?_
      rw [show K * G = 2 * (Real.exp 21 * Real.exp 1.86) * (6 * Real.exp 2) ^ (2 : ℝ)⁻¹ * G
          + A₁ * (8 * Real.exp (1 / 4) + 3) * G + A₀ * G by rw [hK]; ring]
      refine add_le_add (add_le_add ?_ ?_) ?_
      · -- the top level
        obtain ⟨hz3, hzx, -⟩ := hevery L le_rfl
        have hlz : 0 < Real.log (z L) := Real.log_pos (by exact_mod_cast (by omega : 1 < z L))
        have hc0 : 0 ≤ Real.exp 21 * Real.exp 1.86 := by positivity
        have h60 : 0 ≤ (6 * Real.exp 2) ^ (2 : ℝ)⁻¹ := by positivity
        have h1 : Real.log (z L) ^ ((2 * q - 1) / 2) ≤ Real.log x ^ ((2 * q - 1) / 2) :=
          Real.rpow_le_rpow hlz.le (Real.log_le_log (by exact_mod_cast (by omega : 0 < z L)) hzx)
            (by linarith)
        have h2 : (Real.log x / Real.log (z L)) ^ (2 : ℝ)⁻¹ ≤ (6 * Real.exp 2) ^ (2 : ℝ)⁻¹ :=
          Real.rpow_le_rpow (div_nonneg hlx0 hlz.le) htop (by norm_num)
        refine le_trans (rpow_inv_mul_rpow_inv_le_top hX hq2 hq1 hz3 hzx) ?_
        rw [hG]
        calc Real.exp 21 * Real.exp 1.86
              * (Real.log (z L) ^ ((2 * q - 1) / 2) * (Real.log x / Real.log (z L)) ^ (2 : ℝ)⁻¹)
            ≤ Real.exp 21 * Real.exp 1.86
              * (Real.log x ^ ((2 * q - 1) / 2) * (6 * Real.exp 2) ^ (2 : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h1 h2
                (Real.rpow_nonneg (div_nonneg hlx0 hlz.le) _) (Real.rpow_nonneg hlx0 _)) hc0
          _ ≤ Real.exp 21 * Real.exp 1.86
              * (Real.log x ^ ((2 * q - 1) / 2) * (6 * Real.exp 2) ^ (2 : ℝ)⁻¹)
              * (2 * ballotFactor q m ^ (2 * q)⁻¹) :=
              le_mul_of_one_le_right (mul_nonneg hc0 (mul_nonneg (Real.rpow_nonneg hlx0 _) h60))
                (by linarith)
          _ = 2 * (Real.exp 21 * Real.exp 1.86) * (6 * Real.exp 2) ^ (2 : ℝ)⁻¹
              * (Real.log x ^ ((2 * q - 1) / 2) * ballotFactor q m ^ (2 * q)⁻¹) := by ring
      · -- the middle levels
        obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ, φ = fun ℓ => (iterLog ℓ Λ / Λ) ^ (1 / 4 : ℝ)
            + iterLog ℓ Λ ^ (-((2 * q - 1) / 2))
              * min 1 ((2 * q - 1) * iterLog ℓ Λ) ^ (1 / 4 : ℝ) :=
          ⟨_, rfl⟩
        refine le_trans (Finset.sum_le_sum (g := fun k => A₁ * G * φ (L + 1 - k))
          fun k hk => ?_) ?_
        · -- one level
          rw [Finset.mem_Ico] at hk
          obtain ⟨j, hj⟩ : ∃ j, j = L - k := ⟨_, rfl⟩
          have hjL : j < L := by omega
          rw [show L + 1 - (k + 1) = j by omega, show L + 1 - k = j + 1 by omega]
          obtain ⟨-, hκ, hV, hκt⟩ := hcons j hjL
          obtain ⟨hz3, -, -⟩ := hevery j hjL.le
          obtain ⟨hz3', hzx, hnormz⟩ := hevery (j + 1) hjL
          refine le_trans (hmid X μ hX q (z j) (z (j + 1)) x hq2 hq1 hz3 hκ hzx hV) ?_
          obtain ⟨t, ht⟩ : ∃ t : ℝ, t = iterLog (j + 1) Λ := ⟨_, rfl⟩
          rw [← ht] at hκt hnormz
          have ht1 : 1 ≤ t := by
            rw [ht]
            exact hgood.one_le hjL
          have ht0 : 0 < t := by linarith
          have htΛ : t ≤ Λ := by
            rw [ht]
            simpa using iterLog_le_iterLog (Nat.zero_le (j + 1)) (hgood.mono hjL)
          obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log (Real.log (z (j + 1)) / Real.log (z j)) :=
            ⟨_, rfl⟩
          rw [← hl] at hκt ⊢
          have hl1 : 1 ≤ l := by
            rw [hl]
            have h := Real.log_le_log (Real.exp_pos 1) hκ
            rwa [Real.log_exp] at h
          have hlz : 0 ≤ Real.log (z (j + 1)) :=
            Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z (j + 1)))
          have hm'1 : 1 ≤ min (2 * q - 1)⁻¹ l := le_min ((one_le_inv₀ hδ0).2 hδ1) hl1
          have hb'0 : 0 ≤ ballotFactor q (min (2 * q - 1)⁻¹ l) :=
            le_trans (by norm_num) (half_le_ballotFactor (by linarith) hq1 hm'1)
          have hm'm : min (2 * q - 1)⁻¹ l ≤ m := by
            rw [hm]
            exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans hκt htΛ))
          have hn := rpow_le_rpow_mul_rpow_neg_of_le_div (δ := 2 * q - 1) hδ0.le ht1 hlz hlx0 hnormz
          have hbr := ballotFactor_rpow_inv_le hq2.le hq1 (by linarith) hm'm
          have hper := rpow_neg_mul_min_div_min_rpow_le hδ0 hδ1 ht1 htΛ hl1 hκt
          rw [← hm] at hper
          have hφj : φ (j + 1) = (t / Λ) ^ (1 / 4 : ℝ)
              + t ^ (-((2 * q - 1) / 2)) * min 1 ((2 * q - 1) * t) ^ (1 / 4 : ℝ) := by
            rw [hφ, ht]
          rw [hφj, hG]
          calc A₁ * (Real.log (z (j + 1)) ^ ((2 * q - 1) / 2)
                * ballotFactor q (min (2 * q - 1)⁻¹ l) ^ (2 * q)⁻¹)
              ≤ A₁ * ((Real.log x ^ ((2 * q - 1) / 2) * t ^ (-((2 * q - 1) / 2)))
                * ((min (2 * q - 1)⁻¹ l / m) ^ (1 / 4 : ℝ) * ballotFactor q m ^ (2 * q)⁻¹)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hn hbr (Real.rpow_nonneg hb'0 _)
                (mul_nonneg (Real.rpow_nonneg hlx0 _) (Real.rpow_nonneg ht0.le _))) hA₁.le
            _ = A₁ * (Real.log x ^ ((2 * q - 1) / 2) * ballotFactor q m ^ (2 * q)⁻¹)
                * (t ^ (-((2 * q - 1) / 2)) * (min (2 * q - 1)⁻¹ l / m) ^ (1 / 4 : ℝ)) := by ring
            _ ≤ A₁ * (Real.log x ^ ((2 * q - 1) / 2) * ballotFactor q m ^ (2 * q)⁻¹)
                * ((t / Λ) ^ (1 / 4 : ℝ)
                  + t ^ (-((2 * q - 1) / 2)) * min 1 ((2 * q - 1) * t) ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left hper
                (mul_nonneg hA₁.le (mul_nonneg (Real.rpow_nonneg hlx0 _) (Real.rpow_nonneg hb0 _)))
        · -- the sum over the levels
          rw [← Finset.mul_sum]
          have hreidx : ∑ k ∈ Finset.Ico 1 (L + 1), φ (L + 1 - k) = ∑ ℓ ∈ Finset.Icc 1 L, φ ℓ := by
            refine Finset.sum_nbij' (fun k => L + 1 - k) (fun k => L + 1 - k) ?_ ?_ ?_ ?_ ?_
            · intro a ha
              simp only [Finset.mem_Ico, Finset.mem_Icc] at ha ⊢
              omega
            · intro a ha
              simp only [Finset.mem_Ico, Finset.mem_Icc] at ha ⊢
              omega
            · intro a ha
              simp only [Finset.mem_Ico] at ha
              omega
            · intro a ha
              simp only [Finset.mem_Icc] at ha
              omega
            · intro a _
              rfl
          have hsum : ∑ ℓ ∈ Finset.Icc 1 L, φ ℓ ≤ 8 * Real.exp (1 / 4) + 3 := by
            rw [hφ, Finset.sum_add_distrib]
            linarith [sum_iterLog_div_quarter_le hgood, sum_iterLog_damped_le hgood hδ0]
          rw [hreidx]
          calc A₁ * G * ∑ ℓ ∈ Finset.Icc 1 L, φ ℓ ≤ A₁ * G * (8 * Real.exp (1 / 4) + 3) :=
                mul_le_mul_of_nonneg_left hsum (mul_nonneg hA₁.le hG0)
            _ = A₁ * (8 * Real.exp (1 / 4) + 3) * G := by ring
      · -- the bottom level
        obtain ⟨hz03, hzx0, -⟩ := hevery 0 (Nat.zero_le L)
        refine le_trans (hbot X μ hX q (z 0) x hq2 hq1 hbot0 hzx0 hbotV) ?_
        have hlz0 : 0 < Real.log (z 0) := lt_of_lt_of_le (Real.exp_pos 1) hbot0
        have hll1 : 1 ≤ Real.log (Real.log (z 0)) := by
          have h := Real.log_le_log (Real.exp_pos 1) hbot0
          rwa [Real.log_exp] at h
        have hm01 : 1 ≤ min (2 * q - 1)⁻¹ (Real.log (Real.log (z 0))) :=
          le_min ((one_le_inv₀ hδ0).2 hδ1) hll1
        have hm0m : min (2 * q - 1)⁻¹ (Real.log (Real.log (z 0))) ≤ m := by
          rw [hm]
          exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) hbotΛ)
        have hb00 : 0 ≤ ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log (z 0)))) :=
          le_trans (by norm_num) (half_le_ballotFactor (by linarith) hq1 hm01)
        have h1 : Real.log (z 0) ^ ((2 * q - 1) / 2) ≤ Real.log x ^ ((2 * q - 1) / 2) :=
          Real.rpow_le_rpow hlz0.le (Real.log_le_log (by exact_mod_cast (by omega : 0 < z 0)) hzx0)
            (by linarith)
        have h2 : ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log (z 0)))) ^ (2 * q)⁻¹
            ≤ ballotFactor q m ^ (2 * q)⁻¹ :=
          Real.rpow_le_rpow hb00 (ballotFactor_le_ballotFactor (by linarith) hq1 (by linarith) hm0m)
            hw0.le
        rw [hG]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul h1 h2 (Real.rpow_nonneg hb00 _) (Real.rpow_nonneg hlx0 _)) hA₀.le
    rw [hG] at hnorm
    exact le_max_one_sq_mul_of_rpow_inv_le hq2 hq1
      (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) hK0 hlx0 hb0 hnorm
  refine ⟨C, x₀, hC, fun Ω _ X μ hX q x hq2 hq1 hx => ?_⟩
  rw [hX.integral_rpow_weightedRademacherSum_squarefreeExtension_eq]
  exact H _ _ (isIIDPrimeValues_primeExtend rademacherLaw) q x hq2 hq1 hx

/-- **The sharp bound above `q = ½`, for every `x ≥ e^e`.**  There is a `C`, independent of the
probability space, `q` and `x`, such that, for every Rademacher `X`, every `½ < q ≤ 1` and every
`x ≥ e^e`,

`E|S(x)|^{2q} ≤ C·(log x)^{q(2q-1)}·b(min{1/(2q-1), log log x})`.

Above `x₀` this is `RMF.exists_integral_rpow_norm_weightedRademacherSum_le_sharp`.  Below it,
`E|S(x)|^{2q} ≤ 1 + E|S(x)|² ≤ 2 + log x ≤ 2 + |log x₀|` (Jensen, `t^q ≤ 1 + t`, and
`RMF.integral_normSq_weightedRademacherSum_le_one_add_log`), while `x ≥ e^e` gives
`log log x ≥ 1`, so `b(m) ≥ ½`, and `(log x)^{q(2q-1)} ≥ 1`. -/
theorem exists_integral_rpow_norm_weightedRademacherSum_le_sharp_of_exp_exp_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
      ∀ (q x : ℝ), 1 / 2 < q → q ≤ 1 → Real.exp (Real.exp 1) ≤ x →
        (∫ ω, ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ (2 * q) ∂μ)
          ≤ C * (Real.log x ^ (q * (2 * q - 1))
            * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x)))) := by
  obtain ⟨C₀, x₀, hC₀, hlarge⟩ := exists_integral_rpow_norm_weightedRademacherSum_le_sharp
  refine ⟨max C₀ (2 * (2 + |Real.log x₀|)), lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro Ω _ X μ hX q x hq2 hq1 hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (Real.exp_pos 1).le) hx
  have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlx1 : 1 ≤ Real.log x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hlogx
  have hll1 : 1 ≤ Real.log (Real.log x) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlogx
    rwa [Real.log_exp] at h
  have hm1 : 1 ≤ min (2 * q - 1)⁻¹ (Real.log (Real.log x)) :=
    le_min ((one_le_inv₀ (by linarith)).2 (by linarith)) hll1
  have hb2 := half_le_ballotFactor (by linarith) hq1 hm1
  have hL1 : 1 ≤ Real.log x ^ (q * (2 * q - 1)) :=
    Real.one_le_rpow hlx1 (mul_nonneg (by linarith) (by linarith))
  have hR : 1 * (1 / 2) ≤ Real.log x ^ (q * (2 * q - 1))
      * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x))) :=
    mul_le_mul hL1 hb2 (by norm_num) (by linarith)
  rcases le_total x₀ x with h | h
  · -- above `x₀`
    exact le_trans (hlarge Ω X μ hX q x hq2 hq1 h)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · -- below `x₀`: the second moment
    haveI := hX.isProbabilityMeasure
    have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hint : Integrable (fun ω =>
        ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ 2) μ :=
      (integrable_rpow_norm_weightedRademacherSum hX x (by norm_num : (0 : ℝ) ≤ 2)).congr
        (Filter.Eventually.of_forall fun ω => Real.rpow_two _)
    have hB := integral_normSq_weightedRademacherSum_le_one_add_log hRa hx1
    have hpow : ∀ ω,
        ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q)
          = (‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖
            ^ 2) ^ q := by
      intro ω
      rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
    have hcrude : (∫ ω,
        ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖ ^ (2 * q) ∂μ)
        ≤ 1 + (1 + Real.log x) := by
      simp_rw [hpow]
      refine le_trans (integral_rpow_le_rpow_of_integral_le hq0 hq1
        (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint hB) ?_
      exact rpow_le_one_add (by linarith) hq0 hq1
    have hlog : Real.log x ≤ |Real.log x₀| := le_trans (Real.log_le_log hx0 h) (le_abs_self _)
    have hfin : 2 * (2 + |Real.log x₀|) * (1 * (1 / 2))
        ≤ max C₀ (2 * (2 + |Real.log x₀|)) * (Real.log x ^ (q * (2 * q - 1))
          * ballotFactor q (min (2 * q - 1)⁻¹ (Real.log (Real.log x)))) :=
      mul_le_mul (le_max_right _ _) hR (by norm_num) (le_trans (by positivity) (le_max_right _ _))
    linarith

end RMF
