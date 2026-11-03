/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.C3Explicit

/-!
# (C3)*: the ladder of length one, without the Ville factor

For a ladder of length `K = k - k₁ = 1` the event `halfLadder X σ k₁ (k₁ + 1)` is `{Y₀ > 0}` for
the top block `Y₀` alone, so its twisted probability needs no Ville factor: the top step's
comparison (`RMF.le_setIntegral_ladderEvent_one` at `F = 0`) gives
`P_tw(L) ≥ Φ((μ₀ - δ)/√V₀) - lindebergErr δ 0 0` directly (`RMF.le_measureReal_halfLadder_one`).

* **The skeleton with any probability** (`RMF.le_setIntegral_halfLadder_twistQ_of_le_twistMeasure`):
  the factorisation of the head and the ladder, with `P_tw(L)` bounded below by any `c`.
* **The constant** `RMF.c3ValOne q_lo η ϑ_lo δ`: the top step's Gaussian probability at the cell's
  worst corner, `min_V Φ((topMuLo q_lo η ϑ_lo - δ)/√V)`, less the Lindeberg error.  Only the lower
  ends `q_lo`, `ϑ_lo` enter: the second term of `RMF.c3Val` is gone.
* **(C3)* for the ladder of length one** (`RMF.le_setIntegral_halfLadder_twistQ_one`).
-/

open MeasureTheory ProbabilityTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **(C3)*, the skeleton with any lower bound on the ladder probability**: for `q ≤ 1`,
`σ ≥ 0`, `a ≤ scaleCut k₁`, `k₁ ≤ k`, any `h` and any `c ≤ P_tw(halfLadder X σ k₁ k)`
(`P_tw` the twisted tilt over `[scaleCut k₁, scaleCut k)`):
`c·E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(σ+ih)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`
(the proof of `RMF.le_setIntegral_halfLadder_twistQ_ville` with the Ville bound replaced by `c`). -/
theorem le_setIntegral_halfLadder_twistQ_of_le_twistMeasure (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk : k₁ ≤ k) {σ h q : ℝ} (hσ : 0 ≤ σ)
    (hq1 : q ≤ 1) {c : ℝ}
    (hc : c ≤ (twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q).real
      (halfLadder X σ k₁ k)) :
    c * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
        (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  classical
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hc1k : scaleCut (k₁ : ℝ) ≤ scaleCut (k : ℝ) := scaleCut_mono (by exact_mod_cast hk)
  -- the integrand splits at the cut
  have hpt : ∀ ω : Ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            a (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            a (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2)
        = twistPolyQ q (primesIco a (scaleCut (k₁ : ℝ))) σ h (fun p => X (p : ℕ) ω)
          * twistPolyQ q (primesIco (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ))) σ h
              (fun p => X (p : ℕ) ω) := by
    intro ω
    rw [twistPolyQ_primesIco, twistPolyQ_primesIco,
      ← randomEulerProductIco_mul _ ha hc1k (shiftLine σ h),
      ← randomEulerProductIco_mul _ ha hc1k (shiftLine σ 0), norm_mul, norm_mul, mul_pow,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    ring
  have hsplit := setIntegral_mul_split_primeAlgebra (X := X) hX (A := (Set.univ : Set Ω))
    (B := halfLadder X σ k₁ k) MeasurableSet.univ
    (measurableSet_primeAlgebra_halfLadder σ hk le_rfl)
    (measurable_twistPolyQ q (primesIco a (scaleCut (k₁ : ℝ))) σ h)
    (measurable_twistPolyQ q (primesIco (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ))) σ h)
  rw [Set.univ_inter, setIntegral_univ] at hsplit
  rw [mul_comm c, setIntegral_congr_fun (measurableSet_halfLadder hX σ k₁ k) (fun ω _ => hpt ω),
    hsplit]
  simp only [twistPolyQ_primesIco]
  -- the ladder part is `Z·P_tw(L)`, and the moment splits at the cut
  rw [setIntegral_twistQ_eq_mul_twistMeasure hX (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) hσ h q
      (measurableSet_halfLadder hX σ k₁ k),
    integral_rpow_norm_randomEulerProductIco_split hX ha hc1k (shiftLine σ 0) (2 * q)]
  -- the head and `Z` against the moments
  have hhead := integral_rpow_norm_randomEulerProductIco_le_twistQ hX a (scaleCut (k₁ : ℝ))
    (h := h) hσ hq1 (μ := μ)
  have hZ := integral_rpow_norm_randomEulerProductIco_le_twistQ hX (scaleCut (k₁ : ℝ))
    (scaleCut (k : ℝ)) (h := h) hσ hq1 (μ := μ)
  have hkey : ∀ {Eh El V p Wh Wl : ℝ}, 0 ≤ Eh → 0 ≤ El → 0 ≤ p → Eh ≤ Wh → El ≤ Wl → V ≤ p →
      Eh * El * V ≤ Wh * (Wl * p) := by
    intro Eh El V p Wh Wl h1 h2 h3 h4 h5 h6
    calc Eh * El * V ≤ Eh * El * p := mul_le_mul_of_nonneg_left h6 (mul_nonneg h1 h2)
      _ ≤ Wh * Wl * p := mul_le_mul_of_nonneg_right (mul_le_mul h4 h5 h2 (h1.trans h4)) h3
      _ = Wh * (Wl * p) := mul_assoc _ _ _
  exact hkey (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) measureReal_nonneg hhead hZ hc

/-- **The ladder of length one, compared** (no Ville factor): for `k - k₁ = 1`, `k₁ ≥ 20`,
`σ ≥ 0`, `δ > 0` and `V₀ = Var_tw Y₀ > 0`, with `μ₀ = E_tw Y₀` the exact twisted moments of the
top block: `Φ((μ₀ - δ)/√V₀) - lindebergErr δ 0 0 ≤ P_tw(halfLadder X σ k₁ k)`
(`RMF.le_setIntegral_ladderEvent_one` at `F = 0`). -/
theorem le_measureReal_halfLadder_one (hX : IsRademacherPrimeValues X μ) {k₁ k : ℕ}
    (hk₁ : 20 ≤ k₁) (hK : k - k₁ = 1) {σ : ℝ} (hσ : 0 ≤ σ) (h q : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hV : 0 < twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)) :
    normCDF ((twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
          - δ) / √(twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁
            (k - k₁ - 1)))
        - lindebergErr δ 0 0
      ≤ (twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q).real
          (halfLadder X σ k₁ k) := by
  have h1 := le_setIntegral_ladderEvent_one hX hk₁ (by omega : k₁ < k) hσ h q (t := 0)
    (F := 0) le_rfl hδ le_rfl hV
  simp only [zero_mul, sub_zero, setIntegral_const, smul_eq_mul, mul_one] at h1
  have hL : halfLadder X σ k₁ k = ladderEvent (halfLadderStep X σ k₁ k) 1 := by
    rw [halfLadder_eq_ladderEvent, hK]
  rw [hL]
  exact h1

/-- **`c₃` for the ladder of length one** (no Ville factor): the top step's Gaussian
probability at the cell's worst corner, `min_V Φ((μ_lo - δ)/√V)`, less the Lindeberg error;
`μ_lo = topMuLo q_lo η ϑ_lo`, `V ∈ {topVLo η, topVHi}`. -/
noncomputable def c3ValOne (q_lo η ϑ_lo δ : ℝ) : ℝ :=
  min (normCDF ((topMuLo q_lo η ϑ_lo - δ) / √(topVLo η)))
      (normCDF ((topMuLo q_lo η ϑ_lo - δ) / √topVHi))
    - lindebergErr δ 0 0

/-- **(C3)* for the ladder of length one, explicit.**  For `k - k₁ = 1`, `k₁ ≥ 20`,
`a ≤ scaleCut k₁`, `σ ≥ 0`, `σe^k ≤ η ≤ 1`, `0 ≤ q_lo ≤ q ≤ 1`, `δ > 0` and a height
`e^{-(k+ϑ_hi)} ≤ h ≤ e^{-(k+ϑ_lo)}`, `ϑ_lo ≥ 0`:
`c3ValOne·E‖F_{[a,k)}(σ)‖^{2q}
  ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_one (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hK : k - k₁ = 1) {σ η : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ η) (hη : η ≤ 1) {q q_lo : ℝ} (hqlo : q_lo ≤ q)
    (hq0 : 0 ≤ q_lo) (hq1 : q ≤ 1) {δ : ℝ} (hδ : 0 < δ) {h ϑ_lo ϑ_hi : ℝ} (hϑ : 0 ≤ ϑ_lo)
    (hh1 : Real.exp (-((k : ℝ) + ϑ_hi)) ≤ h) (hh2 : h ≤ Real.exp (-((k : ℝ) + ϑ_lo))) :
    c3ValOne q_lo η ϑ_lo δ
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  obtain ⟨hμ1, -, hV1, hV2⟩ := topBlock_moments_mem hX hk₁ (by omega : k₁ < k) hσ hση hqlo
    le_rfl hq0 hq1 hϑ hh1 hh2
  set μ₀ := twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
  set V₀ := twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
  have hVlo := topVLo_pos hη
  have hV0 : 0 < V₀ := hVlo.trans_le hV1
  have hs0 : 0 < √V₀ := Real.sqrt_pos.2 hV0
  obtain ⟨hA, -⟩ := normCDF_div_sqrt_bounds (x := topMuLo q_lo η ϑ_lo - δ) hVlo hV1 hV2
  have h1 : normCDF ((topMuLo q_lo η ϑ_lo - δ) / √V₀) ≤ normCDF ((μ₀ - δ) / √V₀) :=
    normCDF_mono (div_le_div_of_nonneg_right (by linarith) hs0.le)
  have htop := le_measureReal_halfLadder_one hX hk₁ hK hσ h q hδ hV0
  refine le_setIntegral_halfLadder_twistQ_of_le_twistMeasure hX ha (by omega) hσ hq1 ?_
  rw [c3ValOne]
  linarith

end RMF
