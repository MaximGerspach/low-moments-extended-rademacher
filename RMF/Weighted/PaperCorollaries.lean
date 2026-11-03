/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.ExtendedUniformMomentsExplicit
import RMF.Reduction.RademacherLower

/-!
# The paper's corollaries: tails and limits in probability

Corollaries 1.3 and 1.4 of the paper on the extended and the weighted Rademacher sums, from the
uniform upper bounds (`RMF.extended_rademacher_moments_upper_uniform_explicit`, constant `30`;
`RMF.weighted_rademacher_moments_upper_uniform_explicit`, constant `25`) and Markov's inequality.
Write `Y(x) = x^{-1/2}∑_{n≤x} X^e(n)`, `S(x) = ∑_{n≤x} X(n)/√n` and `Λ = log log x`.

* Corollary 1.3, with explicit constants and for every `x ≥ 3`: for `λ ≥ 3`,
  `P(|Y(x)| > λΛ^{-1/4}) ≤ 30e·min(log λ, Λ)/λ` (`RMF.extended_rademacher_tail_explicit`), and
  the same for `S(x)` with `25e` (`RMF.weighted_rademacher_tail_explicit`).  Markov at
  `q = ½ - 1/(2 log λ)`, where `(1 - 2q)⁻¹ = log λ` and `λ^{2q} = λ/e`.
* Corollary 1.4: as `x → ∞`, in probability, `x^{-1/2}∑_{n≤x, n ≠ □} X^e(n) → -1`
  (`RMF.extended_rademacher_nonsquare_tendstoInMeasure`) and `∑_{1<n≤x} X(n)/√n → -1`
  (`RMF.weighted_rademacher_nonsquare_tendstoInMeasure`).  The squares contribute
  `⌊√x⌋/√x → 1` to `Y(x)`, as `X^e(s²) = 1`, and `n = 1` contributes `1` to `S(x)`; and `Y(x)`,
  `S(x)` tend to `0` in probability, by Markov from `E|Y|^{1/2} ≤ 60Λ^{-1/8}` and
  `E|S|^{1/2} ≤ 50Λ^{-1/8}` (the case `q = ¼`).
-/

open MeasureTheory Filter Topology

namespace RMF

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Markov's inequality for a power of the norm -/

/-- **Markov's inequality** for `‖Z‖^r`: `P(‖Z‖ ≥ t) ≤ E‖Z‖^r/t^r` for `r, t > 0`. -/
lemma measureReal_le_norm_le_integral_rpow_div {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → ℂ}
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hint : Integrable (fun ω => ‖Z ω‖ ^ r) μ) :
    μ.real {ω | t ≤ ‖Z ω‖} ≤ (∫ ω, ‖Z ω‖ ^ r ∂μ) / t ^ r := by
  have htr : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  have hsub : {ω | t ≤ ‖Z ω‖} ⊆ {ω | t ^ r ≤ ‖Z ω‖ ^ r} := fun ω hω =>
    Real.rpow_le_rpow ht.le hω hr.le
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg (Z ω)) r) hint (t ^ r)
  rw [le_div_iff₀ htr]
  calc μ.real {ω | t ≤ ‖Z ω‖} * t ^ r ≤ μ.real {ω | t ^ r ≤ ‖Z ω‖ ^ r} * t ^ r :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) htr.le
    _ = t ^ r * μ.real {ω | t ^ r ≤ ‖Z ω‖ ^ r} := mul_comm _ _
    _ ≤ ∫ ω, ‖Z ω‖ ^ r ∂μ := hmark

/-! ### Corollary 1.3: the tails -/

/-- **The tail bound from the uniform moments** (the proof of Corollary 1.3).  If
`E‖Z‖^{2q} ≤ C·min(Λ, (1 - 2q)⁻¹)·Λ^{-q/2}` for every `0 < q < ½`, then for `λ ≥ 3`,
`P(‖Z‖ > λΛ^{-1/4}) ≤ Ce·min(log λ, Λ)/λ`: Markov at `q = ½ - 1/(2 log λ)`, which lies in
`(0, ½)` as `log λ > 1`, where `(1 - 2q)⁻¹ = log λ` and `(λΛ^{-1/4})^{2q} = (λ/e)Λ^{-q/2}`. -/
lemma measureReal_tail_le_of_moments {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → ℂ}
    {C Λ lam : ℝ} (hΛ : 0 < Λ) (hlam : 3 ≤ lam)
    (hint : ∀ r : ℝ, 0 ≤ r → Integrable (fun ω => ‖Z ω‖ ^ r) μ)
    (hmom : ∀ q : ℝ, 0 < q → q < 1 / 2 →
      (∫ ω, ‖Z ω‖ ^ (2 * q) ∂μ) ≤ C * (min Λ (1 - 2 * q)⁻¹ * Λ ^ (-(q / 2)))) :
    μ.real {ω | lam / Λ ^ (1 / 4 : ℝ) < ‖Z ω‖}
      ≤ C * Real.exp 1 * min (Real.log lam) Λ / lam := by
  have hlam0 : 0 < lam := by linarith
  have hL1 : 1 < Real.log lam := by
    have h3 := Real.log_three_gt_d9
    have h := Real.log_le_log (by norm_num) hlam
    linarith
  have hL0 : 0 < Real.log lam := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, 2 * q = 1 - (Real.log lam)⁻¹ :=
    ⟨(1 - (Real.log lam)⁻¹) / 2, by ring⟩
  have hinv : (Real.log lam)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL1
  have hinv0 : 0 < (Real.log lam)⁻¹ := inv_pos.2 hL0
  have hq0 : 0 < q := by linarith
  have hq2 : q < 1 / 2 := by linarith
  have h12q : (1 - 2 * q)⁻¹ = Real.log lam := by rw [hq, sub_sub_cancel, inv_inv]
  have hP : 0 < Λ ^ (q / 2) := Real.rpow_pos_of_pos hΛ _
  have hs0 : 0 < lam / Λ ^ (1 / 4 : ℝ) := div_pos hlam0 (Real.rpow_pos_of_pos hΛ _)
  have hlamq : lam ^ (2 * q) = lam / Real.exp 1 := by
    rw [hq, Real.rpow_sub hlam0, Real.rpow_one, Real.rpow_def_of_pos hlam0,
      mul_inv_cancel₀ hL0.ne']
  have hΛq : (Λ ^ (1 / 4 : ℝ)) ^ (2 * q) = Λ ^ (q / 2) := by
    rw [← Real.rpow_mul hΛ.le]
    congr 1
    ring
  have hspow : (lam / Λ ^ (1 / 4 : ℝ)) ^ (2 * q) = lam / Real.exp 1 / Λ ^ (q / 2) := by
    rw [Real.div_rpow hlam0.le (Real.rpow_nonneg hΛ.le _), hlamq, hΛq]
  have hm := hmom q hq0 hq2
  rw [h12q, Real.rpow_neg hΛ.le] at hm
  have hmark := measureReal_le_norm_le_integral_rpow_div (μ := μ) (Z := Z)
    (by linarith : (0 : ℝ) < 2 * q) hs0 (hint _ (by linarith))
  rw [hspow] at hmark
  calc μ.real {ω | lam / Λ ^ (1 / 4 : ℝ) < ‖Z ω‖}
      ≤ μ.real {ω | lam / Λ ^ (1 / 4 : ℝ) ≤ ‖Z ω‖} :=
        measureReal_mono (Set.setOf_subset_setOf.2 fun _ hω => le_of_lt hω)
    _ ≤ (∫ ω, ‖Z ω‖ ^ (2 * q) ∂μ) / (lam / Real.exp 1 / Λ ^ (q / 2)) := hmark
    _ ≤ C * (min Λ (Real.log lam) * (Λ ^ (q / 2))⁻¹) / (lam / Real.exp 1 / Λ ^ (q / 2)) :=
        div_le_div_of_nonneg_right hm (by positivity)
    _ = C * Real.exp 1 * min (Real.log lam) Λ / lam := by
        rw [min_comm Λ (Real.log lam)]
        field_simp

/-! ### Corollary 1.4: the limits in probability -/

/-- **The squares carry `⌊√x⌋`.**  If `v(p)² = 1` at the primes `p ≤ x`, then
`∑_{n≤x, n = □} v^e(n) = ⌊√x⌋`: the squares `n ≤ x` are the `s²` with `1 ≤ s ≤ √x`, and
`v^e(s²) = 1` (`RMF.compMultExtension_sq_mul_eq` at `m = 1`). -/
lemma sum_isSquare_compMultExtension_eq {v : ℕ → ℂ} {x : ℝ} (hx : 0 ≤ x)
    (hv : ∀ p, p.Prime → p ≤ ⌊x⌋₊ → v p ^ 2 = 1) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsSquare n, compMultExtension v n = (⌊Real.sqrt x⌋₊ : ℂ) := by
  have key : ∀ s : ℕ, s ≤ ⌊Real.sqrt x⌋₊ ↔ s ^ 2 ≤ ⌊x⌋₊ := fun s => by
    simpa using le_floor_sqrt_div_iff hx one_pos s
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsSquare n, compMultExtension v n
      = ∑ _s ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (1 : ℂ) := by
        symm
        refine Finset.sum_bij (fun s _ => s ^ 2) (fun s hs => ?_) (fun s _ s' _ h => ?_)
          (fun n hn => ?_) (fun s hs => ?_)
        · obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
          exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hs1, (key s).1 hsx⟩,
            ⟨s, sq s⟩⟩
        · exact Nat.pow_left_injective two_ne_zero h
        · obtain ⟨hnI, r, hr⟩ := Finset.mem_filter.1 hn
          obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.1 hnI
          have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h0 => by
            subst h0
            simp at hr
            omega
          exact ⟨r, Finset.mem_Icc.2 ⟨hr1, (key r).2 (by rw [sq, ← hr]; exact hnx)⟩,
            by rw [sq, hr]⟩
        · obtain ⟨hs1, hsx⟩ := Finset.mem_Icc.1 hs
          have hle := (key s).1 hsx
          have h := compMultExtension_sq_mul_eq (v := v) (m := 1) (by omega) squarefree_one
            fun p hp hps => hv p hp ((Nat.le_of_dvd (by omega) hps).trans
              ((le_self_pow hs1 two_ne_zero).trans hle))
          rw [mul_one, squarefreeExtension_apply_one] at h
          exact h.symm
    _ = (⌊Real.sqrt x⌋₊ : ℂ) := by simp

/-- **The extended sum off the squares** (from the remark before Corollary 1.4).  Almost surely,
for `x ≥ 0`, `x^{-1/2}∑_{n≤x, n ≠ □} X^e(n) + 1 = Y(x) + (1 - ⌊√x⌋/√x)`, the squares
contributing `⌊√x⌋` (`RMF.sum_isSquare_compMultExtension_eq`). -/
lemma ae_nonsquare_div_add_one_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {x : ℝ} (hx : 0 ≤ x) :
    ∀ᵐ ω ∂μ, (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n, compMultExtension (fun p => X p ω) n)
          / (Real.sqrt x : ℂ) + 1
      = normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω
        + ((1 - (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x : ℝ) : ℂ) := by
  have hsq : ∀ᵐ ω ∂μ, ∀ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), X p ω ^ 2 = 1 :=
    (Filter.eventually_all_finset _).2 fun p hp =>
      ae_sq_X_eq_one hX (Nat.prime_of_mem_primesBelow hp)
  filter_upwards [hsq] with ω hω
  have hS := sum_isSquare_compMultExtension_eq (v := fun p => X p ω) hx
    fun p hp hpx => hω p (Nat.mem_primesBelow.2 ⟨by omega, hp⟩)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) IsSquare
    (compMultExtension fun p => X p ω)
  rw [hS] at hsplit
  rw [normalisedSum, randomSum, ← hsplit]
  push_cast
  ring

/-- `|1 - ⌊√x⌋/√x| ≤ 1/√x` for `x > 0`, as `√x - 1 < ⌊√x⌋ ≤ √x`. -/
lemma abs_one_sub_floor_sqrt_div_sqrt_le {x : ℝ} (hx : 0 < x) :
    |1 - (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x| ≤ (Real.sqrt x)⁻¹ := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le hs.le
  have h2 : Real.sqrt x < ⌊Real.sqrt x⌋₊ + 1 := Nat.lt_floor_add_one _
  have hi : 0 ≤ (Real.sqrt x)⁻¹ := inv_nonneg.2 hs.le
  have e : 1 - (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x
      = (Real.sqrt x - ⌊Real.sqrt x⌋₊) * (Real.sqrt x)⁻¹ := by
    field_simp
  rw [e, abs_of_nonneg (mul_nonneg (by linarith) hi)]
  calc (Real.sqrt x - ⌊Real.sqrt x⌋₊) * (Real.sqrt x)⁻¹ ≤ 1 * (Real.sqrt x)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hi
    _ = (Real.sqrt x)⁻¹ := one_mul _

/-- `C·(log log x)^{-1/8} → 0` as `x → ∞`. -/
lemma tendsto_mul_loglog_rpow_neg_eighth (C : ℝ) :
    Tendsto (fun x : ℝ => C * Real.log (Real.log x) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).const_mul C
  rw [mul_zero] at h
  exact h

/-- **Convergence in measure from a vanishing moment.**  If almost surely
`‖f i - c‖ ≤ ‖Z i‖ + δ i`, with `E‖Z i‖^r ≤ b i` for some `r > 0`, and `b i → 0`, `δ i → 0`, then
`f i → c` in measure: once `δ i < ε/2`, `P(‖f i - c‖ ≥ ε) ≤ P(‖Z i‖ ≥ ε/2) ≤ b i/(ε/2)^r`. -/
lemma tendstoInMeasure_of_norm_sub_le_add {ι : Type*} {l : Filter ι} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f Z : ι → Ω → ℂ} {c : ℂ} {b δ : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (hint : ∀ᶠ i in l, Integrable (fun ω => ‖Z i ω‖ ^ r) μ)
    (hmom : ∀ᶠ i in l, ∫ ω, ‖Z i ω‖ ^ r ∂μ ≤ b i) (hb : Tendsto b l (𝓝 0))
    (hle : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ‖f i ω - c‖ ≤ ‖Z i ω‖ + δ i) (hδ : Tendsto δ l (𝓝 0)) :
    TendstoInMeasure μ f l fun _ => c := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hpow : 0 < (ε / 2) ^ r := Real.rpow_pos_of_pos hε2 r
  have hlim : Tendsto (fun i => b i / (ε / 2) ^ r) l (𝓝 0) := by
    have h := hb.div_const ((ε / 2) ^ r)
    rwa [zero_div] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun i => measureReal_nonneg) ?_
  filter_upwards [hint, hmom, hle, hδ.eventually (eventually_lt_nhds hε2)] with i hi hm hl hd
  have hae : {ω | ε ≤ ‖f i ω - c‖} ≤ᵐ[μ] {ω | ε / 2 ≤ ‖Z i ω‖} := by
    filter_upwards [hl] with ω hω hmem
    change ε ≤ ‖f i ω - c‖ at hmem
    change ε / 2 ≤ ‖Z i ω‖
    linarith
  calc μ.real {ω | ε ≤ ‖f i ω - c‖} ≤ μ.real {ω | ε / 2 ≤ ‖Z i ω‖} := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
    _ ≤ (∫ ω, ‖Z i ω‖ ^ r ∂μ) / (ε / 2) ^ r :=
        measureReal_le_norm_le_integral_rpow_div hr hε2 hi
    _ ≤ b i / (ε / 2) ^ r := div_le_div_of_nonneg_right hm hpow.le

end

/-! ### The corollaries -/

/-- **Corollary 1.3 of the paper, for the extended sum, with the constant `30e`.**  The paper:
for `x` sufficiently large and `λ ≥ 3`,
`P(|x^{-1/2}∑_{n≤x} X^e(n)| > λ/(log log x)^{1/4}) ≪ min{log λ, log log x}/λ`.  Here for every
`x ≥ 3` and `λ ≥ 3` (`lam`), with the constant `30e`: `RMF.measureReal_tail_le_of_moments` on
`RMF.extended_rademacher_moments_upper_uniform_explicit`. -/
theorem extended_rademacher_tail_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x → ∀ lam : ℝ, 3 ≤ lam →
        μ.real {ω | lam / Real.log (Real.log x) ^ (1 / 4 : ℝ)
            < ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖}
          ≤ 30 * Real.exp 1 * min (Real.log lam) (Real.log (Real.log x)) / lam := by
  intro Ω _ X μ hX x hx lam hlam
  haveI := hX.isProbabilityMeasure
  exact measureReal_tail_le_of_moments (by linarith [loglog_ge_of_three_le hx]) hlam
    (fun r hr => integrable_rpow_norm_normalisedSum_compMultExtension hX x hr)
    (extended_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).1

/-- **Corollary 1.3 of the paper, for the weighted sum, with the constant `25e`.**  The paper:
for `x` sufficiently large and `λ ≥ 3`,
`P(|∑_{n≤x} X(n)/√n| > λ/(log log x)^{1/4}) ≪ min{log λ, log log x}/λ`.  Here for every `x ≥ 3`
and `λ ≥ 3` (`lam`), with the constant `25e`: `RMF.measureReal_tail_le_of_moments` on
`RMF.weighted_rademacher_moments_upper_uniform_explicit`. -/
theorem weighted_rademacher_tail_explicit :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ → ∀ x : ℝ, 3 ≤ x → ∀ lam : ℝ, 3 ≤ lam →
        μ.real {ω | lam / Real.log (Real.log x) ^ (1 / 4 : ℝ)
            < ‖weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω‖}
          ≤ 25 * Real.exp 1 * min (Real.log lam) (Real.log (Real.log x)) / lam := by
  intro Ω _ X μ hX x hx lam hlam
  haveI := hX.isProbabilityMeasure
  exact measureReal_tail_le_of_moments (by linarith [loglog_ge_of_three_le hx]) hlam
    (fun r hr => integrable_rpow_norm_weightedRademacherSum hX x hr)
    (weighted_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).1

/-- **Corollary 1.4 of the paper, for the extended sum.**  The paper: as `x → ∞`,
`x^{-1/2}∑_{n≤x, n ≠ □} X^e(n) → -1` in probability.  Here "`n ≠ □`" is `¬IsSquare n` and
convergence in probability is `MeasureTheory.TendstoInMeasure` along `x → ∞` in `ℝ`.  The proof:
`RMF.ae_nonsquare_div_add_one_eq`, `E|Y(x)|^{1/2} ≤ 60Λ^{-1/8}`
(`RMF.extended_rademacher_moments_upper_uniform_explicit` at `q = ¼`) and
`|1 - ⌊√x⌋/√x| ≤ 1/√x`. -/
theorem extended_rademacher_nonsquare_tendstoInMeasure :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
        TendstoInMeasure μ
          (fun (x : ℝ) ω => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬IsSquare n,
            compMultExtension (fun p => X p ω) n) / (Real.sqrt x : ℂ))
          atTop (fun _ => -1) := by
  intro Ω _ X μ hX
  haveI := hX.isProbabilityMeasure
  refine tendstoInMeasure_of_norm_sub_le_add
    (Z := fun x => normalisedSum (fun ω => compMultExtension fun p => X p ω) x)
    (b := fun x => 60 * Real.log (Real.log x) ^ (-(1 / 8 : ℝ)))
    (δ := fun x => (Real.sqrt x)⁻¹) (r := 1 / 2) (by norm_num)
    (Filter.Eventually.of_forall fun x =>
      integrable_rpow_norm_normalisedSum_compMultExtension hX x (by norm_num))
    ?_ (tendsto_mul_loglog_rpow_neg_eighth 60) ?_
    (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  · filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have h := (extended_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).1 (1 / 4)
      (by norm_num) (by norm_num)
    rw [show ((1 : ℝ) - 2 * (1 / 4))⁻¹ = 2 by norm_num,
      show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
      show -((1 / 4 : ℝ) / 2) = -(1 / 8) by norm_num] at h
    have hP : 0 ≤ Real.log (Real.log x) ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_nonneg (by linarith [loglog_ge_of_three_le hx]) _
    have hm := mul_le_mul_of_nonneg_right (min_le_right (Real.log (Real.log x)) 2) hP
    linarith
  · filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    filter_upwards [ae_nonsquare_div_add_one_eq hX hx.le] with ω hω
    rw [sub_neg_eq_add, hω]
    calc ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω
          + ((1 - (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x : ℝ) : ℂ)‖
        ≤ ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
          + ‖((1 - (⌊Real.sqrt x⌋₊ : ℝ) / Real.sqrt x : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖normalisedSum (fun ω => compMultExtension fun p => X p ω) x ω‖
          + (Real.sqrt x)⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith [abs_one_sub_floor_sqrt_div_sqrt_le hx]

/-- **Corollary 1.4 of the paper, for the weighted sum.**  The paper: as `x → ∞`,
`∑_{1<n≤x} X(n)/√n → -1` in probability (the sum over the non-squares, `X` being supported on the
squarefrees).  Convergence in probability is `MeasureTheory.TendstoInMeasure` along `x → ∞` in
`ℝ`.  The proof: `S(x) = 1 + ∑_{1<n≤x} X(n)/√n` as `X(1) = 1`, and `E|S(x)|^{1/2} ≤ 50Λ^{-1/8}`
(`RMF.weighted_rademacher_moments_upper_uniform_explicit` at `q = ¼`). -/
theorem weighted_rademacher_nonsquare_tendstoInMeasure :
    ∀ (Ω : Type*) [MeasurableSpace Ω] (X : ℕ → Ω → ℂ) (μ : Measure Ω),
      IsRademacherPrimeValues X μ →
        TendstoInMeasure μ
          (fun (x : ℝ) ω => ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
            squarefreeExtension (fun p => X p ω) n / (Real.sqrt n : ℂ))
          atTop (fun _ => -1) := by
  intro Ω _ X μ hX
  haveI := hX.isProbabilityMeasure
  refine tendstoInMeasure_of_norm_sub_le_add
    (Z := fun x => weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x)
    (b := fun x => 50 * Real.log (Real.log x) ^ (-(1 / 8 : ℝ)))
    (δ := fun _ => 0) (r := 1 / 2) (by norm_num)
    (Filter.Eventually.of_forall fun x =>
      integrable_rpow_norm_weightedRademacherSum hX x (by norm_num))
    ?_ (tendsto_mul_loglog_rpow_neg_eighth 50) ?_ tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have h := (weighted_rademacher_moments_upper_uniform_explicit Ω X μ hX x hx).1 (1 / 4)
      (by norm_num) (by norm_num)
    rw [show ((1 : ℝ) - 2 * (1 / 4))⁻¹ = 2 by norm_num,
      show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
      show -((1 / 4 : ℝ) / 2) = -(1 / 8) by norm_num] at h
    have hP : 0 ≤ Real.log (Real.log x) ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_nonneg (by linarith [loglog_ge_of_three_le hx]) _
    have hm := mul_le_mul_of_nonneg_right (min_le_right (Real.log (Real.log x)) 2) hP
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    refine Filter.Eventually.of_forall fun ω => le_of_eq ?_
    rw [add_zero, sub_neg_eq_add, weightedRademacherSum,
      ← Finset.add_sum_Ioc_eq_sum_Icc ((Nat.one_le_floor_iff x).2 hx),
      squarefreeExtension_apply_one, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one,
      add_comm]

end RMF
