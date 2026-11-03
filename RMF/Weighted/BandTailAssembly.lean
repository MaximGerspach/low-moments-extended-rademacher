/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.BandTailSmoothing
import RMF.Weighted.PropositionBAssembly

/-!
# Assembling the band tail's rough sum

After the conditioning step of the truncation bound
(`RMF.integral_rpow_norm_blockTruncationTail_le`) the second term is
`E[(∑_{1<r≤x} r⁻¹|T(x/r)|²)^q]` over rough `r`.  It is smoothed at `η = 1/V`, `V = log x/log z`,
where the smoothing error is `O(1)` for every `V`, and split at `R₀ ≍ Vz`, which that choice asks
for.  The pieces:

* **the Rankin range** `r ≤ R₀`, in expectation from the band tail's atom bound
  (`RMF.integral_sum_blockTailTerm_le_of_atom`) and its harmonic mass
  (`RMF.exists_sum_inv_rough_le_mul`);
* **the smoothing error** above `R₀`, in expectation
  (`RMF.exists_integral_blockTailSmoothingError_le`) and integrable
  (`RMF.integrable_blockTailSmoothingError`);
* **the line functional `Z` has integrable powers**
  (`RMF.integrable_rpow_lineDiv_randomEulerProductIco`): without it `E[Z^q]` on the right of the
  assembly could be `0` by convention;
* **the assembly** (`RMF.exists_integral_rpow_sum_blockTailTerm_le`): the sum split at
  `R₀ = A(V+1)z`, the Rankin range below it
  (`RMF.exists_integral_rpow_sum_blockTailTerm_le_rankin`) and the sieve above it
  (`RMF.exists_integral_rpow_sum_blockTailTerm_le_sieve`).
-/

open MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Rankin range, in expectation.**  If `E|T(w)|² ≤ M·w^{-δ}` for every `w > 0`
(`RMF.integral_normSq_blockTailSum_le` supplies this at `δ = 1/log z`), then over `r ∈ [1, R]`

`E ∑_{r∈S} r⁻¹|T(x/r)|² ≤ M·x^{-δ}·R^δ·∑_{r∈S} r⁻¹`,

since `(x/r)^{-δ} = x^{-δ}·r^δ ≤ x^{-δ}·R^δ`. -/
theorem integral_sum_blockTailTerm_le_of_atom {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y z : ℕ) {x δ M R : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hatom : ∀ w : ℝ, 0 < w →
      (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
        ≤ M * w ^ (-δ))
    {S : Finset ℕ} (hS1 : ∀ r ∈ S, 1 ≤ r) (hSR : ∀ r ∈ S, (r : ℝ) ≤ R) :
    (∫ ω, ∑ r ∈ S, blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r ∂μ)
      ≤ M * x ^ (-δ) * R ^ δ * ∑ r ∈ S, ((r : ℝ))⁻¹ := by
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hle := smoothAlgebra_le hX z
  -- each term is integrable: measurable, and at most `(z#)²` almost surely
  have hint : ∀ r ∈ S, Integrable (fun ω =>
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) μ := by
    intro r hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hS1 r hr
    have hmeas : Measurable fun ω =>
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r :=
      measurable_const.mul
        (((measurable_smoothAlgebra_blockTailSum y z (x / r)).mono hle le_rfl).norm.pow_const 2)
    refine (memLp_top_of_bound hmeas.aestronglyMeasurable ((primorial z : ℝ) ^ 2) ?_).integrable
      le_top
    filter_upwards [ae_norm_blockTailSum_le hRa y z (x / r)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (blockTailTerm_nonneg _ _ _ _ _ _), blockTailTerm]
    calc (r : ℝ)⁻¹ * ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z
          (x / r) ω‖ ^ 2
        ≤ 1 * (primorial z : ℝ) ^ 2 :=
          mul_le_mul (inv_le_one_of_one_le₀ hr1)
            (pow_le_pow_left₀ (norm_nonneg _) hω 2) (by positivity) zero_le_one
      _ = (primorial z : ℝ) ^ 2 := one_mul _
  rw [integral_finsetSum S hint, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hS1 r hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hxr : 0 < x / r := div_pos hx hr0
  have hterm : (∫ ω, blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r ∂μ)
      = (r : ℝ)⁻¹ * ∫ ω,
          ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω‖ ^ 2 ∂μ := by
    simp only [blockTailTerm]
    exact integral_const_mul _ _
  have hpow : (x / r) ^ (-δ) = x ^ (-δ) * (r : ℝ) ^ δ := by
    rw [Real.div_rpow hx.le hr0.le, Real.rpow_neg hr0.le, div_inv_eq_mul]
  have hMx : 0 ≤ M * x ^ (-δ) := mul_nonneg hM (Real.rpow_nonneg hx.le _)
  rw [hterm]
  calc (r : ℝ)⁻¹
        * ∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω‖ ^ 2 ∂μ
      ≤ (r : ℝ)⁻¹ * (M * (x / r) ^ (-δ)) :=
        mul_le_mul_of_nonneg_left (hatom _ hxr) (inv_nonneg.2 hr0.le)
    _ = M * x ^ (-δ) * (r : ℝ) ^ δ * (r : ℝ)⁻¹ := by rw [hpow]; ring
    _ ≤ M * x ^ (-δ) * R ^ δ * (r : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr0.le (hSR r hr) hδ) hMx)
          (inv_nonneg.2 hr0.le)

/-- **The harmonic mass of the Rankin range.**  For `z`-rough `r` with `1 < r ≤ A·W·z`, `A ≥ 1`
at least the threshold of `RMF.exists_sum_inv_rough_Ioc_le` and `W ≥ 1`:

`∑ r⁻¹ ≤ A + C·(1 + log W)/log z`,

the range `(z, Az]` by counting (every rough `r > 1` exceeds `z`) and `(Az, AWz]` by the sieve. -/
theorem exists_sum_inv_rough_le_mul :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ (z : ℕ) (A W : ℝ), 2 ≤ z → 1 ≤ A → H ≤ A → 1 ≤ W →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough z r) → (∀ r ∈ S, 1 < r) →
        (∀ r ∈ S, (r : ℝ) ≤ A * W * z) →
        ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ A + C * (1 + Real.log W) / Real.log z := by
  classical
  obtain ⟨C, H₀, hC, hH₀, hharm⟩ := exists_sum_inv_rough_Ioc_le
  refine ⟨C, H₀, hC, hH₀, ?_⟩
  intro z A W hz hA1 hHA hW S hrough hone hle
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hAz0 : (0 : ℝ) ≤ A * z := mul_nonneg hA0.le hz0.le
  have hAz : (z : ℝ) ≤ A * z := le_mul_of_one_le_left hz0.le hA1
  rw [← Finset.sum_filter_add_sum_filter_not S (fun r : ℕ => (r : ℝ) ≤ A * z)]
  -- `(z, Az]` by counting
  have h1 : ∑ r ∈ S.filter (fun r : ℕ => (r : ℝ) ≤ A * z), ((r : ℝ))⁻¹ ≤ A := by
    have hsub : S.filter (fun r : ℕ => (r : ℝ) ≤ A * z) ⊆ Finset.Ioc z ⌊A * z⌋₊ := by
      intro r hr
      rw [Finset.mem_filter] at hr
      exact Finset.mem_Ioc.2 ⟨(hrough r hr.1).lt_of_one_lt (hone r hr.1), Nat.le_floor hr.2⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun i _ _ => inv_nonneg.2 (Nat.cast_nonneg i)) ?_
    refine le_trans (sum_inv_Ioc_le z ⌊A * z⌋₊) ?_
    rw [Nat.card_Ioc, div_le_iff₀ (by positivity)]
    have hfl : ((⌊A * z⌋₊ : ℕ) : ℝ) ≤ A * z := Nat.floor_le hAz0
    have hcast : (((⌊A * z⌋₊ - z : ℕ)) : ℝ) ≤ (⌊A * z⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have hAz1 : A * z ≤ A * ((z : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) hA0.le
    linarith
  -- `(Az, AWz]` by the sieve
  have h2 : ∑ r ∈ S.filter (fun r : ℕ => ¬ (r : ℝ) ≤ A * z), ((r : ℝ))⁻¹
      ≤ C * (1 + Real.log W) / Real.log z := by
    have hsub : S.filter (fun r : ℕ => ¬ (r : ℝ) ≤ A * z)
        ⊆ {n ∈ Finset.Ioc ⌊A * z⌋₊ ⌊A * W * z⌋₊ | IsRough z n} := by
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨Finset.mem_Ioc.2 ⟨(Nat.floor_lt hAz0).2 (not_le.1 hr.2), Nat.le_floor (hle r hr.1)⟩,
        hrough r hr.1⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun i _ _ => inv_nonneg.2 (Nat.cast_nonneg i)) ?_
    have hRR : A * z ≤ A * W * z := by
      rw [mul_right_comm A W]
      exact le_mul_of_one_le_right hAz0 hW
    have hHz : H₀ ≤ A * z := le_trans hHA (le_mul_of_one_le_right hA0.le (by linarith))
    have key := hharm z (A * z) (A * W * z) hz hAz hHz hRR
    have hratio : A * W * z / (A * z) = W := by
      rw [mul_comm A W, mul_assoc W A z, mul_div_assoc, div_self (mul_pos hA0 hz0).ne', mul_one]
    rwa [hratio] at key
  linarith

/-- **The expectation of the band's smoothing error** above `R ≥ max(z, H)`, for `0 < η ≤ 1` and
`x ≥ 1`:  `≤ 2Cη(1 + log x)/log z + 4`.  From the window bound
(`RMF.integral_sum_setIntegral_normSq_blockTailSum_sub_le`), whose `1/η` multiple splits as
`2η∑1/r + 2(1+η)#S/x`: the first against the rough harmonic mass
(`RMF.exists_sum_inv_rough_Ioc_le`), the second through `#S ≤ x`.  At `η = 1/V` it is `≤ 4C + 4`. -/
theorem exists_integral_blockTailSmoothingError_le :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (y z : ℕ) (x η R : ℝ), 2 ≤ z → 1 ≤ x → 0 < η → η ≤ 1 → (z : ℝ) ≤ R → H ≤ R →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough z r) → (∀ r ∈ S, R < (r : ℝ)) →
        (∀ r ∈ S, (r : ℝ) ≤ x) →
        (∫ ω, (1 / η) * ∑ r ∈ S,
            (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
              ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
                - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
              / ((r : ℝ)) ^ 2 ∂μ)
          ≤ 2 * C * η * (1 + Real.log x) / Real.log z + 4 := by
  classical
  obtain ⟨C, H₀, hC, hH₀, hharm⟩ := exists_sum_inv_rough_Ioc_le
  refine ⟨C, H₀, hC, hH₀, ?_⟩
  intro Ω' _ X μ hX y z x η R hz hx1 hη hη1 hzR hHR S hrough hRS hSx
  haveI := hX.isProbabilityMeasure
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hx0 : (0 : ℝ) < x := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hS0 : ∀ r ∈ S, 0 < r := fun r hr => by
    have h : (0 : ℝ) < (r : ℝ) := lt_trans hR0 (hRS r hr)
    exact_mod_cast h
  -- the harmonic mass of `S`
  have hA : ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ C * (1 + Real.log x) / Real.log z := by
    have hsub : S ⊆ {n ∈ Finset.Ioc ⌊R⌋₊ ⌊max R x⌋₊ | IsRough z n} := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨(Nat.floor_lt hR0.le).2 (hRS r hr),
        Nat.le_floor (le_trans (hSx r hr) (le_max_right _ _))⟩, hrough r hr⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun i _ _ => inv_nonneg.2 (Nat.cast_nonneg i)) ?_
    refine le_trans (hharm z R (max R x) hz hzR hHR (le_max_left _ _)) ?_
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC.le) hlogz.le
    have hR1 : (1 : ℝ) ≤ R := by linarith
    have hratio : max R x / R ≤ x := by
      rw [div_le_iff₀ hR0]
      rcases le_total R x with h | h
      · rw [max_eq_right h]
        have := mul_le_mul_of_nonneg_left hR1 hx0.le
        linarith
      · rw [max_eq_left h]
        have := mul_le_mul_of_nonneg_right hx1 hR0.le
        linarith
    have := Real.log_le_log (div_pos (lt_of_lt_of_le hR0 (le_max_left _ _)) hR0) hratio
    linarith
  -- the counting half
  have hB : (S.card : ℝ) ≤ x := by
    have hsub : S ⊆ Finset.Icc 1 ⌊x⌋₊ := fun r hr =>
      Finset.mem_Icc.2 ⟨hS0 r hr, Nat.le_floor (hSx r hr)⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact le_trans (by exact_mod_cast hcard) (Nat.floor_le hx0.le)
  -- the window bound, times `1/η`
  rw [integral_const_mul]
  refine le_trans (mul_le_mul_of_nonneg_left
    (integral_sum_setIntegral_normSq_blockTailSum_sub_le hX y z hx0 hη hS0)
    (le_of_lt (one_div_pos.2 hη))) ?_
  have hsplit : ∀ r ∈ S, 1 / η * (2 * η * (η + (1 + η) * (r : ℝ) / x) / (r : ℝ))
      = 2 * η * ((r : ℝ))⁻¹ + 2 * (1 + η) / x := by
    intro r hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hS0 r hr
    field_simp
    try ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  have half1 : 2 * η * ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ 2 * C * η * (1 + Real.log x) / Real.log z := by
    calc 2 * η * ∑ r ∈ S, ((r : ℝ))⁻¹ ≤ 2 * η * (C * (1 + Real.log x) / Real.log z) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 2 * C * η * (1 + Real.log x) / Real.log z := by ring
  have half2 : (S.card : ℝ) * (2 * (1 + η) / x) ≤ 4 := by
    have hw : 2 * (1 + η) / x ≤ 4 / x := div_le_div_of_nonneg_right (by linarith) hx0.le
    calc (S.card : ℝ) * (2 * (1 + η) / x) ≤ x * (4 / x) :=
          mul_le_mul hB hw (div_nonneg (by linarith) hx0.le) hx0.le
      _ = 4 := by rw [mul_div_assoc', mul_comm x 4, mul_div_assoc, div_self hx0.ne', mul_one]
  linarith

/-- **The band's smoothing error is integrable**: the joint integrability
(`RMF.integrable_uncurry_normSq_blockTailSum_sub`), integrated in `t`. -/
theorem integrable_blockTailSmoothingError {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y z : ℕ) (x η : ℝ)
    (S : Finset ℕ) :
    Integrable (fun ω => (1 / η) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
          - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2) μ := by
  refine (integrable_finsetSum S fun r _ => ?_).const_mul _
  simp only [integral_Icc_eq_integral_Ioc]
  exact ((integrable_uncurry_normSq_blockTailSum_sub hX y z x r
    ((r : ℝ) * (1 + η))).integral_prod_left.const_mul 2).div_const _

/-- **The line functional has integrable powers** for a band, at `0 < c < ½`: the line
product is jointly measurable (`RMF.measurable_uncurry_randomEulerProductIco_line`) and at most
`2^{z-y}` almost surely (`RMF.ae_forall_norm_randomEulerProductIco_line_le_two_pow`), so
`RMF.integrable_rpow_setIntegral_lineDiv_of_bound` applies on the whole line. -/
theorem integrable_rpow_lineDiv_randomEulerProductIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsRademacherPrimeValues X μ) (y z : ℕ) {c L q : ℝ}
    (hc0 : 0 < c) (hc : c < 1 / 2) (hL : 0 < L) (hq0 : 0 ≤ q) :
    Integrable (fun ω => (L⁻¹ * ∫ t : ℝ,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
            ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
          / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q) μ := by
  have hI := integrable_rpow_setIntegral_lineDiv_of_bound (S := Set.univ) (q := q) hc0 hL hq0
    (measurable_uncurry_randomEulerProductIco_line hX (y + 1) (z + 1) c)
    (ae_forall_norm_randomEulerProductIco_line_le_two_pow hX (y + 1) (z + 1) hc)
  simpa only [Measure.restrict_univ] using hI

/-! ### The assembly -/

/-- **The Rankin range, raised to the power `q`.**  For `z`-rough `r` with `1 < r ≤ AWz`, from an
atom bound `E|T(w)|² ≤ M·w^{-1/log z}`:
`E[(∑_r r⁻¹|T(x/r)|²)^q] ≤ 1 + M·x^{-1/log z}·(AWz)^{1/log z}·(A + C(1 + log W)/log z)`,
by Jensen (`RMF.integral_rpow_le_rpow_of_integral_le`) and `t^q ≤ 1 + t`, from the two bounds of
the Rankin range (`RMF.integral_sum_blockTailTerm_le_of_atom`,
`RMF.exists_sum_inv_rough_le_mul`). -/
theorem exists_integral_rpow_sum_blockTailTerm_le_rankin :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (q M A W x : ℝ) (y z : ℕ), 0 ≤ q → q ≤ 1 → 0 ≤ M → 2 ≤ z → 1 ≤ A → H ≤ A → 1 ≤ W →
        0 < x →
        (∀ w : ℝ, 0 < w →
          (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
            ≤ M * w ^ (-(Real.log z)⁻¹)) →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough z r) → (∀ r ∈ S, 1 < r) →
        (∀ r ∈ S, (r : ℝ) ≤ A * W * z) →
        (∫ ω, (∑ r ∈ S,
            blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
          ≤ 1 + M * x ^ (-(Real.log z)⁻¹) * (A * W * z) ^ (Real.log z)⁻¹
              * (A + C * (1 + Real.log W) / Real.log z) := by
  obtain ⟨C, H, hC, hH, hharm⟩ := exists_sum_inv_rough_le_mul
  refine ⟨C, H, hC, hH, ?_⟩
  intro Ω' _ X μ hX q M A W x y z hq0 hq1 hM hz hA1 hHA hW hx hatom S hrough hone hle
  haveI := hX.isProbabilityMeasure
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hS1 : ∀ r ∈ S, 1 ≤ r := fun r hr => (hone r hr).le
  have hAWz : (0 : ℝ) ≤ A * W * z :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg z)
  have hB : (∫ ω, ∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r ∂μ)
      ≤ M * x ^ (-(Real.log z)⁻¹) * (A * W * z) ^ (Real.log z)⁻¹
          * (A + C * (1 + Real.log W) / Real.log z) := by
    refine le_trans (integral_sum_blockTailTerm_le_of_atom hX y z hx (inv_nonneg.2 hlogz.le) hM
      hatom hS1 hle) (mul_le_mul_of_nonneg_left (hharm z A W hz hA1 hHA hW S hrough hone hle) ?_)
    exact mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hx.le _)) (Real.rpow_nonneg hAWz _)
  have hint : Integrable (fun ω => ∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) μ := by
    simpa using integrable_rpow_sum_blockTailTerm hX y z x hS1 zero_le_one
  have h0 : ∀ᵐ ω ∂μ, 0 ≤ ∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r :=
    Filter.Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun r _ => blockTailTerm_nonneg _ _ _ _ _ _
  refine le_trans (integral_rpow_le_rpow_of_integral_le hq0 hq1 h0 hint hB) ?_
  exact rpow_le_one_add (le_trans (integral_nonneg_of_ae h0) hB) hq0 hq1

/-- **The range above `R`, raised to the power `q`.**  For `0 ≤ q ≤ 1`, `z ≥ 3`, `x ≥ 1`,
`2c·log z = 1`, `0 < η ≤ 1`, `R > 1 + η`, `ηR ≥ 4` and `Rη/(1+η) ≥ max(H, z)`, the rough
`r ∈ (R, x]` give `E[(∑_r r⁻¹|T(x/r)|²)^q] ≤ C·(E[Z^q] + 1 + η(1 + log x)/log z)`,
`Z = (log z)⁻¹∫_ℝ |F_{y,z}(½-c+it)/(c+it)|² dt`.  Almost surely the sum is at most `e²C_s·Z` plus
the smoothing error (`RMF.exists_sum_blockTailTerm_le_sieve`); subadditivity splits the power, and
the error goes by Jensen (`RMF.exists_integral_blockTailSmoothingError_le`). -/
theorem exists_integral_rpow_sum_blockTailTerm_le_sieve :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (q c x η R : ℝ) (y z : ℕ), 0 ≤ q → q ≤ 1 → 3 ≤ z → 1 ≤ x → 0 < η → η ≤ 1 →
        1 + η < R → H ≤ R * η / (1 + η) → (z : ℝ) ≤ R * η / (1 + η) → 4 ≤ η * R →
        2 * c * Real.log z = 1 →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough z r) → (∀ r ∈ S, R < (r : ℝ)) →
        (∀ r ∈ S, (r : ℝ) ≤ x) →
        (∫ ω, (∑ r ∈ S,
            blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
          ≤ C * ((∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                      (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                    / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
              + 1 + η * (1 + Real.log x) / Real.log z) := by
  obtain ⟨Cs, Hs, hCs, hHs, hsm⟩ := exists_sum_blockTailTerm_le_sieve
  obtain ⟨Ce, He, hCe, -, herr⟩ := exists_integral_blockTailSmoothingError_le
  refine ⟨max (max 1 (Real.exp 2 * Cs)) (5 + 2 * Ce), max Hs He,
    lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _)),
    lt_of_lt_of_le hHs (le_max_left _ _), ?_⟩
  intro Ω' _ X μ hX q c x η R y z hq0 hq1 hz hx1 hη hη1 hR hHR hzR h4 hc S hrough hRS hSx
  haveI := hX.isProbabilityMeasure
  have hRa : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  -- the numbers
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hz2 : 2 ≤ z := by omega
  have hlogz1 : 1 < Real.log (z : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hz3)
    rwa [Real.log_exp] at h
  have hlogz : 0 < Real.log (z : ℝ) := by linarith
  have h2c : 0 < 2 * c := pos_of_mul_pos_left (by rw [hc]; norm_num) hlogz.le
  have hc0 : 0 < c := by linarith
  have hc1 : 2 * c < 1 := by
    have := mul_lt_mul_of_pos_left hlogz1 h2c
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hRη : R * η / (1 + η) ≤ R := by
    rw [div_le_iff₀ h1η]
    have := mul_le_mul_of_nonneg_left (show η ≤ 1 + η by linarith) hR0.le
    linarith
  have hzR' : (z : ℝ) ≤ R := le_trans hzR hRη
  have hS1 : ∀ r ∈ S, 1 ≤ r := fun r hr => by
    have h : (1 : ℝ) < (r : ℝ) := lt_trans (by linarith) (hRS r hr)
    exact_mod_cast h.le
  have hT0 : 0 ≤ η * (1 + Real.log x) / Real.log z :=
    div_nonneg (mul_nonneg hη.le (by linarith [Real.log_nonneg hx1])) hlogz.le
  -- the line functional and the smoothing error, as functions of `ω`
  obtain ⟨Z, hZ⟩ : ∃ Z : Ω' → ℝ, ∀ ω, Z ω = (Real.log z)⁻¹ * ∫ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := ⟨fun _ => _, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Ω' → ℝ, ∀ ω, E ω = (1 / η) * ∑ r ∈ S,
      (2 * (∫ t in Set.Icc ((r : ℝ)) ((r : ℝ) * (1 + η)),
        ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / r) ω
          - blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z (x / t) ω‖ ^ 2))
        / ((r : ℝ)) ^ 2 := ⟨fun _ => _, fun _ => rfl⟩
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by
    rw [hZ ω]
    exact mul_nonneg (inv_nonneg.2 hlogz.le) (integral_nonneg fun t => sq_nonneg _)
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω => by
    rw [hE ω]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => ?_)
    exact div_nonneg (mul_nonneg (by norm_num)
      (setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _)) (sq_nonneg _)
  -- almost surely, the sum is at most `e²C_s·Z` plus the error
  have hbdd : ∀ᵐ ω ∂μ, ∀ n, ‖(squarefreeExtension fun p => X p ω) n‖ ≤ 1 :=
    MeasureTheory.ae_all_iff.2 fun n => hRa.norm_apply_le_one n
  have hpt : ∀ᵐ ω ∂μ, ∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r
        ≤ Real.exp 2 * Cs * Z ω + E ω := by
    filter_upwards [hbdd] with ω hb
    by_cases hRx : R ≤ x * (1 + η)
    · have h1 := hsm Ω' (fun ω => squarefreeExtension fun p => X p ω) ω hb y z x η R hz2 hη hR
        (le_trans (le_max_left _ _) hHR) hzR S hrough hRS hSx
      have h2 := setIntegral_normSq_blockTailSum_mul_sieve_le (X := X) y z hx0 hR0 hRx hη hη1
        hc0 hc1.le hCs hlogz (two_mul_sieve_shape_div_le_of_four_le hη hη1 h4) ω
      rw [hZ ω, hE ω]
      linarith
    · have hxR : x * (1 + η) < R := not_le.1 hRx
      have hempty : S = ∅ := Finset.eq_empty_of_forall_notMem fun r hr => by
        have h1 := hSx r hr
        have h2 := hRS r hr
        have h3 : x ≤ x * (1 + η) := le_mul_of_one_le_right hx0.le (by linarith)
        linarith
      rw [hempty, Finset.sum_empty]
      exact add_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos 2).le hCs.le) (hZ0 ω)) (hE0 ω)
  -- integrability
  have hIS : Integrable (fun ω => (∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q) μ :=
    integrable_rpow_sum_blockTailTerm hX y z x hS1 hq0
  have hIZ : Integrable (fun ω => Z ω ^ q) μ := by
    simp only [hZ]
    exact integrable_rpow_lineDiv_randomEulerProductIco hX y z hc0 (by linarith) hlogz hq0
  have hIE : Integrable E μ :=
    (integrable_blockTailSmoothingError hX y z x η S).congr
      (Filter.Eventually.of_forall fun ω => (hE ω).symm)
  have hIEq : Integrable (fun ω => E ω ^ q) μ :=
    integrable_rpow_of_integrable hIE (Filter.Eventually.of_forall hE0) hq0 hq1
  -- the power splits
  have hptq : ∀ᵐ ω ∂μ, (∑ r ∈ S,
      blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q
        ≤ (Real.exp 2 * Cs) ^ q * Z ω ^ q + E ω ^ q := by
    filter_upwards [hpt] with ω hω
    have hsum0 : 0 ≤ ∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r :=
      Finset.sum_nonneg fun r _ => blockTailTerm_nonneg _ _ _ _ _ _
    have hC0 : 0 ≤ Real.exp 2 * Cs := mul_nonneg (Real.exp_pos 2).le hCs.le
    calc (∑ r ∈ S,
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q
        ≤ (Real.exp 2 * Cs * Z ω + E ω) ^ q := Real.rpow_le_rpow hsum0 hω hq0
      _ ≤ (Real.exp 2 * Cs * Z ω) ^ q + E ω ^ q :=
          Real.rpow_add_le_add_rpow (mul_nonneg hC0 (hZ0 ω)) (hE0 ω) hq0 hq1
      _ = (Real.exp 2 * Cs) ^ q * Z ω ^ q + E ω ^ q := by rw [Real.mul_rpow hC0 (hZ0 ω)]
  -- the error, by Jensen
  have hEq : (∫ ω, E ω ^ q ∂μ) ≤ 5 + 2 * Ce * (η * (1 + Real.log x) / Real.log z) := by
    have hEint : (∫ ω, E ω ∂μ) ≤ 2 * Ce * η * (1 + Real.log x) / Real.log z + 4 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hE)]
      exact herr Ω' X μ hX y z x η R hz2 hx1 hη hη1 hzR'
        (le_trans (le_max_right _ _) (le_trans hHR hRη)) S hrough hRS hSx
    have hB0 : 0 ≤ 2 * Ce * η * (1 + Real.log x) / Real.log z + 4 := by
      have : 0 ≤ 2 * Ce * η * (1 + Real.log x) / Real.log z :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCe.le) hη.le)
          (by linarith [Real.log_nonneg hx1])) hlogz.le
      linarith
    calc (∫ ω, E ω ^ q ∂μ) ≤ (2 * Ce * η * (1 + Real.log x) / Real.log z + 4) ^ q :=
          integral_rpow_le_rpow_of_integral_le hq0 hq1 (Filter.Eventually.of_forall hE0) hIE hEint
      _ ≤ 1 + (2 * Ce * η * (1 + Real.log x) / Real.log z + 4) := rpow_le_one_add hB0 hq0 hq1
      _ = 5 + 2 * Ce * (η * (1 + Real.log x) / Real.log z) := by ring
  -- assemble
  have hKZ : (Real.exp 2 * Cs) ^ q ≤ max 1 (Real.exp 2 * Cs) :=
    rpow_le_max_one (mul_pos (Real.exp_pos 2) hCs) hq0 hq1
  have hZq0 : 0 ≤ ∫ ω, Z ω ^ q ∂μ := integral_nonneg fun ω => Real.rpow_nonneg (hZ0 ω) q
  have key : (∫ ω, (∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
      ≤ max (max 1 (Real.exp 2 * Cs)) (5 + 2 * Ce)
          * ((∫ ω, Z ω ^ q ∂μ) + 1 + η * (1 + Real.log x) / Real.log z) := by
    calc (∫ ω, (∑ r ∈ S,
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
        ≤ ∫ ω, ((Real.exp 2 * Cs) ^ q * Z ω ^ q + E ω ^ q) ∂μ :=
          integral_mono_ae hIS ((hIZ.const_mul _).add hIEq) hptq
      _ = (Real.exp 2 * Cs) ^ q * (∫ ω, Z ω ^ q ∂μ) + ∫ ω, E ω ^ q ∂μ := by
          rw [integral_add (hIZ.const_mul _) hIEq, integral_const_mul]
      _ ≤ max 1 (Real.exp 2 * Cs) * (∫ ω, Z ω ^ q ∂μ)
            + (5 + 2 * Ce * (η * (1 + Real.log x) / Real.log z)) :=
          add_le_add (mul_le_mul_of_nonneg_right hKZ hZq0) hEq
      _ ≤ max (max 1 (Real.exp 2 * Cs)) (5 + 2 * Ce)
            * ((∫ ω, Z ω ^ q ∂μ) + 1 + η * (1 + Real.log x) / Real.log z) := by
          have e1 := mul_le_mul_of_nonneg_right
            (le_max_left (max 1 (Real.exp 2 * Cs)) (5 + 2 * Ce)) hZq0
          have e2 := mul_le_mul_of_nonneg_right
            (le_max_right (max 1 (Real.exp 2 * Cs)) (5 + 2 * Ce)) hT0
          have e3 := le_max_right (max 1 (Real.exp 2 * Cs)) (5 + 2 * Ce)
          linarith
  simpa only [hZ] using key

/-- **The rough sum of band tails, raised to the power `q`.**  For `0 ≤ q ≤ 1`, `z ≥ 3`, `x ≥ z`,
`2c·log z = 1` and an atom bound `E|T(w)|² ≤ M·w^{-1/log z}`, with `K` absolute and
`V = log x/log z`: `E[(∑_{1<r≤x} r⁻¹|T(x/r)|²)^q] ≤ K·(E[Z^q] + 1 + M·e^{-V}(V+1)²)`.  The sum is
split at `R₀ = A(V+1)z` and smoothed at `η = 1/V`: below `R₀` the Rankin range
(`RMF.exists_integral_rpow_sum_blockTailTerm_le_rankin` at `W = V+1`), above it the sieve
(`RMF.exists_integral_rpow_sum_blockTailTerm_le_sieve`, whose error term is at most `2`). -/
theorem exists_integral_rpow_sum_blockTailTerm_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsRademacherPrimeValues X μ →
      ∀ (q M c x : ℝ) (y z : ℕ), 0 ≤ q → q ≤ 1 → 0 ≤ M → 3 ≤ z → (z : ℝ) ≤ x →
        2 * c * Real.log z = 1 →
        (∀ w : ℝ, 0 < w →
          (∫ ω, ‖blockTailSum (fun ω => squarefreeExtension fun p => X p ω) y z w ω‖ ^ 2 ∂μ)
            ≤ M * w ^ (-(Real.log z)⁻¹)) →
      ∀ S : Finset ℕ, (∀ r ∈ S, IsRough z r) → (∀ r ∈ S, 1 < r) → (∀ r ∈ S, (r : ℝ) ≤ x) →
        (∫ ω, (∑ r ∈ S,
            blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
          ≤ K * ((∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
                  ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1)
                      (z + 1) ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
                    / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ)
              + 1 + M * Real.exp (-(Real.log x / Real.log z))
                  * (Real.log x / Real.log z + 1) ^ 2) := by
  obtain ⟨C₁, H₁, hC₁, -, hrank⟩ := exists_integral_rpow_sum_blockTailTerm_le_rankin
  obtain ⟨C₂, H₂, hC₂, -, hsiev⟩ := exists_integral_rpow_sum_blockTailTerm_le_sieve
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max 4 (max H₁ H₂) := ⟨_, rfl⟩
  have hA4 : 4 ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAH₁ : H₁ ≤ A := by rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAH₂ : H₂ ≤ A := by rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max (1 + 3 * C₂) (Real.exp 1 * A * (A + C₁)),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro Ω' _ X μ hX q M c x y z hq0 hq1 hM hz hzx hc hatom S hrough hone hSx
  haveI := hX.isProbabilityMeasure
  -- the numbers
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hz2 : 2 ≤ z := by omega
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz1 : 1 < Real.log (z : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hz3)
    rwa [Real.log_exp] at h
  have hlogz : 0 < Real.log (z : ℝ) := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogzx : Real.log (z : ℝ) ≤ Real.log x := Real.log_le_log hz0 hzx
  have hlogx : 0 < Real.log x := by linarith
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = Real.log x / Real.log z := ⟨_, rfl⟩
  have hV1 : 1 ≤ V := by rw [hVdef]; exact (one_le_div hlogz).2 hlogzx
  have hV0 : 0 < V := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = V⁻¹ := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact inv_pos.2 hV0
  have hη1 : η ≤ 1 := by rw [hηdef]; exact inv_le_one_of_one_le₀ hV1
  have hηV : η * V = 1 := by rw [hηdef]; exact inv_mul_cancel₀ hV0.ne'
  have h1η : (0 : ℝ) < 1 + η := by linarith
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hAz : 4 ≤ A * z := by
    have := mul_le_mul hA4 hz3 (by norm_num) hA0.le
    linarith
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = A * (V + 1) * z := ⟨_, rfl⟩
  -- the sifting range and the window weight at `R₀`
  have hRη : R₀ * η / (1 + η) = A * z := by
    rw [div_eq_iff h1η.ne', hR₀def]
    linear_combination (A * z) * hηV
  have hηR : η * R₀ = A * z * (1 + η) := by
    rw [hR₀def]
    linear_combination (A * z) * hηV
  have hsR : H₂ ≤ R₀ * η / (1 + η) := by
    rw [hRη]
    exact le_trans hAH₂ (le_mul_of_one_le_right hA0.le (by linarith))
  have hzsR : (z : ℝ) ≤ R₀ * η / (1 + η) := by
    rw [hRη]
    exact le_mul_of_one_le_left hz0.le hA1
  have h4R : 4 ≤ η * R₀ := by
    rw [hηR]
    exact le_trans hAz (le_mul_of_one_le_right (by linarith) (by linarith))
  have hR₀gt : 1 + η < R₀ := by
    have h1 : A * z ≤ R₀ := by
      rw [hR₀def, mul_right_comm]
      exact le_mul_of_one_le_right (mul_nonneg hA0.le hz0.le) (by linarith)
    linarith
  -- split at `R₀`
  have hS1 : ∀ r ∈ S, 1 ≤ r := fun r hr => (hone r hr).le
  have hsub1 : ∀ r ∈ S.filter (fun r : ℕ => (r : ℝ) ≤ R₀), 1 ≤ r :=
    fun r hr => hS1 r (Finset.mem_filter.1 hr).1
  have hsub2 : ∀ r ∈ S.filter (fun r : ℕ => ¬ (r : ℝ) ≤ R₀), 1 ≤ r :=
    fun r hr => hS1 r (Finset.mem_filter.1 hr).1
  have hsplit : ∀ ω, (∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q
      ≤ (∑ r ∈ S.filter (fun r : ℕ => (r : ℝ) ≤ R₀),
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q
        + (∑ r ∈ S.filter (fun r : ℕ => ¬ (r : ℝ) ≤ R₀),
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q := by
    intro ω
    rw [← Finset.sum_filter_add_sum_filter_not S (fun r : ℕ => (r : ℝ) ≤ R₀)]
    exact Real.rpow_add_le_add_rpow
      (Finset.sum_nonneg fun r _ => blockTailTerm_nonneg _ _ _ _ _ _)
      (Finset.sum_nonneg fun r _ => blockTailTerm_nonneg _ _ _ _ _ _) hq0 hq1
  have hI := integrable_rpow_sum_blockTailTerm hX y z x hS1 hq0
  have hI1 := integrable_rpow_sum_blockTailTerm hX y z x hsub1 hq0
  have hI2 := integrable_rpow_sum_blockTailTerm hX y z x hsub2 hq0
  have hmain : (∫ ω, (∑ r ∈ S,
        blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
      ≤ (∫ ω, (∑ r ∈ S.filter (fun r : ℕ => (r : ℝ) ≤ R₀),
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ)
        + ∫ ω, (∑ r ∈ S.filter (fun r : ℕ => ¬ (r : ℝ) ≤ R₀),
          blockTailTerm (fun ω => squarefreeExtension fun p => X p ω) y z x ω r) ^ q ∂μ := by
    rw [← integral_add hI1 hI2]
    exact integral_mono hI (hI1.add hI2) hsplit
  -- below `R₀`: the Rankin range
  have hrk := hrank Ω' X μ hX q M A (V + 1) x y z hq0 hq1 hM hz2 hA1 hAH₁ (by linarith) hx0
    hatom (S.filter (fun r : ℕ => (r : ℝ) ≤ R₀))
    (fun r hr => hrough r (Finset.mem_filter.1 hr).1)
    (fun r hr => hone r (Finset.mem_filter.1 hr).1)
    (fun r hr => by rw [← hR₀def]; exact (Finset.mem_filter.1 hr).2)
  have hxδ : x ^ (-(Real.log z)⁻¹) = Real.exp (-V) := by
    rw [Real.rpow_def_of_pos hx0, hVdef]
    congr 1
    ring
  have hAV0 : 0 < A * (V + 1) := mul_pos hA0 (by linarith)
  have hAV1 : 1 ≤ A * (V + 1) := by
    have := mul_le_mul hA1 (show (1 : ℝ) ≤ V + 1 by linarith) zero_le_one hA0.le
    linarith
  have hRδ : (A * (V + 1) * z) ^ (Real.log z)⁻¹ ≤ Real.exp 1 * (A * (V + 1)) := by
    rw [Real.rpow_def_of_pos (mul_pos hAV0 hz0), Real.log_mul hAV0.ne' hz0.ne']
    have hlogAV : 0 ≤ Real.log (A * (V + 1)) := Real.log_nonneg hAV1
    have h1 : (Real.log (A * (V + 1)) + Real.log z) * (Real.log z)⁻¹
        ≤ Real.log (A * (V + 1)) + 1 := by
      rw [add_mul, mul_inv_cancel₀ hlogz.ne', ← div_eq_mul_inv]
      have := div_le_self hlogAV hlogz1.le
      linarith
    calc Real.exp ((Real.log (A * (V + 1)) + Real.log z) * (Real.log z)⁻¹)
        ≤ Real.exp (Real.log (A * (V + 1)) + 1) := Real.exp_le_exp.2 h1
      _ = Real.exp 1 * (A * (V + 1)) := by
          rw [Real.exp_add, Real.exp_log hAV0, mul_comm (A * (V + 1)) (Real.exp 1)]
  have hbrack : A + C₁ * (1 + Real.log (V + 1)) / Real.log z ≤ (A + C₁) * (V + 1) := by
    have hlogV : Real.log (V + 1) ≤ V := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < V + 1 by linarith)
      linarith
    have hlogV0 : 0 ≤ 1 + Real.log (V + 1) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ V + 1 by linarith)
      linarith
    have h1 : C₁ * (1 + Real.log (V + 1)) / Real.log z ≤ C₁ * (1 + Real.log (V + 1)) :=
      div_le_self (mul_nonneg hC₁.le hlogV0) hlogz1.le
    have h2 : C₁ * (1 + Real.log (V + 1)) ≤ C₁ * (V + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₁.le
    have h3 : A ≤ A * (V + 1) := le_mul_of_one_le_right hA0.le (by linarith)
    linarith
  have hrankB : M * x ^ (-(Real.log z)⁻¹) * (A * (V + 1) * z) ^ (Real.log z)⁻¹
        * (A + C₁ * (1 + Real.log (V + 1)) / Real.log z)
      ≤ Real.exp 1 * A * (A + C₁) * (M * Real.exp (-V) * (V + 1) ^ 2) := by
    rw [hxδ]
    have hMe : 0 ≤ M * Real.exp (-V) := mul_nonneg hM (Real.exp_pos _).le
    have hbr0 : 0 ≤ A + C₁ * (1 + Real.log (V + 1)) / Real.log z := by
      have h1 : 0 ≤ Real.log (V + 1) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ C₁ * (1 + Real.log (V + 1)) / Real.log z :=
        div_nonneg (mul_nonneg hC₁.le (by linarith)) hlogz.le
      linarith
    calc M * Real.exp (-V) * (A * (V + 1) * z) ^ (Real.log z)⁻¹
          * (A + C₁ * (1 + Real.log (V + 1)) / Real.log z)
        ≤ M * Real.exp (-V) * (Real.exp 1 * (A * (V + 1))) * ((A + C₁) * (V + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hRδ hMe) hbrack hbr0
            (mul_nonneg hMe (mul_nonneg (Real.exp_pos 1).le hAV0.le))
      _ = Real.exp 1 * A * (A + C₁) * (M * Real.exp (-V) * (V + 1) ^ 2) := by ring
  -- above `R₀`: the sieve
  have hsv := hsiev Ω' X μ hX q c x η R₀ y z hq0 hq1 hz hx1 hη hη1 hR₀gt hsR hzsR h4R hc
    (S.filter (fun r : ℕ => ¬ (r : ℝ) ≤ R₀)) (fun r hr => hrough r (Finset.mem_filter.1 hr).1)
    (fun r hr => not_le.1 (Finset.mem_filter.1 hr).2)
    (fun r hr => hSx r (Finset.mem_filter.1 hr).1)
  have hT2 : η * (1 + Real.log x) / Real.log z ≤ 2 := by
    have hηlogx : η * Real.log x = Real.log z := by
      rw [hηdef, hVdef, inv_div, div_mul_cancel₀ _ hlogx.ne']
    rw [div_le_iff₀ hlogz]
    linarith
  -- assemble
  have hIZ0 : 0 ≤ ∫ ω, ((Real.log z)⁻¹ * ∫ t : ℝ,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1)
          ((1 / 2 : ℂ) - (c : ℂ) + (t : ℂ) * Complex.I) ω
        / ((c : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ^ q ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (mul_nonneg (inv_nonneg.2 hlogz.le) (integral_nonneg fun t => sq_nonneg _)) q
  have hMV0 : 0 ≤ M * Real.exp (-V) * (V + 1) ^ 2 :=
    mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (sq_nonneg _)
  rw [← hVdef]
  have e1 := mul_le_mul_of_nonneg_right
    (show C₂ ≤ max (1 + 3 * C₂) (Real.exp 1 * A * (A + C₁)) from
      le_trans (by linarith) (le_max_left _ _)) hIZ0
  have e2 := mul_le_mul_of_nonneg_right
    (le_max_right (1 + 3 * C₂) (Real.exp 1 * A * (A + C₁))) hMV0
  have e3 := le_max_left (1 + 3 * C₂) (Real.exp 1 * A * (A + C₁))
  have e4 := mul_le_mul_of_nonneg_left hT2 hC₂.le
  linarith

end RMF
