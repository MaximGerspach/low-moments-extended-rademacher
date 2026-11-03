/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.ChaosInterpolation
import RMF.Reduction.WindowBridge
import RMF.Analysis.ShiftWeight

/-!
# The unit windows, summed at `2/3`

The line integral is a weighted sum over unit windows, `∑_n 8(1+n²)⁻¹·W_n` with
`W_n = ∫_n^{n+1}|F(½+it)|²dt` (`RMF.window_boundOf`).  To bound its `q`-th moment for **small `q`**
there are two moves available and they do not commute:

* **subadditivity** of `u ↦ u^r` (`RMF.rpow_sum_le_sum_rpow`), which turns the sum into
  `∑_n (8(1+n²)⁻¹)^r·W_n^r` and so costs `∑_n (1+n²)^{-r}` — convergent only for `r > ½`;
* **Hölder descent** (`RMF.integral_rpow_le_rpow_of_integral_le`), which trades an exponent `q`
  for an exponent `r ≥ q` at the price of an outer power `q/r`.

Descend first and the sum is `∑_n (1+n²)^{-q}`, which **diverges at `q ≤ ½`**.  Sum first, at the
fixed exponent `r = 2/3`, and it is `∑_n (1+n²)^{-2/3} = ∑_n RMF.shiftWeight (2/3) n`, an absolute
constant (`RMF.summable_shiftWeight`, whose hypothesis `½ < 2/3` is a numeral).  The descent to `q`
then happens **outside** the sum, where it cannot see the windows at all.

That is the same move `RMF.integral_rpow_le_rpow_integral_of_le_two_thirds` makes for the unshifted
moment: the upper bound need only be proved at `q = 2/3`, and every smaller `q` follows.  The
difference is only *where* `2/3` is inserted — there, at the top; here, between the sum and the
descent.

## `5/8`, twice

`RMF.summable_shiftWeight_mul_abs_add_one_rpow` needs `5/8 < q`, and that is exactly what pins
`RMF.periodisation_upper_rademacher` to `5/8 < q` and the Rademacher upper bound to `2/3 ≤ q ≤ 1`.
On this route the same residual is met only at the **fixed** `2/3`, where `5/8 < 2/3` is a numeral
— so the threshold that blocks the periodisation route at a variable `q` is harmless here, and it
is precisely what absorbs the chaos estimate's non-uniform per-window factor.

## The instantiation

`RMF.exists_const_integral_rpow_windowSum_chaos_le_rademacher` feeds the per-window hypothesis
from `RMF.exists_const_integral_chaosWindowShift_rpow_le_int_rademacher`, which holds at every
height and every `q ∈ [0,1]`.  Its height hypothesis `harperWindowLevel cr |n| ≤ ℓogℓog x / 3` is
discharged on `|n| ≤ (ℓogℓog x)²` by `RMF.exists_threshold_harperWindowLevel_le` at `k = 2` — the
range is that lemma's `k = 2` on the nose — and its factor `(⌈harperWindowLevel cr |n|⌉₊ + 1)²` by
`RMF.exists_const_harperWindowLevel_add_two_le`, which puts it below `A²(|n|+1)^{1/4}`.
-/

open Finset MeasureTheory

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Descent through `2/3`, over a finite family of windows.**

`∫ (∑_i a_i g_i)^q ≤ (∑_i a_i^{2/3} b_i)^{3q/2}` for `0 ≤ q ≤ 2/3`, given `∫ g_i^{2/3} ≤ b_i`.

The exponent `2/3` is fixed *before* the sum is taken, so the weights are only ever summed at
`2/3`; the `q` appears solely in the outer power.  At `q = 0` both sides are `1`. -/
theorem integral_rpow_weightedSum_le_of_two_thirds
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι)
    {a : ι → ℝ} {g : ι → Ω → ℝ} {b : ι → ℝ} {q : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hg : ∀ i ω, 0 ≤ g i ω) (hint : ∀ i ∈ s, Integrable (g i) μ)
    (hb : ∀ i ∈ s, (∫ ω, g i ω ^ (2 / 3 : ℝ) ∂μ) ≤ b i)
    (hq0 : 0 ≤ q) (hq : q ≤ 2 / 3) :
    (∫ ω, (∑ i ∈ s, a i * g i ω) ^ q ∂μ)
      ≤ (∑ i ∈ s, a i ^ (2 / 3 : ℝ) * b i) ^ (3 * q / 2) := by
  classical
  have hZ0 : ∀ ω, 0 ≤ ∑ i ∈ s, a i * g i ω := fun ω =>
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hg i ω)
  have hint23 : ∀ i ∈ s, Integrable (fun ω => g i ω ^ (2 / 3 : ℝ)) μ := fun i hi =>
    integrable_rpow_of_integrable (hint i hi)
      (Filter.Eventually.of_forall (hg i)) (by norm_num) (by norm_num)
  -- the sum is integrable, hence so is its `2/3` power
  have hZint1 : Integrable (fun ω => ∑ i ∈ s, a i * g i ω) μ :=
    integrable_finsetSum _ fun i hi => (hint i hi).const_mul _
  have hZint : Integrable (fun ω => (∑ i ∈ s, a i * g i ω) ^ (2 / 3 : ℝ)) μ :=
    integrable_rpow_of_integrable hZint1
      (Filter.Eventually.of_forall hZ0) (by norm_num) (by norm_num)
  have hUint : Integrable (fun ω => ∑ i ∈ s, a i ^ (2 / 3 : ℝ) * g i ω ^ (2 / 3 : ℝ)) μ :=
    integrable_finsetSum _ fun i hi => (hint23 i hi).const_mul _
  -- subadditivity, at the fixed exponent
  have hsub : ∀ ω, (∑ i ∈ s, a i * g i ω) ^ (2 / 3 : ℝ)
      ≤ ∑ i ∈ s, a i ^ (2 / 3 : ℝ) * g i ω ^ (2 / 3 : ℝ) := by
    intro ω
    refine le_trans (rpow_sum_le_sum_rpow s (fun i => mul_nonneg (ha i) (hg i ω))
      (by norm_num) (by norm_num)) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    exact Real.mul_rpow (ha i) (hg i ω)
  have hZB : (∫ ω, (∑ i ∈ s, a i * g i ω) ^ (2 / 3 : ℝ) ∂μ)
      ≤ ∑ i ∈ s, a i ^ (2 / 3 : ℝ) * b i := by
    refine le_trans (integral_mono hZint hUint hsub) ?_
    rw [integral_finsetSum _ fun i hi => (hint23 i hi).const_mul _]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hb i hi) (Real.rpow_nonneg (ha i) _)
  -- and the descent, outside it
  have hmain := integral_rpow_le_rpow_of_integral_le (μ := μ)
    (g := fun ω => (∑ i ∈ s, a i * g i ω) ^ (2 / 3 : ℝ)) (q := 3 * q / 2)
    (by linarith) (by linarith)
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hZ0 ω) _) hZint hZB
  refine le_trans (le_of_eq ?_) hmain
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [← Real.rpow_mul (hZ0 ω)]
  congr 1
  ring

/-- **The windows with a per-window bound that grows with the height**: for `0 ≤ q ≤ 2/3`, if
`∫ W_n^{2/3} ≤ B (|n|+1)^{1/4}` for `n ∈ s`, then
`E[(∑_{n ∈ s} 8(1+n²)⁻¹ W_n)^q] ≤ (8^{2/3} B ∑_n w_n (|n|+1)^{1/4})^{3q/2}`, `w_n = (1+n²)^{-2/3}`.
The chaos estimate's factor `(⌈harperWindowLevel cr |n|⌉₊ + 1)²` is of this form
(`RMF.exists_const_harperWindowLevel_add_two_le`), and the weight sum converges by
`RMF.summable_shiftWeight_mul_abs_add_one_rpow` because it is met at the fixed exponent `2/3`, where
the hypothesis `5/8 < q` is a numeral. -/
theorem integral_rpow_windowSum_le_of_two_thirds_growth
    {μ : Measure Ω} [IsProbabilityMeasure μ] (s : Finset ℤ)
    {g : ℤ → Ω → ℝ} {B q : ℝ} (hg : ∀ n ω, 0 ≤ g n ω) (hint : ∀ n ∈ s, Integrable (g n) μ)
    (hB0 : 0 ≤ B)
    (hb : ∀ n ∈ s, (∫ ω, g n ω ^ (2 / 3 : ℝ) ∂μ) ≤ B * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
    (hq0 : 0 ≤ q) (hq : q ≤ 2 / 3) :
    (∫ ω, (∑ n ∈ s, 8 / (1 + (n : ℝ) ^ 2) * g n ω) ^ q ∂μ)
      ≤ ((8 : ℝ) ^ (2 / 3 : ℝ)
            * (∑' n : ℤ, shiftWeight (2 / 3) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * B)
          ^ (3 * q / 2) := by
  classical
  have hden : ∀ n : ℤ, (0 : ℝ) < 1 + (n : ℝ) ^ 2 := fun n => by positivity
  have ha : ∀ n : ℤ, (0 : ℝ) ≤ 8 / (1 + (n : ℝ) ^ 2) := fun n => by positivity
  have hpow : ∀ n : ℤ, (0 : ℝ) ≤ (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := fun n =>
    Real.rpow_nonneg (by positivity) _
  have hsum := summable_shiftWeight_mul_abs_add_one_rpow (q := 2 / 3) (by norm_num)
  have hw : ∀ n : ℤ, (8 / (1 + (n : ℝ) ^ 2)) ^ (2 / 3 : ℝ)
      = (8 : ℝ) ^ (2 / 3 : ℝ) * shiftWeight (2 / 3) n := by
    intro n
    rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 (hden n).le),
      Real.inv_rpow (hden n).le, shiftWeight, Real.rpow_neg (hden n).le]
  refine le_trans (integral_rpow_weightedSum_le_of_two_thirds s
    (b := fun n => B * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) ha hg hint hb hq0 hq) ?_
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg (ha n) _) (mul_nonneg hB0 (hpow n))) ?_ (by linarith)
  have hstep : ∑ n ∈ s, (8 / (1 + (n : ℝ) ^ 2)) ^ (2 / 3 : ℝ)
        * (B * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
      = (8 : ℝ) ^ (2 / 3 : ℝ)
        * (∑ n ∈ s, shiftWeight (2 / 3) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4)) * B := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by rw [hw n]; ring
  rw [hstep]
  have hle : (∑ n ∈ s, shiftWeight (2 / 3) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4))
      ≤ ∑' n : ℤ, shiftWeight (2 / 3) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
    hsum.sum_le_tsum s fun n _ => mul_nonneg (shiftWeight_nonneg _ n) (hpow n)
  have h80 : (0 : ℝ) ≤ (8 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle h80) hB0

/-! ### The instantiation

Everything above takes the per-window bound as a hypothesis.  Supplying it is the chaos estimate,
whose two `n`-dependent pieces are exactly the two `RMF/Probability/StrongScales.lean` facts. -/

/-- `⌈w⌉₊ + 1 ≤ w + 2`. -/
private lemma ceil_add_one_le {w : ℝ} (hw : 0 ≤ w) : ((⌈w⌉₊ : ℕ) : ℝ) + 1 ≤ w + 2 := by
  linarith [Nat.ceil_lt_add_one hw]

/-- **The small-`q` bound on the windows `|n| ≤ (log log x)²`**: for `0 ≤ q ≤ 2/3`,
`E[(∑_n 8(1+n²)⁻¹·chaosWindowShift x σ n)^q] ≤ (C·(1 + ⅓√(m/4))^{-2/3})^{3q/2}`, where
`m = harperBlockCount D₀ x`; `D₀`, `x₀`, `C` do not depend on `Y`, `ν`, `x`, `σ`, `η`, `q`, `s`.
The target is read at `2/3`, which costs at most `3^{2/3}` when `q ≤ 2/3`.  The per-window bound
is `RMF.exists_const_integral_chaosWindowShift_rpow_le_int_rademacher` at `2/3`, its height
hypothesis `RMF.exists_threshold_harperWindowLevel_le` at `k = 2`. -/
theorem exists_const_integral_rpow_windowSum_chaos_le_rademacher (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (d : ℕ) (hE₁ : 10 * E₀ ≤ Real.exp d) :
    ∃ (D₀ : ℕ) (x₀ C : ℝ), 0 < C ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ η q : ℝ) (s : Finset ℤ), x₀ ≤ x → 0 ≤ σ → 0 ≤ η → η ≤ E₀ →
          |σ| * Real.log x ≤ η → 0 ≤ q → q ≤ 2 / 3 →
          (∀ n ∈ s, |(n : ℝ)| ≤ Real.log (Real.log x) ^ 2) →
          (∫ ω, (∑ n ∈ s, 8 / (1 + (n : ℝ) ^ 2)
              * chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω)
                ^ q ∂ν)
            ≤ (C * (1 + (1 - 2 / 3) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
                  ^ (-(2 / 3) : ℝ)) ^ (3 * q / 2) := by
  classical
  obtain ⟨D₀, x₁, C₁, cr, hC₁, hcr, H⟩ :=
    exists_const_integral_chaosWindowShift_rpow_le_int_rademacher (Ω := Ω) E₀ hE₀ d hE₁
  obtain ⟨A, hA0, hA⟩ := exists_const_harperWindowLevel_add_two_le hcr
  obtain ⟨Λ, hΛ1, hΛ⟩ := exists_threshold_harperWindowLevel_le 2 hcr
  set W : ℝ := ∑' n : ℤ, shiftWeight (2 / 3) n * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) with hWdef
  have hW0 : 0 ≤ W := by
    refine tsum_nonneg fun n => mul_nonneg (shiftWeight_nonneg _ n) ?_
    exact Real.rpow_nonneg (by positivity) _
  refine ⟨D₀, max (max x₁ 2) (Real.exp (Real.exp Λ)),
    (8 : ℝ) ^ (2 / 3 : ℝ) * W * (C₁ * A ^ 2) + 1, by positivity, ?_⟩
  intro Y ν hY x σ η q s hx hσ hη hηE hση hq0 hq hs
  haveI := hY.isProbabilityMeasure
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_right x₁ 2) (le_max_left _ _)) hx
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left x₁ 2) (le_max_left _ _)) hx
  have hxΛ : Real.exp (Real.exp Λ) ≤ x := le_trans (le_max_right _ _) hx
  -- `ℓogℓog x ≥ Λ`, so the height condition holds across the whole of `s`
  have hLL : Λ ≤ Real.log (Real.log x) := by
    have h1 : Real.exp Λ ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hxΛ
      rwa [Real.log_exp] at this
    have := Real.log_le_log (Real.exp_pos Λ) h1
    rwa [Real.log_exp] at this
  have hσ0 : (0 : ℝ) < 1 / 2 + σ := by linarith
  set T : ℝ := (1 + (1 - 2 / 3) * Real.sqrt ((harperBlockCount D₀ x / 4 : ℕ) : ℝ))
    ^ (-(2 / 3) : ℝ) with hTdef
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  -- the per-window bound, at the fixed exponent `2/3`
  have hb : ∀ n ∈ s, (∫ ω, chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω)
        x σ ((n : ℝ)) ω ^ (2 / 3 : ℝ) ∂ν)
      ≤ (C₁ * A ^ 2 * T) * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
    intro n hn
    have habs : (0 : ℝ) ≤ |(n : ℝ)| := abs_nonneg _
    have hlvl : harperWindowLevel cr |(n : ℝ)| ≤ Real.log (Real.log x) / 3 :=
      hΛ _ _ hLL habs (hs n hn)
    have hmain := H Y ν hY x σ η (2 / 3) n hx1 hσ hη hηE hση (by norm_num) (by norm_num) hlvl
    rw [← hTdef] at hmain
    have hce := ceil_add_one_le (harperWindowLevel_nonneg cr |(n : ℝ)|)
    have hAle := hA |(n : ℝ)| habs
    have hnn : (0 : ℝ) ≤ ((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1 := by positivity
    have hsq : (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
        ≤ (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2 :=
      pow_le_pow_left₀ hnn (le_trans hce hAle) 2
    have hid : (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2
        = A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by
      rw [mul_pow, ← Real.rpow_natCast ((|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hkey : C₁ * (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
        ≤ C₁ * A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) :=
      calc C₁ * (((⌈harperWindowLevel cr |(n : ℝ)|⌉₊ : ℕ) : ℝ) + 1) ^ 2
          ≤ C₁ * (A * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 8)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hC₁.le
        _ = C₁ * A ^ 2 * (|(n : ℝ)| + 1) ^ ((1 : ℝ) / 4) := by rw [hid]; ring
    exact le_trans hmain
      (le_of_le_of_eq (mul_le_mul_of_nonneg_right hkey hT0) (by ring))
  -- the descent
  have hstep := integral_rpow_windowSum_le_of_two_thirds_growth (μ := ν) s
    (g := fun n ω =>
      chaosWindowShift (fun ω => squarefreeExtension fun p => Y p ω) x σ ((n : ℝ)) ω)
    (B := C₁ * A ^ 2 * T)
    (fun n ω => chaosWindowShift_nonneg hx2 σ ((n : ℝ)) ω)
    (fun n _ => integrable_chaosWindowShift_rademacher hY x σ ((n : ℝ)) hσ0)
    (by positivity) hb hq0 hq
  refine le_trans hstep (Real.rpow_le_rpow (by positivity) ?_ (by linarith))
  have hWC : (8 : ℝ) ^ (2 / 3 : ℝ) * W * (C₁ * A ^ 2 * T)
      = ((8 : ℝ) ^ (2 / 3 : ℝ) * W * (C₁ * A ^ 2)) * T := by ring
  rw [hWC]
  exact mul_le_mul_of_nonneg_right (by linarith) hT0

/-! ### From the set integral to the window sum

`{t : 1 < |t| ≤ M}` is covered by the unit windows `(n, n+1]` with `n ∈ RMF.midWindows M`, so a
nonnegative integrand's set integral over it is at most the sum of its window integrals: the
windows are pairwise disjoint (`RMF.pairwise_disjoint_Ioc_intCast`), so that is an equality on
their union and monotonicity onto it.  Every window in the range sits at height `≤ M + 1`, which
is what the chaos estimate's height hypothesis is checked against. -/

/-- The unit windows meeting `1 < |t| ≤ M`: `n ∈ [-M-1, -2] ∪ [1, M-1]`. -/
noncomputable def midWindows (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ) - 1) (-2) ∪ Finset.Ico 1 (M : ℤ)

/-- Every window of `RMF.midWindows M` sits at height at most `M + 1`. -/
lemma abs_le_of_mem_midWindows {M : ℕ} {n : ℤ} (hn : n ∈ midWindows M) :
    |(n : ℝ)| ≤ (M : ℝ) + 1 := by
  rw [midWindows, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico] at hn
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : -(M : ℝ) - 1 ≤ (n : ℝ) := by exact_mod_cast h1
    have h2' : (n : ℝ) ≤ -2 := by exact_mod_cast h2
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h2' : (n : ℝ) < (M : ℝ) := by exact_mod_cast h2
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The covering.**  `t` lies in the window `(⌈t⌉ - 1, ⌈t⌉]`, and that window is one of
`RMF.midWindows M` whenever `1 < |t| ≤ M`. -/
lemma mid_subset_iUnion_midWindows (M : ℕ) :
    {t : ℝ | 1 < |t| ∧ |t| ≤ (M : ℝ)}
      ⊆ ⋃ n ∈ midWindows M, Set.Ioc ((n : ℝ)) ((n : ℝ) + 1) := by
  rintro t ⟨ht1, ht2⟩
  have hlow : ((⌈t⌉ : ℤ) : ℝ) - 1 < t := by linarith [Int.ceil_lt_add_one t]
  have hhigh : t ≤ ((⌈t⌉ : ℤ) : ℝ) := Int.le_ceil t
  refine Set.mem_iUnion₂.2 ⟨⌈t⌉ - 1, ?_, ?_⟩
  · rw [midWindows, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
    rcases le_total t 0 with hneg | hpos
    · rw [abs_of_nonpos hneg] at ht1 ht2
      refine Or.inl ⟨?_, ?_⟩
      · have hM : ((-(M : ℤ) : ℤ) : ℝ) ≤ ((⌈t⌉ : ℤ) : ℝ) := by push_cast; linarith
        have : (-(M : ℤ)) ≤ ⌈t⌉ := by exact_mod_cast hM
        omega
      · have : ⌈t⌉ ≤ -1 := Int.ceil_le.2 (by push_cast; linarith)
        omega
    · rw [abs_of_nonneg hpos] at ht1 ht2
      refine Or.inr ⟨?_, ?_⟩
      · have : (1 : ℤ) < ⌈t⌉ := Int.lt_ceil.2 (by push_cast; linarith)
        omega
      · have : ⌈t⌉ ≤ (M : ℤ) := Int.ceil_le.2 (by push_cast; linarith)
        omega
  · refine ⟨?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith

/-- **A covered set integral is at most the sum over the windows**, for a nonnegative integrand. -/
lemma setIntegral_le_sum_window_of_cover {S : Set ℝ} (s : Finset ℤ)
    (hcover : S ⊆ ⋃ n ∈ s, Set.Ioc ((n : ℝ)) ((n : ℝ) + 1))
    {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t)
    (hint : ∀ n ∈ s, IntegrableOn f (Set.Ioc ((n : ℝ)) ((n : ℝ) + 1))) :
    (∫ t in S, f t) ≤ ∑ n ∈ s, ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), f t := by
  have hUint : IntegrableOn f (⋃ n ∈ s, Set.Ioc ((n : ℝ)) ((n : ℝ) + 1)) :=
    integrableOn_finset_iUnion.2 hint
  have hstep : (∫ t in S, f t) ≤ ∫ t in ⋃ n ∈ s, Set.Ioc ((n : ℝ)) ((n : ℝ) + 1), f t :=
    setIntegral_mono_set hUint (Filter.Eventually.of_forall hf0)
      (Filter.Eventually.of_forall hcover)
  refine le_of_le_of_eq hstep ?_
  exact integral_biUnion_finset s (fun n _ => measurableSet_Ioc)
    (fun m _ n _ hmn => pairwise_disjoint_Ioc_intCast hmn) hint

omit [MeasurableSpace Ω] in
/-- **The window integral is the chaos on that window.**  `RMF.chaosWindowShift` is the same
quantity, written as an `intervalIntegral` at `RMF.shiftLine`. -/
lemma chaosWindowShift_eq_window {X : ℕ → Ω → ℂ} (x σ : ℝ) (ω : Ω) (n : ℤ) :
    chaosWindowShift (fun ω => squarefreeExtension fun p => X p ω) x σ ((n : ℝ)) ω
      = (Real.log x)⁻¹ * ∫ t in Set.Ioc ((n : ℝ)) ((n : ℝ) + 1),
          lineSqOf (1 / 2 + σ) (fun ω => squarefreeExtension fun p => X p ω) (⌊x⌋₊ + 1) ω t := by
  rw [chaosWindowShift, intervalIntegral.integral_of_le (by linarith)]
  simp only [lineSqOf, shiftLine]

end RMF
