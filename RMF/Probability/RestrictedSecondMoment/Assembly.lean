/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedSecondMoment.Ranges
import RMF.Probability.RestrictedSecondMoment.RangeNumerals

/-!
# Key Proposition 5: Harper's data and the assembly

Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654), proof of Key
Proposition 5.  The last of the files `Drift.lean`, `Ranges.lean`, `Assembly.lean` in this
directory: Harper's block data (`RMF.harperTheta`, `RMF.harperN`, `RMF.harperBarrierTop`), the
display's hypotheses discharged, the bridges between the ranges' shapes, the tilt cutoffs, the four
range bounds at Harper's tube, and Key Proposition 5 in envelope form
(`RMF.integral_sq_setIntegral_indicator_normSq_harper_le`,
`RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges`).  The instantiation at Harper's
numeric data is in `RMF/Probability/RestrictedSecondMoment.lean`.
-/

set_option linter.style.longFile 2900

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### Harper's data

His blocks are indexed downward: `L(t)` (p. 49) constrains
`∏_{l=j}^{⌊\log\log x⌋-B-2}|I_l(1/2+4V/\log x+it)|` for every
`⌊\log V⌋ + 3 ≤ j ≤ \log\log x - B - 2`, with `I_l` the Euler factor over the primes at scale
`\log x/e^{l+1}`.  Ours run upward, so `m + θ = \log\log x - j - 1` and

* `θ = \{\log\log x\} + B + 1`; the fractional part is forced, since `m` and `j` are integers;
* `N = ⌊\log\log x⌋ - B - 2`, so that `\text{blockScale }θ\,(N+1) = x` exactly;
* `b = N - ⌊\log V⌋ - 3`, where the barrier stops, strictly below `N`, which is why the chain
  carries the two separately;
* `T ⊆ [-1/2,1/2]`, his set of heights.

`θ ≥ 125`, which every barrier estimate here assumes, is then `B ≥ 124`. -/

/-- Harper's `θ`: `\log\log x - ⌊\log\log x⌋₊ + B + 1`, the fractional part of `\log\log x` plus
`B + 1` when `\log\log x ≥ 0`. -/
noncomputable def harperTheta (B : ℕ) (x : ℝ) : ℝ :=
  Real.log (Real.log x) - (⌊Real.log (Real.log x)⌋₊ : ℝ) + (B : ℝ) + 1

/-- Harper's top block index: `⌊\log\log x⌋ - B - 2`. -/
noncomputable def harperN (B : ℕ) (x : ℝ) : ℕ := ⌊Real.log (Real.log x)⌋₊ - B - 2

lemma harperTheta_lt (B : ℕ) (x : ℝ) : harperTheta B x < (B : ℝ) + 2 := by
  have := Nat.lt_floor_add_one (Real.log (Real.log x))
  rw [harperTheta]
  linarith

lemma le_harperTheta {B : ℕ} {x : ℝ} (hx : 0 ≤ Real.log (Real.log x)) :
    (B : ℝ) + 1 ≤ harperTheta B x := by
  have := Nat.floor_le hx
  rw [harperTheta]
  linarith

/-- **`θ ≥ 125` is `B ≥ 124`.** -/
lemma harperTheta_ge {B : ℕ} {x : ℝ} (hB : 124 ≤ B) (hx : 0 ≤ Real.log (Real.log x)) :
    (125 : ℝ) ≤ harperTheta B x := by
  have hB' : (124 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  linarith [le_harperTheta (B := B) (x := x) hx]

/-- **The index arithmetic.**  `N + 1 + θ = \log\log x`, on the nose — which is what makes the top
block scale exactly `x`. -/
lemma harperN_add_harperTheta {B : ℕ} {x : ℝ}
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x)) :
    (harperN B x : ℝ) + 1 + harperTheta B x = Real.log (Real.log x) := by
  have hfl : (B : ℝ) + 2 ≤ (⌊Real.log (Real.log x)⌋₊ : ℝ) := by
    have h : B + 2 ≤ ⌊Real.log (Real.log x)⌋₊ :=
      Nat.le_floor (by push_cast; linarith)
    have : ((B + 2 : ℕ) : ℝ) ≤ (⌊Real.log (Real.log x)⌋₊ : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hflN : B + 2 ≤ ⌊Real.log (Real.log x)⌋₊ := by exact_mod_cast hfl
  have hcast : (harperN B x : ℝ) = (⌊Real.log (Real.log x)⌋₊ : ℝ) - (B : ℝ) - 2 := by
    rw [harperN]
    have : ⌊Real.log (Real.log x)⌋₊ - B - 2 + (B + 2) = ⌊Real.log (Real.log x)⌋₊ := by omega
    have hc : ((⌊Real.log (Real.log x)⌋₊ - B - 2 : ℕ) : ℝ) + ((B + 2 : ℕ) : ℝ)
        = (⌊Real.log (Real.log x)⌋₊ : ℝ) := by
      rw [← Nat.cast_add, this]
    push_cast at hc
    linarith
  rw [hcast, harperTheta]
  ring

/-- **The top block scale is `x`.**  `\text{blockScale }θ\,(N+1) = x`, exactly. -/
lemma blockScale_harperN_succ {B : ℕ} {x : ℝ} (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x)) :
    blockScale (harperTheta B x) (harperN B x + 1) = x := by
  have hlog : 0 < Real.log x := Real.log_pos hx1
  rw [blockScale]
  have hidx : ((harperN B x + 1 : ℕ) : ℝ) + harperTheta B x = Real.log (Real.log x) := by
    push_cast
    linarith [harperN_add_harperTheta (B := B) (x := x) hx]
  rw [hidx, Real.exp_log hlog, Real.exp_log (by linarith : (0 : ℝ) < x)]

/-- Harper's barrier top: the largest block index his `L(t)` constrains, `N - ⌊\log V⌋ - 3`.
Strictly below `RMF.harperN` — which is exactly why the chain carries the barrier's range and the
Euler product's top as separate indices. -/
noncomputable def harperBarrierTop (B : ℕ) (V x : ℝ) : ℕ :=
  harperN B x - ⌊Real.log V⌋₊ - 3

lemma harperBarrierTop_le (B : ℕ) (V x : ℝ) : harperBarrierTop B V x ≤ harperN B x := by
  rw [harperBarrierTop]
  omega

/-! ### The hypotheses of the display, discharged

`RMF.exists_measure_barrier_inter_display_le` carries about twenty hypotheses.  Most are choices,
made here: the envelope holds at every block once the offset is large enough, `r` is a function
of `τ` alone, and `d` a function of `V` alone. -/

/-- **The pair envelope, from the block offset alone**: the `henvc` hypothesis of
`RMF.exists_measure_barrier_inter_display_le`, at every block once `RMF.blockOffsetThreshold ≤ ϑ`,
with no hypothesis on `a`, `m` or `x`.  `RMF.envelope_of_le` is the same budget with
`\min\{a, m+1\}` in place of `RMF.boxEnvelope`'s linear term; at `a = m+1` the two differ by
`RMF.blockSlope 125 - 2 ≥ 18` (`RMF.twenty_le_blockSlope`). -/
lemma boxEnvelope_pair_le {ϑ : ℝ} (hϑ : blockOffsetThreshold ≤ ϑ) (m : ℕ) :
    boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
        + blockWindow m + blockWindow m + 13
      ≤ 1 / 40 * Real.sqrt (Real.log (blockScale ϑ (m + 1))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB : (20 : ℝ) ≤ blockSlope 125 := twenty_le_blockSlope 125
  have hW : blockWindow m ≤ 1 := by
    rw [blockWindow, div_le_one (by positivity)]
    nlinarith
  have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Real.log_le_log (by exact_mod_cast hm) (by linarith)
  have henv := envelope_of_le (ϑ := ϑ) (a := (m : ℝ) + 1) (m := m) hϑ (by linarith)
  rw [min_self] at henv
  simp only [boxEnvelope]
  push_cast
  linarith

/-- **The display's shift**, `r = ⌈\log(2/τ)⌉`, the number of blocks it drops.  `e^r ≥ 2/τ` turns
the shift condition `Tsh ≤ τe^{r+θ}` into a condition on `θ` alone.  It must not be larger: the
middle range's chain also drops about `\log(1/τ)` blocks (`k < r` in
`RMF.setIntegral_normSq_pair_middle_envelope_le`), and at `⌈2\log(2/τ)⌉` the total drop, about
`3\log(1/τ)`, reaches `Λ` at the bottom of the outer range. -/
noncomputable def harperR (τ : ℝ) : ℕ := ⌈Real.log (2 / τ)⌉₊

lemma log_le_harperR (τ : ℝ) : Real.log (2 / τ) ≤ (harperR τ : ℝ) := Nat.le_ceil _

/-- The logarithm is positive on `(0,1]`, which is what makes `r ≥ 1`. -/
lemma log_two_div_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : 0 < Real.log (2 / τ) := by
  refine Real.log_pos ?_
  rw [lt_div_iff₀ hτ0]
  linarith

lemma one_le_harperR {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : 1 ≤ harperR τ :=
  Nat.ceil_pos.2 (by linarith [log_two_div_pos hτ0 hτ1])

/-- **`r ≤ \log(2/τ) + 1`**, which clears the display's `(r : ℝ) ≤ 2\log(2/|t-u|) + 1` with a
whole `\log(2/τ)` to spare — the spare is what keeps the two shifts from compounding past the
block count. -/
lemma harperR_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (harperR τ : ℝ) ≤ 2 * Real.log (2 / τ) + 1 := by
  have hpos := log_two_div_pos hτ0 hτ1
  have h := (Nat.ceil_lt_add_one hpos.le).le
  rw [harperR]
  linarith

/-- **The shift condition, at `r = harperR τ`.**  `τe^{r+θ} ≥ 2e^θ`, uniformly in `τ ∈ (0,1]` —
so the display's `Tsh ≤ τe^{r+θ}` is cleared by `Tsh ≤ 2e^θ`, a condition on `θ` alone. -/
lemma two_mul_exp_le_mul_exp_harperR {τ θ : ℝ} (hτ0 : 0 < τ) :
    2 * Real.exp θ ≤ τ * Real.exp ((harperR τ : ℝ) + θ) := by
  have hd0 : (0 : ℝ) < 2 / τ := by positivity
  have hexp : 2 / τ ≤ Real.exp (harperR τ : ℝ) := by
    have h1 : Real.exp (Real.log (2 / τ)) ≤ Real.exp (harperR τ : ℝ) :=
      Real.exp_le_exp.2 (log_le_harperR τ)
    rwa [Real.exp_log hd0] at h1
  have hmul : τ * ((2 / τ) * Real.exp θ) ≤ τ * (Real.exp (harperR τ : ℝ) * Real.exp θ) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexp (Real.exp_pos θ).le) hτ0.le
  have hid : τ * ((2 / τ) * Real.exp θ) = 2 * Real.exp θ := by
    field_simp
  rw [Real.exp_add]
  linarith [hmul, hid]

/-- **The tilt's drop**, `d = ⌈\log\max(4V, 1)⌉`.  At `σ = 4V/\log x`, `|σ|\log x = 4V`, and
`RMF.sigma_le_one_of_drop` turns this into `|σ|\log x_{N-d+1} ≤ 1`, since `4V ≤ e^d`. -/
noncomputable def harperD (V : ℝ) : ℕ := ⌈Real.log (max (4 * V) 1)⌉₊

lemma le_exp_harperD (V : ℝ) : max (4 * V) 1 ≤ Real.exp (harperD V) := by
  have hmax1 : (1 : ℝ) ≤ max (4 * V) 1 := le_max_right _ _
  have h1 : Real.log (max (4 * V) 1) ≤ ((harperD V : ℕ) : ℝ) := Nat.le_ceil _
  have h2 := Real.exp_le_exp.2 h1
  rwa [Real.exp_log (by linarith : (0 : ℝ) < max (4 * V) 1)] at h2

/-- **The tilt condition, at `d = harperD V`.**  The display's
`|σ|\log(\text{blockScale }θ\,(N-d+1)) ≤ 1`, from the top-scale bound `|σ|\log x_{N+1} ≤ 4V`. -/
lemma sigma_le_one_of_harperD {θ σ V : ℝ} {N : ℕ} (hdN : harperD V ≤ N)
    (hσ : |σ| * Real.log (blockScale θ (N + 1)) ≤ 4 * V) :
    |σ| * Real.log (blockScale θ (N - harperD V + 1)) ≤ 1 :=
  sigma_le_one_of_drop (le_trans (le_max_left _ _) (le_exp_harperD V)) hdN hσ

/-- **`RMF.exists_measure_barrier_inter_harper_data_le` with its block offset named.**  The
offset the display forces is `\max(\mathrm{blockOffsetThreshold}, \log(T_{sh}/2))`: the
envelope's own threshold, and whatever makes the window `T_{sh}` fit.  This is where the `θ₀`
that reaches the denominator's `B₀` is fixed. -/
theorem le_measure_barrier_inter_harper_data_of_display.{u}
    {κ Cst Tsh : ℝ} {n₀ : ℕ} (hTsh : 0 < Tsh)
    (hn₀ : ∀ n : ℕ, n₀ ≤ n →
      4 ≤ n ∧ 4 * Real.log n ^ 20 ≤ (n : ℝ) ∧ 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18))
    (hbound :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m : ℝ) (N r d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < |t - u| → |t - u| ≤ 1 → Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < N - d - r →
            boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
                + blockWindow mm + blockWindow mm + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          (r : ℝ) ≤ 2 * Real.log (2 / |t - u|) + 1 → Λ ≤ 4 * ((N - d - r : ℕ) : ℝ) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a Λ q m V : ℝ) (N : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
        max blockOffsetThreshold (Real.log (Tsh / 2)) ≤ θ → harperR |t - u| + harperD V + 4 ≤ N →
        n₀ ≤ N - harperD V - harperR |t - u| →
        |σ| * Real.log (blockScale θ (N + 1)) ≤ 4 * V →
        0 < |t - u| → |t - u| ≤ 1 →
        (1 : ℝ) ≤ a →
        (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
        1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
        a ≤ m + κ * Real.log (2 / |t - u|) →
        Λ ≤ 4 * ((N - harperD V - harperR |t - u| : ℕ) : ℝ) →
          ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
              (shiftLine σ t) (shiftLine σ u) ν)
            (barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                  localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
              ∩ barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                  localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
            ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  intro Ω' _ Y ν hY θ σ a Λ q m V N t u hf hθ hrdN hn₀N hσ hτ0 hτ1 ha hhf hΛ hq0 hq1
    hm0 hmΛ hmq ham
    hn4
  set r : ℕ := harperR |t - u| with hrdef
  set d : ℕ := harperD V with hddef
  have hϑ : blockOffsetThreshold ≤ θ := le_trans (le_max_left _ _) hθ
  have h125 : (125 : ℝ) ≤ θ := le_trans le_blockOffsetThreshold hϑ
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  -- the shift threshold, from `θ ≥ \log(Tsh/2)`
  have hTsh4 : Tsh ≤ 2 * Real.exp θ := by
    have hlog : Real.log (Tsh / 2) ≤ θ := le_trans (le_max_right _ _) hθ
    have h4 : Tsh / 2 ≤ Real.exp θ := by
      have := Real.exp_le_exp.2 hlog
      rwa [Real.exp_log (by positivity)] at this
    linarith
  -- the two size conditions on the block count
  obtain ⟨-, hbig, hbig2⟩ := hn₀ (N - d - r) (by rw [hddef, hrdef]; omega)
  refine hbound Ω' Y ν hY θ σ a Λ q m N r d t u hf h125
    (one_le_harperR hτ0 hτ1) (by omega) ?_ hτ0 hτ1 ?_ ?_ ha hbig hbig2
    hhf hΛ hq0 hq1 hm0 hmΛ hmq ham (harperR_le hτ0 hτ1) hn4
  · exact sigma_le_one_of_harperD (by omega) hσ
  · exact le_trans hTsh4 (two_mul_exp_le_mul_exp_harperR hτ0)
  · exact fun mm _ => boxEnvelope_pair_le (le_trans hϑ (by linarith)) mm

/-- **The display at Harper's data**: `RMF.exists_measure_barrier_inter_display_le` with the
envelope (`RMF.boxEnvelope_pair_le`), `r = RMF.harperR |t-u|` (`RMF.one_le_harperR`,
`RMF.harperR_le`), the shift threshold (from `θ ≥ θ₀`), the tilt condition at `d = RMF.harperD V`
(`RMF.sigma_le_one_of_harperD`) and the size conditions (`RMF.exists_blockSizeThreshold_of_pos`)
discharged.  The remaining hypotheses are the block count, `1 ≤ a ≤ m + κ\log(2/|t-u|)` with
`m ≤ \min\{√Λ, 1/(1-q)\}`, the envelope `hf`, and `Λ ≤ 4(N-d-r)`. -/
theorem exists_measure_barrier_inter_harper_data_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ (n₀ : ℕ) (θ₀ : ℝ),
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m V : ℝ) (N : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          θ₀ ≤ θ → harperR |t - u| + harperD V + 4 ≤ N →
          n₀ ≤ N - harperD V - harperR |t - u| →
          |σ| * Real.log (blockScale θ (N + 1)) ≤ 4 * V →
          0 < |t - u| → |t - u| ≤ 1 →
          (1 : ℝ) ≤ a →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((N - harperD V - harperR |t - u| : ℕ) : ℝ) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ := exists_measure_barrier_inter_display_le κ hκ
  obtain ⟨n₀, hn₀⟩ := exists_blockSizeThreshold_of_pos (v := (1 : ℝ) / 18) (by norm_num)
  exact ⟨Cst, hCst, n₀, max blockOffsetThreshold (Real.log (Tsh / 2)),
    le_measure_barrier_inter_harper_data_of_display hTsh hn₀ hbound⟩

/-! ### The block count in the outer range

`RMF.exists_measure_barrier_inter_harper_data_le` asks for `Λ ≤ 4(N-d-r)` and `r+d+4 ≤ N`.  Both
are consequences of one computation: at Harper's data the walk is `Λ/3` blocks long, *up to an
absolute additive loss*, and the loss is what forces the `4`.

`N ≥ Λ - B - 3` because `θ < B+2`; `d ≤ \log 4V + 1` because `d = ⌈\log 4V⌉`; and
`r ≤ 2\log 2 + 2Λ/3 + 1` because the outer range is `\log(1/τ) ≤ Λ/3`.  Subtracting,

`N - d - r > Λ/3 - (B + 5 + 2\log 2 + \log 4V)`,

and past `Λ ≥ 12` times that slack the `Λ/3` dominates: `Λ ≤ 4(N-d-r)`. -/

/-- **The additive loss in the block count**, `B + 5 + 2\log 2 + \log(4V)`: in the outer range
`N - d - r > Λ/3 - \text{harperSlack}` (`RMF.harper_block_count`).  It is at least `130` for
`B ≥ 125`. -/
noncomputable def harperSlack (B : ℕ) (V : ℝ) : ℝ :=
  (B : ℝ) + 5 + 2 * Real.log 2 + Real.log (4 * V)

lemma le_harperSlack {B : ℕ} {V : ℝ} (hV : 1 / 4 ≤ V) : 5 ≤ harperSlack B V := by
  have h1 : (1 : ℝ) ≤ 4 * V := by linarith
  have hlog : (0 : ℝ) ≤ Real.log (4 * V) := Real.log_nonneg h1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  rw [harperSlack]
  linarith

/-- **`N ≥ Λ - B - 3`**, because `θ < B + 2` and `N + 1 + θ = Λ`. -/
lemma harperN_ge {B : ℕ} {x : ℝ} (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x)) :
    Real.log (Real.log x) - (B : ℝ) - 3 ≤ (harperN B x : ℝ) := by
  linarith [harperN_add_harperTheta (B := B) (x := x) hx, harperTheta_lt B x]

/-- **`d ≤ \log 4V + 1`**, the drop being a ceiling. -/
lemma harperD_le {V : ℝ} (hV : 1 / 4 ≤ V) : (harperD V : ℝ) ≤ Real.log (4 * V) + 1 := by
  have h1 : (1 : ℝ) ≤ 4 * V := by linarith
  have hmax : max (4 * V) 1 = 4 * V := max_eq_left h1
  rw [harperD, hmax]
  exact (Nat.ceil_lt_add_one (Real.log_nonneg h1)).le

/-- **`\log(2/τ) = \log 2 + \log(1/τ)`**, the form in which the outer range is stated. -/
lemma log_two_div_eq {τ : ℝ} (hτ0 : 0 < τ) :
    Real.log (2 / τ) = Real.log 2 + Real.log (1 / τ) := by
  rw [Real.log_div (by norm_num) hτ0.ne', Real.log_div one_ne_zero hτ0.ne', Real.log_one]
  ring

/-- **The block count at Harper's data**: `r + d + 4 ≤ N` and
`Λ/3 - \text{harperSlack} ≤ N - d - r`, from the one threshold `Λ ≥ 12\,\text{harperSlack}`.
`hτL` is the outer range, `|t-u| > (\log x)^{-1/3}`, i.e. `\log(1/τ) ≤ Λ/3`; the threshold is a
condition on `x` once `B` and `V` are fixed. -/
lemma harper_block_count {B : ℕ} {V x τ : ℝ} (hV : 1 / 4 ≤ V) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hτL : Real.log (1 / τ) ≤ Real.log (Real.log x) / 3)
    (hΛ : 12 * harperSlack B V ≤ Real.log (Real.log x)) :
    harperR τ + harperD V + 4 ≤ harperN B x
      ∧ Real.log (Real.log x) / 3 - harperSlack B V
          ≤ (harperN B x : ℝ) - (harperD V : ℝ) - (harperR τ : ℝ) := by
  set Λ : ℝ := Real.log (Real.log x) with hΛdef
  set S : ℝ := harperSlack B V with hSdef
  have hS5 : (5 : ℝ) ≤ S := le_harperSlack hV
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hBS : (B : ℝ) + 5 ≤ S := by
    have hlog : (0 : ℝ) ≤ Real.log (4 * V) := Real.log_nonneg (by linarith)
    rw [hSdef, harperSlack]
    linarith
  have hNge : Λ - (B : ℝ) - 3 ≤ (harperN B x : ℝ) := harperN_ge (by linarith)
  have hDle : (harperD V : ℝ) ≤ Real.log (4 * V) + 1 := harperD_le hV
  have hRle : (harperR τ : ℝ) ≤ Real.log 2 + Λ / 3 + 1 := by
    have hpos := log_two_div_pos hτ0 hτ1
    have h := (Nat.ceil_lt_add_one hpos.le).le
    have heq := log_two_div_eq hτ0
    rw [harperR]
    linarith
  -- `N - d - r > Λ/3 - S`, in the reals
  have hlogV : Real.log (4 * V) = S - (B : ℝ) - 5 - 2 * Real.log 2 := by
    rw [hSdef, harperSlack]
    ring
  have hcore : Λ / 3 - S ≤ (harperN B x : ℝ) - (harperD V : ℝ) - (harperR τ : ℝ) := by
    rw [hlogV] at hDle
    linarith
  -- so the count clears `4`, and the ℕ subtraction is honest
  have hnat : harperR τ + harperD V + 4 ≤ harperN B x := by
    have hR : ((harperR τ + harperD V + 4 : ℕ) : ℝ) ≤ ((harperN B x : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  exact ⟨hnat, hcore⟩

/-! ### The two bridges into the assembly

`RMF.integral_sq_setIntegral_indicator_normSq_le_of_cases` asks for its pointwise bound as
`P~₂(L t ∩ L u)·E‖F_t‖²‖F_u‖²`; every range bound in this file produces
`∫_{L t ∩ L u}‖F_t‖²‖F_u‖²`.  Those are *equal*, so the restatement below costs nothing.

And the chain's `hbar` asks for the barrier of the block family **started at `r`**, while the
outer-range barrier bound is for an unshifted one.  Those are the same family too:
`RMF.blockScale_add` says advancing the index is advancing the offset, so the shifted pair family is
the pair family at `θ + r` — which is why the display's envelope hypothesis is stated at
`blockScale (θ + r)` and not at `blockScale θ`.  `RMF.blockCutoff_add` then says the tilt does not
move, so the shift is free on both sides. -/

/-- **`E[X²]` from the range bounds, in the form the ranges produce**:
`RMF.integral_sq_setIntegral_indicator_normSq_le_of_cases` with the pointwise hypotheses stated as
set integrals over `L t ∩ L u`, as `RMF.setIntegral_normSq_pair_middle_envelope_le`,
`RMF.setIntegral_normSq_pair_far_envelope_le` and `RMF.setIntegral_normSq_pair_crude_le` deliver.
`RMF.IsSteinhausRMF.setIntegral_normSq_mul_normSq_eq` is an equality, so nothing is lost. -/
theorem integral_sq_setIntegral_indicator_normSq_le_of_setIntegral {Ω' : Type*}
    [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'}
    (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc)
    (hD : 0 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcrude : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C * min Lc (1 / |t - u|))
    (hout : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ D / (|t - u| * Real.log (2 / |t - u|) ^ 2)) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) := by
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hre : ∀ t : ℝ, (0 : ℝ) < (shiftLine σ t).re := by
    intro t
    rw [re_shiftLine]
    linarith
  have hbridge : ∀ t u : ℝ,
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        = ∫ ω in L t ∩ L u,
            ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν := fun t u =>
    (hf.setIntegral_normSq_mul_normSq_eq y (hre t) (hre u) ((hLmeas t).inter (hLmeas u))).symm
  refine integral_sq_setIntegral_indicator_normSq_le_of_cases hY y hσ L hLmeas hSmeas hTm hTsub
    hC hLc hD hε0 hε1 (fun t ht u hu htu hτ => ?_) (fun t ht u hu htu hτ => ?_)
  · rw [hbridge t u]
    exact hcrude t ht u hu htu hτ
  · rw [hbridge t u]
    exact hout t ht u hu htu hτ

/-! ### The chain's two shift hypotheses

`RMF.setIntegral_normSq_pair_middle_le` carries `hAR`, the barrier inside a shifted one, and
`hbar`, a bound on the shifted one's tilted measure; both are supplied in this file.  The shift is
free: advancing the block index by `r` is advancing the offset by `r`, and the tilt does not move
(`RMF.blockCutoff_add`), so the display applies verbatim at `θ + r`, `N - r`.
-/

/-- **The chain's level and the shift's widened height are the same number.**
`RMF.shiftLevel a r hf = 2a + r + Br + |hf r| + 10\log(1+r)` and
`RMF.shiftedHeight a B hf r = 2a + (B+1)r + |hf r| + 10\log(1+r)`. -/
lemma shiftLevel_eq_shiftedHeight (a : ℝ) (r : ℕ) (hf : ℕ → ℝ) :
    shiftLevel a r hf = shiftedHeight a (blockSlope 125) hf r := by
  rw [shiftLevel, shiftedHeight]
  ring

/-- **`hAR`, supplied.**  The pair barrier over `[1,b]` sits inside the shifted pair barrier over
`[1,b-r]`, at the widened height `RMF.shiftLevel a r hf`.  One coordinate at a time, by
`RMF.freeStart_subset_barrierEvent`: a barrier on `[1,b]` constrains `[r,b]` in particular, and the
increments over a window are differences of two constrained walk values. -/
lemma barrierEventPair_subset_shift {Ω'' : Type*} {Z : ℕ → Ω'' → ℝ × ℝ} {b r : ℕ}
    (hr1 : 1 ≤ r) (hrb : r ≤ b) {a : ℝ} {hf : ℕ → ℝ}
    (hhf : ∀ j, 1 ≤ j → j ≤ b → |hf j| ≤ 10 * Real.log j) :
    barrierEventPair Z b (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
        (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
      ⊆ barrierEventPair (fun m => Z (m + r)) (b - r)
          (fun m => -shiftLevel a r hf - blockSlope 125 * m)
          (fun m => shiftLevel a r hf + m + 10 * Real.log m)
          (fun m => -shiftLevel a r hf - blockSlope 125 * m)
          (fun m => shiftLevel a r hf + m + 10 * Real.log m) := by
  simp only [shiftLevel_eq_shiftedHeight]
  refine Set.inter_subset_inter ?_ ?_
  · exact fun ω hω => freeStart_subset_barrierEvent (X := fun m ω => (Z m ω).1) hrb hhf
      (fun j hjr hjb => hω j (le_trans hr1 hjr) hjb)
  · exact fun ω hω => freeStart_subset_barrierEvent (X := fun m ω => (Z m ω).2) hrb hhf
      (fun j hjr hjb => hω j (le_trans hr1 hjr) hjb)

/-! ### The middle range's split index

The chain splits the Euler product at `x_{k+1}`, where two hypotheses pull in opposite
directions.  With `y = \log(1/τ) - θ`: `h52` reads (5.2) at `v₂(k+1)`, and
`RMF.exp_envelope_splitIndex_le` turns `e^{k+1}` into `e^{-θ}/τ` only when `k+1 ≤ ⌊y⌋`; `hQ`
feeds `RMF.exists_integral_normSq_high_shift_le`, whose (5.1) hypothesis `1/τ ≤ \log N₁`,
`N₁ = ⌊x_{k+1}⌋`, needs `k+1 ≥ ⌈y⌉`.  Both hold only for integer `y`, so one is paid for:
`hQ`'s is a genuine hypothesis of (5.1), while `h52`'s only costs a larger `X`.

Two blocks, not one: `⌈y⌉` gives `\log x_{k+1} > 1/τ` only strictly, and the floor in `N₁` costs
`\log 2`; one more block gives `\log x_{k+1} ≥ e/τ`, and `e/τ - \log 2 ≥ 1/τ` for `τ ≤ 1`.  So
`k + 1 = RMF.splitIndex θ m τ + 2`, and (5.2) is read two blocks up, at `e` per block
(`RMF.exp_envelope_succ_le`). -/

/-- **Moving the envelope up one block costs `e`.**  `h(j) = -2\log j` is antitone, so the whole
increment is the `+1` in the exponent. -/
lemma exp_envelope_succ_le (a : ℝ) (j : ℕ) :
    Real.exp (a + ((j + 1 : ℕ) : ℝ) + harperHf (j + 1))
      ≤ Real.exp 1 * Real.exp (a + (j : ℝ) + harperHf j) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hlog : Real.log (j : ℝ) ≤ Real.log ((j : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp
    · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  simp only [harperHf]
  push_cast
  linarith

/-- **The split index is positive in the middle range.**  `\log(1/τ) - θ ≥ \log 2 + θ + 2 ≥ 2`, so
its floor clears `1`; the other half of the minimum is `m ≥ 1`. -/
lemma one_le_splitIndex {θ : ℝ} {m : ℕ} {t : ℝ} (hθ : 0 ≤ θ) (hm1 : 1 ≤ m)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t|)) : 1 ≤ splitIndex θ m t := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor : 1 ≤ ⌊Real.log (1 / |t|) - θ⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  exact le_min hm1 hfloor

/-- **(5.2) at the chain's split index**: `RMF.exp_envelope_splitIndex_sq_le` moved up two
blocks, the `h52` hypothesis of `RMF.setIntegral_normSq_pair_middle_envelope_le` at Harper's tube
`v₂ j = a + j + hf j` and `k = RMF.splitIndex θ m τ + 1`, the split that
`RMF.exists_integral_normSq_high_splitIndex_le` reads.  `X` grows from `4e^{a-θ}` to
`4e²e^{a-θ}`. -/
lemma exp_envelope_splitIndex_add_two_sq_le {θ : ℝ} {m : ℕ} {t : ℝ} (hθ : 0 ≤ θ) (ht : 0 < |t|)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t|))
    (hm : Real.log (2 / |t|) ≤ 2 * (m : ℝ)) (a : ℝ) :
    Real.exp ((fun j : ℕ => a + (j : ℝ) + harperHf j) (splitIndex θ m t + 2)) ^ 2
      ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2
        * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2 := by
  have hbase := exp_envelope_splitIndex_sq_le hθ ht hsmall hm a
  have hidx : splitIndex θ m t + 2 = splitIndex θ m t + 1 + 1 := by omega
  have hchain : Real.exp (a + ((splitIndex θ m t + 2 : ℕ) : ℝ)
        + harperHf (splitIndex θ m t + 2))
      ≤ Real.exp 1 * (Real.exp 1
        * Real.exp (a + (splitIndex θ m t : ℝ) + harperHf (splitIndex θ m t))) := by
    rw [hidx]
    exact le_trans (exp_envelope_succ_le a (splitIndex θ m t + 1))
      (mul_le_mul_of_nonneg_left (exp_envelope_succ_le a (splitIndex θ m t))
        (Real.exp_pos 1).le)
  have h0 : (0 : ℝ) ≤ Real.exp (a + ((splitIndex θ m t + 2 : ℕ) : ℝ)
      + harperHf (splitIndex θ m t + 2)) := (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ h0 hchain 2
  have hmul : (Real.exp 1 ^ 2) ^ 2 * Real.exp (a + (splitIndex θ m t : ℝ)
        + harperHf (splitIndex θ m t)) ^ 2
      ≤ (Real.exp 1 ^ 2) ^ 2 * ((4 * Real.exp (a - θ)) ^ 2
          * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  simp only []
  rw [mul_pow, mul_pow] at hsq
  calc Real.exp (a + ((splitIndex θ m t + 2 : ℕ) : ℝ) + harperHf (splitIndex θ m t + 2)) ^ 2
      ≤ (Real.exp 1 ^ 2) ^ 2 * ((4 * Real.exp (a - θ)) ^ 2
          * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2) := by
        calc Real.exp (a + ((splitIndex θ m t + 2 : ℕ) : ℝ)
              + harperHf (splitIndex θ m t + 2)) ^ 2
            ≤ Real.exp 1 ^ 2 * (Real.exp 1 ^ 2
                * Real.exp (a + (splitIndex θ m t : ℝ)
                    + harperHf (splitIndex θ m t)) ^ 2) := hsq
          _ ≤ (Real.exp 1 ^ 2) ^ 2 * ((4 * Real.exp (a - θ)) ^ 2
                * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2) := by
              rw [← mul_assoc, ← pow_two] at *
              linarith [hmul]
    _ = (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2
          * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2 := by ring

/-! ### The low product, at the split index

`E[P_t] ≪ 1/τ` is the third factor of the p. 53 display and the `hPt` hypothesis of
`RMF.setIntegral_normSq_pair_middle_envelope_le`.  It is Mertens and nothing else:
`RMF.exists_integral_norm_randomEulerProductIco_sq_le` gives `E‖P‖² ≪ \log z` at cutoff `z`, and
`RMF.log_blockScale_splitIndex_le` says the split's scale has `\log x_{j₀} ≤ 1/τ` — which is what
the split index was defined to arrange. -/

/-- **`2 ≤ x_j`**, since `x_j = e^{e^{j+θ}} ≥ e^{e^0} = e`. -/
lemma two_le_blockScale {θ : ℝ} (hθ : 0 ≤ θ) (j : ℕ) : 2 ≤ blockScale θ j := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have h1 : (1 : ℝ) ≤ Real.exp ((j : ℝ) + θ) := by
    rw [Real.one_le_exp_iff]
    linarith
  calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    _ ≤ blockScale θ j := by
        rw [blockScale]
        exact Real.exp_le_exp.2 h1

/-! ### The high product, at the split index

`E[Q] ≪ (τ/σ)²` is the `hQ` hypothesis of `RMF.setIntegral_normSq_pair_middle_envelope_le`, and
`τ/σ = τ\log x/(4V)`: Key Proposition 5's `1/V` comes from `σ`, not from the block grid.

`RMF.exists_integral_normSq_high_shift_le` takes cutoffs `N₁ ≤ M ≤ N₂` and returns
`(\log M/\log N₁)²`.  `N₁` and `N₂` are the ends of the pulled-out product; `M` is free, and is
`⌊e^{1/σ}⌋` rather than a block scale, so that `2σ\log M ≈ 2`.  Then `\log M ≤ 1/σ` and
`\log N₁ ≥ 1/τ`, and the quotient is `τ/σ`.  This needs the floor arm of
`RMF.splitIndex θ m τ = \min\{m, ⌊\log(1/τ)-θ⌋\}` to bind; when `m` binds, `Q` is short, the
heights are in phase over it, and `RMF.exists_integral_normSq_pairIco_le`'s exponent `4` applies.
-/

/-- **`⌊z⌋ > z/2` for `z ≥ 2`.**  Used twice below, to pass between a real cutoff and the natural
number the Euler product is indexed by. -/
lemma half_lt_floor {z : ℝ} (hz : 2 ≤ z) : z / 2 < (⌊z⌋₊ : ℝ) := by
  have h := Nat.sub_one_lt_floor z
  linarith

/-- **The split index's block arithmetic**, shared by
`RMF.exists_integral_normSq_high_splitIndex_le` and its Rademacher twin before they apply their
model's bound.  Law-free and free of `Ω`: arithmetic on `θ`, `σ`, `|t-u|` and the truncations
`⌊x_{j+2}⌋` and `⌊e^{1/σ}⌋`.  The first five conclusions feed the bound, the last two the final
`le_trans`. -/
theorem splitIndex_high_bounds {θ σ t u : ℝ} {m N : ℕ}
    (hθ : 2 ≤ θ) (hσ0 : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hτ0 : 0 < |t - u|) (hτ1 : |t - u| ≤ 1)
    (hfloor : ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ m)
    (hNM : Real.exp ((splitIndex θ m (t - u) : ℝ) + 2 + θ) ≤ 1 / σ)
    (hMN : 1 / σ ≤ Real.log (blockScale θ (N + 1))) :
    (400 : ℝ) ≤ ((⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ : ℕ) : ℝ)
      ∧ ⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ ≤ ⌊Real.exp (1 / σ)⌋₊
      ∧ ⌊Real.exp (1 / σ)⌋₊ ≤ ⌊blockScale θ (N + 1)⌋₊
      ∧ 1 / |t - u|
          ≤ Real.log ((⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ : ℕ) : ℝ)
      ∧ (1 : ℝ) ≤ 2 * σ * Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
      ∧ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
            / Real.log ((⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ : ℕ) : ℝ)
          ≤ |t - u| / σ
      ∧ (0 : ℝ) ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
            / Real.log ((⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ : ℕ) : ℝ) := by
  set j : ℕ := splitIndex θ m (t - u) with hjdef
  set τ : ℝ := |t - u| with hτdef
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hinv1 : (1 : ℝ) ≤ 1 / τ := by
    rw [le_div_iff₀ hτ0]
    linarith
  -- `\log x_{j+2} = e^{j+2+θ} ≥ e⁴ ≥ 9`, so `x_{j+2} ≥ e⁹ ≥ 800`
  have hlogz : Real.log (blockScale θ (j + 2)) = Real.exp ((j : ℝ) + 2 + θ) := by
    rw [log_blockScale]
    push_cast
    ring_nf
  have hinner : (9 : ℝ) ≤ Real.exp ((j : ℝ) + 2 + θ) := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h4 : Real.exp 4 = Real.exp 2 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h9 : (9 : ℝ) ≤ Real.exp 4 := by
      rw [h4]
      nlinarith
    exact le_trans h9 (Real.exp_le_exp.2 (by linarith))
  have hexp9 : (800 : ℝ) ≤ Real.exp 9 := by
    have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he1.le 9
    rw [h9]
    linarith [hpow, (by norm_num : (800 : ℝ) ≤ (2.7 : ℝ) ^ 9)]
  have hz800 : (800 : ℝ) ≤ blockScale θ (j + 2) := by
    refine le_trans hexp9 ?_
    rw [blockScale]
    refine Real.exp_le_exp.2 (le_trans hinner (Real.exp_le_exp.2 ?_))
    push_cast
    linarith
  have hhalf : blockScale θ (j + 2) / 2 < ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) :=
    half_lt_floor (by linarith)
  -- (a) `400 ≤ N₁`
  have h400 : (400 : ℝ) ≤ ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := by linarith
  -- (b) `1/τ ≤ \log N₁`, which is where the floor arm is used
  have hfl : j = ⌊Real.log (1 / τ) - θ⌋₊ := by
    rw [hjdef, splitIndex, min_eq_right hfloor]
  have hgap : Real.log (1 / τ) < (j : ℝ) + 1 + θ := by
    have h := Nat.lt_floor_add_one (Real.log (1 / τ) - θ)
    rw [← hfl] at h
    linarith
  have hlogN₁ : 1 / τ ≤ Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 / τ < Real.exp ((j : ℝ) + 1 + θ) := by
      have h := Real.exp_lt_exp.2 hgap
      rwa [Real.exp_log (by positivity)] at h
    have hsplit : Real.exp ((j : ℝ) + 2 + θ) = Real.exp ((j : ℝ) + 1 + θ) * Real.exp 1 := by
      rw [← Real.exp_add]
      ring_nf
    have h2 : 2 * (1 / τ) ≤ Real.exp ((j : ℝ) + 2 + θ) := by
      rw [hsplit]
      nlinarith [Real.exp_pos ((j : ℝ) + 1 + θ)]
    have h4 : Real.log (blockScale θ (j + 2) / 2)
        ≤ Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hhalf.le
    rw [Real.log_div (blockScale_pos θ (j + 2)).ne' (by norm_num), hlogz] at h4
    linarith
  have hN₁pos : (0 : ℝ) < Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := by linarith
  -- (c), (d): `M = ⌊e^{1/σ}⌋` sits between `N₁` and `N₂`
  have hM3 : (3 : ℝ) ≤ Real.exp (1 / σ) := by
    have h2 : (2 : ℝ) ≤ 1 / σ := by
      rw [le_div_iff₀ hσ0]
      linarith
    linarith [Real.add_one_le_exp (1 / σ)]
  have hhalfM : Real.exp (1 / σ) / 2 < ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) :=
    half_lt_floor (by linarith)
  have hNM' : ⌊blockScale θ (j + 2)⌋₊ ≤ ⌊Real.exp (1 / σ)⌋₊ := by
    refine Nat.floor_le_floor ?_
    rw [← Real.exp_log (blockScale_pos θ (j + 2)), hlogz]
    exact Real.exp_le_exp.2 hNM
  have hMN' : ⌊Real.exp (1 / σ)⌋₊ ≤ ⌊blockScale θ (N + 1)⌋₊ := by
    refine Nat.floor_le_floor ?_
    rw [← Real.exp_log (blockScale_pos θ (N + 1))]
    exact Real.exp_le_exp.2 hMN
  -- (e) `1 ≤ 2σ\log M`, which is what pins `M` at `e^{1/σ}`
  have hlogM_lo : 1 / σ - Real.log 2 ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) := by
    have h4 : Real.log (Real.exp (1 / σ) / 2)
        ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hhalfM.le
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h4
  have hM : (1 : ℝ) ≤ 2 * σ * Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) := by
    have hstep : 2 * σ * (1 / σ - Real.log 2)
        ≤ 2 * σ * Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlogM_lo (by positivity)
    have hid : 2 * σ * (1 / σ - Real.log 2) = 2 - 2 * σ * Real.log 2 := by
      field_simp
    rw [hid] at hstep
    nlinarith
  -- (f) the quotient is `τ/σ`
  have hlogM_hi : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ≤ 1 / σ := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ))
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ Real.exp (1 / σ)))
    rwa [Real.log_exp] at h
  have hlogM0 : (0 : ℝ) ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ 1 / σ := by
      rw [le_div_iff₀ hσ0]
      linarith
    linarith
  have hquot : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
      / Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) ≤ τ / σ := by
    rw [div_le_div_iff₀ hN₁pos hσ0]
    have h1 : (1 : ℝ) ≤ τ * Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlogN₁ hτ0.le
      rw [mul_one_div, div_self hτ0.ne'] at this
      linarith
    have h2 : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) * σ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hlogM_hi hσ0.le
      have hc : 1 / σ * σ = 1 := by field_simp
      linarith
    linarith
  have hquot0 : (0 : ℝ) ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
      / Real.log ((⌊blockScale θ (j + 2)⌋₊ : ℕ) : ℝ) := div_nonneg hlogM0 hN₁pos.le
  exact ⟨h400, hNM', hMN', hlogN₁, hM, hquot, hquot0⟩

/-- **`E[Q] ≪ (τ/σ)²`**, in the regime where the split index is set by `τ` rather than by the top
of the barrier range.

The two hypotheses on `σ` are what place `M` between `N₁` and `N₂`: `e^{j+2+θ} ≤ 1/σ` says the
split is below `M`, and `1/σ ≤ \log x_{N+1}` says `M` is below the top.  At Harper's data
`1/σ = \log x/(4V)`, so the first is the outer range and the second is `V ≥ 1/4`. -/
theorem exists_integral_normSq_high_splitIndex_le :
    ∃ KQ > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (θ σ t u : ℝ) (m N : ℕ), 2 ≤ θ → 0 < σ → σ ≤ 1 / 2 →
        0 < |t - u| → |t - u| ≤ 1 →
        ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ m →
        Real.exp ((splitIndex θ m (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
        1 / σ ≤ Real.log (blockScale θ (N + 1)) →
        (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
                (⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ + 1)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω)
                (⌊blockScale θ (splitIndex θ m (t - u) + 2)⌋₊ + 1)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ KQ * (|t - u| / σ) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_high_shift_le (Ω := Ω)
  refine ⟨K, hK, fun X μ hX θ σ t u m N hθ hσ0 hσhalf hτ0 hτ1 hfloor hNM hMN => ?_⟩
  obtain ⟨h400, hNM', hMN', hlogN₁, hM, hquot, hquot0⟩ :=
    splitIndex_high_bounds hθ hσ0 hσhalf hτ0 hτ1 hfloor hNM hMN
  refine le_trans (hbound X μ hX σ t u _ _ _ hσ0.le hτ0 hτ1 h400 hNM' hMN' hlogN₁ hM) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hquot0 hquot 2) hK.le

/-! ### The primes below `x₀`

`E[P₀(s₁)P₀(s₂)]` is the `hP0` hypothesis of the chain, and it is the one factor that is bounded
by a **constant** rather than by anything depending on `τ`, `V` or `x`: `x₀ = e^{e^θ}` and
`θ = \{\log\log x\} + B + 1 < B + 2`, so the whole range `[2, x₀)` is contained in
`[2, e^{e^{B+2}})`, a fixed set of primes once `B` is fixed.

Two such constants are below.  The deterministic `RMF.bottomSupConst` discards the randomness
entirely and uses the a.e. bound `\|F\| ≤ ∏(1-p^{-1/2-σ})^{-1}`, which is off by a tower.  The
moment bound `RMF.bottomConst` is `≈ (\log x₀)⁴` (Mertens, in-phase exponent `4`,
`RMF.exists_integral_normSq_pairIco_le` after splitting off the primes below `401`); it is the one
the Steinhaus chain uses.  `K0` enters only as a factor of `D`, which may depend on `B`, so any
bound depending on `B` alone closes the chain. -/

/-- `blockScale` is monotone in the offset as well as the index. -/
lemma blockScale_mono_offset {θ ϑ : ℝ} (h : θ ≤ ϑ) (j : ℕ) :
    blockScale θ j ≤ blockScale ϑ j := by
  rw [blockScale, blockScale]
  exact Real.exp_le_exp.2 (Real.exp_le_exp.2 (by linarith))

/-- On the line `\text{Re}\,s = 1/2 + σ` with `σ ≥ 0`, each local factor is dominated by the one at
`σ = 0`. -/
lemma norm_cpow_neg_le_rpow_half {p : ℕ} (hp : p.Prime) {s : ℂ} {σ : ℝ}
    (hre : s.re = 1 / 2 + σ) (hσ : 0 ≤ σ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, hre]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- And that one is `< 1`, so the local factor is a positive real. -/
lemma rpow_half_lt_one {p : ℕ} (hp : p.Prime) : ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)

/-- **The deterministic constant for the bottom block**, `(∏_{p < ⌊x₀⌋+1}(1 - p^{-1/2})⁻¹)⁴`
with `x₀ = RMF.blockScale ϑ 0`: every Euler factor at its largest.  It bounds the two-point moment
over the primes below `x₀` for the Rademacher function
(`RMF.integral_normSq_pair_bottom_le_rademacher`).  A triple exponential in `ϑ`; the Steinhaus
chain uses the moment bound `RMF.bottomConst`. -/
noncomputable def bottomSupConst (ϑ : ℝ) : ℝ :=
  (∏ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1),
      (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) ^ 4

/-- Every factor of `RMF.bottomSupConst` is at least `1`. -/
lemma one_le_one_sub_rpow_half_inv {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤ (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
  have h1 := rpow_half_lt_one hp
  have h0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  rw [inv_eq_one_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))]
  linarith

/-- And so is any product of them.  Stated over an arbitrary finset because the extension from
`x₀` to the cap runs over a set difference. -/
lemma one_le_prod_one_sub_rpow_half_inv' {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    (1 : ℝ) ≤ ∏ p ∈ t, (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
  calc (1 : ℝ) = ∏ _p ∈ t, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ p ∈ t, (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ :=
        Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => one_le_one_sub_rpow_half_inv (ht p hp))

lemma one_le_prod_one_sub_rpow_half_inv (y : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ Nat.primesBelow y, (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ :=
  one_le_prod_one_sub_rpow_half_inv' fun _ hp => Nat.prime_of_mem_primesBelow hp

lemma one_le_bottomSupConst (ϑ : ℝ) : 1 ≤ bottomSupConst ϑ :=
  one_le_pow₀ (one_le_prod_one_sub_rpow_half_inv _)

/-- **The deterministic bound, transported to the offset cap.**  Two monotonicities: each factor
grows as `σ` falls to `0`, and the index set grows as `θ` rises to `ϑ`. -/
lemma prod_one_sub_norm_inv_le {θ ϑ σ : ℝ} (hθϑ : θ ≤ ϑ) {s : ℂ} (hre : s.re = 1 / 2 + σ)
    (hσ : 0 ≤ σ) :
    ∏ p ∈ Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1), (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹
      ≤ ∏ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1),
          (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
  have hsub : Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1)
      ⊆ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1) :=
    primesBelow_mono (Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono_offset hθϑ 0)))
  calc ∏ p ∈ Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1), (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹
      ≤ ∏ p ∈ Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1),
          (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
        · have hp := Nat.prime_of_mem_primesBelow hp
          have hs : 0 < s.re := by rw [hre]; linarith
          have h1 := norm_prime_cpow_neg_lt_one hp hs
          positivity
        · have hp := Nat.prime_of_mem_primesBelow hp
          have h2 := norm_cpow_neg_le_rpow_half hp hre hσ
          have h3 := rpow_half_lt_one hp
          exact inv_anti₀ (by linarith) (by linarith)
    _ ≤ ∏ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1),
          (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
        rw [← Finset.prod_sdiff hsub]
        have h1 : (1 : ℝ) ≤ ∏ p ∈ Nat.primesBelow (⌊blockScale ϑ 0⌋₊ + 1) \
            Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1),
            (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ :=
          one_le_prod_one_sub_rpow_half_inv' fun p hp =>
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.1 hp).1
        have h2 : (0 : ℝ) ≤ ∏ p ∈ Nat.primesBelow (⌊blockScale θ 0⌋₊ + 1),
            (1 - ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ :=
          le_trans zero_le_one (one_le_prod_one_sub_rpow_half_inv _)
        nlinarith

/-- **The truncation arithmetic behind the far-range pair bound**, shared by
`RMF.exists_setIntegral_normSq_pair_far_le` and its Rademacher twin.

Law-free, and free of `Ω`: everything here is arithmetic on `Θ = 2τ₀ + 7`, on `σ`, and on the two
truncations `⌊e^Θ⌋` and `⌊e^{1/σ}⌋`.  The eight conclusions are what the two consumers pass to
`RMF.setIntegral_normSq_pair_far_envelope_le` and to the `calc` that follows it. -/
theorem far_truncation_bounds {θ σ τ0 t u : ℝ} {N : ℕ}
    (hσ0 : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hτ0 : 0 < |t - u|) (hτ1 : |t - u| ≤ 1)
    (hτ0le : 1 / |t - u| ≤ τ0) (hτ0σ : 2 * τ0 + 7 ≤ 1 / σ)
    (hσN : 1 / σ ≤ Real.log (blockScale θ (N + 1))) :
    (400 : ℝ) ≤ ((⌊Real.exp (2 * τ0 + 7)⌋₊ : ℕ) : ℝ)
      ∧ ⌊Real.exp (2 * τ0 + 7)⌋₊ ≤ ⌊Real.exp (1 / σ)⌋₊
      ∧ ⌊Real.exp (1 / σ)⌋₊ ≤ ⌊blockScale θ (N + 1)⌋₊
      ∧ 1 / |t - u| ≤ Real.log ((⌊Real.exp (2 * τ0 + 7)⌋₊ : ℕ) : ℝ)
      ∧ (1 : ℝ) ≤ 2 * σ * Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
      ∧ Real.log ((⌊Real.exp (2 * τ0 + 7)⌋₊ : ℕ) : ℝ) ≤ 2 * τ0 + 7
      ∧ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ≤ 1 / σ
      ∧ (0 : ℝ) ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ)
      ∧ (9 : ℝ) ≤ 2 * τ0 + 7 := by
  set τ : ℝ := |t - u| with hτdef
  have hinv1 : (1 : ℝ) ≤ 1 / τ := by
    rw [le_div_iff₀ hτ0]
    linarith
  have hτ01 : (1 : ℝ) ≤ τ0 := le_trans hinv1 hτ0le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  set Θ : ℝ := 2 * τ0 + 7 with hΘdef
  have hΘ9 : (9 : ℝ) ≤ Θ := by rw [hΘdef]; linarith
  -- `N₁ = ⌊e^Θ⌉`, and `e^Θ ≥ e⁹ ≥ 800`
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexp9 : (800 : ℝ) ≤ Real.exp 9 := by
    have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow : (2.7 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he1.le 9
    rw [h9]
    linarith [hpow, (by norm_num : (800 : ℝ) ≤ (2.7 : ℝ) ^ 9)]
  have hN₁800 : (800 : ℝ) ≤ Real.exp Θ := le_trans hexp9 (Real.exp_le_exp.2 hΘ9)
  have hhalfN : Real.exp Θ / 2 < ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ) := half_lt_floor (by linarith)
  have h400 : (400 : ℝ) ≤ ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ) := by linarith
  -- `\log N₁ ≥ Θ - \log 2 ≥ 1/τ`
  have hlogN₁ : Θ - Real.log 2 ≤ Real.log ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ) := by
    have h4 : Real.log (Real.exp Θ / 2) ≤ Real.log ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hhalfN.le
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h4
  have hlg : 1 / τ ≤ Real.log ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ) := by
    rw [hΘdef] at hlogN₁
    linarith
  have hΘup : Real.log ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ) ≤ Θ := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < ((⌊Real.exp Θ⌋₊ : ℕ) : ℝ))
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ Real.exp Θ))
    rwa [Real.log_exp] at h
  -- `M = ⌊e^{1/σ}⌉`
  have hM3 : (3 : ℝ) ≤ Real.exp (1 / σ) := by
    have h2 : (2 : ℝ) ≤ 1 / σ := by
      rw [le_div_iff₀ hσ0]
      linarith
    linarith [Real.add_one_le_exp (1 / σ)]
  have hhalfM : Real.exp (1 / σ) / 2 < ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) :=
    half_lt_floor (by linarith)
  have hNM : ⌊Real.exp Θ⌋₊ ≤ ⌊Real.exp (1 / σ)⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.2 hτ0σ)
  have hMN₂ : ⌊Real.exp (1 / σ)⌋₊ ≤ ⌊blockScale θ (N + 1)⌋₊ := by
    refine Nat.floor_le_floor ?_
    rw [← Real.exp_log (blockScale_pos θ (N + 1))]
    exact Real.exp_le_exp.2 hσN
  have hlogM_lo : 1 / σ - Real.log 2 ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) := by
    have h4 : Real.log (Real.exp (1 / σ) / 2)
        ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hhalfM.le
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h4
  have hM : (1 : ℝ) ≤ 2 * σ * Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) := by
    have hstep : 2 * σ * (1 / σ - Real.log 2)
        ≤ 2 * σ * Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlogM_lo (by positivity)
    have hid : 2 * σ * (1 / σ - Real.log 2) = 2 - 2 * σ * Real.log 2 := by
      field_simp
    rw [hid] at hstep
    nlinarith
  have hlogM_hi : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ≤ 1 / σ := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ))
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ Real.exp (1 / σ)))
    rwa [Real.log_exp] at h
  have hlogM0 : (0 : ℝ) ≤ Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ 1 / σ := by
      rw [le_div_iff₀ hσ0]
      linarith
    linarith
  exact ⟨h400, hNM, hMN₂, hlg, hM, hΘup, hlogM_hi, hlogM0, hΘ9⟩

/-- **The constant the bottom block costs**,
`(1 + eulerBound 401⁴)·pairIcoConst·\max(1, e^ϑ/\log 400)⁴`.  The two-point moment of the primes
below `x₀ = e^{e^θ}` is `≪ (\log x₀)⁴ = e^{4θ}`, so this is `≪ e^{4ϑ}`, where the deterministic
`RMF.bottomSupConst` is a triple exponential in `ϑ`. -/
noncomputable def bottomConst (ϑ : ℝ) : ℝ :=
  (1 + eulerBound 401 ^ 4) * pairIcoConst * max 1 (Real.exp ϑ / Real.log 400) ^ 4

lemma one_add_eulerBound_le_bottomConst (ϑ : ℝ) :
    1 + eulerBound 401 ^ 4 ≤ bottomConst ϑ := by
  unfold bottomConst
  have h1 : (1 : ℝ) ≤ max 1 (Real.exp ϑ / Real.log 400) ^ 4 := one_le_pow₀ (le_max_left _ _)
  have h0 : (0 : ℝ) ≤ 1 + eulerBound 401 ^ 4 := by positivity
  have hp := one_le_pairIcoConst
  calc 1 + eulerBound 401 ^ 4 = (1 + eulerBound 401 ^ 4) * 1 * 1 := by ring
    _ ≤ (1 + eulerBound 401 ^ 4) * pairIcoConst * max 1 (Real.exp ϑ / Real.log 400) ^ 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp h0) h1 zero_le_one
          (mul_nonneg h0 (le_trans zero_le_one hp))

lemma one_le_bottomConst (ϑ : ℝ) : 1 ≤ bottomConst ϑ :=
  le_trans (le_add_of_nonneg_right (by positivity)) (one_add_eulerBound_le_bottomConst ϑ)

/-- **The constant the bottom block costs, with the split at a floor `y ≥ 400`**,
`(1 + eulerBound (y+1)⁴)·pairIcoConstAt y·\max(1, e^ϑ/\log y)⁴`.  Both sides of the trade move
with `y`: the first factor rises like `e^{28√y}` and the second falls like
`e^{twoPointMomentConst/(√y\log y)}`.  `RMF.bottomConst` is the case `y = 400`. -/
noncomputable def bottomConstAt (y : ℕ) (ϑ : ℝ) : ℝ :=
  (1 + eulerBound (y + 1) ^ 4) * pairIcoConstAt (y : ℝ)
    * max 1 (Real.exp ϑ / Real.log (y : ℝ)) ^ 4

/-- `RMF.bottomConstAt` at `400` is `RMF.bottomConst`. -/
lemma bottomConstAt_four_hundred (ϑ : ℝ) : bottomConstAt 400 ϑ = bottomConst ϑ := by
  unfold bottomConstAt bottomConst
  norm_num [pairIcoConstAt_four_hundred]

lemma one_add_eulerBound_le_bottomConstAt {y : ℕ} (hy : 400 ≤ y) (ϑ : ℝ) :
    1 + eulerBound (y + 1) ^ 4 ≤ bottomConstAt y ϑ := by
  have hyR : (400 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  unfold bottomConstAt
  have h1 : (1 : ℝ) ≤ max 1 (Real.exp ϑ / Real.log (y : ℝ)) ^ 4 := one_le_pow₀ (le_max_left _ _)
  have h0 : (0 : ℝ) ≤ 1 + eulerBound (y + 1) ^ 4 := by positivity
  have hp := one_le_pairIcoConstAt hyR
  calc 1 + eulerBound (y + 1) ^ 4 = (1 + eulerBound (y + 1) ^ 4) * 1 * 1 := by ring
    _ ≤ (1 + eulerBound (y + 1) ^ 4) * pairIcoConstAt (y : ℝ)
          * max 1 (Real.exp ϑ / Real.log (y : ℝ)) ^ 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp h0) h1 zero_le_one
          (mul_nonneg h0 (le_trans zero_le_one hp))

/-- **`hP0`, supplied.**  `E[P₀(s₁)P₀(s₂)] ≤ bottomConstAt y ϑ` for every floor `y ≥ 400`, every
`θ ≤ ϑ` and every pair of heights on the line `1/2 + σ`, `σ ≥ 0`.  For `x₀ ≥ y` it is the
two-point moment bound over the primes below `x₀`, after rotating the pair onto the real axis,
with `\log x₀ = e^θ ≤ e^ϑ`; below `y`, every Euler factor is bounded as for the primes below
`y + 1`.

`ϑ` is the cap on Harper's `θ`, so `ϑ = B + 2` serves — the constant depends on `y` and `B` and on
nothing else, which is all the chain asks of it.

This is the floored form: the split sits at `y + 1` rather than `401`, so the (5.1) error is
charged at `y`.  `RMF.integral_normSq_pair_bottom_le` is the case `y = 400`. -/
theorem integral_normSq_pair_bottom_le_at {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} (hf : IsSteinhausRMF f μ)
    {y : ℕ} (hy : 400 ≤ y)
    {θ ϑ σ : ℝ} (hθϑ : θ ≤ ϑ) {s₁ s₂ : ℂ} (hre₁ : s₁.re = 1 / 2 + σ)
    (hre₂ : s₂.re = 1 / 2 + σ) (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ bottomConstAt y ϑ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hyR : (400 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  set N : ℕ := ⌊blockScale θ 0⌋₊ with hNdef
  have hh₁ : (1 : ℝ) / 2 ≤ s₁.re := by rw [hre₁]; linarith
  have hh₂ : (1 : ℝ) / 2 ≤ s₂.re := by rw [hre₂]; linarith
  rcases le_or_gt ((y : ℕ) : ℝ) (N : ℝ) with hN | hN
  · -- the moment bound, after rotating the pair onto the real axis
    have hs₁ : s₁ = shiftLine σ s₁.im := by
      apply Complex.ext <;> simp [hre₁]
    have hs₂ : s₂ = shiftLine σ s₂.im := by
      apply Complex.ext <;> simp [hre₂]
    rw [hs₁, hs₂]
    refine le_trans (integral_normSq_pair_below_le_at y hy X μ hX σ s₁.im s₂.im N hσ hN) ?_
    have hlog400 : (0 : ℝ) < Real.log (y : ℝ) := Real.log_pos (by linarith)
    have hNpos : (0 : ℝ) < N := by linarith
    have hlogN : Real.log (N : ℝ) ≤ Real.exp ϑ := by
      have h1 : (N : ℝ) ≤ blockScale θ 0 := Nat.floor_le (blockScale_pos θ 0).le
      have h2 : Real.log (N : ℝ) ≤ Real.log (blockScale θ 0) := Real.log_le_log hNpos h1
      have h3 : Real.log (blockScale θ 0) = Real.exp θ := by
        rw [blockScale, Real.log_exp]
        simp
      rw [h3] at h2
      exact le_trans h2 (Real.exp_le_exp.2 hθϑ)
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    have hratio : Real.log (N : ℝ) / Real.log (y : ℝ)
        ≤ max 1 (Real.exp ϑ / Real.log (y : ℝ)) :=
      le_trans (div_le_div_of_nonneg_right hlogN hlog400.le) (le_max_right _ _)
    have hpow : (Real.log (N : ℝ) / Real.log (y : ℝ)) ^ 4
        ≤ max 1 (Real.exp ϑ / Real.log (y : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (div_nonneg hlogN0 hlog400.le) hratio 4
    have hK : 0 ≤ (1 + eulerBound (y + 1) ^ 4) * pairIcoConstAt (y : ℝ) := by
      have := pairIcoConstAt_pos (y : ℝ)
      positivity
    calc (1 + eulerBound (y + 1) ^ 4) * pairIcoConstAt (y : ℝ) / Real.log (y : ℝ) ^ 4
          * Real.log (N : ℝ) ^ 4
        = (1 + eulerBound (y + 1) ^ 4) * pairIcoConstAt (y : ℝ)
            * (Real.log (N : ℝ) / Real.log (y : ℝ)) ^ 4 := by ring
      _ ≤ bottomConstAt y ϑ := by
          unfold bottomConstAt
          exact mul_le_mul_of_nonneg_left hpow hK
  · -- below `400`: every factor deterministically, as for the primes below `401`
    have hN401 : N + 1 ≤ y + 1 := by
      have : N < y := by exact_mod_cast hN
      omega
    have hae : ∀ᵐ ω ∂μ,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (N + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (N + 1) s₂ ω‖ ^ 2
          ≤ 1 + eulerBound (y + 1) ^ 4 := by
      filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw (N + 1)] with ω hω
      have h1 := le_trans (norm_randomEulerProduct_le hω hh₁) (eulerBound_mono hN401)
      have h2 := le_trans (norm_randomEulerProduct_le hω hh₂) (eulerBound_mono hN401)
      have hE : (0 : ℝ) ≤ eulerBound (y + 1) := eulerBound_nonneg (y + 1)
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2,
        pow_nonneg (norm_nonneg (randomEulerProduct
          (fun ω => compMultExtension fun p => X p ω) (N + 1) s₁ ω)) 2,
        pow_nonneg hE 2, sq_nonneg (eulerBound (y + 1) ^ 2)]
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
      (integrable_const _) hae) ?_
    refine le_trans (le_of_eq ?_) (one_add_eulerBound_le_bottomConstAt hy ϑ)
    simp

/-- **`hP0`, supplied**, the case `y = 400` of `RMF.integral_normSq_pair_bottom_le_at`. -/
theorem integral_normSq_pair_bottom_le {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} (hf : IsSteinhausRMF f μ)
    {θ ϑ σ : ℝ} (hθϑ : θ ≤ ϑ) {s₁ s₂ : ℂ} (hre₁ : s₁.re = 1 / 2 + σ)
    (hre₂ : s₂.re = 1 / 2 + σ) (hσ : 0 ≤ σ) :
    (∫ ω, ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProduct f (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂μ)
      ≤ bottomConst ϑ := by
  have h := integral_normSq_pair_bottom_le_at hf (y := 400) le_rfl hθϑ hre₁ hre₂ hσ
  rwa [bottomConstAt_four_hundred] at h

/-! ### The far range, with its cutoffs chosen

`RMF.setIntegral_normSq_pair_far_envelope_le` takes cutoffs `N₁ ≤ M ≤ N₂` and a bound `Θ` on
`\log N₁`.  At Harper's data none of them is a block scale:

* `N₁ = ⌊e^{2τ₀+7}⌋` with `τ₀ ≥ 1/τ`: the far range is `τ > e^{-(2θ+2)}/2`, so `1/τ`, `Θ`,
  `\log⁴(2Θ)` and `Θ²` are bounded in terms of `θ`;
* `M = ⌊e^{1/σ}⌋`, as in the middle range, with `\log M ≤ 1/σ = \log x/(4V)`, the `L/4` of Key
  Proposition 5's numerator;
* `N₂ = ⌊x⌋`, the top.

The `7` clears `400 ≤ N₁` for `τ` near `1`. -/
theorem exists_setIntegral_normSq_pair_far_le :
    ∃ K > 0, ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsSteinhausPrimeValues Y ν →
      ∀ (θ σ τ0 t u Cst W : ℝ) (N : ℕ) (A : Set Ω),
      0 < σ → σ ≤ 1 / 2 → 0 < |t - u| → |t - u| ≤ 1 →
      1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
      1 / σ ≤ Real.log (blockScale θ (N + 1)) → 0 ≤ Cst →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2 →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (blockCutoff θ N) (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (blockCutoff θ N) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
            * ((1 / σ) ^ 2 / W ^ 2) * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨K, hK, hfarsrc⟩ := setIntegral_normSq_pair_far_envelope_le (Ω' := Ω)
  refine ⟨K, hK, ?_⟩
  intro Y ν hY θ σ τ0 t u Cst W N A hσ0 hσhalf hτ0 hτ1 hτ0le hτ0σ hσN hCst hbar
  obtain ⟨h400, hNM, hMN₂, hlg, hM, hΘup, hlogM_hi, hlogM0, hΘ9⟩ :=
    far_truncation_bounds hσ0 hσhalf hτ0 hτ1 hτ0le hτ0σ hσN
  set τ : ℝ := |t - u| with hτdef
  set Θ : ℝ := 2 * τ0 + 7 with hΘdef
  -- the cutoff `N₂ + 1` is the tilt's
  have hcut : ⌊blockScale θ (N + 1)⌋₊ + 1 = blockCutoff θ N := rfl
  have hfar := hfarsrc Y ν hY σ t u (⌊Real.exp Θ⌋₊) (⌊Real.exp (1 / σ)⌋₊)
    (⌊blockScale θ (N + 1)⌋₊) Θ W Cst A hσ0.le hτ0 hτ1 h400 hNM hMN₂ hlg hM hCst hΘup
    (by rw [hcut]; exact hbar)
  rw [hcut] at hfar
  refine le_trans hfar ?_
  have hbase : (0 : ℝ) ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4 := by
    have hlog0 : (0 : ℝ) ≤ Real.log (2 * Θ) := Real.log_nonneg (by linarith)
    positivity
  have hsq : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ^ 2 ≤ (1 / σ) ^ 2 :=
    pow_le_pow_left₀ hlogM0 hlogM_hi 2
  have hW0 : (0 : ℝ) ≤ 1 / W ^ 2 := by positivity
  have hlast : (0 : ℝ) ≤ 1 / (τ * Real.log (2 / τ) ^ 2) := by positivity
  have hdiv : Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ^ 2 / W ^ 2 ≤ (1 / σ) ^ 2 / W ^ 2 := by
    gcongr
  calc Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4
        * (Real.log ((⌊Real.exp (1 / σ)⌋₊ : ℕ) : ℝ) ^ 2 / W ^ 2)
        * (1 / (τ * Real.log (2 / τ) ^ 2))
      ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4 * ((1 / σ) ^ 2 / W ^ 2)
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hbase) hlast
    _ = Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4 * ((1 / σ) ^ 2 / W ^ 2)
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by rw [hΘdef]

/-- **`E[P_t] ≪ 1/τ` at the split the product actually uses.**  The chain's low factor runs to
`x_{k+1}` and the high one starts there, so both must be read at `RMF.splitIndex θ m τ + 2` — two
blocks above the floor, for the reason in the section note above.  Two blocks cost `e²` here,
exactly as they cost `e²` in `(5.2)`. -/
theorem exists_integral_normSq_low_splitIndex_add_two_le :
    ∃ CP > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (θ σ τ : ℝ) (m : ℕ) (s : ℂ), 0 ≤ θ → 0 ≤ σ → s.re = 1 / 2 + σ →
        1 ≤ splitIndex θ m τ →
        (∫ ω, ‖randomEulerProductIco f (⌊blockScale θ 0⌋₊ + 1)
              (⌊blockScale θ (splitIndex θ m τ + 2)⌋₊ + 1) s ω‖ ^ 2 ∂μ) ≤ CP * (1 / |τ|) := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_randomEulerProductIco_sq_le (Ω := Ω)
  refine ⟨C * Real.exp 2, by positivity, fun f μ hf θ σ τ m s hθ hσ hre h1 => ?_⟩
  have hmono : blockScale θ 0 ≤ blockScale θ (splitIndex θ m τ + 2) :=
    blockScale_mono θ (Nat.zero_le _)
  have hy₀ : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ (splitIndex θ m τ + 2)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor hmono)
  -- `\log x_{j+2} = e²\log x_j ≤ e²/τ`
  have hstep : Real.log (blockScale θ (splitIndex θ m τ + 2))
      = Real.exp 2 * Real.log (blockScale θ (splitIndex θ m τ)) := by
    rw [log_blockScale, log_blockScale, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hle : Real.log (blockScale θ (splitIndex θ m τ + 2)) ≤ Real.exp 2 * (1 / |τ|) := by
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (log_blockScale_splitIndex_le hθ h1) (Real.exp_pos 2).le
  refine le_trans (hbound f μ hf _ (blockScale θ (splitIndex θ m τ + 2)) s σ
    (two_le_blockScale hθ _) hy₀ hσ hre) ?_
  calc C * Real.log (blockScale θ (splitIndex θ m τ + 2))
      ≤ C * (Real.exp 2 * (1 / |τ|)) := mul_le_mul_of_nonneg_left hle hC.le
    _ = C * Real.exp 2 * (1 / |τ|) := by ring

/-! ### The crude range, first regime

`τ ≥ 1/L`, where the split is the block above `e^{1/τ}` and every factor is one proved above:

`(5.2)·E[Q]·E[P_t]·E[P₀] ≪ X²·(τ\log²(2/τ))^{-2}·(τ/σ)²·τ^{-1}·K_0
              = X²K_QC_PK_0σ^{-2}·(τ\log⁴(2/τ))^{-1}`,

and `σ^{-1} = \log x/(4V) = L/4`, so this is `≪ e^{2a}L²/(τ\log⁴(2/τ))`.  Against Harper's
target `e^{2a}Λ^{-4}L²/τ` it remains to see `\log⁴(2/τ) ≥ Λ⁴/81`, which is the crude range
`τ ≤ (\log x)^{-1/3}`: the `Λ^{-4}` comes from `hf(k+1) = -2\log(k+1)` with `k+1 ≍ Λ`. -/
theorem setIntegral_normSq_pair_crude_split_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {X KQ CP K0 σ τ : ℝ}
    (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hK0 : 0 ≤ K0) (hτ0 : 0 < τ) (hσ0 : 0 < σ)
    (hlog : Real.log (2 / τ) ≠ 0)
    (h52 : Real.exp (v₂ (k + 1)) ^ 2 ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
          ≤ KQ * (τ / σ) ^ 2)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν)
          ≤ CP * (1 / τ))
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ X ^ 2 * KQ * CP * K0 / σ ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 4)) := by
  have hchain := setIntegral_normSq_pair_crude_le hY θ hs₁ hs₂ hkb hbN
    (KQ := KQ * (τ / σ) ^ 2) (CP := CP * (1 / τ)) (K0 := K0) (u₁ := u₁) (v₁ := v₁)
    (u₂ := u₂) (v₂ := v₂) (by positivity) (by positivity) hQ hPt hP0
  refine le_trans hchain ?_
  -- the four factors multiply out to the stated shape
  have h1 : (0 : ℝ) ≤ KQ * (τ / σ) ^ 2 * (CP * (1 / τ)) := by positivity
  have hstep : Real.exp (v₂ (k + 1)) ^ 2 * (KQ * (τ / σ) ^ 2 * (CP * (1 / τ))) * K0
      ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2
          * (KQ * (τ / σ) ^ 2 * (CP * (1 / τ))) * K0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h52 h1) hK0
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ### Raising the tilt's cutoff does not move the barrier's probability

The chain wants the barrier over `b` blocks under the tilt to `x`, with `b` and `N` independent;
`RMF.exists_measure_barrierEventPair_harper_le` has its barrier over `N'` blocks under the tilt at
`blockCutoff θ' N'`, the same `N'`.  The tilt factorises over primes: raising the cutoff from `y`
to `y'` multiplies the weight by a factor over the primes of `[y, y')`, independent of everything
the barrier reads, which cancels between the restricted integral and the normaliser.

This mirrors `RMF.indepFun_barrierHighProd_lowBlocks`: there the barrier travels with the high
weight and is split from the low blocks, here with the low weight and split from the high ones.
`RMF.blockPairAug` makes the low weight a functional of the blocks `[0, n+2)`, the primes below
`x₀` forming its block `0`. -/

/-- Read an aug-indexed restriction back as the un-augmented family: `m ↦ w(m + 1)` for
`m + 1 < c`, and `0` otherwise (block `m` is aug index `m + 1`); the counterpart of
`RMF.icoExtend` on `Finset.range`. -/
noncomputable def augExtend (c : ℕ) (w : ↑(Finset.range c) → ℝ × ℝ) : ℕ → ℝ × ℝ :=
  fun m => if h : m + 1 ∈ Finset.range c then w ⟨m + 1, h⟩ else 0

lemma measurable_augExtend (c : ℕ) : Measurable (augExtend c) := by
  refine measurable_pi_lambda _ fun m => ?_
  by_cases h : m + 1 ∈ Finset.range c
  · simp only [augExtend, dif_pos h]
    exact measurable_pi_apply _
  · simp only [augExtend, dif_neg h]
    exact measurable_const

lemma augExtend_apply {c m : ℕ} (h : m + 1 ∈ Finset.range c) (w : ↑(Finset.range c) → ℝ × ℝ) :
    augExtend c w m = w ⟨m + 1, h⟩ := dif_pos h

/-- **The barrier together with the low weight is independent of the high blocks.** -/
theorem indepFun_barrierLowProd_highBlocks {ν : Measure Ω} {Z : ℕ → Ω → ℝ × ℝ}
    (hZ : iIndepFun Z ν) (hZm : ∀ m, Measurable (Z m)) {nb c : ℕ} (hnb : nb < c) (Nc : ℕ)
    (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    IndepFun
      (Set.indicator (barrierEventPair (fun m => Z (m + 1)) nb u₁ v₁ u₂ v₂)
        (fun ω => Real.exp (∑ m ∈ Finset.range c, (2 * (Z m ω).1 + 2 * (Z m ω).2))))
      (fun ω => Real.exp (∑ m ∈ Finset.Ico c Nc,
        (2 * (Z m ω).1 + 2 * (Z m ω).2))) ν := by
  classical
  have hdisj : Disjoint (Finset.range c) (Finset.Ico c Nc) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  set g : (↑(Finset.range c) → ℝ × ℝ) → (ℕ → ℝ × ℝ) := augExtend c with hgdef
  have hg : Measurable g := measurable_augExtend c
  have hexpm : ∀ (S : Finset ℕ), Measurable fun w : ↑S → ℝ × ℝ =>
      Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2)) := fun S =>
    Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
      (((measurable_pi_apply m).fst).const_mul 2).add (((measurable_pi_apply m).snd).const_mul 2))
  have hφ : Measurable (Set.indicator (g ⁻¹' barrierSet nb u₁ v₁ u₂ v₂)
      fun w : ↑(Finset.range c) → ℝ × ℝ =>
        Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2))) :=
    (hexpm _).indicator (hg (measurableSet_barrierSet nb u₁ v₁ u₂ v₂))
  have h := indepFun_of_disjoint_groups hZ hZm hdisj hφ (hexpm (Finset.Ico c Nc))
  -- the restriction agrees with the shifted family on every index the barrier reads
  have hagree : ∀ (ω : Ω) (m : ℕ), m < nb →
      g (fun p : ↑(Finset.range c) => Z (p : ℕ) ω) m = Z (m + 1) ω := by
    intro ω m hm
    have hmem : m + 1 ∈ Finset.range c := Finset.mem_range.2 (by omega)
    rw [hgdef]
    exact augExtend_apply hmem _
  have hattach : ∀ (S : Finset ℕ) (ω : Ω),
      (∑ m ∈ (Finset.univ : Finset ↑S), (2 * (Z (m : ℕ) ω).1 + 2 * (Z (m : ℕ) ω).2))
        = ∑ m ∈ S, (2 * (Z m ω).1 + 2 * (Z m ω).2) := by
    intro S ω
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach _ fun m => 2 * (Z m ω).1 + 2 * (Z m ω).2
  have hlowfun : (fun ω => Set.indicator (g ⁻¹' barrierSet nb u₁ v₁ u₂ v₂)
        (fun w : ↑(Finset.range c) → ℝ × ℝ =>
          Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2)))
        (fun p : ↑(Finset.range c) => Z (p : ℕ) ω))
      = Set.indicator (barrierEventPair (fun m => Z (m + 1)) nb u₁ v₁ u₂ v₂)
        (fun ω => Real.exp (∑ m ∈ Finset.range c,
          (2 * (Z m ω).1 + 2 * (Z m ω).2))) := by
    funext ω
    rw [barrierEventPair_eq_preimage]
    by_cases hmem : (fun m => Z (m + 1) ω) ∈ barrierSet nb u₁ v₁ u₂ v₂
    · rw [Set.indicator_of_mem
          (by rw [Set.mem_preimage]; exact (mem_barrierSet_congr (hagree ω)).2 hmem),
        Set.indicator_of_mem (by rw [Set.mem_preimage]; exact hmem)]
      simp only
      congr 1
      exact hattach _ ω
    · rw [Set.indicator_of_notMem
          (by rw [Set.mem_preimage]; exact fun hc => hmem ((mem_barrierSet_congr (hagree ω)).1 hc)),
        Set.indicator_of_notMem (by rw [Set.mem_preimage]; exact hmem)]
  have hhighfun : (fun ω => (fun w : ↑(Finset.Ico c Nc) → ℝ × ℝ =>
        Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2)))
        (fun p : ↑(Finset.Ico c Nc) => Z (p : ℕ) ω))
      = fun ω => Real.exp (∑ m ∈ Finset.Ico c Nc,
        (2 * (Z m ω).1 + 2 * (Z m ω).2)) := by
    funext ω
    simp only
    congr 1
    exact hattach _ ω
  rw [← hlowfun, ← hhighfun]
  exact h

/-- **The tilt's cutoff does not move the barrier's probability**: for a barrier over `n` blocks
and `n ≤ N`, the tilts at `blockCutoff θ N` and at `blockCutoff θ n` give it the same measure.
This lets `RMF.exists_measure_barrierEventPair_harper_le`, whose barrier length and tilt cutoff
coincide, serve the chain's barrier over `b` blocks under the tilt to `x`. -/
theorem tiltedMeasure₂_barrierEventPair_congr_cutoff {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {n N : ℕ} (hnN : n ≤ N) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N) s₁ s₂ ν
        (barrierEventPair (blockPair θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal
      = (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ n) s₁ s₂ ν
          (barrierEventPair (blockPair θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal := by
  classical
  haveI := hY.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  set A : Set Ω := barrierEventPair (blockPair θ s₁ s₂ Y) n u₁ v₁ u₂ v₂ with hAdef
  have hAm : MeasurableSet A :=
    measurableSet_barrierEventPair (measurable_blockPair hY θ s₁ s₂) n u₁ v₁ u₂ v₂
  set W : ℕ → Ω → ℝ := fun y ω =>
    ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y s₁ ω‖ ^ 2
      * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y s₂ ω‖ ^ 2 with hWdef
  -- the aug-block exponential is the two-point weight, at every cutoff
  have haux : ∀ j : ℕ, (fun ω => Real.exp (∑ m ∈ Finset.range (j + 2),
        (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2)))
      =ᵐ[ν] W (blockCutoff θ j) := by
    intro j
    filter_upwards [exp_sum_localTilt₂_ae_eq hY (blockCutoff θ j) hs₁ hs₂] with ω hω
    rw [show j + 2 = j + 1 + 1 from rfl,
      sum_blockPairAug_range_eq_sum_localTilt₂ θ (j + 1) s₁ s₂ ω]
    exact hω
  -- and it splits at the intermediate cutoff
  have hsplit : ∀ ω : Ω, (∑ m ∈ Finset.range (N + 2),
        (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))
      = (∑ m ∈ Finset.range (n + 2),
          (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))
        + ∑ m ∈ Finset.Ico (n + 2) (N + 2),
            (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2) :=
    fun ω => (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  set Lo : Ω → ℝ := fun ω => Real.exp (∑ m ∈ Finset.range (n + 2),
    (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2)) with hLodef
  set Hi : Ω → ℝ := fun ω => Real.exp (∑ m ∈ Finset.Ico (n + 2) (N + 2),
    (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2)) with hHidef
  have hWN : W (blockCutoff θ N) =ᵐ[ν] fun ω => Lo ω * Hi ω := by
    filter_upwards [(haux N).symm] with ω hω
    rw [hω, hLodef, hHidef]
    simp only
    rw [← Real.exp_add, ← hsplit ω]
  have hWn : W (blockCutoff θ n) =ᵐ[ν] Lo := (haux n).symm
  -- measurability of the three factors
  have hZm := measurable_blockPairAug hY θ s₁ s₂
  have hLom : Measurable Lo := Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
    (((hZm m).fst).const_mul 2).add (((hZm m).snd).const_mul 2))
  have hHim : Measurable Hi := Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
    (((hZm m).fst).const_mul 2).add (((hZm m).snd).const_mul 2))
  have hAind : Measurable (Set.indicator A Lo) := hLom.indicator hAm
  -- the two factorisations
  have hindA := indepFun_barrierLowProd_highBlocks (iIndepFun_blockPairAug hY θ s₁ s₂)
    (measurable_blockPairAug hY θ s₁ s₂) (nb := n) (c := n + 2) (by omega) (N + 2)
    u₁ v₁ u₂ v₂
  have hind0 := indepFun_barrierLowProd_highBlocks (iIndepFun_blockPairAug hY θ s₁ s₂)
    (measurable_blockPairAug hY θ s₁ s₂) (nb := 0) (c := n + 2) (by omega) (N + 2)
    u₁ v₁ u₂ v₂
  rw [barrierEventPair_zero] at hind0
  simp only [Set.indicator_univ] at hind0
  have hnum : (∫ ω, Set.indicator A Lo ω * Hi ω ∂ν)
      = (∫ ω, Set.indicator A Lo ω ∂ν) * ∫ ω, Hi ω ∂ν :=
    hindA.integral_mul_eq_mul_integral hAind.aestronglyMeasurable hHim.aestronglyMeasurable
  have hden : (∫ ω, Lo ω * Hi ω ∂ν) = (∫ ω, Lo ω ∂ν) * ∫ ω, Hi ω ∂ν :=
    hind0.integral_mul_eq_mul_integral hLom.aestronglyMeasurable hHim.aestronglyMeasurable
  -- transport to the weights
  have hIN : (∫ ω, W (blockCutoff θ N) ω ∂ν) = (∫ ω, Lo ω ∂ν) * ∫ ω, Hi ω ∂ν := by
    rw [integral_congr_ae hWN, hden]
  have hIn : (∫ ω, W (blockCutoff θ n) ω ∂ν) = ∫ ω, Lo ω ∂ν := integral_congr_ae hWn
  have hAN : (∫ ω in A, W (blockCutoff θ N) ω ∂ν)
      = (∫ ω in A, W (blockCutoff θ n) ω ∂ν) * ∫ ω, Hi ω ∂ν := by
    rw [integral_indicator hAm |>.symm, integral_indicator hAm |>.symm]
    have hind : (fun ω => Set.indicator A (W (blockCutoff θ N)) ω)
        =ᵐ[ν] fun ω => Set.indicator A Lo ω * Hi ω := by
      filter_upwards [hWN] with ω hω
      by_cases hmem : ω ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
    have hind2 : (fun ω => Set.indicator A (W (blockCutoff θ n)) ω)
        =ᵐ[ν] fun ω => Set.indicator A Lo ω := by
      filter_upwards [hWn] with ω hω
      by_cases hmem : ω ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    rw [integral_congr_ae hind, hnum, integral_congr_ae hind2]
  -- and divide
  have hposN : (0 : ℝ) < ∫ ω, W (blockCutoff θ N) ω ∂ν :=
    hf.integral_normSq_mul_normSq_pos _ hs₁ hs₂
  have hposn : (0 : ℝ) < ∫ ω, W (blockCutoff θ n) ω ∂ν :=
    hf.integral_normSq_mul_normSq_pos _ hs₁ hs₂
  have hHi0 : (0 : ℝ) < ∫ ω, Hi ω ∂ν := by
    rw [hIn] at hposn
    rw [hIN] at hposN
    nlinarith
  have hNeq := hf.setIntegral_normSq_mul_normSq_eq (blockCutoff θ N) hs₁ hs₂ hAm
  have hneq := hf.setIntegral_normSq_mul_normSq_eq (blockCutoff θ n) hs₁ hs₂ hAm
  have hfin : (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
        (blockCutoff θ N) s₁ s₂ ν A).toReal * (∫ ω, W (blockCutoff θ N) ω ∂ν)
      = (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
          (blockCutoff θ n) s₁ s₂ ν A).toReal * (∫ ω, W (blockCutoff θ N) ω ∂ν) := by
    rw [← hNeq, hAN, hneq, hIN, hIn]
    ring
  exact mul_right_cancel₀ hposN.ne' hfin

/-! ### The middle range at Harper's tube and split

The tube is Harper's, the split `k + 1 = RMF.splitIndex θ b (t-u) + 2`, the shift `r ≥ k + 1`,
and the shifted barrier runs over `b - r` blocks.  The four analytic inputs remain hypotheses;
`hbarD` is stated as `RMF.exists_measure_barrierEventPair_shift_display_le` states it, at the
chain's `blockCutoff θ N` in the shifted family, so no transport is needed.

`r` is a parameter because it must also satisfy Proposition 7's `Tsh ≤ τe^{r+θ}`, and at
`r ≈ \text{splitIndex} + 2` the offset cancels (`r + θ ≈ \log(1/τ)`, so `τe^{r+θ} = O(1)`): a
larger `B` does not help, while a further `⌈\log Tsh⌉` blocks does.  The caller chooses `r` in
`[\text{splitIndex}+2, b]`. -/
theorem setIntegral_normSq_pair_middle_harper_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν)
    {θ σ a t u : ℝ} {N b r : ℕ} (hbN : b ≤ N) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hτ0 : 0 < |t - u|) (hτ1 : |t - u| ≤ 1)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|))
    (hmb : Real.log (2 / |t - u|) ≤ 2 * (b : ℝ))
    (hsr : splitIndex θ b (t - u) + 2 ≤ r)
    (hrb : r ≤ b)
    {Cst KQ CP K0 L W : ℝ} (hCst : 0 ≤ Cst) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hW : W ≠ 0)
    (hbarD : (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
            (blockCutoff θ N) (shiftLine σ t) (shiftLine σ u) ν
            (barrierEventPair
              (fun mm => blockPair θ (shiftLine σ t) (shiftLine σ u) Y (mm + r)) (b - r)
              (fun m => -shiftLevel a r harperHf - blockSlope 125 * m)
              (fun m => shiftLevel a r harperHf + m + 10 * Real.log m)
              (fun m => -shiftLevel a r harperHf - blockSlope 125 * m)
              (fun m => shiftLevel a r harperHf + m + 10 * Real.log m))).toReal
        ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (splitIndex θ b (t - u) + 2)⌋₊ + 1)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (splitIndex θ b (t - u) + 2)⌋₊ + 1)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ KQ * (|t - u| * L) ^ 2)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (splitIndex θ b (t - u) + 2)⌋₊ + 1)
              (shiftLine σ t) ω‖ ^ 2 ∂ν) ≤ CP * (1 / |t - u|))
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
        (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
        (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
        ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cst * KQ * CP * K0 * L ^ 2 / W ^ 2
          * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [re_shiftLine]; linarith
  have hlog0 : Real.log (2 / |t - u|) ≠ 0 := (log_two_div_pos hτ0 hτ1).ne'
  -- the barrier sits inside the shifted one, at the widened height
  have hAR := barrierEventPair_subset_shift
    (Z := blockPair θ (shiftLine σ t) (shiftLine σ u) Y) (b := b) (r := r)
    (by omega) hrb (a := a) (hf := harperHf) (fun j _ _ => abs_harperHf_le j)
  -- `hbarD` is already at the chain's cutoff, in the shifted family
  have hbar : (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) (shiftLine σ u) ν
        (barrierEventPair
          (fun m => blockPair θ (shiftLine σ t) (shiftLine σ u) Y (m + r)) (b - r)
          (fun m => -shiftLevel a r harperHf - blockSlope 125 * m)
          (fun m => shiftLevel a r harperHf + m + 10 * Real.log m)
          (fun m => -shiftLevel a r harperHf - blockSlope 125 * m)
          (fun m => shiftLevel a r harperHf + m + 10 * Real.log m))).toReal
      ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2 := hbarD
  refine setIntegral_normSq_pair_middle_envelope_le hY θ hs₁ hs₂
    (k := splitIndex θ b (t - u) + 1) ?_ hbN ?_ ?_ hAR hCst hKQ hCP hτ0 hlog0 hW ?_ ?_ ?_ ?_ hP0
  · omega
  · omega
  · omega
  · exact exp_envelope_splitIndex_add_two_sq_le hθ hτ0 hsmall hmb a
  · exact hbar
  · exact hQ
  · exact hPt

/-! ### The crude range, second regime

`τ < 1/L`: the split is the barrier's top, `k + 1 = b`, and `Q` is the `⌊\log V⌋+3` blocks
between `x_b` and `x`.  Neither moment needs a hypothesis on `1/τ`:

* `E[Q_tQ_u]` is bounded by the in-phase exponent `4` of
  `RMF.exists_integral_normSq_pairIco_split_le`, because it truncates at the tilt scale: the free
  range has `\log x/\log x_b = e^{⌊\log V⌋+4}`, which would cost `V⁴` with `V` up to
  `(\log x)^{1/100}`, while `M = e^{1/(2σ)}` has `\log M/\log x_b ∈ [e³/8, e⁴/8]`;
* `E[P_t] ≪ \log x_b ≍ L`, by Mertens.

(5.2) at `k+1 = b` contributes `e^{2a}e^{2b}/b⁴`, so the product is `≪ e^{2a}L³/Λ⁴`, the target.
-/

/-- **`RMF.exists_integral_normSq_pairIco_split_le` at a general pair of heights.**  The common
centre is rotated away; the rotation is an identity, so the constant does not move. -/
theorem exists_integral_normSq_pairIco_split_shift_le :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_pairIco_split_le (Ω := Ω)
  refine ⟨K, hK, fun X μ hX σ t u N₁ M N₂ hσ hN₁ hNM hMN₂ hM => ?_⟩
  have hσ' : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  rw [integral_normSq_ico_pair_shift hX (N₁ + 1) (N₂ + 1) hσ' t u, shiftLine_zero_height,
    shiftLine]
  exact hbound _ μ hf σ (u - t) N₁ M N₂ hσ hN₁ hNM hMN₂ hM

/-- **The crude range's second regime**, `k + 1 = b`.  Same composition as
`RMF.setIntegral_normSq_pair_crude_split_le`, with `E[Q_tQ_u]` and `E[P_t]` both absolute in `τ`
and the `\min\{L,1/τ\}` of the target realised as `L`. -/
theorem setIntegral_normSq_pair_crude_top_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b : ℕ} (hb1 : 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {X KQ CP K0 L : ℝ}
    (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP) (hK0 : 0 ≤ K0) (hL : 0 ≤ L)
    (h52 : Real.exp (v₂ b) ^ 2 ≤ X ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ b⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ b⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ KQ)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) ≤ CP * L)
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ X ^ 2 * KQ * CP * K0 * L := by
  have hchain := setIntegral_normSq_pair_crude_le hY θ hs₁ hs₂ (k := b - 1)
    (by omega) hbN (KQ := KQ) (CP := CP * L) (K0 := K0) (u₁ := u₁) (v₁ := v₁)
    (u₂ := u₂) (v₂ := v₂) hKQ (by positivity)
    (by rw [show b - 1 + 1 = b from by omega]; exact hQ)
    (by rw [show b - 1 + 1 = b from by omega]; exact hPt) hP0
  rw [show b - 1 + 1 = b from by omega] at hchain
  refine le_trans hchain ?_
  have h1 : (0 : ℝ) ≤ KQ * (CP * L) := by positivity
  have hstep : Real.exp (v₂ b) ^ 2 * (KQ * (CP * L)) * K0 ≤ X ^ 2 * (KQ * (CP * L)) * K0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h52 h1) hK0
  refine le_trans hstep (le_of_eq ?_)
  ring

/-! ### Key Proposition 5, envelope form

Harper's Key Proposition 5: `E(∫_𝔏|F(1/2+4V/\log x+it)|² dt)²
≪ e^{2\min\{√(\log\log x), 1/(1-q)\}}(\log x/(V(1+(1-q)√(\log\log x))))²`.

`RMF.integral_sq_setIntegral_indicator_normSq_harper_le` gives `E[X²] ≤ (6 + 2/\log 2)EL_c²/W²`
from the crude bound `EL_c²/Λ⁴·\min\{L_c, 1/τ\}` (`RMF.setIntegral_normSq_pair_crude_split_le`,
`RMF.setIntegral_normSq_pair_crude_top_le`) and the outer bound `EL_c²/W²/(τ\log²(2/τ))`
(`RMF.setIntegral_normSq_pair_middle_harper_le`, `RMF.exists_setIntegral_normSq_pair_far_le`).
`W² ≤ Λ` is spent on the crude range, making `EL²/Λ³` at most `EL²/W²`; `1 + \log(2L) ≤ 3Λ` is
generous; `|T| ≤ 1` is `T ⊆ [-1/2, 1/2]`. -/
theorem integral_sq_setIntegral_indicator_normSq_harper_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) {E Lc W Λ ε : ℝ}
    (hE : 0 ≤ E) (hLc : 1 ≤ Lc) (hΛ : 1 ≤ Λ) (hW : 0 < W) (hWΛ : W ^ 2 ≤ Λ)
    (hlogL : 1 + Real.log (2 * Lc) ≤ 3 * Λ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcrude : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E * Lc ^ 2 / Λ ^ 4 * min Lc (1 / |t - u|))
    (hout : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E * Lc ^ 2 / W ^ 2 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (6 + 2 / Real.log 2) * (E * Lc ^ 2 / W ^ 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hC : (0 : ℝ) ≤ E * Lc ^ 2 / Λ ^ 4 := by positivity
  have hD : (0 : ℝ) ≤ E * Lc ^ 2 / W ^ 2 := by positivity
  -- `|T| ≤ 1`, since `T ⊆ [-1/2,1/2]`
  have hTfin : volume T ≤ 1 := by
    refine le_trans (measure_mono hTsub) ?_
    rw [Real.volume_Icc]
    norm_num
  have hT1 : (volume T).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (by norm_num) hTfin
    simpa using h
  have hbracket : (0 : ℝ) ≤ 2 * (E * Lc ^ 2 / Λ ^ 4) * (1 + Real.log (2 * Lc))
      + 2 * (E * Lc ^ 2 / W ^ 2) / Real.log 2 := by
    have hlog : (0 : ℝ) ≤ Real.log (2 * Lc) := Real.log_nonneg (by linarith)
    have h1 : (0 : ℝ) ≤ 2 * (E * Lc ^ 2 / Λ ^ 4) * (1 + Real.log (2 * Lc)) := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (E * Lc ^ 2 / W ^ 2) / Real.log 2 := by positivity
    linarith
  refine le_trans (integral_sq_setIntegral_indicator_normSq_le_of_setIntegral hY y hσ L hLmeas
    hSmeas hTm hTsub hC hLc hD hε0 hε1 hcrude ?_) ?_
  · intro t ht u hu htu hτ
    refine le_trans (hout t ht u hu htu hτ) (le_of_eq ?_)
    rw [div_div]
  · refine le_trans (mul_le_mul_of_nonneg_right hT1 hbracket) ?_
    rw [one_mul]
    exact harper_outer_total_le hE hΛ hW hWΛ hlogL

/-! ### The range bounds at the chain's cutoff and the barrier top

`RMF.integral_sq_setIntegral_indicator_normSq_harper_le` takes its two range bounds as
hypotheses.  Discharging them at Harper's data needs the barrier bound at the chain's tilt cutoff
rather than the display's, and the block count at the barrier top `b` rather than at `N`. -/

/-- **The display's bound, at a larger tilt cutoff.**  One line from
`RMF.tiltedMeasure₂_barrierEventPair_congr_cutoff`, and the shape every range wants: the display
produces its bound at `blockCutoff θ n`, the chain reads the measure at `blockCutoff θ N`. -/
theorem tiltedMeasure₂_barrier_le_of_cutoff {Y : ℕ → Ω → ℂ} {ν : Measure Ω}
    (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re)
    {n N : ℕ} (hnN : n ≤ N) (u₁ v₁ u₂ v₂ : ℕ → ℝ) {C : ℝ}
    (h : (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ n) s₁ s₂ ν
        (barrierEventPair (blockPair θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal ≤ C) :
    (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N) s₁ s₂ ν
        (barrierEventPair (blockPair θ s₁ s₂ Y) n u₁ v₁ u₂ v₂)).toReal ≤ C := by
  rwa [tiltedMeasure₂_barrierEventPair_congr_cutoff hY θ hs₁ hs₂ hnN u₁ v₁ u₂ v₂]

/-- **`b ≥ N - \log V - 3`.**  The barrier stops `⌊\log V⌋+3` blocks short of the product's top;
in the reals that costs at most `\log V + 3`, and only for `V ≥ 1` — below `1` the floor is `0`
and the bound would run the wrong way. -/
lemma harperBarrierTop_ge {B : ℕ} {V x : ℝ} (hV : 1 ≤ V)
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x) :
    (harperN B x : ℝ) - Real.log V - 3 ≤ (harperBarrierTop B V x : ℝ) := by
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hfl : ((⌊Real.log V⌋₊ : ℕ) : ℝ) ≤ Real.log V := Nat.floor_le hlogV
  have hcast : ((harperBarrierTop B V x : ℕ) : ℝ)
      = (harperN B x : ℝ) - ((⌊Real.log V⌋₊ : ℕ) : ℝ) - 3 := by
    have h1 : harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) = harperN B x := by
      rw [harperBarrierTop]
      omega
    have h2 : ((harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) : ℕ) : ℝ)
        = ((harperN B x : ℕ) : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  rw [hcast]
  linarith

/-- **The intersection of the two one-coordinate barriers is the pair barrier at
`RMF.blockPair`.**  Definitionally so: `RMF.barrierEventPair` projects its family, and the
projections of `RMF.blockPair` reduce by `rfl`.  Distinct from
`RMF.barrierEvent_inter_eq_barrierEventPair`, whose right-hand side is the *sum of pairs* rather
than the pair of sums — equal, but only after `Finset.sum`'s two projections are pushed through,
which is an expensive unification to ask of `exact`. -/
lemma barrierEvent_inter_eq_blockPair {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {θ : ℝ} {N : ℕ}
    {s₁ s₂ : ℂ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} :
    barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω)) N u₁ v₁
        ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)) N u₂ v₂
      = barrierEventPair (blockPair θ s₁ s₂ Y) N u₁ v₁ u₂ v₂ := rfl

/-- **`RMF.exists_measure_barrier_top_harper_le` with its constants left free.**
Cutting the tilted measure down to the top block moves none of them. -/
theorem le_measure_barrier_top_harper_of_inter.{u}
    {κ Cst θ₀ : ℝ} {n₀ : ℕ}
    (hbound :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m V : ℝ) (N : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          θ₀ ≤ θ → harperR |t - u| + harperD V + 4 ≤ N →
          n₀ ≤ N - harperD V - harperR |t - u| →
          |σ| * Real.log (blockScale θ (N + 1)) ≤ 4 * V →
          0 < |t - u| → |t - u| ≤ 1 →
          (1 : ℝ) ≤ a →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((N - harperD V - harperR |t - u| : ℕ) : ℝ) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun mm ω => ∑ p ∈ primeBlockSub θ mm,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a Λ q m V : ℝ) (N b : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
        θ₀ ≤ θ → 0 ≤ σ → b ≤ N →
        harperR |t - u| + harperD V + 4 ≤ b →
        n₀ ≤ b - harperD V - harperR |t - u| →
        |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
        0 < |t - u| → |t - u| ≤ 1 →
        1 ≤ a → (∀ j, 1 ≤ j → j ≤ b → |hf j| ≤ 10 * Real.log j) →
        1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
        a ≤ m + κ * Real.log (2 / |t - u|) →
        Λ ≤ 4 * ((b - harperD V - harperR |t - u| : ℕ) : ℝ) →
          (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
              (shiftLine σ t) (shiftLine σ u) ν
              (barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
            ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  intro Ω' _ Y ν hY θ σ a Λ q m V N b t u hf hθ hσ hbN hrdb hn₀b hσtop hτ0 hτ1 ha hhf hΛ hq0
    hq1 hm0 hmΛ hmq ham hn4
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [re_shiftLine]; linarith
  have hdisp := hbound Ω' Y ν hY θ σ a Λ q m V b t u hf hθ hrdb hn₀b hσtop hτ0 hτ1 ha hhf hΛ
    hq0 hq1 hm0 hmΛ hmq ham hn4
  rw [barrierEvent_inter_eq_blockPair] at hdisp
  exact tiltedMeasure₂_barrier_le_of_cutoff hY θ hs₁ hs₂ hbN
    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
    (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j) hdisp

/-- **The barrier bound the chain consumes**: the barrier over `b` blocks (Harper's `L(t)`, which
stops `⌊\log V⌋+3` short) under the tilt at `blockCutoff θ N`.  It follows from
`RMF.exists_measure_barrier_inter_harper_data_le` at `(θ, b)`,
`RMF.barrierEvent_inter_eq_barrierEventPair` and `RMF.tiltedMeasure₂_barrier_le_of_cutoff`.  The
tilt condition is read at `b`, `|σ|\log x_{b+1} ≤ 4V`, which at Harper's data holds with a factor
`e³` to spare. -/
theorem exists_measure_barrier_top_harper_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ (n₀ : ℕ) (θ₀ : ℝ),
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m V : ℝ) (N b : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          θ₀ ≤ θ → 0 ≤ σ → b ≤ N →
          harperR |t - u| + harperD V + 4 ≤ b →
          n₀ ≤ b - harperD V - harperR |t - u| →
          |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
          0 < |t - u| → |t - u| ≤ 1 →
          1 ≤ a → (∀ j, 1 ≤ j → j ≤ b → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((b - harperD V - harperR |t - u| : ℕ) : ℝ) →
            (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν
                (barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, hCst, n₀, θ₀, hbound⟩ := exists_measure_barrier_inter_harper_data_le κ hκ
  exact ⟨Cst, hCst, n₀, θ₀, le_measure_barrier_top_harper_of_inter hbound⟩

/-- **`RMF.exists_setIntegral_normSq_pair_far_harper_le` with its constants left free.**
Reading the far range end to end at Harper's data moves none of `Cst`, `n₀`, `θ₀`. -/
theorem le_setIntegral_normSq_pair_far_harper_of_barrier.{u}
    {κ Cst θ₀ : ℝ} {n₀ : ℕ} (hCst : 0 < Cst)
    (hbar :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m V : ℝ) (N b : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          θ₀ ≤ θ → 0 ≤ σ → b ≤ N →
          harperR |t - u| + harperD V + 4 ≤ b →
          n₀ ≤ b - harperD V - harperR |t - u| →
          |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
          0 < |t - u| → |t - u| ≤ 1 →
          1 ≤ a → (∀ j, 1 ≤ j → j ≤ b → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((b - harperD V - harperR |t - u| : ℕ) : ℝ) →
            (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν
                (barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'],
      ∃ K > 0,
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a Λ q m V τ0 : ℝ) (N b : ℕ) (t u : ℝ),
        θ₀ ≤ θ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
        harperR |t - u| + harperD V + 4 ≤ b →
        n₀ ≤ b - harperD V - harperR |t - u| →
        |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
        0 < |t - u| → |t - u| ≤ 1 →
        1 ≤ a → 1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
        a ≤ m + κ * Real.log (2 / |t - u|) →
        Λ ≤ 4 * ((b - harperD V - harperR |t - u| : ℕ) : ℝ) →
        1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
        1 / σ ≤ Real.log (blockScale θ (N + 1)) →
            (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
                ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (blockCutoff θ N) (shiftLine σ t) ω‖ ^ 2
                  * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff θ N) (shiftLine σ u) ω‖ ^ 2 ∂ν)
              ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
                  * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
                  * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  intro Ω' _
  obtain ⟨K, hK, hfarsrc⟩ := exists_setIntegral_normSq_pair_far_le (Ω := Ω')
  refine ⟨K, hK, ?_⟩
  intro Y ν hY θ σ a Λ q m V τ0 N b t u hθ hσ0 hσhalf hbN hrdb hn₀b hσtop hτ0 hτ1 ha hΛ hq0 hq1
    hm0 hmΛ hmq ham hn4 hτ0le hτ0σ hσN
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [re_shiftLine]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [re_shiftLine]; linarith
  have hAm : MeasurableSet
      (barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
        (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
        (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)) :=
    measurableSet_barrierEventPair
      (measurable_blockPair hY θ (shiftLine σ t) (shiftLine σ u)) b _ _ _ _
  have hbarA := hbar Ω' Y ν hY θ σ a Λ q m V N b t u harperHf hθ hσ0.le hbN hrdb hn₀b hσtop
    hτ0 hτ1 ha (fun j _ _ => abs_harperHf_le j) hΛ hq0 hq1 hm0 hmΛ hmq ham hn4
  have hfar := hfarsrc Y ν hY θ σ τ0 t u Cst (1 + (1 - q) * Real.sqrt Λ) N _ hσ0 hσhalf
    hτ0 hτ1
    hτ0le hτ0σ hσN hCst.le hbarA
  rw [hf.setIntegral_normSq_mul_normSq_eq (blockCutoff θ N) hs₁ hs₂ hAm]
  exact hfar

/-- **The far range, end to end at Harper's data**: the `hout` shape of
`RMF.integral_sq_setIntegral_indicator_normSq_harper_le`, with the barrier probability from
`RMF.exists_measure_barrier_top_harper_le` and the free moment from
`RMF.exists_setIntegral_normSq_pair_far_le`.  On the far range `τ0 = 2e^{2θ+2}` bounds `1/|t-u|`,
so `τ0²\log⁴(2τ0)` is bounded in terms of `θ`; `1/σ = \log x/(4V) = L/4`. -/
theorem exists_setIntegral_normSq_pair_far_harper_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∃ (n₀ : ℕ) (θ₀ : ℝ),
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ K > 0,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m V τ0 : ℝ) (N b : ℕ) (t u : ℝ),
          θ₀ ≤ θ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
          harperR |t - u| + harperD V + 4 ≤ b →
          n₀ ≤ b - harperD V - harperR |t - u| →
          |σ| * Real.log (blockScale θ (b + 1)) ≤ 4 * V →
          0 < |t - u| → |t - u| ≤ 1 →
          1 ≤ a → 1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          Λ ≤ 4 * ((b - harperD V - harperR |t - u| : ℕ) : ℝ) →
          1 / |t - u| ≤ τ0 → 2 * τ0 + 7 ≤ 1 / σ →
          1 / σ ≤ Real.log (blockScale θ (N + 1)) →
              (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
                  ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                      (blockCutoff θ N) (shiftLine σ t) ω‖ ^ 2
                    * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                        (blockCutoff θ N) (shiftLine σ u) ω‖ ^ 2 ∂ν)
                ≤ Cst * K * (2 * τ0 + 7) ^ 2 * Real.log (2 * (2 * τ0 + 7)) ^ 4
                    * ((1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2)
                    * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨Cst, hCst, n₀, θ₀, hbar⟩ := exists_measure_barrier_top_harper_le κ hκ
  exact ⟨Cst, hCst, n₀, θ₀,
    le_setIntegral_normSq_pair_far_harper_of_barrier hCst hbar⟩

/-! ### `hbar`, and why it is not the display

`RMF.setIntegral_normSq_pair_middle_le`'s `hbar` bounds the shifted barrier, at the widened level
`A = \text{shiftLevel } a\,r\,hf` that `RMF.barrierEventPair_subset_shift` produces; the display
bounds the unshifted barrier at level `a`, shifting internally.

The source is `RMF.exists_proposition7_upper_steinhaus`, which bounds exactly the shifted barrier
by `Cst\min\{1, A/√n\}²`, followed by `RMF.min_one_div_sqrt_sq_le` at `A` through
`RMF.shiftLevel_le_of_le` and `a ≤ m`: the display's own two steps, stopped before the transport
back to the unshifted barrier. -/

/-- The shifted pair family, as `RMF.blockPair`.  `RMF.exists_proposition7_upper_steinhaus` states
its barrier with the *sum of pairs*; the chain reads the *pair of sums*. -/
lemma barrierEventPair_sumPair_shift_eq {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (θ : ℝ) (s₁ s₂ : ℂ)
    (r n : ℕ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    barrierEventPair (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) n u₁ v₁ u₂ v₂
      = barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁ v₁ u₂ v₂ := by
  have hpair : ∀ (m : ℕ) (ω : Ω'), (∑ p ∈ primeBlockSub θ (m + r),
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)))
      = blockPair θ s₁ s₂ Y (m + r) ω :=
    fun m ω => congrFun (sum_pair_eq (fun p ω =>
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) (primeBlockSub θ (m + r))) ω
  rw [barrierEventPair, barrierEventPair]
  congr 1
  · congr 1
    funext m ω
    rw [hpair m ω]
  · congr 1
    funext m ω
    rw [hpair m ω]

/-- **`RMF.exists_measure_barrierEventPair_shift_display_le` with its constants left free.**
Passing Proposition 7 to the display scales the constant by the window factor and leaves
the window `T_{sh}` alone. -/
theorem le_measure_barrierEventPair_shift_display_of_prop7.{u} {κ Cst Tsh : ℝ}
    (hκ : 0 ≤ κ) (hCst : 0 < Cst)
    (hprop7 :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < n →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a → 4 ≤ n →
          4 * Real.log n ^ 20 ≤ (n : ℝ) → 4 * Real.log n ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ (m + r),
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) n
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (a / Real.sqrt n) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ →
      ∀ (θ σ τ a Λ q m : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf hg : ℕ → ℝ),
        (125 : ℝ) ≤ θ → 1 ≤ r → r + n ≤ N →
        s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∀ mm, mm < n →
          boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
              + blockWindow mm + blockWindow mm + 13
            ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
        max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r hf → 4 ≤ n →
        4 * Real.log (n : ℝ) ^ 20 ≤ (n : ℝ) →
        4 * Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) * (1 / 18) →
        (∀ j, 1 ≤ j → j ≤ n → |hg j| ≤ 10 * Real.log j) →
        (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
        1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
        a ≤ m + κ * Real.log (2 / τ) →
        0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / τ) + 1 → Λ ≤ 4 * (n : ℝ) →
          ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
              (blockCutoff θ N) s₁ s₂ μ)
            (barrierEventPair (fun mm => blockPair θ s₁ s₂ X (mm + r)) n
              (fun j => -shiftLevel a r hf - blockSlope 125 * j)
              (fun j => shiftLevel a r hf + j + hg j)
              (fun j => -shiftLevel a r hf - blockSlope 125 * j)
              (fun j => shiftLevel a r hf + j + hg j))).toReal
            ≤ Cst * (4 * (4 / Real.log 2 + 2 * displayWindowConst κ) ^ 2)
                * Real.log (2 / τ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  rw [displayWindowConst]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB := (blockSlope_pos 125).le
  set K : ℝ := 42 + 2 * blockSlope 125 + (31 + blockSlope 125) / Real.log 2 + 2 * κ
    with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    positivity
  intro Ω' _ X μ hX θ σ τ a Λ q m N r n s₁ s₂ hf hg hθ hr1 hrn hre₁ hre₂ hσtop hτ0 hτ1 hτeq
    hTshle henvc ha hn4 hbig hbig2 hhg hhf hΛ hq0 hq1 hm0 hmΛ hmq ham ha0 hr hn3
  have hn1 : 1 ≤ n := by omega
  have hlev : shiftLevel a r hf ≤ 2 * m + K * Real.log (2 / τ) := by
    have h := shiftLevel_le_of_le (a := a) (hf := hf) hτ0 hτ1 hr (hhf r hr1 (by omega))
    have hKL : K * Real.log (2 / τ)
        = (42 + 2 * blockSlope 125 + (31 + blockSlope 125) / Real.log 2)
            * Real.log (2 / τ) + 2 * (κ * Real.log (2 / τ)) := by
      rw [hKdef]
      ring
    linarith [h, ham, hKL]
  have harith := min_one_div_sqrt_sq_le (Λ := Λ) (a := shiftLevel a r hf) (τ := τ) (K := K)
    (q := q) (m := m) (n := n) hΛ hq0 hq1 hτ0 hτ1 hK0 hn1 hm0 hmΛ hmq
    (le_trans ha0 (le_shiftLevel ha0 r hf)) hlev (by norm_num) hn3
  have hprop := hprop7 Ω' X μ hX θ σ τ (shiftLevel a r hf) N r n s₁ s₂ hg hθ hrn hre₁ hre₂
    hσtop hτ0 hτ1 hτeq hTshle henvc ha hn4 hbig hbig2 hhg
  rw [barrierEventPair_sumPair_shift_eq] at hprop
  refine le_trans hprop ?_
  calc Cst * min 1 (shiftLevel a r hf / Real.sqrt n) ^ 2
      ≤ Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2 * Real.log (2 / τ) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := mul_le_mul_of_nonneg_left harith hCst.le
    _ = Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2) * Real.log (2 / τ) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by ring

/-- **`hbar` at Harper's data.**  Proposition 7 at the shifted family, converted by the `Λ`
arithmetic — the same two steps the display takes, stopped before the transport back. -/
theorem exists_measure_barrierEventPair_shift_display_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a Λ q m : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf hg : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < n →
            boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
                + blockWindow mm + blockWindow mm + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r hf → 4 ≤ n →
          4 * Real.log (n : ℝ) ^ 20 ≤ (n : ℝ) →
          4 * Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hg j| ≤ 10 * Real.log j) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / τ) →
          0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / τ) + 1 → Λ ≤ 4 * (n : ℝ) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair (fun mm => blockPair θ s₁ s₂ X (mm + r)) n
                (fun j => -shiftLevel a r hf - blockSlope 125 * j)
                (fun j => shiftLevel a r hf + j + hg j)
                (fun j => -shiftLevel a r hf - blockSlope 125 * j)
                (fun j => shiftLevel a r hf + j + hg j))).toReal
              ≤ Cst * Real.log (2 / τ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hprop7⟩ := exists_proposition7_upper_steinhaus
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : (0 : ℝ) ≤ displayWindowConst κ := displayWindowConst_nonneg hκ
  exact ⟨Cst * (4 * (4 / Real.log 2 + 2 * displayWindowConst κ) ^ 2), Tsh, by positivity, hTsh,
    le_measure_barrierEventPair_shift_display_of_prop7 hκ hCst hprop7⟩

/-- **`RMF.exists_setIntegral_normSq_pair_middle_harper_le` with its constants left free.**
Reading the middle range end to end at Harper's data moves neither `Cst` nor `T_{sh}`. -/
theorem le_setIntegral_normSq_pair_middle_harper_of_shift.{u}
    {κ Cst Tsh : ℝ} (hCst : 0 < Cst)
    (hbarsrc :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a Λ q m : ℝ) (N r n : ℕ) (s₁ s₂ : ℂ) (hf hg : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + n ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (r + n + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < n →
            boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
                + blockWindow mm + blockWindow mm + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r hf → 4 ≤ n →
          4 * Real.log (n : ℝ) ^ 20 ≤ (n : ℝ) →
          4 * Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ n → |hg j| ≤ 10 * Real.log j) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / τ) →
          0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / τ) + 1 → Λ ≤ 4 * (n : ℝ) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair (fun mm => blockPair θ s₁ s₂ X (mm + r)) n
                (fun j => -shiftLevel a r hf - blockSlope 125 * j)
                (fun j => shiftLevel a r hf + j + hg j)
                (fun j => -shiftLevel a r hf - blockSlope 125 * j)
                (fun j => shiftLevel a r hf + j + hg j))).toReal
              ≤ Cst * Real.log (2 / τ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'],
      ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a Λ q m ϑ t u : ℝ) (N b r : ℕ),
        (125 : ℝ) ≤ θ → θ ≤ ϑ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
        splitIndex θ b (t - u) + 2 ≤ r → r ≤ b →
        1 ≤ splitIndex θ b (t - u) → ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b →
        0 < |t - u| → |t - u| ≤ 1 →
        Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) →
        Real.log (2 / |t - u|) ≤ 2 * (b : ℝ) →
        |σ| * Real.log (blockScale θ (b + 1)) ≤ 1 →
        Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
        (∀ mm, mm < b - r →
          boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
              + blockWindow mm + blockWindow mm + 13
            ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
        max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r harperHf → 4 ≤ b - r →
        4 * Real.log ((b - r : ℕ) : ℝ) ^ 20 ≤ ((b - r : ℕ) : ℝ) →
        4 * Real.log ((b - r : ℕ) : ℝ) ^ 8 ≤ ((b - r : ℕ) : ℝ) * (1 / 18) →
        1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
        a ≤ m + κ * Real.log (2 / |t - u|) →
        0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / |t - u|) + 1 → Λ ≤ 4 * ((b - r : ℕ) : ℝ) →
        Real.exp ((splitIndex θ b (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
        1 / σ ≤ Real.log (blockScale θ (N + 1)) →
            (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
                ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                    (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
                  * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                      (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
              ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cst * KQ * CP * bottomConst ϑ
                  * (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2
                  * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  intro Ω' _
  obtain ⟨KQ, hKQ, hQsrc⟩ := exists_integral_normSq_high_splitIndex_le (Ω := Ω')
  obtain ⟨CP, hCP, hPsrc⟩ := exists_integral_normSq_low_splitIndex_add_two_le (Ω := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY θ σ a Λ q m ϑ t u N b r hθ hθϑ hσ0 hσhalf hbN hsr hrb hsplit1 hfloor hτ0 hτ1
    hsmall hmb hσtop hTshle henvc hares hn4 hbig hbig2 hΛ hq0 hq1 hm0 hmΛ hmq ham ha0 hr hn3 hNM
    hMN
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hre₁ : (shiftLine σ t).re = 1 / 2 + σ := re_shiftLine σ t
  have hre₂ : (shiftLine σ u).re = 1 / 2 + σ := re_shiftLine σ u
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hW : (1 : ℝ) + (1 - q) * Real.sqrt Λ ≠ 0 := by
    have hs : (1 : ℝ) ≤ Real.sqrt Λ := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hΛ
    nlinarith
  -- `hbarD`
  have hbarD := hbarsrc Ω' Y ν hY θ σ |t - u| a Λ q m N r (b - r) (shiftLine σ t)
    (shiftLine σ u) harperHf (fun mm => 10 * Real.log mm) hθ (by omega) (by omega) hre₁ hre₂
    (by rw [show r + (b - r) + 1 = b + 1 from by omega]; exact hσtop) hτ0 hτ1
    (by rw [im_shiftLine, im_shiftLine]) hTshle henvc hares hn4 hbig hbig2
    (fun j _ _ => le_of_eq (abs_of_nonneg (by
      have h0 := Real.log_natCast_nonneg j
      positivity)))
    (fun j _ _ => abs_harperHf_le j) hΛ hq0 hq1 hm0 hmΛ hmq ham ha0 hr hn3
  -- `hQ` and `hPt`
  have hQ := hQsrc Y ν hY θ σ t u b N (by linarith) hσ0 hσhalf hτ0 hτ1 hfloor hNM hMN
  have hPt := hPsrc (fun ω => compMultExtension fun p => Y p ω) ν hf θ σ (t - u) b
    (shiftLine σ t) hθ0 hσ0.le hre₁ hsplit1
  -- `hP0`
  have hP0 := integral_normSq_pair_bottom_le hf hθϑ hre₁ hre₂ hσ0.le
  refine setIntegral_normSq_pair_middle_harper_le hY hbN hθ0 hσ0.le hτ0 hτ1 hsmall hmb hsr
    hrb hCst.le hKQ.le hCP.le hW hbarD ?_ ?_ hP0
  · refine le_trans hQ (le_of_eq ?_)
    rw [div_eq_mul_inv, mul_comm |t - u| (1 / σ)]
    field_simp
  · exact hPt

/-- **The middle range, end to end at Harper's data**: the inputs of
`RMF.setIntegral_normSq_pair_middle_harper_le` supplied (`hbarD` by
`RMF.exists_measure_barrierEventPair_shift_display_le`, `hQ` at `L = 1/σ`, `hPt`, `hP0`).  `KQ` and
`CP` are chosen after `Ω'`, as their sources are, and before `θ, σ, a, t, u, N, b, r`: one constant
for every pair `(t, u)`, as `RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges` needs.
-/
theorem exists_setIntegral_normSq_pair_middle_harper_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'],
        ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a Λ q m ϑ t u : ℝ) (N b r : ℕ),
          (125 : ℝ) ≤ θ → θ ≤ ϑ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
          splitIndex θ b (t - u) + 2 ≤ r → r ≤ b →
          1 ≤ splitIndex θ b (t - u) → ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b →
          0 < |t - u| → |t - u| ≤ 1 →
          Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) →
          Real.log (2 / |t - u|) ≤ 2 * (b : ℝ) →
          |σ| * Real.log (blockScale θ (b + 1)) ≤ 1 →
          Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ mm, mm < b - r →
            boxEnvelope (blockSlope 125) mm + boxEnvelope (blockSlope 125) (mm + 1)
                + blockWindow mm + blockWindow mm + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (mm + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ shiftLevel a r harperHf → 4 ≤ b - r →
          4 * Real.log ((b - r : ℕ) : ℝ) ^ 20 ≤ ((b - r : ℕ) : ℝ) →
          4 * Real.log ((b - r : ℕ) : ℝ) ^ 8 ≤ ((b - r : ℕ) : ℝ) * (1 / 18) →
          1 ≤ Λ → 0 ≤ q → q ≤ 1 → 0 ≤ m → m ≤ Real.sqrt Λ → m * (1 - q) ≤ 1 →
          a ≤ m + κ * Real.log (2 / |t - u|) →
          0 ≤ a → (r : ℝ) ≤ 2 * Real.log (2 / |t - u|) + 1 → Λ ≤ 4 * ((b - r : ℕ) : ℝ) →
          Real.exp ((splitIndex θ b (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
          1 / σ ≤ Real.log (blockScale θ (N + 1)) →
              (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
                  ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                      (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
                    * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                        (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
                ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * Cst * KQ * CP * bottomConst ϑ
                    * (1 / σ) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2
                    * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbarsrc⟩ :=
    exists_measure_barrierEventPair_shift_display_le κ hκ
  exact ⟨Cst, Tsh, hCst, hTsh,
    le_setIntegral_normSq_pair_middle_harper_of_shift hCst hbarsrc⟩

/-! ### The crude range, end to end at Harper's data

Two instantiations of `RMF.setIntegral_normSq_pair_crude_le`, exactly as its docstring says.  The
first regime reuses every supplier the middle range uses, minus the barrier probability — which is
the point of the crude range: below `(\log x)^{-1/3}` the `1/Λ⁴` in (5.2) is enough on its own and
the indicators are thrown away. -/

/-- **The crude range's first regime, end to end.**  `τ ≥ 1/L`, split at
`RMF.splitIndex θ b (t-u) + 2`. -/
theorem exists_setIntegral_normSq_pair_crude_split_harper_le {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a ϑ t u : ℝ) (N b : ℕ),
      (125 : ℝ) ≤ θ → θ ≤ ϑ → 0 < σ → σ ≤ 1 / 2 → b ≤ N →
      splitIndex θ b (t - u) + 2 ≤ b → 1 ≤ splitIndex θ b (t - u) →
      ⌊Real.log (1 / |t - u|) - θ⌋₊ ≤ b →
      0 < |t - u| → |t - u| ≤ 1 →
      Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t - u|) →
      Real.log (2 / |t - u|) ≤ 2 * (b : ℝ) →
      Real.exp ((splitIndex θ b (t - u) : ℝ) + 2 + θ) ≤ 1 / σ →
      1 / σ ≤ Real.log (blockScale θ (N + 1)) →
      (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ (4 * Real.exp 1 ^ 2 * Real.exp (a - θ)) ^ 2 * KQ * CP * bottomConst ϑ / σ ^ 2
            * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 4)) := by
  obtain ⟨KQ, hKQ, hQsrc⟩ := exists_integral_normSq_high_splitIndex_le (Ω := Ω')
  obtain ⟨CP, hCP, hPsrc⟩ := exists_integral_normSq_low_splitIndex_add_two_le (Ω := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY θ σ a ϑ t u N b hθ hθϑ hσ0 hσhalf hbN hsp hsplit1 hfloor hτ0 hτ1 hsmall hmb
    hNM hMN
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hre₁ : (shiftLine σ t).re = 1 / 2 + σ := re_shiftLine σ t
  have hre₂ : (shiftLine σ u).re = 1 / 2 + σ := re_shiftLine σ u
  have hθ0 : (0 : ℝ) ≤ θ := by linarith
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [hre₂]; linarith
  have hQ := hQsrc Y ν hY θ σ t u b N (by linarith) hσ0 hσhalf hτ0 hτ1 hfloor hNM hMN
  have hPt := hPsrc (fun ω => compMultExtension fun p => Y p ω) ν hf θ σ (t - u) b
    (shiftLine σ t) hθ0 hσ0.le hre₁ hsplit1
  have hP0 := integral_normSq_pair_bottom_le hf hθϑ hre₁ hre₂ hσ0.le
  have h52 := exp_envelope_splitIndex_add_two_sq_le (θ := θ) (m := b) (t := t - u) hθ0 hτ0
    hsmall hmb a
  exact setIntegral_normSq_pair_crude_split_le hY θ hs₁ hs₂ (k := splitIndex θ b (t - u) + 1)
    (by omega) hbN hKQ.le hCP.le (one_le_bottomConst ϑ |>.trans' zero_le_one) hτ0 hσ0
    (log_two_div_pos hτ0 hτ1).ne' h52 hQ hPt hP0

/-- **The crude range's second regime, end to end.**  `τ < 1/L`, split at the barrier's own top
`k + 1 = b`, where `Q` is the `⌊\log V⌋+3` blocks between `x_b` and `x` and neither moment sees
`1/τ` at all. -/
theorem exists_setIntegral_normSq_pair_crude_top_harper_le {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ KQ CP : ℝ, 0 < KQ ∧ 0 < CP ∧
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a ϑ t u : ℝ) (N b M : ℕ),
      (0 : ℝ) ≤ θ → θ ≤ ϑ → 0 ≤ σ → 1 ≤ b → b ≤ N →
      (400 : ℝ) ≤ ((⌊blockScale θ b⌋₊ : ℕ) : ℝ) →
      ⌊blockScale θ b⌋₊ ≤ M → M ≤ ⌊blockScale θ (N + 1)⌋₊ →
      1 ≤ 2 * σ * Real.log (M : ℝ) →
      (∫ ω in barrierEventPair (blockPair θ (shiftLine σ t) (shiftLine σ u) Y) b
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j)
          (fun j => -a - blockSlope 125 * j) (fun j => a + j + harperHf j),
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Real.exp (a + (b : ℝ) + harperHf b) ^ 2
            * (KQ * (Real.log (M : ℝ)
                / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ)) ^ 4)
            * CP * bottomConst ϑ * Real.log (blockScale θ b) := by
  obtain ⟨KQ, hKQ, hQsrc⟩ := exists_integral_normSq_pairIco_split_shift_le (Ω := Ω')
  obtain ⟨CP, hCP, hPsrc⟩ := exists_integral_norm_randomEulerProductIco_sq_le (Ω := Ω')
  refine ⟨KQ, CP, hKQ, hCP, ?_⟩
  intro Y ν hY θ σ a ϑ t u N b M hθ hθϑ hσ0 hb1 hbN h400 hbM hMN hMtilt
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hre₁ : (shiftLine σ t).re = 1 / 2 + σ := re_shiftLine σ t
  have hre₂ : (shiftLine σ u).re = 1 / 2 + σ := re_shiftLine σ u
  have hs₁ : (0 : ℝ) < (shiftLine σ t).re := by rw [hre₁]; linarith
  have hs₂ : (0 : ℝ) < (shiftLine σ u).re := by rw [hre₂]; linarith
  have hQ := hQsrc Y ν hY σ t u (⌊blockScale θ b⌋₊) M (⌊blockScale θ (N + 1)⌋₊) hσ0 h400 hbM
    hMN hMtilt
  have hy₀ : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ b⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le b)))
  have hPt := hPsrc (fun ω => compMultExtension fun p => Y p ω) ν hf (⌊blockScale θ 0⌋₊ + 1)
    (blockScale θ b) (shiftLine σ t) σ (two_le_blockScale hθ b) hy₀ hσ0 hre₁
  have hP0 := integral_normSq_pair_bottom_le hf hθϑ hre₁ hre₂ hσ0
  refine setIntegral_normSq_pair_crude_top_le hY θ hs₁ hs₂ hb1 hbN
    (KQ := KQ * (Real.log (M : ℝ)
      / Real.log ((⌊blockScale θ b⌋₊ : ℕ) : ℝ)) ^ 4) (CP := CP) (K0 := bottomConst ϑ)
    (L := Real.log (blockScale θ b)) (by positivity) hCP.le
    (le_trans zero_le_one (one_le_bottomConst ϑ)) ?_ le_rfl hQ hPt hP0
  · have hlogb : (0 : ℝ) ≤ Real.log (blockScale θ b) := by
      rw [log_blockScale]
      positivity
    positivity

/-! ### Into Key Proposition 5's envelope shape

`RMF.integral_sq_setIntegral_indicator_normSq_harper_le` wants its hypotheses as
`EL_c²/Λ⁴·\min\{L_c, 1/τ\}` and `EL_c²/W²/(τ\log²(2/τ))`.  For `hout` the middle and far bounds
already end in `(\text{const})·σ^{-2}/W²·(τ\log²(2/τ))^{-1}`, with `L_c = 1/σ`; only the case
split and a `max` are missing.  For `hcrude` the first regime ends in
`(\text{const})·σ^{-2}(τ\log⁴(2/τ))^{-1}`, and on the crude range `\log(2/τ) ≥ Λ/3`, so trading
`\log⁴` for `Λ⁴` costs `81`.

The two crude regimes do not meet at `1/τ = L_c`: the first needs `\exp(j+2+θ) ≤ 1/σ`, and the
two spare blocks cost `e²`, so it covers only `1/τ ≤ L_c/e²`.  The second has no hypothesis on
`τ` and takes the rest, where `\min\{L_c, 1/τ\} ≥ L_c/e²` only; `RMF.crude_top_le_min` carries
that slack as its `K`. -/

/-- **The middle and far bounds, glued.**  Both are already `E L_c²/W²` over `τ\log²(2/τ)`; the
`max` is the only content. -/
lemma le_div_of_middle_far {E₁ E₂ Lc W τ ε' Φ : ℝ} (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hτ0 : 0 < τ)
    (hmid : τ ≤ ε' → Φ ≤ E₁ * Lc ^ 2 / W ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)))
    (hfar : ε' < τ → Φ ≤ E₂ * Lc ^ 2 / W ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2))) :
    Φ ≤ max E₁ E₂ * Lc ^ 2 / W ^ 2 / (τ * Real.log (2 / τ) ^ 2) := by
  have hfac : (0 : ℝ) ≤ 1 / (τ * Real.log (2 / τ) ^ 2) := by positivity
  have hrw : ∀ E : ℝ, E * Lc ^ 2 / W ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2))
      = E * Lc ^ 2 / W ^ 2 / (τ * Real.log (2 / τ) ^ 2) := fun E => by
    rw [mul_one_div]
  have hmono : ∀ E : ℝ, 0 ≤ E → E ≤ max E₁ E₂ →
      E * Lc ^ 2 / W ^ 2 / (τ * Real.log (2 / τ) ^ 2)
        ≤ max E₁ E₂ * Lc ^ 2 / W ^ 2 / (τ * Real.log (2 / τ) ^ 2) := by
    intro E _ hle
    gcongr
  rcases le_or_gt τ ε' with h | h
  · exact le_trans (le_trans (hmid h) (le_of_eq (hrw E₁))) (hmono E₁ hE₁ (le_max_left _ _))
  · exact le_trans (le_trans (hfar h) (le_of_eq (hrw E₂))) (hmono E₂ hE₂ (le_max_right _ _))

/-- **The crude range's first regime, in envelope shape.**  `\log(2/τ) ≥ Λ/3` on the crude range,
so `Λ⁴/\log⁴(2/τ) ≤ 81` — and `81` is the whole cost of trading the `\log⁴` (5.2) produces for the
`Λ⁴` Harper's display asks for.  It is where the crude range's `Λ^{-4}` comes from. -/
lemma crude_split_le_min {C Lc Λ τ Φ : ℝ} (hC : 0 ≤ C) (hτ0 : 0 < τ) (hΛ0 : 0 < Λ)
    (hlog : Λ / 3 ≤ Real.log (2 / τ)) (hmin : 1 / τ ≤ Lc)
    (h : Φ ≤ C * (1 / (τ * Real.log (2 / τ) ^ 4))) :
    Φ ≤ 81 * C / Λ ^ 4 * min Lc (1 / τ) := by
  have hlog0 : (0 : ℝ) < Real.log (2 / τ) := by linarith
  have hmineq : min Lc (1 / τ) = 1 / τ := min_eq_right hmin
  rw [hmineq]
  refine le_trans h (le_of_eq_of_le rfl ?_)
  -- `C/(τ\log⁴) ≤ 81C/(Λ⁴τ)` reduces to `Λ⁴ ≤ 81\log⁴`
  have hpow : Λ ^ 4 ≤ 81 * Real.log (2 / τ) ^ 4 := by
    have h3 : Λ ≤ 3 * Real.log (2 / τ) := by linarith
    have hcube : Λ ^ 4 ≤ (3 * Real.log (2 / τ)) ^ 4 :=
      pow_le_pow_left₀ hΛ0.le h3 4
    calc Λ ^ 4 ≤ (3 * Real.log (2 / τ)) ^ 4 := hcube
      _ = 81 * Real.log (2 / τ) ^ 4 := by ring
  rw [mul_one_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ C * τ)
  linarith [hkey]

/-- **The crude range's second regime, in envelope shape**: `σ³L_b³/n_b⁴ = (σL_b)³(1/n_b)⁴` is
bounded because `σL_b ≤ S` (the drop) and `Λ ≤ 2n_b` (the barrier top is `Λ - O(1)`).  At Harper's
data `σL_b = 4Ve^{-⌊\log V⌋-4} ≤ 4/e³`, the `V` cancelling
(`RMF.sigma_mul_log_blockScale_barrierTop_le`). -/
lemma crude_top_le_min {C S σ Lb Λ nb Lc K τ Φ : ℝ} (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hσ0 : 0 < σ) (hΛ0 : 0 < Λ) (hnb0 : 0 < nb) (hLb0 : 0 ≤ Lb) (hK : 1 ≤ K)
    (hσLb : σ * Lb ≤ S) (hΛb : Λ ≤ 2 * nb) (hLc : Lc = 1 / σ) (hmin : Lc ≤ K * (1 / τ))
    (h : Φ ≤ C * Lb ^ 3 / nb ^ 4) :
    Φ ≤ 16 * K * S ^ 3 * C * Lc ^ 2 / Λ ^ 4 * min Lc (1 / τ) := by
  have hLcpos : (0 : ℝ) < Lc := by rw [hLc]; positivity
  have hcore : Φ ≤ 16 * S ^ 3 * C * Lc ^ 2 / Λ ^ 4 * Lc := by
   rw [hLc]
   refine le_trans h ?_
   have hcube : (σ * Lb) ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ (by positivity) hσLb 3
   have hpow4 : Λ ^ 4 ≤ 16 * nb ^ 4 := by
     have h4 := pow_le_pow_left₀ hΛ0.le hΛb 4
     calc Λ ^ 4 ≤ (2 * nb) ^ 4 := h4
       _ = 16 * nb ^ 4 := by ring
   have h1 : C * Lb ^ 3 / nb ^ 4 = C * (σ * Lb) ^ 3 / (σ ^ 3 * nb ^ 4) := by
     field_simp
   have h2 : C * (σ * Lb) ^ 3 / (σ ^ 3 * nb ^ 4) ≤ C * S ^ 3 / (σ ^ 3 * nb ^ 4) := by
     gcongr
   have h3 : C * S ^ 3 / (σ ^ 3 * nb ^ 4) ≤ 16 * S ^ 3 * C / (σ ^ 3 * Λ ^ 4) := by
     rw [div_le_div_iff₀ (by positivity) (by positivity)]
     have hCS : (0 : ℝ) ≤ C * S ^ 3 := by positivity
     nlinarith [mul_le_mul_of_nonneg_left hpow4 (by positivity : (0 : ℝ) ≤ C * S ^ 3 * σ ^ 3)]
   have h4 : 16 * S ^ 3 * C * (1 / σ) ^ 2 / Λ ^ 4 * (1 / σ)
       = 16 * S ^ 3 * C / (σ ^ 3 * Λ ^ 4) := by
     field_simp
   rw [h4, h1]
   exact le_trans h2 h3
  -- `L_c ≤ K\min\{L_c, 1/τ\}`: on the first arm because `K ≥ 1`, on the second by `hmin`
  have hupg : Lc ≤ K * min Lc (1 / τ) := by
    rcases le_total Lc (1 / τ) with hc | hc
    · rw [min_eq_left hc]
      exact le_mul_of_one_le_left hLcpos.le hK
    · rw [min_eq_right hc]
      exact hmin
  have hcoef : (0 : ℝ) ≤ 16 * S ^ 3 * C * Lc ^ 2 / Λ ^ 4 := by positivity
  calc Φ ≤ 16 * S ^ 3 * C * Lc ^ 2 / Λ ^ 4 * Lc := hcore
    _ ≤ 16 * S ^ 3 * C * Lc ^ 2 / Λ ^ 4 * (K * min Lc (1 / τ)) :=
        mul_le_mul_of_nonneg_left hupg hcoef
    _ = 16 * K * S ^ 3 * C * Lc ^ 2 / Λ ^ 4 * min Lc (1 / τ) := by ring

/-- **`σ\log x_b ≤ 4/e³` at Harper's data, uniformly in `V`**: `σ ≤ 4V/\log x` and
`\log x_b = \log x\,e^{-⌊\log V⌋-4}`, so `σ\log x_b ≤ 4Ve^{-⌊\log V⌋-4}`, and
`⌊\log V⌋ > \log V - 1` gives `4/e³`.  The value oscillates with the fractional part of `\log V`
(between `0.073` and `0.182` at `V ∈ \{1, 2, 10, 10², 10³\}`). -/
lemma sigma_mul_log_blockScale_barrierTop_le {B : ℕ} {V x σ : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hσ : σ * Real.log x ≤ 4 * V) :
    σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x)) ≤ 4 / Real.exp 3 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hfl : Real.log V - 1 < ((⌊Real.log V⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log V)
    linarith
  -- `\log x_{N+1} = \log x`
  have htop : Real.log (blockScale (harperTheta B x) (harperN B x + 1)) = Real.log x := by
    rw [blockScale_harperN_succ hx1 hx]
  rw [log_blockScale] at htop
  -- the index difference
  have hcast : ((harperBarrierTop B V x : ℕ) : ℝ)
      = ((harperN B x : ℕ) : ℝ) - ((⌊Real.log V⌋₊ : ℕ) : ℝ) - 3 := by
    have h1 : harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) = harperN B x := by
      rw [harperBarrierTop]
      omega
    have h2 : ((harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) : ℕ) : ℝ)
        = ((harperN B x : ℕ) : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  -- `\log x_b = \log x \cdot e^{-⌊\log V⌋-4}`
  have hsplit : Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x))
      = Real.log x * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) := by
    rw [log_blockScale, ← htop, ← Real.exp_add]
    congr 1
    push_cast [hcast]
    ring
  rw [hsplit, ← mul_assoc]
  -- `e^{-⌊\log V⌋-4} ≤ 1/(Ve³)`
  have hexp : Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) ≤ Real.exp (-(Real.log V + 3)) :=
    Real.exp_le_exp.2 (by linarith)
  have hV0 : (0 : ℝ) < V := by linarith
  have hval : Real.exp (-(Real.log V + 3)) = 1 / (V * Real.exp 3) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hV0]
    field_simp
  have hpos : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  calc σ * Real.log x * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4))
      ≤ 4 * V * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_right hσ (Real.exp_pos _).le
    _ ≤ 4 * V * (1 / (V * Real.exp 3)) := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = 4 / Real.exp 3 := by
        field_simp

/-- **`1/σ ≤ \log x` at Harper's data.**  The other end of the free cutoff: the middle range, the
crude split and the far range all ask for `1/σ ≤ \log x_{N+1}`, and `x_{N+1} = x`, so it is just
`σ\log x ≥ 1` — which at `σ = 4V/\log x` is `V ≥ 1/4`.  Harper's `V ≥ 1` clears it with room. -/
lemma one_div_sigma_le_log_blockScale_harperN_succ {B : ℕ} {x σ : ℝ} (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x)) (hσ0 : 0 < σ)
    (hσ : 1 ≤ σ * Real.log x) :
    1 / σ ≤ Real.log (blockScale (harperTheta B x) (harperN B x + 1)) := by
  rw [blockScale_harperN_succ hx1 hx, div_le_iff₀ hσ0, mul_comm]
  exact hσ

/-- **`σ\log x_{b+1} ≤ 4/e²` at Harper's data**, the same cancellation one block higher.  The
middle range and the crude split require `|σ|\log x_{b+1} ≤ 1`, which fixes the size of the drop:
with `⌊\log V⌋ + 2` blocks in place of `⌊\log V⌋ + 3` the product is `4e^{\{\log V\}-2}`, above `1`
whenever the fractional part of `\log V` exceeds `2 - \log 4`. -/
lemma sigma_mul_log_blockScale_barrierTop_succ_le {B : ℕ} {V x σ : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hσ : σ * Real.log x ≤ 4 * V) :
    σ * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x + 1))
      ≤ 4 / Real.exp 2 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hfl : Real.log V - 1 < ((⌊Real.log V⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (Real.log V)
    linarith
  have htop : Real.log (blockScale (harperTheta B x) (harperN B x + 1)) = Real.log x := by
    rw [blockScale_harperN_succ hx1 hx]
  rw [log_blockScale] at htop
  have hcast : ((harperBarrierTop B V x : ℕ) : ℝ)
      = ((harperN B x : ℕ) : ℝ) - ((⌊Real.log V⌋₊ : ℕ) : ℝ) - 3 := by
    have h1 : harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) = harperN B x := by
      rw [harperBarrierTop]
      omega
    have h2 : ((harperBarrierTop B V x + (⌊Real.log V⌋₊ + 3) : ℕ) : ℝ)
        = ((harperN B x : ℕ) : ℝ) := by rw [h1]
    push_cast at h2
    linarith
  -- `\log x_{b+1} = \log x \cdot e^{-⌊\log V⌋-3}`
  have hsplit : Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x + 1))
      = Real.log x * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3)) := by
    rw [log_blockScale, ← htop, ← Real.exp_add]
    congr 1
    push_cast [hcast]
    ring
  rw [hsplit, ← mul_assoc]
  have hexp : Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3)) ≤ Real.exp (-(Real.log V + 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have hV0 : (0 : ℝ) < V := by linarith
  have hval : Real.exp (-(Real.log V + 2)) = 1 / (V * Real.exp 2) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hV0]
    field_simp
  have hpos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  calc σ * Real.log x * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3))
      ≤ 4 * V * Real.exp (-(((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_right hσ (Real.exp_pos _).le
    _ ≤ 4 * V * (1 / (V * Real.exp 2)) := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = 4 / Real.exp 2 := by
        field_simp

/-- **The drop hypothesis, discharged.**  `|σ|\log x_{b+1} ≤ 1` at Harper's data — the form the
middle range and the crude split ask for, and, since `1 ≤ 4V`, the far range's `≤ 4V` too. -/
lemma abs_sigma_mul_log_blockScale_barrierTop_succ_le_one {B : ℕ} {V x σ : ℝ} (hV : 1 ≤ V)
    (hx1 : 1 < x) (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x) (hσ0 : 0 ≤ σ)
    (hσ : σ * Real.log x ≤ 4 * V) :
    |σ| * Real.log (blockScale (harperTheta B x) (harperBarrierTop B V x + 1)) ≤ 1 := by
  rw [abs_of_nonneg hσ0]
  refine le_trans (sigma_mul_log_blockScale_barrierTop_succ_le hV hx1 hx hle hσ) ?_
  have hee : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [hee]
    nlinarith
  rw [div_le_one (Real.exp_pos 2)]
  exact h2

/-- **`Λ ≤ 2b` at Harper's data.**  The barrier top is `Λ - O(1)`: `N ≥ Λ - B - 3` and `b` gives up
another `\log V + 3`, so `b ≥ Λ - B - \log V - 6` and the factor `2` is cleared past
`Λ ≥ 2(B + \log V + 6)`. -/
lemma log_log_le_two_mul_barrierTop {B : ℕ} {V x : ℝ} (hV : 1 ≤ V)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log V⌋₊ + 3 ≤ harperN B x)
    (hΛ : 2 * ((B : ℝ) + Real.log V + 6) ≤ Real.log (Real.log x)) :
    Real.log (Real.log x) ≤ 2 * ((harperBarrierTop B V x : ℕ) : ℝ) := by
  have hN := harperN_ge (B := B) (x := x) hx
  have hb := harperBarrierTop_ge (B := B) (V := V) (x := x) hV hle
  linarith

/-- **(5.2) at the barrier top, as `L_b²/n_b⁴`.**  The last shape mismatch in the crude range:
`RMF.exists_setIntegral_normSq_pair_crude_top_harper_le` produces `e^{2(a+b+h(b))}` and
`RMF.crude_top_le_min` consumes `C·L_b³/n_b⁴`.  They are the same thing, because
`e^{2h(b)} = 1/b⁴` and `e^{2b} = L_b²e^{-2θ}` — the `1/b⁴` is Harper's `h(n) = -2\log n` and the
`L_b²` is the block scale, and nothing else happens. -/
lemma exp_barrier_top_sq_eq (a θ : ℝ) {b : ℕ} (hb1 : 1 ≤ b) :
    Real.exp (a + (b : ℝ) + harperHf b) ^ 2
      = Real.exp (2 * a) * Real.exp (-(2 * θ)) * Real.log (blockScale θ b) ^ 2
          / (b : ℝ) ^ 4 := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hh : Real.exp (harperHf b) = 1 / (b : ℝ) ^ 2 := exp_harperHf hb1
  have hsq : ∀ x : ℝ, Real.exp (2 * x) = Real.exp x ^ 2 := fun x => by
    rw [show (2 : ℝ) * x = x + x by ring, Real.exp_add, sq]
  have hnegθ : Real.exp (-(2 * θ)) * Real.exp θ ^ 2 = 1 := by
    rw [← hsq θ, ← Real.exp_add, show -(2 * θ) + 2 * θ = 0 by ring, Real.exp_zero]
  have key : Real.exp (2 * a) * Real.exp (-(2 * θ)) * Real.log (blockScale θ b) ^ 2
      = Real.exp a ^ 2 * Real.exp (b : ℝ) ^ 2 := by
    rw [log_blockScale, Real.exp_add, mul_pow, hsq a]
    calc Real.exp a ^ 2 * Real.exp (-(2 * θ)) * (Real.exp (b : ℝ) ^ 2 * Real.exp θ ^ 2)
        = Real.exp a ^ 2 * Real.exp (b : ℝ) ^ 2 * (Real.exp (-(2 * θ)) * Real.exp θ ^ 2) := by
          ring
      _ = Real.exp a ^ 2 * Real.exp (b : ℝ) ^ 2 := by rw [hnegθ, mul_one]
  rw [key, Real.exp_add, Real.exp_add, hh, mul_pow, mul_pow]
  field_simp

/-! ### Key Proposition 5, assembled from the four ranges

`RMF.integral_sq_setIntegral_indicator_normSq_harper_of_ranges` discharges the two range
hypotheses of `RMF.integral_sq_setIntegral_indicator_normSq_harper_le` by two case splits, the
three reconciliations above and a `max` over four constants.  Its four hypotheses are the
conclusions of `RMF.exists_setIntegral_normSq_pair_crude_split_harper_le`,
`RMF.exists_setIntegral_normSq_pair_crude_top_harper_le`,
`RMF.exists_setIntegral_normSq_pair_middle_harper_le` and
`RMF.exists_setIntegral_normSq_pair_far_harper_le`, split at `1/τ = κ` and at `τ = ε'`.

The crude boundary `κ` is a parameter: the first regime reaches only `1/τ = e^{b+θ-2}`
(`RMF.exp_splitIndex_add_two_le_of_le`), a bounded factor below `L_c`
(`L_c/e^{b+θ-2} ∈ [e⁵/4, e⁶/4]` at Harper's data), and `K`, `hκLc`, `hLcκ` carry that factor.
`ε` is Harper's `(\log x)^{-1/3}` and `ε'` the middle/far boundary `e^{-(2θ+2)}/2`; `hcrudelog`,
`Λ/3 ≤ \log(2/τ)` on the crude range, is what `RMF.crude_split_le_min` turns into `Λ^{-4}`. -/
theorem integral_sq_setIntegral_indicator_normSq_harper_of_ranges {Ω' : Type*}
    [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν)
    (y : ℕ) {σ : ℝ} (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    {C₁ C₂ E₁ E₂ S Lb nb Lc W Λ ε ε' κ K : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hS0 : 0 ≤ S)
    (hLb0 : 0 ≤ Lb) (hnb0 : 0 < nb) (hσ0 : 0 < σ) (hLceq : Lc = 1 / σ) (hLc : 1 ≤ Lc)
    (hΛ : 1 ≤ Λ) (hW : 0 < W) (hWΛ : W ^ 2 ≤ Λ) (hlogL : 1 + Real.log (2 * Lc) ≤ 3 * Λ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hσLb : σ * Lb ≤ S) (hΛb : Λ ≤ 2 * nb)
    (hK1 : 1 ≤ K) (hκLc : κ ≤ Lc) (hLcκ : Lc ≤ K * κ)
    (hcrudelog : ∀ τ : ℝ, 0 < τ → τ ≤ ε → Λ / 3 ≤ Real.log (2 / τ))
    (hcr1 : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε → 1 / |t - u| ≤ κ →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C₁ * Lc ^ 2 * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 4)))
    (hcr2 : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε → κ ≤ 1 / |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C₂ * Lb ^ 3 / nb ^ 4)
    (hmid : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| → |t - u| ≤ ε' →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E₁ * Lc ^ 2 / W ^ 2 * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)))
    (hfar : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| → ε' < |t - u| →
      (∫ ω in L t ∩ L u,
          ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ E₂ * Lc ^ 2 / W ^ 2 * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2))) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (6 + 2 / Real.log 2)
          * (max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / W ^ 2) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hΛ4 : (0 : ℝ) < Λ ^ 4 := by positivity
  have hW2 : (0 : ℝ) < W ^ 2 := pow_pos hW 2
  have hmax1 : (0 : ℝ) ≤ max (81 * C₁) (16 * K * S ^ 3 * C₂) :=
    le_trans (by positivity) (le_max_left _ _)
  have hE : (0 : ℝ) ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
    le_trans hmax1 (le_max_left _ _)
  -- `|t-u| ≤ 1`, since `T ⊆ [-1/2,1/2]`
  have hTle : ∀ t ∈ T, ∀ u ∈ T, |t - u| ≤ 1 := by
    intro t ht u hu
    have h1 := hTsub ht
    have h2 := hTsub hu
    simp only [Set.mem_Icc] at h1 h2
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine integral_sq_setIntegral_indicator_normSq_harper_le hY y hσ0.le L hLmeas hSmeas hTm
    hTsub hE hLc hΛ hW hWΛ hlogL hε0 hε1 ?_ ?_
  · -- the crude range, split at `1/τ = L_c`
    intro t ht u hu htu hτ
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hmin0 : (0 : ℝ) ≤ min Lc (1 / |t - u|) := le_min (by linarith) (by positivity)
    have hLc0 : (0 : ℝ) ≤ Lc := by linarith
    rcases le_or_gt (1 / |t - u|) κ with h | h
    · have hLe : 1 / |t - u| ≤ Lc := le_trans h hκLc
      have h1 := crude_split_le_min (C := C₁ * Lc ^ 2) (by positivity) hτ0 hΛ0
        (hcrudelog _ hτ0 hτ) hLe (hcr1 t ht u hu htu hτ h)
      have hle : 81 * C₁ ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hstep : 81 * (C₁ * Lc ^ 2) / Λ ^ 4
          ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / Λ ^ 4 := by
        rw [div_le_div_iff₀ hΛ4 hΛ4]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg Lc)) hΛ4.le]
      exact le_trans h1 (mul_le_mul_of_nonneg_right hstep hmin0)
    · have hKm : Lc ≤ K * (1 / |t - u|) := by
        refine le_trans hLcκ ?_
        exact mul_le_mul_of_nonneg_left h.le (by linarith)
      have h2 := crude_top_le_min (C := C₂) (K := K) hC₂ hS0 hσ0 hΛ0 hnb0 hLb0
        hK1 hσLb hΛb hLceq hKm (hcr2 t ht u hu htu hτ h.le)
      have hle : 16 * K * S ^ 3 * C₂
          ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hstep : 16 * K * S ^ 3 * C₂ * Lc ^ 2 / Λ ^ 4
          ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / Λ ^ 4 := by
        rw [div_le_div_iff₀ hΛ4 hΛ4]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg Lc)) hΛ4.le]
      exact le_trans h2 (mul_le_mul_of_nonneg_right hstep hmin0)
  · -- the outer range, split at `τ = ε'`
    intro t ht u hu htu hτ
    have hτ0 : (0 : ℝ) < |t - u| := abs_sub_pos.mpr htu
    have hτ1 : |t - u| ≤ 1 := hTle t ht u hu
    have hden : (0 : ℝ) < |t - u| * Real.log (2 / |t - u|) ^ 2 := by
      have hlp := log_two_div_pos hτ0 hτ1
      positivity
    have h := le_div_of_middle_far (E₁ := E₁) (E₂ := E₂) (Lc := Lc) (W := W) (ε' := ε')
      hE₁ hE₂ hτ0 (fun hle => hmid t ht u hu htu hτ hle) (fun hlt => hfar t ht u hu htu hτ hlt)
    have hle : max E₁ E₂ ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) :=
      le_max_right _ _
    have hpos : (0 : ℝ) < W ^ 2 * (|t - u| * Real.log (2 / |t - u|) ^ 2) := mul_pos hW2 hden
    have hstep : max E₁ E₂ * Lc ^ 2 / W ^ 2 / (|t - u| * Real.log (2 / |t - u|) ^ 2)
        ≤ max (max (81 * C₁) (16 * K * S ^ 3 * C₂)) (max E₁ E₂) * Lc ^ 2 / W ^ 2
            / (|t - u| * Real.log (2 / |t - u|) ^ 2) := by
      rw [div_div, div_div, div_le_div_iff₀ hpos hpos]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg Lc)) hpos.le]
    exact le_trans h hstep

end RMF
