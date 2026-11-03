/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RestrictedSecondMoment.Drift

/-!
# Key Proposition 5: the three ranges of `τ = |t - u|`

Harper, *Moments of random multiplicative functions, I* (arXiv:1703.06654), proof of Key
Proposition 5.  The second of the files `Drift.lean`, `Ranges.lean`, `Assembly.lean`:
Proposition 7 on Harper's `R(t)`, the `t`-integration, the `Λ` arithmetic, Harper's remark that
the tilt's range of primes does not matter, the rotation removing the common centre, the free
two-point moment, and the bounds on the crude (`τ ≤ (\log x)^{-1/3}`), middle and far ranges.
The main result is `RMF.integral_sq_setIntegral_indicator_normSq_le_of_cases`.
-/

set_option linter.style.longFile 3800

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RMF

variable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}

/-! ### Harper's `R(t)`, fed to Proposition 7

Harper's outer range needs `P~₂(L(0) ∩ L(t))`, and Proposition 7 is stated above the shift.
`RMF.barrierEvent_subset_harper_shift` differences the barrier at `r` and at `m + r`, giving a
tube on the suffix at level `a' = 2a + r + Br + |h(r)|`, which is `2a + O(\log(2/|t|))` for
`r = O(\log(2/|t|))`.  Two adjustments reach Proposition 7's shape.

The offset function is re-based.  The shifted upper envelope is `a' + m + h(m+r)`, and
Proposition 7 wants `|h'(m)| ≤ 10\log m`, which `h(m+r)` violates at `m = 1`.  Widening the tube
(a larger event) repairs it: `\log(m+r) ≤ \log m + \log(1+r)` for `m ≥ 1`, so `10\log(1+r)` moves
into the level and `h'(m) = 10\log m`.  Both coordinates at once: `RMF.barrierEventPair` is an
intersection of two one-coordinate events, and `Set.inter_subset_inter` applies the inclusion
twice. -/

/-- **Harper's barrier level on the suffix**, `2a + (1+B)r + |h(r)| + 10\log(1+r)` with
`B = RMF.blockSlope 125`: it is `RMF.shiftedHeight a B h r` (`RMF.shiftLevel_eq_shiftedHeight`),
and `2a + O(\log(2/τ))` when `r ≤ 2\log(2/τ) + 1` (`RMF.shiftLevel_le_of_le`). -/
noncomputable def shiftLevel (a : ℝ) (r : ℕ) (hf : ℕ → ℝ) : ℝ :=
  2 * a + r + blockSlope 125 * r + |hf r| + 10 * Real.log (1 + r)

lemma le_shiftLevel {a : ℝ} (ha : 0 ≤ a) (r : ℕ) (hf : ℕ → ℝ) : a ≤ shiftLevel a r hf := by
  rw [shiftLevel]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hB := (blockSlope_pos 125).le
  have hlog : (0 : ℝ) ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  nlinarith [abs_nonneg (hf r), hB, hr0, ha]

/-- **The barrier at both heights sits inside Proposition 7's tube on the suffix.** -/
theorem barrierEventPair_subset_shiftLevel {Ω'' : Type*} {Z : ℕ → Ω'' → ℝ × ℝ} {n r : ℕ}
    {a : ℝ} {hf : ℕ → ℝ} (hr : 1 ≤ r) (hrn : r ≤ n)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → |hf j| ≤ 10 * Real.log j) :
    barrierEventPair Z n (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
        (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
      ⊆ barrierEventPair (fun m => Z (m + r)) (n - r)
          (fun m => -shiftLevel a r hf - blockSlope 125 * m)
          (fun m => shiftLevel a r hf + m + 10 * Real.log m)
          (fun m => -shiftLevel a r hf - blockSlope 125 * m)
          (fun m => shiftLevel a r hf + m + 10 * Real.log m) := by
  have hlog1r : (0 : ℝ) ≤ Real.log (1 + r) := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    exact Real.log_nonneg (by linarith)
  -- the widened tube contains the differenced one
  have hmono : ∀ (Y : ℕ → Ω'' → ℝ),
      barrierEvent (fun m => Y (m + r)) (n - r)
          (fun m => -(2 * a + r + blockSlope 125 * r + |hf r|) - blockSlope 125 * m)
          (fun m => (2 * a + r + blockSlope 125 * r + |hf r|) + m + hf (m + r))
        ⊆ barrierEvent (fun m => Y (m + r)) (n - r)
          (fun m => -shiftLevel a r hf - blockSlope 125 * m)
          (fun m => shiftLevel a r hf + m + 10 * Real.log m) := by
    intro Y
    refine barrierEvent_mono (fun j hj1 hjn => ?_) (fun j hj1 hjn => ?_)
    · rw [shiftLevel]
      linarith
    · -- `\log(j+r) ≤ \log j + \log(1+r)` for `j ≥ 1`
      have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      have hjr : j + r ≤ n := by omega
      have habs := hhf (j + r) (by omega) hjr
      have hcast : ((j + r : ℕ) : ℝ) = (j : ℝ) + (r : ℝ) := by push_cast; ring
      have hprod : (j : ℝ) + (r : ℝ) ≤ (j : ℝ) * (1 + (r : ℝ)) := by nlinarith
      have hlogle : Real.log (((j + r : ℕ) : ℝ)) ≤ Real.log j + Real.log (1 + r) := by
        rw [hcast]
        calc Real.log ((j : ℝ) + (r : ℝ))
            ≤ Real.log ((j : ℝ) * (1 + (r : ℝ))) :=
              Real.log_le_log (by linarith) hprod
          _ = Real.log j + Real.log (1 + r) :=
              Real.log_mul (by linarith) (by linarith)
      rw [shiftLevel]
      linarith [(abs_le.1 habs).2, hlogle]
  exact Set.inter_subset_inter
    (le_trans (barrierEvent_subset_harper_shift hr hrn) (hmono (fun m ω => (Z m ω).1)))
    (le_trans (barrierEvent_subset_harper_shift hr hrn) (hmono (fun m ω => (Z m ω).2)))

/-- **Fewer blocks, larger event.**  The drop is taken by shortening the barrier, and shortening
it only removes constraints. -/
lemma barrierEventPair_subset_of_le {Ω'' : Type*} {Z : ℕ → Ω'' → ℝ × ℝ} {n n' : ℕ}
    (h : n' ≤ n) {u₁ v₁ u₂ v₂ : ℕ → ℝ} :
    barrierEventPair Z n u₁ v₁ u₂ v₂ ⊆ barrierEventPair Z n' u₁ v₁ u₂ v₂ :=
  Set.inter_subset_inter (fun _ hω j hj1 hjn => hω j hj1 (hjn.trans h))
    (fun _ hω j hj1 hjn => hω j hj1 (hjn.trans h))

/-- **`RMF.exists_measure_barrierEventPair_harper_le` with its constants left free.**  Reading
Proposition 7 over all `N` blocks at Harper's scales moves neither `Cst` nor the window
`T_{sh}`. -/
theorem le_measure_barrierEventPair_harper_of_prop7.{u} {Cst Tsh : ℝ}
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
      ∀ (θ σ τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
        (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
        s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < N - d - r →
          boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
              + blockWindow m + blockWindow m + 13
            ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
        max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a →
        4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
        4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
        (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
              (blockCutoff θ N) s₁ s₂ μ)
            (barrierEventPair
              (fun m ω => ∑ p ∈ primeBlockSub θ m,
                (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                  localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
              (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
              (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
            ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  intro Ω' _ X μ hX θ σ τ a N r d s₁ s₂ hf hθ hr1 hrN hre₁ hre₂ hσtop hτ0 hτ1 hτeq hTshle
    henvc ha hbig hbig2 hhf
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_trans zero_le_one (le_max_left _ _)) ha
  have hσm : ∀ m, m ≤ N - d → |σ| * Real.log (blockScale θ (m + 1)) ≤ 1 :=
    hsigma_of_top hσtop
  have hm3 : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + θ := by
    push_cast
    linarith
  haveI hP : IsProbabilityMeasure (tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
      (blockCutoff θ N) s₁ s₂ μ) :=
    hX.isProbabilityMeasure_tiltedMeasure₂ (blockCutoff θ N)
      (re_pos_of_block hm3 hre₁ (hσm 0 (by omega)))
      (re_pos_of_block hm3 hre₂ (hσm 0 (by omega)))
  have hsub := barrierEventPair_subset_shiftLevel (a := a)
    (Z := fun m ω => (∑ p ∈ primeBlockSub θ m,
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))))
    hr1 (by omega : r ≤ N) hhf
  have hsub' := le_trans hsub (barrierEventPair_subset_of_le (by omega : N - d - r ≤ N - r))
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub')) ?_
  exact hprop7 Ω' X μ hX θ σ τ (shiftLevel a r hf) N r (N - d - r) s₁ s₂
    (fun m => 10 * Real.log m) hθ (by omega) hre₁ hre₂
    (by rw [show r + (N - d - r) = N - d from by omega]; exact hσtop)
    hτ0 hτ1 hτeq hTshle henvc
    (le_trans ha (le_shiftLevel ha0 r hf)) (by omega) hbig hbig2
    (fun j hj1 _ => by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 10 * Real.log j)])

/-- **Harper's outer-range barrier bound**: the two-point barrier probability over all `N` blocks
is at most `Cst·\min\{1, a'/√(N-d-r)\}²` with `a' = RMF.shiftLevel a r hf`, by Proposition 7 on
the suffix above the shift.  For `r ≤ 2\log(2/τ) + 1` the level is `2a + O(\log(2/τ))`, and the
`Λ` arithmetic turns this into `≪ \log²(2/|t|)/(1+(1-q)√Λ)²`. -/
theorem exists_measure_barrierEventPair_harper_le :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d - r →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hprop7⟩ := exists_proposition7_upper_steinhaus
  exact ⟨Cst, Tsh, hCst, hTsh,
    le_measure_barrierEventPair_harper_of_prop7 hprop7⟩

/-! ### The `t`-integral, and why it converges

After both bounds the outer range contributes `∫_{ε<|t|≤1} dt/(|t|\log²(2/|t|))`, finite because
of the `\log²(2/|t|)`, which Harper traces to the `-2\log\log` term in the definition of his event.
Here that term is the choice `hf = RMF.harperHf` within `|hf j| ≤ 10\log j`.  The bound below is
uniform in `ε`, so the inner cutoff `(\log x)^{-1/3}` may be sent to `0`.  The antiderivative is
`1/\log(2/t)`. -/

/-- **The `t`-integral of Key Proposition 5, uniformly in the inner cutoff**:
`∫_ε^1 dt/(t\log²(2/t)) ≤ 1/\log 2` for every `ε ∈ (0, 1]`. -/
theorem integral_inv_mul_log_two_div_sq_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in ε..1, 1 / (t * Real.log (2 / t) ^ 2)) ≤ 1 / Real.log 2 := by
  have huIcc : Set.uIcc ε 1 = Set.Icc ε 1 := Set.uIcc_of_le hε1
  -- on `[ε,1]` the integrand is continuous and `\log(2/t) ≥ \log 2 > 0`
  have hlogpos : ∀ t ∈ Set.Icc ε 1, 0 < Real.log (2 / t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hε0 ht.1
    have h2t : (1 : ℝ) < 2 / t := by
      rw [lt_div_iff₀ ht0]
      linarith [ht.2]
    exact Real.log_pos h2t
  have hderiv : ∀ t ∈ Set.uIcc ε 1,
      HasDerivAt (fun x : ℝ => (Real.log (2 / x))⁻¹) (1 / (t * Real.log (2 / t) ^ 2)) t := by
    intro t ht
    rw [huIcc] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hε0 ht.1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hL := hlogpos t ht
    -- `x ↦ 2/x`
    have h1 : HasDerivAt (fun x : ℝ => 2 / x) (-(2 / t ^ 2)) t := by
      have h := (hasDerivAt_inv htne).const_mul (2 : ℝ)
      simpa [div_eq_mul_inv, mul_comm, mul_div_assoc] using h
    -- `x ↦ \log (2/x)`
    have h2 : HasDerivAt (fun x : ℝ => Real.log (2 / x)) (-(1 / t)) t := by
      have hne : (2 : ℝ) / t ≠ 0 := by positivity
      have h := (Real.hasDerivAt_log hne).comp t h1
      refine h.congr_deriv ?_
      field_simp
    -- and its inverse
    have h3 := h2.inv (ne_of_gt hL)
    refine h3.congr_deriv ?_
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log (2 / t) ^ 2)) (Set.uIcc ε 1) := by
    rw [huIcc]
    have hne : ∀ t ∈ Set.Icc ε 1, (2 : ℝ) / t ≠ 0 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hε0 ht.1
      positivity
    have hdiv : ContinuousOn (fun t : ℝ => (2 : ℝ) / t) (Set.Icc ε 1) :=
      continuousOn_const.div continuousOn_id
        (fun t ht => ne_of_gt (lt_of_lt_of_le hε0 ht.1))
    have hlog : ContinuousOn (fun t : ℝ => Real.log (2 / t)) (Set.Icc ε 1) :=
      Real.continuousOn_log.comp hdiv (fun t ht => hne t ht)
    refine ContinuousOn.div continuousOn_const (continuousOn_id.mul (hlog.pow 2)) ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hε0 ht.1
    have hL := hlogpos t ht
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h1 : Real.log (2 / 1) = Real.log 2 := by norm_num
  have hLpos : 0 < Real.log (2 / ε) := hlogpos ε ⟨le_rfl, hε1⟩
  rw [h1]
  have hinvpos : (0 : ℝ) < (Real.log (2 / ε))⁻¹ := inv_pos.2 hLpos
  rw [one_div]
  linarith

/-! ### The double integral collapses, with no invariance in law

Harper fixes one height at `0` by the Steinhaus rotation `f(p) ↦ f(p)p^{-iτ}`, which in Lean would
need the rotation to be measure-preserving and the barrier family to be covariant under it.

It is not needed.  Every range bound depends on `(t,u)` only through `t - u`: the cosine sums
carry `s₁.im - s₂.im` (`RMF.abs_blockMatchedCov_prime_sub_le`), the variances see the weights only
through their moduli, and the shift is a function of `|t - u|`.  So the reduction is made on the
bound, by the translation invariance of Lebesgue measure. -/

/-- **One height integrated out.**  For a non-negative integrand depending only on the difference,
the inner integral over `T` is at most the integral over a fixed window twice as long. -/
theorem setIntegral_sub_le_of_subset {G : ℝ → ℝ} (hG0 : ∀ v, 0 ≤ G v)
    {T : Set ℝ} (hTsub : T ⊆ Set.Icc (-1 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hint : IntegrableOn (fun v => G |v|) (Set.Icc (-2 : ℝ) 2)) :
    (∫ u in T, G |t - u|) ≤ ∫ v in Set.Icc (-2 : ℝ) 2, G |v| := by
  have hemb : MeasurableEmbedding (fun v : ℝ => t - v) := measurableEmbedding_subLeft t
  have hmp : MeasurePreserving (fun v : ℝ => t - v) volume volume :=
    volume.measurePreserving_sub_left t
  have h := hmp.setIntegral_preimage_emb hemb (fun u => G |t - u|) T
  simp only [show ∀ v : ℝ, t - (t - v) = v from fun v => by ring] at h
  rw [← h]
  refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun v => hG0 _) ?_
  refine LE.le.eventuallyLE ?_
  intro v hv
  obtain ⟨h1, h2⟩ := hTsub hv
  obtain ⟨h3, h4⟩ := ht
  exact ⟨by linarith, by linarith⟩

/-! ### The expansion's event is the pair barrier

`RMF.integral_sq_setIntegral_indicator_normSq_eq` produces `P~₂(L t ∩ L u)` for a measurable
family `L` of one-coordinate barriers; Proposition 7 bounds `P~₂(barrierEventPair …)`.
They are the same set: `barrierEventPair` is the intersection of the two coordinate barriers, and
a sum of pairs is the pair of sums (`RMF.sum_pair_eq`). -/

@[simp] lemma im_shiftLine (σ t : ℝ) : (shiftLine σ t).im = t := by
  simp [shiftLine]

/-- **The intersection of the two barriers is the pair barrier.** -/
lemma barrierEvent_inter_eq_barrierEventPair {Ω' : Type*} {Y : ℕ → Ω' → ℂ} {θ : ℝ} {N : ℕ}
    {s₁ s₂ : ℂ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} :
    barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω)) N u₁ v₁
        ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)) N u₂ v₂
      = barrierEventPair (fun m ω => ∑ p ∈ primeBlockSub θ m,
          (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
            localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) N u₁ v₁ u₂ v₂ := by
  have hpair : ∀ (m : ℕ) (ω : Ω'), (∑ p ∈ primeBlockSub θ m,
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)))
      = ((∑ p ∈ primeBlockSub θ m, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω)),
          ∑ p ∈ primeBlockSub θ m, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω)) :=
    fun m ω => congrFun (sum_pair_eq (fun p ω =>
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y (p : ℕ) ω))) (primeBlockSub θ m)) ω
  rw [barrierEventPair]
  congr 1
  · congr 1
    funext m ω
    rw [hpair m ω]
  · congr 1
    funext m ω
    rw [hpair m ω]

/-! ### The threshold on `a` is a constant, not a constraint

Proposition 7's upper bound asks for `a ≥ RMF.result1Threshold (1/18) (9/2) ≥ 8000`, while
Harper's `a = \min\{√Λ, 1/(1-q)\}` is `3` at `q = 2/3`.  Raising the level enlarges the event, so
the bound at level `Ta` bounds the probability at level `a`, and
`\min\{1, Ta/√n\} ≤ T\min\{1, a/√n\}` for `T ≥ 1`: the price is the factor `T²`, and only `1 ≤ a`
is needed. -/

/-- **The shift level is affine in `a` with a non-negative constant term**, so scaling `a` by
`T ≥ 1` scales the level by at most `T`. -/
lemma shiftLevel_mul_le {T a : ℝ} (hT : 1 ≤ T) (r : ℕ) (hf : ℕ → ℝ) :
    shiftLevel (T * a) r hf ≤ T * shiftLevel a r hf := by
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hB := (blockSlope_pos 125).le
  have hlog : (0 : ℝ) ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  have hc : (0 : ℝ) ≤ (r : ℝ) + blockSlope 125 * r + |hf r| + 10 * Real.log (1 + r) := by
    linarith [mul_nonneg hB hr0, abs_nonneg (hf r)]
  rw [shiftLevel, shiftLevel]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T - 1) hc]

/-- **Raising the level enlarges the pair event.**  Both coordinates by `RMF.barrierEvent_mono`. -/
lemma barrierEventPair_mono {Ω'' : Type*} {Z : ℕ → Ω'' → ℝ × ℝ} {n : ℕ}
    {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hu₁ : ∀ j, 1 ≤ j → j ≤ n → u₁ j ≤ u₁' j) (hv₁ : ∀ j, 1 ≤ j → j ≤ n → v₁' j ≤ v₁ j)
    (hu₂ : ∀ j, 1 ≤ j → j ≤ n → u₂ j ≤ u₂' j) (hv₂ : ∀ j, 1 ≤ j → j ≤ n → v₂' j ≤ v₂ j) :
    barrierEventPair Z n u₁' v₁' u₂' v₂' ⊆ barrierEventPair Z n u₁ v₁ u₂ v₂ :=
  Set.inter_subset_inter (barrierEvent_mono hu₁ hv₁) (barrierEvent_mono hu₂ hv₂)

/-- **The level floor the pair bound pays for `1 ≤ a`**,
`\max(1, \mathrm{result1Threshold}\,(1/18)\,(9/2))`.  The bracket is `(1/18, 9/2)` here, not the
`(1/16, 9/2)` of the one-point chain: the pair's variance can be smaller.  It costs a factor
`T^2` in the constant and nothing in the window. -/
noncomputable def pairLevelFloor : ℝ := max 1 (result1Threshold (1 / 18) (9 / 2))

/-- **`RMF.exists_measure_barrierEventPair_harper_one_le` with its constants named.**  Raising
the level to `1` costs the factor `RMF.pairLevelFloor ^ 2` in the constant and leaves the window
`T_{sh}` alone. -/
theorem le_measure_barrierEventPair_harper_one_of_pair.{u} {Cst Tsh : ℝ} (hCst : 0 < Cst)
    (hbound :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d - r →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          max 1 (result1Threshold (1 / 18) (9 / 2)) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
      IsSteinhausPrimeValues X μ →
      ∀ (θ σ τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
        (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
        s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
        |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
        0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < N - d - r →
          boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
              + blockWindow m + blockWindow m + 13
            ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
        (1 : ℝ) ≤ a →
        4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
        4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
        (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
              (blockCutoff θ N) s₁ s₂ μ)
            (barrierEventPair
              (fun m ω => ∑ p ∈ primeBlockSub θ m,
                (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                  localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
              (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
              (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
            ≤ Cst * pairLevelFloor ^ 2
                * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  set T : ℝ := pairLevelFloor with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  intro Ω' _ X μ hX θ σ τ a N r d s₁ s₂ hf hθ hr1 hrN hre₁ hre₂ hσtop hτ0 hτ1 hτeq hTshle
    henvc ha hbig hbig2 hhf
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hTa : T ≤ T * a := by nlinarith
  have haTa : a ≤ T * a := le_mul_of_one_le_left ha0 hT1
  have hkey := hbound Ω' X μ hX θ σ τ (T * a) N r d s₁ s₂ hf hθ hr1 hrN hre₁ hre₂ hσtop hτ0
    hτ1 hτeq hTshle henvc hTa hbig hbig2 hhf
  -- the tilt is a probability measure, so the enlarged event has finite measure
  have hσsm : |σ| ≤ 1 / 4 := by
    have hlog : (4 : ℝ) ≤ Real.log (blockScale θ (N - d + 1)) := by
      rw [log_blockScale]
      have h1 : (0 : ℝ) ≤ ((N - d + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [Real.add_one_le_exp (((N - d + 1 : ℕ) : ℝ) + θ)]
    nlinarith [abs_nonneg σ, hσtop]
  have hs₁ : (0 : ℝ) < s₁.re := by rw [hre₁]; linarith [neg_abs_le σ, hσsm]
  have hs₂ : (0 : ℝ) < s₂.re := by rw [hre₂]; linarith [neg_abs_le σ, hσsm]
  have hPM := hX.isProbabilityMeasure_tiltedMeasure₂ (blockCutoff θ N) hs₁ hs₂
  -- the level-`a` event sits inside the level-`Ta` one
  have hsub := barrierEventPair_mono
    (Z := fun m ω => ∑ p ∈ primeBlockSub θ m,
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) (n := N)
    (u₁ := fun j => -(T * a) - blockSlope 125 * j) (v₁ := fun j => T * a + j + hf j)
    (u₂ := fun j => -(T * a) - blockSlope 125 * j) (v₂ := fun j => T * a + j + hf j)
    (u₁' := fun j => -a - blockSlope 125 * j) (v₁' := fun j => a + j + hf j)
    (u₂' := fun j => -a - blockSlope 125 * j) (v₂' := fun j => a + j + hf j)
    (fun j _ _ => by linarith) (fun j _ _ => by linarith)
    (fun j _ _ => by linarith) (fun j _ _ => by linarith)
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
    (le_trans hkey ?_)
  -- and `min\{1, ·\}` of the scaled level costs a factor `T`
  have hsn : (0 : ℝ) ≤ Real.sqrt ((N - d - r : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hS0 : (0 : ℝ) ≤ shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ) :=
    div_nonneg (le_trans ha0 (le_shiftLevel ha0 r hf)) hsn
  have hlev : shiftLevel (T * a) r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)
      ≤ T * (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (shiftLevel_mul_le hT1 r hf) hsn
  have hmin : min 1 (shiftLevel (T * a) r hf / Real.sqrt ((N - d - r : ℕ) : ℝ))
      ≤ T * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) :=
    le_trans (min_le_min le_rfl hlev) (min_one_mul_le hT1)
  have hTa0 : (0 : ℝ) ≤ T * a := mul_nonneg (by linarith) ha0
  have hmin0 : (0 : ℝ) ≤ min 1 (shiftLevel (T * a) r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) :=
    le_min zero_le_one (div_nonneg (le_trans hTa0 (le_shiftLevel hTa0 r hf)) hsn)
  have hsq := pow_le_pow_left₀ hmin0 hmin 2
  rw [mul_pow] at hsq
  calc Cst * min 1 (shiftLevel (T * a) r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2
      ≤ Cst * (T ^ 2 * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hCst.le
    _ = Cst * T ^ 2 * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by ring

/-- **`RMF.exists_measure_barrierEventPair_harper_le` with `1 ≤ a`.**  The same bound, at the same
shape, with Probability Result 1's threshold traded for an absolute factor in the constant (see
the section note above). -/
theorem exists_measure_barrierEventPair_harper_one_le :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d - r →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ := exists_measure_barrierEventPair_harper_le
  have hT1 : (1 : ℝ) ≤ pairLevelFloor := le_max_left _ _
  exact ⟨Cst * pairLevelFloor ^ 2, Tsh, by positivity, hTsh,
    le_measure_barrierEventPair_harper_one_of_pair hCst hbound⟩

/-- **`RMF.exists_measure_barrier_inter_harper_le` with its constants left free.**  Reading the
pair bound on the intersection instead of the pair event moves neither `Cst` nor `T_{sh}`. -/
theorem le_measure_barrier_inter_harper_of_pair.{u} {Cst Tsh : ℝ}
    (hbound :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (X : ℕ → Ω' → ℂ) (μ : Measure Ω'),
        IsSteinhausPrimeValues X μ →
        ∀ (θ σ τ a : ℝ) (N r d : ℕ) (s₁ s₂ : ℂ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          s₁.re = 1 / 2 + σ → s₂.re = 1 / 2 + σ →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < τ → τ ≤ 1 → |s₁.im - s₂.im| = τ → Tsh ≤ τ * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d - r →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => X p ω)
                (blockCutoff θ N) s₁ s₂ μ)
              (barrierEventPair
                (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (X (p : ℕ) ω),
                    localLog (((p : ℕ) : ℂ) ^ (-s₂)) (X (p : ℕ) ω))) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2) :
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
      IsSteinhausPrimeValues Y ν →
      ∀ (θ σ a : ℝ) (N r d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
        (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
        |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
        0 < |t - u| → |t - u| ≤ 1 → Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
        (∀ m, m < N - d - r →
          boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
              + blockWindow m + blockWindow m + 13
            ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
        (1 : ℝ) ≤ a →
        4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
        4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
        (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
          ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
              (shiftLine σ t) (shiftLine σ u) ν)
            (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
              ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                  localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
            ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  intro Ω' _ Y ν hY θ σ a N r d t u hf hθ hr1 hrN hσtop hτ0 hτ1 hTshle henvc ha hbig hbig2 hhf
  rw [barrierEvent_inter_eq_barrierEventPair]
  exact hbound Ω' Y ν hY θ σ |t - u| a N r d (shiftLine σ t) (shiftLine σ u) hf hθ hr1 hrN
    (re_shiftLine σ t) (re_shiftLine σ u) hσtop hτ0 hτ1
    (by simp only [im_shiftLine]) hTshle henvc ha hbig hbig2 hhf

/-- **The expansion's barrier factor, bounded in the outer range**: the first factor of
`RMF.integral_sq_setIntegral_indicator_normSq_eq` at two heights far enough apart is at most
`Cst·\min\{1, a'/√(N-d-r)\}²`, `a' = RMF.shiftLevel a r hf`, for `1 ≤ a`.  The expansion produces
an intersection of two one-coordinate barriers, Proposition 7 a pair barrier, and
`RMF.barrierEvent_inter_eq_barrierEventPair` identifies them. -/
theorem exists_measure_barrier_inter_harper_le :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a : ℝ) (N r d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < |t - u| → |t - u| ≤ 1 → Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d - r →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ := exists_measure_barrierEventPair_harper_one_le
  exact ⟨Cst, Tsh, hCst, hTsh, le_measure_barrier_inter_harper_of_pair hbound⟩

/-- **The outer integration.**  Once the inner integral is bounded uniformly — which is what
`RMF.setIntegral_sub_le_of_subset` delivers — the double integral is at most `|T|` times that
bound.  With `T ⊆ [-1,1]` the factor `|T|` is itself at most `2`, so nothing is lost. -/
theorem setIntegral_le_of_le_const {F : ℝ → ℝ} {C : ℝ} {T : Set ℝ}
    (hT : MeasurableSet T) (hTfin : volume T ≠ ⊤) (hint : IntegrableOn F T)
    (hF : ∀ t ∈ T, F t ≤ C) :
    (∫ t in T, F t) ≤ (volume T).toReal * C := by
  have hconst : IntegrableOn (fun _ : ℝ => C) T :=
    integrableOn_const hTfin
  calc (∫ t in T, F t) ≤ ∫ _t in T, C := setIntegral_mono_on hint hconst hT hF
    _ = (volume T).toReal • C := setIntegral_const C
    _ = (volume T).toReal * C := smul_eq_mul _ _

/-! ### The `Λ` arithmetic: Proposition 7's output in Harper's units

Proposition 7 gives `\min\{1, a'/√n\}²`; Harper's bound for `P~₂(R(t))` is
`\log²(2/|t|)/(1+(1-q)√Λ)²`.  With `m = \min\{√Λ, 1/(1-q)\}`, written as `m ≤ √Λ` and
`m(1-q) ≤ 1` so that `q = 1` needs no division, two facts do the work: `m(1 + (1-q)√Λ) ≤ 2√Λ`
turns the `m/√Λ` part of `a'/√n` into `1/(1+(1-q)√Λ)`, and `1 + (1-q)√Λ ≤ 2√Λ` does the same
for the `\log(2/τ)/√Λ` part.  The range enters only through `Λ ≤ cn`.

`c` is a parameter, not `3`: Harper's outer range gives `n ≥ Λ/3 - O(1)` with the `O(1)` at
least `B ≥ 125`, so `Λ/3 ≤ n` has no instances at his data, while `Λ ≤ 4n` holds past an
absolute threshold. -/

/-- **The `Λ` arithmetic.**  `\min\{1, a/√n\}² ≪ \log²(2/τ)/(1+(1-q)√Λ)²` whenever the level is
`2m + K\log(2/τ)` and the block count satisfies `Λ ≤ cn`. -/
theorem min_one_div_sqrt_sq_le {Λ a τ K q m c : ℝ} {n : ℕ}
    (hΛ : 1 ≤ Λ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hK : 0 ≤ K)
    (hn1 : 1 ≤ n) (hm0 : 0 ≤ m) (hmΛ : m ≤ Real.sqrt Λ) (hmq : m * (1 - q) ≤ 1)
    (ha0 : 0 ≤ a) (ha : a ≤ 2 * m + K * Real.log (2 / τ)) (hc : 0 < c)
    (hn : Λ ≤ c * (n : ℝ)) :
    min 1 (a / Real.sqrt n) ^ 2
      ≤ c * (4 / Real.log 2 + 2 * K) ^ 2 * Real.log (2 / τ) ^ 2
        / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2 / τ) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hτ0]
    linarith
  have hL0 : (0 : ℝ) < Real.log (2 / τ) := lt_of_lt_of_le hlog2 hL
  have hsΛ : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hΛ
  have hsΛ0 : (0 : ℝ) < Real.sqrt Λ := by linarith
  have hq' : (0 : ℝ) ≤ 1 - q := by linarith
  have hW0 : (0 : ℝ) < 1 + (1 - q) * Real.sqrt Λ := by nlinarith [hsΛ0, hq']
  have hW : 1 + (1 - q) * Real.sqrt Λ ≤ 2 * Real.sqrt Λ := by nlinarith [hsΛ, hq0, hq']
  have hmW : m * (1 + (1 - q) * Real.sqrt Λ) ≤ 2 * Real.sqrt Λ := by
    nlinarith [hmΛ, hmq, hsΛ0, hm0]
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsn0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hs3 : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.2 hc
  have hs3sq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hsn : Real.sqrt Λ ≤ Real.sqrt c * Real.sqrt n := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hn
  set A : ℝ := 4 / Real.log 2 + 2 * K with hAdef
  have hA0 : (0 : ℝ) < A := by
    rw [hAdef]
    positivity
  have hkey : a / Real.sqrt n ≤ Real.sqrt c * A * Real.log (2 / τ)
      / (1 + (1 - q) * Real.sqrt Λ) := by
    rw [div_le_div_iff₀ hsn0 hW0]
    have h1 : a * (1 + (1 - q) * Real.sqrt Λ)
        ≤ (2 * m + K * Real.log (2 / τ)) * (1 + (1 - q) * Real.sqrt Λ) :=
      mul_le_mul_of_nonneg_right ha hW0.le
    have hKL : (0 : ℝ) ≤ K * Real.log (2 / τ) := mul_nonneg hK hL0.le
    have h2a : K * Real.log (2 / τ) * (1 + (1 - q) * Real.sqrt Λ)
        ≤ K * Real.log (2 / τ) * (2 * Real.sqrt Λ) := mul_le_mul_of_nonneg_left hW hKL
    have h2 : (2 * m + K * Real.log (2 / τ)) * (1 + (1 - q) * Real.sqrt Λ)
        ≤ 4 * Real.sqrt Λ + K * Real.log (2 / τ) * (2 * Real.sqrt Λ) := by
      nlinarith [hmW, h2a]
    have hfour : (4 : ℝ) ≤ 4 / Real.log 2 * Real.log (2 / τ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [hL, hlog2]
    have h3 : 4 * Real.sqrt Λ + K * Real.log (2 / τ) * (2 * Real.sqrt Λ)
        ≤ A * Real.log (2 / τ) * Real.sqrt Λ := by
      rw [hAdef]
      nlinarith [hfour, hsΛ0, hKL]
    have h4 : A * Real.log (2 / τ) * Real.sqrt Λ
        ≤ A * Real.log (2 / τ) * (Real.sqrt c * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hsn (by positivity)
    calc a * (1 + (1 - q) * Real.sqrt Λ)
        ≤ A * Real.log (2 / τ) * (Real.sqrt c * Real.sqrt n) := by linarith
      _ = Real.sqrt c * A * Real.log (2 / τ) * Real.sqrt n := by ring
  have hmin : min 1 (a / Real.sqrt n) ≤ a / Real.sqrt n := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt n) := le_min zero_le_one (by positivity)
  have hsq : min 1 (a / Real.sqrt n) ^ 2
      ≤ (Real.sqrt c * A * Real.log (2 / τ) / (1 + (1 - q) * Real.sqrt Λ)) ^ 2 :=
    pow_le_pow_left₀ hmin0 (le_trans hmin hkey) 2
  refine hsq.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, mul_pow, hs3sq]

/-- **The shift level is `2a + O(\log(2/τ))`** for `r ≤ 2\log(2/τ) + 1` and `|h(r)| ≤ 10\log r`:
every term of `RMF.shiftLevel` past `2a` is linear in `r` or in `\log(1+r)`, and `\log x ≤ x`
absorbs the logarithms. -/
lemma shiftLevel_le_of_le {a τ : ℝ} {r : ℕ} {hf : ℕ → ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hr : (r : ℝ) ≤ 2 * Real.log (2 / τ) + 1)
    (hhf : |hf r| ≤ 10 * Real.log r) :
    shiftLevel a r hf
      ≤ 2 * a + (42 + 2 * blockSlope 125
          + (31 + blockSlope 125) / Real.log 2) * Real.log (2 / τ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2 / τ) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hτ0]
    linarith
  have hL0 : (0 : ℝ) < Real.log (2 / τ) := lt_of_lt_of_le hlog2 hL
  have hB := (blockSlope_pos 125).le
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlogr : Real.log r ≤ (r : ℝ) := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · have h1 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h
      linarith [Real.log_le_sub_one_of_pos h1]
  have hlog1r : Real.log (1 + r) ≤ 1 + (r : ℝ) := by
    have h1 : (0 : ℝ) < 1 + (r : ℝ) := by linarith
    linarith [Real.log_le_sub_one_of_pos h1]
  have hconst : (31 : ℝ) + blockSlope 125
      ≤ (31 + blockSlope 125) / Real.log 2 * Real.log (2 / τ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith [hL, hlog2, hB]
  rw [shiftLevel]
  nlinarith [hr, hlogr, hlog1r, hconst, hB, hL0, abs_nonneg (hf r), hhf]

/-- **The display's window constant**, `42 + 2B + (31 + B)/\log 2 + 2κ` at `B = blockSlope 125`:
the length of the window the two display bounds integrate over.  Both
`RMF.exists_measure_barrier_inter_display_le` and
`RMF.exists_measure_barrierEventPair_shift_display_le` scale their input constant by
`4(4/\log 2 + 2K)^2`. -/
noncomputable def displayWindowConst (κ : ℝ) : ℝ :=
  42 + 2 * blockSlope 125 + (31 + blockSlope 125) / Real.log 2 + 2 * κ

lemma displayWindowConst_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ displayWindowConst κ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB := (blockSlope_pos 125).le
  rw [displayWindowConst]
  positivity

/-- **`RMF.exists_measure_barrier_inter_display_le` with its constants left free.**
Passing to the display scales the constant by the window factor and leaves the
window `T_{sh}` alone. -/
theorem le_measure_barrier_inter_display_of_harper.{u} {κ Cst Tsh : ℝ}
    (hκ : 0 ≤ κ) (hCst : 0 < Cst)
    (hbound :
            ∀ (Ω' : Type u) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsSteinhausPrimeValues Y ν →
        ∀ (θ σ a : ℝ) (N r d : ℕ) (t u : ℝ) (hf : ℕ → ℝ),
          (125 : ℝ) ≤ θ → 1 ≤ r → r + d + 4 ≤ N →
          |σ| * Real.log (blockScale θ (N - d + 1)) ≤ 1 →
          0 < |t - u| → |t - u| ≤ 1 → Tsh ≤ |t - u| * Real.exp ((r : ℝ) + θ) →
          (∀ m, m < N - d - r →
            boxEnvelope (blockSlope 125) m + boxEnvelope (blockSlope 125) (m + 1)
                + blockWindow m + blockWindow m + 13
              ≤ 1 / 40 * Real.sqrt (Real.log (blockScale (θ + r) (m + 1)))) →
          (1 : ℝ) ≤ a →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 20 ≤ ((N - d - r : ℕ) : ℝ) →
          4 * Real.log ((N - d - r : ℕ) : ℝ) ^ 8 ≤ ((N - d - r : ℕ) : ℝ) * (1 / 18) →
          (∀ j, 1 ≤ j → j ≤ N → |hf j| ≤ 10 * Real.log j) →
            ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (blockCutoff θ N)
                (shiftLine σ t) (shiftLine σ u) ν)
              (barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j)
                ∩ barrierEvent (fun m ω => ∑ p ∈ primeBlockSub θ m,
                    localLog (((p : ℕ) : ℂ) ^ (-(shiftLine σ u))) (Y (p : ℕ) ω)) N
                  (fun j => -a - blockSlope 125 * j) (fun j => a + j + hf j))).toReal
              ≤ Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2) :
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
            ≤ Cst * (4 * (4 / Real.log 2 + 2 * displayWindowConst κ) ^ 2)
                * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  rw [displayWindowConst]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB := (blockSlope_pos 125).le
  set K : ℝ := 42 + 2 * blockSlope 125 + (31 + blockSlope 125) / Real.log 2 + 2 * κ
    with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    positivity
  intro Ω' _ Y ν hY θ σ a Λ q m N r d t u hf hθ hr1 hrN hσtop hτ0 hτ1 hTshle henvc ha
    hbig hbig2 hhf hΛ hq0 hq1 hm0 hmΛ hmq ham hr hn3
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hn1 : 1 ≤ N - d - r := by omega
  have hlev : shiftLevel a r hf ≤ 2 * m + K * Real.log (2 / |t - u|) := by
    have h := shiftLevel_le_of_le (a := a) (hf := hf) hτ0 hτ1 hr (hhf r hr1 (by omega))
    have hKL : K * Real.log (2 / |t - u|)
        = (42 + 2 * blockSlope 125 + (31 + blockSlope 125) / Real.log 2)
            * Real.log (2 / |t - u|) + 2 * (κ * Real.log (2 / |t - u|)) := by
      rw [hKdef]
      ring
    linarith [h, ham, hKL]
  have harith := min_one_div_sqrt_sq_le (Λ := Λ) (a := shiftLevel a r hf)
    (τ := |t - u|) (K := K) (q := q) (m := m) (n := N - d - r)
    hΛ hq0 hq1 hτ0 hτ1 hK0 hn1 hm0 hmΛ hmq
    (le_trans ha0 (le_shiftLevel ha0 r hf)) hlev (by norm_num) hn3
  refine le_trans (hbound Ω' Y ν hY θ σ a N r d t u hf hθ hr1 hrN hσtop hτ0 hτ1 hTshle
    henvc ha hbig hbig2 hhf) ?_
  calc Cst * min 1 (shiftLevel a r hf / Real.sqrt ((N - d - r : ℕ) : ℝ)) ^ 2
      ≤ Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2 * Real.log (2 / |t - u|) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2) := mul_le_mul_of_nonneg_left harith hCst.le
    _ = Cst * (4 * (4 / Real.log 2 + 2 * K) ^ 2) * Real.log (2 / |t - u|) ^ 2
          / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by ring

/-- **Harper's display for the outer range**: the two-point barrier probability in the outer range
is at most `Cst·\log²(2/|t-u|)/(1+(1-q)√Λ)²`.  `m` stands for `\min\{√Λ, 1/(1-q)\}` through
`m ≤ √Λ` and `m(1-q) ≤ 1`; the outer range enters as `Λ ≤ 4(N-d-r)`, not `Λ/3 ≤ N-d-r`, which
has no instances at Harper's data (`RMF.min_one_div_sqrt_sq_le`). -/
theorem exists_measure_barrier_inter_display_le (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ Cst Tsh : ℝ, 0 < Cst ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
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
              ≤ Cst * Real.log (2 / |t - u|) ^ 2 / (1 + (1 - q) * Real.sqrt Λ) ^ 2 := by
  obtain ⟨Cst, Tsh, hCst, hTsh, hbound⟩ := exists_measure_barrier_inter_harper_le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : (0 : ℝ) ≤ displayWindowConst κ := displayWindowConst_nonneg hκ
  exact ⟨Cst * (4 * (4 / Real.log 2 + 2 * displayWindowConst κ) ^ 2), Tsh, by positivity, hTsh,
    le_measure_barrier_inter_display_of_harper hκ hCst hbound⟩

/-! ### Harper's last display: the outer range collapses to one integrable factor

Harper bounds the outer range by a product of four factors: `(5.2)²` on the pulled-out product
(`RMF.normSq_randomEulerProductIco_le_of_mem_barrierEvent`), `P~₂(R(t))`
(`RMF.exists_measure_barrier_inter_display_le`), `1/|t|` from pulling `E∏|I_l|²` out by the
disjointness of the prime ranges, and `(|t|\log x/V)²` from (5.1) on the quotient
(`RMF.exists_integral_normSq_high_le`).  In the outer range (5.2) takes its second arm, so the
product is `(1/(|t|\log²(2/|t|)))²·\log²(2/|t|)/W²·(1/|t|)·(|t|\log x/V)²`, which is
`(\log x/V)²/W²·1/(|t|\log²(2/|t|))`.  Its integral over the outer range is at most `2/\log 2`,
uniformly in the inner cutoff: `E(∫_ℒ|F|²)² ≪ e^{2m}(\log x/(VW))²`, Key Proposition 5. -/

/-- **The survivor, over both signs.**  `∫_{ε<|t|≤1} dt/(|t|\log²(2/|t|)) ≤ 2/\log 2`, uniformly
in `ε` — which is what lets the inner cutoff `(\log x)^{-1/3}` be sent to `0`. -/
theorem integral_abs_inv_mul_log_sq_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε), 1 / (|t| * Real.log (2 / |t|) ^ 2))
      ≤ 2 / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmeas₁ : MeasurableSet (Set.Ioc ε 1) := measurableSet_Ioc
  have hmeas₂ : MeasurableSet (Set.Ico (-1 : ℝ) (-ε)) := measurableSet_Ico
  -- the even integrand is continuous wherever `ε ≤ |t| ≤ 1`
  have hcontOn : ∀ a b : ℝ, (∀ t ∈ Set.Icc a b, ε ≤ |t| ∧ |t| ≤ 1) →
      ContinuousOn (fun t : ℝ => 1 / (|t| * Real.log (2 / |t|) ^ 2)) (Set.Icc a b) := by
    intro a b hab
    have habs : ContinuousOn (fun t : ℝ => |t|) (Set.Icc a b) := continuous_abs.continuousOn
    have hpos : ∀ t ∈ Set.Icc a b, (0 : ℝ) < |t| :=
      fun t ht => lt_of_lt_of_le hε0 (hab t ht).1
    have hdiv : ContinuousOn (fun t : ℝ => (2 : ℝ) / |t|) (Set.Icc a b) :=
      continuousOn_const.div habs (fun t ht => ne_of_gt (hpos t ht))
    have hne : ∀ t ∈ Set.Icc a b, (2 : ℝ) / |t| ≠ 0 := by
      intro t ht
      have := hpos t ht
      positivity
    have hlog : ContinuousOn (fun t : ℝ => Real.log (2 / |t|)) (Set.Icc a b) :=
      Real.continuousOn_log.comp hdiv (fun t ht => hne t ht)
    refine ContinuousOn.div continuousOn_const (habs.mul (hlog.pow 2)) ?_
    intro t ht
    have h1 := hpos t ht
    have h2 : (1 : ℝ) < 2 / |t| := by
      rw [lt_div_iff₀ h1]
      linarith [(hab t ht).2]
    have hL := Real.log_pos h2
    positivity
  have hint₁ : IntegrableOn (fun t : ℝ => 1 / (|t| * Real.log (2 / |t|) ^ 2))
      (Set.Ioc ε 1) := by
    refine IntegrableOn.mono_set ((hcontOn ε 1 ?_).integrableOn_Icc) Set.Ioc_subset_Icc_self
    intro t ht
    rw [abs_of_pos (lt_of_lt_of_le hε0 ht.1)]
    exact ⟨ht.1, ht.2⟩
  have hint₂ : IntegrableOn (fun t : ℝ => 1 / (|t| * Real.log (2 / |t|) ^ 2))
      (Set.Ico (-1 : ℝ) (-ε)) := by
    refine IntegrableOn.mono_set ((hcontOn (-1) (-ε) ?_).integrableOn_Icc) Set.Ico_subset_Icc_self
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- the positive half is the one-sided bound
  have hpos : (∫ t in Set.Ioc ε 1, 1 / (|t| * Real.log (2 / |t|) ^ 2)) ≤ 1 / Real.log 2 := by
    have hcongr : (∫ t in Set.Ioc ε 1, 1 / (|t| * Real.log (2 / |t|) ^ 2))
        = ∫ t in Set.Ioc ε 1, 1 / (t * Real.log (2 / t) ^ 2) := by
      refine setIntegral_congr_fun hmeas₁ fun t ht => ?_
      rw [abs_of_pos (hε0.trans ht.1)]
    rw [hcongr, ← intervalIntegral.integral_of_le hε1]
    exact integral_inv_mul_log_two_div_sq_le hε0 hε1
  -- the negative half is the positive one reflected
  have hpre : (fun t : ℝ => -t) ⁻¹' Set.Ico (-1 : ℝ) (-ε) = Set.Ioc ε 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hneg : (∫ t in Set.Ico (-1 : ℝ) (-ε), 1 / (|t| * Real.log (2 / |t|) ^ 2))
      ≤ 1 / Real.log 2 := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
      measurableEmbedding_neg (fun t => 1 / (|t| * Real.log (2 / |t|) ^ 2))
      (Set.Ico (-1 : ℝ) (-ε))
    simp only [abs_neg, hpre] at h
    rw [← h]
    exact hpos
  have hdisj : Disjoint (Set.Ioc ε 1) (Set.Ico (-1 : ℝ) (-ε)) := by
    rw [Set.disjoint_left]
    rintro t ⟨ht1, _⟩ ⟨_, ht4⟩
    linarith
  rw [setIntegral_union hdisj hmeas₂ hint₁ hint₂]
  exact le_trans (add_le_add hpos hneg) (le_of_eq (by ring))

/-! ### Harper's licence, derived

Harper remarks that the range of primes in the tilted measure matters little: the
expectation over primes an event does not involve factors out and cancels between numerator and
denominator.  He uses this in the outer range, where the estimate is applied to the quotient
`F/∏_{l≥\text{split}}|I_l|`.  Written out it is `E[1_A LH]/E[LH] = E[1_A L]/E[L]` whenever
`1_A·L ⊥ H`: tilting by something independent of `A` does not move `A`.

The hypothesis holds because the prime ranges are disjoint: the pulled-out product runs over blocks
below `RMF.splitIndex`, `R(t)` over blocks from the shift `r` upward, and `\text{splitIndex} < r`,
Harper's `\log\log x - D - 1 < ⌊\log(|t|\log x)⌋`.  At `τ = 1`, `⌈2\log(1/τ)⌉ = 0` and the ranges
touch, one reason `1 ≤ r` is assumed wherever the shift appears. -/

/-- **Tilting by something independent of `A` does not move `A`.**  Harper's licence, with no
primes in it. -/
theorem measure_tilted_preimage_eq_of_indep {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {ν : Measure Ω} [IsProbabilityMeasure ν] {u : Ω → β} {v : Ω → γ}
    (huv : IndepFun u v ν) (hu : Measurable u) (hv : Measurable v) {B : Set β}
    (hB : MeasurableSet B) {h : γ → ℝ} (hh : Measurable h)
    (hint : Integrable (fun ω => Real.exp (h (v ω))) ν) :
    ν.tilted (fun ω => h (v ω)) (u ⁻¹' B) = ν (u ⁻¹' B) := by
  have hS : MeasurableSet (u ⁻¹' B) := hu hB
  have hZ : (0 : ℝ) < ∫ ω, Real.exp (h (v ω)) ∂ν := integral_exp_pos hint
  have hEm : Measurable (fun ω => Real.exp (h (v ω))) := Real.measurable_exp.comp (hh.comp hv)
  -- the indicator of the preimage is the indicator of `B`, composed
  have hind : (u ⁻¹' B).indicator (fun _ => (1 : ℝ))
      = (fun b => B.indicator (fun _ => (1 : ℝ)) b) ∘ u := by
    funext ω
    by_cases hb : u ω ∈ B
    · rw [Set.indicator_of_mem (by exact hb : ω ∈ u ⁻¹' B)]
      simp [Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem (by exact hb : ω ∉ u ⁻¹' B)]
      simp [Set.indicator_of_notMem hb]
  have hindep : IndepFun ((u ⁻¹' B).indicator (fun _ => (1 : ℝ)))
      (fun ω => Real.exp (h (v ω))) ν := by
    rw [hind, show (fun ω => Real.exp (h (v ω))) = (fun c => Real.exp (h c)) ∘ v from rfl]
    exact huv.comp (measurable_const.indicator hB) (Real.measurable_exp.comp hh)
  have hprod : ∫ ω, ((u ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω) * Real.exp (h (v ω)) ∂ν
      = (∫ ω, (u ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂ν) * ∫ ω, Real.exp (h (v ω)) ∂ν :=
    hindep.integral_mul_eq_mul_integral
      (measurable_const.indicator hS).aestronglyMeasurable hEm.aestronglyMeasurable
  have hsplit : ∀ ω, (u ⁻¹' B).indicator (fun ω => Real.exp (h (v ω))) ω
      = (u ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * Real.exp (h (v ω)) := by
    intro ω
    by_cases hb : ω ∈ u ⁻¹' B
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, one_mul]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, zero_mul]
  have hsetint : (∫ ω in u ⁻¹' B, Real.exp (h (v ω)) ∂ν)
      = ν.real (u ⁻¹' B) * ∫ ω, Real.exp (h (v ω)) ∂ν := by
    rw [← integral_indicator hS]
    simp only [hsplit]
    rw [hprod, integral_indicator_const _ hS, smul_eq_mul, mul_one]
  rw [tilted_apply_eq_ofReal_integral' _ hS, integral_div, hsetint,
    mul_div_assoc, div_self hZ.ne', mul_one]
  exact ENNReal.ofReal_toReal (measure_ne_top ν _)

/-- The same with the tilt exponent given directly.  Leaving `h` to be inferred makes the
application a higher-order unification problem, which does not terminate in any heartbeat
budget — so the consumer uses this form. -/
theorem measure_tilted_preimage_eq_of_indep' {β : Type*} [MeasurableSpace β]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {u : Ω → β} {g : Ω → ℝ}
    (hug : IndepFun u g ν) (hu : Measurable u) (hg : Measurable g)
    {B : Set β} (hB : MeasurableSet B) (hint : Integrable (fun ω => Real.exp (g ω)) ν) :
    ν.tilted g (u ⁻¹' B) = ν (u ⁻¹' B) :=
  measure_tilted_preimage_eq_of_indep (v := g) (h := id) hug hu hg hB measurable_id hint

/-- **A finite block of local weights is bounded, hence integrable**, under any finite measure
absolutely continuous with respect to `μ`.  `RMF.integrable_exp_localTilt₂` is the one-prime case;
the point of the finite product is that the bound multiplies out. -/
lemma integrable_exp_sum_localTilt₂ {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (S : Finset Nat.Primes) {s₁ s₂ : ℂ}
    (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (ν : Measure Ω) [IsFiniteMeasure ν] (hν : ν ≪ μ) :
    Integrable (fun ω => Real.exp (∑ p ∈ S, localTilt₂ s₁ s₂ p (X (p : ℕ) ω))) ν := by
  classical
  haveI := hX.isProbabilityMeasure
  -- every value lies on the circle, `ν`-almost everywhere
  have hae : ∀ p : Nat.Primes, ∀ᵐ ω ∂ν, ‖X (p : ℕ) ω‖ = 1 := by
    intro p
    refine hν.ae_le ?_
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_steinhausLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  have haeS : ∀ᵐ ω ∂ν, ∀ p ∈ S, ‖X (p : ℕ) ω‖ = 1 :=
    (ae_ball_iff S.countable_toSet).2 fun p _ => hae p
  set C : ℝ := ∏ p ∈ S, ((1 - ‖((p : ℕ) : ℂ) ^ (-s₁)‖)⁻¹ ^ 2
    * (1 - ‖((p : ℕ) : ℂ) ^ (-s₂)‖)⁻¹ ^ 2) with hCdef
  refine (memLp_top_of_bound ?_ C ?_).integrable le_top
  · refine Measurable.aestronglyMeasurable (Real.measurable_exp.comp ?_)
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_localTilt₂ s₁ s₂ p).comp (hX.measurable (p : ℕ) p.2)
  · filter_upwards [haeS] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_sum, hCdef]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_nonneg _)) fun p hp => ?_
    have hw₁ : ‖((p : ℕ) : ℂ) ^ (-s₁)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₁
    have hw₂ : ‖((p : ℕ) : ℂ) ^ (-s₂)‖ < 1 := norm_prime_cpow_neg_lt_one p.2 hs₂
    rw [localTilt₂_apply, Real.exp_add]
    exact mul_le_mul (exp_two_localLog_le (hω p hp) hw₁) (exp_two_localLog_le (hω p hp) hw₂)
      (Real.exp_nonneg _) (by positivity)

/-! ### The licence at a subset, and the grouping it needs

The outer range needs the licence not between two *cutoffs* but between a set of primes and a
**subset** of it: the quotient's tilt weight is the product over `[x_{\text{split}}, x)`, a middle
range, not an initial segment.  The proof does not change — `Finset.sum_sdiff` does not care
whether the subset is an initial segment — so this is the same statement with
`primesBelowSub y ⊆ primesBelowSub y'` replaced by `S₁ ⊆ S`. -/

/-- **Two prime sets differ by a tilt over the difference**, for an arbitrary subset. -/
theorem tilted_sum_localTilt₂_eq_tilted_sdiff {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {S S₁ : Finset Nat.Primes} (hS : S₁ ⊆ S)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    μ.tilted (fun ω => ∑ p ∈ S, localTilt₂ s₁ s₂ p (X (p : ℕ) ω))
      = (μ.tilted (fun ω => ∑ p ∈ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω))).tilted
          (fun ω => ∑ p ∈ S \ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω)) := by
  classical
  haveI := hX.isProbabilityMeasure
  rw [tilted_tilted (integrable_exp_sum_localTilt₂ hX S₁ hs₁ hs₂ μ
    (Measure.AbsolutelyContinuous.refl μ))]
  congr 1
  funext ω
  simp only [Pi.add_apply]
  rw [← Finset.sum_sdiff hS]
  exact add_comm _ _

/-- **The licence at a subset.**  The tilt may be taken over `S₁` instead of `S` for an event that
does not involve the primes in between. -/
theorem measure_tilted_sum_localTilt₂_congr {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) {S S₁ : Finset Nat.Primes} (hS : S₁ ⊆ S)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {β : Type*} [MeasurableSpace β]
    {u : Ω → β} (hu : Measurable u) {B : Set β} (hB : MeasurableSet B)
    (hindep : IndepFun u (fun ω => ∑ p ∈ S \ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω))
      (μ.tilted (fun ω => ∑ p ∈ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω)))) :
    μ.tilted (fun ω => ∑ p ∈ S, localTilt₂ s₁ s₂ p (X (p : ℕ) ω)) (u ⁻¹' B)
      = μ.tilted (fun ω => ∑ p ∈ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω)) (u ⁻¹' B) := by
  classical
  haveI := hX.isProbabilityMeasure
  haveI : IsProbabilityMeasure
      (μ.tilted (fun ω => ∑ p ∈ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω))) :=
    isProbabilityMeasure_tilted (integrable_exp_sum_localTilt₂ hX S₁ hs₁ hs₂ μ
      (Measure.AbsolutelyContinuous.refl μ))
  have hvm : Measurable (fun ω => ∑ p ∈ S \ S₁, localTilt₂ s₁ s₂ p (X (p : ℕ) ω)) :=
    Finset.measurable_sum _ fun p _ =>
      (measurable_localTilt₂ s₁ s₂ p).comp (hX.measurable (p : ℕ) p.2)
  rw [tilted_sum_localTilt₂_eq_tilted_sdiff hX hS hs₁ hs₂]
  exact measure_tilted_preimage_eq_of_indep' hindep hu hvm hB
    (integrable_exp_sum_localTilt₂ hX (S \ S₁) hs₁ hs₂ _
      (tilted_absolutelyContinuous μ _))

/-- **Functions of disjoint groups of an independent family are independent.**  The step every
pull-out in the outer range rests on, in the form the applications want: a measurable function of
the blocks in `S` against a measurable function of the blocks in `T`. -/
theorem indepFun_of_disjoint_groups {ι E : Type*} [MeasurableSpace E] {ν : Measure Ω}
    {Z : ι → Ω → E} (hZ : iIndepFun Z ν) (hZm : ∀ m, Measurable (Z m))
    {S T : Finset ι} (hST : Disjoint S T) {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {φ : (S → E) → β} {ψ : (T → E) → γ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (fun ω => φ fun m : S => Z (m : ι) ω)
      (fun ω => ψ fun m : T => Z (m : ι) ω) ν :=
  (hZ.indepFun_finset S T hST hZm).comp hφ hψ

/-! ### The barrier as a preimage

`RMF.indepFun_of_disjoint_groups` takes its two functions as maps out of the *restriction* of the
family to a finite index set.  To hand it the barrier, the barrier has to be exhibited as a
preimage — which it is, and of a set that does not mention `Ω` at all: a two-point barrier is a
condition on the *sequence of increments*, nothing more.

Separating that out is what makes the independence step routine: the sequence-level set is
measurable once and for all, and the only thing that changes between applications is which
increments the map reads. -/

/-- **The two-point barrier, as a set of increment sequences**: the `w` with
`∑_{m<j}(w m).1 ∈ [u₁ j, v₁ j]` and `∑_{m<j}(w m).2 ∈ [u₂ j, v₂ j]` for every `1 ≤ j ≤ n`. -/
def barrierSet (n : ℕ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) : Set (ℕ → ℝ × ℝ) :=
  {w | ∀ j, 1 ≤ j → j ≤ n →
    (∑ m ∈ Finset.range j, (w m).1) ∈ Set.Icc (u₁ j) (v₁ j) ∧
      (∑ m ∈ Finset.range j, (w m).2) ∈ Set.Icc (u₂ j) (v₂ j)}

lemma measurableSet_barrierSet (n : ℕ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    MeasurableSet (barrierSet n u₁ v₁ u₂ v₂) := by
  have hrw : barrierSet n u₁ v₁ u₂ v₂ = ⋂ j ∈ Set.Icc 1 n,
      ((fun w : ℕ → ℝ × ℝ => ∑ m ∈ Finset.range j, (w m).1) ⁻¹' Set.Icc (u₁ j) (v₁ j)
        ∩ (fun w : ℕ → ℝ × ℝ => ∑ m ∈ Finset.range j, (w m).2) ⁻¹' Set.Icc (u₂ j) (v₂ j)) := by
    ext w
    simp only [barrierSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun h j hj => ⟨h j hj.1 hj.2 |>.1, h j hj.1 hj.2 |>.2⟩,
      fun h j hj1 hjn => ⟨(h j ⟨hj1, hjn⟩).1, (h j ⟨hj1, hjn⟩).2⟩⟩
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_
  have h₁ : Measurable fun w : ℕ → ℝ × ℝ => ∑ m ∈ Finset.range j, (w m).1 :=
    Finset.measurable_sum _ fun m _ => (measurable_pi_apply m).fst
  have h₂ : Measurable fun w : ℕ → ℝ × ℝ => ∑ m ∈ Finset.range j, (w m).2 :=
    Finset.measurable_sum _ fun m _ => (measurable_pi_apply m).snd
  exact (h₁ measurableSet_Icc).inter (h₂ measurableSet_Icc)

/-- **Membership depends only on the first `n` increments.** -/
lemma mem_barrierSet_congr {n : ℕ} {u₁ v₁ u₂ v₂ : ℕ → ℝ} {w w' : ℕ → ℝ × ℝ}
    (h : ∀ m, m < n → w m = w' m) :
    w ∈ barrierSet n u₁ v₁ u₂ v₂ ↔ w' ∈ barrierSet n u₁ v₁ u₂ v₂ := by
  have hsum : ∀ j, j ≤ n → (∑ m ∈ Finset.range j, (w m).1) = ∑ m ∈ Finset.range j, (w' m).1
      ∧ (∑ m ∈ Finset.range j, (w m).2) = ∑ m ∈ Finset.range j, (w' m).2 := by
    intro j hj
    constructor <;>
      exact Finset.sum_congr rfl fun m hm => by
        rw [h m (lt_of_lt_of_le (Finset.mem_range.1 hm) hj)]
  constructor
  · intro hw j hj1 hjn
    obtain ⟨e₁, e₂⟩ := hsum j hjn
    rw [← e₁, ← e₂]
    exact hw j hj1 hjn
  · intro hw j hj1 hjn
    obtain ⟨e₁, e₂⟩ := hsum j hjn
    rw [e₁, e₂]
    exact hw j hj1 hjn

/-- **The two-point barrier is a preimage of `RMF.barrierSet`.**  True for any family, with no
measurability needed: it is a restatement of the definition. -/
lemma barrierEventPair_eq_preimage {Ω' : Type*} (Y : ℕ → Ω' → ℝ × ℝ) (n : ℕ)
    (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    barrierEventPair Y n u₁ v₁ u₂ v₂
      = (fun ω => fun m => Y m ω) ⁻¹' barrierSet n u₁ v₁ u₂ v₂ := by
  ext ω
  simp only [barrierEventPair, barrierEvent, barrierSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_preimage, walk_apply]
  exact ⟨fun h j hj1 hjn => ⟨h.1 j hj1 hjn, h.2 j hj1 hjn⟩,
    fun h => ⟨fun j hj1 hjn => (h j hj1 hjn).1, fun j hj1 hjn => (h j hj1 hjn).2⟩⟩

/-- The sequence rebuilt from the increments the shifted barrier reads: `m ↦ w(m + r)` for
`m < n`, and `0` otherwise.  Only the first `n` entries matter, by `RMF.mem_barrierSet_congr`. -/
noncomputable def shiftExtend (r n : ℕ) (w : ↑(Finset.Ico r (r + n)) → ℝ × ℝ) : ℕ → ℝ × ℝ :=
  fun m => if h : m + r ∈ Finset.Ico r (r + n) then w ⟨m + r, h⟩ else 0

lemma measurable_shiftExtend (r n : ℕ) : Measurable (shiftExtend r n) := by
  refine measurable_pi_lambda _ fun m => ?_
  by_cases h : m + r ∈ Finset.Ico r (r + n)
  · simp only [shiftExtend, dif_pos h]
    exact measurable_pi_apply _
  · simp only [shiftExtend, dif_neg h]
    exact measurable_const

/-- **The shifted two-point barrier factors through the restriction to its own blocks.**  This is
what `RMF.indepFun_of_disjoint_groups` consumes: the event is a preimage under a map that reads
only the increments in `[r, r+n)`. -/
lemma barrierEventPair_shift_eq_preimage {Ω' : Type*} (Z : ℕ → Ω' → ℝ × ℝ) (n r : ℕ)
    (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    barrierEventPair (fun m => Z (m + r)) n u₁ v₁ u₂ v₂
      = (fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => Z (p : ℕ) ω)
          ⁻¹' barrierSet n u₁ v₁ u₂ v₂ := by
  rw [barrierEventPair_eq_preimage]
  ext ω
  simp only [Set.mem_preimage]
  refine mem_barrierSet_congr fun m hm => ?_
  have h : m + r ∈ Finset.Ico r (r + n) := by
    rw [Finset.mem_Ico]
    omega
  simp only [shiftExtend, dif_pos h]

/-- **The shifted barrier is independent of the low blocks**, the hypothesis of every pull-out and
of the licence; it needs only `k < r`, the split index below the shift.  The low functional is
`∑_{m ≤ k}(2(Z m).1 + 2(Z m).2)` because `RMF.localTilt₂` is twice the sum of the two local logs.
-/
theorem indepFun_barrierShift_lowBlocks {ν : Measure Ω} {Z : ℕ → Ω → ℝ × ℝ}
    (hZ : iIndepFun Z ν) (hZm : ∀ m, Measurable (Z m)) {n r k : ℕ} (hkr : k < r) :
    IndepFun (fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => Z (p : ℕ) ω)
      (fun ω => ∑ m ∈ Finset.range (k + 1), (2 * (Z m ω).1 + 2 * (Z m ω).2)) ν := by
  classical
  have hdisj : Disjoint (Finset.Ico r (r + n)) (Finset.range (k + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_range] at hb
    omega
  have hψ : Measurable fun w : ↑(Finset.range (k + 1)) → ℝ × ℝ =>
      ∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2) :=
    Finset.measurable_sum _ fun m _ =>
      (((measurable_pi_apply m).fst).const_mul 2).add (((measurable_pi_apply m).snd).const_mul 2)
  have h := indepFun_of_disjoint_groups hZ hZm hdisj (measurable_shiftExtend r n) hψ
  have hfun : (fun ω => ∑ m ∈ (Finset.univ : Finset ↑(Finset.range (k + 1))),
        (2 * (Z (m : ℕ) ω).1 + 2 * (Z (m : ℕ) ω).2))
      = fun ω => ∑ m ∈ Finset.range (k + 1), (2 * (Z m ω).1 + 2 * (Z m ω).2) := by
    funext ω
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach _ fun m => 2 * (Z m ω).1 + 2 * (Z m ω).2
  rw [← hfun]
  exact h

/-! ### Removing the common centre

The (5.1) estimates are parametrised by `(σ, \text{difference})`, with the first height at the
real point (`RMF.localTwoPointMoment p σ t` and everything above it), while the expansion identity
produces a general pair `(σ+it, σ+iu)`.  The local moment depends only on `w₁\overline{w₂}`
(`RMF.integral_inv_one_sub_mul_conj_steinhausLaw`), so the bounds depend on `t - u`, but their
statements pin a height.

One rotation reconciles them: `RMF.IsSteinhausPrimeValues.integral_comp_rotate` transports any
measurable functional of the family, and rotating by the unimodular `RMF.shiftConst n p = p^{-in}`
moves every height by `+in`, so `(σ+it, σ+iu)` becomes `(σ, σ+i(u-t))`.  The functional must be
in closed form in the values at the primes: `RMF.primeExtend`, `RMF.eulerClosed`, and its block
analogue `RMF.eulerClosedIco`. -/

/-- The block Euler product in closed form, `∏_{p∈[y₀,y₁)}(1 - x_p p^{-s})⁻¹`, as a function of
the values `x` at the primes (read through `RMF.primeExtend`). -/
noncomputable def eulerClosedIco (x : Nat.Primes → ℂ) (y₀ y₁ : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ primesIco y₀ y₁, (1 - primeExtend x p * (p : ℂ) ^ (-s))⁻¹

lemma measurable_eulerClosedIco (y₀ y₁ : ℕ) (s : ℂ) :
    Measurable fun x : Nat.Primes → ℂ => eulerClosedIco x y₀ y₁ s := by
  unfold eulerClosedIco
  exact Finset.measurable_prod _ fun p _ =>
    (measurable_const.sub ((measurable_primeExtend p).mul measurable_const)).inv

omit [MeasurableSpace Ω] in
/-- At any `ω` where the block's values are bounded by one, the functional is the random Euler
product. -/
lemma eulerClosedIco_eq {X : ℕ → Ω → ℂ} {y₀ y₁ : ℕ} {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco y₀ y₁, ‖X p ω‖ ≤ 1) :
    eulerClosedIco (fun p : Nat.Primes => X (p : ℕ) ω) y₀ y₁ s
      = randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ y₁ s ω := by
  rw [randomEulerProductIco_compMult_eq hs hω, eulerClosedIco]
  exact Finset.prod_congr rfl fun p hp => by
    rw [primeExtend_apply _ (prime_of_mem_primesIco hp)]

/-- **The shift, on the block product.**  Evaluating at `s + in` is rotating by `p^{-in}`. -/
lemma eulerClosedIco_shift (x : Nat.Primes → ℂ) (y₀ y₁ : ℕ) (s : ℂ) (n : ℝ) :
    eulerClosedIco x y₀ y₁ (s + (n : ℂ) * Complex.I)
      = eulerClosedIco (fun p => shiftConst n (p : ℕ) * x p) y₀ y₁ s := by
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' := prime_of_mem_primesIco hp
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp'.pos.ne'
  congr 1
  congr 1
  rw [primeExtend_apply _ hp', primeExtend_apply _ hp', shiftConst,
    show -(s + (n : ℂ) * Complex.I) = -s + -(n : ℂ) * Complex.I by ring,
    Complex.cpow_add _ _ hp0]
  ring

/-- At height zero the shifted line is the real point.  (Not `RMF.shiftLine_zero`, which zeroes
the *first* argument.) -/
lemma shiftLine_zero_height (σ : ℝ) : shiftLine σ 0 = ((1 / 2 + σ : ℝ) : ℂ) := by
  simp [shiftLine]

lemma shiftLine_add_mul_I (σ v n : ℝ) :
    shiftLine σ v + (n : ℂ) * Complex.I = shiftLine σ (v + n) := by
  rw [shiftLine, shiftLine]
  push_cast
  ring

/-- **The common centre comes out.**  The three-fold block moment at a general pair of heights
equals the one at `(σ, σ + i(u-t))`, the shape of the (5.1) estimates: one application of
`RMF.IsSteinhausPrimeValues.integral_comp_rotate` at `RMF.shiftConst t`. -/
theorem integral_normSq_ico_triple_shift {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y₀ N₁ N₂ : ℕ) {σ : ℝ} (hσ : 0 < 1 / 2 + σ) (t u : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ N₁
            (shiftLine σ t) ω‖ ^ 2
        * (‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
              (shiftLine σ t) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
              (shiftLine σ u) ω‖ ^ 2) ∂μ)
      = ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) y₀ N₁
            (shiftLine σ 0) ω‖ ^ 2
        * (‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
              (shiftLine σ 0) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
              (shiftLine σ (u - t)) ω‖ ^ 2) ∂μ := by
  classical
  have hre : ∀ v : ℝ, 0 < (shiftLine σ v).re := fun v => by rw [re_shiftLine]; exact hσ
  set Φ : (Nat.Primes → ℂ) → ℝ := fun x =>
    ‖eulerClosedIco x y₀ N₁ (shiftLine σ 0)‖ ^ 2
      * (‖eulerClosedIco x N₁ N₂ (shiftLine σ 0)‖ ^ 2
        * ‖eulerClosedIco x N₁ N₂ (shiftLine σ (u - t))‖ ^ 2) with hΦdef
  have hΦm : Measurable Φ := by
    rw [hΦdef]
    exact (((measurable_eulerClosedIco y₀ N₁ (shiftLine σ 0)).norm.pow_const 2).mul
      ((((measurable_eulerClosedIco N₁ N₂ (shiftLine σ 0)).norm.pow_const 2)).mul
        ((measurable_eulerClosedIco N₁ N₂ (shiftLine σ (u - t))).norm.pow_const 2)))
  have hrot := hX.integral_comp_rotate (c := shiftConst t)
    (fun p hp => norm_shiftConst t hp) hΦm
  -- the rotated functional is the integrand at the original pair of heights
  have hleft : ∀ ω : Ω, Φ (fun p => shiftConst t (p : ℕ) * X (p : ℕ) ω)
      = ‖eulerClosedIco (fun p : Nat.Primes => X (p : ℕ) ω) y₀ N₁ (shiftLine σ t)‖ ^ 2
        * (‖eulerClosedIco (fun p : Nat.Primes => X (p : ℕ) ω) N₁ N₂ (shiftLine σ t)‖ ^ 2
          * ‖eulerClosedIco (fun p : Nat.Primes => X (p : ℕ) ω) N₁ N₂ (shiftLine σ u)‖ ^ 2) := by
    intro ω
    rw [hΦdef]
    simp only
    rw [← eulerClosedIco_shift, ← eulerClosedIco_shift, ← eulerClosedIco_shift,
      shiftLine_add_mul_I, shiftLine_add_mul_I, zero_add,
      show u - t + t = u from by ring]
  simp only [hleft] at hrot
  -- and both sides may be read as random Euler products
  have hae₁ := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw y₀ N₁
  have hae₂ := ae_forall_norm_le_one_primesIco hX norm_le_one_steinhausLaw N₁ N₂
  refine Eq.trans (integral_congr_ae ?_) (Eq.trans hrot (integral_congr_ae ?_))
  · filter_upwards [hae₁, hae₂] with ω h₁ h₂
    rw [eulerClosedIco_eq (hre t) h₁, eulerClosedIco_eq (hre t) h₂,
      eulerClosedIco_eq (hre u) h₂]
  · filter_upwards [hae₁, hae₂] with ω h₁ h₂
    rw [hΦdef]
    simp only
    rw [eulerClosedIco_eq (hre 0) h₁, eulerClosedIco_eq (hre 0) h₂,
      eulerClosedIco_eq (hre (u - t)) h₂]

/-! ### The free two-point moment, and the far range

The outer range splits again, at `τ ≍ e^{-(θ+1)}`.  By `τ = |t-u|` the ranges are the crude range
`τ ≤ (\log x)^{-1/3}` (indicators discarded), the middle range (the quotient route) and the far
range `e^{-(θ+1)} < τ ≤ 1`.  In the far range `RMF.splitIndex` is `0`, the low product is empty
and the quotient route is vacuous, as in Harper, whose `ℓ` starts at `1`.  It is also unneeded:
there `1/τ ≤ e^{θ+1} = \log(\text{blockScale }θ\,1)`, so the free two-point moment costs only a
factor bounded in terms of `θ` more than the target, and the barrier probability is multiplied
in.  Against the target `L²/(W²τ\log²(2/τ))` the deficit is `τ\log⁴(2/τ) ≤ \log⁴(2e^{θ+1})`.
Below `e^{1/|t|}` the cosine does not oscillate, so the low two-point moment has the fourth power
`(\log N₂/\log N₁)⁴`. -/

/-- **Splitting the free two-point moment at an intermediate cutoff.**  Both ranges carry both
heights, so this is immediate from the product formula: `RMF.primesIco_union` and
`Finset.prod_union` are the whole proof. -/
theorem IsSteinhausRMF.integral_normSq_mul_normSq_Ico_split {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsSteinhausRMF f μ) {y₀ c y : ℕ}
    (h₀ : y₀ ≤ c) (h₁ : c ≤ y) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    (∫ ω, ‖randomEulerProductIco f y₀ y s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f y₀ y s₂ ω‖ ^ 2 ∂μ)
      = (∫ ω, ‖randomEulerProductIco f y₀ c s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f y₀ c s₂ ω‖ ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco f c y s₁ ω‖ ^ 2
            * ‖randomEulerProductIco f c y s₂ ω‖ ^ 2 ∂μ := by
  rw [hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ y hs₁ hs₂,
    hf.integral_norm_randomEulerProductIco_sq_mul_sq y₀ c hs₁ hs₂,
    hf.integral_norm_randomEulerProductIco_sq_mul_sq c y hs₁ hs₂,
    ← primesIco_union h₀ h₁, Finset.prod_union (disjoint_primesIco y₀ c y)]

/-- **The (5.1) exponent with no oscillation used**:
`∑_{N₁<p≤N₂}(2 + 2\cos(t\log p))p^{-1-2σ} ≤ 4(\log\log N₂ - \log\log N₁) + D` for every height
and range, from `2 + 2\cos ≤ 4`, `p^{-1-2σ} ≤ p^{-1}` (`σ ≥ 0`) and Mertens.  It governs below
`e^{1/|t|}`; past that scale `RMF.exists_sum_two_add_two_cos_rpow_le` has `2` in place of `4`. -/
theorem exists_sum_two_add_two_cos_rpow_low_le :
    ∃ D > 0, ∀ (t σ : ℝ), 0 ≤ σ → ∀ N₁ N₂ : ℕ, 2 ≤ N₁ → N₁ ≤ N₂ →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨C, hC, hmert⟩ := exists_abs_sum_primesIco_inv_sub_le
  refine ⟨4 * C, by positivity, fun t σ hσ N₁ N₂ hN₁ hN12 => ?_⟩
  have hterm : ∀ p ∈ primesIco (N₁ + 1) (N₂ + 1),
      (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ) ≤ 4 * ((p : ℝ))⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (prime_of_mem_primesIco hp).one_lt.le
    have hrpow : (p : ℝ) ^ (-1 - 2 * σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hcos : (2 : ℝ) + 2 * Real.cos (t * Real.log p) ≤ 4 := by
      linarith [Real.cos_le_one (t * Real.log p)]
    calc (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)
        ≤ 4 * (p : ℝ) ^ (-1 : ℝ) :=
          mul_le_mul hcos hrpow (by positivity) (by norm_num)
      _ = 4 * ((p : ℝ))⁻¹ := by rw [Real.rpow_neg_one]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have h := hmert N₁ N₂ hN₁ hN12
  rw [abs_le] at h
  linarith [hsum, h.2]

/-- **The free two-point moment over a range, with no oscillation used**:
`E‖I_{(N₁,N₂]}(1/2+σ)‖²‖I_{(N₁,N₂]}(1/2+σ+it)‖² ≤ K(\log N₂/\log N₁)⁴` for every `t` and
`σ ≥ 0`.  The sibling of `RMF.exists_integral_normSq_high_le` below `e^{1/|t|}`, via
`RMF.exists_sum_two_add_two_cos_rpow_low_le`; it needs neither `1/|t| ≤ \log N₁` nor the tilt
hypothesis, and in the far range neither is available. -/
theorem exists_integral_normSq_pairIco_le :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ t : ℝ) (N₁ N₂ : ℕ), 0 ≤ σ → 400 ≤ (N₁ : ℝ) → N₁ ≤ N₂ →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  obtain ⟨C, hC, h51⟩ := exists_abs_log_integral_two_point_le (Ω := Ω)
  obtain ⟨D, hD, hsum⟩ := exists_sum_two_add_two_cos_rpow_low_le
  refine ⟨Real.exp (D + C), Real.exp_pos _, fun f μ hf σ t N₁ N₂ hσ hN₁ hN12 => ?_⟩
  have hexp4 : ∀ r : ℝ, 0 < r → Real.exp (4 * Real.log r) = r ^ 4 := by
    intro r hr
    rw [show (4 : ℝ) * Real.log r = Real.log r + Real.log r + Real.log r + Real.log r by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr]
    ring
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hN₂R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  have hlogN₂ : (1 : ℝ) ≤ Real.log (N₂ : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hN₂R)
  have hre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hs₁ : (0 : ℝ) < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hs₂ : (0 : ℝ) < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by linarith
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by positivity
    linarith
  have h := h51 f μ hf σ t ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) (by exact_mod_cast hN₁) hN₂R hσ'
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ) := by nlinarith
    calc C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C / 1 :=
          div_le_div_of_nonneg_left hC.le (by norm_num) hden
      _ = C := by ring
  have hps := hsum t σ hσ N₁ N₂ (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ))) hN12
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
        ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ 4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C) := by
    linarith [h.2, hps, herr]
  have hEpos := hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂
  have hratio : (0 : ℝ) < Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ) := by
    apply div_pos <;> linarith
  have hconv : Real.exp (4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ)))
      + (D + C)) = Real.exp (D + C) * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
    rw [← Real.log_div (by linarith) (by linarith), Real.exp_add, hexp4 _ hratio]
    ring
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (4 * (Real.log (Real.log (N₂ : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + C) * (Real.log (N₂ : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := hconv

/-- **The (5.1) exponent with the tilt but no oscillation**: the split of
`RMF.exists_sum_two_add_two_cos_rpow_split_le` at the truncation scale `M`, with the in-phase
bound below it, so the factor is `4` and no hypothesis on `t` is needed.  The crude range's second
regime uses it: there `τ < 1/\log x`, `e^{1/|t|}` lies above the product, and only the tilt,
truncating at `M = e^{1/(2σ)}`, limits the range. -/
theorem exists_sum_two_add_two_cos_rpow_split4_le :
    ∃ D > 0, ∀ (t σ : ℝ), 0 ≤ σ → ∀ N₁ M N₂ : ℕ,
      2 ≤ N₁ → N₁ ≤ M → M ≤ N₂ → 1 ≤ 2 * σ * Real.log M →
      (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        ≤ 4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + D := by
  obtain ⟨D₀, hD₀, hlow⟩ := exists_sum_two_add_two_cos_rpow_low_le
  obtain ⟨C, hC, htail⟩ := exists_sum_prime_Ioc_rpow_tail_le
  refine ⟨D₀ + 4 * C, by positivity, fun t σ hσ N₁ M N₂ hN₁ hNM hMN₂ hM => ?_⟩
  have hsplit : (∑ p ∈ primesIco (N₁ + 1) (N₂ + 1),
        (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
      = (∑ p ∈ primesIco (N₁ + 1) (M + 1),
          (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ))
        + ∑ p ∈ primesIco (M + 1) (N₂ + 1),
            (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ) := by
    rw [← primesIco_union (by omega : N₁ + 1 ≤ M + 1) (by omega : M + 1 ≤ N₂ + 1),
      Finset.sum_union (disjoint_primesIco _ _ _)]
  rw [hsplit]
  have hbelow := hlow t σ hσ N₁ M hN₁ hNM
  have habove : (∑ p ∈ primesIco (M + 1) (N₂ + 1),
      (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)) ≤ 4 * C := by
    have hterm : ∀ p ∈ primesIco (M + 1) (N₂ + 1),
        (2 + 2 * Real.cos (t * Real.log p)) * (p : ℝ) ^ (-1 - 2 * σ)
          ≤ 4 * (p : ℝ) ^ (-1 - 2 * σ) := by
      intro p _
      have hc := Real.cos_le_one (t * Real.log p)
      have hnn : (0 : ℝ) ≤ (p : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (by positivity) _
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hconv : (∑ p ∈ primesIco (M + 1) (N₂ + 1), (p : ℝ) ^ (-1 - 2 * σ))
        = ∑ p ∈ Finset.Ioc ⌊(M : ℝ)⌋₊ ⌊(N₂ : ℝ)⌋₊ with Nat.Prime p, (p : ℝ) ^ (-1 - 2 * σ) := by
      rw [Nat.floor_natCast, Nat.floor_natCast, filter_prime_Ioc_eq_primesIco]
    have hMR : (2 : ℝ) ≤ (M : ℝ) := by
      have : (2 : ℕ) ≤ M := le_trans hN₁ hNM
      exact_mod_cast this
    have hMN₂R : ((M : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hMN₂
    have hbound := htail (2 * σ) (M : ℝ) (N₂ : ℝ) (by linarith) hMR hMN₂R hM
    rw [hconv] at hsum
    linarith
  linarith

/-- **The free two-point moment, truncated by the tilt**:
`E‖I_{(N₁,N₂]}(1/2+σ)‖²‖I_{(N₁,N₂]}(1/2+σ+it)‖² ≤ K(\log M/\log N₁)⁴` when `1 ≤ 2σ\log M`.  In
the crude range's second regime the range `(x_b, x]` has `\log x/\log x_b = e^{⌊\log V⌋+4}`, so
the untruncated bound loses `V⁴`; at Harper's data `\log M/\log x_b ∈ [e³/8, e⁴/8]`, the `V`
cancelling between the tilt and the drop, as in Harper. -/
theorem exists_integral_normSq_pairIco_split_le :
    ∃ K > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsSteinhausRMF f μ →
      ∀ (σ t : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
  obtain ⟨C, hC, h51⟩ := exists_abs_log_integral_two_point_le (Ω := Ω)
  obtain ⟨D, hD, hsum⟩ := exists_sum_two_add_two_cos_rpow_split4_le
  refine ⟨Real.exp (D + C), Real.exp_pos _, fun f μ hf σ t N₁ M N₂ hσ hN₁ hNM hMN₂ hM => ?_⟩
  have hexp4 : ∀ r : ℝ, 0 < r → Real.exp (4 * Real.log r) = r ^ 4 := by
    intro r hr
    rw [show (4 : ℝ) * Real.log r = Real.log r + Real.log r + Real.log r + Real.log r by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr]
    ring
  have hN12 : N₁ ≤ N₂ := le_trans hNM hMN₂
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (N₁ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN₁pos]
    linarith [Real.exp_one_lt_d9]
  have hMR : ((N₁ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hNM
  have hN₂R : ((N₁ : ℕ) : ℝ) ≤ ((N₂ : ℕ) : ℝ) := by exact_mod_cast hN12
  have hlogM : (1 : ℝ) ≤ Real.log (M : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hMR)
  have hlogN₂ : (1 : ℝ) ≤ Real.log (N₂ : ℝ) := le_trans hlogN (Real.log_le_log hN₁pos hN₂R)
  have hre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hs₁ : (0 : ℝ) < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hs₂ : (0 : ℝ) < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  have hσ' : -(1 / Real.log ((N₂ : ℕ) : ℝ)) ≤ σ := by
    have hpos : (0 : ℝ) < Real.log ((N₂ : ℕ) : ℝ) := by linarith
    have : (0 : ℝ) ≤ 1 / Real.log ((N₂ : ℕ) : ℝ) := by positivity
    linarith
  have h := h51 f μ hf σ t ((N₁ : ℕ) : ℝ) ((N₂ : ℕ) : ℝ) (by exact_mod_cast hN₁) hN₂R hσ'
  rw [Nat.floor_natCast, Nat.floor_natCast] at h
  have herr : C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 : ℝ) ≤ Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ) := by nlinarith
    calc C / (Real.sqrt ((N₁ : ℕ) : ℝ) * Real.log ((N₁ : ℕ) : ℝ)) ≤ C / 1 :=
          div_le_div_of_nonneg_left hC.le (by norm_num) hden
      _ = C := by ring
  have hps := hsum t σ hσ N₁ M N₂ (by exact_mod_cast (by linarith : (2 : ℝ) ≤ (N₁ : ℝ)))
    hNM hMN₂ hM
  rw [filter_prime_Ioc_eq_primesIco] at h
  rw [abs_le] at h
  have hlogE : Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
        ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
      * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
          (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ 4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C) := by
    linarith [h.2, hps, herr]
  have hEpos := hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂
  have hratio : (0 : ℝ) < Real.log (M : ℝ) / Real.log (N₁ : ℝ) := by
    apply div_pos <;> linarith
  have hconv : Real.exp (4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ)))
      + (D + C)) = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := by
    rw [← Real.log_div (by linarith) (by linarith), Real.exp_add, hexp4 _ hratio]
    ring
  calc (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
        * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      = Real.exp (Real.log (∫ ω, ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
            ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
          * ‖randomEulerProductIco f (N₁ + 1) (N₂ + 1)
              (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)) :=
        (Real.exp_log hEpos).symm
    _ ≤ Real.exp (4 * (Real.log (Real.log (M : ℝ)) - Real.log (Real.log (N₁ : ℝ))) + (D + C)) :=
        Real.exp_le_exp.2 hlogE
    _ = Real.exp (D + C) * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 4 := hconv

/-- **The far range's arithmetic.**  Against the target `1/(τ\log²(2/τ))` the free moment leaves
a deficit `τ\log⁴(2/τ)`, and on `[ε,1]` that is at most `\log⁴(2/ε)` — which for
`ε = e^{-(θ+1)}` is `(θ+1+\log 2)⁴`, absolute, as `θ` is. -/
lemma mul_log_two_div_pow_four_le {ε τ : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ) (hτ1 : τ ≤ 1) :
    τ * Real.log (2 / τ) ^ 4 ≤ Real.log (2 / ε) ^ 4 := by
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hε hετ
  have hge : (1 : ℝ) ≤ 2 / τ := by
    rw [le_div_iff₀ hτ0]
    linarith
  have h2 : (0 : ℝ) ≤ Real.log (2 / τ) := Real.log_nonneg hge
  have hdiv : 2 / τ ≤ 2 / ε := by
    rw [div_le_div_iff₀ hτ0 hε]
    nlinarith
  have hmono : Real.log (2 / τ) ≤ Real.log (2 / ε) :=
    Real.log_le_log (by linarith) hdiv
  have hpow : Real.log (2 / τ) ^ 4 ≤ Real.log (2 / ε) ^ 4 := pow_le_pow_left₀ h2 hmono 4
  nlinarith [pow_nonneg h2 4]

/-- **The free two-point moment of the full product**, over all primes below the cutoff:
`E‖F_y(s_t)‖²‖F_y(s_u)‖² ≤ K(\log N₁)⁴(\log M/\log N₁)²`, the second factor of the expansion
identity.  At `\log N₁ = 1/|t|` this is `L²/|t|²`, which does not integrate, but in the far range
`1/|t| ≤ e^{θ+1}`.  The range splits at `400`, as (5.1) needs: `[2,400]` by the deterministic
`RMF.eulerBound` at `401`, then `RMF.exists_integral_normSq_pairIco_le` and
`RMF.exists_integral_normSq_high_le`. -/
theorem exists_integral_normSq_pair_full_le :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (σ t : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t| → |t| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (N₂ + 1)
                ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (N₂ + 1)
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          ≤ K * Real.log (N₁ : ℝ) ^ 4 * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨K₁, hK₁, hlow⟩ := exists_integral_normSq_pairIco_le (Ω := Ω)
  obtain ⟨K₂, hK₂, hhigh⟩ := exists_integral_normSq_high_le (Ω := Ω)
  have hlog400 : (0 : ℝ) < Real.log 400 := Real.log_pos (by norm_num)
  refine ⟨(1 + eulerBound 401 ^ 4) * K₁ * K₂ / Real.log 400 ^ 4, by positivity,
    fun X μ hX σ t N₁ M N₂ hσ ht ht1 hN₁ hNM hMN₂ hlg hM => ?_⟩
  haveI := hX.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  have hre : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hs₁ : (0 : ℝ) < (((1 / 2 + σ : ℝ) : ℂ)).re := by simpa using hre
  have hs₂ : (0 : ℝ) < ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using hre
  have hh₁ : (1 : ℝ) / 2 ≤ (((1 / 2 + σ : ℝ) : ℂ)).re := by
    simpa using (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + σ)
  have hh₂ : (1 : ℝ) / 2 ≤ ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    simpa using (by linarith : (1:ℝ)/2 ≤ 1/2 + σ)
  have hN₁N : 400 ≤ N₁ := by exact_mod_cast hN₁
  -- the three ranges
  simp only [← randomEulerProductIco_zero]
  rw [hf.integral_normSq_mul_normSq_Ico_split (Nat.zero_le 401) (by omega : 401 ≤ N₂ + 1)
      hs₁ hs₂,
    hf.integral_normSq_mul_normSq_Ico_split (by omega : (400 : ℕ) + 1 ≤ N₁ + 1)
      (by omega : N₁ + 1 ≤ N₂ + 1) hs₁ hs₂]
  -- `[2,400]`: deterministic, uniform in the height
  have hbot : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 401
          ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 401
            (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ 1 + eulerBound 401 ^ 4 := by
    have hae : ∀ᵐ ω ∂μ,
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 401
              ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 401
                (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2
          ≤ 1 + eulerBound 401 ^ 4 := by
      filter_upwards [ae_forall_norm_le_one hX norm_le_one_steinhausLaw 401] with ω hω
      rw [randomEulerProductIco_zero, randomEulerProductIco_zero]
      have h1 := norm_randomEulerProduct_le hω hh₁
      have h2 := norm_randomEulerProduct_le hω hh₂
      have hE : (0 : ℝ) ≤ eulerBound 401 := eulerBound_nonneg 401
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2,
        pow_nonneg (norm_nonneg (randomEulerProduct
          (fun ω => compMultExtension fun p => X p ω) 401 ((1 / 2 + σ : ℝ) : ℂ) ω)) 2,
        pow_nonneg hE 2, sq_nonneg (eulerBound 401 ^ 2)]
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
      (integrable_const _) hae) ?_
    simp
  have hmid := hlow (fun ω => compMultExtension fun p => X p ω) μ hf σ t 400 N₁ hσ
    (by norm_num) hN₁N
  have htop := hhigh (fun ω => compMultExtension fun p => X p ω) μ hf σ t N₁ M N₂ hσ ht ht1
    hN₁ hNM hMN₂ hlg hM
  have hmid0 := (hf.integral_normSq_mul_normSq_Ico_pos (400 + 1) (N₁ + 1) hs₁ hs₂).le
  have htop0 := (hf.integral_normSq_mul_normSq_Ico_pos (N₁ + 1) (N₂ + 1) hs₁ hs₂).le
  have hbot0 := (hf.integral_normSq_mul_normSq_Ico_pos 0 401 hs₁ hs₂).le
  calc (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 401
            ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) 0 401
              (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
        * ((∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (400 + 1)
              (N₁ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (400 + 1)
                (N₁ + 1) (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
          * ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) ((1 / 2 + σ : ℝ) : ℂ) ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (N₁ + 1)
                  (N₂ + 1) (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2 ∂μ)
      ≤ (1 + eulerBound 401 ^ 4)
          * ((K₁ * (Real.log (N₁ : ℝ) / Real.log ((400 : ℕ) : ℝ)) ^ 4)
            * (K₂ * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2)) :=
        mul_le_mul hbot (mul_le_mul hmid htop htop0 (by positivity))
          (by positivity) (by positivity)
    _ = (1 + eulerBound 401 ^ 4) * K₁ * K₂ / Real.log 400 ^ 4 * Real.log (N₁ : ℝ) ^ 4
          * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
        rw [show (((400 : ℕ) : ℝ)) = (400 : ℝ) by norm_num, div_pow]
        field_simp

/-- **The far range collapses** to the same integrable factor as the middle range: with the free
moment `≪ ℓ²L²`, `1/τ ≤ ℓ ≤ Θ`, and the barrier `≪ \log²(2/τ)/W²`, the product is
`(Θ²·τ\log⁴(2/τ))·L²/W²·1/(τ\log²(2/τ))`, the bracket at most `Θ²\log⁴(2Θ)`.  In the far range
`RMF.splitIndex` is `0`, so there is no quotient, pull-out or licence, and
`RMF.integral_abs_inv_mul_log_sq_le` integrates this range and the middle one together. -/
lemma harper_far_collapse {P E Cst K Θ ℓ L W τ : ℝ}
    (hCst : 0 ≤ Cst) (hK : 0 ≤ K) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hℓ : 1 / τ ≤ ℓ) (hℓΘ : ℓ ≤ Θ) (hE0 : 0 ≤ E)
    (hP : P ≤ Cst * Real.log (2 / τ) ^ 2 / W ^ 2)
    (hE : E ≤ K * ℓ ^ 4 * (L / ℓ) ^ 2) :
    P * E ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4 * (L ^ 2 / W ^ 2)
        * (1 / (τ * Real.log (2 / τ) ^ 2)) := by
  have hℓ1 : (1 : ℝ) ≤ ℓ := le_trans (by rw [le_div_iff₀ hτ0]; linarith) hℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hΘ0 : (0 : ℝ) < Θ := by linarith
  have hlog0 : (0 : ℝ) < Real.log (2 / τ) := Real.log_pos (by rw [lt_div_iff₀ hτ0]; linarith)
  have hεle : 1 / Θ ≤ τ := by
    have h1 : 1 / τ ≤ Θ := le_trans hℓ hℓΘ
    rw [div_le_iff₀ hτ0] at h1
    rw [div_le_iff₀ hΘ0]
    linarith
  have harith : τ * Real.log (2 / τ) ^ 4 ≤ Real.log (2 * Θ) ^ 4 := by
    have h := mul_log_two_div_pow_four_le (ε := 1 / Θ) (by positivity) hεle hτ1
    rwa [show (2 : ℝ) / (1 / Θ) = 2 * Θ by field_simp] at h
  have hEΘ : E ≤ K * Θ ^ 2 * L ^ 2 := by
    have hrw : K * ℓ ^ 4 * (L / ℓ) ^ 2 = K * ℓ ^ 2 * L ^ 2 := by
      field_simp
    rw [hrw] at hE
    have hsq : ℓ ^ 2 ≤ Θ ^ 2 := pow_le_pow_left₀ (by linarith) hℓΘ 2
    have hKL : (0 : ℝ) ≤ K * L ^ 2 := by positivity
    have hprod : (0 : ℝ) ≤ K * L ^ 2 * (Θ ^ 2 - ℓ ^ 2) := mul_nonneg hKL (by linarith)
    nlinarith [hprod]
  have hPE : P * E ≤ (Cst * Real.log (2 / τ) ^ 2 / W ^ 2) * (K * Θ ^ 2 * L ^ 2) :=
    mul_le_mul hP hEΘ hE0 (by positivity)
  have hcoef : (0 : ℝ) ≤ Cst * K * Θ ^ 2 * L ^ 2 / W ^ 2 := by positivity
  have hstep : Real.log (2 / τ) ^ 2 ≤ Real.log (2 * Θ) ^ 4 / (τ * Real.log (2 / τ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc Real.log (2 / τ) ^ 2 * (τ * Real.log (2 / τ) ^ 2) = τ * Real.log (2 / τ) ^ 4 := by ring
      _ ≤ Real.log (2 * Θ) ^ 4 := harith
  calc P * E ≤ (Cst * Real.log (2 / τ) ^ 2 / W ^ 2) * (K * Θ ^ 2 * L ^ 2) := hPE
    _ = (Cst * K * Θ ^ 2 * L ^ 2 / W ^ 2) * Real.log (2 / τ) ^ 2 := by ring
    _ ≤ (Cst * K * Θ ^ 2 * L ^ 2 / W ^ 2)
          * (Real.log (2 * Θ) ^ 4 / (τ * Real.log (2 / τ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep hcoef
    _ = Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4 * (L ^ 2 / W ^ 2)
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by ring

/-! ### The middle range's pull-out

The middle range's chain: (1) `‖F_t‖²‖F_u‖² = P_tP_uQ` on the blocks; (2) (5.2) bounds `P_u` on
the barrier, which then relaxes to `R(t)`; (3) `E[1_{R(t)}·Q·P_t] = E[1_{R(t)}Q]·E[P_t]`;
(4) `∫ 1_{R(t)}Q = P~_Q(R(t))·E[Q]`; (5) `P~_Q(R(t)) = P~₂(R(t))`, Harper's licence.

Step 3 needs the pair `(1_{R(t)}, Q)` independent of `P_t`.  The quotient is
`\exp(2∑_{m>k}\text{increment}_m)` at each height, so `Q` reads the blocks `(k, N]`, the barrier
`[r, r+n) ⊆ (k, N]` and `P_t` the blocks `[0, k]`: one application of
`RMF.indepFun_of_disjoint_groups`.  `RMF.icoExtend` (`RMF.shiftExtend` without the shift) writes
both high functionals on one index set. -/

/-- The sequence rebuilt from the increments in `[a,b)`: `m ↦ w m` for `m ∈ [a, b)`, and `0`
otherwise (`RMF.shiftExtend` without the shift). -/
noncomputable def icoExtend (a b : ℕ) (w : ↑(Finset.Ico a b) → ℝ × ℝ) : ℕ → ℝ × ℝ :=
  fun m => if h : m ∈ Finset.Ico a b then w ⟨m, h⟩ else 0

lemma measurable_icoExtend (a b : ℕ) : Measurable (icoExtend a b) := by
  refine measurable_pi_lambda _ fun m => ?_
  by_cases h : m ∈ Finset.Ico a b
  · simp only [icoExtend, dif_pos h]
    exact measurable_pi_apply _
  · simp only [icoExtend, dif_neg h]
    exact measurable_const

lemma icoExtend_apply {a b m : ℕ} (h : m ∈ Finset.Ico a b) (w : ↑(Finset.Ico a b) → ℝ × ℝ) :
    icoExtend a b w m = w ⟨m, h⟩ := dif_pos h

/-- **The barrier together with the quotient is independent of the low blocks**: step 3 of the
middle range's chain.  `k < r` puts the split index below the shift, and `r + n ≤ N + 1` puts the
barrier's blocks inside the quotient's range, so both functionals live on one side. -/
theorem indepFun_barrierHighProd_lowBlocks {ν : Measure Ω} {Z : ℕ → Ω → ℝ × ℝ}
    (hZ : iIndepFun Z ν) (hZm : ∀ m, Measurable (Z m)) {n r k N : ℕ} (hkr : k < r)
    (hrn : r + n ≤ N + 1) (u₁ v₁ u₂ v₂ : ℕ → ℝ) (c₁ c₂ : ℝ) :
    IndepFun
      (Set.indicator (barrierEventPair (fun m => Z (m + r)) n u₁ v₁ u₂ v₂)
        (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (Z m ω).1 + 2 * (Z m ω).2))))
      (fun ω => ∑ m ∈ Finset.range (k + 1), (c₁ * (Z m ω).1 + c₂ * (Z m ω).2)) ν := by
  classical
  have hdisj : Disjoint (Finset.Ico (k + 1) (N + 1)) (Finset.range (k + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_range] at hb
    omega
  -- the high-side functional: the barrier's own restriction, and the quotient's sum
  set g : (↑(Finset.Ico (k + 1) (N + 1)) → ℝ × ℝ) → (ℕ → ℝ × ℝ) := fun w =>
    shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => icoExtend (k + 1) (N + 1) w (p : ℕ)
    with hgdef
  have hg : Measurable g := by
    rw [hgdef]
    exact (measurable_shiftExtend r n).comp (measurable_pi_lambda _ fun p =>
      (measurable_pi_apply ((p : ℕ))).comp (measurable_icoExtend (k + 1) (N + 1)))
  have hh : Measurable fun w : ↑(Finset.Ico (k + 1) (N + 1)) → ℝ × ℝ =>
      Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2)) :=
    Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
      (((measurable_pi_apply m).fst).const_mul 2).add (((measurable_pi_apply m).snd).const_mul 2))
  have hφ : Measurable (Set.indicator (g ⁻¹' barrierSet n u₁ v₁ u₂ v₂)
      fun w : ↑(Finset.Ico (k + 1) (N + 1)) → ℝ × ℝ =>
        Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2))) :=
    hh.indicator (hg (measurableSet_barrierSet n u₁ v₁ u₂ v₂))
  have hψ : Measurable fun w : ↑(Finset.range (k + 1)) → ℝ × ℝ =>
      ∑ m ∈ Finset.univ, (c₁ * (w m).1 + c₂ * (w m).2) :=
    Finset.measurable_sum _ fun m _ =>
      (((measurable_pi_apply m).fst).const_mul c₁).add
        (((measurable_pi_apply m).snd).const_mul c₂)
  have h := indepFun_of_disjoint_groups hZ hZm hdisj hφ hψ
  -- both sides are what they should be
  have hlowfun : (fun ω => ∑ m ∈ (Finset.univ : Finset ↑(Finset.range (k + 1))),
        (c₁ * (Z (m : ℕ) ω).1 + c₂ * (Z (m : ℕ) ω).2))
      = fun ω => ∑ m ∈ Finset.range (k + 1), (c₁ * (Z m ω).1 + c₂ * (Z m ω).2) := by
    funext ω
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach _ fun m => c₁ * (Z m ω).1 + c₂ * (Z m ω).2
  have hrestr : ∀ ω : Ω, g (fun p : ↑(Finset.Ico (k + 1) (N + 1)) => Z (p : ℕ) ω)
      = shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => Z (p : ℕ) ω := by
    intro ω
    have heq : (fun p : ↑(Finset.Ico r (r + n)) =>
          icoExtend (k + 1) (N + 1) (fun q : ↑(Finset.Ico (k + 1) (N + 1)) => Z (q : ℕ) ω)
            (p : ℕ))
        = fun p : ↑(Finset.Ico r (r + n)) => Z (p : ℕ) ω := by
      funext p
      have hp2 := p.2
      have hp : ((p : ℕ)) ∈ Finset.Ico (k + 1) (N + 1) := by
        rw [Finset.mem_Ico] at hp2 ⊢
        omega
      rw [icoExtend_apply hp]
    rw [hgdef]
    simp only
    rw [heq]
  have hhighfun : (fun ω => Set.indicator (g ⁻¹' barrierSet n u₁ v₁ u₂ v₂)
        (fun w : ↑(Finset.Ico (k + 1) (N + 1)) → ℝ × ℝ =>
          Real.exp (∑ m ∈ Finset.univ, (2 * (w m).1 + 2 * (w m).2)))
        (fun p : ↑(Finset.Ico (k + 1) (N + 1)) => Z (p : ℕ) ω))
      = Set.indicator (barrierEventPair (fun m => Z (m + r)) n u₁ v₁ u₂ v₂)
        (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (Z m ω).1 + 2 * (Z m ω).2))) := by
    funext ω
    rw [barrierEventPair_shift_eq_preimage]
    by_cases hmem : (fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => Z (p : ℕ) ω) ω
        ∈ barrierSet n u₁ v₁ u₂ v₂
    · rw [Set.indicator_of_mem (by rw [Set.mem_preimage, hrestr ω]; exact hmem),
        Set.indicator_of_mem (by rw [Set.mem_preimage]; exact hmem)]
      simp only
      congr 1
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach _ fun m => 2 * (Z m ω).1 + 2 * (Z m ω).2
    · rw [Set.indicator_of_notMem (by rw [Set.mem_preimage, hrestr ω]; exact hmem),
        Set.indicator_of_notMem (by rw [Set.mem_preimage]; exact hmem)]
  rw [← hlowfun, ← hhighfun]
  exact h

/-- **Step 3 of the middle range's chain: the low product comes out**,
`E[1_{R(t)}·Q·P] = E[1_{R(t)}Q]·E[P]`, with `P` the low product at free coefficients: `(2,0)` for
`P_t` (the pull-out), `(2,2)` for `P_tP_u` (the licence).  No integrability is assumed:
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` needs only strong measurability, and the
integrability of `Q` is the two-point moment being bounded. -/
theorem integral_barrierHighProd_mul_lowBlocks {ν : Measure Ω} {Z : ℕ → Ω → ℝ × ℝ}
    (hZ : iIndepFun Z ν) (hZm : ∀ m, Measurable (Z m)) {n r k N : ℕ} (hkr : k < r)
    (hrn : r + n ≤ N + 1) (u₁ v₁ u₂ v₂ : ℕ → ℝ) (c₁ c₂ : ℝ) :
    (∫ ω, Set.indicator (barrierEventPair (fun m => Z (m + r)) n u₁ v₁ u₂ v₂)
          (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
            (2 * (Z m ω).1 + 2 * (Z m ω).2))) ω
        * Real.exp (∑ m ∈ Finset.range (k + 1), (c₁ * (Z m ω).1 + c₂ * (Z m ω).2)) ∂ν)
      = (∫ ω, Set.indicator (barrierEventPair (fun m => Z (m + r)) n u₁ v₁ u₂ v₂)
            (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
              (2 * (Z m ω).1 + 2 * (Z m ω).2))) ω ∂ν)
        * ∫ ω, Real.exp (∑ m ∈ Finset.range (k + 1),
            (c₁ * (Z m ω).1 + c₂ * (Z m ω).2)) ∂ν := by
  classical
  have hind := (indepFun_barrierHighProd_lowBlocks hZ hZm hkr hrn u₁ v₁ u₂ v₂ c₁ c₂).comp
    (measurable_id (α := ℝ)) Real.measurable_exp
  have hhm : Measurable (Set.indicator (barrierEventPair (fun m => Z (m + r)) n u₁ v₁ u₂ v₂)
      fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
        (2 * (Z m ω).1 + 2 * (Z m ω).2))) := by
    refine Measurable.indicator ?_ ?_
    · exact Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
        (((hZm m).fst).const_mul 2).add (((hZm m).snd).const_mul 2))
    · rw [barrierEventPair_shift_eq_preimage]
      exact ((measurable_shiftExtend r n).comp
        (measurable_pi_lambda _ fun p => hZm (p : ℕ))) (measurableSet_barrierSet n u₁ v₁ u₂ v₂)
  have hlm : Measurable fun ω => Real.exp (∑ m ∈ Finset.range (k + 1),
      (c₁ * (Z m ω).1 + c₂ * (Z m ω).2)) :=
    Real.measurable_exp.comp (Finset.measurable_sum _ fun m _ =>
      (((hZm m).fst).const_mul c₁).add (((hZm m).snd).const_mul c₂))
  exact hind.integral_mul_eq_mul_integral hhm.aestronglyMeasurable hlm.aestronglyMeasurable

/-! ### The quotient, as a functional of the increments

`RMF.integral_barrierHighProd_mul_lowBlocks` pulls out a factor written as
`\exp(∑_{m ∈ [k+1,N+1)}(2\,\text{inc}₁ + 2\,\text{inc}₂))`, and the chain's step 1 produces one
written as `‖I_{[x_{k+1},x_{N+1})}(s₁)‖²‖·(s₂)‖²`.  **They are the same thing**, and this section
says so.

`RMF.log_norm_randomEulerProductIco_eq_walk` already identifies the product from the *bottom* of
the blocks with the walk, which is what (5.2) consumes.  What the pull-out needs is the same at a
general pair of block endpoints, and that is one subtraction: the blocks multiply
(`RMF.eulerProductIco_mul`), the norms are positive, so the logarithms add. -/

/-- **The block product from `x_a` to `x_b` is the exponential of the increments between.** -/
lemma log_norm_randomEulerProductIco_eq_sum {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ) {a b : ℕ}
    (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
      = ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω) := by
  have hfa : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ a⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le a)))
  have hab' : ⌊blockScale θ a⌋₊ + 1 ≤ ⌊blockScale θ b⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ hab))
  have hωa : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hab'⟩
  have hωmid : ∀ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, le_trans hfa hp.2.1, hp.2.2⟩
  have hpa := norm_randomEulerProductIco_pos (Y := Y) hs hωa
  have hpm := norm_randomEulerProductIco_pos (Y := Y) hs hωmid
  have hmul : ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1) s ω‖
      * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
      = ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖ := by
    rw [← norm_mul]
    simp only [randomEulerProductIco]
    rw [eulerProductIco_mul _ hfa hab']
  have hlogsplit := congrArg Real.log hmul
  rw [Real.log_mul hpa.ne' hpm.ne'] at hlogsplit
  have hkey : Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
        (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
      = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
        - Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ a⌋₊ + 1) s ω‖ := by
    rw [← hlogsplit]
    ring
  rw [hkey, log_norm_randomEulerProductIco_eq_walk θ b hs hω,
    log_norm_randomEulerProductIco_eq_walk θ a hs hωa, walk_apply, walk_apply,
    Finset.sum_Ico_eq_sub _ hab]

/-- **The quotient is the exponential the pull-out reads**: the two-height block product between
`x_a` and `x_b`, squared at both heights, is
`\exp(∑_{m ∈ [a,b)}(2\,\text{inc}₁ + 2\,\text{inc}₂))`, the functional that
`RMF.integral_barrierHighProd_mul_lowBlocks` pulls out at `a = k+1`, `b = N+1`.  At `a = 0` it is
the low product `P_tP_u`. -/
lemma normSq_mul_normSq_randomEulerProductIco_eq_exp {Ω : Type*} {Y : ℕ → Ω → ℂ} (θ : ℝ)
    {a b : ℕ} (hab : a ≤ b) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s₂ ω‖ ^ 2
      = Real.exp (∑ m ∈ Finset.Ico a b,
          (2 * (∑ p ∈ primeBlockSub θ m,
                localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
            + 2 * ∑ p ∈ primeBlockSub θ m,
                localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))) := by
  have hab' : ⌊blockScale θ a⌋₊ + 1 ≤ ⌊blockScale θ b⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ hab))
  have hfa : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ a⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le a)))
  have hωmid : ∀ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, le_trans hfa hp.2.1, hp.2.2⟩
  have hexp2 : ∀ x : ℝ, 0 < x → Real.exp (2 * Real.log x) = x ^ 2 := by
    intro x hx
    rw [show (2 : ℝ) * Real.log x = Real.log x + Real.log x by ring, Real.exp_add,
      Real.exp_log hx]
    ring
  have hsplit : (∑ m ∈ Finset.Ico a b,
        (2 * (∑ p ∈ primeBlockSub θ m,
              localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
          + 2 * ∑ p ∈ primeBlockSub θ m,
              localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = 2 * (∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
            localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
        + 2 * ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
            localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit, ← log_norm_randomEulerProductIco_eq_sum θ hab hs₁ hω,
    ← log_norm_randomEulerProductIco_eq_sum θ hab hs₂ hω, Real.exp_add,
    hexp2 _ (norm_randomEulerProductIco_pos (Y := Y) hs₁ hωmid),
    hexp2 _ (norm_randomEulerProductIco_pos (Y := Y) hs₂ hωmid)]

/-! ### Primitives for the middle range

A name for the two-height increment process (`RMF.blockPair`), and the integrability of the
products the pull-out separates; the barrier event's measurability is
`RMF.measurableSet_barrierEventPair`.  For `Re s > 0`,
`RMF.IsSteinhausRMF.ae_norm_randomEulerProductIco_le` bounds each block product by the constant
`∏_p(1-‖p^{-s}‖)^{-1}`, so on a probability space these integrands are integrable.  The bound is
very lossy and only licenses monotonicity steps. -/

/-- **The two-height increment process**:
`m ↦ (∑_{p∈B_m} ℓ(p^{-s₁}, Y_p), ∑_{p∈B_m} ℓ(p^{-s₂}, Y_p))` with `B_m = RMF.primeBlockSub θ m`
and `ℓ = RMF.localLog`; every barrier of the outer range is stated on it. -/
noncomputable def blockPair {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) :
    ℕ → Ω' → ℝ × ℝ := fun m ω =>
  (∑ p ∈ primeBlockSub θ m, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
    ∑ p ∈ primeBlockSub θ m, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))

lemma measurable_blockPair {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'}
    (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) (m : ℕ) :
    Measurable (blockPair θ s₁ s₂ Y m) := by
  refine Measurable.prodMk ?_ ?_ <;>
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)

/-- **The pull-out's integrand is integrable**, deterministically — the low product at one height
times the two high ones. -/
lemma IsSteinhausRMF.integrable_normSq_triple_Ico {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} [IsFiniteMeasure μ]
    (hf : IsSteinhausRMF f μ) (a b c d : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    Integrable (fun ω => ‖randomEulerProductIco f a b s₁ ω‖ ^ 2
      * (‖randomEulerProductIco f c d s₁ ω‖ ^ 2
        * ‖randomEulerProductIco f c d s₂ ω‖ ^ 2)) μ := by
  have hpos : ∀ (y₀ y₁ : ℕ) (s : ℂ), 0 < s.re →
      (0 : ℝ) ≤ ∏ p ∈ primesIco y₀ y₁, (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
    intro y₀ y₁ s hs
    refine Finset.prod_nonneg fun p hp => ?_
    have := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    positivity
  refine Integrable.mono' (integrable_const
    ((∏ p ∈ primesIco a b, (1 - ‖((p : ℕ) : ℂ) ^ (-s₁)‖)⁻¹) ^ 2
      * (((∏ p ∈ primesIco c d, (1 - ‖((p : ℕ) : ℂ) ^ (-s₁)‖)⁻¹) ^ 2)
        * ((∏ p ∈ primesIco c d, (1 - ‖((p : ℕ) : ℂ) ^ (-s₂)‖)⁻¹) ^ 2)))) ?_ ?_
  · exact ((((hf.aemeasurable_randomEulerProductIco a b hs₁).norm.pow_const 2).mul
      ((((hf.aemeasurable_randomEulerProductIco c d hs₁).norm.pow_const 2)).mul
        ((hf.aemeasurable_randomEulerProductIco c d hs₂).norm.pow_const 2)))).aestronglyMeasurable
  · filter_upwards [hf.ae_norm_randomEulerProductIco_le a b hs₁,
      hf.ae_norm_randomEulerProductIco_le c d hs₁,
      hf.ae_norm_randomEulerProductIco_le c d hs₂] with ω h₁ h₂ h₃
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₂ 2)
        (pow_le_pow_left₀ (norm_nonneg _) h₃ 2) (by positivity)
        (pow_nonneg (hpos c d s₁ hs₁) 2))
      (by positivity) (pow_nonneg (hpos a b s₁ hs₁) 2)

/-- **Steps 1 and 2 of the middle range's chain**: on the barrier `P_u ≤ e^{2v₂(k+1)}` by (5.2),
so `∫_A ‖F_t‖²‖F_u‖² ≤ e^{2v₂(k+1)}∫_A P_tQ ≤ e^{2v₂(k+1)}∫ 1_R·P_tQ` for measurable `R ⊇ A`.
(5.2) is stated at the unshifted envelope, so it comes before the passage to `R`, and the pull-out
after, since `A` involves the low blocks and `R` does not; `RMF.barrierEventPair_subset_shiftLevel`
supplies `R`. -/
theorem setIntegral_normSq_pair_le_indicator {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {R : Set Ω'} (hRm : MeasurableSet R)
    (hAR : barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂ ⊆ R) :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
        * ∫ ω, Set.indicator R (fun ω =>
            ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2))
              ω ∂ν := by
  classical
  haveI := hY.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hf0 : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ (k + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le _)))
  have hfk : ⌊blockScale θ (k + 1)⌋₊ + 1 ≤ ⌊blockScale θ (N + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (by omega)))
  have hAm : MeasurableSet (barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂) :=
    measurableSet_barrierEventPair (measurable_blockPair hY θ s₁ s₂) b u₁ v₁ u₂ v₂
  have hGint := hf.integrable_normSq_triple_Ico (⌊blockScale θ 0⌋₊ + 1)
    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1)
    (⌊blockScale θ (N + 1)⌋₊ + 1) hs₁ hs₂
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_steinhausLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hkey : ∀ᵐ ω ∂ν, Set.indicator (barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
        (fun ω => ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω
      ≤ Real.exp (v₂ (k + 1)) ^ 2 * Set.indicator R (fun ω =>
          ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)) ω := by
    filter_upwards [hae] with ω hω
    have hRnn : (0 : ℝ) ≤ Set.indicator R (fun ω =>
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)) ω :=
      Set.indicator_nonneg (fun _ _ => by positivity) ω
    by_cases hmem : ω ∈ barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hAR hmem)]
      -- the product splits at the block cutoff
      have hmul : ∀ s : ℂ, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖
          = ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s ω‖
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖ := by
        intro s
        rw [← norm_mul]
        simp only [randomEulerProductIco]
        rw [eulerProductIco_mul _ hf0 hfk]
      -- (5.2) at the second height
      have hωk : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1),
          ‖Y p ω‖ ≤ 1 := by
        intro p hp
        refine hω p ?_
        rw [mem_primesIco] at hp ⊢
        exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hfk⟩
      have h52 := normSq_randomEulerProductIco_le_of_mem_barrierEvent θ hs₂ hωk hmem.2
        (Nat.le_add_left 1 k) hkb
      rw [hmul s₁, hmul s₂, mul_pow, mul_pow]
      have hnn : (0 : ℝ) ≤ ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) := by
        positivity
      nlinarith [mul_nonneg (sub_nonneg.2 h52) hnn]
    · rw [Set.indicator_of_notMem hmem]
      have : (0 : ℝ) ≤ Real.exp (v₂ (k + 1)) ^ 2 := by positivity
      exact mul_nonneg this hRnn
  calc (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
          ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      = ∫ ω, Set.indicator (barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
          (fun ω => ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω ∂ν :=
        (integral_indicator hAm).symm
    _ ≤ ∫ ω, Real.exp (v₂ (k + 1)) ^ 2 * Set.indicator R (fun ω =>
          ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)) ω ∂ν :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω =>
            Set.indicator_nonneg (fun _ _ => by positivity) ω)
          ((hGint.indicator hRm).const_mul _) hkey
    _ = _ := integral_const_mul _ _

@[simp] lemma blockPair_fst {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) (m : ℕ)
    (ω : Ω') : (blockPair θ s₁ s₂ Y m ω).1
      = ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω) := rfl

@[simp] lemma blockPair_snd {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) (m : ℕ)
    (ω : Ω') : (blockPair θ s₁ s₂ Y m ω).2
      = ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω) := rfl

/-- **The blocks are independent.**  The base-measure sibling of
`RMF.iIndepFun_blockSumPair_tiltedMeasure₂`, and the hypothesis every pull-out needs: the primes
are independent, the blocks are disjoint, so the block sums are.  `RMF.sum_pair_eq` is what turns
the grouping lemma's sum of pairs into `RMF.blockPair`'s pair of sums. -/
lemma iIndepFun_blockPair {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'}
    (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) :
    iIndepFun (blockPair θ s₁ s₂ Y) ν := by
  have h := iIndepFun_finsetSum_of_pairwiseDisjoint
    (f := fun (p : Nat.Primes) (ω : Ω') =>
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
    (fun p => ((measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)))
    (hY.iIndep.comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun _ => (measurable_localLog _).prodMk (measurable_localLog _))
    (S := fun m => primeBlockSub θ m) (pairwise_disjoint_primeBlockSub θ)
  have heq : (fun m (ω : Ω') => ∑ p ∈ primeBlockSub θ m,
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = blockPair θ s₁ s₂ Y := by
    funext m
    exact sum_pair_eq _ _
  rwa [heq] at h

/-- **The low product is the exponential too**, at one height — the `(2,0)` end of the pull-out's
free coefficients. -/
lemma normSq_randomEulerProductIco_eq_exp {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ) {a b : ℕ}
    (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) {ω : Ω'}
    (hω : ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1) :
    ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖ ^ 2
      = Real.exp (2 * ∑ m ∈ Finset.Ico a b, ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) := by
  have hfa : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ a⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le a)))
  have hωmid : ∀ p ∈ primesIco (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, le_trans hfa hp.2.1, hp.2.2⟩
  rw [← log_norm_randomEulerProductIco_eq_sum θ hab hs hω,
    show (2 : ℝ) * Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
        = Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖
          + Real.log ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ a⌋₊ + 1) (⌊blockScale θ b⌋₊ + 1) s ω‖ by ring,
    Real.exp_add, Real.exp_log (norm_randomEulerProductIco_pos (Y := Y) hs hωmid)]
  ring

/-- **Steps 1–3 of the middle range's chain**:
`∫_A ‖F_t‖²‖F_u‖² ≤ e^{2v₂(k+1)}·(∫ 1_{R(t)}Q)·E[P_t]`, from
`RMF.setIntegral_normSq_pair_le_indicator` and `RMF.integral_barrierHighProd_mul_lowBlocks`,
joined by `RMF.normSq_mul_normSq_randomEulerProductIco_eq_exp` and
`RMF.normSq_randomEulerProductIco_eq_exp`.  Steps 4 and 5 read `∫ 1_{R(t)}Q` as
`P~₂(R(t))·E[Q]`. -/
theorem setIntegral_normSq_pair_le_pullout {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
        * ((∫ ω, Set.indicator
              (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
              (fun ω => ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                  * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                      (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)
              ω ∂ν)
          * ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) := by
  classical
  haveI := hY.isProbabilityMeasure
  have hRm : MeasurableSet
      (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :=
    measurableSet_barrierEventPair (fun m => measurable_blockPair hY θ s₁ s₂ (m + r))
      n u₁' v₁' u₂' v₂'
  refine le_trans (setIntegral_normSq_pair_le_indicator hY θ hs₁ hs₂ hkb hbN hRm hAR) ?_
  have hfk : ⌊blockScale θ (k + 1)⌋₊ + 1 ≤ ⌊blockScale θ (N + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (by omega)))
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_steinhausLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hrestrict : ∀ ω : Ω',
      (∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1), ‖Y p ω‖ ≤ 1) →
      ∀ p ∈ primesIco (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1), ‖Y p ω‖ ≤ 1 := by
    intro ω hω p hp
    refine hω p ?_
    rw [mem_primesIco] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hfk⟩
  have hlowrw : ∀ ω : Ω', (∑ m ∈ Finset.range (k + 1),
        (2 * (∑ p ∈ primeBlockSub θ m,
              localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
          + 0 * ∑ p ∈ primeBlockSub θ m,
              localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = 2 * ∑ m ∈ Finset.Ico 0 (k + 1), ∑ p ∈ primeBlockSub θ m,
          localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω) := by
    intro ω
    rw [← Finset.range_eq_Ico, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hform : (∫ ω, Set.indicator
        (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
        (fun ω => ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2))
            ω ∂ν)
      = ∫ ω, Set.indicator
            (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
            (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
              (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))) ω
          * Real.exp (∑ m ∈ Finset.range (k + 1),
              (2 * (blockPair θ s₁ s₂ Y m ω).1 + 0 * (blockPair θ s₁ s₂ Y m ω).2)) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    by_cases hmem : ω ∈ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp only [blockPair_fst, blockPair_snd]
      rw [hlowrw ω,
        normSq_randomEulerProductIco_eq_exp θ (Nat.zero_le (k + 1)) hs₁ (hrestrict ω hω),
        normSq_mul_normSq_randomEulerProductIco_eq_exp θ (by omega : k + 1 ≤ N + 1) hs₁ hs₂ hω]
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  rw [hform, integral_barrierHighProd_mul_lowBlocks (iIndepFun_blockPair hY θ s₁ s₂)
    (measurable_blockPair hY θ s₁ s₂) hkr hrn u₁' v₁' u₂' v₂' 2 0]
  have hQback : (∫ ω, Set.indicator
        (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
        (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))) ω ∂ν)
      = ∫ ω, Set.indicator
            (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
            (fun ω => ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)
            ω ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    by_cases hmem : ω ∈ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp only [blockPair_fst, blockPair_snd]
      rw [normSq_mul_normSq_randomEulerProductIco_eq_exp θ (by omega : k + 1 ≤ N + 1)
        hs₁ hs₂ hω]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  have hPback : (∫ ω, Real.exp (∑ m ∈ Finset.range (k + 1),
        (2 * (blockPair θ s₁ s₂ Y m ω).1 + 0 * (blockPair θ s₁ s₂ Y m ω).2)) ∂ν)
      = ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [blockPair_fst, blockPair_snd]
    rw [hlowrw ω,
      normSq_randomEulerProductIco_eq_exp θ (Nat.zero_le (k + 1)) hs₁ (hrestrict ω hω)]
  rw [hQback, hPback]

/-! ### Steps 4 and 5 — the quotient's tilt

`∫ 1_{R(t)}Q = P~_Q(R(t))·E[Q]` is the definition of the tilted measure, and
`P~_Q(R(t)) = P~₂(R(t))` is Harper's licence.  Both need the quotient's exponent presented as a sum
over **primes** rather than over blocks, since that is the form
`RMF.measure_tilted_sum_localTilt₂_congr` is stated in — so the blocks have to be reassembled
first.

`RMF.biUnion_primeBlockSub_eq_sdiff` does that from the bottom; the `Ico` version below is the
same induction started at `a` instead of `0`, and it is what the *middle* range of blocks needs. -/

/-- **The blocks between `a` and `b` telescope to the annulus between the cutoffs.**  The `Ico`
sibling of `RMF.biUnion_primeBlockSub_eq_sdiff`. -/
lemma biUnion_primeBlockSub_Ico_eq_sdiff (θ : ℝ) {a b : ℕ} (hab : a ≤ b) :
    (Finset.Ico a b).biUnion (primeBlockSub θ)
      = primesBelowSub (⌊blockScale θ b⌋₊ + 1) \ primesBelowSub (⌊blockScale θ a⌋₊ + 1) := by
  classical
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hins : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hins, Finset.biUnion_insert, ih, primeBlockSub_eq_sdiff]
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, fun hc => h2 (primesBelowSub_floor_mono hab hc)⟩
      · exact ⟨primesBelowSub_floor_mono (Nat.le_succ b) h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hj : p ∈ primesBelowSub (⌊blockScale θ b⌋₊ + 1)
      · exact Or.inr ⟨hj, h2⟩
      · exact Or.inl ⟨h1, hj⟩

/-- **The quotient's exponent, as a sum over primes.**  `∑_{m ∈ [a,b)}(2\,\text{inc}₁+2\,
\text{inc}₂)` is `∑_{p} localTilt₂ p` over the annulus — which is exactly what
`RMF.localTilt₂` is: twice the sum of the two local logs. -/
lemma sum_blockPair_Ico_eq_sum_localTilt₂ {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ) {a b : ℕ}
    (hab : a ≤ b) (s₁ s₂ : ℂ) (ω : Ω') :
    (∑ m ∈ Finset.Ico a b,
        (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))
      = ∑ p ∈ primesBelowSub (⌊blockScale θ b⌋₊ + 1) \ primesBelowSub (⌊blockScale θ a⌋₊ + 1),
          localTilt₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
  classical
  rw [← biUnion_primeBlockSub_Ico_eq_sdiff θ hab,
    Finset.sum_biUnion fun i _ j _ hij => pairwise_disjoint_primeBlockSub θ hij]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [blockPair_fst, blockPair_snd]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp [localTilt₂, localTilt]

/-- **Step 4: the restricted integral is the tilted measure times the free one.**  The definition
of `MeasureTheory.Measure.tilted`, with the normaliser undone — the sibling of
`RMF.IsSteinhausRMF.setIntegral_normSq_mul_normSq_eq`, which does the same for the weight
`‖F(s₁)‖²‖F(s₂)‖²` at a cutoff. -/
theorem integral_indicator_exp_eq_tilted_mul {ν : Measure Ω} [IsProbabilityMeasure ν]
    {g : Ω → ℝ} (hint : Integrable (fun ω => Real.exp (g ω)) ν)
    {R : Set Ω} (hR : MeasurableSet R) :
    (∫ ω, Set.indicator R (fun ω => Real.exp (g ω)) ω ∂ν)
      = (ν.tilted g R).toReal * ∫ ω, Real.exp (g ω) ∂ν := by
  have hZ : (0 : ℝ) < ∫ ω, Real.exp (g ω) ∂ν := integral_exp_pos hint
  have hR0 : (0 : ℝ) ≤ ∫ ω in R, Real.exp (g ω) ∂ν :=
    setIntegral_nonneg hR fun _ _ => (Real.exp_pos _).le
  rw [integral_indicator hR, tilted_apply_eq_ofReal_integral' _ hR, integral_div,
    ENNReal.toReal_ofReal (div_nonneg hR0 hZ.le), div_mul_cancel₀ _ hZ.ne']

/-! ### The block below the blocks

Step 5 wants `P~_Q(R(t)) = P~₂(R(t))`, and `P~₂` tilts by the product over **all** primes below the
cutoff — including those below `x₀`, which lie in no block at all.  So the licence's
`S \ S₁ = primesBelowSub\,x_{k+1}` is *not* a union of blocks, and
`RMF.indepFun_barrierShift_lowBlocks` does not reach it.

The repair is to give the primes below `x₀` a block of their own.  `RMF.augBlock` is the block
family with that extra block at index `0` and block `m` at index `m+1`; it is still pairwise
disjoint, so `RMF.blockPairAug` is still an independent family, and now **every** initial segment
of primes is a union of its blocks.  The barrier reads indices `[r+1, r+1+n)` instead of
`[r, r+n)` and `RMF.shiftExtend_blockPairAug` says that is the same function — so the shift
machinery transfers unchanged. -/

/-- The block family with the primes below `x₀ = blockScale θ 0` adjoined as block `0`:
`0 ↦ primesBelowSub (⌊x₀⌋ + 1)`, `m + 1 ↦ RMF.primeBlockSub θ m`. -/
noncomputable def augBlock (θ : ℝ) : ℕ → Finset Nat.Primes
  | 0 => primesBelowSub (⌊blockScale θ 0⌋₊ + 1)
  | m + 1 => primeBlockSub θ m

lemma disjoint_primesBelowSub_primeBlockSub (θ : ℝ) (m : ℕ) :
    Disjoint (primesBelowSub (⌊blockScale θ 0⌋₊ + 1)) (primeBlockSub θ m) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [primeBlockSub_eq_sdiff, Finset.mem_sdiff] at hp'
  exact hp'.2 (primesBelowSub_floor_mono (Nat.zero_le m) hp)

lemma pairwise_disjoint_augBlock (θ : ℝ) :
    Pairwise fun i j => Disjoint (augBlock θ i) (augBlock θ j) := by
  intro i j hij
  cases i with
  | zero =>
    cases j with
    | zero => exact absurd rfl hij
    | succ n => exact disjoint_primesBelowSub_primeBlockSub θ n
  | succ m =>
    cases j with
    | zero => exact (disjoint_primesBelowSub_primeBlockSub θ m).symm
    | succ n => exact pairwise_disjoint_primeBlockSub θ fun h => hij (by omega)

/-- The two-height increment process of the augmented family:
`m ↦ (∑_{p∈augBlock θ m} ℓ(p^{-s₁}, Y_p), ∑_{p∈augBlock θ m} ℓ(p^{-s₂}, Y_p))`. -/
noncomputable def blockPairAug {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) :
    ℕ → Ω' → ℝ × ℝ := fun m ω =>
  (∑ p ∈ augBlock θ m,
      localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
    ∑ p ∈ augBlock θ m,
      localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))

@[simp] lemma blockPairAug_succ {Ω' : Type*} (θ : ℝ) (s₁ s₂ : ℂ) (Y : ℕ → Ω' → ℂ) (m : ℕ) :
    blockPairAug θ s₁ s₂ Y (m + 1) = blockPair θ s₁ s₂ Y m := rfl

lemma measurable_blockPairAug {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) (m : ℕ) :
    Measurable (blockPairAug θ s₁ s₂ Y m) := by
  refine Measurable.prodMk ?_ ?_ <;>
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)

/-- **The augmented blocks are independent**, by the same grouping as
`RMF.iIndepFun_blockPair` — the extra block is disjoint from all the others. -/
lemma iIndepFun_blockPairAug {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ) (s₁ s₂ : ℂ) :
    iIndepFun (blockPairAug θ s₁ s₂ Y) ν := by
  have h := iIndepFun_finsetSum_of_pairwiseDisjoint
    (f := fun (p : Nat.Primes) (ω : Ω') =>
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
    (fun p => ((measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)).prodMk
      ((measurable_localLog _).comp (hY.measurable (p : ℕ) p.2)))
    (hY.iIndep.comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun _ => (measurable_localLog _).prodMk (measurable_localLog _))
    (S := augBlock θ) (pairwise_disjoint_augBlock θ)
  have heq : (fun m (ω : Ω') => ∑ p ∈ augBlock θ m,
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = blockPairAug θ s₁ s₂ Y := by
    funext m
    exact sum_pair_eq _ _
  rwa [heq] at h

/-- **Every initial segment of primes is a union of augmented blocks.**  This is what the plain
`RMF.biUnion_primeBlockSub_eq_sdiff` could not say: there the union misses the primes below
`x₀`. -/
lemma biUnion_augBlock_eq (θ : ℝ) (j : ℕ) :
    (Finset.range (j + 1)).biUnion (augBlock θ)
      = primesBelowSub (⌊blockScale θ j⌋₊ + 1) := by
  classical
  induction j with
  | zero =>
    rw [Finset.range_one, Finset.singleton_biUnion]
    rfl
  | succ j ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, ih]
    change primeBlockSub θ j ∪ primesBelowSub (⌊blockScale θ j⌋₊ + 1) = _
    rw [primeBlockSub_eq_sdiff]
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · exact primesBelowSub_floor_mono (Nat.le_succ j) h1
    · intro h1
      by_cases hj : p ∈ primesBelowSub (⌊blockScale θ j⌋₊ + 1)
      · exact Or.inr hj
      · exact Or.inl ⟨h1, hj⟩

/-- **The low tilt, as a sum over augmented blocks.**  The `(2,2)` functional over
`[0,j]` is `∑_{p < x_j} localTilt₂ p` — all of it, not just the part above `x₀`. -/
lemma sum_blockPairAug_range_eq_sum_localTilt₂ {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ) (j : ℕ)
    (s₁ s₂ : ℂ) (ω : Ω') :
    (∑ m ∈ Finset.range (j + 1),
        (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))
      = ∑ p ∈ primesBelowSub (⌊blockScale θ j⌋₊ + 1),
          localTilt₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
  classical
  rw [← biUnion_augBlock_eq θ j,
    Finset.sum_biUnion fun i _ k _ hik => pairwise_disjoint_augBlock θ hik]
  refine Finset.sum_congr rfl fun m _ => ?_
  change 2 * (∑ p ∈ augBlock θ m, localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω))
      + 2 * (∑ p ∈ augBlock θ m, localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω))
    = _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp [localTilt₂, localTilt]

/-- **The shift sees the same function either way.**  Shifting the augmented family by `r+1` is
shifting the plain one by `r`, so every lemma about the shifted barrier transfers. -/
lemma shiftExtend_blockPairAug {Ω' : Type*} {Y : ℕ → Ω' → ℂ} (θ : ℝ) (s₁ s₂ : ℂ) (r n : ℕ)
    (ω : Ω') :
    (shiftExtend (r + 1) n fun p : ↑(Finset.Ico (r + 1) (r + 1 + n)) =>
        blockPairAug θ s₁ s₂ Y (p : ℕ) ω)
      = shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) => blockPair θ s₁ s₂ Y (p : ℕ) ω := by
  funext m
  by_cases h : m + r ∈ Finset.Ico r (r + n)
  · have h' : m + (r + 1) ∈ Finset.Ico (r + 1) (r + 1 + n) := by
      rw [Finset.mem_Ico] at h ⊢
      omega
    simp only [shiftExtend, dif_pos h, dif_pos h']
    change blockPairAug θ s₁ s₂ Y (m + (r + 1)) ω = blockPair θ s₁ s₂ Y (m + r) ω
    rw [show m + (r + 1) = m + r + 1 by ring]
    rfl
  · have h' : m + (r + 1) ∉ Finset.Ico (r + 1) (r + 1 + n) := by
      rw [Finset.mem_Ico] at h ⊢
      omega
    simp only [shiftExtend, dif_neg h, dif_neg h']

/-- **The augmented blocks are independent under any measure the primes are independent under.**
The form step 5 needs, where the measure is the quotient's own tilt rather than `ν`. -/
lemma iIndepFun_blockPairAug_of {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    (ν' : Measure Ω') (hm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)))
    (hi : iIndepFun (fun p : Nat.Primes => Y ((p : Nat.Primes) : ℕ)) ν') (θ : ℝ) (s₁ s₂ : ℂ) :
    iIndepFun (blockPairAug θ s₁ s₂ Y) ν' := by
  have h := iIndepFun_finsetSum_of_pairwiseDisjoint
    (f := fun (p : Nat.Primes) (ω : Ω') =>
      (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
    (fun p => ((measurable_localLog _).comp (hm p)).prodMk ((measurable_localLog _).comp (hm p)))
    (hi.comp
      (fun (p : Nat.Primes) (z : ℂ) => (localLog (((p : ℕ) : ℂ) ^ (-s₁)) z,
        localLog (((p : ℕ) : ℂ) ^ (-s₂)) z))
      fun _ => (measurable_localLog _).prodMk (measurable_localLog _))
    (S := augBlock θ) (pairwise_disjoint_augBlock θ)
  have heq : (fun m (ω : Ω') => ∑ p ∈ augBlock θ m,
        (localLog (((p : ℕ) : ℂ) ^ (-s₁)) (Y ((p : Nat.Primes) : ℕ) ω),
          localLog (((p : ℕ) : ℂ) ^ (-s₂)) (Y ((p : Nat.Primes) : ℕ) ω)))
      = blockPairAug θ s₁ s₂ Y := by
    funext m
    exact sum_pair_eq _ _
  rwa [heq] at h

/-- **Step 5: Harper's licence, at the quotient's tilt**, `P~_Q(R(t)) = P~₂(R(t))`.  The tilt over
the low primes, everything below `x_{k+1}` including the primes below `x₀`, is independent of
`R(t)`, which reads only blocks above the shift (`k < r`).  Under the quotient's tilt the primes
stay independent (`RMF.iIndepFun_tilted_finsetSum`), hence so do the blocks of `RMF.blockPairAug`,
and `RMF.indepFun_barrierShift_lowBlocks` supplies the hypothesis of
`RMF.measure_tilted_sum_localTilt₂_congr`. -/
theorem measure_tilted_quotient_eq_tiltedMeasure₂ {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N k r n : ℕ} (hkN : k + 1 ≤ N + 1)
    (hkr : k < r) (u₁' v₁' u₂' v₂' : ℕ → ℝ) :
    ν.tilted (fun ω => ∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))
        (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
      = tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
          (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') := by
  classical
  haveI := hY.isProbabilityMeasure
  have hTS : primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1)
      ⊆ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1) := primesBelowSub_floor_mono hkN
  have hS₁S : primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
        \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1)
      ⊆ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1) := Finset.sdiff_subset
  have hdiff : primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
        \ (primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
          \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1))
      = primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1) := Finset.sdiff_sdiff_eq_self hTS
  have hexp : (fun ω => ∑ m ∈ Finset.Ico (k + 1) (N + 1),
        (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))
      = fun ω => ∑ p ∈ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
            \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1),
          localTilt₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
    funext ω
    exact sum_blockPair_Ico_eq_sum_localTilt₂ θ hkN s₁ s₂ ω
  -- the primes stay independent under the quotient's tilt
  have hprimes : iIndepFun (fun p : Nat.Primes => Y ((p : Nat.Primes) : ℕ))
      (ν.tilted fun ω => ∑ p ∈ primesBelowSub (⌊blockScale θ (N + 1)⌋₊ + 1)
          \ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1),
        localTilt₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω)) :=
    iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun p : Nat.Primes => Y ((p : Nat.Primes) : ℕ)) (g := localTilt₂ s₁ s₂)
      hY.iIndep (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2)
      (fun p => measurable_localTilt₂ s₁ s₂ p)
      (fun p _ => integrable_exp_localTilt₂ hY p hs₁ hs₂)
  have hAug := indepFun_barrierShift_lowBlocks
    (iIndepFun_blockPairAug_of _ (fun p => hY.measurable ((p : Nat.Primes) : ℕ) p.2)
      hprimes θ s₁ s₂)
    (measurable_blockPairAug hY θ s₁ s₂) (n := n) (r := r + 1) (k := k + 1) (by omega)
  have hfun1 : (fun ω => shiftExtend (r + 1) n fun p : ↑(Finset.Ico (r + 1) (r + 1 + n)) =>
        blockPairAug θ s₁ s₂ Y (p : ℕ) ω)
      = fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) =>
        blockPair θ s₁ s₂ Y (p : ℕ) ω := by
    funext ω
    exact shiftExtend_blockPairAug θ s₁ s₂ r n ω
  have hfun2 : (fun ω => ∑ m ∈ Finset.range (k + 1 + 1),
        (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))
      = fun ω => ∑ p ∈ primesBelowSub (⌊blockScale θ (k + 1)⌋₊ + 1),
          localTilt₂ s₁ s₂ p (Y ((p : Nat.Primes) : ℕ) ω) := by
    funext ω
    exact sum_blockPairAug_range_eq_sum_localTilt₂ θ (k + 1) s₁ s₂ ω
  rw [hfun1, hfun2] at hAug
  have hu : Measurable (fun ω => shiftExtend r n fun p : ↑(Finset.Ico r (r + n)) =>
      blockPair θ s₁ s₂ Y (p : ℕ) ω) :=
    (measurable_shiftExtend r n).comp
      (measurable_pi_lambda _ fun p => measurable_blockPair hY θ s₁ s₂ (p : ℕ))
  rw [hexp, tiltedMeasure₂_eq_tilted_finsetSum hY _ hs₁ hs₂,
    barrierEventPair_shift_eq_preimage]
  refine (measure_tilted_sum_localTilt₂_congr hY hS₁S hs₁ hs₂ hu
    (measurableSet_barrierSet n u₁' v₁' u₂' v₂') ?_).symm
  rw [hdiff]
  exact hAug

/-- **The two-height block product is integrable**, deterministically — the quotient of the
outer-range chain.  `RMF.IsSteinhausRMF.integrable_normSq_triple_Ico` without the low factor. -/
lemma IsSteinhausRMF.integrable_normSq_pair_Ico {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → ArithmeticFunction ℂ} {μ : Measure Ω'} [IsFiniteMeasure μ]
    (hf : IsSteinhausRMF f μ) (c d : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) :
    Integrable (fun ω => ‖randomEulerProductIco f c d s₁ ω‖ ^ 2
      * ‖randomEulerProductIco f c d s₂ ω‖ ^ 2) μ := by
  have hpos : ∀ (y₀ y₁ : ℕ) (s : ℂ), 0 < s.re →
      (0 : ℝ) ≤ ∏ p ∈ primesIco y₀ y₁, (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)⁻¹ := by
    intro y₀ y₁ s hs
    refine Finset.prod_nonneg fun p hp => ?_
    have := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    positivity
  refine Integrable.mono' (integrable_const
    ((∏ p ∈ primesIco c d, (1 - ‖((p : ℕ) : ℂ) ^ (-s₁)‖)⁻¹) ^ 2
      * (∏ p ∈ primesIco c d, (1 - ‖((p : ℕ) : ℂ) ^ (-s₂)‖)⁻¹) ^ 2)) ?_ ?_
  · exact (((hf.aemeasurable_randomEulerProductIco c d hs₁).norm.pow_const 2).mul
      ((hf.aemeasurable_randomEulerProductIco c d hs₂).norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [hf.ae_norm_randomEulerProductIco_le c d hs₁,
      hf.ae_norm_randomEulerProductIco_le c d hs₂] with ω h₁ h₂
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
      (pow_le_pow_left₀ (norm_nonneg _) h₂ 2) (by positivity) (pow_nonneg (hpos c d s₁ hs₁) 2)

/-- **The middle range, assembled**: steps 1–5 of the chain,
`∫_A ‖F_t‖²‖F_u‖² ≤ (5.2)·P~₂(R(t))·E[Q]·E[P_t]`, the four factors of Harper's outer-range
bound: (5.2) gives `1/(τ\log²(2/τ))` at each height, `RMF.exists_measure_barrier_inter_display_le`
gives `\log²(2/τ)/W²`, `RMF.exists_integral_norm_randomEulerProductIco_sq_le` gives
`E[P_t] ≪ 1/τ`, and `RMF.exists_integral_normSq_high_le` gives `E[Q] ≪ (τL)²`. -/
theorem setIntegral_normSq_pair_middle_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
        * ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
                (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')).toReal
            * (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                    (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
          * ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) := by
  classical
  haveI := hY.isProbabilityMeasure
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => Y p ω) ν := hY.isSteinhausRMF
  have hRm : MeasurableSet
      (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :=
    measurableSet_barrierEventPair (fun m => measurable_blockPair hY θ s₁ s₂ (m + r))
      n u₁' v₁' u₂' v₂'
  refine le_trans (setIntegral_normSq_pair_le_pullout hY θ hs₁ hs₂ hkb hbN hkr hrn hAR)
    (le_of_eq ?_)
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_steinhausLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hQae : ∀ᵐ ω ∂ν, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2
      = Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
          (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2)) := by
    filter_upwards [hae] with ω hω
    simp only [blockPair_fst, blockPair_snd]
    exact normSq_mul_normSq_randomEulerProductIco_eq_exp θ (by omega : k + 1 ≤ N + 1)
      hs₁ hs₂ hω
  have hint : Integrable (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
      (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))) ν :=
    (hf.integrable_normSq_pair_Ico (⌊blockScale θ (k + 1)⌋₊ + 1)
      (⌊blockScale θ (N + 1)⌋₊ + 1) hs₁ hs₂).congr hQae
  have h4 := integral_indicator_exp_eq_tilted_mul hint hRm
  have h5 := measure_tilted_quotient_eq_tiltedMeasure₂ hY θ hs₁ hs₂
    (by omega : k + 1 ≤ N + 1) hkr (n := n) u₁' v₁' u₂' v₂'
  have hind : (∫ ω, Set.indicator
        (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
        (fun ω => ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω ∂ν)
      = ∫ ω, Set.indicator
          (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
          (fun ω => Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
            (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2))) ω ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hQae] with ω hω
    by_cases hmem : ω ∈ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂'
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  have hfree : (∫ ω, Real.exp (∑ m ∈ Finset.Ico (k + 1) (N + 1),
        (2 * (blockPair θ s₁ s₂ Y m ω).1 + 2 * (blockPair θ s₁ s₂ Y m ω).2)) ∂ν)
      = ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hQae] with ω hω
    rw [hω]
  rw [hind, h4, h5, hfree]

/-! ### The three ranges, at the expansion's own integrand

The expansion identity leaves `∫_{L t ∩ L u}‖F_t‖²‖F_u‖²`, with `F` over all primes below the
cutoff, while the middle range's chain runs over the blocks from `x₀` up.  The primes below `x₀`,
block `0` of `RMF.augBlock`, are pulled out first.  That costs `E[P₀] ≪ (\log x₀)⁴` with
`\log x₀ = e^{θ}`: bounded in terms of `θ`, and much smaller than the deterministic bound,
`RMF.eulerBound` at `x₀`. -/

/-- **The rotation, for a plain pair.**  `RMF.integral_normSq_ico_triple_shift` at `y₀ = N₁`,
where the low factor is the empty product. -/
theorem integral_normSq_ico_pair_shift {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (N₁ N₂ : ℕ) {σ : ℝ} (hσ : 0 < 1 / 2 + σ) (t u : ℝ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
            (shiftLine σ t) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
            (shiftLine σ u) ω‖ ^ 2 ∂μ)
      = ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
            (shiftLine σ 0) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) N₁ N₂
            (shiftLine σ (u - t)) ω‖ ^ 2 ∂μ := by
  have hre : ∀ v : ℝ, 0 < (shiftLine σ v).re := fun v => by rw [re_shiftLine]; exact hσ
  have h := integral_normSq_ico_triple_shift hX N₁ N₁ N₂ hσ t u
  simp only [norm_randomEulerProductIco_self_eq_one (hre t),
    norm_randomEulerProductIco_self_eq_one (hre 0), one_pow, one_mul] at h
  exact h

/-- **The two-fold weight is the exponential of the prime sum.**  `RMF.tiltExponent₂_ae_eq_sum`
and `RMF.IsSteinhausRMF.exp_tiltExponent₂_ae_eq`, composed. -/
lemma exp_sum_localTilt₂_ae_eq {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsSteinhausPrimeValues X μ) (y : ℕ) {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re)
    (hs₂ : 0 < s₂.re) :
    (fun ω => Real.exp (∑ p ∈ primesBelowSub y, localTilt₂ s₁ s₂ p (X ((p : Nat.Primes) : ℕ) ω)))
      =ᵐ[μ] fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y s₁ ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) y s₂ ω‖ ^ 2 := by
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  filter_upwards [tiltExponent₂_ae_eq_sum hX y hs₁ hs₂, hf.exp_tiltExponent₂_ae_eq y hs₁ hs₂]
    with ω h1 h2
  rw [← h1]
  exact h2

/-- **The bottom of the Euler product comes out.**  The expansion's integrand runs over all primes
below the cutoff, the middle range's chain over the blocks from `x₀` up.  The primes below `x₀`
form block `0` of `RMF.augBlock`, disjoint from the others, so they pull out as the low blocks do
(`RMF.integral_barrierHighProd_mul_lowBlocks` at `r = 1`, `k = 0`), at the cost
`E[P₀] ≪ (\log x₀)⁴`. -/
theorem setIntegral_normSq_pair_split_bottom {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) (N b : ℕ) (hbN : b ≤ N) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      = (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
            ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
        * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν := by
  classical
  haveI := hY.isProbabilityMeasure
  have hAm : MeasurableSet (barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂) :=
    measurableSet_barrierEventPair (measurable_blockPair hY θ s₁ s₂) b u₁ v₁ u₂ v₂
  have hf0 : ⌊blockScale θ 0⌋₊ + 1 ≤ ⌊blockScale θ (N + 1)⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_le_floor (blockScale_mono θ (Nat.zero_le _)))
  have hae := ae_forall_norm_le_one_primesIco hY norm_le_one_steinhausLaw
    (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1)
  have hbar : (fun m => blockPairAug θ s₁ s₂ Y (m + 1)) = blockPair θ s₁ s₂ Y := by
    funext m
    exact blockPairAug_succ θ s₁ s₂ Y m
  have hpull := integral_barrierHighProd_mul_lowBlocks (iIndepFun_blockPairAug hY θ s₁ s₂)
    (measurable_blockPairAug hY θ s₁ s₂) (n := b) (r := 1) (k := 0) (N := N + 1)
    (by omega) (by omega) u₁ v₁ u₂ v₂ 2 2
  rw [hbar] at hpull
  -- the high exponential is the block product, the low one the product below `x₀`
  have hW : ∀ᵐ ω ∂ν, Real.exp (∑ m ∈ Finset.Ico (0 + 1) (N + 1 + 1),
        (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))
      = ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [← Finset.sum_Ico_add' (fun m => 2 * (blockPairAug θ s₁ s₂ Y m ω).1
      + 2 * (blockPairAug θ s₁ s₂ Y m ω).2) 0 (N + 1) 1]
    simp only [blockPairAug_succ, blockPair_fst, blockPair_snd]
    exact (normSq_mul_normSq_randomEulerProductIco_eq_exp θ (Nat.zero_le (N + 1)) hs₁ hs₂
      hω).symm
  have hP : ∀ᵐ ω ∂ν, Real.exp (∑ m ∈ Finset.range (0 + 1),
        (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))
      = ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 := by
    filter_upwards [exp_sum_localTilt₂_ae_eq hY (⌊blockScale θ 0⌋₊ + 1) hs₁ hs₂] with ω hω
    rw [sum_blockPairAug_range_eq_sum_localTilt₂ θ 0 s₁ s₂ ω]
    exact hω
  -- the whole product splits at `x₀`
  have hsplit : ∀ᵐ ω ∂ν,
      ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2
        = (‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2)
          * (‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hmul : ∀ s : ℂ, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
          (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖
        = ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s ω‖
          * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s ω‖ := by
      intro s
      rw [← norm_mul]
      simp only [randomEulerProduct, randomEulerProductIco]
      rw [eulerProduct_mul_eulerProductIco _ hf0]
    rw [hmul s₁, hmul s₂, mul_pow, mul_pow]
    ring
  -- assemble
  rw [← integral_indicator hAm, ← integral_indicator hAm]
  have hleft : (∫ ω, Set.indicator (barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2) ω ∂ν)
      = ∫ ω, Set.indicator (barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂)
          (fun ω => Real.exp (∑ m ∈ Finset.Ico (0 + 1) (N + 1 + 1),
            (2 * (blockPairAug θ s₁ s₂ Y m ω).1
              + 2 * (blockPairAug θ s₁ s₂ Y m ω).2))) ω
        * Real.exp (∑ m ∈ Finset.range (0 + 1),
            (2 * (blockPairAug θ s₁ s₂ Y m ω).1 + 2 * (blockPairAug θ s₁ s₂ Y m ω).2)) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hW, hP, hsplit] with ω hw hp hs
    by_cases hmem : ω ∈ barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hs, hw, hp]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  rw [hleft, hpull]
  refine congrArg₂ (· * ·) (integral_congr_ae ?_) (integral_congr_ae hP)
  filter_upwards [hW] with ω hw
  by_cases hmem : ω ∈ barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hw]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- **The middle range, at the expansion's own integrand**: `RMF.setIntegral_normSq_pair_middle_le`
with the bottom of the Euler product pulled out, so that the left side is what
`RMF.integral_sq_setIntegral_indicator_normSq_eq` leaves:
`∫_A ‖F_{<y}(s₁)‖²‖F_{<y}(s₂)‖² ≤ (5.2)·P~₂(R(t))·E[Q]·E[P_t]·E[P₀]`, with
`E[P₀] ≪ (\log x₀)⁴ = e^{4θ}`. -/
theorem setIntegral_normSq_pair_full_middle_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂') :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2
          * ((tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
                  (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
                  (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n
                    u₁' v₁' u₂' v₂')).toReal
              * (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                      (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
                    * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                        (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2
                    ∂ν)
            * ∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν)
        * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν := by
  rw [setIntegral_normSq_pair_split_bottom hY θ hs₁ hs₂ N b hbN u₁ v₁ u₂ v₂]
  exact mul_le_mul_of_nonneg_right
    (setIntegral_normSq_pair_middle_le hY θ hs₁ hs₂ hkb hbN hkr hrn hAR)
    (integral_nonneg fun ω => by positivity)

/-- **The free two-point moment of the full product, at a general pair of heights.**
`RMF.exists_integral_normSq_pair_full_le` with the common centre rotated away
(`RMF.integral_normSq_ico_pair_shift`), which is the form the far range needs — there the two
heights are `\text{shiftLine }σ\,t` and `\text{shiftLine }σ\,u`, not `σ` and `σ+it`.

The constant is the same constant: the rotation is an identity. -/
theorem exists_integral_normSq_pair_full_shift_le :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t - u| → |t - u| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t - u| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (N₂ + 1)
                (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => X p ω) (N₂ + 1)
                (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ K * Real.log (N₁ : ℝ) ^ 4 * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_pair_full_le (Ω := Ω)
  refine ⟨K, hK, fun X μ hX σ t u N₁ M N₂ hσ htu htu1 hN₁ hNM hMN₂ hlg hM => ?_⟩
  have hσ' : (0 : ℝ) < 1 / 2 + σ := by linarith
  simp only [← randomEulerProductIco_zero]
  rw [integral_normSq_ico_pair_shift hX 0 (N₂ + 1) hσ' t u, shiftLine_zero_height, shiftLine]
  simp only [randomEulerProductIco_zero]
  have habs : |u - t| = |t - u| := abs_sub_comm u t
  exact hbound X μ hX σ (u - t) N₁ M N₂ hσ (by rwa [habs]) (by rwa [habs]) hN₁ hNM hMN₂
    (by rwa [habs]) hM

/-- **The crude range's integral.**  `∫_{-2}^{2}\min\{L_c,1/|v|\}\,dv ≤ 2(1 + \log(2L_c))`.

This is the `\log` a constant envelope cannot supply, and the crude range needs it: its integrand
is `L²\min\{L,1/τ\}`, not a constant.  Below `1/L_c` the minimum is `L_c` and contributes `1`;
above it the minimum is `1/|v|` and contributes `\log(2L_c)`. -/
theorem integral_min_abs_inv_le {Lc : ℝ} (hLc : 1 ≤ Lc) :
    (∫ v in Set.Icc (-2 : ℝ) 2, min Lc (1 / |v|)) ≤ 2 * (1 + Real.log (2 * Lc)) := by
  have hLc0 : (0 : ℝ) < Lc := by linarith
  have hinv : (0 : ℝ) < 1 / Lc := by positivity
  have hinv2 : 1 / Lc ≤ 2 := by
    rw [div_le_iff₀ hLc0]
    linarith
  have hnn : ∀ v : ℝ, (0 : ℝ) ≤ min Lc (1 / |v|) := fun v => le_min hLc0.le (by positivity)
  have hbdd : ∀ v : ℝ, min Lc (1 / |v|) ≤ Lc := fun v => min_le_left _ _
  have hmeas : Measurable fun v : ℝ => min Lc (1 / |v|) := by fun_prop
  have hint : ∀ a b : ℝ, IntegrableOn (fun v : ℝ => min Lc (1 / |v|)) (Set.Icc a b) := by
    intro a b
    refine Measure.integrableOn_of_bounded (M := Lc) measure_Icc_lt_top.ne
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn v)]
    exact hbdd v
  have hintIoc : ∀ a b : ℝ, IntegrableOn (fun v : ℝ => min Lc (1 / |v|)) (Set.Ioc a b) :=
    fun a b => (hint a b).mono_set Set.Ioc_subset_Icc_self
  -- the right half
  have hright : (∫ v in Set.Icc (0 : ℝ) 2, min Lc (1 / |v|)) ≤ 1 + Real.log (2 * Lc) := by
    have hsplit : Set.Icc (0 : ℝ) 2 = Set.Icc (0 : ℝ) (1 / Lc) ∪ Set.Ioc (1 / Lc) 2 :=
      (Set.Icc_union_Ioc_eq_Icc hinv.le hinv2).symm
    have hdisj : Disjoint (Set.Icc (0 : ℝ) (1 / Lc)) (Set.Ioc (1 / Lc) 2) := by
      rw [Set.disjoint_left]
      rintro v ⟨_, h2⟩ ⟨h3, _⟩
      linarith
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioc (hint 0 (1 / Lc))
      (hintIoc (1 / Lc) 2)]
    have hlow : (∫ v in Set.Icc (0 : ℝ) (1 / Lc), min Lc (1 / |v|)) ≤ 1 := by
      have hvol : (volume (Set.Icc (0 : ℝ) (1 / Lc))).toReal = 1 / Lc := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by positivity)]
        ring
      have h := setIntegral_le_of_le_const (F := fun v : ℝ => min Lc (1 / |v|)) (C := Lc)
        measurableSet_Icc measure_Icc_lt_top.ne (hint 0 (1 / Lc)) (fun v _ => hbdd v)
      rw [hvol] at h
      refine le_trans h (le_of_eq ?_)
      field_simp
    have hhigh : (∫ v in Set.Ioc (1 / Lc) 2, min Lc (1 / |v|)) ≤ Real.log (2 * Lc) := by
      have hcont : ContinuousOn (fun v : ℝ => 1 / v) (Set.uIcc (1 / Lc) 2) := by
        rw [Set.uIcc_of_le hinv2]
        refine continuousOn_const.div continuousOn_id fun v hv => ?_
        exact ne_of_gt (lt_of_lt_of_le hinv hv.1)
      have hintinv : IntegrableOn (fun v : ℝ => 1 / v) (Set.Ioc (1 / Lc) 2) := by
        refine IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
        have huI : IntegrableOn (fun v : ℝ => 1 / v) (Set.uIcc (1 / Lc) 2) volume :=
          hcont.integrableOn_uIcc
        rwa [Set.uIcc_of_le hinv2] at huI
      have hmono : (∫ v in Set.Ioc (1 / Lc) 2, min Lc (1 / |v|))
          ≤ ∫ v in Set.Ioc (1 / Lc) 2, 1 / v := by
        refine setIntegral_mono_on (hintIoc (1 / Lc) 2) hintinv measurableSet_Ioc fun v hv => ?_
        have hv0 : (0 : ℝ) < v := lt_trans hinv hv.1
        rw [abs_of_pos hv0]
        exact min_le_right _ _
      refine le_trans hmono (le_of_eq ?_)
      have hnot : (0 : ℝ) ∉ Set.uIcc (1 / Lc) 2 := by
        rw [Set.uIcc_of_le hinv2]
        exact fun hc => absurd hc.1 (not_le.2 hinv)
      rw [← intervalIntegral.integral_of_le hinv2, integral_one_div hnot]
      congr 1
      field_simp
    linarith
  -- the left half is the right one reflected
  have hpre : (fun v : ℝ => -v) ⁻¹' Set.Icc (-2 : ℝ) 0 = Set.Icc (0 : ℝ) 2 := by
    ext v
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hleft : (∫ v in Set.Icc (-2 : ℝ) 0, min Lc (1 / |v|)) ≤ 1 + Real.log (2 * Lc) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
      measurableEmbedding_neg (fun v : ℝ => min Lc (1 / |v|)) (Set.Icc (-2 : ℝ) 0)
    simp only [abs_neg, hpre] at h
    rw [← h]
    exact hright
  have hsplit2 : Set.Icc (-2 : ℝ) 2 = Set.Icc (-2 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 2 :=
    (Set.Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)).symm
  have hdisj2 : Disjoint (Set.Icc (-2 : ℝ) 0) (Set.Ioc (0 : ℝ) 2) := by
    rw [Set.disjoint_left]
    rintro v ⟨_, h2⟩ ⟨h3, _⟩
    linarith
  have hIoc_le : (∫ v in Set.Ioc (0 : ℝ) 2, min Lc (1 / |v|)) ≤ 1 + Real.log (2 * Lc) := by
    refine le_trans (setIntegral_mono_set (hint 0 2)
      (Filter.Eventually.of_forall hnn) (Filter.Eventually.of_forall
        (fun v hv => Set.Ioc_subset_Icc_self hv))) hright
  rw [hsplit2, setIntegral_union hdisj2 measurableSet_Ioc (hint (-2) 0) (hintIoc 0 2)]
  linarith

/-! ### The envelope the three ranges share

`RMF.setIntegral_sub_le_of_subset` and `RMF.setIntegral_le_of_le_const` do the `t`-integration
once a **single** function of `τ = |t-u|` dominates the integrand on all of `T × T`.  That function
is `RMF.outerEnvelope`: `C\min\{L_c, 1/|τ|\}`, the crude range's shape, plus `D/(τ\log²(2/τ))` on
`(ε, 1]` — the survivor of `RMF.harper_middle_collapse` and of `RMF.harper_far_collapse` alike,
which is why the middle and far ranges can be integrated together.

It is bounded (so integrable on any bounded set), and for `L_c ≥ 1`, `0 < ε ≤ 1` its integral over
`[-2,2]` is `≤ 2C(1 + \log(2L_c)) + 2D/\log 2` (`RMF.integral_outerEnvelope_le`), uniformly in the
inner cutoff `ε`. -/

/-- **The envelope of the three ranges**, `C\min\{L_c, 1/|τ|\} + 1_{(ε,1]}(τ)·D/(τ\log²(2/τ))`:
the crude range's shape plus the survivor of `RMF.harper_middle_collapse` and
`RMF.harper_far_collapse`.  The first piece cannot be a constant: `CL_c` over `[0,ε]` overshoots
by `(\log x)^{2/3}/(VΛ³)`, and the crude range needs `∫\min\{L_c, 1/τ\} ≪ \log(εL_c)`. -/
noncomputable def outerEnvelope (C Lc D ε : ℝ) (τ : ℝ) : ℝ :=
  C * min Lc (1 / |τ|)
    + Set.indicator (Set.Ioc ε 1) (fun v => D / (v * Real.log (2 / v) ^ 2)) τ

lemma outerEnvelope_nonneg {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 0 ≤ Lc) (hD : 0 ≤ D)
    (hε : 0 < ε) (τ : ℝ) : 0 ≤ outerEnvelope C Lc D ε τ := by
  simp only [outerEnvelope]
  refine add_nonneg (mul_nonneg hC (le_min hLc (by positivity)))
    (Set.indicator_nonneg (fun v hv => ?_) τ)
  have hv0 : 0 < v := lt_of_lt_of_le hε hv.1.le
  have : (0 : ℝ) ≤ Real.log (2 / v) := Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith [hv.2])
  positivity

lemma measurable_outerEnvelope (C Lc D ε : ℝ) : Measurable (outerEnvelope C Lc D ε) := by
  unfold outerEnvelope
  refine Measurable.add ?_ (Measurable.indicator ?_ measurableSet_Ioc) <;> fun_prop

/-- The envelope is bounded, hence integrable on any bounded set. -/
lemma outerEnvelope_le {C Lc D ε : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : 0 < ε) (τ : ℝ) :
    outerEnvelope C Lc D ε τ ≤ C * Lc + D / (ε * Real.log 2 ^ 2) := by
  have hmin : C * min Lc (1 / |τ|) ≤ C * Lc :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hC
  have key : Set.indicator (Set.Ioc ε 1) (fun v => D / (v * Real.log (2 / v) ^ 2)) τ
      ≤ D / (ε * Real.log 2 ^ 2) := by
   by_cases hv : τ ∈ Set.Ioc ε 1
   · rw [Set.indicator_of_mem hv]
     have hv0 : 0 < τ := lt_of_lt_of_le hε hv.1.le
     have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
     have hge : Real.log 2 ≤ Real.log (2 / τ) := by
       refine Real.log_le_log (by norm_num) ?_
       rw [le_div_iff₀ hv0]
       linarith [hv.2]
     have hden : ε * Real.log 2 ^ 2 ≤ τ * Real.log (2 / τ) ^ 2 := by
       have h1 : Real.log 2 ^ 2 ≤ Real.log (2 / τ) ^ 2 := pow_le_pow_left₀ hlog2.le hge 2
       nlinarith [hv.1.le, sq_nonneg (Real.log 2)]
     exact div_le_div_of_nonneg_left hD (by positivity) hden
   · rw [Set.indicator_of_notMem hv]
     positivity
  simp only [outerEnvelope]
  linarith

lemma integrableOn_min_abs_inv (Lc : ℝ) (hLc : 0 ≤ Lc) (a b : ℝ) :
    IntegrableOn (fun v : ℝ => min Lc (1 / |v|)) (Set.Icc a b) := by
  have hmeas : Measurable fun v : ℝ => min Lc (1 / |v|) := by fun_prop
  refine Measure.integrableOn_of_bounded (M := Lc) measure_Icc_lt_top.ne
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hLc (by positivity))]
  exact min_le_left _ _

lemma integrableOn_outerEnvelope {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 0 ≤ Lc) (hD : 0 ≤ D)
    (hε : 0 < ε) (a b : ℝ) :
    IntegrableOn (fun v => outerEnvelope C Lc D ε |v|) (Set.Icc a b) := by
  refine Measure.integrableOn_of_bounded (M := C * Lc + D / (ε * Real.log 2 ^ 2))
    measure_Icc_lt_top.ne
    ((measurable_outerEnvelope C Lc D ε).comp measurable_norm).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun v => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (outerEnvelope_nonneg hC hLc hD hε _)]
  exact outerEnvelope_le hC hD hε _

/-- **The envelope integrates.**  `∫_{-2}^{2}\text{env}(|v|)\,dv ≤ 2C(1+\log(2L_c)) + 2D/\log 2`,
uniformly in the inner cutoff — which is what lets `ε = (\log x)^{-1/3}` be sent to `0`.  The first
term is `RMF.integral_min_abs_inv_le`, the crude range's logarithm; the second is
`RMF.integral_abs_inv_mul_log_sq_le`. -/
theorem integral_outerEnvelope_le {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc) (hD : 0 ≤ D)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ v in Set.Icc (-2 : ℝ) 2, outerEnvelope C Lc D ε |v|)
      ≤ 2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2 := by
  have hS : Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε) ⊆ Set.Icc (-2 : ℝ) 2 := by
    rintro v (hv | hv)
    · exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · exact ⟨by linarith [hv.1], by linarith [hv.2, hε0]⟩
  have hSm : MeasurableSet (Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε)) :=
    measurableSet_Ioc.union measurableSet_Ico
  have hmem : ∀ v : ℝ, (|v| ∈ Set.Ioc ε 1) ↔ v ∈ Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε) := by
    intro v
    simp only [Set.mem_Ioc, Set.mem_Ico, Set.mem_union, abs_le, lt_abs]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2.2⟩
      · exact Or.inr ⟨h2.1, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, ⟨by linarith, h2⟩⟩
      · exact ⟨Or.inr (by linarith), ⟨h1, by linarith⟩⟩
  have hsplit : ∀ v : ℝ, outerEnvelope C Lc D ε |v|
      = C * min Lc (1 / |v|) + Set.indicator (Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε))
          (fun w => D * (1 / (|w| * Real.log (2 / |w|) ^ 2))) v := by
    intro v
    simp only [outerEnvelope, abs_abs]
    congr 1
    by_cases hv : |v| ∈ Set.Ioc ε 1
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((hmem v).1 hv)]
      field_simp
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun hc => hv ((hmem v).2 hc))]
  simp only [hsplit]
  have hint1 : IntegrableOn (fun v : ℝ => C * min Lc (1 / |v|)) (Set.Icc (-2 : ℝ) 2) :=
    (integrableOn_min_abs_inv Lc (by linarith) (-2 : ℝ) 2).const_mul C
  have hint2 : IntegrableOn (fun v => Set.indicator (Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε))
      (fun w => D * (1 / (|w| * Real.log (2 / |w|) ^ 2))) v) (Set.Icc (-2 : ℝ) 2) := by
    have h := (integrableOn_outerEnvelope (Lc := Lc) hC (by linarith) hD hε0 (-2 : ℝ) 2)
    have h' : IntegrableOn (fun v : ℝ => C * min Lc (1 / |v|)
        + Set.indicator (Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε))
          (fun w => D * (1 / (|w| * Real.log (2 / |w|) ^ 2))) v) (Set.Icc (-2 : ℝ) 2) :=
      h.congr (Filter.Eventually.of_forall fun v => hsplit v)
    refine (h'.sub hint1).congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Pi.sub_apply, add_sub_cancel_left]
  rw [integral_add hint1 hint2,
    setIntegral_indicator hSm, Set.inter_eq_self_of_subset_right hS, integral_const_mul,
    integral_const_mul]
  have hmin : C * (∫ v in Set.Icc (-2 : ℝ) 2, min Lc (1 / |v|))
      ≤ 2 * C * (1 + Real.log (2 * Lc)) := by
    calc C * (∫ v in Set.Icc (-2 : ℝ) 2, min Lc (1 / |v|))
        ≤ C * (2 * (1 + Real.log (2 * Lc))) :=
          mul_le_mul_of_nonneg_left (integral_min_abs_inv_le hLc) hC
      _ = 2 * C * (1 + Real.log (2 * Lc)) := by ring
  have hI := integral_abs_inv_mul_log_sq_le hε0 hε1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfin : D * (∫ v in Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε),
      1 / (|v| * Real.log (2 / |v|) ^ 2)) ≤ 2 * D / Real.log 2 := by
    calc D * (∫ v in Set.Ioc ε 1 ∪ Set.Ico (-1 : ℝ) (-ε), 1 / (|v| * Real.log (2 / |v|) ^ 2))
        ≤ D * (2 / Real.log 2) := mul_le_mul_of_nonneg_left hI hD
      _ = 2 * D / Real.log 2 := by ring
  linarith

/-- **The `t`-integration**: given one envelope for the integrand off the diagonal,
`E[X²] ≤ |T|·(2C(1+\log(2L_c)) + 2D/\log 2)`, `X = ∫_T 1_{L t}‖F_t‖² dt`, uniformly in `ε`.
`hpt` is required only for `t ≠ u` (at `τ = 0` the envelope is `0` by `1/0 = 0`, and the
diagonal is null); the three ranges supply it.  Neither integral is assumed integrable:
`MeasureTheory.integral_mono_of_nonneg` needs only the majorant to be. -/
theorem integral_sq_setIntegral_indicator_normSq_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-1 : ℝ) 1) {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc)
    (hD : 0 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hpt : ∀ t ∈ T, ∀ u ∈ T, t ≠ u →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ outerEnvelope C Lc D ε |t - u|) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) := by
  have hTfin : volume T ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hTsub) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rw [integral_sq_setIntegral_indicator_normSq_eq hY y hσ L hLmeas hSmeas hTfin]
  have hnn : ∀ t u : ℝ, (0 : ℝ) ≤
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
        * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν := fun t u =>
    mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun ω => by positivity)
  have hinner : ∀ t ∈ T, (∫ u in T,
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
        * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ 2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2 := by
    intro t ht
    have hmaj : IntegrableOn (fun u => outerEnvelope C Lc D ε |t - u|) T := by
      refine Measure.integrableOn_of_bounded (M := C * Lc + D / (ε * Real.log 2 ^ 2)) hTfin ?_ ?_
      · exact ((measurable_outerEnvelope C Lc D ε).comp
          ((measurable_const.sub measurable_id).norm)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun u => ?_
        rw [Real.norm_eq_abs,
          abs_of_nonneg (outerEnvelope_nonneg (Lc := Lc) hC (by linarith) hD hε0 _)]
        exact outerEnvelope_le (Lc := Lc) hC hD hε0 _
    calc (∫ u in T,
        (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ ∫ u in T, outerEnvelope C Lc D ε |t - u| :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => hnn t u) hmaj
            (by
              have hne : ∀ᵐ u : ℝ, u ≠ t := by
                have h0 : (volume ({t} : Set ℝ)) = 0 := by simp
                filter_upwards [compl_mem_ae_iff.2 h0] with u hu
                simpa using hu
              filter_upwards [ae_restrict_mem hTm, ae_restrict_of_ae hne] with u hu hune
              exact hpt t ht u hu (Ne.symm hune))
      _ ≤ ∫ v in Set.Icc (-2 : ℝ) 2, outerEnvelope C Lc D ε |v| :=
          setIntegral_sub_le_of_subset
            (outerEnvelope_nonneg (Lc := Lc) hC (by linarith) hD hε0) hTsub (hTsub ht)
            (integrableOn_outerEnvelope (Lc := Lc) hC (by linarith) hD hε0 (-2 : ℝ) 2)
      _ ≤ 2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2 :=
          integral_outerEnvelope_le hC hLc hD hε0 hε1
  calc (∫ t in T, ∫ u in T,
        (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
              (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ ∫ _t in T, (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => integral_nonneg fun u => hnn t u)
          (integrableOn_const hTfin)
          ((ae_restrict_iff' hTm).2 (Filter.Eventually.of_forall fun t ht => hinner t ht))
    _ = (volume T).toReal • (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) :=
        setIntegral_const _
    _ = (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) :=
        smul_eq_mul _ _

/-- **The far range, end to end**: `P~₂(L t ∩ L u)·E[‖F_t‖²‖F_u‖²]` is at most
`Cst·K·Θ²\log⁴(2Θ)·(\log M)²/W²·1/(τ\log²(2/τ))`, from the barrier bound (a hypothesis, supplied
by `RMF.exists_measure_barrier_inter_display_le` at Harper's data) and
`RMF.exists_integral_normSq_pair_full_shift_le`, multiplied out by `RMF.harper_far_collapse`. -/
theorem setIntegral_normSq_pair_far_envelope_le {Ω' : Type*} [MeasurableSpace Ω'] :
    ∃ K > 0, ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsSteinhausPrimeValues Y ν →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ) (Θ W Cst : ℝ) (A : Set Ω'),
      0 ≤ σ → 0 < |t - u| → |t - u| ≤ 1 →
      400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
      1 / |t - u| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
      0 ≤ Cst → Real.log (N₁ : ℝ) ≤ Θ →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          ≤ Cst * Real.log (2 / |t - u|) ^ 2 / W ^ 2 →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
            (shiftLine σ t) (shiftLine σ u) ν A).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ Cst * K * Θ ^ 2 * Real.log (2 * Θ) ^ 4
            * (Real.log (M : ℝ) ^ 2 / W ^ 2)
            * (1 / (|t - u| * Real.log (2 / |t - u|) ^ 2)) := by
  obtain ⟨K, hK, hfree⟩ := exists_integral_normSq_pair_full_shift_le (Ω := Ω')
  refine ⟨K, hK, ?_⟩
  intro Y ν hY σ t u N₁ M N₂ Θ W Cst A hσ htu htu1 hN₁ hNM hMN₂ hlg hM hCst hΘ hbar
  have hmom := hfree Y ν hY σ t u N₁ M N₂ hσ htu htu1 hN₁ hNM hMN₂ hlg hM
  have hE0 : (0 : ℝ) ≤ ∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
        (N₂ + 1) (shiftLine σ t) ω‖ ^ 2
      * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
          (shiftLine σ u) ω‖ ^ 2 ∂ν := integral_nonneg fun ω => by positivity
  have hmom' : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
          (shiftLine σ t) ω‖ ^ 2
        * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) (N₂ + 1)
            (shiftLine σ u) ω‖ ^ 2 ∂ν)
      ≤ K * Real.log (N₁ : ℝ) ^ 4
          * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := hmom
  exact harper_far_collapse hCst hK.le htu htu1 hlg hΘ hE0 hbar hmom'

/-- **The high factor at a general pair of heights.**  `RMF.exists_integral_normSq_high_le` with
the common centre rotated away — the quotient `Q` of the middle range's chain lives at
`(\text{shiftLine }σ\,t, \text{shiftLine }σ\,u)`, not at `(σ, σ+it)`.  Same constant: the
rotation is an identity. -/
theorem exists_integral_normSq_high_shift_le :
    ∃ K > 0, ∀ (X : ℕ → Ω → ℂ) (μ : Measure Ω), IsSteinhausPrimeValues X μ →
      ∀ (σ t u : ℝ) (N₁ M N₂ : ℕ), 0 ≤ σ → 0 < |t - u| → |t - u| ≤ 1 →
        400 ≤ (N₁ : ℝ) → N₁ ≤ M → M ≤ N₂ →
        1 / |t - u| ≤ Real.log (N₁ : ℝ) → 1 ≤ 2 * σ * Real.log (M : ℝ) →
        (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ t) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => X p ω) (N₁ + 1)
                (N₂ + 1) (shiftLine σ u) ω‖ ^ 2 ∂μ)
          ≤ K * (Real.log (M : ℝ) / Real.log (N₁ : ℝ)) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_integral_normSq_high_le (Ω := Ω)
  refine ⟨K, hK, fun X μ hX σ t u N₁ M N₂ hσ htu htu1 hN₁ hNM hMN₂ hlg hM => ?_⟩
  have hσ' : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hf : IsSteinhausRMF (fun ω => compMultExtension fun p => X p ω) μ := hX.isSteinhausRMF
  rw [integral_normSq_ico_pair_shift hX (N₁ + 1) (N₂ + 1) hσ' t u, shiftLine_zero_height,
    shiftLine]
  have habs : |u - t| = |t - u| := abs_sub_comm u t
  exact hbound _ μ hf σ (u - t) N₁ M N₂ hσ (by rwa [habs]) (by rwa [habs]) hN₁ hNM hMN₂
    (by rwa [habs]) hM

/-- **(5.2)'s second arm, squared**: on the barrier the pulled-out product at one height is at
most `4e^{a-θ}/(τ\log²(2/τ))`.  `RMF.exp_envelope_splitIndex_le` gives
`e^a\min\{e^m, e^{-θ}/τ\}/j²`, and `1/j² ≤ 4/\log²(2/τ)` needs `\log(2/τ) ≤ 2j`, hence both
`\log(2/τ) ≤ 2m` and `τ ≤ e^{-(2θ+2)}/2`, which fixes the middle range's upper endpoint.  The far
range takes the rest, with `Θ = 2e^{2θ+2}` in `RMF.harper_far_collapse`. -/
lemma exp_envelope_splitIndex_sq_le {θ : ℝ} {m : ℕ} {t : ℝ} (hθ : 0 ≤ θ) (ht : 0 < |t|)
    (hsmall : Real.log 2 + 2 * θ + 2 ≤ Real.log (1 / |t|))
    (hm : Real.log (2 / |t|) ≤ 2 * (m : ℝ)) (a : ℝ) :
    Real.exp (a + (splitIndex θ m t : ℝ) + harperHf (splitIndex θ m t)) ^ 2
      ≤ (4 * Real.exp (a - θ)) ^ 2 * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log (2 / |t|) = Real.log 2 + Real.log (1 / |t|) := by
    rw [show (2 : ℝ) / |t| = 2 * (1 / |t|) by ring, Real.log_mul (by norm_num) (by positivity)]
  have hlogpos : (0 : ℝ) < Real.log (2 / |t|) := by
    rw [hlogt]
    linarith
  -- the split index is at least one, and at least half the logarithm
  have hfl : Real.log (1 / |t|) - θ - 1 ≤ (⌊Real.log (1 / |t|) - θ⌋₊ : ℝ) := by
    have hnn : (0 : ℝ) ≤ Real.log (1 / |t|) - θ := by linarith
    linarith [Nat.sub_one_lt_floor (Real.log (1 / |t|) - θ),
      Nat.floor_le hnn]
  have hmR : Real.log (2 / |t|) ≤ 2 * (m : ℝ) := hm
  have h2j : Real.log (2 / |t|) ≤ 2 * (splitIndex θ m t : ℝ) := by
    rw [splitIndex]
    rcases le_total (m : ℝ) ((⌊Real.log (1 / |t|) - θ⌋₊ : ℕ) : ℝ) with h | h
    · have : min m ⌊Real.log (1 / |t|) - θ⌋₊ = m := by
        refine Nat.min_eq_left ?_
        exact_mod_cast h
      rw [this]
      exact hmR
    · have : min m ⌊Real.log (1 / |t|) - θ⌋₊ = ⌊Real.log (1 / |t|) - θ⌋₊ := by
        refine Nat.min_eq_right ?_
        exact_mod_cast h
      rw [this, hlogt]
      linarith
  have hj1 : 1 ≤ splitIndex θ m t := by
    by_contra hc
    have hj0 : splitIndex θ m t = 0 := by omega
    rw [hj0] at h2j
    simp only [Nat.cast_zero, mul_zero] at h2j
    linarith
  have hjpos : (0 : ℝ) < (splitIndex θ m t : ℝ) := by exact_mod_cast hj1
  have hbase := exp_envelope_splitIndex_le hθ hj1 a
  have hmin : min (Real.exp (m : ℝ)) (Real.exp (-θ) / |t|) ≤ Real.exp (-θ) / |t| :=
    min_le_right _ _
  have hinvsq : 1 / (splitIndex θ m t : ℝ) ^ 2 ≤ 4 / Real.log (2 / |t|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2j, hlogpos.le, hjpos.le]
  have hstep : Real.exp (a + (splitIndex θ m t : ℝ) + harperHf (splitIndex θ m t))
      ≤ 4 * Real.exp (a - θ) * (1 / (|t| * Real.log (2 / |t|) ^ 2)) := by
    refine le_trans hbase ?_
    have hea : (0 : ℝ) < Real.exp a := Real.exp_pos a
    have hkey : Real.exp a * min (Real.exp (m : ℝ)) (Real.exp (-θ) / |t|)
        / (splitIndex θ m t : ℝ) ^ 2
        ≤ Real.exp a * (Real.exp (-θ) / |t|) * (4 / Real.log (2 / |t|) ^ 2) := by
      rw [div_eq_mul_one_div]
      refine mul_le_mul ?_ hinvsq (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hmin hea.le
    refine le_trans hkey (le_of_eq ?_)
    rw [Real.exp_sub, Real.exp_neg]
    field_simp
  have hnn : (0 : ℝ) ≤ Real.exp (a + (splitIndex θ m t : ℝ) + harperHf (splitIndex θ m t)) :=
    (Real.exp_pos _).le
  calc Real.exp (a + (splitIndex θ m t : ℝ) + harperHf (splitIndex θ m t)) ^ 2
      ≤ (4 * Real.exp (a - θ) * (1 / (|t| * Real.log (2 / |t|) ^ 2))) ^ 2 :=
        pow_le_pow_left₀ hnn hstep 2
    _ = (4 * Real.exp (a - θ)) ^ 2 * (1 / (|t| * Real.log (2 / |t|) ^ 2)) ^ 2 := by ring

/-- **The middle range collapses**, as arithmetic: the five factors of
`RMF.setIntegral_normSq_pair_full_middle_le`, bounded by `RMF.exp_envelope_splitIndex_sq_le`,
`RMF.exists_measure_barrier_inter_display_le`, `RMF.exists_integral_normSq_high_shift_le`,
`RMF.exists_integral_norm_randomEulerProductIco_sq_le` and a constant bound on `E[P₀]`, multiply
to Harper's outer-range bound, whose `τ`-dependence cancels to one integrable factor. -/
lemma harper_middle_collapse {E52 Pbar Q Pt P0 X Cst KQ CP K0 L W τ : ℝ}
    (hPbar : 0 ≤ Pbar) (hQ0 : 0 ≤ Q) (hPt0 : 0 ≤ Pt) (hP00 : 0 ≤ P0)
    (hCst : 0 ≤ Cst) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP)
    (hτ0 : 0 < τ) (hlog : Real.log (2 / τ) ≠ 0) (hW : W ≠ 0)
    (h52 : E52 ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2)
    (hbar : Pbar ≤ Cst * Real.log (2 / τ) ^ 2 / W ^ 2)
    (hQ : Q ≤ KQ * (τ * L) ^ 2)
    (hPt : Pt ≤ CP * (1 / τ))
    (hP0 : P0 ≤ K0) :
    E52 * (Pbar * Q * Pt) * P0
      ≤ X ^ 2 * Cst * KQ * CP * K0 * L ^ 2 / W ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) := by
  have hX2 : (0 : ℝ) ≤ X ^ 2 := sq_nonneg X
  have hfac : (0 : ℝ) ≤ (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2 := sq_nonneg _
  have hbar0 : (0 : ℝ) ≤ Cst * Real.log (2 / τ) ^ 2 / W ^ 2 := by positivity
  have hQ0' : (0 : ℝ) ≤ KQ * (τ * L) ^ 2 := by positivity
  have hPt0' : (0 : ℝ) ≤ CP * (1 / τ) := by positivity
  have hprod : E52 * (Pbar * Q * Pt) * P0
      ≤ (X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2)
        * ((Cst * Real.log (2 / τ) ^ 2 / W ^ 2) * (KQ * (τ * L) ^ 2) * (CP * (1 / τ))) * K0 := by
    have h1 : Pbar * Q * Pt
        ≤ (Cst * Real.log (2 / τ) ^ 2 / W ^ 2) * (KQ * (τ * L) ^ 2) * (CP * (1 / τ)) :=
      mul_le_mul (mul_le_mul hbar hQ hQ0 hbar0) hPt hPt0 (by positivity)
    exact mul_le_mul (mul_le_mul h52 h1 (by positivity) (by positivity)) hP0 hP00
      (by positivity)
  refine le_trans hprod (le_of_eq ?_)
  field_simp

/-- **The case split into the envelope**: the pointwise hypothesis of
`RMF.integral_sq_setIntegral_indicator_normSq_le`, from a bound on the crude range and one above
it.  The middle and far ranges leave the same function of `τ`, `D/(τ\log²(2/τ))`, so two cases
suffice, and each piece of `RMF.outerEnvelope` is nonnegative. -/
lemma le_outerEnvelope_of_cases {C Lc D ε Φ τ : ℝ} (hC : 0 ≤ C) (hLc : 0 ≤ Lc) (hD : 0 ≤ D)
    (hε : 0 < ε) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hcrude : τ ≤ ε → Φ ≤ C * min Lc (1 / τ))
    (hout : ε < τ → Φ ≤ D / (τ * Real.log (2 / τ) ^ 2)) :
    Φ ≤ outerEnvelope C Lc D ε τ := by
  have hmin0 : (0 : ℝ) ≤ C * min Lc (1 / τ) :=
    mul_nonneg hC (le_min hLc (by positivity))
  rw [outerEnvelope, abs_of_pos hτ]
  rcases le_or_gt τ ε with h | h
  · have hind : (0 : ℝ) ≤ Set.indicator (Set.Ioc ε 1)
        (fun v => D / (v * Real.log (2 / v) ^ 2)) τ := by
      refine Set.indicator_nonneg (fun v hv => ?_) τ
      have hv0 : 0 < v := lt_of_lt_of_le hε hv.1.le
      have : (0 : ℝ) ≤ Real.log (2 / v) :=
        Real.log_nonneg (by rw [le_div_iff₀ hv0]; linarith [hv.2])
      positivity
    linarith [hcrude h]
  · rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨h, hτ1⟩)]
    linarith [hout h]

/-- **The middle range end to end**: `RMF.setIntegral_normSq_pair_full_middle_le` composed with
`RMF.harper_middle_collapse`, bounding the expansion's integrand by the envelope's shape.  The
five bounds are hypotheses, as in `RMF.harper_middle_collapse`. -/
theorem setIntegral_normSq_pair_middle_envelope_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k r n : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    (hkr : k < r) (hrn : r + n ≤ N + 1) {u₁ v₁ u₂ v₂ u₁' v₁' u₂' v₂' : ℕ → ℝ}
    (hAR : barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂
      ⊆ barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')
    {X Cst KQ CP K0 L W τ : ℝ} (hCst : 0 ≤ Cst) (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP)
    (hτ0 : 0 < τ) (hlog : Real.log (2 / τ) ≠ 0) (hW : W ≠ 0)
    (h52 : Real.exp (v₂ (k + 1)) ^ 2 ≤ X ^ 2 * (1 / (τ * Real.log (2 / τ) ^ 2)) ^ 2)
    (hbar : (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ s₂ ν
            (barrierEventPair (fun m => blockPair θ s₁ s₂ Y (m + r)) n u₁' v₁' u₂' v₂')).toReal
        ≤ Cst * Real.log (2 / τ) ^ 2 / W ^ 2)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
        ≤ KQ * (τ * L) ^ 2)
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
      ≤ X ^ 2 * Cst * KQ * CP * K0 * L ^ 2 / W ^ 2
          * (1 / (τ * Real.log (2 / τ) ^ 2)) := by
  refine le_trans (setIntegral_normSq_pair_full_middle_le hY θ hs₁ hs₂ hkb hbN hkr hrn hAR) ?_
  exact harper_middle_collapse ENNReal.toReal_nonneg
    (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
    (integral_nonneg fun ω => by positivity) hCst hKQ hCP hτ0 hlog hW h52 hbar hQ hPt hP0

/-- **The barrier over no blocks is everything.**  `1 ≤ j ≤ 0` is empty, so the constraint is
vacuous — which is what turns `RMF.setIntegral_normSq_pair_le_pullout` into the crude range's
factorisation. -/
@[simp] lemma barrierEvent_zero {Ω'' : Type*} (X : ℕ → Ω'' → ℝ) (u v : ℕ → ℝ) :
    barrierEvent X 0 u v = Set.univ := by
  ext ω
  simp only [barrierEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro j hj1 hj0
  exact absurd (le_trans hj1 hj0) (by norm_num)

@[simp] lemma barrierEventPair_zero {Ω'' : Type*} (Z : ℕ → Ω'' → ℝ × ℝ) (u₁ v₁ u₂ v₂ : ℕ → ℝ) :
    barrierEventPair Z 0 u₁ v₁ u₂ v₂ = Set.univ := by
  rw [barrierEventPair, barrierEvent_zero, barrierEvent_zero, Set.univ_inter]

/-- **The crude range end to end**: below `(\log x)^{-1/3}` the saving `1/Λ⁴` in (5.2) lets the
indicators be discarded, as in Harper, so the chain is the middle range's over no blocks, where
the pull-out is a plain factorisation: `∫_A ‖F_t‖²‖F_u‖² ≤ (5.2)·E[Q_tQ_u]·E[P_t]·E[P₀]`.  The
split `k` is a parameter because the two regimes split differently, `k+1 = splitIndex + 2` for
`τ ≥ 1/L` and `k+1 = b` for `τ < 1/L` (`RMF.setIntegral_normSq_pair_crude_split_le`,
`RMF.setIntegral_normSq_pair_crude_top_le`). -/
theorem setIntegral_normSq_pair_crude_le {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (θ : ℝ)
    {s₁ s₂ : ℂ} (hs₁ : 0 < s₁.re) (hs₂ : 0 < s₂.re) {N b k : ℕ} (hkb : k + 1 ≤ b) (hbN : b ≤ N)
    {u₁ v₁ u₂ v₂ : ℕ → ℝ} {KQ CP K0 : ℝ} (hKQ : 0 ≤ KQ) (hCP : 0 ≤ CP)
    (hQ : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ (k + 1)⌋₊ + 1) (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ KQ)
    (hPt : (∫ ω, ‖randomEulerProductIco (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) (⌊blockScale θ (k + 1)⌋₊ + 1) s₁ ω‖ ^ 2 ∂ν) ≤ CP)
    (hP0 : (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ 0⌋₊ + 1) s₁ ω‖ ^ 2
            * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
                (⌊blockScale θ 0⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν) ≤ K0) :
    (∫ ω in barrierEventPair (blockPair θ s₁ s₂ Y) b u₁ v₁ u₂ v₂,
        ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
            (⌊blockScale θ (N + 1)⌋₊ + 1) s₁ ω‖ ^ 2
          * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω)
              (⌊blockScale θ (N + 1)⌋₊ + 1) s₂ ω‖ ^ 2 ∂ν)
      ≤ Real.exp (v₂ (k + 1)) ^ 2 * (KQ * CP) * K0 := by
  rw [setIntegral_normSq_pair_split_bottom hY θ hs₁ hs₂ N b hbN u₁ v₁ u₂ v₂]
  have h12 := setIntegral_normSq_pair_le_pullout hY θ hs₁ hs₂ hkb hbN (r := k + 1) (n := 0)
    (lt_add_one k) (by omega) (u₁ := u₁) (v₁ := v₁) (u₂ := u₂) (v₂ := v₂)
    (u₁' := u₁) (v₁' := v₁) (u₂' := u₂) (v₂' := v₂)
    (by simp)
  rw [barrierEventPair_zero] at h12
  simp only [Set.indicator_univ] at h12
  refine mul_le_mul (le_trans h12 ?_) hP0 (integral_nonneg fun ω => by positivity)
    (by positivity)
  exact mul_le_mul_of_nonneg_left (mul_le_mul hQ hPt (integral_nonneg fun ω => by positivity) hKQ)
    (by positivity)

/-- **The last arithmetic of the `t`-integration**: at the ranges' constants `C = EL²/Λ⁴` and
`D = EL²/W²`, `2C(1+\log 2L) + 2D/\log 2 ≤ (6 + 2/\log 2)EL²/W²`, Key Proposition 5's shape.
The crude range's `EL²/Λ³` is at most `EL²/W²` because `W² ≤ Λ`; `1 + \log(2L) ≤ 3Λ` is
generous. -/
lemma harper_outer_total_le {E L W Λ : ℝ} (hE : 0 ≤ E) (hΛ : 1 ≤ Λ) (hW : 0 < W)
    (hWΛ : W ^ 2 ≤ Λ) (hlogL : 1 + Real.log (2 * L) ≤ 3 * Λ) :
    2 * (E * L ^ 2 / Λ ^ 4) * (1 + Real.log (2 * L)) + 2 * (E * L ^ 2 / W ^ 2) / Real.log 2
      ≤ (6 + 2 / Real.log 2) * (E * L ^ 2 / W ^ 2) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hEL : (0 : ℝ) ≤ E * L ^ 2 := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : (E * L ^ 2 / Λ ^ 4) * (3 * Λ) = 3 * (E * L ^ 2 / Λ ^ 3) := by
    field_simp
  have h1 : 2 * (E * L ^ 2 / Λ ^ 4) * (1 + Real.log (2 * L)) ≤ 6 * (E * L ^ 2 / Λ ^ 3) := by
    have hX : (0 : ℝ) ≤ E * L ^ 2 / Λ ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlogL hX
    rw [hkey] at hmul
    linarith
  have hWΛ3 : W ^ 2 ≤ Λ ^ 3 := by nlinarith [sq_nonneg Λ]
  have h2 : E * L ^ 2 / Λ ^ 3 ≤ E * L ^ 2 / W ^ 2 :=
    div_le_div_of_nonneg_left hEL (by positivity) hWΛ3
  have h3 : 2 * (E * L ^ 2 / Λ ^ 4) * (1 + Real.log (2 * L))
        + 2 * (E * L ^ 2 / W ^ 2) / Real.log 2
      ≤ 6 * (E * L ^ 2 / W ^ 2) + 2 * (E * L ^ 2 / W ^ 2) / Real.log 2 := by
    linarith
  refine le_trans h3 (le_of_eq ?_)
  ring

/-- **`E[X²]` from the two pointwise bounds**: `E[X²] ≤ |T|·(2C(1+\log 2L_c) + 2D/\log 2)`,
`X = ∫_T 1_{L t}‖F_t‖² dt`, given `C\min\{L_c,1/τ\}` on the crude range and `D/(τ\log²(2/τ))`
above it.  With `RMF.harper_outer_total_le` at `C = EL²/Λ⁴`, `D = EL²/W²` and `|T| ≤ 1` this is
Key Proposition 5's shape; `RMF/Probability/RestrictedSecondMoment/Assembly.lean` supplies
Harper's data. -/
theorem integral_sq_setIntegral_indicator_normSq_le_of_cases {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsSteinhausPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTsub : T ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) {C Lc D ε : ℝ} (hC : 0 ≤ C) (hLc : 1 ≤ Lc)
    (hD : 0 ≤ D) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hcrude : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → |t - u| ≤ ε →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ C * min Lc (1 / |t - u|))
    (hout : ∀ t ∈ T, ∀ u ∈ T, t ≠ u → ε < |t - u| →
      (tiltedMeasure₂ (fun ω => compMultExtension fun p => Y p ω) y
            (shiftLine σ t) (shiftLine σ u) ν (L t ∩ L u)).toReal
          * (∫ ω, ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                (shiftLine σ t) ω‖ ^ 2
              * ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
                  (shiftLine σ u) ω‖ ^ 2 ∂ν)
        ≤ D / (|t - u| * Real.log (2 / |t - u|) ^ 2)) :
    (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => compMultExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν)
      ≤ (volume T).toReal * (2 * C * (1 + Real.log (2 * Lc)) + 2 * D / Real.log 2) := by
  have hTsub' : T ⊆ Set.Icc (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [(hTsub ht).1], by linarith [(hTsub ht).2]⟩
  refine integral_sq_setIntegral_indicator_normSq_le hY y hσ L hLmeas hSmeas hTm hTsub' hC hLc
    hD hε0 hε1 ?_
  intro t ht u hu htu
  have hτ0 : 0 < |t - u| := abs_pos.2 (sub_ne_zero.2 htu)
  have hτ1 : |t - u| ≤ 1 := by
    have h1 := hTsub ht
    have h2 := hTsub hu
    rw [abs_le]
    constructor
    · linarith [h1.1, h2.2]
    · linarith [h1.2, h2.1]
  exact le_outerEnvelope_of_cases hC (by linarith) hD hε0 hτ0 hτ1
    (fun h => hcrude t ht u hu htu h) (fun h => hout t ht u hu htu h)

end RMF
