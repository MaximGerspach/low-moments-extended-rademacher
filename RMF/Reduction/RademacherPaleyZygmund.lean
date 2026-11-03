/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Reduction.RademacherNumerator
import RMF.Reduction.PaleyZygmund

/-!
# Paley–Zygmund on the restricted integral, for the Rademacher function

`RMF.rpow_integral_div_rpow_integral_sq_le_integral_rpow` is
`(\int X)^{2-q}/(\int X^2)^{1-q} \le \int X^q`, and it is law-free.  What is not is the three side
conditions, at `X\,\omega = \int_T 1_{L(t)}(\omega)\|F_t(\omega)\|^2\,dt`:

* `X` is a.e. measurable, because the integrand is jointly integrable
  (`RMF.integrable_uncurry_indicator_normSq_rademacher`);
* `X` is a.e. **bounded** by `\text{eulerBound } y^2\cdot|T|`, because
  `RMF.ae_forall_norm_indicator_normSq_shiftLine_sqfree_le` bounds the integrand pointwise — by the
  *same* `RMF.eulerBound` the Steinhaus branch uses, since the squarefree product obeys it;
* `\int X^2 > 0`, which comes from the numerator.

So both `X^q` and `X^2` are integrable against a probability measure and the step goes through
verbatim.  **Nothing here is weaker than its Steinhaus mirror**; the numerator that feeds it uses
the full-exponent bound `RMF.le_integral_normSq_of_drop_sqfree'`.
-/

open MeasureTheory

namespace RMF

/-- **Paley–Zygmund on the restricted integral, for the Rademacher RMF.**  The
`RMF.rpow_div_rpow_le_integral_rpow_of_bounds_of_integrable` instance; the mathematics is there,
and all this supplies is the pair of facts about the squarefree product. -/
theorem rpow_div_rpow_le_integral_rpow_of_bounds_rademacher {Ω' : Type*} [MeasurableSpace Ω']
    {Y : ℕ → Ω' → ℂ} {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (L : ℝ → Set Ω') (hLmeas : ∀ t, MeasurableSet (L t))
    (hSmeas : MeasurableSet {q : Ω' × ℝ | q.1 ∈ L q.2}) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTfin : volume T ≠ ⊤)
    {q N Dn : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hN0 : 0 < N) (hDn0 : 0 < Dn)
    (hN : N ≤ ∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ∂ν)
    (hD : (∫ ω, (∫ t in T, Set.indicator (L t)
        (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
          (shiftLine σ t) ω‖ ^ 2) ω) ^ 2 ∂ν) ≤ Dn) :
    N ^ (2 - q) / Dn ^ (1 - q)
      ≤ ∫ ω, (∫ t in T, Set.indicator (L t)
          (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω) y
            (shiftLine σ t) ω‖ ^ 2) ω) ^ q ∂ν := by
  haveI : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  exact rpow_div_rpow_le_integral_rpow_of_bounds_of_integrable y L hTm hTfin
    (integrable_uncurry_indicator_normSq_rademacher hY y (by linarith) L hLmeas hSmeas hTfin)
    (ae_forall_norm_indicator_normSq_shiftLine_sqfree_le hY y hσ L)
    hq0 hq1 hN0 hDn0 hN hD

/-! ### The two barrier tops differ by exactly three blocks

Paley–Zygmund needs numerator and denominator on **one** event.  The denominator,
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher`, runs over
`RMF.harperBarrierTop B V x = RMF.harperN B x - (\lfloor\log V\rfloor + 3)`; the numerator,
`RMF.exists_le_integral_restricted_normSq_numerator_rademacher`, runs over
`RMF.harperBlockCount D x - d`, with the tilt drop `d` satisfying `10\eta \le e^d` at
`\eta = \sigma\log x = 4V`.  So the numerator needs `40V \le e^d`, which
`d = \lfloor\log V\rfloor + 6` gives (`RMF.forty_mul_le_exp_floor_log_add_six`, below) and
`\lfloor\log V\rfloor + 3` does not.
A shorter barrier is a bigger event, and the numerator's event must lie inside the denominator's,
so the denominator moves: three blocks down is `V \mapsto e^3V`, and the range theorems, monotone
in `V`, are reused at `e^3V`. -/

/-- **`40V \le e^{\lfloor\log V\rfloor + 6}`.**  The Rademacher counterpart of
`RMF.four_mul_le_exp_floor_log_add_three`: three more blocks, because `e^3 > 10` and the tilt
condition carries a factor of ten. -/
lemma forty_mul_le_exp_floor_log_add_six {V : ℝ} (hV : 1 ≤ V) :
    40 * V ≤ Real.exp (((⌊Real.log V⌋₊ : ℕ) : ℝ) + 6) := by
  have hbase := four_mul_le_exp_floor_log_add_three hV
  have hsplit : Real.exp (((⌊Real.log V⌋₊ : ℕ) : ℝ) + 6)
      = Real.exp (((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3) * Real.exp 3 := by
    rw [← Real.exp_add]
    ring_nf
  have hpos : (0 : ℝ) < Real.exp (((⌊Real.log V⌋₊ : ℕ) : ℝ) + 3) := Real.exp_pos _
  rw [hsplit]
  nlinarith [ten_le_exp_three, hbase, hpos]

/-! ### The numerator at Harper's data, on the denominator's own event

`RMF.exists_le_integral_restricted_normSq_numerator_rademacher` is stated on `RMF.harperOffset D x`
and `RMF.harperBlockCount D x - d`; the denominator on `RMF.harperTheta B x` and
`RMF.harperBarrierTop B V' x`.  They are the same grid at `D = B + 2`,
`d = \lfloor\log V\rfloor + 6` and `V' = e^3V` (`RMF.harperOffset_eq_harperTheta`,
`RMF.harperBlockCount_sub_eq_harperBarrierTop_exp_three`): the drop is `+6` rather than the
Steinhaus `+3` because the tilt condition is `10\eta \le e^d`.

**Harper's height range discharges the numerator's three side conditions.**  At `t \in [1/3,1/2]`,
`\tau = 2t \in [2/3,1]` gives `0 < \tau` and `\tau^2 \le 1 \le e^{\ldots}`, and
`T_{sh} \le \tau e^{\theta}` is an absolute threshold on `B` because `\theta \ge B + 1`.
-/

/-- **The numerator at Harper's numeric data, for the Rademacher function**: the numerator of
Paley–Zygmund on exactly the event and product that
`RMF.integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher` bounds at `V' = e^3V`;
the twin of `RMF.exists_le_integral_restricted_normSq_harper_data`, with exponent `-64` and
`T ⊆ [1/3,1/2]`.  The slope `B_s ≥ blockSlope 125` is carried because the barrier estimate here,
Harper's Proposition 6, has slope `RMF.blockSlopeAdd Kd 125`. -/
theorem exists_le_integral_restricted_normSq_harper_data_rademacher :
    ∃ (B₀ : ℕ) (a₀ α Bs : ℝ), 0 < α ∧ blockSlope 125 ≤ Bs ∧
      ∀ B : ℕ, B₀ ≤ B → ∀ V : ℝ, 1 ≤ V → ∃ x₀ : ℝ,
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          0 ≤ σ → σ * Real.log x ≤ 4 * V → a₀ ≤ a →
          MeasurableSet T → volume T ≠ ⊤ → T ⊆ Set.Icc (1 / 3 : ℝ) (1 / 2) →
            (volume T).toReal
                * (α * min 1 (a / Real.sqrt
                    (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ))))
                * Real.exp (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) - 64)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                    (harperBarrierTop B (Real.exp 3 * V) x)
                    (fun j => -a - Bs * j) (fun j => a + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ∂ν := by
  obtain ⟨D₀, a₀, α, Bs, Tsh, c, hD₀, hα, hBs, hTsh, hcpos, H⟩ :=
    exists_le_integral_restricted_normSq_numerator_rademacher
  refine ⟨max D₀ ⌈2 * Tsh⌉₊, a₀, α, Bs, hα, hBs, ?_⟩
  intro B hB V hV
  obtain ⟨x₀, H⟩ := H (B + 2)
    (le_trans (le_trans (le_max_left _ _) hB) (by omega)) (⌊Real.log V⌋₊ + 6)
  refine ⟨x₀, ?_⟩
  intro Ω' _ Y ν hY x σ a T hx hx1 hxΛ hσ0 hσ4 ha hT hTfin hTsub
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hθeq : harperOffset (B + 2) x = harperTheta B x := harperOffset_eq_harperTheta B hΛ0
  have hθB : (B : ℝ) + 1 ≤ harperTheta B x := le_harperTheta hΛ0
  -- `B` clears the numerator's own height threshold, which is absolute
  have hTshB : 2 * Tsh ≤ (B : ℝ) := by
    have hcl : (2 : ℝ) * Tsh ≤ ((⌈2 * Tsh⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hcb : ((⌈2 * Tsh⌉₊ : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hB
    linarith
  -- Harper's height range discharges the oscillatory-pair condition outright
  have hheight : ∀ t ∈ T, 0 < 2 * t
      ∧ (2 * t) ^ 2 ≤ Real.exp (c / 2 * Real.exp (harperOffset (B + 2) x / 10))
      ∧ Tsh ≤ 2 * t * Real.exp (harperOffset (B + 2) x) := by
    intro t ht
    obtain ⟨htl, htu⟩ := Set.mem_Icc.1 (hTsub ht)
    refine ⟨by linarith, ?_, ?_⟩
    · have h1 : (2 * t) ^ 2 ≤ 1 := by nlinarith
      have h2 : (1 : ℝ) ≤ Real.exp (c / 2 * Real.exp (harperOffset (B + 2) x / 10)) :=
        Real.one_le_exp (by positivity)
      linarith
    · rw [hθeq]
      have heθ : 2 * Tsh + 2 ≤ Real.exp (harperTheta B x) := by
        have := Real.add_one_le_exp (harperTheta B x)
        linarith
      have hkey : (2 : ℝ) / 3 * (2 * Tsh + 2) ≤ 2 * t * Real.exp (harperTheta B x) :=
        mul_le_mul (by linarith) heθ (by linarith) (by linarith)
      linarith
  have hsrc := H Ω' Y ν hY x σ (4 * V) a T harperHf hx hσ0
    (by rw [abs_of_nonneg hσ0]; exact hσ4)
    (by push_cast; linarith [forty_mul_le_exp_floor_log_add_six hV])
    ha hT hTfin hheight (fun j _ _ => abs_harperHf_le j)
  rw [hθeq, harperBlockCount_sub_eq_harperBarrierTop_exp_three B hV x] at hsrc
  rwa [blockCutoff_harperN hx1 hxΛ]

/-! ### The lower bound on `\int X^q`, composed

Paley–Zygmund with the numerator and the denominator both at Harper's data, on the same barrier
event.  Three things are reconciled:

* the **slope** — the numerator's is raised to `max (blockSlope 125) B_s`, and the denominator
  takes it as a parameter;
* the **length** — the denominator is read at `V' = e^3V`, three blocks short, because the
  Rademacher tilt drop is `\lfloor\log V\rfloor + 6`;
* the **height range** — `T \subseteq [1/3,1/2]` is Harper's own, and both halves want it.

The only numeric hypothesis that moves relative to the Steinhaus twin is the count, from
`6B + 3\log V + 40` to `6B + 3\log V + 49`: the denominator asks it of `V'`, and
`\log V' = \log V + 3`. -/

/-- **The lower bound on `\int X^q`, composed, for the Rademacher function**; the twin of
`RMF.exists_le_integral_rpow_harper_data`.  The conclusion is the raw quotient, exactly as there;
the lemmas simplifying it (`RMF.one_div_W_le_min_one_div_sqrt`, `RMF.exp_neg_le_exp_neg_two_mul`,
`RMF.rpow_neg_le_rpow_mul_rpow`, `RMF.pz_shape_le`) are law-free and are reused. -/
theorem exists_le_integral_rpow_harper_data_rademacher :
    ∃ (a₀ α Bs : ℝ), 0 < α ∧ blockSlope 125 ≤ Bs ∧ ∀ κ : ℝ, 0 ≤ κ → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (σ a q m x : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 49 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (1 / 3 : ℝ) (1 / 2) → volume T ≠ ⊤ →
          0 < (volume T).toReal →
          a₀ ≤ a → 1 ≤ a → 0 ≤ m → m ≤ Real.sqrt (Real.log (Real.log x)) →
          m * (1 - q) ≤ 1 → a ≤ m + κ * Real.log 2 →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            ((volume T).toReal
                  * (α * min 1 (a / Real.sqrt
                      (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ))))
                  * Real.exp (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) - 64)) ^ (2 - q)
                / ((6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
                    / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2)) ^ (1 - q)
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun m ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
                      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                    (harperBarrierTop B (Real.exp 3 * V) x)
                    (fun j => -a - Bs * j) (fun j => a + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ q ∂ν := by
  obtain ⟨B₁, a₀, α, Bs, hα, hBs, HN⟩ :=
    exists_le_integral_restricted_normSq_harper_data_rademacher
  refine ⟨a₀, α, Bs, hα, hBs, ?_⟩
  intro κ hκ
  obtain ⟨B₂, HD⟩ :=
    integral_sq_setIntegral_indicator_normSq_harper_data_le_rademacher κ Bs hκ hBs
  refine ⟨max B₁ B₂, ?_⟩
  intro B hB Ω' _
  obtain ⟨E, hE, HD⟩ := HD B (le_trans (le_max_right _ _) hB) Ω'
  refine ⟨E, hE, ?_⟩
  intro V hV
  have hV0 : (0 : ℝ) < V := by linarith
  have he3 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hVV' : V ≤ Real.exp 3 * V := by nlinarith
  have hV1' : (1 : ℝ) ≤ Real.exp 3 * V := le_trans hV hVV'
  have hlogV' : Real.log (Real.exp 3 * V) = Real.log V + 3 := by
    rw [Real.log_mul (Real.exp_ne_zero 3) hV0.ne', Real.log_exp]
    ring
  obtain ⟨x₀, HN⟩ := HN B (le_trans (le_max_left _ _) hB) V hV
  obtain ⟨Λ₀, HD⟩ := HD V (Real.exp 3 * V) hV hVV' le_rfl
  refine ⟨Λ₀, x₀, ?_⟩
  intro Y ν hY σ a q m x T hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub
    hTfin hT0 ha₀ ha1 hm0 hmΛ hmq ham hq0 hq1 hqΛ
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hσ4 : σ * Real.log x ≤ 4 * V := le_of_eq hσeq
  -- the barrier top, three blocks short, is still positive
  have hΛ6' : (B : ℝ) + Real.log (Real.exp 3 * V) + 6 ≤ Real.log (Real.log x) := by
    rw [hlogV']
    linarith
  have hle' := floor_log_add_three_le_harperN hV1' hxΛ hΛ6'
  have hbge := barrierTop_ge_data hV1' hxΛ hle'
  rw [hlogV'] at hbge
  have hb0R : (0 : ℝ) < ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) := by linarith
  have hsq0 : (0 : ℝ) < Real.sqrt (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hb0R
  -- the two bounds
  have hnum := HN Ω' Y ν hY x σ a T hx hx1 hxΛ hσ0.le hσ4 ha₀ hTm hTfin hTsub
  have hden := HD Y ν hY σ a q m x T hx1 hx3 hΛ₀ (by rw [hlogV']; linarith) hfarwin hσ0 hσhalf
    hσeq hTm hTsub ha1 hm0 hmΛ hmq ham (by linarith) hq1.le hqΛ
  -- the measurability the Paley-Zygmund step needs
  have hXmeas : ∀ (t : ℝ) (m : ℕ), Measurable (fun ω => ∑ p ∈ primeBlockSub (harperTheta B x) m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω)) := fun t m =>
    Finset.measurable_sum _ fun p _ => (measurable_localLogAdd _).comp (hY.measurable (p : ℕ) p.2)
  -- both bounds are positive
  have hminpos : (0 : ℝ)
      < min 1 (a / Real.sqrt (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ))) :=
    lt_min one_pos (by positivity)
  have hNpos : (0 : ℝ) < (volume T).toReal
      * (α * min 1 (a / Real.sqrt (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ))))
      * Real.exp (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) - 64) := by positivity
  have hWpos : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]
  have hDpos : (0 : ℝ) < (6 + 2 / Real.log 2) * (E * Real.exp (2 * a) * (1 / σ) ^ 2
      / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ 2) := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  exact rpow_div_rpow_le_integral_rpow_of_bounds_rademacher hY
    (blockCutoff (harperTheta B x) (harperN B x)) hσ0.le _
    (fun t => measurableSet_barrierEvent (hXmeas t) _ _ _)
    (measurableSet_prod_barrierEventAdd hY (harperTheta B x) σ
      (harperBarrierTop B (Real.exp 3 * V) x) _ _)
    hTm hTfin hq0 hq1 hNpos hDpos hnum hden

/-- **The Rademacher numerator's `e^{n-64}` is `\log x/V` up to a factor depending only on `B`.**
The twin of `RMF.log_div_le_exp_barrierTop_sub`, at the shortened barrier and the deeper exponent.

`b' \ge \Lambda - B - \log V - 9` --- three more than the Steinhaus `-6`, because the drop gives up
`\lfloor\log V\rfloor + 6` blocks --- and `e^{\Lambda} = \log x`, so the factor is `e^{B+73}`
where the Steinhaus one is `e^{B+69}`: `3` for the extra blocks and `1` for the `-64`. -/
lemma log_div_le_exp_barrierTop_sub_rademacher {B : ℕ} {V x : ℝ} (hV : 1 ≤ V) (hx1 : 1 < x)
    (hx : (B : ℝ) + 2 ≤ Real.log (Real.log x))
    (hle : ⌊Real.log (Real.exp 3 * V)⌋₊ + 3 ≤ harperN B x) :
    Real.log x / (V * Real.exp ((B : ℝ) + 73))
      ≤ Real.exp (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) - 64) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hV0 : (0 : ℝ) < V := by linarith
  have he3 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hV1' : (1 : ℝ) ≤ Real.exp 3 * V := by nlinarith
  have hlogV' : Real.log (Real.exp 3 * V) = Real.log V + 3 := by
    rw [Real.log_mul (Real.exp_ne_zero 3) hV0.ne', Real.log_exp]
    ring
  have hbge := barrierTop_ge_data hV1' hx hle
  rw [hlogV'] at hbge
  have hkey : Real.exp (Real.log (Real.log x) - (((B : ℝ) + 73) + Real.log V))
      = Real.log x / (V * Real.exp ((B : ℝ) + 73)) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log hV0, Real.exp_log hlogx]
    ring
  rw [← hkey]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The lower bound on `\int X^q`, in Harper's shape, for the Rademacher function**; the twin of
`RMF.exists_le_integral_rpow_harper_shape`, and the end of the Rademacher Paley–Zygmund step.

`\int X^q \gg c\cdot(\log x)^q\,V^{-q}\,W^{-q}`, `W = 1 + (1-q)\sqrt{\log\log x}` --- **the same
shape as the Steinhaus one, with the same exponents**, where `c` depends on `|T|`, `κ`, `B` and the
space `Ω'` but not on `V`, `x`, `q`, `Y` or `ν`.  What differs is confined to the constants and the
barrier:

* the factor is `e^{B+73}` rather than `e^{B+69}`;
* the count threshold is `6B + 3\log V + 49` rather than `+40`;
* the barrier top is `RMF.harperBarrierTop B (e^3V) x`, and `T \subseteq [1/3,1/2]`.

The level `RMF.harperLevel a_0 n q` and the shape parameter `m = \min\{\sqrt\Lambda, 1/(1-q)\}`
are unchanged. -/
theorem exists_le_integral_rpow_harper_shape_rademacher :
    ∃ (a₀ α Bs : ℝ), 0 < α ∧ 1 ≤ a₀ ∧ blockSlope 125 ≤ Bs ∧
      ∀ κ : ℝ, a₀ ≤ κ * Real.log 2 → ∃ B₀ : ℕ,
      ∀ B : ℕ, B₀ ≤ B →
      ∀ (Ω' : Type*) [MeasurableSpace Ω'], ∃ E : ℝ, 0 < E ∧
        ∀ V : ℝ, 1 ≤ V → ∃ Λ₀ x₀ : ℝ,
        ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (σ q x : ℝ) (T : Set ℝ),
          x₀ ≤ x → 1 < x → 3 ≤ x → Λ₀ ≤ Real.log (Real.log x) →
          (B : ℝ) + 2 ≤ Real.log (Real.log x) →
          6 * (B : ℝ) + 3 * Real.log V + 49 ≤ Real.log (Real.log x) →
          4 * V * (4 * Real.exp (2 * (B : ℝ) + 6) + 7) ≤ Real.log x →
          0 < σ → σ ≤ 1 / 2 → σ * Real.log x = 4 * V →
          MeasurableSet T → T ⊆ Set.Icc (1 / 3 : ℝ) (1 / 2) → volume T ≠ ⊤ →
          0 < (volume T).toReal →
          0 < q → q < 1 → 1 ≤ q * Real.sqrt (Real.log (Real.log x)) →
            min ((volume T).toReal * α) (((volume T).toReal * α) ^ (2 : ℝ))
                * min 1 (1 / ((6 + 2 / Real.log 2) * E))
                * Real.exp (-(2 * (1 + κ * Real.log 2)))
                * (1 + (1 - q) * Real.sqrt (Real.log (Real.log x))) ^ (-q)
                * (Real.exp ((B : ℝ) + 73) ^ (-(2 : ℝ)) * Real.log x ^ q * V ^ (-q))
              ≤ ∫ ω, (∫ t in T, Set.indicator (barrierEvent
                    (fun mm ω => ∑ p ∈ primeBlockSub (harperTheta B x) mm,
                      localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ t))) (Y (p : ℕ) ω))
                    (harperBarrierTop B (Real.exp 3 * V) x)
                    (fun j => -harperLevel a₀
                        ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) q - Bs * j)
                    (fun j => harperLevel a₀
                        ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) q + j + harperHf j))
                  (fun ω => ‖randomEulerProduct (fun ω => squarefreeExtension fun p => Y p ω)
                    (blockCutoff (harperTheta B x) (harperN B x)) (shiftLine σ t) ω‖ ^ 2) ω)
                  ^ q ∂ν := by
  obtain ⟨a₀, α, Bs, hα, hBs, hcomp⟩ := exists_le_integral_rpow_harper_data_rademacher
  refine ⟨max 1 a₀, α, Bs, hα, le_max_left _ _, hBs, ?_⟩
  intro κ hκa
  have hlog2' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hκ : 0 ≤ κ := by
    by_contra hcon
    have hneg : κ < 0 := not_le.mp hcon
    nlinarith [le_max_left (1 : ℝ) a₀, hκa]
  obtain ⟨B₀, hcomp⟩ := hcomp κ hκ
  refine ⟨B₀, ?_⟩
  intro B hB Ω' _
  obtain ⟨E, hE, hcomp⟩ := hcomp B hB Ω'
  refine ⟨E, hE, ?_⟩
  intro V hV
  obtain ⟨Λ₀, x₀, hcomp⟩ := hcomp V hV
  refine ⟨Λ₀, x₀, ?_⟩
  intro Y ν hY σ q x T hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq hTm hTsub hTfin
    hT0 hq0 hq1 hqΛ
  have hlog2 : (0 : ℝ) < Real.log 2 := hlog2'
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hlogV : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log x) := by linarith
  have hσ4 : σ * Real.log x ≤ 4 * V := le_of_eq hσeq
  have hV0 : (0 : ℝ) < V := by linarith
  have he3 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hV1' : (1 : ℝ) ≤ Real.exp 3 * V := by nlinarith
  have hlogV' : Real.log (Real.exp 3 * V) = Real.log V + 3 := by
    rw [Real.log_mul (Real.exp_ne_zero 3) hV0.ne', Real.log_exp]
    ring
  have hΛ6' : (B : ℝ) + Real.log (Real.exp 3 * V) + 6 ≤ Real.log (Real.log x) := by
    rw [hlogV']
    linarith
  have hle' := floor_log_add_three_le_harperN hV1' hxΛ hΛ6'
  have hbge := barrierTop_ge_data hV1' hxΛ hle'
  rw [hlogV'] at hbge
  have hn0 : (0 : ℝ) < ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) := by linarith
  -- the block count is at most `Λ`
  have hnΛ : ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) ≤ Real.log (Real.log x) := by
    have h1 : ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) ≤ ((harperN B x : ℕ) : ℝ) := by
      exact_mod_cast harperBarrierTop_le B (Real.exp 3 * V) x
    have h2 : ((harperN B x : ℕ) : ℝ) ≤ ((⌊Real.log (Real.log x)⌋₊ : ℕ) : ℝ) := by
      have : harperN B x ≤ ⌊Real.log (Real.log x)⌋₊ := by
        rw [harperN]; omega
      exact_mod_cast this
    linarith [Nat.floor_le hΛ0, h1, h2]
  -- the level and the shape parameter
  set a : ℝ := harperLevel (max 1 a₀) ((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) q
    with hadef
  set m : ℝ := min (Real.sqrt (Real.log (Real.log x))) (1 / (1 - q)) with hmdef
  have hd0 : (0 : ℝ) < 1 - q := by linarith
  have hm0 : (0 : ℝ) ≤ m := le_min (Real.sqrt_nonneg _) (by positivity)
  have hmΛ : m ≤ Real.sqrt (Real.log (Real.log x)) := min_le_left _ _
  have hmq : m * (1 - q) ≤ 1 := by
    have h1 : m ≤ 1 / (1 - q) := min_le_right _ _
    rw [le_div_iff₀ hd0] at h1
    linarith
  have ha₀ : max 1 a₀ ≤ a := le_harperLevel _ _ _
  have hκa' : max 1 a₀ ≤ κ * Real.log 2 := hκa
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_left _ _) ha₀
  have ham : a ≤ m + κ * Real.log 2 := by
    rw [hadef, harperLevel]
    refine max_le (le_trans hκa' (by linarith)) ?_
    refine le_trans ?_ (by linarith [mul_nonneg hκ hlog2.le] : m ≤ m + κ * Real.log 2)
    exact min_le_min (Real.sqrt_le_sqrt hnΛ) le_rfl
  -- the composition, at this level
  have hcomp' := hcomp Y ν hY σ a q m x T hx hx1 hx3 hΛ₀ hxΛ hΛcnt hfarwin hσ0 hσhalf hσeq
    hTm hTsub hTfin hT0 (le_trans (le_max_right 1 a₀) ha₀) ha1 hm0 hmΛ hmq ham hq0 hq1 hqΛ
  refine le_trans ?_ hcomp'
  -- and the shape
  have hMW : 1 / (1 + (1 - q) * Real.sqrt (Real.log (Real.log x)))
      ≤ min 1 (a / Real.sqrt (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ))) :=
    one_div_W_le_min_one_div_sqrt hn0 hnΛ hq1
  have hE₁ge : Real.log x / (V * Real.exp ((B : ℝ) + 73))
      ≤ Real.exp (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ) - 64) :=
    log_div_le_exp_barrierTop_sub_rademacher hV hx1 hxΛ hle'
  have hSgeq : (1 / σ) ^ 2 = (Real.log x / (4 * V)) ^ 2 := by
    have : 1 / σ = Real.log x / (4 * V) := by
      rw [eq_div_iff (by linarith), ← hσeq]
      field_simp
    rw [this]
  have hWpos : (0 : ℝ) < 1 + (1 - q) * Real.sqrt (Real.log (Real.log x)) := by
    nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]
  have hminpos : (0 : ℝ)
      < min 1 (a / Real.sqrt (((harperBarrierTop B (Real.exp 3 * V) x : ℕ) : ℝ))) :=
    lt_min one_pos (by positivity)
  have hclog : (1 : ℝ) ≤ Real.exp ((B : ℝ) + 73) := by
    have := Real.add_one_le_exp ((B : ℝ) + 73)
    linarith
  exact pz_shape_le hT0 hα hminpos (Real.exp_pos _) (by positivity) hE (by positivity) hWpos
    hlogx hV0 hclog hq0 hq1 hκ hMW hE₁ge hSgeq hmq ham

end RMF
