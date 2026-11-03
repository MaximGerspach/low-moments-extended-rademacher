/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.Chaining
import RMF.EulerProduct.RademacherJointLaplace

/-!
# The Rademacher chaining: Lemma B.2 at the second-moment tilt

The Rademacher counterpart of `RMF/Probability/Chaining.lean` (Hamdan's Lemma B.2), for the
squarefree Euler product:

* `RMF.IsRademacherRMF.exists_measure_exists_gt_le`:
  `μ{ω | ∃ h ∈ [h₀, h₀+r), V < ℓog‖F_y(σ+ih)‖} ≤ C·exp(AA − 2V)`, `AA = ∑_{p<y} p^{−2σ}`;
* `RMF.IsRademacherRMF.exists_measure_exists_lt_le`: the lower tail, through the reflection
  `X ↦ −X` (`RMF.IsRademacherPrimeValues.neg`).

**The base height is carried, not rotated.**  The Steinhaus chaining reaches `[h₀, h₀+r)` by
rotating the values (`RMF.IsSteinhausPrimeValues.mul_unimodular`).  The Rademacher law is not
invariant under multiplication by a unimodular constant, so every leaf here takes the base height
as a parameter; negation is a symmetry of the law, and gives the lower tail.

**The tail is `exp(AA − 2V)`, not `exp(−V²/AA)`.**  At the tilt `l₁ = 2` the block second moment is
exact, `E‖F_{[y₀,y₁)}(s)‖² = ∏_p (1 + ‖p^{−s}‖²) ≤ exp AA`, so the one-point leaf is Markov with no
constant (`RMF.IsRademacherRMF.measure_ge_le_second_moment`), and the pair coefficient at `l₁ = 2`
does not see `∑_p p^{−2σ}cos(2t ℓog p)`.  The chain term takes `l₁ = 2` where the base bound is
available and `l₁ = 0` where it is not (`RMF.IsRademacherRMF.exists_measure_chain_term_two_le`).

Everything law-free in `RMF/Probability/Chaining.lean` — the net, the level and height sums, the
union bound — is used as it stands.  The file also holds the block second moment of the
squarefree product, its non-vanishing and integrability, and the identification of `ℓog‖F‖` with
the `localLogAdd` walk.
-/

open MeasureTheory

namespace RMF

/-! ### The link leaf

`RMF.IsSteinhausRMF.exists_measure_link_le` sets `l₂ = V₂/(DP)` and gets `+l₁V₂/2 - V₂²/(2DP)`.
For the Rademacher pair bound that choice leaves no decay: its `ℓog p` term is
`(2l₂ + l₁l₂ + l₂²)` where Steinhaus has `(l₁l₂ + l₂²)/2`, so at `l₂ = V₂/(DP)` the `+V₂²/(DP)`
cancels the `-l₂V₂` entirely.  At the halved tilt `l₂ = V₂/(2DP)` the `ℓog p` term contributes
`V₂ + l₁V₂/2 + V₂²/(4DP)` against `-l₂V₂ = -V₂²/(2DP)`, leaving `+l₁V₂/2 + V₂ - V₂²/(4DP)` with no
hypothesis on `V₂` (`RMF.link_exponent_eq`).  The optimal `l₂` would give
`-(V₂ - (2+l₁)DP)²/(4DP)`, at the price of `V₂ ≥ (2+l₁)DP`. -/

/-- At index `0` the general-base pair abscissa is the base height line. -/
lemma pairAbscissaAt_zero_heightLine (σ h₀ h₁ h₂ : ℝ) :
    pairAbscissaAt σ h₀ h₁ h₂ 0 = heightLine σ h₀ := by
  simp [pairAbscissaAt, heightLine]

/-- At index `1` the general-base pair abscissa is the first moving height line. -/
lemma pairAbscissaAt_one_heightLine (σ h₀ h₁ h₂ : ℝ) :
    pairAbscissaAt σ h₀ h₁ h₂ 1 = heightLine σ h₁ := by
  simp [pairAbscissaAt, heightLine]

/-- At index `2` the general-base pair abscissa is the second moving height line. -/
lemma pairAbscissaAt_two_heightLine (σ h₀ h₁ h₂ : ℝ) :
    pairAbscissaAt σ h₀ h₁ h₂ 2 = heightLine σ h₂ := by
  simp [pairAbscissaAt, heightLine]

/-- The halved tilt, as pure arithmetic: at `l₂ = V₂/(2B)` the pair bound's `ℓog p` term less
`l₂V₂` is `V₂ + l₁V₂/2 - V₂²/(4B)`. -/
lemma link_exponent_eq {l₁ V₂ B : ℝ} (hB : B ≠ 0) :
    (2 * (V₂ / (2 * B)) + l₁ * (V₂ / (2 * B)) + (V₂ / (2 * B)) ^ 2) * B
        - V₂ / (2 * B) * V₂
      = V₂ + l₁ * V₂ / 2 - V₂ ^ 2 / (4 * B) := by
  field_simp
  ring

/-- **One link of the chain, Rademacher case, at a general base, for `0 ≤ l₁ ≤ Λ`:**
`μ(E) ≤ exp((l₁²/2 + l₁/2)A - l₁V₁ + l₁V₂/2 + V₂ - V₂²/(4DP) + C)` on every event where the base
walk at height `h₀` is at least `V₁` and the increment between `h₁` and `h₂` is at least `V₂`.
The counterpart of `RMF.IsSteinhausRMF.exists_measure_link_le`, whose base is pinned at `0`; the
base height `h₀` replaces the rotation.  It is used at `l₁ = 0` by
`RMF.IsRademacherRMF.exists_measure_chain_term_two_le`. -/
theorem IsRademacherRMF.exists_measure_link_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 0 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (l₁ σ V₁ V₂ D h₀ h₁ h₂ : ℝ) (y₀ y : ℕ) (E : Set Ω),
        0 ≤ l₁ → l₁ ≤ Λ → σ₀ ≤ σ → |h₁ - h₂| ≤ D → 0 ≤ V₂ → 0 < D →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) →
        V₂ / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
        MeasurableSet E →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖) →
        (∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₁) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₂) ω‖) →
          μ.real E ≤ Real.exp ((l₁ ^ 2 / 2 + l₁ / 2)
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            - l₁ * V₁ + l₁ * V₂ / 2 + V₂
            - V₂ ^ 2 / (4 * (D * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p))
            + C) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsRademacherRMF.exists_measure_le_exp_pair_at (Ω := Ω) (σ₀ := σ₀) (Λ := Λ) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₁ σ V₁ V₂ D h₀ h₁ h₂ y₀ y E hl₁ hl₁Λ hσ hD hV₂ hD0 hP₁ hV₂P hE hE₁ hE₂
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := ⟨_, rfl⟩
  obtain ⟨Pr, hPdef⟩ : ∃ Pr : ℝ,
      Pr = ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := ⟨_, rfl⟩
  rw [← hPdef] at hP₁ hV₂P
  rw [← hAdef, ← hPdef]
  have hB : (0 : ℝ) < D * Pr := by positivity
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂ : ℝ, l₂ = V₂ / (2 * (D * Pr)) := ⟨_, rfl⟩
  have hl₂ : (0 : ℝ) ≤ l₂ := by rw [hl₂def]; positivity
  have hl₂D : l₂ * D = V₂ / (2 * Pr) := by
    rw [hl₂def]
    field_simp
  have hV₂half : V₂ / (2 * Pr) ≤ Λ := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Pr)]
    rw [div_le_iff₀ hP₁] at hV₂P
    linarith
  have hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ := by
    have h1 : l₂ * |h₁ - h₂| ≤ l₂ * D := mul_le_mul_of_nonneg_left hD hl₂
    rw [hl₂D] at h1
    linarith
  have hbr₀ : pairAbscissaAt σ h₀ h₁ h₂ 0 = heightLine σ h₀ :=
    pairAbscissaAt_zero_heightLine σ h₀ h₁ h₂
  have hbr₁ : pairAbscissaAt σ h₀ h₁ h₂ 1 = heightLine σ h₁ :=
    pairAbscissaAt_one_heightLine σ h₀ h₁ h₂
  have hbr₂ : pairAbscissaAt σ h₀ h₁ h₂ 2 = heightLine σ h₂ :=
    pairAbscissaAt_two_heightLine σ h₀ h₁ h₂
  have hE₁' : ∀ ω ∈ E,
      V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 0) ω‖ := by
    intro ω hω
    rw [hbr₀]
    exact hE₁ ω hω
  have hE₂' : ∀ ω ∈ E,
      V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 1) ω‖
        - Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 2) ω‖ := by
    intro ω hω
    rw [hbr₁, hbr₂]
    exact hE₂ ω hω
  have h := hbound f μ hf l₁ l₂ σ h₀ h₁ h₂ V₁ V₂ y₀ y E hl₁ hl₂ hσ hl₁Λ hl₂Λ hE hE₁' hE₂'
  rw [← hAdef, ← hPdef] at h
  refine le_trans h (Real.exp_le_exp.2 ?_)
  have hnn : (0 : ℝ) ≤ 2 * l₂ + l₁ * l₂ + l₂ ^ 2 := by
    have := mul_nonneg hl₁ hl₂
    nlinarith [sq_nonneg l₂]
  have hcross : (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr
      ≤ (2 * l₂ + l₁ * l₂ + l₂ ^ 2) * (D * Pr) := by
    have h1 : |h₁ - h₂| * Pr ≤ D * Pr := mul_le_mul_of_nonneg_right hD hP₁.le
    nlinarith
  have hid := link_exponent_eq (l₁ := l₁) (V₂ := V₂) (B := D * Pr) (ne_of_gt hB)
  rw [← hl₂def] at hid
  linarith

/-! ### Twice the chain weight

The Rademacher link leaves `-V₂²/(4B)` where the Steinhaus one leaves `-V₂²/(2B)`.  The Steinhaus
cross term `+l₁V₂/2` is absorbed by half of its quadratic under `4ΛB ≤ V₂` (`RMF.cross_le_quarter`),
which here would consume the whole decay; `8ΛB ≤ V₂` gives `+l₁V₂/2 ≤ V₂²/(8B)` instead.  By the
computation of `RMF.four_mul_le_chainWeight` that costs `48Λ² ≤ q` in place of `24Λ²`. -/

/-- **Twice the chain weight:** `8ΛB ≤ V₂` from `48Λ² ≤ q`, where `B = (3r/4^{ℓ+1})·P` and
`V₂ = (q/2)(1/4)(3/4)^ℓ`; `RMF.four_mul_le_chainWeight` gives `4ΛB ≤ V₂` from `24Λ² ≤ q`.  With
`Λ ≥ 1` it supplies the `8B ≤ V₂` of `RMF.chain_absorb_three_halves`. -/
lemma eight_mul_le_chainWeight {r P Λ : ℝ} (hr : 0 < r) (hP : 0 < P) (hΛ : 0 < Λ)
    (hrP : r * P ≤ Λ) {q : ℕ} (hq : 48 * Λ ^ 2 ≤ (q : ℝ)) (ℓ : ℕ) :
    8 * Λ * (3 * r / 4 ^ (ℓ + 1) * P) ≤ (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) := by
  have hp4 : (0 : ℝ) < (4 : ℝ) ^ ℓ := by positivity
  have h3l : (1 : ℝ) ≤ (3 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  have hlhs : 8 * Λ * (3 * r / 4 ^ (ℓ + 1) * P) = 6 * Λ * (r * P) / 4 ^ ℓ := by
    rw [pow_succ]
    field_simp
    ring
  have hrhs : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) = (q : ℝ) * 3 ^ ℓ / (8 * 4 ^ ℓ) := by
    rw [div_pow]
    field_simp
    ring
  rw [hlhs, hrhs, div_le_div_iff₀ hp4 (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hrP (by positivity : (0 : ℝ) ≤ 48 * Λ * 4 ^ ℓ),
    mul_le_mul_of_nonneg_left h3l (by positivity : (0 : ℝ) ≤ (q : ℝ) * 4 ^ ℓ),
    mul_le_mul_of_nonneg_right hq hp4.le, mul_nonneg hΛ.le hp4.le]

/-! ### The level bound in eighth form

`RMF.two_mul_le_sq_div_two_mul` gives `2·(1/(192Λ))q²(9/4)^ℓ ≤ V₂²/(2B)`; dividing both sides by
four gives `q²(9/4)^ℓ/(384Λ) ≤ V₂²/(8B)`.  The Steinhaus proof folds `2·(1/(192Λ))` into its `c`
by a rewrite that does not apply at another constant, so the division is a lemma. -/

/-- **The level bound in eighth form:** `q²(9/4)^ℓ/(384Λ) ≤ V₂²/(8B)`, which is
`RMF.two_mul_le_sq_div_two_mul` divided by four.  `RMF.chain_sixteenth_of_two_mul` halves it again
for the second-moment tilt. -/
lemma chain_eighth_of_two_mul {r P Λ : ℝ} (hr : 0 < r) (hP : 0 < P) (hΛ : 0 < Λ)
    (hrP : r * P ≤ Λ) (q ℓ : ℕ) :
    1 / (384 * Λ) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ
      ≤ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (8 * (3 * r / 4 ^ (ℓ + 1) * P)) := by
  have hB : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) * P := by positivity
  have h := two_mul_le_sq_div_two_mul hr hP hΛ hrP q ℓ
  have hsplit : ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (8 * (3 * r / 4 ^ (ℓ + 1) * P))
      = ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (2 * (3 * r / 4 ^ (ℓ + 1) * P)) / 4 := by
    rw [div_div]
    ring_nf
  have hc : 1 / (384 * Λ) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ
      = 2 * (1 / (192 * Λ)) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ / 4 := by
    field_simp
    ring
  rw [hsplit, hc]
  linarith

/-! ### The chain's index gap

The Steinhaus proof has this inline.  Both Rademacher branches take it as a hypothesis and the
union bound supplies it once per `i`; it is arithmetic on `i % 4` and does not involve the law. -/

/-- **Consecutive chain indices are within `3r/4^(ℓ+1)`.**

`i` and `4⌊i/4⌋` differ by `i % 4 ≤ 3`, so the heights they name differ by at most
`3·(r/4^(ℓ+1))`. -/
lemma abs_index_gap_le {r : ℝ} (hr : 0 < r) (i ℓ : ℕ) :
    |(i : ℝ) * (r / 4 ^ (ℓ + 1)) - ((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))|
      ≤ 3 * r / 4 ^ (ℓ + 1) := by
  have hdm : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
  have hcast : (i : ℝ) - ((4 * (i / 4) : ℕ) : ℝ) = ((i % 4 : ℕ) : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hdm
    push_cast at h ⊢
    linarith
  have hmod3 : ((i % 4 : ℕ) : ℝ) ≤ 3 := by
    have h : i % 4 ≤ 3 := by omega
    exact_mod_cast h
  have hr4 : (0 : ℝ) < r / 4 ^ (ℓ + 1) := by positivity
  rw [← sub_mul, hcast, abs_of_nonneg (by positivity),
    show 3 * r / 4 ^ (ℓ + 1) = 3 * (r / 4 ^ (ℓ + 1)) from by ring]
  exact mul_le_mul_of_nonneg_right hmod3 hr4.le

/-! ### The bracket's measurability

A fact about a measurable process and a guarded conjunction, with no law in it; the union bound
and Lemma B.2 both need it. -/

/-- **The chain's bracket is measurable.**

`{ω | (q < Q → V − q − 1 < S 0 ω) ∧ S 0 ω ≤ V − q}` is measurable for a measurable `S`.  The
guard is decided by `q < Q`, which is a proposition about numerals, so the set is either an
intersection of two half-lines or a single one. -/
lemma measurableSet_bracket {Ω : Type*} [MeasurableSpace Ω] {S : ℝ → Ω → ℝ}
    (hSmeas : ∀ t : ℝ, Measurable (S t)) (V : ℝ) (q Q : ℕ) :
    MeasurableSet {ω : Ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)} := by
  by_cases hqQ : q < Q
  · have hrw : {ω : Ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
        = {ω : Ω | V - (q : ℝ) - 1 < S 0 ω} ∩ {ω : Ω | S 0 ω ≤ V - (q : ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun h => ⟨h.1 hqQ, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩
    rw [hrw]
    exact (measurableSet_lt measurable_const (hSmeas 0)).inter
      (measurableSet_le (hSmeas 0) measurable_const)
  · have hrw : {ω : Ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
        = {ω : Ω | S 0 ω ≤ V - (q : ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hqQ, h⟩⟩
    rw [hrw]
    exact measurableSet_le (hSmeas 0) measurable_const

/-! ### The sum over `q`, combining the two slice bounds

The last step of Lemma B.2, as a law-free statement about two families of bounds: split
`Finset.Icc 1 Q` at `q₀`, sum the flat bound below and the chaining bound above, and apply
`RMF.sum_chaining_le`, whose `hT : ∀ q ∈ T, 3 ≤ cq²` uses the same `c` as the summand's decay.
`RMF.IsRademacherRMF.exists_measure_exists_gt_le` applies it at `W = 2V − AA`, `Λ := 1` and
`c = 1/(768Λ)`, with `hT` from `RMF.three_le_chain_threshold_two`.  `Cb` needs no sign
hypothesis; `Cl` does, for the monotonicity step. -/

/-- **The sum over `q` of the two slice bounds.**  Given a flat bound `Cb·exp(−W)` on
`Finset.Ioc 0 q₀` and a chaining bound on `Finset.Ioc q₀ Q`, the sum over `Finset.Icc 1 Q` is at
most `(q₀·Cb + Cl·Csum)·exp(−W)`, where `Csum` is `RMF.sum_chaining_le`'s constant at `c`.  Here
`c` is the decay constant of the summand, `1/(768Λ)` in
`RMF.IsRademacherRMF.exists_measure_exists_gt_le`. -/
lemma sum_slices_le {Q q₀ L : ℕ} {W Λ c Cb Cl : ℝ} {a : ℕ → ℝ}
    (hc : 0 < c) (hq₀Q : q₀ < Q) (hCl : 0 ≤ Cl)
    (hT : ∀ q ∈ Finset.Ioc q₀ Q, 3 ≤ c * (q : ℝ) ^ 2)
    (hsmall : ∀ q ∈ Finset.Ioc 0 q₀, a q ≤ Cb * Real.exp (-W))
    (hbig : ∀ q ∈ Finset.Ioc q₀ Q, a q ≤ Cl * ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1)
        * Real.exp (-W + 2 * Λ * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ)) :
    ∑ q ∈ Finset.Icc 1 Q, a q
      ≤ ((q₀ : ℝ) * Cb + Cl * (8 * Real.exp (2 * Λ)
          * (Real.exp ((2 * Λ) ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹)))
        * Real.exp (-W) := by
  have hIcc : (Finset.Icc 1 Q : Finset ℕ) = Finset.Ioc 0 Q := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le q₀) hq₀Q.le]
  have hsum1 := Finset.sum_le_sum hsmall
  rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at hsum1
  have hsum2 := Finset.sum_le_sum hbig
  rw [← Finset.mul_sum] at hsum2
  have hchain := sum_chaining_le (W := W) (Λ := Λ) (c := c) hc (Finset.Ioc q₀ Q) hT L
  have hfin := mul_le_mul_of_nonneg_left hchain hCl
  nlinarith only [hsum1, hsum2, hfin]

/-! ### The walk, for the squarefree Euler product

`RMF.log_norm_randomEulerProductIco_eq` and `RMF.le_log_norm_randomEulerProductIco` are stated for
`RMF.compMultExtension`, whose local factor is `(1 − Xₐp^{−s})⁻¹`; the Rademacher field is
`RMF.squarefreeExtension`, with local factor `1 + Xₐp^{−s}`, so neither applies.  The bridge from
the product to the sum of logarithms uses `RMF.localLogAdd w z = ℓog‖1 + zw‖`,
`RMF.localLogAdd_eq_neg_localLog` and `RMF.randomEulerProductIco_sqfree_eq`, which needs neither
`0 < Re s` nor a bound on the values.  Unimodularity keeps each factor away from zero, so that the
logarithm splits: `‖1 + Xₐw‖ > 0` is `RMF.norm_one_sub_mul_pos` at `−w`.  The lower bound is
`ℓog(1 − p^{−σ})`, from `‖1 + Xₐw‖ ≥ 1 − ‖w‖`; its value never reaches the exponent, since the
branch of Lemma B.2 that uses it has tilt zero. -/

/-- **The walk is the logarithm of the squarefree Euler product**, at every `ω` whose values are
unimodular.

`ℓog‖F_y(s)‖ = ∑_{p<y} localLogAdd(p^{−s}, Xₐ)`, the additive counterpart of
`RMF.log_norm_randomEulerProductIco_eq`. -/
lemma log_norm_randomEulerProductIco_sqfree_eq {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y s ω‖
      = ∑ p ∈ primesIco y₀ y, localLogAdd ((p : ℂ) ^ (-s)) (X p ω) := by
  have hne : ∀ p ∈ primesIco y₀ y, ‖1 + X p ω * (p : ℂ) ^ (-s)‖ ≠ 0 := by
    intro p hp
    have hw : ‖-((p : ℂ) ^ (-s))‖ < 1 := by
      rw [norm_neg]
      exact norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    have hpos := norm_one_sub_mul_pos (hω p hp) hw
    rw [mul_neg, sub_neg_eq_add] at hpos
    exact ne_of_gt hpos
  rw [randomEulerProductIco_sqfree_eq, norm_prod, Real.log_prod hne]
  rfl

/-- **A crude lower bound on the squarefree walk:** `∑_{p<y} ℓog(1 − p^{−σ}) ≤ ℓog‖F_y(s)‖` at
every `ω` whose values are unimodular, the logarithm of `RMF.le_norm_randomEulerProductIco_sqfree`.
The counterpart of `RMF.le_log_norm_randomEulerProductIco`, which bounds the multiplicative factor
by `1 + ‖w‖` instead.  Its consumer is the branch of Lemma B.2 where the base bound is unavailable;
that branch has tilt zero, so the value never reaches the exponent. -/
lemma le_log_norm_randomEulerProductIco_sqfree {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω}
    (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    ∑ p ∈ primesIco y₀ y, Real.log (1 - ((p : ℕ) : ℝ) ^ (-s.re))
      ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          y₀ y s ω‖ := by
  have hw : ∀ p ∈ primesIco y₀ y,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
    intro p hp
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos, Complex.neg_re]
  have hfac : ∀ p ∈ primesIco y₀ y, (0 : ℝ) < 1 - ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
    intro p hp
    have := norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
    linarith
  have hprod : (0 : ℝ) < ∏ p ∈ primesIco y₀ y, (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖) :=
    Finset.prod_pos hfac
  have hsum : ∑ p ∈ primesIco y₀ y, Real.log (1 - ((p : ℕ) : ℝ) ^ (-s.re))
      = Real.log (∏ p ∈ primesIco y₀ y, (1 - ‖((p : ℕ) : ℂ) ^ (-s)‖)) := by
    rw [Real.log_prod fun p hp => ne_of_gt (hfac p hp)]
    exact (Finset.sum_congr rfl fun p hp => by rw [hw p hp]).symm
  rw [hsum]
  exact Real.log_le_log hprod (le_norm_randomEulerProductIco_sqfree y₀ y hs hω)

/-! ### The block second moment, exactly

The Rademacher pair coefficient `l₁²/4 + (l₁²/4 − l₁/2)·c`, `c = (∑_p p^{−2σ}cos(2tℓog p))/A`,
loses its `c`-term at `l₁ = 2`, since `l₁²/4 − l₁/2 = 0` there; bounding it by `l₁²/2 + l₁/2`
adds the two worst cases where only their maximum holds.  At that tilt the moment is exact:
`∫‖1 + zw‖² = 1 + ‖w‖²` because the Rademacher law is centred
(`RMF.integral_norm_one_add_mul_sq_rademacherLaw`), with no prime number theorem, truncation or
constant.  The `primesBelow` version is `RMF.IsRademacherRMF.integral_norm_randomEulerProduct_sq`;
the block version below is the squarefree sibling of
`RMF.integral_norm_randomEulerProductIco_sq_compMult`, with two hypotheses fewer, since
`RMF.randomEulerProductIco_sqfree_eq` is pointwise and unconditional. -/

/-- **The block second moment of the squarefree Euler product**, for any i.i.d. prime values.

`E‖F_{[y₀,y₁)}(s)‖² = ∏_p E‖1 + z·p^{−s}‖²`.  The squarefree sibling of
`RMF.integral_norm_randomEulerProductIco_sq_compMult`, and **unconditional in `s`**: the
factorisation `RMF.randomEulerProductIco_sqfree_eq` holds pointwise at every `ω` with no
hypothesis, where the multiplicative one needs `0 < Re s` and unimodularity almost surely. -/
theorem integral_norm_randomEulerProductIco_sq_sqfree {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℂ} {ν : Measure ℂ} {μ : Measure Ω} (hX : IsIIDPrimeValues X ν μ)
    (y₀ y₁ : ℕ) (s : ℂ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ 2 ∂ν := by
  have hpt : ∀ ω : Ω,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω‖ ^ 2
        = ∏ p ∈ primesIco y₀ y₁, ‖1 + X p ω * (p : ℂ) ^ (-s)‖ ^ 2 := by
    intro ω
    rw [randomEulerProductIco_sqfree_eq, norm_prod, ← Finset.prod_pow]
  simp_rw [hpt]
  exact hX.integral_prod (fun _ hp => prime_of_mem_primesIco hp)
    (fun p z => ‖1 + z * (p : ℂ) ^ (-s)‖ ^ 2) fun _ _ => by fun_prop

/-- **The block second moment of the Rademacher Euler product**, exactly.

`E‖F_{[y₀,y₁)}(s)‖² = ∏_p (1 + ‖p^{−s}‖²)`, with no hypothesis on `s` at all.  Each factor is
`RMF.integral_norm_one_add_mul_sq_rademacherLaw`, which is the parallelogram law: `EX = 0`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_sq {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ)
    (s : ℂ) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ)
      = ∏ p ∈ primesIco y₀ y₁, (1 + ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  rw [integral_norm_randomEulerProductIco_sq_sqfree hX y₀ y₁ s]
  exact Finset.prod_congr rfl fun p _ => integral_norm_one_add_mul_sq_rademacherLaw _

/-- **The block second moment, in the form the chaining consumes:**
`E‖F_{[y₀,y₁)}(s)‖² ≤ exp(∑_p p^{−2σ})`, from `1 + x ≤ e^x` on each factor.  The right side is
`exp AA` for the `AA` of the chaining, so Markov at tilt `2` reads `exp(AA − 2V)`. -/
theorem IsRademacherRMF.integral_norm_randomEulerProductIco_sq_le {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ) (s : ℂ) :
    (∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ)
      ≤ Real.exp (∑ p ∈ primesIco y₀ y₁, ((p : ℕ) : ℝ) ^ (-2 * s.re)) := by
  have hnorm : ∀ p ∈ primesIco y₀ y₁,
      ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 = ((p : ℕ) : ℝ) ^ (-2 * s.re) := by
    intro p hp
    rw [Complex.norm_natCast_cpow_of_pos (prime_of_mem_primesIco hp).pos, Complex.neg_re,
      ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ((p : ℕ) : ℝ))]
    congr 1
    push_cast
    ring
  rw [hf.integral_norm_randomEulerProductIco_sq y₀ y₁ s, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  rw [hnorm p hp]
  linarith [Real.add_one_le_exp (((p : ℕ) : ℝ) ^ (-2 * s.re))]

/-- **The squarefree Euler product does not vanish on the unimodularity set:**
`0 < ‖F_{[y₀,y)}(s)‖` whenever `Re s > 0` and every value is unimodular, since each factor has
`‖1 + Xₐw‖ ≥ 1 − ‖w‖ > 0`.  This turns `V ≤ ℓog‖F‖` into `e^{2V} ≤ ‖F‖²`; without it the Lean
convention `ℓog 0 = 0` would put the vanishing points into the event. -/
lemma norm_randomEulerProductIco_sqfree_pos {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ} {s : ℂ}
    (hs : 0 < s.re) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    0 < ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y s ω‖ := by
  rw [randomEulerProductIco_sqfree_eq, norm_prod]
  refine Finset.prod_pos fun p hp => ?_
  have hw : ‖-((p : ℂ) ^ (-s))‖ < 1 := by
    rw [norm_neg]
    exact norm_prime_cpow_neg_lt_one (prime_of_mem_primesIco hp) hs
  have hpos := norm_one_sub_mul_pos (hω p hp) hw
  rwa [mul_neg, sub_neg_eq_add] at hpos

/-! ### The block weight is integrable, and the base leaf that follows

`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq` evaluates the block second moment;
Markov also needs the integrand to be integrable.  The Steinhaus counterpart needs `0 < Re s`,
because its bound `∏(1 − ‖p^{−s}‖)⁻¹` is finite only there; the Rademacher bound `∏(1 + ‖p^{−s}‖)`
is finite for every `s`, as in `RMF.IsRademacherRMF.integrable_norm_randomEulerProduct_sq`.

The base leaf is then Markov at tilt `2`: `μ(E) ≤ exp(AA − 2V)`, with no constant and no tilt
range. -/

/-- **The block weight is integrable**, with no hypothesis on `s`.

The `Ico` sibling of `RMF.IsRademacherRMF.integrable_norm_randomEulerProduct_sq`.  The bound is
`(∏_p (1 + ‖p^{−s}‖))²`, which is finite for every `s` — the Steinhaus version's
`∏(1 − ‖p^{−s}‖)⁻¹` is not, which is why that one carries `0 < Re s` and this one does not. -/
theorem IsRademacherRMF.integrable_norm_randomEulerProductIco_sq {Ω : Type*}
    [MeasurableSpace Ω] {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω}
    (hf : IsRademacherRMF f μ) (y₀ y₁ : ℕ) (s : ℂ) :
    Integrable (fun ω => ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2) μ := by
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hpt : ∀ ω,
      randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y₁ s ω
        = ∏ p ∈ primesIco y₀ y₁, (1 + X p ω * ((p : ℕ) : ℂ) ^ (-s)) :=
    fun ω => randomEulerProductIco_sqfree_eq y₀ y₁ s ω
  have hmeas : AEStronglyMeasurable
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        y₀ y₁ s ω‖ ^ 2) μ := by
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hpt]
    refine ((Finset.measurable_prod _ fun p hp => ?_).norm).pow_const 2
    exact ((hX.measurable p (prime_of_mem_primesIco hp)).mul_const _).const_add 1
  refine (memLp_top_of_bound hmeas
    ((∏ p ∈ primesIco y₀ y₁, (1 + ‖((p : ℕ) : ℂ) ^ (-s)‖)) ^ 2) ?_).integrable le_top
  filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y₁] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [hpt ω, norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, norm_mul]
  have := mul_le_of_le_one_left (norm_nonneg (((p : ℕ) : ℂ) ^ (-s))) (hω p hp)
  linarith

/-- **The one-point upper tail at the second-moment tilt:** `μ(E) ≤ exp(AA − 2V)` on any event
where `ℓog‖F_{[y₀,y)}(s)‖ ≥ V` and the product does not vanish.  No `∃ C` and no tilt range: at
tilt `2` the moment is exact.  `hEpos` is discharged by
`RMF.norm_randomEulerProductIco_sqfree_pos` on the unimodularity set. -/
theorem IsRademacherRMF.measure_ge_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    {V : ℝ} {s : ℂ} {y₀ y₁ : ℕ} {E : Set Ω} (hE : MeasurableSet E)
    (hEpos : ∀ ω ∈ E, 0 < ‖randomEulerProductIco f y₀ y₁ s ω‖)
    (hEV : ∀ ω ∈ E, V ≤ Real.log ‖randomEulerProductIco f y₀ y₁ s ω‖) :
    μ.real E
      ≤ Real.exp ((∑ p ∈ primesIco y₀ y₁, ((p : ℕ) : ℝ) ^ (-2 * s.re)) - 2 * V) := by
  have hprob : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hint := hf.integrable_norm_randomEulerProductIco_sq y₀ y₁ s
  have hsq : Real.exp (2 * V) = Real.exp V ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hge : ∀ ω ∈ E,
      Real.exp (2 * V) ≤ ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 := by
    intro ω hω
    rw [hsq]
    refine pow_le_pow_left₀ (Real.exp_pos V).le ?_ 2
    calc Real.exp V ≤ Real.exp (Real.log ‖randomEulerProductIco f y₀ y₁ s ω‖) :=
          Real.exp_le_exp.2 (hEV ω hω)
      _ = ‖randomEulerProductIco f y₀ y₁ s ω‖ := Real.exp_log (hEpos ω hω)
  have h1 : μ.real E * Real.exp (2 * V)
      ≤ ∫ ω in E, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ := by
    rw [← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hE hge
  have h2 : (∫ ω in E, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ)
      ≤ ∫ ω, ‖randomEulerProductIco f y₀ y₁ s ω‖ ^ 2 ∂μ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => by positivity)
  have h3 := hf.integral_norm_randomEulerProductIco_sq_le y₀ y₁ s
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  linarith

/-! ### The pair coefficient at the second-moment tilt

`RMF.pair_trig_at_le` bounds `2(Ac₀ + Bd)² − (A(2c₀²−1) + BE)` by `2A² + A + (4B + 4AB + 4B²)T`.
At `A = 1` the `c₀²` terms cancel exactly,

    2(c₀ + Bd)² − ((2c₀² − 1) + BE)  =  1 + 4Bc₀d + 2B²d² − BE,

and the base height survives only in `4Bc₀d`, which carries `d ≤ T = |h₁−h₂|·ℓog p`: the constant
drops from `3` to `1` and the linear coefficient from `8B + 4B²` to `6B + 4B²`.  The ladder above
is generic in the coefficient (`RMF.exists_pair_prime_sum_bound_at_rademacherLaw` carries the main
term symbolically), so replacing `RMF.sum_pair_main_term_pairAbscissaAt_le` re-derives the joint
moment.  The bound stays linear in `T`, as the first-power sum `∑_p p^{−2σ}ℓog p` of the chaining
requires.  Their siblings are in `EulerProduct/RademacherJointLaplace.lean`. -/

/-- **The pair trigonometric bound at the second-moment tilt:**
`2(c₀ + Bd)² − ((2c₀² − 1) + BE) ≤ 1 + (6B + 4B²)T`.  `RMF.pair_trig_at_le` at `A = 1`, where the
`c₀²` terms cancel and `2A² + A` collapses from `3` to `1`; the surviving base-height term `4Bc₀d`
is bounded by `4BT`.  `0 ≤ T` is not assumed, being implied by `|d| ≤ T`. -/
lemma pair_trig_at_one_le {B c₀ d E T : ℝ} (hB : 0 ≤ B) (hc₀ : |c₀| ≤ 1)
    (hd2 : |d| ≤ 2) (hdT : |d| ≤ T) (hE : |E| ≤ 2 * T) :
    2 * (c₀ + B * d) ^ 2 - ((2 * c₀ ^ 2 - 1) + B * E)
      ≤ 1 + (6 * B + 4 * B ^ 2) * T := by
  have hcd : c₀ * d ≤ T := by
    refine le_trans (le_abs_self _) ?_
    rw [abs_mul]
    calc |c₀| * |d| ≤ 1 * T := mul_le_mul hc₀ hdT (abs_nonneg _) zero_le_one
      _ = T := one_mul T
  have hdd : d ^ 2 ≤ 2 * T := by
    have h := mul_le_mul hd2 hdT (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg d)] at h
    exact h
  have hnegE : -E ≤ 2 * T := by linarith [(abs_le.1 hE).1]
  nlinarith [mul_le_mul_of_nonneg_left hcd hB,
    mul_le_mul_of_nonneg_left hdd (sq_nonneg B),
    mul_le_mul_of_nonneg_left hnegE hB]

/-- **The main term at a general base and the second-moment tilt, one prime:**
`main(p) ≤ p^{−2σ} + (3l₂ + l₂²)|h₁ − h₂|·p^{−2σ}ℓog p`, against
`RMF.pair_main_term_pairAbscissaAt_le`'s `3p^{−2σ} + (4l₂ + l₂²)…` at `l₁ = 2`.  The first
coefficient is the `AA` in `exp(AA − 2V)`. -/
lemma pair_main_term_pairAbscissaAt_two_le {p : ℕ} (hp : p.Prime) {l₂ σ h₀ h₁ h₂ : ℝ}
    (hl₂ : 0 ≤ l₂) :
    ((∑ a, pairWeight 2 l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
        - 2 * (∑ a, pairWeight 2 l₂ a
            * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
        + 2 * (∑ a, pairWeight 2 l₂ a
            * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2)
      ≤ (p : ℝ) ^ (-2 * σ)
        + (3 * l₂ + l₂ ^ 2) * |h₁ - h₂| * ((p : ℝ) ^ (-2 * σ) * Real.log p) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hpR : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one hp1
  have hlog0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hpow : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg hpR.le _
  have hT : (0 : ℝ) ≤ |h₁ - h₂| * Real.log (p : ℝ) := mul_nonneg (abs_nonneg _) hlog0
  have hd2 : |Real.cos (h₁ * Real.log (p : ℝ)) - Real.cos (h₂ * Real.log (p : ℝ))| ≤ 2 :=
    le_trans (abs_sub _ _) (by
      linarith [Real.abs_cos_le_one (h₁ * Real.log (p : ℝ)),
        Real.abs_cos_le_one (h₂ * Real.log (p : ℝ))])
  have hdT : |Real.cos (h₁ * Real.log (p : ℝ)) - Real.cos (h₂ * Real.log (p : ℝ))|
      ≤ |h₁ - h₂| * Real.log (p : ℝ) := by
    refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
    rw [show h₁ * Real.log (p : ℝ) - h₂ * Real.log (p : ℝ) = (h₁ - h₂) * Real.log (p : ℝ) by
      ring, abs_mul, abs_of_nonneg hlog0]
  have hE : |Real.cos (2 * (h₁ * Real.log (p : ℝ))) - Real.cos (2 * (h₂ * Real.log (p : ℝ)))|
      ≤ 2 * (|h₁ - h₂| * Real.log (p : ℝ)) := by
    refine le_trans (Real.abs_cos_sub_cos_le _ _) ?_
    rw [show 2 * (h₁ * Real.log (p : ℝ)) - 2 * (h₂ * Real.log (p : ℝ))
        = (h₁ - h₂) * (2 * Real.log (p : ℝ)) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.log (p : ℝ))]
    exact le_of_eq (by ring)
  rw [pair_local_poly_eq_at hp 2 l₂ σ h₀ h₁ h₂, Real.cos_two_mul (h₀ * Real.log (p : ℝ))]
  have hkey := pair_trig_at_one_le (B := l₂ / 2)
    (c₀ := Real.cos (h₀ * Real.log (p : ℝ)))
    (d := Real.cos (h₁ * Real.log (p : ℝ)) - Real.cos (h₂ * Real.log (p : ℝ)))
    (E := Real.cos (2 * (h₁ * Real.log (p : ℝ))) - Real.cos (2 * (h₂ * Real.log (p : ℝ))))
    (T := |h₁ - h₂| * Real.log (p : ℝ)) (by linarith)
    (Real.abs_cos_le_one _) hd2 hdT hE
  nlinarith [mul_le_mul_of_nonneg_left hkey hpow, hT]

/-- **The main-term bound at the second-moment tilt, summed over a block:**
`∑_p main(p) ≤ ∑_p p^{−2σ} + (3l₂ + l₂²)|h₁ − h₂| ∑_p p^{−2σ}ℓog p`, uniformly in the base `h₀`.
The first coefficient is `1`, which is what makes `exp(AA − 2V)` reachable. -/
theorem sum_pair_main_term_pairAbscissaAt_two_le {l₂ σ h₀ h₁ h₂ : ℝ} (hl₂ : 0 ≤ l₂)
    (y₀ y : ℕ) :
    (∑ p ∈ primesIco y₀ y,
        ((∑ a, pairWeight 2 l₂ a * ‖(p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)‖ ^ 2)
          - 2 * (∑ a, pairWeight 2 l₂ a
              * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re ^ 2)
          + 2 * (∑ a, pairWeight 2 l₂ a
              * ((p : ℂ) ^ (-pairAbscissaAt σ h₀ h₁ h₂ a)).re) ^ 2))
      ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
        + (3 * l₂ + l₂ ^ 2) * |h₁ - h₂|
          * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) := by
  refine le_trans (Finset.sum_le_sum fun p hp =>
    pair_main_term_pairAbscissaAt_two_le (prime_of_mem_primesIco hp) hl₂) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **The pair joint moment at a general base and the second-moment tilt:**
`ℓog E ∏ₐ ‖F(wₐ)‖^{2qₐ} ≤ ∑_p p^{−2σ} + (3l₂ + l₂²)|h₁−h₂| ∑_p p^{−2σ}ℓog p + C`.  The
counterpart of `RMF.IsRademacherRMF.exists_log_joint_moment_pair_le_at`, which at `l₁ = 2` gives
`3∑_p p^{−2σ} + (4l₂ + l₂²)… + C`; the coefficient enters only through the summed bound. -/
theorem IsRademacherRMF.exists_log_joint_moment_pair_le_at_two {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 2 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (l₂ σ h₀ h₁ h₂ : ℝ) (y₀ y : ℕ), 0 ≤ l₂ → σ₀ ≤ σ → l₂ * |h₁ - h₂| ≤ Λ →
          Real.log (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
                ^ (2 * pairWeight 2 l₂ a) ∂μ)
            ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
              + (3 * l₂ + l₂ ^ 2) * |h₁ - h₂|
                * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
              + C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pair_prime_sum_bound_at_rademacherLaw (σ₀ := σ₀) (Λ := Λ) hσ₀ (by linarith)
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₂ σ h₀ h₁ h₂ y₀ y hl₂ hσ hl₂Λ
  rw [hf.integral_prod_norm_randomEulerProductIco_rpow_pair_at y₀ y 2 l₂ σ h₀ h₁ h₂
    (by linarith)]
  have h1 := abs_le.1 (hbound 2 l₂ σ h₀ h₁ h₂ y₀ y (by norm_num) hl₂ hσ hΛ hl₂Λ)
  have h2 := sum_pair_main_term_pairAbscissaAt_two_le (l₂ := l₂) (σ := σ)
    (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) hl₂ y₀ y
  linarith [h1.2]

/-! ### The Chernoff wrapper and the link leaf at the second-moment tilt

`RMF.IsRademacherRMF.exists_measure_le_exp_pair_at` turns the joint moment into a tail bound, and
the coefficient enters its proof only where it applies
`RMF.IsRademacherRMF.exists_log_joint_moment_pair_le_at`; the `l₁ = 2` version swaps that step.

With the coefficient `3l₂ + l₂²` and `G = |h₁−h₂|·PP ≤ B = D·PP`, the `l₂`-part of the exponent is
`3l₂G + l₂²G − l₂V₂`, increasing in `G`; its optimum `l₂* = (V₂ − 3B)/(2B)` gives
`−(V₂ − 3B)²/(4B)`.  The link leaf takes `l₂ = V₂/(2B)`, which loses `9B/4` against it and keeps
the decay `−V₂²/(4B)`.  Compared with `l₁ = 2` in the general bound, the link exponent goes from
`3·AA − 2V₁ + 2V₂ − V₂²/(4B) + C` to `AA − 2V₁ + 3V₂/2 − V₂²/(4B) + C`. -/

/-- **Lemma B.1's Chernoff wrapper at a general base and the second-moment tilt.**

The counterpart of `RMF.IsRademacherRMF.exists_measure_le_exp_pair_at` at `l₁ = 2`, with the
coefficient `AA` in place of `3·AA` and `3l₂ + l₂²` in place of `4l₂ + l₂²`.  Everything but the
joint-moment step is generic in the coefficient, so this is that proof with one `obtain`
swapped. -/
theorem IsRademacherRMF.exists_measure_le_exp_pair_at_two {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 2 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (l₂ σ h₀ h₁ h₂ V₁ V₂ : ℝ) (y₀ y : ℕ) (E : Set Ω),
        0 ≤ l₂ → σ₀ ≤ σ → l₂ * |h₁ - h₂| ≤ Λ → MeasurableSet E →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 0) ω‖) →
        (∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 1) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ 2) ω‖) →
          μ.real E ≤ Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            + (3 * l₂ + l₂ ^ 2) * |h₁ - h₂|
              * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
            + C - (2 * V₁ + l₂ * V₂)) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsRademacherRMF.exists_log_joint_moment_pair_le_at_two (Ω := Ω) (σ₀ := σ₀) (Λ := Λ) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf l₂ σ h₀ h₁ h₂ V₁ V₂ y₀ y E hl₂ hσ hl₂Λ hE hE₁ hE₂
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hre : ∀ a ∈ (Finset.univ : Finset (Fin 3)), 0 < (pairAbscissaAt σ h₀ h₁ h₂ a).re := by
    intro a _
    rw [pairAbscissaAt_re]
    linarith
  have hq : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      |pairWeight 2 l₂ a| ≤ 2 / 2 + l₂ / 2 := fun a _ => abs_pairWeight_le (by norm_num) hl₂ a
  have hint := hf.integrable_prod_norm_rpow Finset.univ (pairWeight 2 l₂)
    (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hq (by linarith) hre
  have hIpos := hf.integral_prod_norm_pair_pos_at hσ₀ 2 l₂ σ h₀ h₁ h₂ y₀ y hσ
  have hW : ∀ ω ∈ E, 2 * V₁ + l₂ * V₂
      ≤ ∑ a, 2 * pairWeight 2 l₂ a
        * Real.log ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖ := by
    intro ω hω
    rw [sum_two_mul_pairWeight_mul]
    have hA := mul_le_mul_of_nonneg_left (hE₁ ω hω) (by norm_num : (0 : ℝ) ≤ 2)
    have hB := mul_le_mul_of_nonneg_left (hE₂ ω hω) hl₂
    linarith
  have hge : ∀ᵐ ω ∂(μ.restrict E), Real.exp (2 * V₁ + l₂ * V₂)
      ≤ ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight 2 l₂ a) := by
    filter_upwards [ae_restrict_of_ae (hf.prod_norm_rpow_ae_eq Finset.univ
      (pairWeight 2 l₂) (pairAbscissaAt σ h₀ h₁ h₂) y₀ y hre), ae_restrict_mem hE] with ω h1 h2
    rw [h1]
    exact Real.exp_le_exp.2 (hW ω h2)
  have h1 : μ.real E * Real.exp (2 * V₁ + l₂ * V₂)
      ≤ ∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight 2 l₂ a)) ∂μ := by
    have hc : (∫ _ω in E, Real.exp (2 * V₁ + l₂ * V₂) ∂μ)
        = μ.real E * Real.exp (2 * V₁ + l₂ * V₂) := by
      rw [setIntegral_const, smul_eq_mul]
    rw [← hc]
    exact integral_mono_ae (integrableOn_const (by simp [measure_ne_top]))
      hint.integrableOn hge
  have h2 : (∫ ω in E, (∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight 2 l₂ a)) ∂μ)
      ≤ ∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
          ^ (2 * pairWeight 2 l₂ a) ∂μ := by
    refine setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => ?_)
    exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) _
  have h3 : (∫ ω, ∏ a, ‖randomEulerProductIco f y₀ y (pairAbscissaAt σ h₀ h₁ h₂ a) ω‖
        ^ (2 * pairWeight 2 l₂ a) ∂μ)
      ≤ Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
        + (3 * l₂ + l₂ ^ 2) * |h₁ - h₂|
          * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) + C) := by
    have h := hbound f μ hf l₂ σ h₀ h₁ h₂ y₀ y hl₂ hσ hl₂Λ
    have h4 := Real.exp_le_exp.2 h
    rwa [Real.exp_log hIpos] at h4
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  linarith

/-- **The link exponent at the second-moment tilt**, at `l₂ = V₂/(2B)`.

`(3l₂ + l₂²)B − l₂V₂ = 3V₂/2 − V₂²/(4B)`.  The counterpart of `RMF.link_exponent_eq`, whose
`2l₂ + l₁l₂ + l₂²` gives `V₂ + l₁V₂/2 − V₂²/(4B)` and hence `2V₂ − V₂²/(4B)` at `l₁ = 2`. -/
lemma link_exponent_two_eq {V₂ B : ℝ} (hB : B ≠ 0) :
    (3 * (V₂ / (2 * B)) + (V₂ / (2 * B)) ^ 2) * B - V₂ / (2 * B) * V₂
      = 3 * V₂ / 2 - V₂ ^ 2 / (4 * B) := by
  field_simp
  ring

/-- **One link of the chain at the second-moment tilt:**
`μ(E) ≤ exp(AA − 2V₁ + 3V₂/2 − V₂²/(4DP) + C)`, against
`RMF.IsRademacherRMF.exists_measure_link_le`'s `3AA − 2V₁ + 2V₂ − V₂²/(4DP)` at `l₁ = 2`.  The
`AA` coefficient is `1`, which is what the barrier needs; the decay `−V₂²/(4DP)` is unchanged. -/
theorem IsRademacherRMF.exists_measure_link_le_two {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 2 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ V₁ V₂ D h₀ h₁ h₂ : ℝ) (y₀ y : ℕ) (E : Set Ω),
        σ₀ ≤ σ → |h₁ - h₂| ≤ D → 0 ≤ V₂ → 0 < D →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) →
        V₂ / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
        MeasurableSet E →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖) →
        (∀ ω ∈ E, V₂ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₁) ω‖
            - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₂) ω‖) →
          μ.real E ≤ Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            - 2 * V₁ + 3 * V₂ / 2
            - V₂ ^ 2 / (4 * (D * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p))
            + C) := by
  obtain ⟨C, hC, hbound⟩ :=
    IsRademacherRMF.exists_measure_le_exp_pair_at_two (Ω := Ω) (σ₀ := σ₀) (Λ := Λ) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf σ V₁ V₂ D h₀ h₁ h₂ y₀ y E hσ hD hV₂ hD0 hP₁ hV₂P hE hE₁ hE₂
  set Pr := ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p with hPdef
  have hB : (0 : ℝ) < D * Pr := by positivity
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂ : ℝ, l₂ = V₂ / (2 * (D * Pr)) := ⟨_, rfl⟩
  have hl₂ : (0 : ℝ) ≤ l₂ := by rw [hl₂def]; positivity
  have hl₂D : l₂ * D = V₂ / (2 * Pr) := by
    rw [hl₂def]
    field_simp
  have hV₂half : V₂ / (2 * Pr) ≤ Λ := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Pr)]
    rw [div_le_iff₀ hP₁] at hV₂P
    linarith
  have hl₂Λ : l₂ * |h₁ - h₂| ≤ Λ := by
    have h := mul_le_mul_of_nonneg_left hD hl₂
    rw [hl₂D] at h
    linarith
  have h := hbound f μ hf l₂ σ h₀ h₁ h₂ V₁ V₂ y₀ y E hl₂ hσ hl₂Λ hE
    (fun ω hω => by rw [pairAbscissaAt_zero_heightLine]; exact hE₁ ω hω)
    (fun ω hω => by
      rw [pairAbscissaAt_one_heightLine, pairAbscissaAt_two_heightLine]
      exact hE₂ ω hω)
  refine le_trans h (Real.exp_le_exp.2 ?_)
  have hcoef : (3 * l₂ + l₂ ^ 2) * (D * Pr) - l₂ * V₂
      = 3 * V₂ / 2 - V₂ ^ 2 / (4 * (D * Pr)) := by
    rw [hl₂def]
    exact link_exponent_two_eq (ne_of_gt hB)
  have hmono : (3 * l₂ + l₂ ^ 2) * |h₁ - h₂| * Pr ≤ (3 * l₂ + l₂ ^ 2) * (D * Pr) := by
    have hc0 : (0 : ℝ) ≤ 3 * l₂ + l₂ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hD (le_of_lt hP₁)
    nlinarith [mul_le_mul_of_nonneg_left this hc0]
  linarith

/-! ### The chain term's absorption at the second-moment tilt

At `l₁ = 2` the base bound enters the exponent as `−2V₁`.  Where the base bound is unavailable,
Lemma B.2 manufactures `V₁ = ∑_p ℓog(1 − p^{−σ})` (`RMF.le_log_norm_randomEulerProductIco_sqfree`),
with `|V₁| ≈ ∑_p p^{−σ}` far above `AA`, so that branch uses `l₁ = 0`, where
`RMF.IsRademacherRMF.exists_measure_link_le` has no `AA` term and no `V₁`.  Both branches then need
exactly `V₂ ≥ 8B`:

    positive (l₁ = 2):   3V₂/2 − V₂²/(4B) ≤ −V₂²/(16B)   ↔   V₂ ≥ 8B
    negative (l₁ = 0):     V₂  − V₂²/(4B) ≤ −V₂²/(16B)   ←   V₂ ≥ 8B

and `RMF.eight_mul_le_chainWeight` supplies `8ΛB ≤ V₂` with `Λ ≥ 1`.  The decay constant is
`c = 1/(768Λ)`, and `RMF.sum_chaining_le`'s `3 ≤ cq²` needs `q² ≥ 2304Λ`. -/

/-- **The positive branch's absorption.**  `3V₂/2 − V₂²/(4B) ≤ −V₂²/(16B)` once `8B ≤ V₂`.

The linear cost of the increment is paid by three quarters of the quadratic, leaving a sixteenth
for the chain's decay.  **Tight at `V₂ = 8B`**, where both sides are `−4B`. -/
lemma chain_absorb_three_halves {V₂ B : ℝ} (hB : 0 < B) (hV₂ : 8 * B ≤ V₂) :
    3 * V₂ / 2 - V₂ ^ 2 / (4 * B) ≤ -(V₂ ^ 2 / (16 * B)) := by
  have hV₂0 : (0 : ℝ) ≤ V₂ := by linarith
  have hsplit : V₂ ^ 2 / (4 * B) - V₂ ^ 2 / (16 * B) = 3 * V₂ ^ 2 / (16 * B) := by
    field_simp
    ring
  have hlin : 3 * V₂ / 2 ≤ 3 * V₂ ^ 2 / (16 * B) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * B)]
    nlinarith [mul_le_mul_of_nonneg_right hV₂ hV₂0]
  linarith

/-- **The zero-tilt branch's absorption.**  `V₂ − V₂²/(4B) ≤ −V₂²/(16B)` once `8B ≤ V₂`.

The same statement with the smaller linear cost the `l₁ = 0` branch pays; it is slack here, and
the sixteenth is kept so both branches feed the same decay comparison. -/
lemma chain_absorb_one {V₂ B : ℝ} (hB : 0 < B) (hV₂ : 8 * B ≤ V₂) :
    V₂ - V₂ ^ 2 / (4 * B) ≤ -(V₂ ^ 2 / (16 * B)) := by
  have h := chain_absorb_three_halves hB hV₂
  have hV₂0 : (0 : ℝ) ≤ V₂ := by linarith
  linarith

/-- **The level bound at the halved decay constant.**

`RMF.chain_eighth_of_two_mul` at `c = 1/(384Λ)` gives `V₂²/(8B)`; halving both sides gives
`c = 1/(768Λ)` against `V₂²/(16B)`, which is what the positive branch leaves. -/
lemma chain_sixteenth_of_two_mul {r P Λ : ℝ} (hr : 0 < r) (hP : 0 < P) (hΛ : 0 < Λ)
    (hrP : r * P ≤ Λ) (q ℓ : ℕ) :
    1 / (768 * Λ) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ
      ≤ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (16 * (3 * r / 4 ^ (ℓ + 1) * P)) := by
  have h := chain_eighth_of_two_mul hr hP hΛ hrP q ℓ
  have hB : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) * P := by positivity
  have e1 : 1 / (768 * Λ) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ * 2
      = 1 / (384 * Λ) * (q : ℝ) ^ 2 * (9 / 4 : ℝ) ^ ℓ := by
    field_simp
    ring
  have e2 : ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (16 * (3 * r / 4 ^ (ℓ + 1) * P)) * 2
      = ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)) ^ 2
        / (8 * (3 * r / 4 ^ (ℓ + 1) * P)) := by
    field_simp
    ring
  linarith

/-- **The positive branch's exponent at the second-moment tilt:**
`AA − 2(V−q−1) + 3V₂/2 − V₂²/(4B) ≤ AA − 2V + 2(q+1) − cq²(9/4)^ℓ` for `c = 1/(768Λ)`,
`48Λ² ≤ q`, `V₂ = (q/2)(1/4)(3/4)^ℓ` and `B = (3r/4^(ℓ+1))·PP`.  The base bound enters linearly,
so the shift costs `2(q+1)` with no `Λ`, and no `V ≤ Λ·AA` is needed. -/
lemma chain_positive_exponent_two_le {AA PP c Λ V r V₂ B : ℝ} {q ℓ : ℕ}
    (hP : 0 < PP) (hr : 0 < r) (hΛ : 1 ≤ Λ) (hrP : r * PP ≤ Λ)
    (hcdef : c = 1 / (768 * Λ)) (hq : 48 * Λ ^ 2 ≤ (q : ℝ))
    (hV₂def : V₂ = (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ))
    (hBdef : B = 3 * r / 4 ^ (ℓ + 1) * PP) :
    AA - 2 * (V - (q : ℝ) - 1) + 3 * V₂ / 2 - V₂ ^ 2 / (4 * B)
      ≤ AA - 2 * V + 2 * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hBpos : (0 : ℝ) < B := by rw [hBdef]; positivity
  have h8 : 8 * B ≤ V₂ := by
    have h := eight_mul_le_chainWeight hr hP hΛ0 hrP hq ℓ
    rw [hBdef, hV₂def]
    have hB' : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) * PP := by positivity
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1) hB'.le]
  have habs := chain_absorb_three_halves hBpos h8
  have hlevel : c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ ≤ V₂ ^ 2 / (16 * B) := by
    have h := chain_sixteenth_of_two_mul hr hP hΛ0 hrP q ℓ
    rw [hcdef, hV₂def, hBdef]
    exact h
  linarith

/-- **The zero-tilt branch's exponent at the second-moment tilt:**
`V₂ − V₂²/(4B) ≤ AA − 2V + 2(q+1) − cq²(9/4)^ℓ` when `V ≤ q+1`.  At `l₁ = 0` the base bound does
not enter; `V ≤ q+1` makes `AA − 2V + 2(q+1) ≥ AA > 0`, so only the increment's own cost is paid. -/
lemma chain_zero_exponent_two_le {AA PP c Λ V r V₂ B : ℝ} {q ℓ : ℕ}
    (hA : 0 < AA) (hP : 0 < PP) (hr : 0 < r) (hΛ : 1 ≤ Λ) (hrP : r * PP ≤ Λ)
    (hcdef : c = 1 / (768 * Λ)) (hq : 48 * Λ ^ 2 ≤ (q : ℝ)) (hV : V ≤ (q : ℝ) + 1)
    (hV₂def : V₂ = (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ))
    (hBdef : B = 3 * r / 4 ^ (ℓ + 1) * PP) :
    V₂ - V₂ ^ 2 / (4 * B)
      ≤ AA - 2 * V + 2 * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hBpos : (0 : ℝ) < B := by rw [hBdef]; positivity
  have h8 : 8 * B ≤ V₂ := by
    have h := eight_mul_le_chainWeight hr hP hΛ0 hrP hq ℓ
    rw [hBdef, hV₂def]
    have hB' : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) * PP := by positivity
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1) hB'.le]
  have habs := chain_absorb_one hBpos h8
  have hlevel : c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ ≤ V₂ ^ 2 / (16 * B) := by
    have h := chain_sixteenth_of_two_mul hr hP hΛ0 hrP q ℓ
    rw [hcdef, hV₂def, hBdef]
    exact h
  linarith

/-- **One term of the chain at the second-moment tilt:**
`μ(E) ≤ exp C · exp(AA − 2V + 2(q+1) − cq²(9/4)^ℓ)`.  It uses `l₁ = 2`
(`RMF.IsRademacherRMF.exists_measure_link_le_two`) when `q + 1 ≤ V` and `l₁ = 0`
(`RMF.IsRademacherRMF.exists_measure_link_le`) when `V < q + 1`.  Neither `V ≤ Λ·AA`, `AA/2 ≤ V`,
`q + 1 ≤ 4Λ·AA` nor `Λ ≤ Λ'` is assumed. -/
theorem IsRademacherRMF.exists_measure_chain_term_two_le {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ Λ' : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) (hΛ' : 2 ≤ Λ') :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ V r c V₁ h₀ : ℝ) (q ℓ : ℕ) (h₁ h₂ : ℝ) (y₀ y : ℕ) (S : ℝ → Ω → ℝ)
        (G E : Set Ω),
        σ₀ ≤ σ → 0 < r →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
        c = 1 / (768 * Λ) → 48 * Λ ^ 2 ≤ (q : ℝ) →
        (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
            / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ' →
        |h₁ - h₂| ≤ 3 * r / 4 ^ (ℓ + 1) → MeasurableSet E → E ⊆ G →
        (∀ (t : ℝ) (ω : Ω), ω ∈ G →
          S t ω = Real.log ‖randomEulerProductIco f y₀ y (heightLine σ (h₀ + t)) ω‖) →
        (∀ ω ∈ E, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖) →
        ((q : ℝ) + 1 ≤ V → ∀ ω ∈ E, V - (q : ℝ) - 1 ≤ S 0 ω) →
        (∀ ω ∈ E, (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) ≤ S h₁ ω - S h₂ ω) →
          μ.real E ≤ Real.exp C
            * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
              - 2 * V + 2 * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
  obtain ⟨Ct, hCt, htwo⟩ :=
    IsRademacherRMF.exists_measure_link_le_two (Ω := Ω) (σ₀ := σ₀) (Λ := Λ') hσ₀ hΛ'
  obtain ⟨Cz, hCz, hzero⟩ :=
    IsRademacherRMF.exists_measure_link_le (Ω := Ω) (σ₀ := σ₀) (Λ := Λ') hσ₀ (by linarith)
  refine ⟨max Ct Cz, lt_of_lt_of_le hCt (le_max_left _ _), ?_⟩
  intro f μ hf σ V r c V₁ h₀ q ℓ h₁ h₂ y₀ y S G E hσ hr hA hP hrP hcdef hq hV₂P hgap hE hEG
    hSeq hV₁ hE₁ hE₂
  have hV₂0 : (0 : ℝ) ≤ (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ) := by positivity
  have hD0 : (0 : ℝ) < 3 * r / 4 ^ (ℓ + 1) := by positivity
  have hgap' : |h₀ + h₁ - (h₀ + h₂)| ≤ 3 * r / 4 ^ (ℓ + 1) := by
    rw [show h₀ + h₁ - (h₀ + h₂) = h₁ - h₂ from by ring]
    exact hgap
  have hE₂' : ∀ ω ∈ E, (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
      ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ (h₀ + h₁)) ω‖
        - Real.log ‖randomEulerProductIco f y₀ y (heightLine σ (h₀ + h₂)) ω‖ := by
    intro ω hω
    rw [← hSeq h₁ ω (hEG hω), ← hSeq h₂ ω (hEG hω)]
    exact hE₂ ω hω
  rcases lt_or_ge V ((q : ℝ) + 1) with hV | hV
  · have h := hzero f μ hf 0 σ V₁ ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ))
      (3 * r / 4 ^ (ℓ + 1)) h₀ (h₀ + h₁) (h₀ + h₂) y₀ y E le_rfl (by linarith) hσ hgap'
      hV₂0 hD0 hP hV₂P hE hV₁ hE₂'
    refine le_trans h ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hexp := chain_zero_exponent_two_le (AA := ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
      (PP := ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) (c := c) (Λ := Λ) (V := V)
      (r := r) (V₂ := (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ))
      (B := 3 * r / 4 ^ (ℓ + 1) * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
      (q := q) (ℓ := ℓ) hA hP hr hΛ hrP hcdef hq (le_of_lt hV) rfl rfl
    have hmax : Cz ≤ max Ct Cz := le_max_right _ _
    linarith
  · have hE₁' : ∀ ω ∈ E, V - (q : ℝ) - 1
        ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖ := by
      intro ω hω
      have h0 := hSeq 0 ω (hEG hω)
      rw [add_zero] at h0
      rw [← h0]
      exact hE₁ hV ω hω
    have h := htwo f μ hf σ (V - (q : ℝ) - 1) ((q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ))
      (3 * r / 4 ^ (ℓ + 1)) h₀ (h₀ + h₁) (h₀ + h₂) y₀ y E hσ hgap' hV₂0 hD0 hP hV₂P hE
      hE₁' hE₂'
    refine le_trans h ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hexp := chain_positive_exponent_two_le
      (AA := ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
      (PP := ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) (c := c) (Λ := Λ) (V := V)
      (r := r) (V₂ := (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ))
      (B := 3 * r / 4 ^ (ℓ + 1) * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p)
      (q := q) (ℓ := ℓ) hP hr hΛ hrP hcdef hq rfl rfl
    have hmax : Ct ≤ max Ct Cz := le_max_left _ _
    linarith

/-! ### The union bound and the small slices at the second-moment tilt

`RMF.sum_slices_le` applies as it stands: its `hbig` slot
`Cl · ∑_ℓ 4^(ℓ+1) · exp(−W + 2Λ(q+1) − cq²(9/4)^ℓ)` is the second-moment exponent at
`W = 2V − AA` and `Λ := 1`, and its constant's `(2Λ)²/(2c)` becomes `2/c = 1536Λ`.

The small slices consume `RMF.IsRademacherRMF.measure_ge_le_second_moment`, which carries no
constant, no `σ₀` and no tilt range, so neither `AA/2 ≤ V − q₀ − 1` nor `V ≤ Λ·AA` is needed.  It
needs `0 < ‖F‖` pointwise, since `ℓog 0 = 0` would let a vanishing point satisfy `V ≤ ℓog‖F‖` when
`V ≤ 0`; that is stated on `G` and discharged by `RMF.norm_randomEulerProductIco_sqfree_pos`. -/

/-- **The union bound over the chain's slices at the second-moment tilt:** the measure of the
union of the slices over `ℓ < L`, `i < 4^(ℓ+1)` is at most
`exp C · ∑_{ℓ<L} 4^(ℓ+1) · exp(AA − 2V + 2(q+1) − cq²(9/4)^ℓ)`, by
`RMF.IsRademacherRMF.exists_measure_chain_term_two_le` once per `(ℓ, i)`. -/
theorem IsRademacherRMF.exists_measure_chain_union_two_le {Ω : Type*} [MeasurableSpace Ω]
    {σ₀ Λ Λ' : ℝ} (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) (hΛ' : 2 ≤ Λ') :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ V r c V₁ h₀ : ℝ) (q Q L y₀ y : ℕ) (S : ℝ → Ω → ℝ) (G : Set Ω),
        σ₀ ≤ σ → 0 < r →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        0 < (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
        c = 1 / (768 * Λ) → 48 * Λ ^ 2 ≤ (q : ℝ) →
        (q : ℝ) / 8 / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ' →
        MeasurableSet G → (∀ t : ℝ, Measurable (S t)) →
        (∀ (t : ℝ) (ω : Ω), ω ∈ G →
          S t ω = Real.log ‖randomEulerProductIco f y₀ y (heightLine σ (h₀ + t)) ω‖) →
        (∀ ω ∈ G, V₁ ≤ Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖) →
        ((q : ℝ) + 1 ≤ V → q < Q) →
          μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
            (G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
              ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
                  ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                    - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
            ≤ Real.exp C * ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1)
                * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
                  - 2 * V + 2 * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
  obtain ⟨Cd, hCd, hterm⟩ := IsRademacherRMF.exists_measure_chain_term_two_le
    (Ω := Ω) (σ₀ := σ₀) (Λ := Λ) (Λ' := Λ') hσ₀ hΛ hΛ'
  refine ⟨Cd, hCd, ?_⟩
  intro f μ hf σ V r c V₁ h₀ q Q L y₀ y S G hσ hr hA hP hrP hcdef hq hqP
    hGmeas hSmeas hSeq hV₁ hQlt
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  rw [Finset.mul_sum]
  refine le_trans (measureReal_biUnion_finset_le _ _) (Finset.sum_le_sum fun ℓ _ => ?_)
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  have hV2P : (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
      / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ' := by
    have hw1 : ((3 : ℝ) / 4) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hw1 hq0
    rw [div_le_iff₀ hP]
    rw [div_le_iff₀ hP] at hqP
    linarith
  have hb : ∀ i ∈ Finset.range (4 ^ (ℓ + 1)),
      μ.real (G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω})
        ≤ Real.exp Cd
          * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            - 2 * V + 2 * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro i _
    exact hterm f μ hf σ V r c V₁ h₀ q ℓ ((i : ℝ) * (r / 4 ^ (ℓ + 1)))
      (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) y₀ y S G _ hσ hr hA hP hrP
      hcdef hq hV2P (abs_index_gap_le hr i ℓ)
      ((hGmeas.inter (measurableSet_bracket hSmeas V q Q)).inter
        (measurableSet_le measurable_const ((hSmeas _).sub (hSmeas _))))
      (fun ω hω => hω.1.1) hSeq (fun ω hω => hV₁ ω hω.1.1)
      (fun hV ω hω => le_of_lt (hω.1.2.1 (hQlt hV))) (fun ω hω => hω.2)
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  exact le_of_eq (by ring)

/-- **The slices below the threshold at the second-moment tilt:** for `q ≤ q₀` the union is at
most `exp(AA − 2V + 2(q₀+1))`, from the base bound alone; the caller reads `exp(2(q₀+1))` off it
as `RMF.sum_slices_le`'s `Cb` at `W = 2V − AA`.  `hGpos` is discharged by
`RMF.norm_randomEulerProductIco_sqfree_pos` on the unimodularity set. -/
theorem IsRademacherRMF.measure_chain_small_two_le {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ArithmeticFunction ℂ} {μ : Measure Ω} (hf : IsRademacherRMF f μ)
    (σ V r h₀ : ℝ) (q q₀ Q L y₀ y : ℕ) (S : ℝ → Ω → ℝ) (G : Set Ω)
    (hq₀ : q ≤ q₀) (hqQ : q < Q)
    (hGmeas : MeasurableSet G) (hSmeas : ∀ t : ℝ, Measurable (S t))
    (hSeq : ∀ (t : ℝ) (ω : Ω), ω ∈ G →
      S t ω = Real.log ‖randomEulerProductIco f y₀ y (heightLine σ (h₀ + t)) ω‖)
    (hGpos : ∀ ω ∈ G, 0 < ‖randomEulerProductIco f y₀ y (heightLine σ h₀) ω‖) :
    μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
      (G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
        ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
            ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
              - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          - 2 * V + 2 * ((q₀ : ℝ) + 1)) := by
  haveI : IsProbabilityMeasure μ := by
    obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
    exact hX.isProbabilityMeasure
  have hcast : (q : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast hq₀
  have hsub : (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
      (G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
        ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
            ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
              - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ⊆ G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)} := by
    refine Set.iUnion₂_subset fun ℓ _ => Set.iUnion₂_subset fun i _ => ?_
    exact Set.inter_subset_left
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  have h := hf.measure_ge_le_second_moment (V := V - (q : ℝ) - 1) (s := heightLine σ h₀)
    (y₀ := y₀) (y₁ := y) (hGmeas.inter (measurableSet_bracket hSmeas V q Q))
    (fun ω hω => hGpos ω hω.1)
    (fun ω hω => by
      have h0 := hSeq 0 ω hω.1
      rw [add_zero] at h0
      rw [← h0]
      exact le_of_lt (hω.2.1 hqQ))
  refine le_trans h (Real.exp_le_exp.2 ?_)
  simp only [re_heightLine]
  linarith

/-! ### The Rademacher walk is Lipschitz in the height

Lemma B.2's setup needs a Lipschitz bound for the squarefree walk, a sum of `localLogAdd`, and
`RMF.abs_sum_localLog_sub_le` is stated for `localLog`.  `RMF.localLogAdd_eq_neg_localLog`
(`EulerProduct/RademacherLogField.lean`) reflects the weight, `localLogAdd w z = −localLog (−w) z`,
which does not fit, since `abs_sum_localLog_sub_le` needs its weight to be literally
`(p : ℂ) ^ (−s)`.  Reflecting the value instead, `localLogAdd w z = −localLog w (−z)`, keeps the
weight and moves the reflection onto `Y`, where `‖−Y p‖ = ‖Y p‖`.  So the Lipschitz constant is
the Steinhaus one, `(1 − 2^{−σ})⁻¹ · ∑_p p^{−σ}ℓog p`. -/

/-- **The reflection in the value.**  `localLogAdd w z = −localLog w (−z)`.

The companion of `RMF.localLogAdd_eq_neg_localLog`, which reflects the weight instead.  Both are
immediate from `localLog w z = −ℓog‖1 − zw‖` and `localLogAdd w z = ℓog‖1 + zw‖`, but **only
this one keeps the weight `(p : ℂ) ^ (−s)` intact**, which is what lets the Steinhaus Lipschitz
bound be reused verbatim. -/
lemma localLogAdd_eq_neg_localLog_neg (w z : ℂ) : localLogAdd w z = -localLog w (-z) := by
  simp [localLogAdd, localLog, neg_mul, sub_neg_eq_add]

/-- **The squarefree walk is Lipschitz in the height**, with the Steinhaus constant.

The `localLogAdd` counterpart of `RMF.abs_sum_localLog_sub_le`, obtained from it by reflecting
the values: `‖−Y p‖ = ‖Y p‖`, so the unimodularity hypothesis transfers unchanged and the two
sums differ only by an overall sign, which `abs_neg` removes. -/
lemma abs_sum_localLogAdd_sub_le {B : Finset ℕ} (hB : ∀ p ∈ B, Nat.Prime p) {Y : ℕ → ℂ}
    (hY : ∀ p ∈ B, ‖Y p‖ ≤ 1) {s s' : ℂ} {σ : ℝ} (hs : s.re = σ) (hs' : s'.re = σ)
    (hσ : 0 < σ) :
    |(∑ p ∈ B, localLogAdd ((p : ℂ) ^ (-s)) (Y p))
        - ∑ p ∈ B, localLogAdd ((p : ℂ) ^ (-s')) (Y p)|
      ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ * (∑ p ∈ B, (p : ℝ) ^ (-σ) * Real.log p)
        * |s.im - s'.im| := by
  have h := abs_sum_localLog_sub_le (B := B) hB (Y := fun p => -Y p)
    (fun p hp => by rw [norm_neg]; exact hY p hp) hs hs' hσ
  have key : ∀ u : ℂ, (∑ p ∈ B, localLogAdd ((p : ℂ) ^ (-u)) (Y p))
      = -∑ p ∈ B, localLog ((p : ℂ) ^ (-u)) (-Y p) := by
    intro u
    have h1 : (∑ p ∈ B, localLogAdd ((p : ℂ) ^ (-u)) (Y p))
        = ∑ p ∈ B, -localLog ((p : ℂ) ^ (-u)) (-Y p) :=
      Finset.sum_congr rfl fun p _ => localLogAdd_eq_neg_localLog_neg _ _
    rw [h1, Finset.sum_neg_distrib]
  rw [key s, key s',
    show -(∑ p ∈ B, localLog ((p : ℂ) ^ (-s)) (-Y p))
        - -(∑ p ∈ B, localLog ((p : ℂ) ^ (-s')) (-Y p))
      = -((∑ p ∈ B, localLog ((p : ℂ) ^ (-s)) (-Y p))
        - ∑ p ∈ B, localLog ((p : ℂ) ^ (-s')) (-Y p)) from by ring,
    abs_neg]
  exact h

/-! ### Lemma B.2's arithmetic, extracted

The two inequalities of Lemma B.2's shell, proved in a context of a few hypotheses rather than in
the shell's.  The final combination `base + slices ≤ (Cb + Cq)·E` is one `linarith only`, since
`RMF.sum_slices_le` handles the whole range `Finset.Icc 1 Q`; and there is no `V²/AA` in the
second-moment exponent, so the Steinhaus `hVA : V²/AA ≤ Λ·V` does not arise. -/

/-- **The chain weight is within `Λ'` of the log-weighted prime sum:** `q/8/PP ≤ 3Λ + q₀ + 3`, the
`hqP` of `RMF.IsRademacherRMF.exists_measure_chain_union_two_le` at `Λ' = 3Λ + q₀ + 3`.  From
`q ≤ Q ≤ V + q₀ + 3 ≤ (Λ + q₀ + 3)·AA`, using `1 ≤ AA`, and `PP ≥ ℓog 2·AA` with `ℓog 2 > 1/8`.
This is why Lemma B.2 keeps `V ≤ Λ·AA` as a hypothesis. -/
lemma chain_weight_div_le_lambda' {AA PP V Λ q Q q₀ : ℝ}
    (hΛ : 1 ≤ Λ) (hq₀ : 0 ≤ q₀) (hA1 : 1 ≤ AA) (hP : 0 < PP)
    (hPlow : Real.log 2 * AA ≤ PP) (hVΛ : V ≤ Λ * AA)
    (hqQ : q ≤ Q) (hQ : Q ≤ V + q₀ + 3) :
    q / 8 / PP ≤ 3 * Λ + q₀ + 3 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hA0 : (0 : ℝ) < AA := by linarith
  rw [div_div, div_le_iff₀ (by positivity : (0 : ℝ) < 8 * PP)]
  have h2 : V + q₀ + 3 ≤ (Λ + q₀ + 3) * AA := by
    nlinarith only [hVΛ, hA1, hq₀,
      mul_nonneg hq₀ (by linarith : (0 : ℝ) ≤ AA - 1)]
  have h3 : (3 * Λ + q₀ + 3) * (Real.log 2 * AA) ≤ (3 * Λ + q₀ + 3) * PP :=
    mul_le_mul_of_nonneg_left hPlow (by linarith)
  have hscal : Λ + q₀ + 3 ≤ 8 * ((3 * Λ + q₀ + 3) * Real.log 2) := by
    nlinarith only [hlog2, hq₀, hΛ,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Λ + q₀ + 3)
        (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803)]
  have h4 := mul_le_mul_of_nonneg_right hscal hA0.le
  linarith only [hqQ, hQ, h2, h3, h4]

/-- **The chaining threshold at `c = 1/(768Λ)`:** `3 ≤ cq²` for `q > q₀ ≥ 48Λ² + 48Λ`, which is
`RMF.sum_slices_le`'s `hT`.  `q₀` is double Steinhaus's `24Λ² + 24Λ`, as `c` is halved: from
`q > 48Λ(Λ+1) ≥ 96Λ`, `q² ≥ 9216Λ² ≥ 9216Λ` against the needed `2304Λ`, a factor `4` uniform in
`Λ`. -/
lemma three_le_chain_threshold_two {Λ c q₀ q : ℝ} (hΛ : 1 ≤ Λ)
    (hcdef : c = 1 / (768 * Λ)) (hq₀ : 48 * Λ ^ 2 + 48 * Λ ≤ q₀) (hq : q₀ < q) :
    3 ≤ c * q ^ 2 := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hsqΛ : Λ ≤ Λ ^ 2 := by nlinarith only [hΛ]
  have h96 : 96 * Λ ≤ q := by linarith only [hq₀, hq, hsqΛ]
  have hq0 : (0 : ℝ) < q := by linarith
  have hsq : 9216 * Λ ^ 2 ≤ q ^ 2 := by nlinarith only [h96, hΛ0.le, hq0]
  rw [hcdef, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith only [hsq, hsqΛ, hΛ0.le]

/-- **Lemma B.2, Rademacher case, on an arbitrary interval.**

`μ{ω | ∃ h ∈ [h₀, h₀+r), V < ℓog‖F(σ+ih)‖} ≤ C·exp(AA − 2V)`, the counterpart of
`RMF.IsSteinhausRMF.exists_measure_exists_gt_le` and of its `_shift`.

**There is no rotation.**  The Rademacher law is not invariant under multiplication by a unimodular
constant, so the base is carried: `S t ω = ℓog‖F(heightLine σ (h₀ + t))‖`, and
`RMF.measureReal_inter_exists_gt_le` applies as it stands, its `Set.Ico 0 r` living in the walk's
parameter.

**The exponent is `AA − 2V`, not `−V²/AA`.**  At the second-moment tilt the block moment is exact,
so the leaf is Chernoff with no truncation constant.  At the barrier, with `V = A + τ + b` and
`a ≤ τ + C₁`, `exp(a − 2V) ≤ exp(C₁)·exp(−τ)·exp(−2A)·exp(−2b)`; the `exp(−τ)` is consumed exactly
by the barrier's union over `N ≤ 2e^{τ+ϑ}` intervals (`RMF.barrier_upper_exponent_two_le`). -/
theorem IsRademacherRMF.exists_measure_exists_gt_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ V r h₀ : ℝ) (y₀ y : ℕ), σ₀ ≤ σ → 0 < r → 0 ≤ V →
        1 ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        V ≤ Λ * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
              V < Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
            ≤ C * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * V) := by
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (768 * Λ) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  obtain ⟨q₀, hq₀def⟩ : ∃ q₀ : ℕ, q₀ = ⌈48 * Λ ^ 2 + 48 * Λ⌉₊ := ⟨_, rfl⟩
  have hq₀ge : (48 : ℝ) * Λ ^ 2 + 48 * Λ ≤ (q₀ : ℝ) := by rw [hq₀def]; exact Nat.le_ceil _
  have hq₀R : (0 : ℝ) ≤ (q₀ : ℝ) := Nat.cast_nonneg q₀
  obtain ⟨Λ', hΛ'def⟩ : ∃ Λ' : ℝ, Λ' = 3 * Λ + (q₀ : ℝ) + 3 := ⟨_, rfl⟩
  have hΛ'2 : (2 : ℝ) ≤ Λ' := by rw [hΛ'def]; linarith
  obtain ⟨Cb, hCbdef⟩ : ∃ Cb : ℝ, Cb = Real.exp (2 * ((q₀ : ℝ) + 1)) := ⟨_, rfl⟩
  have hCb0 : (0 : ℝ) < Cb := by rw [hCbdef]; exact Real.exp_pos _
  obtain ⟨Csum, hCsumdef⟩ : ∃ Csum : ℝ, Csum = 8 * Real.exp (2 * 1)
      * (Real.exp ((2 * 1) ^ 2 / (2 * c)) * (1 - Real.exp (-(c / 2)))⁻¹) := ⟨_, rfl⟩
  have hCsum0 : (0 : ℝ) ≤ Csum := by
    have h1 : Real.exp (-(c / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have h2 : (0 : ℝ) < 1 - Real.exp (-(c / 2)) := by linarith
    rw [hCsumdef]
    positivity
  obtain ⟨Cd, hCd, hunion⟩ := IsRademacherRMF.exists_measure_chain_union_two_le
    (Ω := Ω) (σ₀ := σ₀) (Λ := Λ) (Λ' := Λ') hσ₀ hΛ hΛ'2
  refine ⟨Real.exp 2 + (q₀ : ℝ) * Cb + Real.exp Cd * Csum, ?_, ?_⟩
  · have h1 := Real.exp_pos (2 : ℝ)
    have h2 := Real.exp_pos Cd
    nlinarith only [h1, h2, hCb0, hCsum0, hq₀R]
  intro f μ hf σ V r h₀ y₀ y hσ hr hV hA1 hVΛ hrP
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  haveI := hX.isProbabilityMeasure
  have hA : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) := by linarith
  have hP : (0 : ℝ) < ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p := by
    have h := log_two_mul_sum_le_sum_mul_log σ y₀ y
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith only [h, hl2, hA]
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hre0 : (0 : ℝ) < (heightLine σ h₀).re := by rw [re_heightLine]; exact hσ0
  -- the unimodularity set
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    have hrw : {ω : Ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1}
        = ⋂ p ∈ primesIco y₀ y, {ω : Ω | ‖X p ω‖ ≤ 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hGdef, hrw]
    exact (primesIco y₀ y).measurableSet_biInter fun p hp =>
      measurableSet_le ((hX.measurable p (prime_of_mem_primesIco hp)).norm) measurable_const
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  -- the walk, based at `h₀`
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → Ω → ℝ, S = fun t ω =>
    ∑ p ∈ primesIco y₀ y, localLogAdd ((p : ℂ) ^ (-(heightLine σ (h₀ + t)))) (X p ω) := ⟨_, rfl⟩
  have hSmeas : ∀ t : ℝ, Measurable (S t) := by
    intro t
    simp only [hSdef]
    exact Finset.measurable_sum _ fun p hp =>
      (measurable_localLogAdd _).comp (hX.measurable p (prime_of_mem_primesIco hp))
  have hSeq : ∀ (t : ℝ) (ω : Ω), ω ∈ G →
      S t ω = Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (heightLine σ (h₀ + t)) ω‖ := by
    intro t ω hω
    rw [hGdef] at hω
    simp only [hSdef]
    exact (log_norm_randomEulerProductIco_sqfree_eq
      (by rw [re_heightLine]; exact hσ0) hω).symm
  -- the Lipschitz bound and the level at which the chain is cut
  obtain ⟨Lip, hLipdef⟩ : ∃ Lip : ℝ, Lip = (1 - (2 : ℝ) ^ (-σ))⁻¹
      * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) * Real.log p := ⟨_, rfl⟩
  have hθ : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hLip0 : (0 : ℝ) ≤ Lip := by
    have h1 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by linarith
    have h2 : (0 : ℝ) ≤ ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-σ) * Real.log p := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpp := prime_of_mem_primesIco hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
      have hl := Real.log_nonneg hp1
      have hr0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
      positivity
    rw [hLipdef]
    positivity
  have hLip : ∀ ω ∈ G, ∀ u v : ℝ, |S u ω - S v ω| ≤ Lip * |u - v| := by
    intro ω hω u v
    rw [hGdef] at hω
    have h := abs_sum_localLogAdd_sub_le (B := primesIco y₀ y)
      (fun p hp => prime_of_mem_primesIco hp) hω
      (re_heightLine σ (h₀ + u)) (re_heightLine σ (h₀ + v)) hσ0
    rw [im_heightLine, im_heightLine, show h₀ + u - (h₀ + v) = u - v from by ring] at h
    simp only [hSdef]
    rw [hLipdef]
    exact h
  obtain ⟨L, hL⟩ := exists_level_le (Lip := Lip) hr (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌈V⌉₊ + q₀ + 2 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; omega
  have hq₀Q : q₀ < Q := by rw [hQdef]; omega
  have hQupper : (Q : ℝ) ≤ V + (q₀ : ℝ) + 3 := by
    rw [hQdef]
    push_cast
    have := Nat.ceil_lt_add_one hV
    linarith
  have hQge : V + (q₀ : ℝ) + 2 ≤ (Q : ℝ) := by
    rw [hQdef]
    push_cast
    have := Nat.le_ceil V
    linarith
  -- the target, moved onto the unimodularity set and reindexed by `h = h₀ + t`
  have htarget : μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
      V < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
        (heightLine σ h) ω‖} = μ.real (G ∩ {ω | ∃ t ∈ Set.Ico 0 r, V < S t ω}) := by
    have hset : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        V < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
          (heightLine σ h) ω‖} = G ∩ {ω | ∃ t ∈ Set.Ico 0 r, V < S t ω} := by
      ext ω
      constructor
      · rintro ⟨hωG, h, hh, hlt⟩
        simp only [Set.mem_Ico] at hh
        refine ⟨hωG, h - h₀, ?_, ?_⟩
        · simp only [Set.mem_Ico]
          constructor <;> linarith [hh.1, hh.2]
        · rw [hSeq (h - h₀) ω hωG, show h₀ + (h - h₀) = h from by ring]
          exact hlt
      · rintro ⟨hωG, t, ht, hlt⟩
        simp only [Set.mem_Ico] at ht
        refine ⟨hωG, h₀ + t, ?_, ?_⟩
        · simp only [Set.mem_Ico]
          constructor <;> linarith [ht.1, ht.2]
        · rw [← hSeq t ω hωG]
          exact hlt
    unfold MeasureTheory.Measure.real
    rw [measure_eq_measure_inter_of_compl_null hGnull, hset]
  rw [htarget]
  refine le_trans (measureReal_inter_exists_gt_le (μ := μ) (S := S) (G := G) (V := V)
    hr hQ1 hLip0 hLip hL) ?_
  -- the base point
  have hbase0 : μ.real (G ∩ {ω | V - 1 < S 0 ω})
      ≤ Real.exp 2 * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * V) := by
    have h := hf.measure_ge_le_second_moment (V := V - 1) (s := heightLine σ h₀)
      (y₀ := y₀) (y₁ := y) (hGmeas.inter (measurableSet_lt measurable_const (hSmeas 0)))
      (fun ω hω => norm_randomEulerProductIco_sqfree_pos hre0 (by
        have := hω.1
        rwa [hGdef] at this))
      (fun ω hω => by
        have h0 := hSeq 0 ω hω.1
        rw [add_zero] at h0
        rw [← h0]
        exact le_of_lt hω.2)
    refine le_trans h (le_of_eq ?_)
    rw [← Real.exp_add]
    simp only [re_heightLine]
    ring_nf
  -- the slices below the threshold
  have hsmall : ∀ q ∈ Finset.Ioc 0 q₀,
      μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Cb * Real.exp (-(2 * V - (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)))) := by
    intro q hq
    have hq₀' : q ≤ q₀ := (Finset.mem_Ioc.1 hq).2
    have h := hf.measure_chain_small_two_le σ V r h₀ q q₀ Q L y₀ y S G hq₀'
      (lt_of_le_of_lt hq₀' hq₀Q) hGmeas hSmeas hSeq
      (fun ω hω => norm_randomEulerProductIco_sqfree_pos hre0 (by rwa [hGdef] at hω))
    refine le_trans h (le_of_eq ?_)
    rw [hCbdef, ← Real.exp_add]
    ring_nf
  -- the slices above it
  obtain ⟨V₁, hV₁def⟩ : ∃ V₁ : ℝ, V₁ = ∑ p ∈ primesIco y₀ y,
      Real.log (1 - ((p : ℕ) : ℝ) ^ (-(heightLine σ h₀).re)) := ⟨_, rfl⟩
  have hV₁ : ∀ ω ∈ G, V₁ ≤ Real.log ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => X p ω) y₀ y (heightLine σ h₀) ω‖ := by
    intro ω hω
    rw [hV₁def]
    exact le_log_norm_randomEulerProductIco_sqfree hre0 (by rwa [hGdef] at hω)
  have hbig : ∀ q ∈ Finset.Ioc q₀ Q,
      μ.real (⋃ ℓ ∈ Finset.range L, ⋃ i ∈ Finset.range (4 ^ (ℓ + 1)),
        (G ∩ {ω | (q < Q → V - (q : ℝ) - 1 < S 0 ω) ∧ S 0 ω ≤ V - (q : ℝ)}
          ∩ {ω | (q : ℝ) / 2 * ((1 / 4) * (3 / 4) ^ ℓ)
              ≤ S ((i : ℝ) * (r / 4 ^ (ℓ + 1))) ω
                - S (((4 * (i / 4) : ℕ) : ℝ) * (r / 4 ^ (ℓ + 1))) ω}))
      ≤ Real.exp Cd * ∑ ℓ ∈ Finset.range L, (4 : ℝ) ^ (ℓ + 1)
          * Real.exp (-(2 * V - (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)))
            + 2 * 1 * ((q : ℝ) + 1) - c * (q : ℝ) ^ 2 * (9 / 4) ^ ℓ) := by
    intro q hq
    have hq₀q : q₀ < q := (Finset.mem_Ioc.1 hq).1
    have hqQ' : q ≤ Q := (Finset.mem_Ioc.1 hq).2
    have hq₀qR : (q₀ : ℝ) < (q : ℝ) := by exact_mod_cast hq₀q
    have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ'
    have hq48 : 48 * Λ ^ 2 ≤ (q : ℝ) := by linarith only [hq₀ge, hq₀qR, hΛ0.le]
    have hqP : (q : ℝ) / 8 / (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ' := by
      rw [hΛ'def]
      exact chain_weight_div_le_lambda' hΛ hq₀R hA1 hP
        (log_two_mul_sum_le_sum_mul_log σ y₀ y) hVΛ hqQR hQupper
    have h := hunion _ μ hf σ V r c V₁ h₀ q Q L y₀ y S G hσ hr hA hP hrP hcdef hq48 hqP
      hGmeas hSmeas hSeq hV₁ (fun hqV => by
        have hlt : (q : ℝ) < (Q : ℝ) := by linarith only [hqV, hQge, hq₀R]
        exact_mod_cast hlt)
    refine le_trans h (le_of_eq ?_)
    refine congrArg (fun z => Real.exp Cd * z) (Finset.sum_congr rfl fun ℓ _ => ?_)
    congr 2
    ring
  -- the sum over `q`, then the base point
  have hT : ∀ q ∈ Finset.Ioc q₀ Q, 3 ≤ c * (q : ℝ) ^ 2 := by
    intro q hq
    have hq₀q : q₀ < q := (Finset.mem_Ioc.1 hq).1
    have hq₀qR : (q₀ : ℝ) < (q : ℝ) := by exact_mod_cast hq₀q
    exact three_le_chain_threshold_two hΛ hcdef hq₀ge hq₀qR
  have hslices := sum_slices_le (W := 2 * V - ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
    (Λ := 1) (Cb := Cb) (Cl := Real.exp Cd) hc hq₀Q (Real.exp_pos Cd).le hT hsmall hbig
  rw [← hCsumdef] at hslices
  have hEeq : Real.exp (-(2 * V - ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)))
      = Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * V) := by
    congr 1
    ring
  rw [hEeq] at hslices
  linarith only [hbase0, hslices]

/-! ### The reflection `X ↦ −X`, and what it buys

The Steinhaus lower tail reduces to the upper tail by reflecting the values with
`RMF.IsSteinhausPrimeValues.mul_unimodular` at `c = −1`, then a pointwise inequality
(`RMF.neg_log_norm_randomEulerProductIco_le`) dominating `−ℓog‖F(X)‖` by `ℓog‖F(−X)‖ + 4AA`.
Both halves transfer.  Rotation by a general unimodular constant is not a Rademacher symmetry, but
negation is: `rademacherLaw` is the fair coin on `{1, −1}`, and `z ↦ −z` swaps its two atoms.  In
`mul_unimodular` only the law step is Steinhaus-specific (`RMF.map_mul_left_steinhausLaw`, in
`Probability/Laws.lean`); `RMF.map_neg_rademacherLaw` replaces it.  The pointwise inequality is
the same estimate read in the other direction: both reduce to `∑_p ∓ℓog‖1 − (X_p w)²‖ ≤ 4AA`, and
`RMF.abs_log_norm_one_sub_le` is two-sided.  `RMF.IsSteinhausPrimeValues.mul_unimodular` is in
`Probability/PrimeValues.lean`. -/

/-- **The Rademacher law is invariant under negation.**

`z ↦ −z` swaps the fair coin's two atoms, so the law is unchanged.  The counterpart of
`RMF.map_mul_left_steinhausLaw`, which holds for *every* unimodular `c`; here only `c = −1`
is available, and that is exactly the case the lower tail needs. -/
theorem map_neg_rademacherLaw :
    rademacherLaw.map (fun z : ℂ => (-1 : ℂ) * z) = rademacherLaw := by
  have hm : Measurable (fun z : ℂ => (-1 : ℂ) * z) := by fun_prop
  conv_lhs => rw [rademacherLaw]
  rw [Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm, Measure.map_dirac' hm,
    show ((-1 : ℂ) * 1) = -1 from by ring, show ((-1 : ℂ) * (-1)) = 1 from by ring,
    add_comm]
  rfl

/-- **Negating the values preserves the Rademacher hypotheses.**

The counterpart of `RMF.IsSteinhausPrimeValues.mul_unimodular` at `c = −1`.  Measurability and
independence are law-free; only the law step differs, and it is `RMF.map_neg_rademacherLaw`
in place of `RMF.map_mul_left_steinhausLaw`. -/
theorem IsRademacherPrimeValues.neg {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ}
    {μ : Measure Ω} (hX : IsRademacherPrimeValues X μ) :
    IsRademacherPrimeValues (fun p ω => (-1 : ℂ) * X p ω) μ := by
  refine ⟨fun p hp => (hX.measurable p hp).const_mul _, ?_, fun p hp => ?_⟩
  · exact hX.iIndep.comp (fun _ : Nat.Primes => fun z : ℂ => (-1 : ℂ) * z)
      (fun _ => measurable_id.const_mul _)
  · refine ⟨((hX.measurable p hp).const_mul _).aemeasurable, ?_⟩
    have hcomp : (fun ω => (-1 : ℂ) * X p ω) = (fun z : ℂ => (-1 : ℂ) * z) ∘ X p := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (hX.measurable p hp), (hX.hasLaw p hp).map_eq,
      map_neg_rademacherLaw]

/-- **The additive local logarithm at reflected values.**

`ℓog‖1+zw‖ + ℓog‖1−zw‖ = ℓog‖1 − (zw)²‖`, the counterpart of
`RMF.localLog_add_localLog_neg`, from which it differs only by an overall sign. -/
lemma localLogAdd_add_localLogAdd_neg {w z : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    localLogAdd w z + localLogAdd w ((-1 : ℂ) * z) = Real.log ‖1 - (z * w) ^ 2‖ := by
  have hz' : ‖(-1 : ℂ) * z‖ ≤ 1 := by rwa [norm_mul, norm_neg, norm_one, one_mul]
  have h1 := norm_one_sub_mul_pos hz' hw
  have h2 := norm_one_sub_mul_pos hz hw
  have hprod : (1 - ((-1 : ℂ) * z) * w) * (1 - z * w) = 1 - (z * w) ^ 2 := by ring
  rw [localLogAdd, localLogAdd, show (1 : ℂ) + z * w = 1 - ((-1 : ℂ) * z) * w from by ring,
    show (1 : ℂ) + ((-1 : ℂ) * z) * w = 1 - z * w from by ring, ← hprod, norm_mul,
    Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]

/-- **The reflected squarefree walk dominates the walk's negative**, up to `4∑_p p^{−2σ}`.

The counterpart of `RMF.neg_log_norm_randomEulerProductIco_le`.  Both reduce to bounding
`∑_p ∓ℓog‖1 − (X_p p^{−s})²‖` by `4AA`, and `RMF.abs_log_norm_one_sub_le` is two-sided, so the
same estimate serves — **Steinhaus needs its upper half and this needs its lower half.** -/
lemma neg_log_norm_randomEulerProductIco_sqfree_le {Ω : Type*} {X : ℕ → Ω → ℂ} {y₀ y : ℕ}
    {s : ℂ} (hs : 1 / 3 ≤ s.re) {ω : Ω} (hω : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1) :
    -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y s ω‖
      ≤ Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y s ω‖
          + 4 * ∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * s.re) := by
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hω' : ∀ p ∈ primesIco y₀ y, ‖(-1 : ℂ) * X p ω‖ ≤ 1 := by
    intro p hp
    rw [norm_mul, norm_neg, norm_one, one_mul]
    exact hω p hp
  rw [log_norm_randomEulerProductIco_sqfree_eq hs0 hω,
    log_norm_randomEulerProductIco_sqfree_eq hs0 hω']
  have hterm : ∀ p ∈ primesIco y₀ y,
      -localLogAdd ((p : ℂ) ^ (-s)) (X p ω)
        ≤ localLogAdd ((p : ℂ) ^ (-s)) ((-1 : ℂ) * X p ω) + 4 * (p : ℝ) ^ (-2 * s.re) := by
    intro p hp
    have hpp := prime_of_mem_primesIco hp
    have hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
    have hwlt : ‖(p : ℂ) ^ (-s)‖ < 1 := norm_prime_cpow_neg_lt_one hpp hs0
    have hkey := localLogAdd_add_localLogAdd_neg (hω p hp) hwlt
    have hsq : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
    have hnv : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ ≤ (p : ℝ) ^ (-2 * s.re) := by
      rw [norm_pow, norm_mul, hw, ← hsq]
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
      have ha : ‖X p ω‖ ≤ 1 := hω p hp
      have ha0 : (0 : ℝ) ≤ ‖X p ω‖ := norm_nonneg _
      calc (‖X p ω‖ * (p : ℝ) ^ (-s.re)) ^ 2
          = ‖X p ω‖ ^ 2 * ((p : ℝ) ^ (-s.re)) ^ 2 := by ring
        _ ≤ 1 * ((p : ℝ) ^ (-s.re)) ^ 2 :=
            mul_le_mul_of_nonneg_right (by nlinarith only [ha, ha0]) (by positivity)
        _ = ((p : ℝ) ^ (-s.re)) ^ 2 := one_mul _
    have h34 : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ ≤ 3 / 4 :=
      le_trans hnv (rpow_prime_neg_two_mul_le (by linarith) hpp.two_le)
    have hvlt : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ < 1 := by linarith
    have habs := abs_log_norm_one_sub_le hvlt
    have hfrac : ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖ / (1 - ‖(X p ω * (p : ℂ) ^ (-s)) ^ 2‖)
        ≤ 4 * (p : ℝ) ^ (-2 * s.re) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [hnv, h34, norm_nonneg ((X p ω * (p : ℂ) ^ (-s)) ^ 2)]
    rw [abs_le] at habs
    linarith only [hkey, habs.1, hfrac]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact hsum

/-- **Lemma B.2's lower tail, Rademacher case.**

`μ{ω | ∃ h ∈ [h₀, h₀+r), W + 4AA < −ℓog‖F(σ+ih)‖} ≤ C·exp(AA − 2W)`, the counterpart of
`RMF.IsSteinhausRMF.exists_measure_exists_lt_le`.

It reduces to the upper tail as the Steinhaus one does: negation is a Rademacher symmetry
(`RMF.map_neg_rademacherLaw`), so `RMF.IsRademacherPrimeValues.neg` reflects the family, and
`RMF.neg_log_norm_randomEulerProductIco_sqfree_le` dominates `−ℓog‖F(X)‖` by `ℓog‖F(−X)‖ + 4AA`
pointwise on the unimodularity set.  No chaining is redone, and the interval `[h₀, h₀+r)` passes
straight through, since Lemma B.2 already carries its base. -/
theorem IsRademacherRMF.exists_measure_exists_lt_le {Ω : Type*} [MeasurableSpace Ω] {σ₀ Λ : ℝ}
    (hσ₀ : 1 / 3 < σ₀) (hΛ : 1 ≤ Λ) :
    ∃ C > 0, ∀ (f : Ω → ArithmeticFunction ℂ) (μ : Measure Ω), IsRademacherRMF f μ →
      ∀ (σ W r h₀ : ℝ) (y₀ y : ℕ), σ₀ ≤ σ → 0 < r → 0 ≤ W →
        1 ≤ (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        W ≤ Λ * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) →
        r * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ) * Real.log p) ≤ Λ →
          μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
              W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
                < -Real.log ‖randomEulerProductIco f y₀ y (heightLine σ h) ω‖}
            ≤ C * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * W) := by
  obtain ⟨C, hC, H⟩ := IsRademacherRMF.exists_measure_exists_gt_le (Ω := Ω) hσ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro f μ hf σ W r h₀ y₀ y hσ hr hW hA1 hWΛ hrP
  obtain ⟨X, hX, rfl⟩ := hf.exists_primeValues
  haveI := hX.isProbabilityMeasure
  have hσ13 : (1 : ℝ) / 3 ≤ σ := by linarith
  have hX' := hX.neg
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1} := ⟨_, rfl⟩
  have hGnull : μ Gᶜ = 0 := by
    have h := ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw y₀ y
    rw [ae_iff] at h
    rw [hGdef, Set.compl_setOf]
    exact h
  have hsub : G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      ⊆ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} := by
    rintro ω ⟨hωG, h, hh, hlt⟩
    have hωu : ∀ p ∈ primesIco y₀ y, ‖X p ω‖ ≤ 1 := by rw [hGdef] at hωG; exact hωG
    have hre : (heightLine σ h).re = σ := re_heightLine σ h
    have hrefl := neg_log_norm_randomEulerProductIco_sqfree_le (X := X) (y := y)
      (s := heightLine σ h) (by rw [hre]; exact hσ13) hωu
    rw [hre] at hrefl
    exact ⟨h, hh, by linarith⟩
  calc μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
        W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
          < -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) y₀ y
            (heightLine σ h) ω‖}
      = μ.real (G ∩ {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W + 4 * (∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ))
            < -Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              y₀ y (heightLine σ h) ω‖}) := by
        unfold MeasureTheory.Measure.real
        rw [measure_eq_measure_inter_of_compl_null hGnull _]
    _ ≤ μ.real {ω | ∃ h ∈ Set.Ico h₀ (h₀ + r),
          W < Real.log ‖randomEulerProductIco (fun ω => squarefreeExtension fun p =>
            (-1 : ℂ) * X p ω) y₀ y (heightLine σ h) ω‖} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ C * Real.exp ((∑ p ∈ primesIco y₀ y, (p : ℝ) ^ (-2 * σ)) - 2 * W) :=
        H _ μ hX'.isRademacherRMF σ W r h₀ y₀ y hσ hr hW hA1 hWΛ hrP

end RMF
