/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.SmallPrimesAbove
import RMF.Probability.LadderVille
import RMF.Probability.BallotReversal

/-!
# (C3)*: the twisted tilt, Ville, and the skeleton

The low factor of the explicit per-scale estimate is `E[1_L‖F_low(s_h)‖²‖F_low(σ)‖^{2q-2}]`,
`L = RMF.halfLadder X σ k₁ k`, and (C3)* bounds it below by a constant times
`E‖F_low(σ)‖^{2q}`.  This file bounds it below by `E‖F_low(σ)‖^{2q}` times a ladder probability
under one tilt; the constant is made explicit in `RMF/UniformLower/C3Explicit.lean`.

* **The twisted tilt** `RMF.twistMeasure`: `μ` tilted by
  `∑_{a ≤ p < b}[2 log‖1 + X_p p^{-(σ+ih)}‖ + (2q - 2) log‖1 + X_p p^{-σ}‖]` (`σ` on the line
  `½ + σ`).  A probability measure under which the values at the primes stay independent
  (`RMF.iIndepFun_twistMeasure`), hence so do the blocks (`RMF.iIndepFun_halfBlock_twistMeasure`),
  each with its own tilted two-point law (`RMF.map_twistMeasure_of_mem`), and whose density is
  the twist (`RMF.setIntegral_twistQ_eq_mul_twistMeasure`):
  `E[1_A‖F(s_h)‖²‖F(σ)‖^{2q-2}] = E[‖F(s_h)‖²‖F(σ)‖^{2q-2}]·P_tw(A)`.
* **The ladder in reversed time** (`RMF.halfLadder_eq_ladderEvent`): with `Y_i` the block
  `K - 1 - i` (`RMF.halfLadderStep`, the top block first), `L = {T_1, …, T_K > 0}`,
  `T_i = Y_0 + … + Y_{i-1}`, `K = k - k₁`.
* **The skeleton** (`RMF.le_setIntegral_halfLadder_twistQ_ville`): the head `[a, scaleCut k₁)`
  and the ladder `[scaleCut k₁, scaleCut k)` factorise; the head is bounded by
  `RMF.integral_rpow_norm_randomEulerProductIco_le_twistQ`, the ladder part is `Z·P_tw(L)` with
  `Z ≥ E‖F_ladder(σ)‖^{2q}` by the same lemma, and `P_tw(L)` by the Ville ladder bound
  `RMF.le_measureReal_ladderEvent`:
  `E‖F(σ)‖^{2q}·E_tw[1{T_1, …, T_m > 0}(1 - F_m e^{-tT_m})] ≤ E[1_L‖F(s_h)‖²‖F(σ)‖^{2q-2}]`.
  `RMF.le_setIntegral_halfLadder_twistQ_ville_of_le` is the form
  `RMF.le_setIntegral_halfLadder_twistQ_explicit` instantiates.
-/

open MeasureTheory ProbabilityTheory

namespace RMF

section Defs

variable {Ω : Type*}

/-- The local exponent of the twisted tilt at the prime `p`:
`2 log‖1 + z p^{-(σ+ih)}‖ + (2q - 2) log‖1 + z p^{-σ}‖`, with `σ` on the line `½ + σ`. -/
noncomputable def twistLocal (σ h q : ℝ) (p : Nat.Primes) (z : ℂ) : ℝ :=
  2 * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ h)) z
    + (2 * q - 2) * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) z

lemma measurable_twistLocal (σ h q : ℝ) (p : Nat.Primes) : Measurable (twistLocal σ h q p) :=
  ((measurable_localLogAdd _).const_mul 2).add ((measurable_localLogAdd _).const_mul _)

/-- **The step of the reversed ladder walk**: `RMF.halfBlock X k₁ σ 0 (K - 1 - i)` for
`i < K = k - k₁`, the top block first (`RMF.halfLadderStep_of_lt`).  Written through
`RMF.revIdx`, so that the whole family is a reindexing of the blocks. -/
noncomputable def halfLadderStep (X : ℕ → Ω → ℂ) (σ : ℝ) (k₁ k i : ℕ) (ω : Ω) : ℝ :=
  halfBlock X k₁ σ 0 (revIdx (k - k₁) i) ω

lemma halfLadderStep_of_lt (X : ℕ → Ω → ℂ) (σ : ℝ) {k₁ k i : ℕ} (hi : i < k - k₁) :
    halfLadderStep X σ k₁ k i = halfBlock X k₁ σ 0 (k - k₁ - 1 - i) := by
  funext ω
  simp only [halfLadderStep, revIdx, if_pos hi]

/-- **The ladder event in reversed time**: `k` is a strict ladder time of the walk from `k₁`
exactly when every suffix `T_i = S_K - S_{K-i}`, `1 ≤ i ≤ K = k - k₁`, is positive
(`RMF.walk_reverse`). -/
lemma halfLadder_eq_ladderEvent (X : ℕ → Ω → ℂ) (σ : ℝ) (k₁ k : ℕ) :
    halfLadder X σ k₁ k = ladderEvent (halfLadderStep X σ k₁ k) (k - k₁) := by
  ext ω
  have hrev : ∀ i, i ≤ k - k₁ → walk (halfLadderStep X σ k₁ k) i ω
      = walk (halfBlock X k₁ σ 0) (k - k₁) ω - walk (halfBlock X k₁ σ 0) (k - k₁ - i) ω := by
    intro i hi
    have h := walk_reverse (halfBlock X k₁ σ 0) hi ω
    have hneg : walk (fun m => -halfBlock X k₁ σ 0 (revIdx (k - k₁) m)) i ω
        = -walk (halfLadderStep X σ k₁ k) i ω := by
      simp only [walk_apply, halfLadderStep, Pi.neg_apply, Finset.sum_neg_distrib]
    linarith
  simp only [halfLadder, Set.mem_setOf_eq]
  rw [mem_ladderEvent]
  constructor
  · intro hL i hi1 hiK
    rw [hrev i hiK]
    have := hL (k - k₁ - i) (by omega)
    linarith
  · intro hL j hj
    have := hL (k - k₁ - j) (by omega) (by omega)
    rw [hrev _ (by omega), show k - k₁ - (k - k₁ - j) = j by omega] at this
    linarith

end Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The twisted tilt** over the primes of `[a, b)`: `μ` tilted by the sum of
`RMF.twistLocal σ h q p (X_p)` over `a ≤ p < b`.  Its density is
`‖F_{[a,b)}(σ+ih)‖²‖F_{[a,b)}(σ)‖^{2q-2}`, normalised
(`RMF.setIntegral_twistQ_eq_mul_twistMeasure`). -/
noncomputable def twistMeasure (X : ℕ → Ω → ℂ) (μ : Measure Ω) (a b : ℕ) (σ h q : ℝ) :
    Measure Ω :=
  μ.tilted fun ω => ∑ p ∈ primesIcoSub a b, twistLocal σ h q p (X (p : ℕ) ω)

variable {X : ℕ → Ω → ℂ} {μ : Measure Ω}

lemma twistMeasure_absolutelyContinuous (a b : ℕ) (σ h q : ℝ) :
    twistMeasure X μ a b σ h q ≪ μ :=
  tilted_absolutelyContinuous μ _

/-- **Each local weight of the twisted tilt is integrable**: on the circle the local exponent is
bounded, by `RMF.abs_localLogAdd_le`. -/
lemma integrable_exp_twistLocal (hX : IsRademacherPrimeValues X μ) {σ : ℝ} (hσ : 0 ≤ σ)
    (h q : ℝ) (p : Nat.Primes) :
    Integrable (fun ω => Real.exp (twistLocal σ h q p (X (p : ℕ) ω))) μ := by
  have hprob := hX.isProbabilityMeasure
  have hw : ∀ h' : ℝ, ‖((p : ℕ) : ℂ) ^ (-shiftLine σ h')‖ < 1 := fun h' =>
    norm_prime_cpow_neg_lt_one p.2 (by rw [re_shiftLine]; linarith)
  have hae : ∀ᵐ ω ∂μ, ‖X (p : ℕ) ω‖ = 1 := by
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  refine (memLp_top_of_bound
    (((measurable_twistLocal σ h q p).comp (hX.measurable (p : ℕ) p.2)).exp.aestronglyMeasurable)
    (Real.exp (2 * Real.log ((1 - ‖((p : ℕ) : ℂ) ^ (-shiftLine σ h)‖)⁻¹)
      + |2 * q - 2| * Real.log ((1 - ‖((p : ℕ) : ℂ) ^ (-shiftLine σ 0)‖)⁻¹))) ?_).integrable
    le_top
  filter_upwards [hae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.2 ?_
  have h1 := abs_localLogAdd_le hω le_rfl (hw h)
  have h2 := abs_localLogAdd_le hω le_rfl (hw 0)
  have h2' : (2 * q - 2) * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
      ≤ |2 * q - 2| * Real.log ((1 - ‖((p : ℕ) : ℂ) ^ (-shiftLine σ 0)‖)⁻¹) :=
    le_trans (le_abs_self _) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  simp only [Function.comp_apply, twistLocal]
  linarith [(abs_le.1 h1).2]

/-- **The values at the primes stay independent under the twisted tilt**: its exponent is a sum
of functions of the individual values (`RMF.iIndepFun_tilted_finsetSum`). -/
theorem iIndepFun_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (h q : ℝ) :
    iIndepFun (fun p : Nat.Primes => X (p : ℕ)) (twistMeasure X μ a b σ h q) :=
  iIndepFun_tilted_finsetSum (𝓧 := fun _ : Nat.Primes => ℂ)
    (X := fun p : Nat.Primes => X (p : ℕ)) (g := twistLocal σ h q)
    hX.iIndep (fun p => hX.measurable (p : ℕ) p.2) (measurable_twistLocal σ h q)
    (fun p _ => integrable_exp_twistLocal hX hσ h q p)

/-- **The twisted tilt is a probability measure.** -/
theorem isProbabilityMeasure_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (h q : ℝ) : IsProbabilityMeasure (twistMeasure X μ a b σ h q) :=
  (iIndepFun_twistMeasure hX a b hσ h q).isProbabilityMeasure

/-- **The blocks stay independent under the twisted tilt**, at any offset `θ` and any point
`σ' + ih'`: they are sums over the disjoint `RMF.primeBlockSub θ m`
(`RMF.iIndepFun_finsetSum_of_pairwiseDisjoint`). -/
theorem iIndepFun_halfBlock_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (h q θ σ' h' : ℝ) :
    iIndepFun (fun m => halfBlock X θ σ' h' m) (twistMeasure X μ a b σ h q) :=
  iIndepFun_finsetSum_of_pairwiseDisjoint
    (fun p : Nat.Primes => (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2))
    ((iIndepFun_twistMeasure hX a b hσ h q).comp
      (fun (p : Nat.Primes) (z : ℂ) => localLogAdd (((p : ℕ) : ℂ) ^ (-(shiftLine σ' h'))) z)
      fun _ => measurable_localLogAdd _)
    (pairwise_disjoint_primeBlockSub θ)

/-- **The law of `X_p` under the twisted tilt**, for a prime of `[a, b)`: the Rademacher law
tilted by `RMF.twistLocal σ h q p` (`RMF.map_tilted_finsetSum_of_mem`). -/
theorem map_twistMeasure_of_mem (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (h q : ℝ) {p : Nat.Primes} (hp : p ∈ primesIcoSub a b) :
    (twistMeasure X μ a b σ h q).map (X (p : ℕ)) = rademacherLaw.tilted (twistLocal σ h q p) := by
  rw [twistMeasure, map_tilted_finsetSum_of_mem (𝓧 := fun _ : Nat.Primes => ℂ)
      (X := fun r : Nat.Primes => X (r : ℕ)) (g := twistLocal σ h q)
      hX.iIndep (fun r => hX.measurable (r : ℕ) r.2) (measurable_twistLocal σ h q)
      (fun r _ => integrable_exp_twistLocal hX hσ h q r) hp,
    (hX.hasLaw (p : ℕ) p.2).map_eq]

/-- **The density of the twisted tilt is the twist.**  For measurable `A`,
`E[1_A‖F_{[a,b)}(σ+ih)‖²‖F_{[a,b)}(σ)‖^{2q-2}]
  = E[‖F_{[a,b)}(σ+ih)‖²‖F_{[a,b)}(σ)‖^{2q-2}]·P_tw(A)`.
Off a null set the twist is `exp` of the tilt exponent: `‖1 + X_p p^{-σ}‖ ≥ 1 - p^{-½-σ} > 0`, so
the negative power `2q - 2` is harmless. -/
theorem setIntegral_twistQ_eq_mul_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) (h q : ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ h) ω‖ ^ 2
          * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
            (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ)
        * (twistMeasure X μ a b σ h q).real A := by
  classical
  have hprob := hX.isProbabilityMeasure
  -- the twist is `exp` of the tilt exponent, off a null set
  have hae : (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ h) ω‖ ^ 2
        * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b
          (shiftLine σ 0) ω‖ ^ (2 * q - 2))
      =ᵐ[μ] fun ω => Real.exp (∑ p ∈ primesIcoSub a b, twistLocal σ h q p (X (p : ℕ) ω)) := by
    filter_upwards [ae_forall_norm_le_one_primesIco hX norm_le_one_rademacherLaw a b] with ω hω
    rw [twistQ_eq_prod, Real.exp_sum]
    have hsub : ∏ p ∈ primesIcoSub a b, Real.exp (twistLocal σ h q p (X (p : ℕ) ω))
        = ∏ p ∈ primesIco a b, Real.exp (2 * localLogAdd ((p : ℂ) ^ (-shiftLine σ h)) (X p ω)
            + (2 * q - 2) * localLogAdd ((p : ℂ) ^ (-shiftLine σ 0)) (X p ω)) :=
      Finset.prod_subtype_of_mem (fun n : ℕ =>
          Real.exp (2 * localLogAdd ((n : ℂ) ^ (-shiftLine σ h)) (X n ω)
            + (2 * q - 2) * localLogAdd ((n : ℂ) ^ (-shiftLine σ 0)) (X n ω)))
        fun _ hp => prime_of_mem_primesIco hp
    rw [hsub]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_primesIco hp
    have hre : ∀ h' : ℝ, 0 < (shiftLine σ h').re := fun h' => by rw [re_shiftLine]; linarith
    have hpos1 : 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ :=
      norm_one_add_mul_pos_of_le_one (hω p hp) (norm_prime_cpow_neg_lt_one hpp (hre h))
    have hpos2 : 0 < ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ 0)‖ :=
      norm_one_add_mul_pos_of_le_one (hω p hp) (norm_prime_cpow_neg_lt_one hpp (hre 0))
    have hsq : 2 * Real.log ‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖
        = Real.log (‖1 + X p ω * (p : ℂ) ^ (-shiftLine σ h)‖ ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [Real.exp_add, localLogAdd, localLogAdd, Real.rpow_def_of_pos hpos2, hsq,
      Real.exp_log (pow_pos hpos1 2), mul_comm (Real.log _) (2 * q - 2)]
  have hint : Integrable
      (fun ω => Real.exp (∑ p ∈ primesIcoSub a b, twistLocal σ h q p (X (p : ℕ) ω))) μ := by
    by_contra hni
    have h0 : twistMeasure X μ a b σ h q = 0 := tilted_of_not_integrable hni
    have h1 := (isProbabilityMeasure_twistMeasure hX a b hσ h q).measure_univ
    rw [h0] at h1
    simp at h1
  have hZpos := integral_exp_pos hint
  rw [setIntegral_congr_ae hA (hae.mono fun ω hω _ => hω), integral_congr_ae hae]
  have hPA : (twistMeasure X μ a b σ h q).real A
      = (∫ ω in A, Real.exp (∑ p ∈ primesIcoSub a b, twistLocal σ h q p (X (p : ℕ) ω)) ∂μ)
        / ∫ ω, Real.exp (∑ p ∈ primesIcoSub a b, twistLocal σ h q p (X (p : ℕ) ω)) ∂μ := by
    rw [measureReal_def, twistMeasure, tilted_apply_eq_ofReal_integral' _ hA,
      ENNReal.toReal_ofReal (setIntegral_nonneg hA fun ω _ =>
        div_nonneg (Real.exp_pos _).le hZpos.le), integral_div]
  rw [hPA, mul_div_cancel₀ _ hZpos.ne']

/-- **A block's exponential moments are finite** under any finite `P ≪ μ`: the values are
unimodular `μ`-almost surely, so the block is bounded (`RMF.abs_localLogAdd_le`). -/
lemma integrable_exp_mul_halfBlock_of_absolutelyContinuous (hX : IsRademacherPrimeValues X μ)
    {P : Measure Ω} [IsFiniteMeasure P] (hP : P ≪ μ) (θ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (h c : ℝ)
    (m : ℕ) : Integrable (fun ω => Real.exp (c * halfBlock X θ σ h m ω)) P := by
  have hw : ∀ p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖ < 1 := fun p =>
    norm_prime_cpow_neg_lt_one p.2 (by rw [re_shiftLine]; linarith)
  have hae : ∀ᵐ ω ∂μ, ∀ p ∈ primeBlockSub θ m, ‖X (p : ℕ) ω‖ = 1 := by
    refine (Filter.eventually_all_finset _).2 fun p _ => ?_
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 norm_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun measurable_norm measurable_const)
  refine (memLp_top_of_bound
    ((measurable_halfBlock hX θ σ h m).const_mul c).exp.aestronglyMeasurable
    (Real.exp (|c| * ∑ p ∈ primeBlockSub θ m,
      Real.log ((1 - ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖)⁻¹))) ?_).integrable le_top
  filter_upwards [hP.ae_le hae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.2 ?_
  have hblock : |halfBlock X θ σ h m ω|
      ≤ ∑ p ∈ primeBlockSub θ m, Real.log ((1 - ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ h))‖)⁻¹) := by
    unfold halfBlock
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun p hp => abs_localLogAdd_le (hω p hp) le_rfl (hw p))
  calc c * halfBlock X θ σ h m ω ≤ |c * halfBlock X θ σ h m ω| := le_abs_self _
    _ = |c| * |halfBlock X θ σ h m ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hblock (abs_nonneg c)

/-- **The real-point moment factorises across a cut**:
`E‖F_{[a,c)}(s)‖^r = E‖F_{[a,b)}(s)‖^r·E‖F_{[b,c)}(s)‖^r` for `a ≤ b ≤ c`, prime by prime. -/
lemma integral_rpow_norm_randomEulerProductIco_split (hX : IsRademacherPrimeValues X μ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (s : ℂ) (r : ℝ) :
    ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a c s ω‖ ^ r ∂μ
      = (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a b s ω‖ ^ r
          ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) b c s ω‖ ^ r
            ∂μ := by
  classical
  have hm : ∀ p : ℕ, Measurable fun z : ℂ => ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r :=
    fun p => ((measurable_const.add (measurable_id.mul measurable_const)).norm).pow_const _
  have hI : ∀ a' b' : ℕ,
      ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a' b' s ω‖ ^ r ∂μ
        = ∏ p ∈ primesIco a' b', ∫ z, ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r ∂rademacherLaw := by
    intro a' b'
    rw [integral_congr_ae (Filter.Eventually.of_forall
        (rpow_norm_randomEulerProductIco_eq_prod (X := X) a' b' s r)),
      hX.integral_prod (fun p hp => prime_of_mem_primesIco hp)
        (fun p z => ‖1 + z * (p : ℂ) ^ (-s)‖ ^ r) fun p _ => (hm p).aestronglyMeasurable]
  rw [hI, hI, hI, ← primesIco_union hab hbc, Finset.prod_union (disjoint_primesIco a b c)]

/-- **(C3)*, the skeleton.**  For `q ≤ 1`, `σ ≥ 0`, `a ≤ scaleCut k₁`, `k₁ < k`, `m ≤ K = k - k₁`,
`t ≥ 0` and any `h`; with `P_tw` the twisted tilt over the ladder primes
`[scaleCut k₁, scaleCut k)`, `Y_i = RMF.halfLadderStep X σ k₁ k i` (the block `K - 1 - i`) and
`T_i = Y_0 + … + Y_{i-1}`:
`E‖F_{[a,k)}(σ)‖^{2q}·E_tw[1{T_1, …, T_m > 0}(1 - F_m e^{-tT_m})]
  ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(σ+ih)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`,
`F_m = ∏_{m ≤ i < K} max(1, E_tw e^{-tY_i})`. -/
theorem le_setIntegral_halfLadder_twistQ_ville (hX : IsRademacherPrimeValues X μ)
    {a k₁ k m : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk : k₁ < k) (hm : m ≤ k - k₁) {σ h q t : ℝ}
    (hσ : 0 ≤ σ) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
        (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ)
      * ∫ ω in ladderEvent (halfLadderStep X σ k₁ k) m,
          (1 - (∏ i ∈ Finset.Ico m (k - k₁), max 1 (∫ ω', Real.exp
              (-(t * halfLadderStep X σ k₁ k i ω'))
              ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q)))
            * Real.exp (-(t * walk (halfLadderStep X σ k₁ k) m ω)))
          ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q)
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  classical
  haveI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  haveI := isProbabilityMeasure_twistMeasure hX (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) hσ h q
  have hk₁k : k₁ ≤ k := hk.le
  have hc1k : scaleCut (k₁ : ℝ) ≤ scaleCut (k : ℝ) := scaleCut_mono (by exact_mod_cast hk₁k)
  -- the Ville ladder bound under the twisted tilt
  have hYm : ∀ i, Measurable (halfLadderStep X σ k₁ k i) :=
    fun i => measurable_halfBlock hX _ σ 0 _
  have hYind : iIndepFun (halfLadderStep X σ k₁ k)
      (twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q) := by
    have hrev := (iIndepFun_halfBlock_twistMeasure hX (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) hσ
      h q (k₁ : ℝ) σ 0).precomp (revIdx_injective (k - k₁))
    exact hrev
  have hYint : ∀ i, m ≤ i → i < k - k₁ → Integrable
      (fun ω => Real.exp (-(t * halfLadderStep X σ k₁ k i ω)))
      (twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q) := by
    intro i _ _
    refine (integrable_exp_mul_halfBlock_of_absolutelyContinuous hX
      (twistMeasure_absolutelyContinuous _ _ σ h q) (k₁ : ℝ) hσ 0 (-t)
      (revIdx (k - k₁) i)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [halfLadderStep, neg_mul]
  have hville := le_measureReal_ladderEvent hYm hYind ht hm hYint
  rw [← halfLadder_eq_ladderEvent] at hville
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
    (measurableSet_primeAlgebra_halfLadder σ hk₁k le_rfl)
    (measurable_twistPolyQ q (primesIco a (scaleCut (k₁ : ℝ))) σ h)
    (measurable_twistPolyQ q (primesIco (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ))) σ h)
  rw [Set.univ_inter, setIntegral_univ] at hsplit
  rw [setIntegral_congr_fun (measurableSet_halfLadder hX σ k₁ k) (fun ω _ => hpt ω), hsplit]
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
    (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _) measureReal_nonneg hhead hZ
    hville

/-- **(C3)*, the skeleton in the form the explicit bound instantiates**
(`RMF.le_setIntegral_halfLadder_twistQ_explicit`).  Under the hypotheses of
`RMF.le_setIntegral_halfLadder_twistQ_ville`, with upper bounds `E_tw e^{-tY_i} ≤ f_i` for
`m ≤ i < K` and a lower bound
`c ≤ E_tw[1{T_1, …, T_m > 0}(1 - (∏_{m ≤ i < K} max(1, f_i))e^{-tT_m})]`:
`c·E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(σ+ih)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_ville_of_le (hX : IsRademacherPrimeValues X μ)
    {a k₁ k m : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk : k₁ < k) (hm : m ≤ k - k₁) {σ h q t : ℝ}
    (hσ : 0 ≤ σ) (hq1 : q ≤ 1) (ht : 0 ≤ t) {f : ℕ → ℝ}
    (hf : ∀ i, m ≤ i → i < k - k₁ → ∫ ω, Real.exp (-(t * halfLadderStep X σ k₁ k i ω))
      ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q) ≤ f i)
    {c : ℝ} (hc : c ≤ ∫ ω in ladderEvent (halfLadderStep X σ k₁ k) m,
      (1 - (∏ i ∈ Finset.Ico m (k - k₁), max 1 (f i))
        * Real.exp (-(t * walk (halfLadderStep X σ k₁ k) m ω)))
      ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q)) :
    c * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
        (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  haveI := isProbabilityMeasure_twistMeasure hX (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) hσ h q
  have hskel := le_setIntegral_halfLadder_twistQ_ville hX ha hk hm (h := h) hσ hq1 ht
  have hYm : ∀ i, Measurable (halfLadderStep X σ k₁ k i) :=
    fun i => measurable_halfBlock hX _ σ 0 _
  have hE0 : 0 ≤ ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
      (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hFF : (∏ i ∈ Finset.Ico m (k - k₁), max 1 (∫ ω', Real.exp
        (-(t * halfLadderStep X σ k₁ k i ω'))
        ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q)))
      ≤ ∏ i ∈ Finset.Ico m (k - k₁), max 1 (f i) :=
    Finset.prod_le_prod (fun i _ => le_trans zero_le_one (le_max_left _ _)) fun i hi =>
      max_le_max_left 1 (hf i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2)
  have hmono := le_trans hc (setIntegral_mono_on
    (integrableOn_ladderEvent_one_sub_mul_exp hYm ht _ m)
    (integrableOn_ladderEvent_one_sub_mul_exp hYm ht _ m) (measurableSet_ladderEvent hYm m)
    fun ω _ => sub_le_sub_left (mul_le_mul_of_nonneg_right hFF (Real.exp_pos _).le) 1)
  calc c * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
        (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ (∫ ω in ladderEvent (halfLadderStep X σ k₁ k) m,
          (1 - (∏ i ∈ Finset.Ico m (k - k₁), max 1 (∫ ω', Real.exp
              (-(t * halfLadderStep X σ k₁ k i ω'))
              ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q)))
            * Real.exp (-(t * walk (halfLadderStep X σ k₁ k) m ω)))
          ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q))
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
          (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ :=
        mul_le_mul_of_nonneg_right hmono hE0
    _ = _ := mul_comm _ _
    _ ≤ _ := hskel

end RMF
