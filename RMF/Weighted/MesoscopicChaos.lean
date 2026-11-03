/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.RademacherChaosMoment
import RMF.Weighted.Mesoscopic
import RMF.Weighted.EulerMomentBand

/-!
# The mesoscopic chaos estimate: the two propositions

`RMF/Weighted/Mesoscopic.lean` reduces one `e`-adic block of `Z_m` to a product of two factors
(`RMF.integral_rpow_setIntegral_normSq_split_le`),

`E[(∫_{B}‖F_y(½+σ+it)‖²dt)^q] ≤ e^{143800q}·E‖F_z(½+σ)‖^{2q}·E[(∫_{B}‖F_{(z,y]}(½+σ+it)‖²dt)^q]`,

and a moment bound for the Euler product at a point bounds the first
(`RMF/Weighted/MesoscopicBlock.lean`).  This file bounds the second, the mesoscopic chaos estimate
(`RMF.exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher`, and at a
shift of either sign its `_signed` form).

## The two propositions

They are Harper's Key Propositions 3 and 4, the Rademacher forms of his Key Propositions 1 and 2
(Harper, *Moments of random multiplicative functions, I*, arXiv:1703.06654), transported from the
unit window to a block: Proposition I, the barriered first moment, saves a factor
`min{1, a/√J}`; Proposition II bounds the probability that the barrier fails.
`RMF.integral_rpow_le_of_goodSets` turns them into the `q`-th moment through the
geometric family of levels `a_k = k/(1-q)`, so `q` enters neither proposition.  The transfer
across the prime split (`RMF.setIntegral_normSq_randomEulerProductIco_le_of_le`) is an
independence identity: the barrier constrains only primes above `z`, so `E‖F_z(s)‖²` cancels.

## What a block looks like

Fix the window `B = (T/e, T]` and the split `z` with `1 ≤ T·log z ≤ 2`.  The primes left in the
product are `(z, y]`, and the `e`-adic scales between them are `RMF.blockScale θ m` for
`m = 0, …, J`, with `blockScale θ 0 ≈ z` and `blockScale θ J ≈ y`, so `J ≈ log(T·log y)`: the
**depth** of the block, which is what the unit window's `log log x` becomes.

## The height condition

Both propositions carry the unit-window chain's `(2·Im s)² ≤ e^θ`.  The split needs only
`e^θ ≥ log z`, so the offset may sit a bounded factor higher:
`RMF.exists_harperOffset_at_split_scale` picks `D` with `K ≤ T·e^{harperOffset D x} ≤ e^4·K`, and
then `(2h)² ≤ e^θ` for every `h ≤ T` (`RMF.sq_two_mul_le_exp_harperOffset`), at the cost of a
constant in the depth.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### The barrier at depth `J` -/

/-- **The good event for a mesoscopic block**, at height `s` and level `a`: the walk over the
`e`-adic prime scales `RMF.blockScale θ m` stays in `[-a - c·ℓ, a + ℓ + hf ℓ]` for every depth
`r ≤ ℓ ≤ J`.  This is `RMF.harperGoodRangeAdd` with three parameters freed: the offset `θ`
instead of `RMF.harperOffset D x`, the depth `J` instead of `RMF.harperBlockCount D x`, and the
start `r` instead of `⌈a/4⌉₊`. -/
def mesoGood {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (θ c : ℝ) (J r : ℕ) (a : ℝ) (hf : ℕ → ℝ)
    (s : ℂ) : Set Ω' :=
  {ω | ∀ ℓ, r ≤ ℓ → ℓ ≤ J →
    walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
      localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (Y ((p : Nat.Primes) : ℕ) ω)) ℓ ω
      ∈ Set.Icc (-a - c * (ℓ : ℝ)) (a + (ℓ : ℝ) + hf ℓ)}

/-- The good event is measurable — the same `RMF.measurableSet_freeStartBarrier` the unit-window
good sets use, since freeing the offset and the depth changes nothing it looks at. -/
lemma measurableSet_mesoGood {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → ℂ}
    {ν : Measure Ω'} (hY : IsRademacherPrimeValues Y ν) (θ c : ℝ) (J r : ℕ) (a : ℝ)
    (hf : ℕ → ℝ) (s : ℂ) :
    MeasurableSet (mesoGood Y θ c J r a hf s) :=
  measurableSet_freeStartBarrier (fun _ => Finset.measurable_sum _ fun p _ =>
    (measurable_localLogAdd _).comp (hY.measurable ((p : Nat.Primes) : ℕ) p.2)) _ _ _ _

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The barrier as a function of the prime values

The block split leaves `RMF.randomEulerProductIco z n`, not the full product, so Proposition I
has to be about the *high* factor.  It is the same statement: the low primes cancel out of the
ratio, because the barrier only constrains primes above `z`.

Making that precise is the only real work.  `RMF.IsIIDPrimeValues.integral_mul_split` asks for
each factor as a measurable function of the **tuple** of values at a finite set of primes, and
the barrier is a set, not a product.  `RMF.tupleWalk` and `RMF.tupleGood` are the barrier in that
presentation.  The sum in `RMF.tupleWalk` runs over the whole of `S` with a filter picking out
the `m`-th `e`-adic block, so one definition serves every `S` containing the blocks and no
coercion between `Finset ℕ` and `Finset Nat.Primes` appears in the definition — only in the one
lemma that identifies it with `RMF.walk`. -/

open Classical in
/-- The block walk to depth `ℓ`, as a function of the values at a finite set `S` of primes. -/
noncomputable def tupleWalk (S : Finset ℕ) (θ : ℝ) (s : ℂ) (ℓ : ℕ) (v : ↥S → ℂ) : ℝ :=
  ∑ m ∈ Finset.range ℓ,
    ∑ p ∈ S.attach.filter fun p : ↥S =>
        blockScale θ m < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ blockScale θ (m + 1),
      localLogAdd ((p.1 : ℂ) ^ (-s)) (v p)

lemma measurable_tupleWalk (S : Finset ℕ) (θ : ℝ) (s : ℂ) (ℓ : ℕ) :
    Measurable (tupleWalk S θ s ℓ) :=
  Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun p _ =>
    (measurable_localLogAdd _).comp (measurable_pi_apply p)

omit [MeasurableSpace Ω] in
/-- **The tuple presentation is the walk**, as soon as `S` holds the blocks below `ℓ`.

The two sums run over the same primes in two index types — `↥S` and `Nat.Primes` — and
`RMF.mem_primeBlockSub` is what matches the filter to the block. -/
lemma tupleWalk_eq_walk {X : ℕ → Ω → ℂ} {S : Finset ℕ} (hSp : ∀ p ∈ S, Nat.Prime p)
    {θ : ℝ} {s : ℂ} {ℓ : ℕ}
    (hS : ∀ m, m < ℓ → ∀ p ∈ primeBlockSub θ m, ((p : Nat.Primes) : ℕ) ∈ S) (ω : Ω) :
    tupleWalk S θ s ℓ (fun p => X (p : ℕ) ω)
      = walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X ((p : Nat.Primes) : ℕ) ω)) ℓ ω := by
  classical
  rw [walk_apply, tupleWalk]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  set g : ℕ → ℝ := fun k => localLogAdd ((k : ℂ) ^ (-s)) (X k ω) with hg
  set cond : ℕ → Prop := fun k =>
    blockScale θ m < (k : ℝ) ∧ (k : ℝ) ≤ blockScale θ (m + 1) with hcond
  have himg : (primeBlockSub θ m).image (fun p : Nat.Primes => (p : ℕ)) = S.filter cond := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hS m hm p hp, (mem_primeBlockSub.1 hp).1, (mem_primeBlockSub.1 hp).2⟩
    · rintro ⟨hk, h1, h2⟩
      exact ⟨⟨k, hSp k hk⟩, mem_primeBlockSub.2 ⟨h1, h2⟩, rfl⟩
  have hinj : ∀ p ∈ primeBlockSub θ m, ∀ q ∈ primeBlockSub θ m,
      ((p : Nat.Primes) : ℕ) = ((q : Nat.Primes) : ℕ) → p = q :=
    fun p _ q _ h => Subtype.ext h
  calc (∑ p ∈ S.attach.filter fun p : ↥S =>
          blockScale θ m < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ blockScale θ (m + 1),
            localLogAdd ((p.1 : ℂ) ^ (-s)) (X p.1 ω))
      = ∑ p ∈ S.attach, if cond p.1 then g p.1 else 0 := by
        rw [Finset.sum_filter]
    _ = ∑ k ∈ S, if cond k then g k else 0 :=
        Finset.sum_attach S fun k => if cond k then g k else 0
    _ = ∑ k ∈ S.filter cond, g k := (Finset.sum_filter _ _).symm
    _ = ∑ k ∈ (primeBlockSub θ m).image (fun p : Nat.Primes => (p : ℕ)), g k := by rw [himg]
    _ = ∑ p ∈ primeBlockSub θ m, g ((p : Nat.Primes) : ℕ) := Finset.sum_image hinj

open Classical in
/-- The barrier event, as a subset of tuple space. -/
def tupleGood (S : Finset ℕ) (θ c : ℝ) (J r : ℕ) (a : ℝ) (hf : ℕ → ℝ) (s : ℂ) :
    Set (↥S → ℂ) :=
  {v | ∀ ℓ, r ≤ ℓ → ℓ ≤ J →
    tupleWalk S θ s ℓ v ∈ Set.Icc (-a - c * (ℓ : ℝ)) (a + (ℓ : ℝ) + hf ℓ)}

lemma measurableSet_tupleGood (S : Finset ℕ) (θ c : ℝ) (J r : ℕ) (a : ℝ) (hf : ℕ → ℝ)
    (s : ℂ) : MeasurableSet (tupleGood S θ c J r a hf s) := by
  have hrw : tupleGood S θ c J r a hf s
      = ⋂ ℓ ∈ Set.Icc r J,
          (tupleWalk S θ s ℓ) ⁻¹' Set.Icc (-a - c * (ℓ : ℝ)) (a + (ℓ : ℝ) + hf ℓ) := by
    ext v
    simp only [tupleGood, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun h ℓ hℓ => h ℓ hℓ.1 hℓ.2, fun h ℓ h1 h2 => h ℓ ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun ℓ _ =>
    (measurable_tupleWalk S θ s ℓ) measurableSet_Icc

omit [MeasurableSpace Ω] in
/-- The two presentations of the barrier agree. -/
lemma mem_tupleGood_iff {X : ℕ → Ω → ℂ} {S : Finset ℕ} (hSp : ∀ p ∈ S, Nat.Prime p)
    {θ c : ℝ} {J r : ℕ} {a : ℝ} {hf : ℕ → ℝ} {s : ℂ}
    (hS : ∀ m, m < J → ∀ p ∈ primeBlockSub θ m, ((p : Nat.Primes) : ℕ) ∈ S) (ω : Ω) :
    (fun p : ↥S => X (p : ℕ) ω) ∈ tupleGood S θ c J r a hf s
      ↔ ω ∈ mesoGood X θ c J r a hf s := by
  have hw : ∀ ℓ, ℓ ≤ J → tupleWalk S θ s ℓ (fun p => X (p : ℕ) ω)
      = walk (fun m ω => ∑ p ∈ primeBlockSub θ m,
          localLogAdd (((p : ℕ) : ℂ) ^ (-s)) (X ((p : Nat.Primes) : ℕ) ω)) ℓ ω :=
    fun ℓ hℓ => tupleWalk_eq_walk hSp (fun m hm => hS m (lt_of_lt_of_le hm hℓ)) ω
  constructor
  · intro h ℓ h1 h2
    rw [← hw ℓ h2]
    exact h ℓ h1 h2
  · intro h ℓ h1 h2
    rw [hw ℓ h2]
    exact h ℓ h1 h2

/-! ### The low primes cancel

With the barrier presented as a tuple event, `RMF.IsIIDPrimeValues.integral_mul_split` applies at
exponent `1` and gives the factorisation.  Both the barriered and the free second moment carry
the same factor `E‖F_z(s)‖²`, so it cancels from the ratio, and **Proposition I for the block
product is exactly Proposition I for the full product**.  No new estimate is involved. -/

/-- **The low primes factor out of a barriered second moment.**  For any event `G` that is a
function of the values at `RMF.primesIco z n` — the barrier is one —

`∫_G ‖F_n(s)‖² = E‖F_z(s)‖²·∫_G ‖F_{[z,n)}(s)‖²`. -/
lemma setIntegral_normSq_split {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z n : ℕ) (hzn : z ≤ n) (s : ℂ)
    {G : Set Ω} {T : Set (↥(primesIco z n) → ℂ)} (hT : MeasurableSet T)
    (hGT : ∀ ω, ω ∈ G ↔ (fun p : ↥(primesIco z n) => X (p : ℕ) ω) ∈ T) :
    (∫ ω in G, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s ω‖ ^ 2 ∂μ)
      = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 ∂μ)
        * ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            z n s ω‖ ^ 2 ∂μ := by
  classical
  haveI := hX.isProbabilityMeasure
  have hhigh : Measurable fun ω => (fun p : ↥(primesIco z n) => X (p : ℕ) ω) :=
    measurable_primeTuple hX _ fun p hp => prime_of_mem_primesIco hp
  have hlow : Measurable fun ω => (fun p : ↥(Nat.primesBelow z) => X (p : ℕ) ω) :=
    measurable_primeTuple hX _ fun p hp => Nat.prime_of_mem_primesBelow hp
  have hGeq : G = (fun ω => (fun p : ↥(primesIco z n) => X (p : ℕ) ω)) ⁻¹' T := by
    ext ω; exact hGT ω
  have hG : MeasurableSet G := by rw [hGeq]; exact hhigh hT
  have hφ : Measurable fun v : ↥(Nat.primesBelow z) → ℂ =>
      ‖primePoly (Nat.primesBelow z) s v‖ ^ 2 :=
    ((continuous_primePoly _ s).norm.pow 2).measurable
  have hψ : Measurable fun v : ↥(primesIco z n) → ℂ =>
      Set.indicator T (fun v => ‖primePoly (primesIco z n) s v‖ ^ 2) v :=
    Measurable.indicator ((continuous_primePoly _ s).norm.pow 2).measurable hT
  have h := hX.integral_mul_split z n hφ hψ
    (hφ.comp hlow).aestronglyMeasurable (hψ.comp hhigh).aestronglyMeasurable
  -- the high factor is the indicator of `G` times the block product
  have hψeq : ∀ ω, Set.indicator T (fun v => ‖primePoly (primesIco z n) s v‖ ^ 2)
        (fun p : ↥(primesIco z n) => X (p : ℕ) ω)
      = Set.indicator G (fun ω => ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) z n s ω‖ ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem ((hGT ω).1 hω), Set.indicator_of_mem hω, primePoly_primesIco]
    · rw [Set.indicator_of_notMem (fun hc => hω ((hGT ω).2 hc)), Set.indicator_of_notMem hω]
  -- and the product of the two is the indicator of `G` times the full product
  have hmul : ∀ ω, (‖primePoly (Nat.primesBelow z) s (fun p => X (p : ℕ) ω)‖ ^ 2)
        * Set.indicator T (fun v => ‖primePoly (primesIco z n) s v‖ ^ 2)
            (fun p : ↥(primesIco z n) => X (p : ℕ) ω)
      = Set.indicator G (fun ω => ‖randomEulerProduct
          (fun ω => squarefreeExtension fun p => X p ω) n s ω‖ ^ 2) ω := by
    intro ω
    rw [hψeq ω, primePoly_primesBelow]
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
        normSq_randomEulerProduct_split hzn s ω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  have hlhs : (∫ ω in G,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s ω‖ ^ 2 ∂μ)
      = ∫ ω, (‖primePoly (Nat.primesBelow z) s (fun p => X (p : ℕ) ω)‖ ^ 2)
          * Set.indicator T (fun v => ‖primePoly (primesIco z n) s v‖ ^ 2)
              (fun p : ↥(primesIco z n) => X (p : ℕ) ω) ∂μ := by
    rw [← integral_indicator hG]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hmul ω).symm)
  have hrhs1 : (∫ ω, ‖primePoly (Nat.primesBelow z) s (fun p => X (p : ℕ) ω)‖ ^ 2 ∂μ)
      = ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [primePoly_primesBelow])
  have hrhs2 : (∫ ω, Set.indicator T (fun v => ‖primePoly (primesIco z n) s v‖ ^ 2)
        (fun p : ↥(primesIco z n) => X (p : ℕ) ω) ∂μ)
      = ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          z n s ω‖ ^ 2 ∂μ := by
    rw [← integral_indicator hG]
    exact integral_congr_ae (Filter.Eventually.of_forall hψeq)
  rw [hlhs, h, hrhs1, hrhs2]

/-- **Proposition I transfers to the block product**, on any line `Re s = ½ + σ > 0`: the
cancelled factor `E‖F_z(s)‖²` is positive there. -/
theorem setIntegral_normSq_randomEulerProductIco_le_of_le_signed {X : ℕ → Ω → ℂ}
    {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z n : ℕ) (hzn : z ≤ n) {s : ℂ} {σ : ℝ}
    (hs : s.re = 1 / 2 + σ) (hσ : 0 < 1 / 2 + σ)
    {G : Set Ω} {T : Set (↥(primesIco z n) → ℂ)} (hT : MeasurableSet T)
    (hGT : ∀ ω, ω ∈ G ↔ (fun p : ↥(primesIco z n) => X (p : ℕ) ω) ∈ T) {K : ℝ}
    (hle : (∫ ω in G,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s ω‖ ^ 2 ∂μ)
        ≤ K * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            n s ω‖ ^ 2 ∂μ) :
    (∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        z n s ω‖ ^ 2 ∂μ)
      ≤ K * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          z n s ω‖ ^ 2 ∂μ := by
  haveI := hX.isProbabilityMeasure
  -- `E‖F_z(s)‖² > 0`, which is what may be cancelled
  have hpos : (0 : ℝ) < ∫ ω,
      ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 ∂μ := by
    have h := integral_norm_randomEulerProductIco_rpow_pos hX 0 z hσ hs 2
    simp only [randomEulerProductIco_zero] at h
    have hpt : ∀ ω : Ω,
        ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ (2 : ℝ)
          = ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 := by
      intro ω
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [integral_congr_ae (Filter.Eventually.of_forall hpt)] at h
  have hfree : (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
        n s ω‖ ^ 2 ∂μ)
      = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 ∂μ)
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            z n s ω‖ ^ 2 ∂μ := by
    have hu := setIntegral_normSq_split hX z n hzn s (G := Set.univ) (T := Set.univ)
      MeasurableSet.univ (fun ω => by simp)
    simpa only [Measure.restrict_univ] using hu
  -- both sides of `hle` carry the same factor, which is positive
  rw [setIntegral_normSq_split hX z n hzn s hT hGT, hfree] at hle
  refine le_of_mul_le_mul_left ?_ hpos
  calc (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 ∂μ)
        * ∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
            z n s ω‖ ^ 2 ∂μ
      ≤ K * ((∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            z s ω‖ ^ 2 ∂μ)
          * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              z n s ω‖ ^ 2 ∂μ) := hle
    _ = (∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) z s ω‖ ^ 2 ∂μ)
          * (K * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
              z n s ω‖ ^ 2 ∂μ) := by ring

/-- **Proposition I transfers from the full product to the block product.**  For `σ ≥ 0` the
bound on the barriered ratio is the same for `F_n` and for `F_{[z,n)}`, because `E‖F_z(s)‖²`
cancels: the unit-window estimate serves where the block split needs a block estimate.  The case
`σ ≥ 0` of `RMF.setIntegral_normSq_randomEulerProductIco_le_of_le_signed`. -/
theorem setIntegral_normSq_randomEulerProductIco_le_of_le {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z n : ℕ) (hzn : z ≤ n) {s : ℂ} {σ : ℝ}
    (hs : s.re = 1 / 2 + σ) (hσ : 0 ≤ σ)
    {G : Set Ω} {T : Set (↥(primesIco z n) → ℂ)} (hT : MeasurableSet T)
    (hGT : ∀ ω, ω ∈ G ↔ (fun p : ↥(primesIco z n) => X (p : ℕ) ω) ∈ T) {K : ℝ}
    (hle : (∫ ω in G,
          ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) n s ω‖ ^ 2 ∂μ)
        ≤ K * ∫ ω, ‖randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω)
            n s ω‖ ^ 2 ∂μ) :
    (∫ ω in G, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
        z n s ω‖ ^ 2 ∂μ)
      ≤ K * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω)
          z n s ω‖ ^ 2 ∂μ := by
  exact setIntegral_normSq_randomEulerProductIco_le_of_le_signed hX z n hzn hs (by linarith) hT
    hGT hle

/-! ### The offset at the split scale

The block split fixes `z` by `T·log z ≍ 1`, and the barrier's offset `θ` has to satisfy
`e^θ ≥ log z` for the walk's primes to be above `z`.  That leaves `e^θ` free by a bounded factor,
and the two propositions want it *used*: Proposition I needs `(2·Im s)² ≤ e^θ`, Proposition II is
proportional to `T·e^θ`.  Both are met at once by `T·e^θ ≍ 1`, and the lattice `θ = harperOffset
D x`, `D ∈ ℕ`, is fine enough to hit it because consecutive offsets differ by exactly `1`. -/

/-- **The offset can always be put at the split scale.**  For every `0 < T ≤ 1` and every target
scale `K ≥ 4` there is a `D ≥ 4` with `K ≤ T·e^{harperOffset D x} ≤ e^4·K` and
`(D:ℝ) ≤ 4 + log K - log T`.  `e^{harperOffset D x}` moves by a factor `e` per step, so the target
window needs ratio at least `e`; `e^4` absorbs the clamp at `D = 4`.  `K` is free because the
unit-window chain bounds the height from both sides, `(2 Im s)² ≤ e^θ` and `Tsh ≤ 2·Im s·e^θ`,
and only the second needs `K` large. -/
theorem exists_harperOffset_at_split_scale (x : ℝ) {T K : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hK : 4 ≤ K) :
    ∃ D : ℕ, 4 ≤ D ∧ (D : ℝ) ≤ 4 + Real.log K - Real.log T
      ∧ K ≤ T * Real.exp (harperOffset D x)
      ∧ T * Real.exp (harperOffset D x) ≤ Real.exp 4 * K := by
  set f : ℝ := Int.fract (Real.log (Real.log x)) with hfdef
  have hf0 : (0 : ℝ) ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  have hlogT : Real.log T ≤ 0 := Real.log_nonpos hT0.le hT1
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h2]
    linarith [Real.log_two_gt_d9]
  have hlogK : (1 : ℝ) ≤ Real.log K :=
    le_trans hlog4 (Real.log_le_log (by norm_num) hK)
  set u : ℝ := 1 + Real.log K - Real.log T - f with hudef
  set D : ℕ := max 4 ⌈u⌉₊ with hDdef
  have hD4 : 4 ≤ D := le_max_left _ _
  have hDge : u ≤ (D : ℝ) := by
    refine le_trans (Nat.le_ceil u) ?_
    exact_mod_cast Nat.le_max_right 4 ⌈u⌉₊
  have hDboth : (D : ℝ) ≤ 5 + Real.log K - Real.log T - f
      ∧ (D : ℝ) ≤ 4 + Real.log K - Real.log T := by
    rcases le_total ⌈u⌉₊ 4 with hc | hc
    · have hD : D = 4 := max_eq_left hc
      rw [hD]
      push_cast
      exact ⟨by linarith, by linarith⟩
    · have hDc : D = ⌈u⌉₊ := max_eq_right hc
      have hu3 : (3 : ℝ) < u := by exact_mod_cast Nat.lt_ceil.1 (by omega : 3 < ⌈u⌉₊)
      have hlt := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ u)
      rw [hudef] at hlt
      rw [hDc]
      exact ⟨by linarith, by linarith⟩
  obtain ⟨hDle, hDdepth⟩ := hDboth
  have hθ : harperOffset D x = f + (D : ℝ) - 1 := rfl
  have hexp : T * Real.exp (harperOffset D x) = Real.exp (Real.log T + (f + (D : ℝ) - 1)) := by
    rw [Real.exp_add, Real.exp_log hT0, hθ]
  refine ⟨D, hD4, hDdepth, ?_, ?_⟩
  · have hle : Real.log K ≤ Real.log T + (f + (D : ℝ) - 1) := by
      rw [hudef] at hDge
      linarith
    have h := Real.exp_le_exp.2 hle
    rw [Real.exp_log (by linarith : (0 : ℝ) < K)] at h
    rw [hexp]
    exact h
  · have hRHS : Real.exp (4 + Real.log K) = Real.exp 4 * K := by
      rw [Real.exp_add, Real.exp_log (by linarith : (0 : ℝ) < K)]
    have hle : Real.log T + (f + (D : ℝ) - 1) ≤ 4 + Real.log K := by linarith
    rw [hexp, ← hRHS]
    exact Real.exp_le_exp.2 hle

/-- **The height condition at such an offset.**  `(2h)² ≤ e^θ` for every `0 < h ≤ T ≤ 1`, from
`4 ≤ T·e^θ` alone: `4h² ≤ 4T² ≤ 4 ≤ 4/T ≤ e^θ`. -/
lemma sq_two_mul_le_exp_harperOffset {T h θ : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hh0 : 0 < h) (hh : h ≤ T) (hθ : 4 ≤ T * Real.exp θ) : (2 * h) ^ 2 ≤ Real.exp θ := by
  have hexp0 : (0 : ℝ) < Real.exp θ := Real.exp_pos θ
  have hdiv : 4 / T ≤ Real.exp θ := by
    rw [div_le_iff₀ hT0]
    linarith [hθ, mul_comm T (Real.exp θ)]
  have hsq : 4 * h ^ 2 ≤ 4 / T := by
    rw [le_div_iff₀ hT0]
    nlinarith [hh0.le, hh, hT1]
  nlinarith [hsq, hdiv]

/-- **Proposition I at a shift of either sign**, for `σ > -½`: restricting the second moment of
the block product `F_{[z, ⌊x⌋+1)}(s)` to the good event saves a factor `min{1, a/√(J - r)}`,
`J = harperBlockCount D x - d` the depth.  From the unit-window statement
`RMF.exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop`, which already takes a
signed shift; the transfer across the split needs only `½ + σ > 0`. -/
theorem exists_setIntegral_mesoGood_normSq_randomEulerProductIco_le_rademacher_signed :
    ∃ (D₀ n₀ : ℕ) (x₀ a₀ A B Tsh : ℝ), 4 ≤ D₀ ∧ 0 < A ∧ 20 ≤ B ∧ 0 < Tsh ∧
      ∀ (Ω' : Type*) [MeasurableSpace Ω'] (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'),
        IsRademacherPrimeValues Y ν →
        ∀ (x σ a η : ℝ) (z D r d : ℕ) (s : ℂ) (hf : ℕ → ℝ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          s.re = 1 / 2 + σ → -(1 / 2) < σ →
          |σ| * Real.log x ≤ η → 10 * η ≤ Real.exp d →
          0 < 2 * s.im → (2 * s.im) ^ 2 ≤ Real.exp (harperOffset D x) →
          Tsh ≤ 2 * s.im * Real.exp (harperOffset D x) →
          (z : ℝ) ≤ blockScale (harperOffset D x) 0 → z ≤ ⌊x⌋₊ + 1 →
          a₀ ≤ a → 1 ≤ a → 1 ≤ r → r ≤ harperBlockCount D x - d → (r : ℝ) ≤ a / 4 + 1 →
          n₀ ≤ harperBlockCount D x - d - r →
          (∀ j, 1 ≤ j → j ≤ harperBlockCount D x - d → |hf j| ≤ 10 * Real.log j) →
            (∫ ω in mesoGood Y (harperOffset D x) B (harperBlockCount D x - d) r a hf s,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  z (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν)
              ≤ A * min 1 (a / Real.sqrt (((harperBlockCount D x - d : ℕ) : ℝ) - r))
                * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                    z (⌊x⌋₊ + 1) s ω‖ ^ 2 ∂ν := by
  obtain ⟨D₀, n₀, x₀, a₀, A, B, Tsh, hD₀, hA, hB, hTsh, H⟩ :=
    exists_setIntegral_restricted_normSq_le_rademacher_of_offset_of_drop
  refine ⟨D₀, n₀, max x₀ 2, a₀, A, B, Tsh, hD₀, hA, hB, hTsh, ?_⟩
  intro Ω' _ Y ν hY x σ a η z D r d s hf hx hDD hDlog hres hσ hση hη hτ0 hτsq hT hzb hzn
    ha₀ ha1 hr1 hrn hra hn₀ hhf
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) < x := by linarith
  have hsre : 0 < s.re := by rw [hres]; linarith
  -- the unit-window estimate, for the full product
  have hfull := H Ω' Y ν hY x σ a η D r d s hf hx0 hDD hDlog hres hsre hση hη hτ0 hτsq hT
    ha₀ ha1 hr1 hrn hra hn₀ hhf
  -- every prime the barrier looks at lies in `[z, ⌊x⌋₊+1)`
  have hblk : ∀ m, m < harperBlockCount D x - d →
      ∀ p ∈ primeBlockSub (harperOffset D x) m,
        ((p : Nat.Primes) : ℕ) ∈ primesIco z (⌊x⌋₊ + 1) := by
    intro m hm p hp
    rw [mem_primeBlockSub] at hp
    refine mem_primesIco.2 ⟨p.2, ?_, ?_⟩
    · have h0 : blockScale (harperOffset D x) 0 ≤ blockScale (harperOffset D x) m :=
        blockScale_mono _ (Nat.zero_le m)
      have hzp : (z : ℝ) < ((p : ℕ) : ℝ) := lt_of_le_of_lt (le_trans hzb h0) hp.1
      exact_mod_cast hzp.le
    · have hJ : m + 1 ≤ harperBlockCount D x := by omega
      have h1 : blockScale (harperOffset D x) (m + 1)
          ≤ blockScale (harperOffset D x) (harperBlockCount D x) := blockScale_mono _ hJ
      rw [blockScale_harperOffset_last hx1 hDlog] at h1
      have he1 : (Real.exp 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp (by norm_num))
      have hxe : x ^ (Real.exp 1)⁻¹ ≤ x := by
        calc x ^ (Real.exp 1)⁻¹ ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) he1
          _ = x := Real.rpow_one x
      have hpx : ((p : ℕ) : ℝ) < (⌊x⌋₊ : ℝ) + 1 :=
        lt_of_le_of_lt (le_trans hp.2 (le_trans h1 hxe)) (Nat.lt_floor_add_one x)
      exact_mod_cast hpx
  -- and so the barrier is an event of the high primes
  refine setIntegral_normSq_randomEulerProductIco_le_of_le_signed hY z (⌊x⌋₊ + 1) hzn hres
    (by linarith)
    (measurableSet_tupleGood (primesIco z (⌊x⌋₊ + 1)) (harperOffset D x) B
      (harperBlockCount D x - d) r a hf s)
    (fun ω => (mem_tupleGood_iff (fun p hp => prime_of_mem_primesIco hp) hblk ω).symm) hfull

/-! ### Proposition II — the barrier fails rarely

Harper's Key Proposition 4, in the form `RMF.integral_rpow_le_of_decomposition` consumes: the bad
event is `∃ h` in the *window*, not at one height, because the decomposition puts the indicator
outside the height integral.

`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_top` already gives exactly this at a
fixed offset and an arbitrary window, with the bound proportional to the **width**:

`P(bad on a window of width w) ≤ C·e^D·w·e^{-2a}`.

So the block form is that statement read at `w ≍ T`, and the factor is `e^D·T ≍ e^{θ}·T` — which
is `O(1)` **exactly when the offset sits at the split scale**, `e^θ ≍ 1/T ≍ log z`.  That is what
`RMF.harperDt` arranges, and it is why `D` has to move with the height. -/

lemma harperGoodRangeAdd_eq_mesoGood {Ω' : Type*} (Y : ℕ → Ω' → ℂ) (c : ℝ) (D : ℕ)
    (x δ a : ℝ) (t : ℕ) (h : ℝ) :
    harperGoodRangeAdd Y c D x δ a t h
      = mesoGood Y (harperOffset D x) c t ⌈a / 4⌉₊ a (fun j => 2 * Real.log j)
        (shiftLine δ h) := rfl

/-- **Proposition II at a shift of either sign**, for `δ ≥ -1/12`: the probability that the
barrier fails somewhere on the window `[T/e, T]` is at most `C·T·e^{harperOffset D x}·e^{-2a}`.
From `RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_top_signed`. -/
theorem exists_const_measureReal_notMem_mesoGood_le_rademacher_signed {Ω' : Type*}
    [MeasurableSpace Ω'] :
    ∃ a₀ C : ℝ, 0 < C ∧
      ∀ (E₀ : ℝ) (d : ℕ), 0 ≤ E₀ → E₀ ≤ Real.exp d →
      ∀ (Y : ℕ → Ω' → ℂ) (ν : Measure Ω'), IsRademacherPrimeValues Y ν →
        ∀ (D : ℕ) (x δ η a c T : ℝ), 4 ≤ D → 1 < x →
          (D : ℝ) ≤ Real.log (Real.log x) →
          -(1 / 12) ≤ δ → 0 ≤ η → η ≤ E₀ → |δ| * Real.log x ≤ η → a₀ ≤ a → 20 ≤ c →
          0 < T → 1 ≤ T * Real.exp (harperOffset D x) →
            ν.real {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T,
                ω ∉ mesoGood Y (harperOffset D x) c (harperBlockCount D x - d) ⌈a / 4⌉₊ a
                  (fun j => 2 * Real.log j) (shiftLine δ h)}
              ≤ C * (T * Real.exp (harperOffset D x)) * Real.exp (-(2 * a)) := by
  obtain ⟨a₀, C, hC, H⟩ :=
    exists_const_measureReal_notMem_harperGoodRangeAdd_of_top_signed (Ω' := Ω')
  refine ⟨max a₀ 1, C * Real.exp 1, mul_pos hC (Real.exp_pos 1), ?_⟩
  intro E₀ d hE₀ hEd Y ν hY D x δ η a c T hD hx1 hxD hδ0 hη0 hηE hδx ha hc hT hTθ
  haveI := hY.isProbabilityMeasure
  have ha₀ : a₀ ≤ a := le_trans (le_max_left _ _) ha
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have hθ0 : (0 : ℝ) < Real.exp (harperOffset D x) := Real.exp_pos _
  -- the window fits in a band of width `T`, which is wide enough to pay for the mesh
  have hw : Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D x)) ≤ T := by
    have hr0 : (0 : ℝ) ≤ (⌈a / 4⌉₊ : ℝ) := Nat.cast_nonneg _
    have h1 : Real.exp (-((⌈a / 4⌉₊ : ℝ) + harperOffset D x))
        ≤ Real.exp (-harperOffset D x) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-harperOffset D x) ≤ T := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hθ0]
      linarith [hTθ]
    linarith
  have hsub : {ω : Ω' | ∃ h ∈ Set.Icc (T / Real.exp 1) T,
        ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h}
      ⊆ {ω : Ω' | ∃ h ∈ Set.Ico (T / Real.exp 1) (T / Real.exp 1 + T),
          ω ∉ harperGoodRangeAdd Y c D x δ a (harperBlockCount D x - d) h} := by
    rintro ω ⟨h, hh, hnot⟩
    exact ⟨h, ⟨hh.1, by linarith [hh.2, div_pos hT (Real.exp_pos 1)]⟩, hnot⟩
  have hmain := H E₀ d hE₀ hEd Y ν hY D x δ η a c (T / Real.exp 1) T hD hx1 hxD hδ0 hη0 hηE
    hδx ha₀ hc hw
  -- `e^D ≤ e·e^θ`, which is where the visible factor comes from
  have hexpD : Real.exp (D : ℝ) ≤ Real.exp 1 * Real.exp (harperOffset D x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [sub_one_le_harperOffset D x])
  simp only [← harperGoodRangeAdd_eq_mesoGood]
  refine le_trans (le_trans (measureReal_mono hsub (measure_ne_top _ _)) hmain) ?_
  have hstep : C * Real.exp (D : ℝ) * T ≤ C * Real.exp 1 * (T * Real.exp (harperOffset D x)) := by
    have := mul_le_mul_of_nonneg_left hexpD hC.le
    nlinarith [hT.le, hC.le, Real.exp_pos (harperOffset D x)]
  exact mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le

/-! ### The pointwise decomposition

`RMF.integral_rpow_le_of_goodSets` is the interpolation over a geometric family of levels,
abstracted away from the model: it takes the chaos `Z`, the chaos restricted to a family of good
sets `Rst`, the window `win` the family is read over, and `hdec` — the pointwise decomposition
along a chain of good sets.  Everything else it needs of the model it gets through four fields.

`hdec` is the only one of the four that has to be re-proved for a block, and it is one line of
arithmetic (`RMF.le_add_sum_add_of_le_add_mul`) on top of one observation: off the bad set the
indicator does nothing, so the restricted integral *is* the integral. -/

omit [MeasurableSpace Ω] in
/-- **One step of the decomposition.**  `W ≤ R + 1_{bad}·W`, for any nonnegative integrand and
any family of sets indexed by the height. -/
lemma setIntegral_le_indicator_add {g : ℝ → Ω → ℝ} (hg0 : ∀ h ω, 0 ≤ g h ω)
    {win : Set ℝ} (hwin : MeasurableSet win) (G : ℝ → Set Ω) (ω : Ω) :
    (∫ h in win, g h ω)
      ≤ (∫ h in win, Set.indicator (G h) (g h) ω)
        + Set.indicator {ω | ∃ h ∈ win, ω ∉ G h} (fun _ => (1 : ℝ)) ω * ∫ h in win, g h ω := by
  have hR0 : (0 : ℝ) ≤ ∫ h in win, Set.indicator (G h) (g h) ω :=
    integral_nonneg fun h => Set.indicator_nonneg (fun _ _ => hg0 h ω) ω
  by_cases hb : ω ∈ {ω | ∃ h ∈ win, ω ∉ G h}
  · rw [Set.indicator_of_mem hb, one_mul]
    linarith
  · rw [Set.indicator_of_notMem hb, zero_mul, add_zero]
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at hb
    exact le_of_eq (setIntegral_congr_fun hwin fun h hh =>
      (Set.indicator_of_mem (hb h hh) (g h)).symm)

omit [MeasurableSpace Ω] in
/-- **The decomposition along a chain**, in the shape `RMF.integral_rpow_le_of_goodSets` asks
for, and with the scaling `c` carried through — the interpolation wants `E Z ≤ 1`, and dividing
by the first moment is how a block gets there. -/
lemma setIntegral_le_decomposition {g : ℝ → Ω → ℝ} (hg0 : ∀ h ω, 0 ≤ g h ω)
    {win : Set ℝ} (hwin : MeasurableSet win) {c : ℝ} (hc : 0 ≤ c)
    (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ) (hrm : r ≤ m) :
    c * ∫ h in win, g h ω
      ≤ (c * ∫ h in win, Set.indicator (S r h) (g h) ω)
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ win, ω ∉ S j h} (fun _ => (1 : ℝ)) ω
              * (c * ∫ h in win, Set.indicator (S (j + 1) h) (g h) ω))
        + Set.indicator {ω | ∃ h ∈ win, ω ∉ S m h} (fun _ => (1 : ℝ)) ω
            * (c * ∫ h in win, g h ω) := by
  have hbase := le_add_sum_add_of_le_add_mul (Z := ∫ h in win, g h ω)
    (R := fun j => ∫ h in win, Set.indicator (S j h) (g h) ω)
    (I := fun j => Set.indicator {ω | ∃ h ∈ win, ω ∉ S j h} (fun _ => (1 : ℝ)) ω)
    (integral_nonneg fun h => hg0 h ω)
    (fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (fun _ => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one)
    (fun j => setIntegral_le_indicator_add hg0 hwin (S j) ω) r m hrm
  set W : ℝ := ∫ h in win, g h ω with hW
  set R : ℕ → ℝ := fun j => ∫ h in win, Set.indicator (S j h) (g h) ω with hR
  set I : ℕ → ℝ :=
    fun j => Set.indicator {ω | ∃ h ∈ win, ω ∉ S j h} (fun _ => (1 : ℝ)) ω with hI
  set G : ℝ := ∑ j ∈ Finset.Ico r m, I j * R (j + 1) with hG
  have hsum : (∑ j ∈ Finset.Ico r m, I j * (c * R (j + 1))) = c * G := by
    rw [hG, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  have hmul := mul_le_mul_of_nonneg_left hbase hc
  have hexp : c * (R r + G + I m * W) = c * R r + c * G + I m * (c * W) := by ring
  linarith [hmul, hexp]

/-! ### Integrability of the two processes

Both are bounded by the envelope of the block product times the length of the window, which is
`RMF.ae_setIntegral_normSq_primesIco_mem_Icc_signed`; the only work is the measurability of the
restricted one, where the indicator has to be read as a set in `Ω × ℝ` before
`MeasureTheory.StronglyMeasurable.integral_prod_right'` can see it. -/

/-- The window integral of the block product is integrable in `ω`, on any line
`Re s = ½ + σ > 0`. -/
lemma integrable_setIntegral_normSq_primesIco_signed {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ a b : ℝ} (hσ : 0 < 1 / 2 + σ) (hab : a ≤ b) :
    Integrable (fun ω => ∫ h in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) μ := by
  haveI := hX.isProbabilityMeasure
  have hslice := (integrable_uncurry_normSq_shiftLine_primesIco hX z y (I := Set.Icc a b) hσ
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integral_prod_left
  refine (memLp_top_of_bound hslice.1
    ((b - a) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ?_).integrable le_top
  filter_upwards [ae_setIntegral_normSq_primesIco_mem_Icc_signed hX z y hσ hab] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun h => sq_nonneg _)]
  exact hω.2

/-- The window integral of the block product is integrable in `ω`.

The case `σ ≥ 0` of `RMF.integrable_setIntegral_normSq_primesIco_signed`. -/
lemma integrable_setIntegral_normSq_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ a b : ℝ} (hσ : 0 ≤ σ) (hab : a ≤ b) :
    Integrable (fun ω => ∫ h in Set.Icc a b,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) μ := by
  exact integrable_setIntegral_normSq_primesIco_signed hX z y (by linarith) hab

/-- The restricted window integral is integrable in `ω`, on any line `Re s = ½ + σ > 0`. -/
lemma integrable_setIntegral_indicator_normSq_primesIco_signed {X : ℕ → Ω → ℂ}
    {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ a b : ℝ} (hσ : 0 < 1 / 2 + σ) (hab : a ≤ b)
    (S : ℝ → Set Ω) (hS : MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2}) :
    Integrable (fun ω => ∫ h in Set.Icc a b, Set.indicator (S h)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) ω) μ := by
  haveI := hX.isProbabilityMeasure
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (h : ℝ) =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) := by
    have h2 := (measurable_uncurry_primePoly hX (primesIco z y)
      (fun p hp => prime_of_mem_primesIco hp) σ).norm.pow_const 2
    simp only [primePoly_primesIco] at h2
    exact h2
  have hind : Measurable fun p : Ω × ℝ => Set.indicator (S p.2)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ p.2) ω‖ ^ 2) p.1 := by
    have hrw : (fun p : Ω × ℝ => Set.indicator (S p.2)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ p.2) ω‖ ^ 2) p.1)
        = Set.indicator {p : Ω × ℝ | p.1 ∈ S p.2}
          (fun p : Ω × ℝ => ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) z y (shiftLine σ p.2) p.1‖ ^ 2) := by
      funext p
      by_cases hp : p.1 ∈ S p.2
      · have h1 := Set.indicator_of_mem hp
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ p.2) ω‖ ^ 2)
        have h2 := Set.indicator_of_mem (a := p) (s := {p : Ω × ℝ | p.1 ∈ S p.2}) hp
          (fun p : Ω × ℝ => ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) z y (shiftLine σ p.2) p.1‖ ^ 2)
        rw [h1, h2]
      · have h1 := Set.indicator_of_notMem hp
          (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ p.2) ω‖ ^ 2)
        have h2 := Set.indicator_of_notMem (a := p) (s := {p : Ω × ℝ | p.1 ∈ S p.2}) hp
          (fun p : Ω × ℝ => ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => X p ω) z y (shiftLine σ p.2) p.1‖ ^ 2)
        rw [h1, h2]
    rw [hrw]
    exact Measurable.indicator hjoint hS
  have hmeas : AEStronglyMeasurable (fun ω => ∫ h in Set.Icc a b, Set.indicator (S h)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) ω) μ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc a b))
      hind.stronglyMeasurable).aestronglyMeasurable
  refine (memLp_top_of_bound hmeas
    ((b - a) * (∏ p ∈ primesIco z y, (1 + (p : ℝ) ^ (-(1 / 2 + σ)))) ^ 2) ?_).integrable le_top
  have hslice := (integrable_uncurry_normSq_shiftLine_primesIco hX z y (I := Set.Icc a b) hσ
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).prod_right_ae
  filter_upwards [ae_setIntegral_normSq_primesIco_mem_Icc_signed hX z y hσ hab, hslice]
    with ω hω hint
  have h0 : (0 : ℝ) ≤ ∫ h in Set.Icc a b, Set.indicator (S h)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) ω :=
    integral_nonneg fun h => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  have hle : (∫ h in Set.Icc a b, Set.indicator (S h)
      (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) ω)
      ≤ ∫ h in Set.Icc a b,
        ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2 := by
    refine integral_mono (Integrable.mono' hint ?_ ?_) hint fun h => ?_
    · exact (hind.comp (measurable_prodMk_left (α := Ω))).aestronglyMeasurable
    · filter_upwards with h
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)]
      exact Set.indicator_apply_le' (fun _ => le_rfl) fun _ => sq_nonneg _
    · exact Set.indicator_apply_le' (fun _ => le_rfl) fun _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  linarith [hω.2]

/-! ### The first moment of a block

The interpolation wants `E Z ≤ C₁`, and the whole point of dividing by `C₁` afterwards is that
`C₁` is where the `T²·log x` of the final bound comes from.  It is Mertens:

`E‖F_{[z,x]}(½+σ+ih)‖² ≤ exp(∑_{z ≤ p ≤ x} 1/p) ≍ log x / log z ≤ T·log x`,

the last step by `T·log z ≥ 1`, and the window contributes its own length `≤ T`. -/

/-- **The second moment of a block product, in terms of the window scale.**
`E‖F_{[z,⌊x⌋+1)}(s)‖² ≤ e²¹·T·log x` whenever `Re s ≥ ½` and `T·log z ≥ 1`.
`RMF.IsRademacherRMF.integral_norm_randomEulerProductIco_sq_le` gives `exp(∑ p^{-2 Re s})`, and
`RMF.abs_sum_prime_Ioc_inv_sub_log_log_sub_le` turns the sum into `log log x - log log z` with an
error `20/log z ≤ 20` — the error is given away entirely, which is why `e²¹` and not `e^γ`. -/
lemma integral_normSq_randomEulerProductIco_le_mertens {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z : ℕ} {x σ T : ℝ}
    (hz2 : 2 ≤ z) (hzx : (z : ℝ) ≤ x) (hσ : 0 ≤ σ)
    (hT0 : 0 < T) (hT1 : T ≤ 1) (hTz : 1 ≤ T * Real.log z) {s : ℂ} (hs : s.re = 1 / 2 + σ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1)
        s ω‖ ^ 2 ∂μ) ≤ Real.exp 21 * (T * Real.log x) := by
  classical
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hx2 : (2 : ℝ) ≤ x := le_trans hz2R hzx
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hlogz1 : (1 : ℝ) ≤ Real.log z := by nlinarith [hTz, hT1, hlogz]
  -- each term of the exponent is at most `1/p`
  have hterm : ∀ p ∈ primesIco z (⌊x⌋₊ + 1),
      ((p : ℕ) : ℝ) ^ (-2 * s.re) ≤ (1 : ℝ) / p := by
    intro p hp
    have hp2 : 2 ≤ p := (prime_of_mem_primesIco hp).two_le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp2
    have hexp : -2 * s.re ≤ -1 := by rw [hs]; linarith
    have h := Real.rpow_le_rpow_of_exponent_le hp1 hexp
    rwa [Real.rpow_neg_one, ← one_div] at h
  -- Mertens on the block, with the error given away
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le (z : ℝ) x hz2R hzx
  rw [Nat.floor_natCast] at hmert
  have hmertle := (abs_le.1 hmert).2
  have h20 : (20 : ℝ) / Real.log z ≤ 20 := by
    rw [div_le_iff₀ hlogz]; linarith
  have hznot : z ∉ {p ∈ Finset.Ioc z ⌊x⌋₊ | Nat.Prime p} := by
    simp only [Finset.mem_filter, Finset.mem_Ioc, not_and]
    intro hc
    exact absurd hc.1 (lt_irrefl z)
  have hsub : primesIco z (⌊x⌋₊ + 1) ⊆ insert z {p ∈ Finset.Ioc z ⌊x⌋₊ | Nat.Prime p} := by
    intro p hp
    rw [mem_primesIco] at hp
    rcases eq_or_lt_of_le hp.2.1 with heq | hlt
    · rw [← heq]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hlt, by omega⟩, hp.1⟩
  have hsum : (∑ p ∈ primesIco z (⌊x⌋₊ + 1), (1 : ℝ) / p)
      ≤ 41 / 2 + (Real.log (Real.log x) - Real.log (Real.log z)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity) ?_
    rw [Finset.sum_insert hznot]
    have hz : (1 : ℝ) / z ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  -- assemble
  refine le_trans (hf.integral_norm_randomEulerProductIco_sq_le z (⌊x⌋₊ + 1) s) ?_
  have hchain : (∑ p ∈ primesIco z (⌊x⌋₊ + 1), ((p : ℕ) : ℝ) ^ (-2 * s.re))
      ≤ 41 / 2 + (Real.log (Real.log x) - Real.log (Real.log z)) :=
    le_trans (Finset.sum_le_sum hterm) hsum
  refine le_trans (Real.exp_le_exp.2 hchain) ?_
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hlogx, Real.exp_log hlogz]
  have hdiv : Real.log x / Real.log z ≤ T * Real.log x := by
    rw [div_le_iff₀ hlogz]
    nlinarith [hTz, hlogx.le, hlogz]
  have he : Real.exp (41 / 2) ≤ Real.exp 21 := Real.exp_le_exp.2 (by norm_num)
  have hpos : (0 : ℝ) ≤ Real.log x / Real.log z := by positivity
  calc Real.exp (41 / 2) * (Real.log x / Real.log z)
      ≤ Real.exp 21 * (Real.log x / Real.log z) := mul_le_mul_of_nonneg_right he hpos
    _ ≤ Real.exp 21 * (T * Real.log x) :=
        mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le

/-- **The second moment of a block product at a shift of either sign.**
`E‖F_{[z,⌊x⌋+1)}(s)‖² ≤ e³⁷·T·log x` for `Re s = ½ + σ` with `σ ≥ 0` or `2|σ|·log x ≤ 1`, and
`T·log z ≥ 1`.  For `σ ≥ 0` it is `RMF.integral_normSq_randomEulerProductIco_le_mertens`.  To the
left of `½` the termwise `p^{-2 Re s} ≤ 1/p` fails, and reading the tilt multiplicatively would put
`(log x/log z)^e` here; Mertens is read additively instead
(`RMF.sum_prime_rpow_signed_shift_le_sum_inv_add`, `16` in the exponent). -/
lemma integral_normSq_randomEulerProductIco_le_mertens_signed {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) {z : ℕ} {x σ T : ℝ}
    (hz2 : 2 ≤ z) (hzx : (z : ℝ) ≤ x) (hσ : 0 ≤ σ ∨ 2 * |σ| * Real.log x ≤ 1)
    (hT0 : 0 < T) (hT1 : T ≤ 1) (hTz : 1 ≤ T * Real.log z) {s : ℂ} (hs : s.re = 1 / 2 + σ) :
    (∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z (⌊x⌋₊ + 1)
        s ω‖ ^ 2 ∂μ) ≤ Real.exp 37 * (T * Real.log x) := by
  classical
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hx2 : (2 : ℝ) ≤ x := le_trans hz2R hzx
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  rcases hσ with hσ0 | hσx
  · refine le_trans
      (integral_normSq_randomEulerProductIco_le_mertens hX hz2 hzx hσ0 hT0 hT1 hTz hs) ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by norm_num)) (mul_pos hT0 hlogx).le
  have hf : IsRademacherRMF (fun ω => squarefreeExtension fun p => X p ω) μ := hX.isRademacherRMF
  have hlogz1 : (1 : ℝ) ≤ Real.log z := by nlinarith [hTz, hT1, hlogz]
  -- the floor of `x` bounds the primes, and `log ⌊x⌋ ≤ log x`
  have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hfl0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hlogfl : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log hfl0 (Nat.floor_le (by linarith))
  have hσfl : 2 * |σ| * Real.log (⌊x⌋₊ : ℝ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hlogfl (by positivity)) hσx
  -- Mertens at the shift, additively
  have hshift := sum_prime_rpow_signed_shift_le_sum_inv_add (S := primesIco z (⌊x⌋₊ + 1)) hfl2
    (fun p hp => ⟨prime_of_mem_primesIco hp, by have := (mem_primesIco.1 hp).2.2; omega⟩) hσfl
  have hre : ∀ p ∈ primesIco z (⌊x⌋₊ + 1),
      ((p : ℕ) : ℝ) ^ (-2 * s.re) = (p : ℝ) ^ (-(1 + 2 * σ)) := by
    intro p _
    rw [hs]
    congr 1
    ring
  -- Mertens on the block, with the error given away
  have hmert := abs_sum_prime_Ioc_inv_sub_log_log_sub_le (z : ℝ) x hz2R hzx
  rw [Nat.floor_natCast] at hmert
  have hmertle := (abs_le.1 hmert).2
  have h20 : (20 : ℝ) / Real.log z ≤ 20 := by
    rw [div_le_iff₀ hlogz]; linarith
  have hznot : z ∉ {p ∈ Finset.Ioc z ⌊x⌋₊ | Nat.Prime p} := by
    simp only [Finset.mem_filter, Finset.mem_Ioc, not_and]
    intro hc
    exact absurd hc.1 (lt_irrefl z)
  have hsub : primesIco z (⌊x⌋₊ + 1) ⊆ insert z {p ∈ Finset.Ioc z ⌊x⌋₊ | Nat.Prime p} := by
    intro p hp
    rw [mem_primesIco] at hp
    rcases eq_or_lt_of_le hp.2.1 with heq | hlt
    · rw [← heq]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hlt, by omega⟩, hp.1⟩
  have hsum : (∑ p ∈ primesIco z (⌊x⌋₊ + 1), (1 : ℝ) / p)
      ≤ 41 / 2 + (Real.log (Real.log x) - Real.log (Real.log z)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity) ?_
    rw [Finset.sum_insert hznot]
    have hz : (1 : ℝ) / z ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hinv : ∑ p ∈ primesIco z (⌊x⌋₊ + 1), ((p : ℝ))⁻¹
      = ∑ p ∈ primesIco z (⌊x⌋₊ + 1), (1 : ℝ) / p :=
    Finset.sum_congr rfl fun p _ => (one_div _).symm
  -- assemble
  refine le_trans (hf.integral_norm_randomEulerProductIco_sq_le z (⌊x⌋₊ + 1) s) ?_
  have hchain : (∑ p ∈ primesIco z (⌊x⌋₊ + 1), ((p : ℕ) : ℝ) ^ (-2 * s.re))
      ≤ 73 / 2 + (Real.log (Real.log x) - Real.log (Real.log z)) := by
    rw [Finset.sum_congr rfl hre]
    linarith
  refine le_trans (Real.exp_le_exp.2 hchain) ?_
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hlogx, Real.exp_log hlogz]
  have hdiv : Real.log x / Real.log z ≤ T * Real.log x := by
    rw [div_le_iff₀ hlogz]
    nlinarith [hTz, hlogx.le, hlogz]
  have he : Real.exp (73 / 2) ≤ Real.exp 37 := Real.exp_le_exp.2 (by norm_num)
  have hpos : (0 : ℝ) ≤ Real.log x / Real.log z := by positivity
  calc Real.exp (73 / 2) * (Real.log x / Real.log z)
      ≤ Real.exp 37 * (Real.log x / Real.log z) := mul_le_mul_of_nonneg_right he hpos
    _ ≤ Real.exp 37 * (T * Real.log x) :=
        mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le

/-! ### The height integral of a per-height bound -/

/-- **A per-height bound integrates over the window**, in the plain-constant form.  The sibling
of `RMF.integral_indicator_le_of_per_height`, whose right-hand side is tied to the free moment at
height `0`; here the per-height bound is a constant, which is what the block needs. -/
theorem integral_setIntegral_indicator_le_of_per_height {ν : Measure Ω} [SFinite ν]
    {L : ℝ → Set Ω} {g : ℝ → Ω → ℝ} {W : Set ℝ} (hW : MeasurableSet W) (hWfin : volume W ≠ ⊤)
    {K : ℝ}
    (hInt : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => Set.indicator (L t) (g t) ω)
      (ν.prod (volume.restrict W)))
    (hper : ∀ t ∈ W, (∫ ω, Set.indicator (L t) (g t) ω ∂ν) ≤ K) :
    (∫ ω, (∫ t in W, Set.indicator (L t) (g t) ω) ∂ν) ≤ (volume W).toReal * K := by
  rw [integral_integral_swap hInt]
  have hconst : IntegrableOn (fun _ : ℝ => K) W := integrableOn_const hWfin
  have hmono := setIntegral_mono_on hInt.integral_prod_right hconst hW hper
  rwa [setIntegral_const, smul_eq_mul] at hmono

/-- The uncurried restricted integrand is product-integrable on any line `Re s = ½ + σ > 0`. -/
lemma integrable_uncurry_indicator_normSq_primesIco_signed {X : ℕ → Ω → ℂ}
    {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 < 1 / 2 + σ) {I : Set ℝ}
    (hI : volume I ≠ ⊤) (S : ℝ → Set Ω) (hS : MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2}) :
    Integrable (Function.uncurry fun (ω : Ω) (h : ℝ) => Set.indicator (S h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω)
      (μ.prod (volume.restrict I)) := by
  haveI := hX.isProbabilityMeasure
  have hbase := integrable_uncurry_normSq_shiftLine_primesIco hX z y (I := I) hσ hI
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (h : ℝ) =>
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
        (shiftLine σ h) ω‖ ^ 2) := by
    have h2 := (measurable_uncurry_primePoly hX (primesIco z y)
      (fun p hp => prime_of_mem_primesIco hp) σ).norm.pow_const 2
    simp only [primePoly_primesIco] at h2
    exact h2
  have hrw : (Function.uncurry fun (ω : Ω) (h : ℝ) => Set.indicator (S h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω)
      = Set.indicator {p : Ω × ℝ | p.1 ∈ S p.2}
        (Function.uncurry fun (ω : Ω) (h : ℝ) =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2) := by
    funext p
    by_cases hp : p.1 ∈ S p.2
    · have h1 := Set.indicator_of_mem hp
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ p.2) ω‖ ^ 2)
      have h2 := Set.indicator_of_mem (a := p) (s := {p : Ω × ℝ | p.1 ∈ S p.2}) hp
        (Function.uncurry fun (ω : Ω) (h : ℝ) =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2)
      rw [Function.uncurry_apply_pair, h1, h2]
      rfl
    · have h1 := Set.indicator_of_notMem hp
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ p.2) ω‖ ^ 2)
      have h2 := Set.indicator_of_notMem (a := p) (s := {p : Ω × ℝ | p.1 ∈ S p.2}) hp
        (Function.uncurry fun (ω : Ω) (h : ℝ) =>
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
            (shiftLine σ h) ω‖ ^ 2)
      rw [Function.uncurry_apply_pair, h1, h2]
  rw [hrw]
  exact hbase.indicator hS

/-- The uncurried restricted integrand is product-integrable, which is what the swap needs.

The case `σ ≥ 0` of `RMF.integrable_uncurry_indicator_normSq_primesIco_signed`. -/
lemma integrable_uncurry_indicator_normSq_primesIco {X : ℕ → Ω → ℂ} {μ : Measure Ω}
    (hX : IsRademacherPrimeValues X μ) (z y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {I : Set ℝ}
    (hI : volume I ≠ ⊤) (S : ℝ → Set Ω) (hS : MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2}) :
    Integrable (Function.uncurry fun (ω : Ω) (h : ℝ) => Set.indicator (S h)
        (fun ω => ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) z y
          (shiftLine σ h) ω‖ ^ 2) ω)
      (μ.prod (volume.restrict I)) := by
  exact integrable_uncurry_indicator_normSq_primesIco_signed hX z y (by linarith) hI S hS

/-! ### What the two give

`RMF.integral_rpow_le_of_goodSets`, the interpolation over the levels `a_k = k/(1-q)`, asks for
four things:

* `hdec` — `RMF.setIntegral_le_decomposition`, one line of arithmetic;
* `hZmean` — `RMF.integral_normSq_randomEulerProductIco_le_mertens`: the interpolation's constant
  is quadratic in the mean, so normalising to `E Z ≤ 1` keeps the constant independent of `x`,
  `T` and `q` and puts `(T²·log x)^q` outside;
* `Gbad` — Proposition II;
* `Gint` — Proposition I at each height, integrated over the window
  (`RMF.integral_setIntegral_indicator_le_of_per_height`).

The space is fixed before the constants here, unlike in Proposition I, because Proposition II's
own input (`RMF.exists_const_measureReal_notMem_harperGoodRangeAdd_of_top`) is stated that way. -/

set_option maxHeartbeats 1600000 in
-- one proof carries the whole assembly: four fields of the interpolation, each with its own
-- Fubini and its own envelope, over a goal the size of the statement
/-- **The mesoscopic chaos estimate at a shift of either sign.**  As
`RMF.exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher`, for
`σ ≥ -1/12` with `|σ|·log x ≤ 1` and, when `σ < 0`, `2|σ|·log x ≤ 1`; the first moment that
normalises the process is `RMF.integral_normSq_randomEulerProductIco_le_mertens_signed`, at `e³⁷`
for `e²¹`.  A band of Proposition B (`RMF/Weighted/PropositionB.lean`) needs it at its shift
`½ - c`, `2c·log z ≤ 1`. -/
theorem exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher_signed :
    ∃ (D₀ t₀ : ℕ) (x₀ Klo A : ℝ), 4 ≤ D₀ ∧ 4 ≤ Klo ∧ Real.exp (D₀ : ℝ) ≤ Klo ∧ 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ T q : ℝ) (z D : ℕ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          2 ≤ z → (z : ℝ) ≤ x → z ≤ ⌊x⌋₊ + 1 →
          (z : ℝ) ≤ blockScale (harperOffset D x) 0 →
          -(1 / 12) ≤ σ → |σ| * Real.log x ≤ 1 → (0 ≤ σ ∨ 2 * |σ| * Real.log x ≤ 1) →
          0 ≤ q → q ≤ 1 →
          0 < T → T ≤ 1 → 1 ≤ T * Real.log z →
          Klo ≤ T * Real.exp (harperOffset D x) →
          T * Real.exp (harperOffset D x) ≤ Real.exp 4 * Klo →
          t₀ ≤ harperBlockCount D x - 3 →
            (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (T ^ 2 * Real.log x) ^ q
                * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - 3 : ℕ) : ℝ)) ^ (-q) := by
  classical
  obtain ⟨D₀, n₀, x₀, a₀I, A₁, B, Tsh, hD₀, hA₁, hB, hTsh, HI⟩ :=
    exists_setIntegral_mesoGood_normSq_randomEulerProductIco_le_rademacher_signed
  obtain ⟨a₀II, C₂', hC₂', HII⟩ :=
    exists_const_measureReal_notMem_mesoGood_le_rademacher_signed (Ω' := Ω)
  set a₀ : ℝ := max (max a₀I a₀II) 1 with ha₀def
  set Klo : ℝ := max (max 4 (Tsh * Real.exp 1)) (Real.exp (D₀ : ℝ)) with hKlodef
  set C₂ : ℝ := max (max A₁ (C₂' * (Real.exp 4 * Klo))) 1 with hC₂def
  set Kfin : ℝ := 3 * (max 1 1 + max 1 (2 * C₂ * (max a₀ 3 + 1))
      + 2 * (max 1 (2 * C₂) * max 1 (2 * C₂)) + max 1 (2 * C₂) * max 1 1) with hKfindef
  have hC₂1 : (1 : ℝ) ≤ C₂ := le_max_right _ _
  have hC₂0 : (0 : ℝ) < C₂ := by linarith
  have hKfin0 : (0 : ℝ) < Kfin := by
    have h1 : (1 : ℝ) ≤ max 1 (1 : ℝ) := le_max_left _ _
    have h2 : (1 : ℝ) ≤ max 1 (2 * C₂ * (max a₀ 3 + 1)) := le_max_left _ _
    have h3 : (1 : ℝ) ≤ max 1 (2 * C₂) := le_max_left _ _
    rw [hKfindef]
    nlinarith
  refine ⟨D₀, max (2 * n₀) (⌈max a₀ 3⌉₊ ^ 2), max x₀ 2, Klo, Real.exp 37 * Kfin,
    hD₀, le_trans (le_max_left _ _) (le_max_left _ _), le_max_right _ _, by positivity, ?_⟩
  intro Y ν hY x σ T q z D hx hDD hDlog hz2 hzx hzn hzb hσ hσx hσm hq0 hq1 hT0 hT1 hTz hKlo hKb
    ht₀
  haveI := hY.isProbabilityMeasure
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hD4 : 4 ≤ D := le_trans hD₀ hDD
  have hexp3 : (10 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [h3]
    nlinarith [h1]
  have hA₁C₂ : A₁ ≤ C₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hTe0 : (0 : ℝ) < T / Real.exp 1 := div_pos hT0 (Real.exp_pos 1)
  have he1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTe : T / Real.exp 1 ≤ T := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
  have hvolfin : volume (Set.Icc (T / Real.exp 1) T) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hvol : (volume (Set.Icc (T / Real.exp 1) T)).toReal = T - T / Real.exp 1 := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  -- the normalising constant, and the two processes
  set M : ℝ := Real.exp 37 * (T ^ 2 * Real.log x) with hMdef
  have hM0 : (0 : ℝ) < M := by rw [hMdef]; positivity
  set Zf : Ω → ℝ := fun ω => M⁻¹ * ∫ h in Set.Icc (T / Real.exp 1) T,
    ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
      (shiftLine σ h) ω‖ ^ 2 with hZfdef
  set Rf : (ℝ → Set Ω) → Ω → ℝ := fun S ω => M⁻¹ * ∫ h in Set.Icc (T / Real.exp 1) T,
    Set.indicator (S h) (fun ω => ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ω
    with hRfdef
  set t : ℕ := harperBlockCount D x - 3 with htdef
  set Gset : ℝ → ℝ → Set Ω := fun a h =>
    mesoGood Y (harperOffset D x) B t ⌈a / 4⌉₊ a (fun j => 2 * Real.log j) (shiftLine σ h)
    with hGsetdef
  have hZ0 : ∀ ω, 0 ≤ Zf ω := fun ω =>
    mul_nonneg (by positivity) (integral_nonneg fun h => sq_nonneg _)
  have hR0 : ∀ (S : ℝ → Set Ω) (ω : Ω), 0 ≤ Rf S ω := fun S ω =>
    mul_nonneg (by positivity)
      (integral_nonneg fun h => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
  have hZi : Integrable Zf ν :=
    (integrable_setIntegral_normSq_primesIco_signed hY z (⌊x⌋₊ + 1) (by linarith) hTe).const_mul _
  have hRi : ∀ S : ℝ → Set Ω, (∀ h, MeasurableSet (S h)) →
      MeasurableSet {p : Ω × ℝ | p.1 ∈ S p.2} → Integrable (Rf S) ν := fun S _ hS =>
    (integrable_setIntegral_indicator_normSq_primesIco_signed hY z (⌊x⌋₊ + 1) (by linarith) hTe
      S hS).const_mul _
  have hdec : ∀ (S : ℕ → ℝ → Set Ω) (ω : Ω) (r m : ℕ), r ≤ m →
      Zf ω ≤ Rf (S r) ω
        + (∑ j ∈ Finset.Ico r m,
            Set.indicator {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T, ω ∉ S j h}
              (fun _ => (1 : ℝ)) ω * Rf (S (j + 1)) ω)
        + Set.indicator {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T, ω ∉ S m h}
            (fun _ => (1 : ℝ)) ω * Zf ω := fun S ω r m hrm =>
    setIntegral_le_decomposition (fun _ _ => sq_nonneg _) measurableSet_Icc
      (inv_nonneg.2 hM0.le) S ω r m hrm
  -- the per-height first moment
  have hmert : ∀ h : ℝ, (∫ ω, ‖randomEulerProductIco
      (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2 ∂ν)
      ≤ Real.exp 37 * (T * Real.log x) := fun h =>
    integral_normSq_randomEulerProductIco_le_mertens_signed hY hz2 hzx hσm hT0 hT1 hTz
      (re_shiftLine σ h)
  -- `E Z ≤ 1`
  have hZmean : (∫ ω, Zf ω ∂ν) ≤ 1 := by
    have hInt : Integrable (Function.uncurry fun (ω : Ω) (tt : ℝ) =>
        Set.indicator (Set.univ : Set Ω) (fun ω => ‖randomEulerProductIco
          (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
            (shiftLine σ tt) ω‖ ^ 2) ω)
        (ν.prod (volume.restrict (Set.Icc (T / Real.exp 1) T))) := by
      simpa only [Set.indicator_univ] using
        integrable_uncurry_normSq_shiftLine_primesIco hY z (⌊x⌋₊ + 1) (by linarith)
          (I := Set.Icc (T / Real.exp 1) T) hvolfin
    have h := integral_setIntegral_indicator_le_of_per_height
      (L := fun _ => (Set.univ : Set Ω))
      (g := fun (tt : ℝ) ω => ‖randomEulerProductIco
        (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1) (shiftLine σ tt) ω‖ ^ 2)
      measurableSet_Icc hvolfin hInt (fun tt _ => by
        simpa only [Set.indicator_univ] using hmert tt)
    simp only [Set.indicator_univ] at h
    rw [hvol] at h
    rw [hZfdef, integral_const_mul, inv_mul_le_iff₀ hM0, mul_one, hMdef]
    refine le_trans h ?_
    nlinarith [Real.exp_pos (37 : ℝ), hlogx, hT0, hTe0]
  -- the good family
  have hGmeas : ∀ a h, MeasurableSet (Gset a h) := fun a h =>
    measurableSet_mesoGood hY _ _ _ _ _ _ _
  have hYm : ∀ p : Nat.Primes, Measurable (Y ((p : Nat.Primes) : ℕ)) := fun p =>
    hY.measurable ((p : Nat.Primes) : ℕ) p.2
  have hGunc : ∀ a : ℝ, MeasurableSet {p : Ω × ℝ | p.1 ∈ Gset a p.2} := fun a =>
    measurableSet_freeStartBarrierAdd_uncurry hYm σ (harperOffset D x) ⌈a / 4⌉₊ t
      (fun j => -a - B * (j : ℝ)) (fun j => a + (j : ℝ) + 2 * Real.log j)
  have hGbad : ∀ a : ℝ, a₀ ≤ a →
      ν.real {ω | ∃ h ∈ Set.Icc (T / Real.exp 1) T, ω ∉ Gset a h}
        ≤ C₂ * Real.exp (-(2 * a)) := by
    intro a ha
    have haII : a₀II ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
    have hTθ1 : (1 : ℝ) ≤ T * Real.exp (harperOffset D x) :=
      le_trans (le_trans (le_trans (by norm_num) (le_max_left (4 : ℝ) (Tsh * Real.exp 1)))
        (le_max_left _ _)) hKlo
    have h := HII 1 3 (by norm_num) (Real.one_le_exp (by positivity)) Y ν hY D x σ 1
      a B T hD4 hx1 hDlog hσ (by norm_num) le_rfl hσx haII hB hT0 hTθ1
    refine le_trans h ?_
    have hstep : C₂' * (T * Real.exp (harperOffset D x)) ≤ C₂ := by
      refine le_trans (mul_le_mul_of_nonneg_left hKb hC₂'.le) ?_
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
  have hGint : ∀ a : ℝ, a₀ ≤ a → 2 * ⌈a / 4⌉₊ ≤ t → n₀ ≤ t - ⌈a / 4⌉₊ →
      (∫ ω, Rf (Gset a) ω ∂ν) ≤ C₂ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊)) := by
    intro a ha h2r hn
    have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
    have haI : a₀I ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
    have hr1 : 1 ≤ ⌈a / 4⌉₊ := Nat.ceil_pos.2 (by linarith)
    have hrt : ⌈a / 4⌉₊ ≤ t := by omega
    have hra : ((⌈a / 4⌉₊ : ℕ) : ℝ) ≤ a / 4 + 1 :=
      (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ a / 4)).le
    have hmin0 : (0 : ℝ) ≤ min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊)) :=
      le_min zero_le_one (by positivity)
    -- Proposition I at each height
    have hper : ∀ h ∈ Set.Icc (T / Real.exp 1) T,
        (∫ ω, Set.indicator (Gset a h) (fun ω => ‖randomEulerProductIco
            (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
              (shiftLine σ h) ω‖ ^ 2) ω ∂ν)
          ≤ A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))
            * (Real.exp 37 * (T * Real.log x)) := by
      intro h hh
      have hh0 : (0 : ℝ) < h := lt_of_lt_of_le hTe0 hh.1
      have him : (shiftLine σ h).im = h := im_shiftLine σ h
      have hTθ4 : (4 : ℝ) ≤ T * Real.exp (harperOffset D x) :=
        le_trans (le_trans (le_max_left (4 : ℝ) (Tsh * Real.exp 1)) (le_max_left _ _)) hKlo
      have hsq : (2 * (shiftLine σ h).im) ^ 2 ≤ Real.exp (harperOffset D x) := by
        rw [him]
        exact sq_two_mul_le_exp_harperOffset hT0 hT1 hh0 hh.2 hTθ4
      have hTshle : Tsh ≤ 2 * (shiftLine σ h).im * Real.exp (harperOffset D x) := by
        rw [him]
        have hTsh' : Tsh * Real.exp 1 ≤ T * Real.exp (harperOffset D x) :=
          le_trans (le_trans (le_max_right (4 : ℝ) (Tsh * Real.exp 1)) (le_max_left _ _)) hKlo
        have hE1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
        have hEθ : (0 : ℝ) < Real.exp (harperOffset D x) := Real.exp_pos _
        have hstep : 2 * (T / Real.exp 1) * Real.exp (harperOffset D x)
            ≤ 2 * h * Real.exp (harperOffset D x) := by
          have h2 : 2 * (T / Real.exp 1) ≤ 2 * h := by linarith [hh.1]
          exact mul_le_mul_of_nonneg_right h2 hEθ.le
        have hlow : Tsh ≤ 2 * (T / Real.exp 1) * Real.exp (harperOffset D x) := by
          have hid : 2 * (T / Real.exp 1) * Real.exp (harperOffset D x)
              = 2 * (T * Real.exp (harperOffset D x)) / Real.exp 1 := by
            field_simp
          rw [hid, le_div_iff₀ hE1]
          nlinarith [hTsh', hTsh.le, mul_nonneg hT0.le hEθ.le]
        linarith
      have hI := HI Ω Y ν hY x σ a 1 z D ⌈a / 4⌉₊ 3 (shiftLine σ h)
        (fun j => 2 * Real.log j) hx0 hDD hDlog (re_shiftLine σ h) (by linarith) hσx
        (by push_cast; linarith [hexp3]) (by rw [him]; linarith) hsq hTshle
        hzb hzn haI ha1 hr1 hrt hra hn
        (fun j hj _ => by
          have h0 : (0 : ℝ) ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
          rw [abs_of_nonneg (by linarith)]
          linarith)
      rw [integral_indicator (hGmeas a h)]
      refine le_trans hI ?_
      exact mul_le_mul_of_nonneg_left (hmert h)
        (mul_nonneg hA₁.le hmin0)
    have hInt := integrable_uncurry_indicator_normSq_primesIco_signed hY z (⌊x⌋₊ + 1)
      (σ := σ) (by linarith)
      (I := Set.Icc (T / Real.exp 1) T) hvolfin (Gset a) (hGunc a)
    have h := integral_setIntegral_indicator_le_of_per_height measurableSet_Icc hvolfin
      hInt hper
    rw [hvol] at h
    rw [hRfdef, integral_const_mul, inv_mul_le_iff₀ hM0]
    refine le_trans h ?_
    have hu : (0 : ℝ) ≤ A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊)) :=
      mul_nonneg hA₁.le hmin0
    have hfac : (T - T / Real.exp 1) * T ≤ T ^ 2 := by nlinarith [hTe0, hT0]
    have hrest : (0 : ℝ) ≤ A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))
        * (Real.exp 37 * Real.log x) := mul_nonneg hu (by positivity)
    have hbase : (T - T / Real.exp 1)
        * (A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊)) * (Real.exp 37 * (T * Real.log x)))
        ≤ M * (A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) := by
      rw [hMdef]
      calc (T - T / Real.exp 1)
            * (A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))
              * (Real.exp 37 * (T * Real.log x)))
          = ((T - T / Real.exp 1) * T)
            * (A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))
              * (Real.exp 37 * Real.log x)) := by ring
        _ ≤ T ^ 2 * (A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))
              * (Real.exp 37 * Real.log x)) := mul_le_mul_of_nonneg_right hfac hrest
        _ = Real.exp 37 * (T ^ 2 * Real.log x)
              * (A₁ * min 1 (a / Real.sqrt ((t : ℝ) - ⌈a / 4⌉₊))) := by ring
    refine le_trans hbase ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    exact mul_le_mul_of_nonneg_right hA₁C₂ hmin0
  -- the interpolation
  have hT1' : 2 * n₀ ≤ t := le_trans (le_max_left _ _) ht₀
  have hT2' : ⌈max a₀ 3⌉₊ ^ 2 ≤ t := le_trans (le_max_right _ _) ht₀
  have hmain := integral_rpow_le_of_goodSets (ν := ν) (Z := Zf) (Rst := Rf)
    (win := Set.Icc (T / Real.exp 1) T) (q := q) (t := t) (n₀ := n₀) (a₀ := a₀)
    (C₁ := 1) (C₂ := C₂) hZ0 hZi hR0 hRi hdec hq0 hq1 one_pos hC₂0 hZmean hT1' hT2'
    Gset hGmeas hGunc hGbad hGint
  -- undo the normalisation
  have hZeq : ∀ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
      ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω) z (⌊x⌋₊ + 1)
        (shiftLine σ h) ω‖ ^ 2) = M * Zf ω := by
    intro ω
    rw [hZfdef, ← mul_assoc, mul_inv_cancel₀ hM0.ne', one_mul]
  simp only [hZeq]
  have hpow : ∀ ω : Ω, (M * Zf ω) ^ q = M ^ q * Zf ω ^ q := fun ω =>
    Real.mul_rpow hM0.le (hZ0 ω)
  simp only [hpow]
  rw [integral_const_mul]
  have hMq : M ^ q ≤ Real.exp 37 * (T ^ 2 * Real.log x) ^ q := by
    rw [hMdef, Real.mul_rpow (Real.exp_pos 37).le (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (Real.exp 37) ^ q ≤ (Real.exp 37) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (37 : ℝ)]) hq1
      _ = Real.exp 37 := Real.rpow_one _
  have hint0 : (0 : ℝ) ≤ ∫ ω, Zf ω ^ q ∂ν :=
    integral_nonneg fun ω => Real.rpow_nonneg (hZ0 ω) q
  have htarget0 : (0 : ℝ) ≤ (1 + (1 - q) * Real.sqrt ((t : ℕ) : ℝ)) ^ (-q) :=
    Real.rpow_nonneg (by positivity) _
  calc M ^ q * ∫ ω, Zf ω ^ q ∂ν
      ≤ M ^ q * (Kfin * (1 + (1 - q) * Real.sqrt ((t : ℕ) : ℝ)) ^ (-q)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hM0.le q)
        refine le_trans hmain (le_of_eq ?_)
        rw [hKfindef]
    _ ≤ (Real.exp 37 * (T ^ 2 * Real.log x) ^ q)
          * (Kfin * (1 + (1 - q) * Real.sqrt ((t : ℕ) : ℝ)) ^ (-q)) := by
        refine mul_le_mul_of_nonneg_right hMq (by positivity)
    _ = Real.exp 37 * Kfin * (T ^ 2 * Real.log x) ^ q
          * (1 + (1 - q) * Real.sqrt ((t : ℕ) : ℝ)) ^ (-q) := by ring

set_option maxHeartbeats 1600000 in
-- one application of the `_signed` theorem above; the limit is taken from it
/-- **The mesoscopic chaos estimate.**  For a block over the window `[T/e, T]` split at `z`, with
`t = harperBlockCount D x - 3` the depth, uniformly for `0 ≤ q ≤ 1`,
`E[(∫_{T/e}^{T}‖F_{[z,x]}(½+σ+ih)‖²dh)^q]  ≤  A·(T²·log x)^q·(1 + (1-q)√t)^{-q}`;
the level `a_k = k/(1-q)` of the decomposition is what makes it uniform in `q`.  The offset
hypotheses `Klo ≤ T·e^{harperOffset D x} ≤ e⁴·Klo` are met for every `0 < T ≤ 1` by
`RMF.exists_harperOffset_at_split_scale` at `K := Klo`.  The `σ ≥ 0` case of `…_signed`. -/
theorem exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher :
    ∃ (D₀ t₀ : ℕ) (x₀ Klo A : ℝ), 4 ≤ D₀ ∧ 4 ≤ Klo ∧ Real.exp (D₀ : ℝ) ≤ Klo ∧ 0 < A ∧
      ∀ (Y : ℕ → Ω → ℂ) (ν : Measure Ω), IsRademacherPrimeValues Y ν →
        ∀ (x σ T q : ℝ) (z D : ℕ),
          x₀ ≤ x → D₀ ≤ D → (D : ℝ) ≤ Real.log (Real.log x) →
          2 ≤ z → (z : ℝ) ≤ x → z ≤ ⌊x⌋₊ + 1 →
          (z : ℝ) ≤ blockScale (harperOffset D x) 0 →
          0 ≤ σ → σ * Real.log x ≤ 1 → 0 ≤ q → q ≤ 1 →
          0 < T → T ≤ 1 → 1 ≤ T * Real.log z →
          Klo ≤ T * Real.exp (harperOffset D x) →
          T * Real.exp (harperOffset D x) ≤ Real.exp 4 * Klo →
          t₀ ≤ harperBlockCount D x - 3 →
            (∫ ω, (∫ h in Set.Icc (T / Real.exp 1) T,
                ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => Y p ω)
                  z (⌊x⌋₊ + 1) (shiftLine σ h) ω‖ ^ 2) ^ q ∂ν)
              ≤ A * (T ^ 2 * Real.log x) ^ q
                * (1 + (1 - q) * Real.sqrt ((harperBlockCount D x - 3 : ℕ) : ℝ)) ^ (-q) := by
  obtain ⟨D₀, t₀, x₀, Klo, A, hD₀, hKlo, hKloD, hA, H⟩ :=
    exists_const_integral_rpow_setIntegral_normSq_randomEulerProductIco_le_rademacher_signed
      (Ω := Ω)
  refine ⟨D₀, t₀, x₀, Klo, A, hD₀, hKlo, hKloD, hA, ?_⟩
  intro Y ν hY x σ T q z D hx hDD hDlog hz2 hzx hzn hzb hσ hσx hq0 hq1 hT0 hT1 hTz hKl hKb ht₀
  exact H Y ν hY x σ T q z D hx hDD hDlog hz2 hzx hzn hzb (by linarith)
    (by rw [abs_of_nonneg hσ]; exact hσx) (Or.inl hσ) hq0 hq1 hT0 hT1 hTz hKl hKb ht₀

end RMF
