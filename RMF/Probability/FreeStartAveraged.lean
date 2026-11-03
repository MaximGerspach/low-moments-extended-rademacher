/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Probability.BlockComparisonSharp
import RMF.Probability.BarrierSupermartingale

/-!
# Proposition 5's upper half, averaged over the restart

The walk is restarted once, at the free start `r`, and averaged over the position `W_r` rather
than charged at the worst position.  The blocks are independent under the tilt, the suffix is
compared with the Gaussian walk for each position, and Probability Result 1 is used in an affine
form, so that it integrates against the law of `W_r`.  The level becomes `a` plus the drift, the
logarithm and `Var W_r/(4a)`.  Result 1 enters as the property `RMF.Result1Affine` of its
constants, which the Gaussian supermartingale (`RMF.result1Affine_sharp`) provides.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RMF

/-! ### Prefix and suffix of an independent family -/

section Indep

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The prefix is independent of a later block**, for any independent family: the proof of
`RMF.IsGaussianWalk.indepFun_prefixSums_blockSums` uses nothing else. -/
lemma indepFun_prefixSums_blockSums_of_iIndepFun {L : ℕ → Ω → ℝ} (hind : iIndepFun L μ)
    (hmeas : ∀ m, Measurable (L m)) (k n : ℕ) :
    IndepFun (fun ω => prefixSums k fun i => L i ω)
      (fun ω => blockSums k n fun i => L i ω) μ := by
  have hdisj : Disjoint (Finset.range k) (Finset.Ico k n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    omega
  exact (hind.indepFun_finset _ _ hdisj hmeas).comp
    (measurable_prefixSums k) (measurable_blockSums k n)

end Indep

/-! ### Probability Result 1 in affine form -/

/-- The constant `√(πv₊/2) + β(1 + log 2) + 2β log(KT)`; `RMF.Result1Affine` is supplied at
`RMF.result1SharpShift` instead (`RMF.result1Affine_sharp`). -/
noncomputable def result1AffineShift (vmax β K T : ℝ) : ℝ :=
  √(Real.pi * vmax / 2) + β * (1 + Real.log 2) + 2 * β * Real.log (K * T)

/-! ### Probability Result 1 in affine form, as a property of its constants -/

universe u

/-- **Probability Result 1 in affine form at the constants `K`, `T`, `σ`**: every Gaussian walk
with variances in `[v₋, v₊]` stays below `ℓ + β log j` up to `n` with probability at most
`K(ℓ + σ)/((1 - 2β/T)√n)`, for every level `ℓ ≥ 0` and every `n ≥ 1`. -/
def Result1Affine (vmin vmax β K T σ : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ℕ → Ω → ℝ)
    (v : ℕ → ℝ≥0), IsGaussianWalk G v μ → VarBracket v vmin vmax → ∀ ℓ : ℝ, 0 ≤ ℓ →
      ∀ n : ℕ, 1 ≤ n → μ.real {ω | ∀ j ≤ n, walk G j ω ≤ ℓ + β * Real.log j}
        ≤ K * ((ℓ + σ) / (1 - 2 * β / T)) / √(n : ℝ)

/-- **`RMF.Result1Affine` at the Gaussian constant**, at `σ = result1SharpShift v₊ β K T M` and
`K²(M-1)πv₋ ≥ 2M` (`RMF.IsGaussianWalk.measureReal_forall_le_log_le_affine_sharp`). -/
theorem result1Affine_sharp {vmin vmax β K T : ℝ} {M : ℕ} (hβ : 0 ≤ β) (hK : 0 < K)
    (hT : 2 * β < T) (hKT : 1 ≤ K * T) (hM : 2 ≤ M)
    (hKM : 2 * (M : ℝ) ≤ K ^ 2 * ((M : ℝ) - 1) * (Real.pi * vmin))
    (hKσ : 1 ≤ K * result1SharpShift vmax β K T M) :
    Result1Affine.{u} vmin vmax β K T (result1SharpShift vmax β K T M) := by
  intro Ω _ μ _ G v h hv ℓ hℓ n hn
  exact h.measureReal_forall_le_log_le_affine_sharp hv hβ hK hT hKT hM hKM hKσ hℓ hn

/-! ### The suffix at a fixed position -/

section Suffix

variable {Ω : Type*} {Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']

set_option maxHeartbeats 1000000 in
-- the suffix argument of Proposition 5's upper half, with the position `x` as a parameter
/-- **The suffix from a fixed position.**  If the walk stands at `x ∈ [-a - cr, a + r + h(r)]` at
the free start `r`, the rest of the tube `[-a - cj, a + j + h(j)]` has probability at most
`(1 + ε)K(ℓ + σ)/((1 - 2β/T)√(n - r))`, with `ℓ = a + r + 2 + 2C + β(log r + log 2) - x ≥ 0`:
Lemma 4 on the suffix (`RMF.measure_barrierEvent_le`), the drift at cost `2C`
(`RMF.barrierEvent_recentre`), and Probability Result 1 in affine form (`RMF.Result1Affine`). -/
theorem suffix_barrierEvent_le {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {G : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax)
    {L : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {θ : ℕ → ℝ} {w M M' hf : ℕ → ℝ} {n r : ℕ}
    {ε a c C β K T x : ℝ}
    (hL : ∀ m, Measurable (L m)) (hN : ∀ m, Measurable (N m))
    (hNG : ∀ m ω, N m ω = G m ω + θ m)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C)
    (hw : ∀ m, 0 < w m) (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hM0 : ∀ j, 0 ≤ M j)
    (hMenv : ∀ i : ℕ, 1 ≤ i → i ≤ n - r →
      2 * a + (1 + c) * r + c * i + |hf r| ≤ M (r + i) ∧
        2 * a + (1 + c) * r + i + hf (r + i) ≤ M (r + i))
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) (hε0 : 0 ≤ ε)
    (hcmp : IsWindowComparison P Q (fun m => L (m + r)) (fun m => N (m + r))
      (fun m => w (m + r)) (fun m => M' (m + r)) (n - r) ε)
    (hr1 : 1 ≤ r) (hrn : r < n) (hβ : 0 ≤ β)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ β * Real.log j)
    (hC : 0 ≤ C) {σ : ℝ} (hR1 : Result1Affine.{u} vmin vmax β K T σ)
    (hx : x ∈ Set.Icc (-a - c * r) (a + r + hf r)) :
    (P (barrierEvent (fun m => L (m + r)) (n - r) (fun i => -a - c * ((r + i : ℕ) : ℝ) - x)
        (fun i => a + ((r + i : ℕ) : ℝ) + hf (r + i) - x))).toReal
      ≤ (1 + ε) * (K * ((a + r + 2 + 2 * C + β * (Real.log r + Real.log 2) - x
          + σ) / (1 - 2 * β / T)) / √((n - r : ℕ) : ℝ)) := by
  have hkn : r ≤ n := hrn.le
  have hnr1 : 1 ≤ n - r := by omega
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrR
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hx1 := hx.1
  have hx2 := hx.2
  have hhfr := hhf r hr1 hkn
  set ℓ := a + r + 2 + 2 * C + β * (Real.log r + Real.log 2) - x with hℓdef
  have hℓ : 0 ≤ ℓ := by
    rw [hℓdef]
    have : 0 ≤ β * Real.log 2 := mul_nonneg hβ hlog2
    nlinarith
  -- Lemma 4 on the suffix
  have hMs : ∀ i, 1 ≤ i → i ≤ n - r →
      -M (r + i) ≤ -a - c * ((r + i : ℕ) : ℝ) - x ∧
        a + ((r + i : ℕ) : ℝ) + hf (r + i) - x ≤ M (r + i) := by
    intro i hi1 hin
    obtain ⟨h1, h2⟩ := hMenv i hi1 hin
    have habs : hf r ≤ |hf r| := le_abs_self _
    push_cast
    constructor <;> nlinarith
  have hMMs : ∀ m, m < n - r → M (r + m) + M (r + (m + 1)) + w (m + r) ≤ M' (m + r) := by
    intro m hm
    have h := hMM (r + m) (by omega)
    rw [show m + r = r + m from Nat.add_comm m r]
    exact h
  have h4 := measure_barrierEvent_le (X := fun m => L (m + r)) (N := fun m => N (m + r))
    (w := fun m => w (m + r)) (M := fun j => M (r + j)) (M' := fun m => M' (m + r))
    (n := n - r) (u := fun i => -a - c * ((r + i : ℕ) : ℝ) - x)
    (v := fun i => a + ((r + i : ℕ) : ℝ) + hf (r + i) - x)
    (fun m => hL _) (fun m => hN _) (fun m => hw _)
    (sum_shift_le (fun m => (hw m).le) hkn hwsum) (fun j => hM0 _) hMs hε0 hMMs hcmp
  -- the drift, then the lower barrier
  have hshift := barrierEvent_recentre (N := fun m => N (m + r)) (G := fun m => G (m + r))
    (θ := fun m => θ (m + r)) (C := 2 * C) (n := n - r) (fun m ω => hNG _ _)
    (drift_shift_le hkn hθ)
    (u := fun i => (-a - c * ((r + i : ℕ) : ℝ) - x) - 2)
    (v := fun i => (a + ((r + i : ℕ) : ℝ) + hf (r + i) - x) + 2)
  have hdrop : barrierEvent (fun m => G (m + r)) (n - r)
        (fun i => ((-a - c * ((r + i : ℕ) : ℝ) - x) - 2) - i - 2 * C)
        (fun i => ((a + ((r + i : ℕ) : ℝ) + hf (r + i) - x) + 2) - i + 2 * C)
      ⊆ {ω | ∀ i ≤ n - r, walk (fun m => G (m + r)) i ω ≤ ℓ + β * Real.log i} := by
    intro ω hω i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simpa [walk] using hℓ
    have hb := Set.mem_Icc.1 (hω i hi1 hi)
    have hfi := hhf (r + i) (by omega) (by omega)
    have hlog := log_natCast_add_le hr1 hi1
    have hβlog := mul_le_mul_of_nonneg_left hlog hβ
    push_cast at hb hfi hβlog ⊢
    rw [hℓdef]
    nlinarith [hb.2, hfi, hβlog]
  have hQ : (Q (barrierEvent (fun m => N (m + r)) (n - r)
        (fun i => (-a - c * ((r + i : ℕ) : ℝ) - x) - 2)
        (fun i => (a + ((r + i : ℕ) : ℝ) + hf (r + i) - x) + 2))).toReal
      ≤ Q.real {ω | ∀ i ≤ n - r, walk (fun m => G (m + r)) i ω ≤ ℓ + β * Real.log i} :=
    ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono (le_trans hshift hdrop))
  -- Probability Result 1, in affine form, on the shifted walk
  have hr1' := hR1 Ω' Q (fun m => G (m + r)) (fun i => v (i + r)) (hGw.shift r)
    ⟨hv.pos, fun i => hv.lo (i + r), fun i => hv.hi (i + r)⟩ ℓ hℓ (n - r) hnr1
  refine le_trans h4 (mul_le_mul_of_nonneg_left (le_trans hQ ?_) (by linarith))
  exact hr1'

end Suffix

/-! ### Averaging over the restart -/

section Averaged

variable {Ω : Type*} {Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- `(y - t)⁺ ≤ y²/(4t)` for `t > 0`. -/
lemma max_sub_zero_le_sq_div {y t : ℝ} (ht : 0 < t) : max (y - t) 0 ≤ y ^ 2 / (4 * t) := by
  rw [le_div_iff₀ (by positivity)]
  rcases le_total (y - t) 0 with h | h
  · rw [max_eq_right h, zero_mul]
    positivity
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (y - 2 * t)]

/-- **An event of an independent pair, fibre by fibre**:
`μ((X, Y) ∈ S) = ∫ (law Y)(S_x) d(law X)`. -/
lemma measure_preimage_prod_eq_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} (hX : Measurable X)
    (hY : Measurable Y) (hind : IndepFun X Y μ) {S : Set (α × β)} (hS : MeasurableSet S) :
    μ ((fun ω => (X ω, Y ω)) ⁻¹' S) = ∫⁻ x, (μ.map Y) (Prod.mk x ⁻¹' S) ∂(μ.map X) := by
  rw [← Measure.map_apply (hX.prodMk hY) hS,
    hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, Measure.prod_apply hS]

set_option maxHeartbeats 1000000 in
-- the pair decomposition, the fibre bound and the integration in one proof
/-- **Proposition 5's upper half with the free start averaged.**  For a walk `W` of independent
blocks, compared with a Gaussian walk after the free start `r`, and with `|E W_r - r| ≤ C` and
`Var W_r ≤ V`,
`P(W_j ∈ [-a - cj, a + j + h(j)] ∀ r ≤ j ≤ n)
  ≤ (1 + ε)K(a + 2 + 3C + β(log r + log 2) + V/(4a) + σ)/((1 - 2β/T)√(n - r))`.
The position `W_r` is independent of the suffix, the suffix is bounded at each position by
`RMF.suffix_barrierEvent_le`, and that bound is affine in the position, so it integrates to the
mean position; the positive part costs `E(W_r - κ)⁺ ≤ Var W_r/(4a)`. -/
theorem freeStart_barrier_le_averaged {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {G : ℕ → Ω' → ℝ} {v : ℕ → ℝ≥0} (hGw : IsGaussianWalk G v Q)
    {vmin vmax : ℝ} (hv : VarBracket v vmin vmax)
    {L : ℕ → Ω → ℝ} {N : ℕ → Ω' → ℝ} {θ : ℕ → ℝ} {w M M' hf : ℕ → ℝ} {n r : ℕ}
    {ε a c C β K T V : ℝ}
    (hL : ∀ m, Measurable (L m)) (hLind : iIndepFun L P) (hN : ∀ m, Measurable (N m))
    (hNG : ∀ m ω, N m ω = G m ω + θ m)
    (hθ : ∀ j, j ≤ n → |(∑ m ∈ Finset.range j, θ m) - j| ≤ C)
    (hw : ∀ m, 0 < w m) (hwsum : ∀ j, j ≤ n → ∑ m ∈ Finset.range j, w m ≤ 2)
    (hM0 : ∀ j, 0 ≤ M j)
    (hMenv : ∀ i : ℕ, 1 ≤ i → i ≤ n - r →
      2 * a + (1 + c) * r + c * i + |hf r| ≤ M (r + i) ∧
        2 * a + (1 + c) * r + i + hf (r + i) ≤ M (r + i))
    (hMM : ∀ m, m < n → M m + M (m + 1) + w m ≤ M' m) (hε0 : 0 ≤ ε)
    (hcmp : IsWindowComparison P Q (fun m => L (m + r)) (fun m => N (m + r))
      (fun m => w (m + r)) (fun m => M' (m + r)) (n - r) ε)
    (hr1 : 1 ≤ r) (hrn : r < n) (hβ : 0 ≤ β)
    (hhf : ∀ j, 1 ≤ j → j ≤ n → hf j ≤ β * Real.log j)
    (hC : 0 ≤ C) (hK : 0 < K) (hT : 2 * β < T) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hR1 : Result1Affine.{u} vmin vmax β K T σ) (ha : 0 < a)
    (hWint : Integrable (walk L r) P) (hWmean : |(∫ ω, walk L r ω ∂P) - r| ≤ C)
    (hWsq : Integrable (fun ω => (walk L r ω - ∫ ω', walk L r ω' ∂P) ^ 2) P)
    (hWvar : ∫ ω, (walk L r ω - ∫ ω', walk L r ω' ∂P) ^ 2 ∂P ≤ V) :
    (P {ω | ∀ j, r ≤ j → j ≤ n → walk L j ω ∈ Set.Icc (-a - c * j) (a + j + hf j)}).toReal
      ≤ (1 + ε) * (K * ((a + 2 + 3 * C + β * (Real.log r + Real.log 2) + V / (4 * a)
          + σ) / (1 - 2 * β / T)) / √((n - r : ℕ) : ℝ)) := by
  have hkn : r ≤ n := hrn.le
  have hnr1 : 1 ≤ n - r := by omega
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrR
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - 2 * β / T := by
    rw [sub_pos, div_lt_one hT0]
    exact hT
  have hsn : 0 < √((n - r : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnr1)
  set κ := a + r + 2 + 2 * C + β * (Real.log r + Real.log 2) with hκdef
  set F := (1 + ε) * K / ((1 - 2 * β / T) * √((n - r : ℕ) : ℝ)) with hFdef
  have hF0 : 0 ≤ F := by positivity
  set EW := ∫ ω, walk L r ω ∂P with hEW
  -- the prefix, the suffix, and the event of the pair
  set Φ : Ω → (ℕ → ℝ) := fun ω => prefixSums r fun i => L i ω with hΦdef
  set Ψ : Ω → (ℕ → ℝ) := fun ω => blockSums r n fun i => L i ω with hΨdef
  have hΦ : Measurable Φ :=
    (measurable_prefixSums r).comp (measurable_pi_lambda _ fun i => hL (i : ℕ))
  have hΨ : Measurable Ψ :=
    (measurable_blockSums r n).comp (measurable_pi_lambda _ fun i => hL (i : ℕ))
  have hind : IndepFun Φ Ψ P := indepFun_prefixSums_blockSums_of_iIndepFun hLind hL r n
  have hΦr : ∀ ω, Φ ω r = walk L r ω := fun ω => prefixSums_comp L le_rfl ω
  have hΨi : ∀ ω (i : ℕ), i ≤ n - r → Ψ ω (r + i) = walk (fun m => L (m + r)) i ω := by
    intro ω i hi
    rw [hΨdef]
    simp only
    rw [blockSums_comp L (by omega) (by omega) ω, walk_shift]
  set S : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {p | p.1 r ∈ Set.Icc (-a - c * r) (a + r + hf r) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ n - r → p.2 (r + i) ∈ Set.Icc (-a - c * ((r + i : ℕ) : ℝ) - p.1 r)
        (a + ((r + i : ℕ) : ℝ) + hf (r + i) - p.1 r)} with hSdef
  have hS : MeasurableSet S := by
    have hrw : S = (Prod.fst ⁻¹' {φ : ℕ → ℝ | φ r ∈ Set.Icc (-a - c * r) (a + r + hf r)})
        ∩ ⋂ i ∈ Set.Icc 1 (n - r), {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 (r + i)
          ∈ Set.Icc (-a - c * ((r + i : ℕ) : ℝ) - p.1 r)
            (a + ((r + i : ℕ) : ℝ) + hf (r + i) - p.1 r)} := by
      ext p
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
        Set.mem_Icc]
      exact and_congr_right fun _ => ⟨fun h i hi => h i hi.1 hi.2, fun h i h1 h2 => h i ⟨h1, h2⟩⟩
    rw [hrw]
    refine MeasurableSet.inter ?_ (MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_)
    · exact measurable_fst ((measurable_pi_apply r) measurableSet_Icc)
    · have h1 : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 (r + i) :=
        (measurable_pi_apply (r + i)).comp measurable_snd
      have h2 : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 r :=
        (measurable_pi_apply r).comp measurable_fst
      exact (measurableSet_le (measurable_const.sub h2) h1).inter
        (measurableSet_le h1 (measurable_const.sub h2))
  have hsub : {ω | ∀ j, r ≤ j → j ≤ n → walk L j ω ∈ Set.Icc (-a - c * j) (a + j + hf j)}
      ⊆ (fun ω => (Φ ω, Ψ ω)) ⁻¹' S := by
    intro ω hω
    simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq]
    refine ⟨by rw [hΦr]; exact hω r le_rfl hkn, fun i hi1 hin => ?_⟩
    rw [hΦr, hΨi ω i hin, walk_shift]
    have hb := Set.mem_Icc.1 (hω (r + i) (by omega) (by omega))
    push_cast at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  -- the fibre bound
  have hfib : ∀ φ : ℕ → ℝ, (P.map Ψ) (Prod.mk φ ⁻¹' S)
      ≤ ENNReal.ofReal (F * (max (κ - φ r) 0 + σ)) := by
    intro φ
    by_cases hx : φ r ∈ Set.Icc (-a - c * r) (a + r + hf r)
    · have hslice : MeasurableSet (Prod.mk φ ⁻¹' S) := measurable_prodMk_left hS
      have hset : Ψ ⁻¹' (Prod.mk φ ⁻¹' S)
          = barrierEvent (fun m => L (m + r)) (n - r)
              (fun i => -a - c * ((r + i : ℕ) : ℝ) - φ r)
              (fun i => a + ((r + i : ℕ) : ℝ) + hf (r + i) - φ r) := by
        ext ω
        simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, barrierEvent]
        constructor
        · rintro ⟨-, h⟩ i hi1 hin
          rw [← hΨi ω i hin]
          exact h i hi1 hin
        · intro h
          refine ⟨hx, fun i hi1 hin => ?_⟩
          rw [hΨi ω i hin]
          exact h i hi1 hin
      rw [Measure.map_apply hΨ hslice, hset, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      refine ENNReal.ofReal_le_ofReal (le_trans (suffix_barrierEvent_le hGw hv hL hN hNG hθ hw
        hwsum hM0 hMenv hMM hε0 hcmp hr1 hrn hβ hhf hC hR1 hx) (le_of_eq ?_))
      have hpos : 0 ≤ κ - φ r := by
        have hfr := hhf r hr1 hkn
        rw [hκdef]
        have : 0 ≤ β * Real.log 2 := mul_nonneg hβ hlog2
        nlinarith [hx.2]
      rw [max_eq_left hpos, hFdef, hκdef]
      field_simp
    · have hempty : Prod.mk φ ⁻¹' S = ∅ := by
        ext ψ
        simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun h => absurd h hx
      rw [hempty, measure_empty]
      exact zero_le
  -- integrate over the position
  have hmaxint : Integrable (fun ω => max (κ - walk L r ω) 0) P :=
    ((integrable_const κ).sub hWint).pos_part
  have hint : Integrable (fun ω => F * (max (κ - walk L r ω) 0 + σ)) P :=
    (hmaxint.add (integrable_const σ)).const_mul F
  have hlint : (P {ω | ∀ j, r ≤ j → j ≤ n → walk L j ω ∈ Set.Icc (-a - c * j) (a + j + hf j)})
      ≤ ENNReal.ofReal (∫ ω, F * (max (κ - walk L r ω) 0 + σ) ∂P) := by
    calc _ ≤ P ((fun ω => (Φ ω, Ψ ω)) ⁻¹' S) := measure_mono hsub
      _ = ∫⁻ φ, (P.map Ψ) (Prod.mk φ ⁻¹' S) ∂(P.map Φ) :=
          measure_preimage_prod_eq_lintegral hΦ hΨ hind hS
      _ ≤ ∫⁻ φ, ENNReal.ofReal (F * (max (κ - φ r) 0 + σ)) ∂(P.map Φ) := lintegral_mono hfib
      _ = ∫⁻ ω, ENNReal.ofReal (F * (max (κ - walk L r ω) 0 + σ)) ∂P := by
          rw [lintegral_map (by fun_prop) hΦ]
          refine lintegral_congr fun ω => ?_
          rw [hΦr]
      _ = ENNReal.ofReal (∫ ω, F * (max (κ - walk L r ω) 0 + σ) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω =>
            mul_nonneg hF0 (add_nonneg (le_max_right _ _) hσ0))).symm
  -- the mean position, and the positive part
  have hEW := abs_le.1 hWmean
  have ht : a ≤ κ - EW := by
    rw [hκdef]
    have : 0 ≤ β * (Real.log r + Real.log 2) := mul_nonneg hβ (by linarith)
    linarith [hEW.2]
  have hpt : ∀ ω, max (κ - walk L r ω) 0
      ≤ (κ - walk L r ω) + (walk L r ω - EW) ^ 2 / (4 * a) := by
    intro ω
    have h1 := max_sub_zero_le_sq_div (y := walk L r ω - EW) (t := κ - EW) (by linarith)
    have h2 : (walk L r ω - EW) ^ 2 / (4 * (κ - EW)) ≤ (walk L r ω - EW) ^ 2 / (4 * a) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    rcases le_total (κ - walk L r ω) 0 with h | h
    · rw [max_eq_right h]
      have : max (walk L r ω - EW - (κ - EW)) 0 = walk L r ω - κ := by
        rw [max_eq_left (by linarith)]
        ring
      linarith
    · rw [max_eq_left h]
      have : 0 ≤ (walk L r ω - EW) ^ 2 / (4 * a) := by positivity
      linarith
  have hmean_int : ∫ ω, max (κ - walk L r ω) 0 ∂P ≤ a + 2 + 3 * C
      + β * (Real.log r + Real.log 2) + V / (4 * a) := by
    have hi1 : Integrable (fun ω => κ - walk L r ω) P := (integrable_const κ).sub hWint
    have hi2 : Integrable (fun ω => (walk L r ω - EW) ^ 2 / (4 * a)) P := hWsq.div_const _
    have hint2 : Integrable (fun ω => (κ - walk L r ω) + (walk L r ω - EW) ^ 2 / (4 * a)) P :=
      hi1.add hi2
    calc ∫ ω, max (κ - walk L r ω) 0 ∂P
        ≤ ∫ ω, (κ - walk L r ω) + (walk L r ω - EW) ^ 2 / (4 * a) ∂P :=
          integral_mono hmaxint hint2 hpt
      _ = (κ - EW) + (∫ ω, (walk L r ω - EW) ^ 2 ∂P) / (4 * a) := by
          rw [integral_add hi1 hi2, integral_sub (integrable_const κ) hWint, integral_const,
            integral_div]
          simp only [probReal_univ, smul_eq_mul, one_mul]
          rfl
      _ ≤ a + 2 + 3 * C + β * (Real.log r + Real.log 2) + V / (4 * a) := by
          have hV : (∫ ω, (walk L r ω - EW) ^ 2 ∂P) / (4 * a) ≤ V / (4 * a) :=
            div_le_div_of_nonneg_right hWvar (by positivity)
          rw [hκdef]
          linarith [hEW.1]
  have hfinal : ∫ ω, F * (max (κ - walk L r ω) 0 + σ) ∂P
      ≤ F * (a + 2 + 3 * C + β * (Real.log r + Real.log 2) + V / (4 * a) + σ) := by
    rw [integral_const_mul, integral_add hmaxint (integrable_const σ), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) hF0
  calc (P {ω | ∀ j, r ≤ j → j ≤ n → walk L j ω ∈ Set.Icc (-a - c * j) (a + j + hf j)}).toReal
      ≤ ∫ ω, F * (max (κ - walk L r ω) 0 + σ) ∂P :=
        ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun ω => mul_nonneg hF0
          (add_nonneg (le_max_right _ _) hσ0)) hlint
    _ ≤ F * (a + 2 + 3 * C + β * (Real.log r + Real.log 2) + V / (4 * a) + σ) := hfinal
    _ = (1 + ε) * (K * ((a + 2 + 3 * C + β * (Real.log r + Real.log 2) + V / (4 * a)
          + σ) / (1 - 2 * β / T)) / √((n - r : ℕ) : ℝ)) := by
        rw [hFdef]
        field_simp

end Averaged

end RMF
