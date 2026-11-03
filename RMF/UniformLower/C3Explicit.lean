/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.UniformLower.C3Twist
import RMF.UniformLower.HP1Certificate
import RMF.UniformLower.WindowBlockData
import RMF.Probability.ProductIndependence
import Mathlib.Probability.Moments.SubGaussian

/-!
# (C3)*: the explicit inputs at `m = 1`

(C3)* is the lower bound
`c·E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`, in the
form of the skeleton `RMF.le_setIntegral_halfLadder_twistQ_ville_of_le`
(`RMF/UniformLower/C3Twist.lean`).  This file makes the skeleton's inputs at `m = 1` explicit: the
per-step bounds `hf` and the top step's lower bound `hc`.  The ladder is `[k₁, k)`, `K = k - k₁`,
`k₁ ≥ 20`; `P_tw` is `RMF.twistMeasure` over its primes; `u_p = p^{-½-σ}` (`RMF.twistU`),
`φ_p = h log p`.  The items:

1. **One prime.**  Under `P_tw` the value at `p` is a coin with log-odds
   `D = 2(ℓ_a(1) - ℓ_a(-1)) + (2q - 2)(ℓ₊ - ℓ₋)` (`RMF.integral_twistMeasure_eq_coinBias`), so
   `E_tw ℓ_p = u²(2q - ½ - 2(1 - cos φ)) ± 14u³`, `E_tw ℓ_p² = u² ± 57u⁴`, `Var = u² ± u³`, and by
   Hoeffding's lemma on the two atoms, for every `t ≥ 0`,
   `E_tw e^{-tℓ_p} ≤ exp(-tu²(2q - ½ - 2(1 - cos φ)) + t²u²/2 + (14t + t²/2)u³)`.
2. **One block.**  The primes stay independent:
   `E_tw e^{-tY} ≤ exp(-t((2q - ½)S - 2(S - C(h))) + t²S/2 + (14t + t²/2)∑u³)`, and the exact
   `E_tw Y`, `Var_tw Y` (`RMF.twistBlockMean`, `RMF.twistBlockVar`) are within `14∑u³`, `∑u³` of
   `(2q - ½)S - 2(S - C(h))` and `S`.  On block `m` at offset `θ`, `∑u³ ≤ e^{-e^{m+θ}/2}S`.
3. **The steps below the top** (`hf`).  The deficit `S - C(h)` is at most `S(ye^{-i})²/2`
   (pointwise, `y = he^k`) and `(1 - e^{-2})y²e^{-2i}/4 + 1/150000 + 7.43·10⁻⁸` (the two-regime
   cosine sum `RMF.blockCosErr`); `RMF.c3Step` takes the better, and `RMF.villeFactor` collects
   the steps, monotone in `K` (`RMF.villeFactor_le_of_le`).
4. **The top step** (`hc`).  `1{y > 0}(1 - Fe^{-ty}) ≥ S(y/δ) - F·S((y + δ)/δ)e^{-ty}`; each term
   is compared with `N(E_tw Y₀, Var_tw Y₀)` by Lindeberg over the top block's primes
   (`RMF.abs_integral_halfBlock_sub_gaussianReal_le`, error `M₃·105e^{-e^{20}/2}`), and against the
   Gaussian each is a normal distribution function (`RMF.le_setIntegral_ladderEvent_one`).
5. **Ranges.**  Over a cell `h ∈ [e^{-k-ϑ_hi}, e^{-k-ϑ_lo}]`, `E_tw Y₀ ∈ [topMuLo, topMuHi]` and
   `Var_tw Y₀ ∈ [topVLo, topVHi]` (`RMF.topBlock_moments_mem`, via `blockCos(-1-ϑ, 0)` and
   `RMF.cosExpAnti`).
6. **Assembly.**  `RMF.c3Val` is the Gaussian value at the cell's worst corner, and
   `RMF.le_setIntegral_halfLadder_twistQ_explicit` is (C3)* at `m = 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace RMF

/-! ### The two-atom tilted law -/

/-- **The bias of a tilted fair coin** with log-odds `D`: `κ(D) = (e^D - 1)/(e^D + 1)`
(`= tanh(D/2)`). -/
noncomputable def coinBias (D : ℝ) : ℝ := (Real.exp D - 1) / (Real.exp D + 1)

/-- `|κ(D) - D/2| ≤ |D|³` for `|D| ≤ 1`: the numerator of `κ(D) - D/2` is `2ρ - D³/2 - Dρ`,
`ρ = e^D - 1 - D - D²/2`, `|ρ| ≤ 2|D|³/9` (`Real.exp_bound`). -/
lemma abs_coinBias_sub_le {D : ℝ} (hD : |D| ≤ 1) : |coinBias D - D / 2| ≤ |D| ^ 3 := by
  have hb := Real.exp_bound hD (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  set ρ := Real.exp D - (1 + D + D ^ 2 / 2) with hρ
  have hρb : |ρ| ≤ |D| ^ 3 * (2 / 9) := by
    rw [hρ]
    convert hb using 2
  have hE : 0 < Real.exp D := Real.exp_pos D
  have hkey : coinBias D - D / 2 = (2 * ρ - D ^ 3 / 2 - D * ρ) / (2 * (Real.exp D + 1)) := by
    rw [coinBias, hρ]
    field_simp
    ring
  have hD3 : 0 ≤ |D| ^ 3 := by positivity
  have hDρ : |D * ρ| ≤ |D| ^ 3 * (2 / 9) := by
    rw [abs_mul]
    calc |D| * |ρ| ≤ 1 * (|D| ^ 3 * (2 / 9)) :=
          mul_le_mul hD hρb (abs_nonneg _) zero_le_one
      _ = |D| ^ 3 * (2 / 9) := one_mul _
  have hnum : |2 * ρ - D ^ 3 / 2 - D * ρ| ≤ 2 * |D| ^ 3 := by
    have h1 : |2 * ρ - D ^ 3 / 2 - D * ρ| ≤ 2 * |ρ| + |D| ^ 3 / 2 + |D * ρ| := by
      have := abs_sub (2 * ρ - D ^ 3 / 2) (D * ρ)
      have h2 := abs_sub (2 * ρ) (D ^ 3 / 2)
      rw [abs_mul, abs_two, abs_div, abs_pow, abs_two] at h2
      linarith
    linarith
  rw [hkey, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * (Real.exp D + 1)),
    div_le_iff₀ (by linarith)]
  nlinarith

/-- **The tilted Rademacher law as a biased coin**: for any tilt `T` and any `g`,
`∫ g d(rademacherLaw.tilted T) = (g 1 + g (-1))/2 + (g 1 - g (-1))/2·κ(T 1 - T (-1))`. -/
theorem integral_tilted_rademacherLaw_coinBias (T g : ℂ → ℝ) :
    ∫ z, g z ∂(rademacherLaw.tilted T)
      = (g 1 + g (-1)) / 2 + (g 1 - g (-1)) / 2 * coinBias (T 1 - T (-1)) := by
  rw [integral_tilted, integral_rademacherLaw_eq, integral_rademacherLaw_eq]
  simp only [smul_eq_mul]
  have ha := Real.exp_pos (T 1)
  have hb := Real.exp_pos (T (-1))
  rw [coinBias, Real.exp_sub]
  field_simp
  ring

/-! ### One prime under the twisted tilt, in real variables

With `ℓ_± = log(1 ± u)` the two values of `log‖1 + X_p p^{-σ'}‖`, `Δ = log‖1 + a‖ - log‖1 - a‖`
for `a = p^{-(σ'+ih)}` (`Re a = uc`, `c = cos(h log p)`), and `r = 2q - 2`: the log-odds of the
twisted law are `D = 2Δ + r(ℓ₊ - ℓ₋)`, so the mean is `(ℓ₊ + ℓ₋)/2 + (ℓ₊ - ℓ₋)/2·κ(D)`.  The
inputs are the expansions `(ℓ₊ + ℓ₋)/2 = -u²/2 + O(u³)`, `ℓ₊ - ℓ₋ = 2u + O(u³)`,
`Δ = 2uc + O(u³)` (`RMF/EulerProduct/RademacherLogField.lean`). -/

/-- The common core of the one-prime expansions: `κ(D)` is within `777u³` of `2uc + ru`, and
`(ℓ₊ - ℓ₋)/2` within `12u³` of `u`. -/
lemma twoAtom_core {u c r Lp Lm Δa : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 1000) (hc : |c| ≤ 1)
    (hr : |r| ≤ 2) (hH : |(Lp - Lm) - 2 * u| ≤ 24 * u ^ 3)
    (hΔ : |Δa - 2 * (u * c)| ≤ 24 * u ^ 3) :
    |coinBias (2 * Δa + r * (Lp - Lm)) - (2 * (u * c) + r * u)| ≤ 777 * u ^ 3
      ∧ |(Lp - Lm) / 2 - u| ≤ 12 * u ^ 3 ∧ |2 * (u * c) + r * u| ≤ 4 * u := by
  have hu2 : u ^ 2 ≤ 1 / 1000000 := by nlinarith
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hHu : |(Lp - Lm) / 2 - u| ≤ 12 * u ^ 3 := by
    rw [show (Lp - Lm) / 2 - u = ((Lp - Lm) - 2 * u) / 2 by ring, abs_div, abs_two]
    linarith
  have hX : |2 * (u * c) + r * u| ≤ 4 * u := by
    have h1 : |2 * (u * c)| ≤ 2 * u := by
      rw [abs_mul, abs_two, abs_mul, abs_of_nonneg hu0]
      nlinarith [abs_nonneg c]
    have h2 : |r * u| ≤ 2 * u := by
      rw [abs_mul, abs_of_nonneg hu0]
      nlinarith [abs_nonneg r]
    calc |2 * (u * c) + r * u| ≤ |2 * (u * c)| + |r * u| := abs_add_le _ _
      _ ≤ 4 * u := by linarith
  have hDX : |(2 * Δa + r * (Lp - Lm)) / 2 - (2 * (u * c) + r * u)| ≤ 48 * u ^ 3 := by
    have hrH : |r * ((Lp - Lm) - 2 * u)| ≤ 2 * (24 * u ^ 3) := by
      rw [abs_mul]
      exact mul_le_mul hr hH (abs_nonneg _) (by norm_num)
    rw [show (2 * Δa + r * (Lp - Lm)) / 2 - (2 * (u * c) + r * u)
        = (Δa - 2 * (u * c)) + r * ((Lp - Lm) - 2 * u) / 2 by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_two]
    linarith
  have hD : |2 * Δa + r * (Lp - Lm)| ≤ 9 * u := by
    have h := abs_le.1 hDX
    have h' := abs_le.1 hX
    rw [abs_le]
    constructor <;> nlinarith
  have hD1 : |2 * Δa + r * (Lp - Lm)| ≤ 1 := by linarith
  have hκ := abs_coinBias_sub_le hD1
  have hD3 : |2 * Δa + r * (Lp - Lm)| ^ 3 ≤ (9 * u) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hD 3
  refine ⟨?_, hHu, hX⟩
  calc |coinBias (2 * Δa + r * (Lp - Lm)) - (2 * (u * c) + r * u)|
      ≤ |coinBias (2 * Δa + r * (Lp - Lm)) - (2 * Δa + r * (Lp - Lm)) / 2|
        + |(2 * Δa + r * (Lp - Lm)) / 2 - (2 * (u * c) + r * u)| := abs_sub_le _ _ _
    _ ≤ (9 * u) ^ 3 + 48 * u ^ 3 := add_le_add (hκ.trans hD3) hDX
    _ = 777 * u ^ 3 := by ring

/-- **The twisted mean of one prime, in real variables**:
`|(ℓ₊ + ℓ₋)/2 + (ℓ₊ - ℓ₋)/2·κ(D) - u²(2c + r - ½)| ≤ 14u³`. -/
lemma abs_twoAtom_mean_sub_le {u c r Lp Lm Δa : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 1000)
    (hc : |c| ≤ 1) (hr : |r| ≤ 2) (hA : |(Lp + Lm) / 2 + u ^ 2 / 2| ≤ 12 * u ^ 3)
    (hH : |(Lp - Lm) - 2 * u| ≤ 24 * u ^ 3) (hΔ : |Δa - 2 * (u * c)| ≤ 24 * u ^ 3) :
    |(Lp + Lm) / 2 + (Lp - Lm) / 2 * coinBias (2 * Δa + r * (Lp - Lm))
        - u ^ 2 * (2 * c + r - 1 / 2)| ≤ 14 * u ^ 3 := by
  obtain ⟨hκX, hHu, hX⟩ := twoAtom_core hu0 hu hc hr hH hΔ
  set κ := coinBias (2 * Δa + r * (Lp - Lm))
  set X := 2 * (u * c) + r * u
  set H := (Lp - Lm) / 2
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hu4 : u * u ^ 3 ≤ u ^ 3 / 1000 := by nlinarith
  have hH2 : |H| ≤ 2 * u := by
    have := abs_le.1 hHu
    rw [abs_le]
    constructor <;> nlinarith
  have hid : (Lp + Lm) / 2 + H * κ - u ^ 2 * (2 * c + r - 1 / 2)
      = ((Lp + Lm) / 2 + u ^ 2 / 2) + H * (κ - X) + (H - u) * X := by
    simp only [H, X]
    ring
  have h1 : |H * (κ - X)| ≤ 2 * u * (777 * u ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul hH2 hκX (abs_nonneg _) (by positivity)
  have h2 : |(H - u) * X| ≤ 12 * u ^ 3 * (4 * u) := by
    rw [abs_mul]
    exact mul_le_mul hHu hX (abs_nonneg _) (by positivity)
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  nlinarith

/-- **The twisted second moment of one prime, in real variables**:
`|(ℓ₊² + ℓ₋²)/2 + (ℓ₊² - ℓ₋²)/2·κ(D) - u²| ≤ 57u⁴`. -/
lemma abs_twoAtom_sq_sub_le {u c r Lp Lm Δa : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 1000)
    (hc : |c| ≤ 1) (hr : |r| ≤ 2) (hA : |(Lp + Lm) / 2 + u ^ 2 / 2| ≤ 12 * u ^ 3)
    (hH : |(Lp - Lm) - 2 * u| ≤ 24 * u ^ 3) (hΔ : |Δa - 2 * (u * c)| ≤ 24 * u ^ 3) :
    |(Lp * Lp + Lm * Lm) / 2 + (Lp * Lp - Lm * Lm) / 2 * coinBias (2 * Δa + r * (Lp - Lm))
        - u ^ 2| ≤ 57 * u ^ 4 := by
  obtain ⟨hκX, hHu, hX⟩ := twoAtom_core hu0 hu hc hr hH hΔ
  set κ := coinBias (2 * Δa + r * (Lp - Lm))
  set H := (Lp - Lm) / 2
  set A := (Lp + Lm) / 2
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hu2 : u ^ 2 ≤ 1 / 1000000 := by nlinarith
  have hA1 : |A| ≤ u ^ 2 := by
    have := abs_le.1 hA
    rw [abs_le]
    constructor <;> nlinarith
  have hHp : |H + u| ≤ 3 * u := by
    have := abs_le.1 hHu
    rw [abs_le]
    constructor <;> nlinarith
  have hH2 : |H| ≤ 2 * u := by
    have := abs_le.1 hHu
    rw [abs_le]
    constructor <;> nlinarith
  have hκ5 : |κ| ≤ 5 * u := by
    have := abs_le.1 hκX
    have := abs_le.1 hX
    rw [abs_le]
    constructor <;> nlinarith
  have hid : (Lp * Lp + Lm * Lm) / 2 + (Lp * Lp - Lm * Lm) / 2 * κ - u ^ 2
      = A * A + (H - u) * (H + u) + 2 * (A * H * κ) := by
    simp only [A, H]
    ring
  have h1 : |A * A| ≤ u ^ 2 * u ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul hA1 hA1 (abs_nonneg _) (by positivity)
  have h2 : |(H - u) * (H + u)| ≤ 12 * u ^ 3 * (3 * u) := by
    rw [abs_mul]
    exact mul_le_mul hHu hHp (abs_nonneg _) (by positivity)
  have h3 : |2 * (A * H * κ)| ≤ 2 * (u ^ 2 * (2 * u) * (5 * u)) := by
    rw [abs_mul, abs_two, abs_mul, abs_mul]
    gcongr
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  nlinarith

/-! ### One prime under the twisted tilt -/

/-- The size of one prime's local variable on the line `½ + σ`: `u_p = p^{-½-σ}`. -/
noncomputable def twistU (σ : ℝ) (p : Nat.Primes) : ℝ := ((p : ℕ) : ℝ) ^ (-(1 / 2 + σ))

lemma twistU_nonneg (σ : ℝ) (p : Nat.Primes) : 0 ≤ twistU σ p :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma norm_cpow_eq_twistU (σ h : ℝ) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-shiftLine σ h)‖ = twistU σ p :=
  norm_cpow_neg_shiftLine p.2.pos σ h

lemma twistU_sq (σ : ℝ) (p : Nat.Primes) :
    twistU σ p ^ 2 = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := by
  rw [← norm_cpow_eq_twistU σ 0 p]
  exact norm_sq_prime_cpow_neg p (re_shiftLine σ 0)

/-- On a ladder block past offset `20` every `u_p` is below `10⁻⁴⁰`. -/
lemma twistU_le_of_mem_primeBlockSub {θ σ : ℝ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 20 ≤ (m : ℝ) + θ)
    {p : Nat.Primes} (hp : p ∈ primeBlockSub θ m) : twistU σ p ≤ 1 / 10 ^ 40 := by
  rw [← norm_cpow_eq_twistU σ 0 p]
  exact norm_cpow_le_of_mem_primeBlockSub hσ hm (re_shiftLine σ 0) hp

/-- The three one-prime expansions the twisted moments consume, with `w = p^{-σ'}`,
`a = p^{-(σ'+ih)}`, `u = u_p`, `c = cos(h log p)`: `(ℓ₊ + ℓ₋)/2 = -u²/2 + O(u³)`,
`ℓ₊ - ℓ₋ = 2u + O(u³)`, `Δ_a = 2uc + O(u³)`. -/
lemma twistPrime_inputs (σ h : ℝ) (p : Nat.Primes) (hu : twistU σ p ≤ 1 / 5) :
    |(localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1
          + localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1)) / 2 + twistU σ p ^ 2 / 2|
        ≤ 12 * twistU σ p ^ 3
      ∧ |(localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1
          - localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1)) - 2 * twistU σ p|
        ≤ 24 * twistU σ p ^ 3
      ∧ |(localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ h)) 1
          - localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ h)) (-1))
          - 2 * (twistU σ p * Real.cos (h * Real.log ((p : ℕ) : ℝ)))| ≤ 24 * twistU σ p ^ 3 := by
  have hw := norm_cpow_eq_twistU σ 0 p
  have ha := norm_cpow_eq_twistU σ h p
  have hre0 : (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)).re = twistU σ p := by
    rw [re_cpow_neg_shiftLine p.2.pos σ 0, zero_mul, Real.cos_zero, mul_one]
    rfl
  have hreh : (((p : ℕ) : ℂ) ^ (-shiftLine σ h)).re
      = twistU σ p * Real.cos (h * Real.log ((p : ℕ) : ℝ)) :=
    re_cpow_neg_shiftLine p.2.pos σ h
  refine ⟨?_, ?_, ?_⟩
  · have h1 := abs_integral_localLogAdd_sub_le (w := ((p : ℕ) : ℂ) ^ (-shiftLine σ 0))
      (by rw [hw]; exact hu)
    rw [integral_rademacherLaw_eq, smul_eq_mul, hw, hre0] at h1
    rw [show (localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1
          + localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1)) / 2 + twistU σ p ^ 2 / 2
        = 2⁻¹ * (localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1
          + localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1))
          - (twistU σ p ^ 2 / 2 - twistU σ p ^ 2) by ring]
    exact h1
  · have h1 := abs_localLogAdd_diff_sub_le (w := ((p : ℕ) : ℂ) ^ (-shiftLine σ 0))
      (by rw [hw]; exact hu)
    rwa [hw, hre0] at h1
  · have h1 := abs_localLogAdd_diff_sub_le (w := ((p : ℕ) : ℂ) ^ (-shiftLine σ h))
      (by rw [ha]; exact hu)
    rwa [ha, hreh] at h1

/-- The log-odds of the twisted law at `p`:
`T(1) - T(-1) = 2Δ_a + (2q - 2)(ℓ₊ - ℓ₋)`. -/
lemma twistLocal_one_sub_neg_one (σ h q : ℝ) (p : Nat.Primes) :
    twistLocal σ h q p 1 - twistLocal σ h q p (-1)
      = 2 * (localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ h)) 1
          - localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ h)) (-1))
        + (2 * q - 2) * (localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1
          - localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1)) := by
  simp only [twistLocal]
  ring

section OnePrime

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- Under the twisted tilt the values at the primes are `±1` almost surely. -/
lemma ae_eq_one_or_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ) (σ h q : ℝ)
    (p : Nat.Primes) :
    ∀ᵐ ω ∂(twistMeasure X μ a b σ h q), X (p : ℕ) ω = 1 ∨ X (p : ℕ) ω = -1 := by
  have hae : ∀ᵐ ω ∂μ, X (p : ℕ) ω ^ 2 = 1 := by
    refine ((hX.hasLaw (p : ℕ) p.2).ae_iff ?_).2 sq_eq_one_rademacherLaw
    exact measurableSet_setOf.1 (measurableSet_eq_fun (measurable_id.pow_const 2)
      measurable_const)
  filter_upwards [(twistMeasure_absolutelyContinuous a b σ h q).ae_le hae] with ω hω
  exact sq_eq_one_iff.1 hω

/-- **One prime's law under the twisted tilt, as a biased coin**: for `p` in the ladder range and
measurable `g`, `E_tw g(X_p) = (g 1 + g (-1))/2 + (g 1 - g (-1))/2·κ(T_p(1) - T_p(-1))`. -/
theorem integral_twistMeasure_eq_coinBias (hX : IsRademacherPrimeValues X μ) {a b : ℕ}
    {σ : ℝ} (hσ : 0 ≤ σ) (h q : ℝ) {p : Nat.Primes} (hp : p ∈ primesIcoSub a b) {g : ℂ → ℝ}
    (hg : Measurable g) :
    ∫ ω, g (X (p : ℕ) ω) ∂(twistMeasure X μ a b σ h q)
      = (g 1 + g (-1)) / 2
        + (g 1 - g (-1)) / 2 * coinBias (twistLocal σ h q p 1 - twistLocal σ h q p (-1)) := by
  rw [← integral_map (f := g) (hX.measurable (p : ℕ) p.2).aemeasurable hg.aestronglyMeasurable,
    map_twistMeasure_of_mem hX a b hσ h q hp, integral_tilted_rademacherLaw_coinBias]

/-- `|ℓ_p| ≤ 2u_p` at both atoms, for `u_p ≤ ½`. -/
lemma abs_localLogAdd_le_two_twistU (σ : ℝ) (p : Nat.Primes) (hu : twistU σ p ≤ 1 / 2)
    {z : ℂ} (hz : ‖z‖ = 1) :
    |localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) z| ≤ 2 * twistU σ p := by
  have hu0 := twistU_nonneg σ p
  have h1 := abs_localLogAdd_le hz (norm_cpow_eq_twistU σ 0 p).le (by linarith)
  have h2 : Real.log ((1 - twistU σ p)⁻¹) ≤ (1 - twistU σ p)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 (by linarith))
  have h3 : (1 - twistU σ p)⁻¹ - 1 ≤ 2 * twistU σ p := by
    rw [inv_eq_one_div, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The local variable `ℓ_p(ω) = log‖1 + X_p(ω)p^{-σ'}‖` lies between its two atoms,
`P_tw`-almost surely. -/
lemma ae_mem_Icc_localLogAdd_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) (h q : ℝ) (p : Nat.Primes) :
    ∀ᵐ ω ∂(twistMeasure X μ a b σ h q),
      localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
        ∈ Set.Icc (localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1))
          (localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1) := by
  have hle : localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (-1)
      ≤ localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) 1 := by
    have hu0 := twistU_nonneg σ p
    have hu1 : twistU σ p < 1 := by
      rw [← norm_cpow_eq_twistU σ 0 p]
      exact norm_prime_cpow_neg_lt_one p.2 (by rw [re_shiftLine]; linarith)
    have hw : ((p : ℕ) : ℂ) ^ (-shiftLine σ 0) = ((twistU σ p : ℝ) : ℂ) :=
      cpow_neg_shiftLine_zero (p : ℕ) σ
    rw [localLogAdd, localLogAdd, hw,
      show (1 : ℂ) + (-1) * ((twistU σ p : ℝ) : ℂ) = ((1 - twistU σ p : ℝ) : ℂ) by
        push_cast; ring,
      show (1 : ℂ) + 1 * ((twistU σ p : ℝ) : ℂ) = ((1 + twistU σ p : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  filter_upwards [ae_eq_one_or_twistMeasure hX a b σ h q p] with ω hω
  rcases hω with h1 | h1
  · rw [h1]
    exact ⟨hle, le_rfl⟩
  · rw [h1]
    exact ⟨le_rfl, hle⟩

/-- **The twisted mean of one prime**: `|E_tw ℓ_p - u²(2cos(h log p) + 2q - 2 - ½)| ≤ 14u³` for
`p` in the ladder range, `u = u_p ≤ 1/1000` and `0 ≤ q ≤ 1`. -/
theorem abs_integral_localLogAdd_twistMeasure_sub_le (hX : IsRademacherPrimeValues X μ)
    {a b : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {p : Nat.Primes} (hp : p ∈ primesIcoSub a b) (hu : twistU σ p ≤ 1 / 1000) :
    |∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          ∂(twistMeasure X μ a b σ h q)
        - twistU σ p ^ 2 * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2)|
      ≤ 14 * twistU σ p ^ 3 := by
  obtain ⟨hA, hH, hΔ⟩ := twistPrime_inputs σ h p (by linarith)
  rw [integral_twistMeasure_eq_coinBias hX hσ h q hp (measurable_localLogAdd _),
    twistLocal_one_sub_neg_one]
  exact abs_twoAtom_mean_sub_le (twistU_nonneg σ p) hu (Real.abs_cos_le_one _)
    (by rw [abs_le]; constructor <;> linarith) hA hH hΔ

/-- **The twisted second moment of one prime**: `|E_tw ℓ_p² - u²| ≤ 57u⁴`. -/
theorem abs_integral_mul_self_localLogAdd_twistMeasure_sub_le
    (hX : IsRademacherPrimeValues X μ) {a b : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {p : Nat.Primes} (hp : p ∈ primesIcoSub a b)
    (hu : twistU σ p ≤ 1 / 1000) :
    |∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          ∂(twistMeasure X μ a b σ h q) - twistU σ p ^ 2|
      ≤ 57 * twistU σ p ^ 4 := by
  obtain ⟨hA, hH, hΔ⟩ := twistPrime_inputs σ h p (by linarith)
  have hg : Measurable fun z => localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) z
      * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) z :=
    (measurable_localLogAdd _).mul (measurable_localLogAdd _)
  rw [integral_twistMeasure_eq_coinBias hX hσ h q hp hg, twistLocal_one_sub_neg_one]
  exact abs_twoAtom_sq_sub_le (twistU_nonneg σ p) hu (Real.abs_cos_le_one _)
    (by rw [abs_le]; constructor <;> linarith) hA hH hΔ

/-- **The twisted variance of one prime**: `|E_tw ℓ_p² - (E_tw ℓ_p)² - u²| ≤ u³`. -/
theorem abs_variance_localLogAdd_twistMeasure_sub_le (hX : IsRademacherPrimeValues X μ)
    {a b : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {p : Nat.Primes} (hp : p ∈ primesIcoSub a b) (hu : twistU σ p ≤ 1 / 1000) :
    |(∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          ∂(twistMeasure X μ a b σ h q))
        - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          ∂(twistMeasure X μ a b σ h q)) ^ 2 - twistU σ p ^ 2|
      ≤ twistU σ p ^ 3 := by
  have h2 := abs_integral_mul_self_localLogAdd_twistMeasure_sub_le hX hσ h hq0 hq1 hp hu
  have h1 := abs_integral_localLogAdd_twistMeasure_sub_le hX hσ h hq0 hq1 hp hu
  set u := twistU σ p
  set M := ∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
    ∂(twistMeasure X μ a b σ h q)
  have hu0 : 0 ≤ u := twistU_nonneg σ p
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hc := Real.abs_cos_le_one (h * Real.log ((p : ℕ) : ℝ))
  have hmain : |u ^ 2 * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2)|
      ≤ u ^ 2 * (9 / 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_le] at hc ⊢
    constructor <;> linarith [hc.1, hc.2]
  have hM : |M| ≤ 5 * u ^ 2 := by
    have := abs_sub_abs_le_abs_sub M
      (u ^ 2 * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2))
    nlinarith
  have hM2 : M ^ 2 ≤ 25 * u ^ 4 := by
    have := sq_le_sq' (abs_le.1 hM).1 (abs_le.1 hM).2
    nlinarith
  have hu4 : u * u ^ 3 ≤ u ^ 3 / 1000 := by nlinarith
  rw [show (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          ∂(twistMeasure X μ a b σ h q)) - M ^ 2 - u ^ 2
      = ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
          ∂(twistMeasure X μ a b σ h q)) - u ^ 2) - M ^ 2 by ring]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (sq_nonneg M)]
  nlinarith

/-- **Item 1: one prime's exponential moment under the twisted tilt** (Hoeffding's lemma on the
two atoms, `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`): for `t ≥ 0`,
`E_tw e^{-tℓ_p} ≤ exp(-t·u²(2q - ½ - 2(1 - cos(h log p))) + t²u²/2 + (14t + t²/2)u³)`. -/
theorem integral_exp_neg_mul_localLogAdd_twistMeasure_le (hX : IsRademacherPrimeValues X μ)
    {a b : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {p : Nat.Primes} (hp : p ∈ primesIcoSub a b) (hu : twistU σ p ≤ 1 / 1000) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ ω, Real.exp (-(t * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)))
        ∂(twistMeasure X μ a b σ h q)
      ≤ Real.exp (-(t * (twistU σ p ^ 2
            * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2)))
          + t ^ 2 * twistU σ p ^ 2 / 2 + (14 * t + t ^ 2 / 2) * twistU σ p ^ 3) := by
  haveI := isProbabilityMeasure_twistMeasure hX a b hσ h q
  set P := twistMeasure X μ a b σ h q
  set w : ℂ := ((p : ℕ) : ℂ) ^ (-shiftLine σ 0)
  set ξ : Ω → ℝ := fun ω => localLogAdd w (X (p : ℕ) ω) with hξ
  set u := twistU σ p
  have hξm : Measurable ξ := (measurable_localLogAdd w).comp (hX.measurable (p : ℕ) p.2)
  have hsub := hasSubgaussianMGF_of_mem_Icc hξm.aemeasurable
    (ae_mem_Icc_localLogAdd_twistMeasure hX a b hσ h q p)
  have hmgf := hsub.mgf_le (-t)
  set M := ∫ ω, ξ ω ∂P
  have hsplit : ∫ ω, Real.exp (-(t * ξ ω)) ∂P
      = Real.exp (-(t * M)) * mgf (fun ω => ξ ω - M) P (-t) := by
    rw [mgf, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  have hM := abs_integral_localLogAdd_twistMeasure_sub_le hX hσ h hq0 hq1 hp hu
  obtain ⟨-, hH, -⟩ := twistPrime_inputs σ h p (by linarith)
  have hu0 : 0 ≤ u := twistU_nonneg σ p
  have hu3 : 0 ≤ u ^ 3 := by positivity
  -- the Hoeffding parameter is at most `u² + u³`
  have hc : ((‖localLogAdd w 1 - localLogAdd w (-1)‖₊ / 2) ^ 2 : ℝ≥0) ≤ (u ^ 2 + u ^ 3 : ℝ) := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    have hHu : |(localLogAdd w 1 - localLogAdd w (-1)) / 2 - u| ≤ 12 * u ^ 3 := by
      rw [show (localLogAdd w 1 - localLogAdd w (-1)) / 2 - u
          = ((localLogAdd w 1 - localLogAdd w (-1)) - 2 * u) / 2 by ring, abs_div, abs_two]
      linarith
    have h1 := abs_le.1 hHu
    have hu4 : u * u ^ 3 ≤ u ^ 3 / 1000 := by nlinarith
    nlinarith
  have hM' : -(t * M) ≤ -(t * (u ^ 2 * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ))
      + (2 * q - 2) - 1 / 2))) + t * (14 * u ^ 3) := by
    have := (abs_le.1 hM).1
    nlinarith
  rw [hsplit]
  calc Real.exp (-(t * M)) * mgf (fun ω => ξ ω - M) P (-t)
      ≤ Real.exp (-(t * M)) * Real.exp ((u ^ 2 + u ^ 3) * (-t) ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (hmgf.trans ?_) (Real.exp_pos _).le
        exact Real.exp_le_exp.2 (by
          have := mul_le_mul_of_nonneg_right hc (sq_nonneg (-t))
          linarith)
    _ = Real.exp (-(t * M) + (u ^ 2 + u ^ 3) * (-t) ^ 2 / 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end OnePrime

/-! ### One block under the twisted tilt -/

/-- The main terms of one block, summed: `∑ u²(2c + 2q - 2 - ½) = (2q - ½)S - 2(S - C(h))`. -/
lemma sum_twistMain_eq (θ σ h q : ℝ) (m : ℕ) :
    ∑ p ∈ primeBlockSub θ m,
        twistU σ p ^ 2 * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2)
      = (2 * q - 1 / 2) * blockRpowSum θ σ m
        - 2 * (blockRpowSum θ σ m - blockCosSum θ σ h m) := by
  have h1 : ∀ p ∈ primeBlockSub θ m,
      twistU σ p ^ 2 * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2)
        = (2 * q - 5 / 2) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
          + 2 * (Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)) := by
    intro p _
    rw [twistU_sq]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    blockRpowSum, blockCosSum]
  ring

/-- `∑ u² = S`. -/
lemma sum_twistU_sq (θ σ : ℝ) (m : ℕ) :
    ∑ p ∈ primeBlockSub θ m, twistU σ p ^ 2 = blockRpowSum θ σ m := by
  rw [blockRpowSum]
  exact Finset.sum_congr rfl fun p _ => twistU_sq σ p

/-- The primes of the ladder's blocks lie in the ladder's range. -/
lemma primeBlockSub_subset_primesIcoSub_scaleCut {k₁ k m : ℕ} (hm : m < k - k₁) :
    primeBlockSub (k₁ : ℝ) m ⊆ primesIcoSub (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) := by
  intro p hp
  have h := mem_primesIco_of_mem_primeBlockSub_range (n := k - k₁) hm hp
  have hcast : (k₁ : ℝ) + ((k - k₁ : ℕ) : ℝ) = (k : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    ring
  rw [hcast] at h
  rw [mem_primesIcoSub]
  exact ⟨(mem_primesIco.1 h).2.1, (mem_primesIco.1 h).2.2⟩

section OneBlock

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **The exact twisted mean of a block**: `∑_p E_tw ℓ_p`. -/
noncomputable def twistBlockMean (X : ℕ → Ω → ℂ) (μ : Measure Ω) (a b : ℕ) (σ h q θ : ℝ)
    (m : ℕ) : ℝ :=
  ∑ p ∈ primeBlockSub θ m, ∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
    ∂(twistMeasure X μ a b σ h q)

/-- **The exact twisted variance of a block**: `∑_p (E_tw ℓ_p² - (E_tw ℓ_p)²)`. -/
noncomputable def twistBlockVar (X : ℕ → Ω → ℂ) (μ : Measure Ω) (a b : ℕ) (σ h q θ : ℝ)
    (m : ℕ) : ℝ :=
  ∑ p ∈ primeBlockSub θ m,
    ((∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
        * localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
        ∂(twistMeasure X μ a b σ h q))
      - (∫ ω, localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)
        ∂(twistMeasure X μ a b σ h q)) ^ 2)

/-- The local variables `ℓ_p` stay independent under the twisted tilt. -/
lemma iIndepFun_localLogAdd_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (h q : ℝ) :
    iIndepFun (fun (p : Nat.Primes) ω => localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0))
      (X (p : ℕ) ω)) (twistMeasure X μ a b σ h q) :=
  (iIndepFun_twistMeasure hX a b hσ h q).comp
    (fun (p : Nat.Primes) (z : ℂ) => localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) z)
    fun _ => measurable_localLogAdd _

/-- `|ℓ_p| ≤ 2u_p`, `P_tw`-almost surely, for `u_p ≤ ½`. -/
lemma ae_abs_localLogAdd_le_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ)
    (σ h q : ℝ) (p : Nat.Primes) (hu : twistU σ p ≤ 1 / 2) :
    ∀ᵐ ω ∂(twistMeasure X μ a b σ h q),
      |localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)| ≤ 2 * twistU σ p := by
  filter_upwards [ae_eq_one_or_twistMeasure hX a b σ h q p] with ω hω
  rcases hω with h1 | h1 <;> rw [h1] <;>
    exact abs_localLogAdd_le_two_twistU σ p hu (by simp)

/-- **Item 2, the mean**: `|E_tw Y - ((2q - ½)S - 2(S - C(h)))| ≤ 14∑u³` for a block past offset
`20` inside the tilt's range, `0 ≤ q ≤ 1`. -/
theorem abs_twistBlockMean_sub_le (hX : IsRademacherPrimeValues X μ) {a b : ℕ} {θ σ : ℝ}
    (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {m : ℕ} (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesIcoSub a b) :
    |twistBlockMean X μ a b σ h q θ m
        - ((2 * q - 1 / 2) * blockRpowSum θ σ m - 2 * (blockRpowSum θ σ m - blockCosSum θ σ h m))|
      ≤ 14 * ∑ p ∈ primeBlockSub θ m, twistU σ p ^ 3 := by
  rw [← sum_twistMain_eq, twistBlockMean, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_integral_localLogAdd_twistMeasure_sub_le hX hσ h hq0 hq1 (hB hp)
    ((twistU_le_of_mem_primeBlockSub hσ hm hp).trans (by norm_num))

/-- **Item 2, the variance**: `|Var_tw Y - S| ≤ ∑u³`. -/
theorem abs_twistBlockVar_sub_le (hX : IsRademacherPrimeValues X μ) {a b : ℕ} {θ σ : ℝ}
    (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {m : ℕ} (hm : 20 ≤ (m : ℝ) + θ)
    (hB : primeBlockSub θ m ⊆ primesIcoSub a b) :
    |twistBlockVar X μ a b σ h q θ m - blockRpowSum θ σ m|
      ≤ ∑ p ∈ primeBlockSub θ m, twistU σ p ^ 3 := by
  rw [← sum_twistU_sq, twistBlockVar, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  exact abs_variance_localLogAdd_twistMeasure_sub_le hX hσ h hq0 hq1 (hB hp)
    ((twistU_le_of_mem_primeBlockSub hσ hm hp).trans (by norm_num))

/-- **Item 2: one block's exponential moment under the twisted tilt**: for a block past offset
`20` inside the tilt's range and `t ≥ 0`,
`E_tw e^{-tY} ≤ exp(-t((2q - ½)S - 2(S - C(h))) + t²S/2 + (14t + t²/2)∑u³)`,
`S = RMF.blockRpowSum`, `C(h) = RMF.blockCosSum` at `h`. -/
theorem integral_exp_neg_mul_halfBlock_twistMeasure_le (hX : IsRademacherPrimeValues X μ)
    {a b : ℕ} {θ σ : ℝ} (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {m : ℕ}
    (hm : 20 ≤ (m : ℝ) + θ) (hB : primeBlockSub θ m ⊆ primesIcoSub a b) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Real.exp (-(t * halfBlock X θ σ 0 m ω)) ∂(twistMeasure X μ a b σ h q)
      ≤ Real.exp (-(t * ((2 * q - 1 / 2) * blockRpowSum θ σ m
            - 2 * (blockRpowSum θ σ m - blockCosSum θ σ h m)))
          + t ^ 2 * blockRpowSum θ σ m / 2
          + (14 * t + t ^ 2 / 2) * ∑ p ∈ primeBlockSub θ m, twistU σ p ^ 3) := by
  haveI := isProbabilityMeasure_twistMeasure hX a b hσ h q
  set P := twistMeasure X μ a b σ h q
  set ξ : Nat.Primes → Ω → ℝ := fun p ω =>
    localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω) with hξ
  have hξm : ∀ p, Measurable (ξ p) := fun p =>
    (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)
  have hind : iIndepFun ξ P := iIndepFun_localLogAdd_twistMeasure hX a b hσ h q
  have hmgf := hind.mgf_sum hξm (primeBlockSub θ m) (t := -t)
  have hL : ∫ ω, Real.exp (-(t * halfBlock X θ σ 0 m ω)) ∂P
      = mgf (∑ p ∈ primeBlockSub θ m, ξ p) P (-t) := by
    rw [mgf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Finset.sum_apply, halfBlock, hξ, neg_mul]
  have hper : ∀ p ∈ primeBlockSub θ m, mgf (ξ p) P (-t)
      ≤ Real.exp (-(t * (twistU σ p ^ 2
            * (2 * Real.cos (h * Real.log ((p : ℕ) : ℝ)) + (2 * q - 2) - 1 / 2)))
          + t ^ 2 * twistU σ p ^ 2 / 2 + (14 * t + t ^ 2 / 2) * twistU σ p ^ 3) := by
    intro p hp
    have := integral_exp_neg_mul_localLogAdd_twistMeasure_le hX hσ h hq0 hq1 (hB hp)
      ((twistU_le_of_mem_primeBlockSub hσ hm hp).trans (by norm_num)) ht
    simp only [mgf, hξ, neg_mul]
    exact this
  rw [hL, hmgf]
  refine (Finset.prod_le_prod (fun p _ => mgf_nonneg) hper).trans (le_of_eq ?_)
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, sum_twistMain_eq,
    sum_twistU_sq]

end OneBlock

/-! ### The block data: drift deficits, Mertens sums, cubic remainders -/

/-- On block `m` at offset `θ` the phase is at most `he^{m+1+θ}`:
`1 - cos(h log p) ≤ (he^{m+1+θ})²/2` for `h ≥ 0`. -/
lemma one_sub_cos_le_of_mem_primeBlockSub {θ h : ℝ} (hh : 0 ≤ h) {m : ℕ} {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    1 - Real.cos (h * Real.log ((p : ℕ) : ℝ)) ≤ (h * Real.exp ((m : ℝ) + 1 + θ)) ^ 2 / 2 := by
  rw [mem_primeBlockSub] at hp
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hlog0 : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg hp1
  have hlog : Real.log ((p : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) + 1 + θ) := by
    have h1 := Real.log_le_log (by linarith) hp.2
    rw [blockScale, Real.log_exp] at h1
    push_cast at h1
    exact h1
  have h1 := Real.one_sub_sq_div_two_le_cos (x := h * Real.log ((p : ℕ) : ℝ))
  have h2 : (h * Real.log ((p : ℕ) : ℝ)) ^ 2 ≤ (h * Real.exp ((m : ℝ) + 1 + θ)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hh hlog0) (mul_le_mul_of_nonneg_left hlog hh) 2
  linarith

/-- **The drift deficit, pointwise**: `S - C(h) ≤ S·(he^{m+1+θ})²/2` (`1 - cos x ≤ x²/2`). -/
lemma blockRpowSum_sub_blockCosSum_le_sq {θ σ h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    blockRpowSum θ σ m - blockCosSum θ σ h m
      ≤ blockRpowSum θ σ m * ((h * Real.exp ((m : ℝ) + 1 + θ)) ^ 2 / 2) := by
  rw [blockRpowSum, blockCosSum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hw : 0 ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        - Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
      = ((p : ℕ) : ℝ) ^ (-1 - 2 * σ) * (1 - Real.cos (h * Real.log ((p : ℕ) : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_sub_cos_le_of_mem_primeBlockSub hh hp) hw

/-- The damping `p^{-2σ} ∈ [e^{-2σe^{m+1+θ}}, 1]` on block `m`, against the weights `1 - cos ≥ 0`:
`e^{-2σe^{m+1+θ}}(S⁰ - C⁰(h)) ≤ S - C(h) ≤ S⁰ - C⁰(h)`, `⁰` the sums at `σ = 0`. -/
lemma blockRpowSum_sub_blockCosSum_bounds_zero {θ σ h : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    Real.exp (-(2 * σ * Real.exp ((m : ℝ) + 1 + θ)))
        * (blockRpowSum θ 0 m - blockCosSum θ 0 h m)
        ≤ blockRpowSum θ σ m - blockCosSum θ σ h m
      ∧ blockRpowSum θ σ m - blockCosSum θ σ h m
        ≤ blockRpowSum θ 0 m - blockCosSum θ 0 h m := by
  have hterm : ∀ p ∈ primeBlockSub θ m,
      ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
          - Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * σ)
        = Real.exp (-(2 * σ * Real.log ((p : ℕ) : ℝ)))
          * (((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))
            - Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))) := by
    intro p _
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show (-1 - 2 * σ : ℝ) = -1 + -(2 * σ) by ring, Real.rpow_add hp0,
      Real.rpow_def_of_pos hp0 (-(2 * σ)), mul_zero, sub_zero]
    ring_nf
  have hsplit : blockRpowSum θ σ m - blockCosSum θ σ h m
      = ∑ p ∈ primeBlockSub θ m, Real.exp (-(2 * σ * Real.log ((p : ℕ) : ℝ)))
          * (((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))
            - Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))) := by
    rw [blockRpowSum, blockCosSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have hzero : blockRpowSum θ 0 m - blockCosSum θ 0 h m
      = ∑ p ∈ primeBlockSub θ m, (((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))
          - Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))) := by
    rw [blockRpowSum, blockCosSum, ← Finset.sum_sub_distrib]
  have hnn : ∀ p ∈ primeBlockSub θ m, 0 ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ))
      - Real.cos (h * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ)) := by
    intro p _
    have hw : 0 ≤ ((p : ℕ) : ℝ) ^ (-1 - 2 * (0 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hc := Real.cos_le_one (h * Real.log ((p : ℕ) : ℝ))
    nlinarith
  rw [hsplit, hzero, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (hnn p hp)
    rw [mem_primeBlockSub] at hp
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hlog : Real.log ((p : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) + 1 + θ) := by
      have h1 := Real.log_le_log (by linarith) hp.2
      rw [blockScale, Real.log_exp] at h1
      push_cast at h1
      exact h1
    exact Real.exp_le_exp.2 (by nlinarith)
  · refine Finset.sum_le_sum fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have he : Real.exp (-(2 * σ * Real.log ((p : ℕ) : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.log_nonneg hp1])
    exact mul_le_of_le_one_left (hnn p hp) he

/-- **The drift deficit, integrated** (the two-regime cosine sum `RMF.blockCosErr` at `σ = 0`): for
`m + k ≥ 20` and `0 < h ≤ 2e^{-20}`,
`S - C(h) ≤ (e² - 1)e^{2(m + log h + k)}/4 + 1/150000 + 7.43·10⁻⁸`. -/
lemma blockRpowSum_sub_blockCosSum_le_blockCos {k m : ℕ} {σ h : ℝ} (hσ : 0 ≤ σ)
    (hkm : 20 ≤ (m : ℝ) + k) (hh0 : 0 < h) (hh : h ≤ 2 * Real.exp (-20)) :
    blockRpowSum k σ m - blockCosSum k σ h m
      ≤ (Real.exp 2 - 1) * Real.exp (2 * ((m : ℝ) + (Real.log h + k))) / 4
        + (1 / 150000 + 7.43 / 10 ^ 8) := by
  have h1 := (blockRpowSum_sub_blockCosSum_bounds_zero (θ := k) (h := h) hσ m).2
  have h2 := blockRpowSum_le (θ := k) (σ := 0) (m := m) le_rfl (by linarith)
  have h3 := abs_le.1 (abs_blockCosSum_sub_blockCos_le (k := k) (m := m) (σ := 0) (δ := 0) le_rfl
    hh0 (by simp))
  have h4 := blockCosErr_le_numeral (θ := k) (m := m) hkm hh
  have h5 := one_sub_le_blockCos (Real.log h + k) m
  linarith [h3.1]

/-- **The block's Mertens sum**: `e^{-2η}(1 - 1/150000) ≤ S ≤ 1 + 1/150000` for
`σe^{m+1+θ} ≤ η`, `m + θ ≥ 16` (`RMF.sum_norm_sq_primeBlockSub_bounds_sharp`). -/
lemma blockRpowSum_bounds_of_mul_exp_le {θ σ η : ℝ} {m : ℕ} (hm : 16 ≤ (m : ℝ) + θ)
    (hσ : 0 ≤ σ) (hη : σ * Real.exp ((m : ℝ) + 1 + θ) ≤ η) :
    Real.exp (-(2 * η)) * (1 - 1 / 150000) ≤ blockRpowSum θ σ m
      ∧ blockRpowSum θ σ m ≤ 1 + 1 / 150000 := by
  have hη' : |σ| * Real.log (blockScale θ (m + 1)) ≤ η := by
    rw [abs_of_nonneg hσ, log_blockScale]
    push_cast
    exact hη
  have hS : blockRpowSum θ σ m
      = ∑ p ∈ primeBlockSub θ m, ‖((p : ℕ) : ℂ) ^ (-(shiftLine σ 0))‖ ^ 2 :=
    Finset.sum_congr rfl fun p _ => (norm_sq_prime_cpow_neg p (re_shiftLine σ 0)).symm
  rw [hS]
  exact sum_norm_sq_primeBlockSub_bounds_sharp (w := fun p => ((p : ℕ) : ℂ) ^ (-(shiftLine σ 0)))
    hm hσ hη' fun p _ => norm_sq_prime_cpow_neg p (re_shiftLine σ 0)

/-- On block `m` at offset `θ`, `u_p ≤ e^{-e^{m+θ}/2}` (`p > e^{e^{m+θ}}`). -/
lemma twistU_le_exp_of_mem_primeBlockSub {θ σ : ℝ} (hσ : 0 ≤ σ) {m : ℕ} {p : Nat.Primes}
    (hp : p ∈ primeBlockSub θ m) :
    twistU σ p ≤ Real.exp (-(Real.exp ((m : ℝ) + θ) / 2)) := by
  rw [mem_primeBlockSub] at hp
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hlog : Real.exp ((m : ℝ) + θ) < Real.log ((p : ℕ) : ℝ) := by
    have h1 := Real.log_lt_log (blockScale_pos θ m) hp.1
    rwa [log_blockScale] at h1
  have he0 := Real.exp_pos ((m : ℝ) + θ)
  rw [twistU, Real.rpow_def_of_pos hp0]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- **The cubic remainders decay along the ladder**: `∑_{B_m} u³ ≤ e^{-e^{m+θ}/2}·S_m`. -/
lemma sum_twistU_cube_le {θ σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    ∑ p ∈ primeBlockSub θ m, twistU σ p ^ 3
      ≤ Real.exp (-(Real.exp ((m : ℝ) + θ) / 2)) * blockRpowSum θ σ m := by
  rw [← sum_twistU_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have h1 := twistU_le_exp_of_mem_primeBlockSub hσ hp
  have h0 := twistU_nonneg σ p
  calc twistU σ p ^ 3 = twistU σ p * twistU σ p ^ 2 := by ring
    _ ≤ Real.exp (-(Real.exp ((m : ℝ) + θ) / 2)) * twistU σ p ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- `e^{-e^{m+θ}/2} ≤ e^{-e^{20}/2}·e^{-m}` from `θ ≥ 20`: the remainders are summable in `m`. -/
lemma exp_neg_exp_le_geom {θ : ℝ} (hθ : 20 ≤ θ) (m : ℕ) :
    Real.exp (-(Real.exp ((m : ℝ) + θ) / 2))
      ≤ Real.exp (-(Real.exp 20 / 2)) * Real.exp (-1) ^ m := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.exp 20 * ((m : ℝ) + 1) ≤ Real.exp ((m : ℝ) + θ) := by
    have ha := Real.add_one_le_exp (m : ℝ)
    have hb : Real.exp ((m : ℝ) + 20) ≤ Real.exp ((m : ℝ) + θ) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_add, mul_comm (Real.exp (m : ℝ))] at hb
    nlinarith [Real.exp_pos 20]
  have h2 : (2 : ℝ) ≤ Real.exp 20 := by
    have := Real.add_one_le_exp (20 : ℝ)
    linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-! ### The steps below the top: the Ville factor

The reversed step `i ≥ 1` is the block `m = K - 1 - i` at offset `k₁` (scale `k - 1 - i`), where
`he^{m+1+k₁} = ye^{-i}`, `y = he^k`.  By item 2 its exponent is at most
`tS(t/2 - (2q - ½)) + 2t(S - C(h)) + (14t + t²/2)∑u³`, and the deficit `S - C(h)` is at most
`Sy²e^{-2i}/2` (pointwise) and `(1 - e^{-2})y²e^{-2i}/4 + 1/150000 + 7.43·10⁻⁸` (integrated);
`RMF.c3Step` is the smaller of the two resulting exponents. -/

/-- The lower end of the Mertens bracket, `e^{-2η}(1 - 1/150000)` (`σe^k ≤ η`). -/
noncomputable def c3Slo (η : ℝ) : ℝ := Real.exp (-(2 * η)) * (1 - 1 / 150000)

/-- The upper end of the Mertens bracket, `1 + 1/150000`. -/
noncomputable def c3Shi : ℝ := 1 + 1 / 150000

/-- `max(S_lo z, S_hi z) ≥ Sz` for every `S ∈ [S_lo, S_hi]`. -/
noncomputable def c3Scale (η z : ℝ) : ℝ := max (c3Slo η * z) (c3Shi * z)

/-- **The exponent of step `i`**: the smaller of the pointwise and the integrated bound. -/
noncomputable def c3Step (q t η y : ℝ) (i : ℕ) : ℝ :=
  min (c3Scale η (t * (y ^ 2 * Real.exp (-(2 * (i : ℝ))) + (t / 2 - (2 * q - 1 / 2)))))
    (c3Scale η (t * (t / 2 - (2 * q - 1 / 2)))
      + 2 * t * ((1 - Real.exp (-2)) * y ^ 2 * Real.exp (-(2 * (i : ℝ))) / 4
        + (1 / 150000 + 7.43 / 10 ^ 8)))

/-- `∑_{1 ≤ i < K} max(0, c3Step i)`: the logarithm of the Ville factor, up to `RMF.villeErr`. -/
noncomputable def villeSum (q t η y : ℝ) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 K, max 0 (c3Step q t η y i)

/-- The steps' cubic remainders, summed over any ladder: `3(14t + t²/2)e^{-e^{20}/2}`. -/
noncomputable def villeErr (t : ℝ) : ℝ := (14 * t + t ^ 2 / 2) * (3 * Real.exp (-(Real.exp 20 / 2)))

/-- **The Ville factor** `F(q, t, K) = exp(villeSum + villeErr)`. -/
noncomputable def villeFactor (q t η y : ℝ) (K : ℕ) : ℝ :=
  Real.exp (villeSum q t η y K + villeErr t)

lemma c3Slo_le_c3Shi {η : ℝ} (hη : 0 ≤ η) : c3Slo η ≤ c3Shi := by
  have h := Real.exp_le_one_iff.2 (by linarith : -(2 * η) ≤ 0)
  rw [c3Slo, c3Shi]
  nlinarith [Real.exp_pos (-(2 * η))]

lemma c3Slo_pos (η : ℝ) : 0 < c3Slo η := by
  rw [c3Slo]
  exact mul_pos (Real.exp_pos _) (by norm_num)

lemma mul_le_c3Scale {η S z : ℝ} (hlo : c3Slo η ≤ S) (hhi : S ≤ c3Shi) : S * z ≤ c3Scale η z := by
  rw [c3Scale]
  rcases le_total 0 z with hz | hz
  · exact (mul_le_mul_of_nonneg_right hhi hz).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right hlo hz).trans (le_max_left _ _)

lemma c3Scale_mono {η : ℝ} {z z' : ℝ} (hz : z ≤ z') : c3Scale η z ≤ c3Scale η z' :=
  max_le_max (mul_le_mul_of_nonneg_left hz (c3Slo_pos η).le)
    (mul_le_mul_of_nonneg_left hz (by norm_num [c3Shi]))

/-- `(he^{a-b})² = (he^a)²e^{-2b}`. -/
lemma sq_mul_exp_sub (h a b : ℝ) :
    (h * Real.exp (a - b)) ^ 2 = (h * Real.exp a) ^ 2 * Real.exp (-(2 * b)) := by
  rw [mul_pow, mul_pow, sq (Real.exp (a - b)), sq (Real.exp a), ← Real.exp_add, ← Real.exp_add,
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `(e² - 1)e^{2(c + log h)} = (1 - e^{-2})h²e^{2(c+1)}`. -/
lemma exp_two_sub_one_mul_exp_eq {h : ℝ} (h0 : 0 < h) (c : ℝ) :
    (Real.exp 2 - 1) * Real.exp (2 * (c + Real.log h))
      = (1 - Real.exp (-2)) * (h ^ 2 * Real.exp (2 * (c + 1))) := by
  have e1 : Real.exp (2 * Real.log h) = h ^ 2 := by
    rw [show (2 : ℝ) * Real.log h = Real.log h + Real.log h by ring, Real.exp_add,
      Real.exp_log h0, sq]
  have e2 : Real.exp (2 * (c + 1)) = Real.exp 2 * Real.exp (2 * c) := by
    rw [← Real.exp_add]
    ring_nf
  have e3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  rw [show 2 * (c + Real.log h) = 2 * c + 2 * Real.log h by ring, Real.exp_add, e1, e2]
  linear_combination (h ^ 2 * Real.exp (2 * c)) * e3

section Ville

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Item 3: one step below the top.**  For the reversed step `1 ≤ i < K = k - k₁` of the
ladder, `k₁ ≥ 20`, `σe^k ≤ η`, `0 < h ≤ e^{-k}`, `0 ≤ q ≤ 1`, `t ≥ 0`:
`E_tw e^{-tY_i} ≤ exp(max(0, c3Step q t η (he^k) i) + ε_i)`,
`ε_i = (14t + t²/2)S_hi e^{-e^{20}/2}e^{-(K-1-i)}`. -/
theorem integral_exp_neg_mul_halfLadderStep_le (hX : IsRademacherPrimeValues X μ) {k₁ k : ℕ}
    (hk₁ : 20 ≤ k₁) {σ η : ℝ} (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ η) {h : ℝ} (hh0 : 0 < h)
    (hh : h ≤ Real.exp (-(k : ℝ))) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {t : ℝ} (ht : 0 ≤ t)
    {i : ℕ} (hiK : i < k - k₁) :
    ∫ ω, Real.exp (-(t * halfLadderStep X σ k₁ k i ω))
        ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q)
      ≤ Real.exp (max 0 (c3Step q t η (h * Real.exp k) i)
          + (14 * t + t ^ 2 / 2) * (c3Shi * Real.exp (-(Real.exp 20 / 2)))
            * Real.exp (-1) ^ (k - k₁ - 1 - i)) := by
  set m := k - k₁ - 1 - i with hm
  have hmk : (m : ℝ) + i + 1 + k₁ = k := by
    have : m + i + 1 + k₁ = k := by omega
    exact_mod_cast this
  have hk₁' : (20 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm20 : 20 ≤ (m : ℝ) + k₁ := by linarith
  rw [halfLadderStep_of_lt X σ hiK]
  have hB : primeBlockSub (k₁ : ℝ) m ⊆ primesIcoSub (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) :=
    primeBlockSub_subset_primesIcoSub_scaleCut (by omega)
  refine (integral_exp_neg_mul_halfBlock_twistMeasure_le hX hσ h hq0 hq1 hm20 hB ht).trans
    (Real.exp_le_exp.2 ?_)
  set S := blockRpowSum (k₁ : ℝ) σ m
  set C := blockCosSum (k₁ : ℝ) σ h m
  set E3 := ∑ p ∈ primeBlockSub (k₁ : ℝ) m, twistU σ p ^ 3
  set y := h * Real.exp k
  have hη : σ * Real.exp ((m : ℝ) + 1 + k₁) ≤ η :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hσ) hση
  obtain ⟨hSlo, hShi⟩ := blockRpowSum_bounds_of_mul_exp_le (by linarith) hσ hη
  have hS0 : 0 ≤ S := blockRpowSum_nonneg _ _ _
  -- the two bounds on the deficit
  have hpt : S - C ≤ S * (y ^ 2 * Real.exp (-(2 * (i : ℝ))) / 2) := by
    have h1 := blockRpowSum_sub_blockCosSum_le_sq (θ := (k₁ : ℝ)) (σ := σ) hh0.le m
    rwa [show (m : ℝ) + 1 + k₁ = k - i by linarith, sq_mul_exp_sub] at h1
  have hint : S - C ≤ (1 - Real.exp (-2)) * y ^ 2 * Real.exp (-(2 * (i : ℝ))) / 4
      + (1 / 150000 + 7.43 / 10 ^ 8) := by
    have hh2 : h ≤ 2 * Real.exp (-20) := by
      have : Real.exp (-(k : ℝ)) ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith)
      linarith [Real.exp_pos (-20)]
    have h1 := blockRpowSum_sub_blockCosSum_le_blockCos (k := k₁) (m := m) hσ hm20 hh0 hh2
    have h2 := exp_two_sub_one_mul_exp_eq hh0 ((m : ℝ) + k₁)
    rw [show (m : ℝ) + (Real.log h + k₁) = (m : ℝ) + k₁ + Real.log h by ring, h2,
      show 2 * ((m : ℝ) + k₁ + 1) = 2 * (k : ℝ) + -(2 * (i : ℝ)) by linarith, Real.exp_add]
      at h1
    have h3 : h ^ 2 * (Real.exp (2 * (k : ℝ)) * Real.exp (-(2 * (i : ℝ))))
        = y ^ 2 * Real.exp (-(2 * (i : ℝ))) := by
      rw [show (2 : ℝ) * k = k + k by ring, Real.exp_add]
      ring
    rw [h3] at h1
    linarith
  -- the main part of the exponent
  have hmain : -(t * ((2 * q - 1 / 2) * S - 2 * (S - C))) + t ^ 2 * S / 2
      ≤ c3Step q t η y i := by
    have hid : -(t * ((2 * q - 1 / 2) * S - 2 * (S - C))) + t ^ 2 * S / 2
        = S * (t * (t / 2 - (2 * q - 1 / 2))) + 2 * t * (S - C) := by ring
    rw [hid, c3Step]
    refine le_min ?_ ?_
    · have h1 : S * (t * (t / 2 - (2 * q - 1 / 2))) + 2 * t * (S - C)
          ≤ S * (t * (y ^ 2 * Real.exp (-(2 * (i : ℝ))) + (t / 2 - (2 * q - 1 / 2)))) := by
        have := mul_le_mul_of_nonneg_left hpt (by linarith : (0 : ℝ) ≤ 2 * t)
        nlinarith
      exact h1.trans (mul_le_c3Scale hSlo hShi)
    · have h1 := mul_le_c3Scale (z := t * (t / 2 - (2 * q - 1 / 2))) hSlo hShi
      have h2 := mul_le_mul_of_nonneg_left hint (by linarith : (0 : ℝ) ≤ 2 * t)
      linarith
  -- the cubic remainders
  have hrem : (14 * t + t ^ 2 / 2) * E3
      ≤ (14 * t + t ^ 2 / 2) * (c3Shi * Real.exp (-(Real.exp 20 / 2))) * Real.exp (-1) ^ m := by
    have h1 := sum_twistU_cube_le (θ := (k₁ : ℝ)) hσ m
    have h2 := exp_neg_exp_le_geom (θ := (k₁ : ℝ)) hk₁' m
    have h3 : E3 ≤ c3Shi * Real.exp (-(Real.exp 20 / 2)) * Real.exp (-1) ^ m := by
      refine h1.trans ?_
      calc Real.exp (-(Real.exp ((m : ℝ) + k₁) / 2)) * S
          ≤ (Real.exp (-(Real.exp 20 / 2)) * Real.exp (-1) ^ m) * c3Shi :=
            mul_le_mul h2 hShi hS0 (by positivity)
        _ = c3Shi * Real.exp (-(Real.exp 20 / 2)) * Real.exp (-1) ^ m := by ring
    rw [mul_assoc (14 * t + t ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have := le_max_right 0 (c3Step q t η y i)
  linarith

/-- **The Ville factor bounds the steps' product**: with `f i` the bound of
`RMF.integral_exp_neg_mul_halfLadderStep_le`,
`∏_{1 ≤ i < K} max(1, f_i) ≤ villeFactor q t η y K`. -/
lemma prod_max_one_stepBound_le {k₁ k : ℕ} {q t η y : ℝ} (ht : 0 ≤ t) :
    ∏ i ∈ Finset.Ico 1 (k - k₁), max 1 (Real.exp (max 0 (c3Step q t η y i)
        + (14 * t + t ^ 2 / 2) * (c3Shi * Real.exp (-(Real.exp 20 / 2)))
          * Real.exp (-1) ^ (k - k₁ - 1 - i)))
      ≤ villeFactor q t η y (k - k₁) := by
  set K := k - k₁
  set A : ℝ := (14 * t + t ^ 2 / 2) * (c3Shi * Real.exp (-(Real.exp 20 / 2))) with hA
  have hA0 : 0 ≤ A := by rw [hA, c3Shi]; positivity
  have hmax : ∀ i ∈ Finset.Ico 1 K, max 1 (Real.exp (max 0 (c3Step q t η y i)
        + A * Real.exp (-1) ^ (K - 1 - i)))
      = Real.exp (max 0 (c3Step q t η y i) + A * Real.exp (-1) ^ (K - 1 - i)) := by
    intro i _
    refine max_eq_right (Real.one_le_exp ?_)
    have := le_max_left 0 (c3Step q t η y i)
    positivity
  rw [Finset.prod_congr rfl hmax, ← Real.exp_sum, villeFactor]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_add_distrib, villeSum]
  refine add_le_add_right ?_ _
  -- the remainders: a reflected geometric sum
  rw [← Finset.mul_sum]
  have hK1 : K ≤ K - 1 + 1 := by omega
  have hrefl := Finset.sum_Ico_reflect (fun j => Real.exp (-1) ^ j) 1 hK1
  rw [hrefl]
  have he0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have he1 : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hgeom := geom_sum_Ico_le_of_lt_one (m := K - 1 + 1 - K) (n := K - 1 + 1 - 1) he0 he1
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    linarith
  have hpow : Real.exp (-1) ^ (K - 1 + 1 - K) ≤ 1 := pow_le_one₀ he0 he1.le
  have hsum : ∑ j ∈ Finset.Ico (K - 1 + 1 - K) (K - 1 + 1 - 1), Real.exp (-1) ^ j ≤ 2 := by
    refine hgeom.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc A * ∑ j ∈ Finset.Ico (K - 1 + 1 - K) (K - 1 + 1 - 1), Real.exp (-1) ^ j
      ≤ A * 2 := mul_le_mul_of_nonneg_left hsum hA0
    _ ≤ villeErr t := by
        rw [hA, villeErr, c3Shi]
        have he := Real.exp_pos (-(Real.exp 20 / 2))
        have h14 : 0 ≤ 14 * t + t ^ 2 / 2 := by positivity
        nlinarith

end Ville

/-! ### The Ville factor's monotonicity -/

/-- `max(0, c3Step)` is antitone in `q` and monotone in `y ≥ 0`. -/
lemma max_zero_c3Step_mono {q q' t η y y' : ℝ} (i : ℕ) (ht : 0 ≤ t) (hq : q' ≤ q)
    (hy0 : 0 ≤ y) (hy : y ≤ y') :
    max 0 (c3Step q t η y i) ≤ max 0 (c3Step q' t η y' i) := by
  refine max_le_max le_rfl ?_
  have hy2 : y ^ 2 ≤ y' ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have he := Real.exp_pos (-(2 * (i : ℝ)))
  have he2 : 0 ≤ 1 - Real.exp (-2) := by
    have := Real.exp_le_one_iff.2 (by norm_num : (-2 : ℝ) ≤ 0)
    linarith
  rw [c3Step, c3Step]
  refine min_le_min (c3Scale_mono ?_) (add_le_add (c3Scale_mono ?_) ?_)
  · refine mul_le_mul_of_nonneg_left ?_ ht
    nlinarith
  · refine mul_le_mul_of_nonneg_left ?_ ht
    linarith
  · refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have := mul_le_mul_of_nonneg_right hy2 he.le
    have := mul_le_mul_of_nonneg_left this he2
    nlinarith

/-- **The Ville factor for `K ≤ K_max`.**  It is monotone in `K` and `y ≥ 0` and antitone in
`q`: `villeFactor q t η y K ≤ villeFactor q_lo t η y_hi K_max`. -/
theorem villeFactor_le_of_le {q q_lo t η y y_hi : ℝ} {K K_max : ℕ} (ht : 0 ≤ t)
    (hq : q_lo ≤ q) (hy0 : 0 ≤ y) (hy : y ≤ y_hi) (hK : K ≤ K_max) :
    villeFactor q t η y K ≤ villeFactor q_lo t η y_hi K_max := by
  rw [villeFactor, villeFactor]
  refine Real.exp_le_exp.2 (add_le_add ?_ le_rfl)
  rw [villeSum, villeSum]
  calc ∑ i ∈ Finset.Ico 1 K, max 0 (c3Step q t η y i)
      ≤ ∑ i ∈ Finset.Ico 1 K, max 0 (c3Step q_lo t η y_hi i) :=
        Finset.sum_le_sum fun i _ => max_zero_c3Step_mono i ht hq hy0 hy
    _ ≤ ∑ i ∈ Finset.Ico 1 K_max, max 0 (c3Step q_lo t η y_hi i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hK)
          fun i _ _ => le_max_left _ _

/-! ### The smooth minorant of the top step

`1{y > 0}(1 - Fe^{-ty}) ≥ S(y/δ) - F·S((y + δ)/δ)e^{-ty}` (`S` the smoothstep): the first term
is `≤ 1{y > 0}`, the second `≥ 1{y > 0}e^{-ty}`.  Both are `C³` with explicit derivative bounds
(the second through the chain `RMF.lindExp`, …, `RMF.lindExp₃`), so the Lindeberg swap applies
to each, and against a Gaussian each is bounded by a normal distribution function. -/

/-- `S((y - a)/δ)·e^{-ty}`: vanishes for `y ≤ a`, and is `e^{-ty}` for `y ≥ a + δ`. -/
noncomputable def lindExp (δ a t y : ℝ) : ℝ := smoothstep ((y - a) / δ) * Real.exp (-(t * y))

/-- The first derivative of `RMF.lindExp`. -/
noncomputable def lindExp₁ (δ a t y : ℝ) : ℝ :=
  (deriv smoothstep ((y - a) / δ) / δ - t * smoothstep ((y - a) / δ)) * Real.exp (-(t * y))

/-- The second derivative of `RMF.lindExp`. -/
noncomputable def lindExp₂ (δ a t y : ℝ) : ℝ :=
  (deriv (deriv smoothstep) ((y - a) / δ) / δ / δ - 2 * t * (deriv smoothstep ((y - a) / δ) / δ)
    + t ^ 2 * smoothstep ((y - a) / δ)) * Real.exp (-(t * y))

/-- The third derivative of `RMF.lindExp`. -/
noncomputable def lindExp₃ (δ a t y : ℝ) : ℝ :=
  (deriv (deriv (deriv smoothstep)) ((y - a) / δ) / δ / δ / δ
    - 3 * t * (deriv (deriv smoothstep) ((y - a) / δ) / δ / δ)
    + 3 * t ^ 2 * (deriv smoothstep ((y - a) / δ) / δ) - t ^ 3 * smoothstep ((y - a) / δ))
    * Real.exp (-(t * y))

lemma hasDerivAt_exp_neg_mul (t x : ℝ) :
    HasDerivAt (fun y => Real.exp (-(t * y))) (-t * Real.exp (-(t * x))) x :=
  (((hasDerivAt_id' x).const_mul t).neg.exp).congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma hasDerivAt_lindExp (δ a t x : ℝ) : HasDerivAt (lindExp δ a t) (lindExp₁ δ a t x) x := by
  have h := (hasDerivAt_rise δ a x).mul (hasDerivAt_exp_neg_mul t x)
  exact h.congr_deriv (by simp only [lindExp₁]; ring)

lemma hasDerivAt_lindExp₁ (δ a t x : ℝ) : HasDerivAt (lindExp₁ δ a t) (lindExp₂ δ a t x) x := by
  have h := ((hasDerivAt_rise₁ δ a x).sub ((hasDerivAt_rise δ a x).const_mul t)).mul
    (hasDerivAt_exp_neg_mul t x)
  exact h.congr_deriv (by simp only [lindExp₂, Pi.sub_apply]; ring)

lemma hasDerivAt_lindExp₂ (δ a t x : ℝ) : HasDerivAt (lindExp₂ δ a t) (lindExp₃ δ a t x) x := by
  have h := (((hasDerivAt_rise₂ δ a x).sub ((hasDerivAt_rise₁ δ a x).const_mul (2 * t))).add
    ((hasDerivAt_rise δ a x).const_mul (t ^ 2))).mul (hasDerivAt_exp_neg_mul t x)
  exact h.congr_deriv (by simp only [lindExp₃, Pi.sub_apply, Pi.add_apply]; ring)

/-- The four derivative bounds of `RMF.lindExp` for `t ≥ 0`: each factor `S^{(j)}/δ^j` against
`e^{-ty} ≤ e^{-ta}` where the smoothstep is active (`y > a`), and `0` below. -/
noncomputable def lindM (δ a t : ℝ) : Fin 4 → ℝ
  | 0 => Real.exp (-(t * a))
  | 1 => (35 / 16 / δ + t) * Real.exp (-(t * a))
  | 2 => (105 / 4 / δ / δ + 2 * t * (35 / 16 / δ) + t ^ 2) * Real.exp (-(t * a))
  | 3 => (105 / 2 / δ / δ / δ + 3 * t * (105 / 4 / δ / δ) + 3 * t ^ 2 * (35 / 16 / δ) + t ^ 3)
      * Real.exp (-(t * a))

/-- The atoms of every derivative bound: `|S^{(j)}(x)|/δ^j ≤ C_j/δ^j`. -/
lemma smoothstep_atom_bounds {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |smoothstep x| ≤ 1 ∧ |deriv smoothstep x / δ| ≤ 35 / 16 / δ
      ∧ |deriv (deriv smoothstep) x / δ / δ| ≤ 105 / 4 / δ / δ
      ∧ |deriv (deriv (deriv smoothstep)) x / δ / δ / δ| ≤ 105 / 2 / δ / δ / δ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (smoothstep_nonneg x)]
    exact smoothstep_le_one x
  · rw [abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (abs_deriv_smoothstep_le x) hδ.le
  · rw [abs_div, abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (abs_deriv2_smoothstep_le x)
      hδ.le) hδ.le
  · rw [abs_div, abs_div, abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
      (abs_deriv3_smoothstep_le x) hδ.le) hδ.le) hδ.le

lemma abs_mul_exp_neg_le {P M t a y : ℝ} (ht : 0 ≤ t) (hay : a ≤ y) (hP : |P| ≤ M) :
    |P * Real.exp (-(t * y))| ≤ M * Real.exp (-(t * a)) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hP (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
    ((abs_nonneg _).trans hP)

/-- **The derivative bounds of `RMF.lindExp`**, for `δ > 0`, `t ≥ 0`. -/
theorem abs_lindExp_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) (y : ℝ) :
    |lindExp δ a t y| ≤ lindM δ a t 0 ∧ |lindExp₁ δ a t y| ≤ lindM δ a t 1
      ∧ |lindExp₂ δ a t y| ≤ lindM δ a t 2 ∧ |lindExp₃ δ a t y| ≤ lindM δ a t 3 := by
  have he := Real.exp_pos (-(t * a))
  have hM : ∀ j, 0 ≤ lindM δ a t j := by
    intro j
    fin_cases j <;> simp only [lindM] <;> positivity
  rcases le_or_gt y a with hya | hya
  · have hx : (y - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    simp only [lindExp, lindExp₁, lindExp₂, lindExp₃, smoothstep_of_nonpos hx,
      deriv_smoothstep_of_nonpos hx, deriv2_smoothstep_of_nonpos hx,
      deriv3_smoothstep_of_nonpos hx]
    simp only [zero_div, mul_zero, zero_mul, add_zero, abs_zero, sub_self]
    exact ⟨hM 0, hM 1, hM 2, hM 3⟩
  obtain ⟨b0, b1, b2, b3⟩ := smoothstep_atom_bounds hδ ((y - a) / δ)
  set s0 := smoothstep ((y - a) / δ)
  set s1 := deriv smoothstep ((y - a) / δ) / δ
  set s2 := deriv (deriv smoothstep) ((y - a) / δ) / δ / δ
  set s3 := deriv (deriv (deriv smoothstep)) ((y - a) / δ) / δ / δ / δ
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have hc : ∀ {c X M : ℝ}, 0 ≤ c → |X| ≤ M → |c * X| ≤ c * M := fun hc hX => by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hX hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 := abs_mul_exp_neg_le ht hya.le b0
    rw [one_mul] at h0
    exact h0
  · refine abs_mul_exp_neg_le ht hya.le ?_
    have h1 := hc ht b0
    exact (abs_sub _ _).trans (by linarith)
  · refine abs_mul_exp_neg_le ht hya.le ?_
    have h1 := hc (by linarith : (0 : ℝ) ≤ 2 * t) b1
    have h2 := hc ht2 b0
    exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add b2 h1)) h2)
      |>.trans (by linarith)
  · refine abs_mul_exp_neg_le ht hya.le ?_
    have h1 := hc (by linarith : (0 : ℝ) ≤ 3 * t) b2
    have h2 := hc (by positivity : (0 : ℝ) ≤ 3 * t ^ 2) b1
    have h3 := hc ht3 b0
    refine (abs_sub _ _).trans ?_
    refine (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add b3 h1)) h2)) h3).trans ?_
    linarith

/-- **The smooth minorant**: for `F ≥ 0`, `δ > 0`,
`S(y/δ) - F·lindExp δ (-δ) t y ≤ 1{y > 0}(1 - Fe^{-ty})`. -/
lemma smoothstep_sub_lindExp_le_indicator {δ : ℝ} (hδ : 0 < δ) (t : ℝ) {F : ℝ} (hF : 0 ≤ F)
    (y : ℝ) :
    smoothstep ((y - 0) / δ) - F * lindExp δ (-δ) t y
      ≤ (Set.Ioi (0 : ℝ)).indicator (fun y => 1 - F * Real.exp (-(t * y))) y := by
  have hL0 : 0 ≤ lindExp δ (-δ) t y := mul_nonneg (smoothstep_nonneg _) (Real.exp_pos _).le
  by_cases hy : y ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hy]
    have hy0 : (0 : ℝ) < y := hy
    have h1 : smoothstep ((y - -δ) / δ) = 1 :=
      smoothstep_of_one_le (by rw [le_div_iff₀ hδ]; linarith)
    rw [lindExp, h1, one_mul]
    linarith [smoothstep_le_one ((y - 0) / δ)]
  · rw [Set.indicator_of_notMem hy]
    have hy0 : y ≤ 0 := not_lt.1 hy
    rw [smoothstep_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
    nlinarith

/-! ### The Gaussian side of the top step -/

/-- A Gaussian integral after `y = μ - z`: `∫ g d N(μ, v) = ∫ g(μ - z) dN(0, v)(z)`. -/
lemma integral_gaussianReal_eq_integral_sub {g : ℝ → ℝ} (hg : Measurable g) (μ : ℝ) (v : ℝ≥0) :
    ∫ y, g y ∂(gaussianReal μ v) = ∫ z, g (μ - z) ∂(gaussianReal 0 v) := by
  have hmap : (gaussianReal 0 v).map (fun z => μ - z) = gaussianReal μ v := by
    have hf : (fun z : ℝ => μ - z) = (fun x : ℝ => -x) ∘ (fun z : ℝ => z + -μ) := by
      funext z
      simp only [Function.comp_apply]
      ring
    rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_add_const,
      gaussianReal_map_neg]
    simp
  rw [← hmap, integral_map (by fun_prop) hg.aestronglyMeasurable]

/-- **The first term against a Gaussian**: `Φ((μ - δ)/√v) ≤ E S(G/δ)`, `G ~ N(μ, v)`. -/
theorem normCDF_le_integral_smoothstep_gaussianReal {δ : ℝ} (hδ : 0 < δ) (μ : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) :
    normCDF ((μ - δ) / √(v : ℝ)) ≤ ∫ y, smoothstep ((y - 0) / δ) ∂(gaussianReal μ v) := by
  have hS : Continuous fun y : ℝ => smoothstep ((y - 0) / δ) :=
    contDiff_smoothstep.continuous.comp (by fun_prop)
  rw [integral_gaussianReal_eq_integral_sub hS.measurable, ← gaussianReal_real_Iic_eq_normCDF hv,
    ← integral_indicator_one measurableSet_Iic]
  have hSm : Measurable fun z : ℝ => smoothstep ((μ - z - 0) / δ) :=
    (hS.comp (by fun_prop : Continuous fun z : ℝ => μ - z)).measurable
  refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) ?_ fun z => ?_
  · refine Integrable.of_bound hSm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (smoothstep_nonneg _)]
    exact smoothstep_le_one _
  · by_cases hz : z ∈ Set.Iic (μ - δ)
    · rw [Set.indicator_of_mem hz, Pi.one_apply,
        smoothstep_of_one_le (by rw [le_div_iff₀ hδ]; linarith [(Set.mem_Iic.1 hz)])]
    · rw [Set.indicator_of_notMem hz]
      exact smoothstep_nonneg _

/-- **The exponential term against a Gaussian**: for `t ≥ 0`, `G ~ N(μ, v)`,
`E lindExp δ a t G ≤ e^{-tμ + t²v/2}Φ((μ - a - tv)/√v)`. -/
theorem integral_lindExp_gaussianReal_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ y, lindExp δ a t y ∂(gaussianReal μ v)
      ≤ Real.exp (-(t * μ) + t ^ 2 * v / 2) * normCDF ((μ - a - t * v) / √(v : ℝ)) := by
  have hvpos : (0 : ℝ) < v := by positivity
  have hL : Continuous (lindExp δ a t) := by
    unfold lindExp
    exact (contDiff_smoothstep.continuous.comp (by fun_prop)).mul (by fun_prop)
  have hform := integral_indicator_exp_gaussianReal hvpos t (μ - a)
  rw [Real.toNNReal_coe] at hform
  rw [integral_gaussianReal_eq_integral_sub hL.measurable, Real.exp_add, mul_assoc, ← hform,
    ← integral_const_mul]
  have hm : Measurable fun z : ℝ =>
      Real.exp (-(t * μ)) * (Set.Iic (μ - a)).indicator (fun y => Real.exp (t * y)) z :=
    measurable_const.mul ((by fun_prop : Measurable fun y : ℝ => Real.exp (t * y)).indicator
      measurableSet_Iic)
  have hbd : ∀ z, Real.exp (-(t * μ)) * (Set.Iic (μ - a)).indicator (fun y => Real.exp (t * y)) z
      ≤ Real.exp (-(t * a)) := by
    intro z
    by_cases hz : z ∈ Set.Iic (μ - a)
    · rw [Set.indicator_of_mem hz, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [Set.mem_Iic.1 hz])
    · rw [Set.indicator_of_notMem hz, mul_zero]
      exact (Real.exp_pos _).le
  have hnn : ∀ z, 0 ≤ Real.exp (-(t * μ))
      * (Set.Iic (μ - a)).indicator (fun y => Real.exp (t * y)) z := fun z =>
    mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) z)
  have hLm : Measurable fun z : ℝ => lindExp δ a t (μ - z) :=
    (hL.comp (by fun_prop : Continuous fun z : ℝ => μ - z)).measurable
  refine integral_mono ?_ ?_ fun z => ?_
  · refine Integrable.of_bound hLm.aestronglyMeasurable (lindM δ a t 0)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_lindExp_le hδ a ht (μ - z)).1
  · refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp (-(t * a)))
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]
    exact hbd z
  · simp only
    by_cases hz : z ∈ Set.Iic (μ - a)
    · rw [Set.indicator_of_mem hz, lindExp]
      have h1 : Real.exp (-(t * (μ - z))) = Real.exp (-(t * μ)) * Real.exp (t * z) := by
        rw [← Real.exp_add]
        ring_nf
      rw [h1]
      have h2 := smoothstep_le_one ((μ - z - a) / δ)
      have h3 : 0 ≤ Real.exp (-(t * μ)) * Real.exp (t * z) := by positivity
      nlinarith
    · rw [Set.indicator_of_notMem hz, mul_zero, lindExp,
        smoothstep_of_nonpos (div_nonpos_of_nonpos_of_nonneg
          (by linarith [not_le.1 (show ¬ z ≤ μ - a from hz)]) hδ.le), zero_mul]

/-! ### The top step compared: Lindeberg over the block's primes -/

section TopStep

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- Every `ℓ_p` is square integrable under the twisted tilt (`|ℓ_p| ≤ log(1/(1 - u_p))`,
`u_p < 1`). -/
lemma memLp_two_localLogAdd_twistMeasure (hX : IsRademacherPrimeValues X μ) (a b : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (h q : ℝ) (p : Nat.Primes) :
    MemLp (fun ω => localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω)) 2
      (twistMeasure X μ a b σ h q) := by
  haveI := isProbabilityMeasure_twistMeasure hX a b hσ h q
  have hu1 : twistU σ p < 1 := by
    rw [← norm_cpow_eq_twistU σ 0 p]
    exact norm_prime_cpow_neg_lt_one p.2 (by rw [re_shiftLine]; linarith)
  refine MemLp.of_bound
    ((measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)).aestronglyMeasurable
    (Real.log ((1 - twistU σ p)⁻¹)) ?_
  filter_upwards [ae_eq_one_or_twistMeasure hX a b σ h q p] with ω hω
  rw [Real.norm_eq_abs]
  rcases hω with h1 | h1 <;> rw [h1] <;>
    exact abs_localLogAdd_le (by simp) (norm_cpow_eq_twistU σ 0 p).le hu1

/-- **Item 4, the comparison.**  For a block past offset `20` inside the tilt's range and any
`C³` test function `f` with `|f'''| ≤ M₃`, the block against `N(E_tw Y, Var_tw Y)`:
`|E_tw f(Y) - E f(G)| ≤ M₃·105e^{-e^{20}/2}` — Lindeberg over the block's primes
(`RMF.abs_integral_sum_sub_le`) against independent Gaussians with the primes' twisted means and
variances (`RMF.exists_gaussian_matching_moments`), `∑(E|ℓ_p|³ + E|N_p|³) ≤ 104∑u³`. -/
theorem abs_integral_halfBlock_sub_gaussianReal_le (hX : IsRademacherPrimeValues X μ) {a b : ℕ}
    {θ σ : ℝ} (hσ : 0 ≤ σ) (h : ℝ) {q : ℝ} {m : ℕ} (hm : 20 ≤ (m : ℝ) + θ)
    {f f₁ f₂ f₃ : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hM₀ : ∀ x, |f x| ≤ M₀) (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂)
    (hM₃ : ∀ x, |f₃ x| ≤ M₃) :
    |∫ ω, f (halfBlock X θ σ 0 m ω) ∂(twistMeasure X μ a b σ h q)
        - ∫ y, f y ∂(gaussianReal (twistBlockMean X μ a b σ h q θ m)
            (twistBlockVar X μ a b σ h q θ m).toNNReal)|
      ≤ M₃ * (105 * Real.exp (-(Real.exp 20 / 2))) := by
  classical
  haveI := isProbabilityMeasure_twistMeasure hX a b hσ h q
  set P := twistMeasure X μ a b σ h q with hP
  set s := primeBlockSub θ m
  set ξ : Nat.Primes → Ω → ℝ := fun p ω =>
    localLogAdd (((p : ℕ) : ℂ) ^ (-shiftLine σ 0)) (X (p : ℕ) ω) with hξ
  have hξm : ∀ p, Measurable (ξ p) := fun p =>
    (measurable_localLogAdd _).comp (hX.measurable (p : ℕ) p.2)
  have hind : iIndepFun ξ P := iIndepFun_localLogAdd_twistMeasure hX a b hσ h q
  have hL2 : ∀ p, MemLp (ξ p) 2 P := fun p => memLp_two_localLogAdd_twistMeasure hX a b hσ h q p
  set m₁ : Nat.Primes → ℝ := fun p => ∫ ω, ξ p ω ∂P with hm₁
  set m₂ : Nat.Primes → ℝ := fun p => ∫ ω, ξ p ω * ξ p ω ∂P with hm₂
  have hm12 : ∀ p, m₁ p ^ 2 ≤ m₂ p := fun p => sq_integral_le_integral_mul_self (hL2 p)
  obtain ⟨Ω', mΩ', Q, G, hQ, hGm, hGi, hGlaw, hG1, hG2⟩ :=
    exists_gaussian_matching_moments m₁ m₂ hm12
  haveI := hQ
  -- the block's primes: `u_p ≤ ½` and `|ℓ_p| ≤ 2u_p`
  have hu : ∀ p ∈ s, twistU σ p ≤ 1 / 2 := fun p hp =>
    (twistU_le_of_mem_primeBlockSub hσ hm hp).trans (by norm_num)
  have hbd : ∀ p ∈ s, ∀ᵐ ω ∂P, |ξ p ω| ≤ 2 * twistU σ p := fun p hp =>
    ae_abs_localLogAdd_le_twistMeasure hX a b σ h q p (hu p hp)
  have hcube : ∀ p, Measurable fun ω => |ξ p ω| ^ 3 := fun p => (hξm p).abs.pow_const 3
  have hTξ : ∀ p ∈ s, Integrable (fun ω => |ξ p ω| ^ 3) P := fun p hp =>
    Integrable.of_bound (hcube p).aestronglyMeasurable ((2 * twistU σ p) ^ 3)
      ((hbd p hp).mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (abs_nonneg _) hω 3)
  have key := abs_integral_sum_sub_le (s := s) (P := P) (Q := Q) hf hf₁ hf₂ hM₀ hM₁ hM₂ hM₃ hξm
    hGm hind hGi (fun p _ => (hL2 p).integrable one_le_two)
    (fun p _ => (hL2 p).integrable_mul (hL2 p))
    (fun p _ => integrable_of_hasLaw_gaussianReal (hGm p) (hGlaw p))
    (fun p _ => integrable_mul_self_of_hasLaw_gaussianReal (hGm p) (hGlaw p))
    (fun p _ => (hG1 p).symm) (fun p _ => (hG2 p).symm) hTξ
    (fun p _ => integrable_abs_cube_of_hasLaw_gaussianReal (hGm p) (hGlaw p))
  -- the Gaussian side is `N(E_tw Y, Var_tw Y)`
  have hV0 : 0 ≤ twistBlockVar X μ a b σ h q θ m :=
    Finset.sum_nonneg fun p _ => by linarith [hm12 p]
  have hvar : ∑ p ∈ s, matchingVar (m₁ p) (m₂ p) = (twistBlockVar X μ a b σ h q θ m).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_sum, Real.coe_toNNReal _ hV0, twistBlockVar]
    exact Finset.sum_congr rfl fun p _ => coe_matchingVar (hm12 p)
  have hlaw := map_sum_gaussianReal hGm hGi hGlaw s
  rw [hvar] at hlaw
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hGauss : ∫ ω, f (∑ p ∈ s, G p ω) ∂Q
      = ∫ y, f y ∂(gaussianReal (twistBlockMean X μ a b σ h q θ m)
          (twistBlockVar X μ a b σ h q θ m).toNNReal) := by
    rw [twistBlockMean, ← hlaw, integral_map (Finset.measurable_sum s fun p _ => hGm p).aemeasurable
      hfc.aestronglyMeasurable]
  have hY : ∀ ω, halfBlock X θ σ 0 m ω = ∑ p ∈ s, ξ p ω := fun ω => rfl
  simp only [hY]
  rw [← hGauss]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hM₃ 0)))
  -- the third moments
  have hA3 := absMomentConst_three_le
  have hper : ∀ p ∈ s, (∫ ω, |ξ p ω| ^ 3 ∂P) + ∫ ω, |G p ω| ^ 3 ∂Q ≤ 104 * twistU σ p ^ 3 := by
    intro p hp
    have hu0 := twistU_nonneg σ p
    have h1 : ∫ ω, |ξ p ω| ^ 3 ∂P ≤ (2 * twistU σ p) ^ 3 := by
      have := integral_mono_ae (hTξ p hp) (integrable_const ((2 * twistU σ p) ^ 3))
        ((hbd p hp).mono fun ω hω => pow_le_pow_left₀ (abs_nonneg _) hω 3)
      simpa using this
    have hm2 : m₂ p ≤ (2 * twistU σ p) ^ 2 := by
      have := integral_mono_ae ((hL2 p).integrable_mul (hL2 p))
        (integrable_const ((2 * twistU σ p) ^ 2))
        ((hbd p hp).mono fun ω hω => by
          simp only [Pi.mul_apply]
          rw [← sq, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
      simpa using this
    have hm1 : |m₁ p| ≤ 2 * twistU σ p := by
      have := norm_integral_le_of_norm_le_const (μ := P) (f := ξ p)
        ((hbd p hp).mono fun ω hω => by rwa [Real.norm_eq_abs])
      simpa using this
    have hsq : √(m₂ p) ≤ 2 * twistU σ p := by
      calc √(m₂ p) ≤ √((2 * twistU σ p) ^ 2) := Real.sqrt_le_sqrt hm2
        _ = 2 * twistU σ p := Real.sqrt_sq (by positivity)
    have h2 := integral_abs_cube_of_hasLaw_matching (hGm p) (hm12 p) (hGlaw p)
    have hsq3 : √(m₂ p) ^ 3 ≤ (2 * twistU σ p) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 3
    have hm13 : |m₁ p| ^ 3 ≤ (2 * twistU σ p) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hm1 3
    have hprod : absMomentConst 3 * √(m₂ p) ^ 3 ≤ 2 * (2 * twistU σ p) ^ 3 :=
      mul_le_mul hA3 hsq3 (by positivity) (by norm_num)
    have h8 : (2 * twistU σ p) ^ 3 = 8 * twistU σ p ^ 3 := by ring
    linarith
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum]
  have hE := sum_twistU_cube_le (θ := θ) (m := m) hσ
  have hS := blockRpowSum_le (θ := θ) (m := m) hσ (by linarith)
  have hexp : Real.exp (-(Real.exp ((m : ℝ) + θ) / 2)) ≤ Real.exp (-(Real.exp 20 / 2)) :=
    Real.exp_le_exp.2 (by linarith [Real.exp_le_exp.2 hm])
  have hS0 := blockRpowSum_nonneg θ σ m
  have he0 := Real.exp_pos (-(Real.exp 20 / 2))
  calc 104 * ∑ p ∈ s, twistU σ p ^ 3
      ≤ 104 * (Real.exp (-(Real.exp 20 / 2)) * (1 + 1 / 150000)) := by
        refine mul_le_mul_of_nonneg_left (hE.trans ?_) (by norm_num)
        exact mul_le_mul hexp hS hS0 he0.le
    _ ≤ 105 * Real.exp (-(Real.exp 20 / 2)) := by nlinarith

/-- **The Lindeberg error of the top step**: the two test functions' third-derivative bounds,
`105/(2δ³)` and `lindM δ (-δ) t 3`, against `∑(E|ℓ_p|³ + E|N_p|³) ≤ 105e^{-e^{20}/2}`. -/
noncomputable def lindebergErr (δ t F : ℝ) : ℝ :=
  (105 / 2 / δ / δ / δ + F * lindM δ (-δ) t 3) * (105 * Real.exp (-(Real.exp 20 / 2)))

/-- On the ladder event `{T₁ > 0}` the integrand is a function of the top step `Y₀`. -/
lemma setIntegral_ladderEvent_one_eq {P : Measure Ω} {Y : ℕ → Ω → ℝ} (hY : Measurable (Y 0))
    (g : ℝ → ℝ) :
    ∫ ω in ladderEvent Y 1, g (walk Y 1 ω) ∂P
      = ∫ ω, (Set.Ioi (0 : ℝ)).indicator g (Y 0 ω) ∂P := by
  have hw : ∀ ω, walk Y 1 ω = Y 0 ω := fun ω => by simp [walk_apply]
  have hset : ladderEvent Y 1 = Y 0 ⁻¹' Set.Ioi 0 := by
    ext ω
    rw [mem_ladderEvent, Set.mem_preimage, Set.mem_Ioi, ← hw ω]
    constructor
    · exact fun h => h 1 le_rfl le_rfl
    · intro h i h1 h2
      rwa [show i = 1 by omega]
  rw [← integral_indicator (hset ▸ hY measurableSet_Ioi)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  by_cases hω : ω ∈ ladderEvent Y 1
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (by rwa [hset] at hω), hw]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (by rwa [hset] at hω)]

/-- **Item 4: the top step, compared.**  For the ladder `[k₁, k)`, `k₁ ≥ 20`, `σ ≥ 0`,
`t ≥ 0`, `δ > 0`, `F ≥ 0`, with `μ₀ = E_tw Y₀`, `V₀ = Var_tw Y₀ > 0` the exact twisted moments of
the top block:
`Φ((μ₀ - δ)/√V₀) - F·e^{-tμ₀ + t²V₀/2}Φ((μ₀ + δ - tV₀)/√V₀) - lindebergErr δ t F
  ≤ E_tw[1{T₁ > 0}(1 - Fe^{-tT₁})]` — the `hc` of `RMF.le_setIntegral_halfLadder_twistQ_ville_of_le`
at `m = 1`. -/
theorem le_setIntegral_ladderEvent_one (hX : IsRademacherPrimeValues X μ) {k₁ k : ℕ}
    (hk₁ : 20 ≤ k₁) (hk : k₁ < k) {σ : ℝ} (hσ : 0 ≤ σ) (h q : ℝ) {t δ F : ℝ} (ht : 0 ≤ t)
    (hδ : 0 < δ) (hF : 0 ≤ F)
    (hV : 0 < twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)) :
    normCDF ((twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
          - δ) / √(twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁
            (k - k₁ - 1)))
        - F * (Real.exp (-(t * twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q
              k₁ (k - k₁ - 1)) + t ^ 2 * twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ))
                σ h q k₁ (k - k₁ - 1) / 2)
          * normCDF ((twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁
              (k - k₁ - 1) + δ - t * twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ))
                σ h q k₁ (k - k₁ - 1))
            / √(twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁
              (k - k₁ - 1))))
        - lindebergErr δ t F
      ≤ ∫ ω in ladderEvent (halfLadderStep X σ k₁ k) 1,
          (1 - F * Real.exp (-(t * walk (halfLadderStep X σ k₁ k) 1 ω)))
          ∂(twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q) := by
  haveI := isProbabilityMeasure_twistMeasure hX (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) hσ h q
  set P := twistMeasure X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q
  set m₀ := k - k₁ - 1
  set μ₀ := twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ m₀
  set V₀ := twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ m₀
  set v : ℝ≥0 := V₀.toNNReal
  have hv : (v : ℝ) = V₀ := Real.coe_toNNReal _ hV.le
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, NNReal.coe_zero] at hv
    linarith
  have hm20 : 20 ≤ (m₀ : ℝ) + k₁ := by
    have : (20 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    linarith [Nat.cast_nonneg (α := ℝ) m₀]
  have hY0 : halfLadderStep X σ k₁ k 0 = halfBlock X k₁ σ 0 m₀ := by
    rw [halfLadderStep_of_lt X σ (by omega : 0 < k - k₁)]
    rfl
  have hYm : Measurable (halfBlock X k₁ σ 0 m₀) := measurable_halfBlock hX _ σ 0 _
  rw [setIntegral_ladderEvent_one_eq (by rw [hY0]; exact hYm)
    (fun y => 1 - F * Real.exp (-(t * y))), hY0]
  -- the two test functions
  set ψ₁ : ℝ → ℝ := fun y => smoothstep ((y - 0) / δ)
  have hψ₁c : Continuous ψ₁ := contDiff_smoothstep.continuous.comp (by fun_prop)
  have hψ₂c : Continuous (lindExp δ (-δ) t) := by
    unfold lindExp
    exact (contDiff_smoothstep.continuous.comp (by fun_prop)).mul (by fun_prop)
  have hb₁ : ∀ x, |ψ₁ x| ≤ 1 := fun x => (smoothstep_atom_bounds hδ ((x - 0) / δ)).1
  have hb₂ : ∀ x, |lindExp δ (-δ) t x| ≤ lindM δ (-δ) t 0 := fun x =>
    (abs_lindExp_le hδ (-δ) ht x).1
  have hi₁ : Integrable (fun ω => ψ₁ (halfBlock X k₁ σ 0 m₀ ω)) P :=
    Integrable.of_bound (hψ₁c.measurable.comp hYm).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb₁ _)
  have hi₂ : Integrable (fun ω => lindExp δ (-δ) t (halfBlock X k₁ σ 0 m₀ ω)) P :=
    Integrable.of_bound (hψ₂c.measurable.comp hYm).aestronglyMeasurable (lindM δ (-δ) t 0)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb₂ _)
  -- the minorant
  have hminor : ∫ ω, ψ₁ (halfBlock X k₁ σ 0 m₀ ω) ∂P
      - F * ∫ ω, lindExp δ (-δ) t (halfBlock X k₁ σ 0 m₀ ω) ∂P
      ≤ ∫ ω, (Set.Ioi (0 : ℝ)).indicator (fun y => 1 - F * Real.exp (-(t * y)))
          (halfBlock X k₁ σ 0 m₀ ω) ∂P := by
    rw [← integral_const_mul, ← integral_sub hi₁ (hi₂.const_mul F)]
    refine integral_mono (hi₁.sub (hi₂.const_mul F)) ?_ fun ω =>
      smoothstep_sub_lindExp_le_indicator hδ t hF _
    have hgm : Measurable ((Set.Ioi (0 : ℝ)).indicator fun y => 1 - F * Real.exp (-(t * y))) :=
      (measurable_const.sub (measurable_const.mul
        (measurable_id.const_mul t).neg.exp)).indicator measurableSet_Ioi
    refine Integrable.of_bound (hgm.comp hYm).aestronglyMeasurable (1 + F)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases hy : halfBlock X k₁ σ 0 m₀ ω ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy]
      have he1 : Real.exp (-(t * halfBlock X k₁ σ 0 m₀ ω)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [Set.mem_Ioi.1 hy])
      have he0 := Real.exp_pos (-(t * halfBlock X k₁ σ 0 m₀ ω))
      rw [abs_le]
      constructor <;> nlinarith
    · rw [Set.indicator_of_notMem hy, abs_zero]
      linarith
  -- the two comparisons
  have hL₁ := abs_integral_halfBlock_sub_gaussianReal_le hX (a := scaleCut (k₁ : ℝ))
    (b := scaleCut (k : ℝ)) hσ h (q := q) hm20
    (f := ψ₁) (f₁ := fun y => deriv smoothstep ((y - 0) / δ) / δ)
    (f₂ := fun y => deriv (deriv smoothstep) ((y - 0) / δ) / δ / δ)
    (f₃ := fun y => deriv (deriv (deriv smoothstep)) ((y - 0) / δ) / δ / δ / δ)
    (fun x => hasDerivAt_rise δ 0 x) (fun x => hasDerivAt_rise₁ δ 0 x)
    (fun x => hasDerivAt_rise₂ δ 0 x) hb₁ (fun x => (smoothstep_atom_bounds hδ _).2.1)
    (fun x => (smoothstep_atom_bounds hδ _).2.2.1) (fun x => (smoothstep_atom_bounds hδ _).2.2.2)
  have hL₂ := abs_integral_halfBlock_sub_gaussianReal_le hX (a := scaleCut (k₁ : ℝ))
    (b := scaleCut (k : ℝ)) hσ h (q := q) hm20
    (hasDerivAt_lindExp δ (-δ) t) (hasDerivAt_lindExp₁ δ (-δ) t) (hasDerivAt_lindExp₂ δ (-δ) t)
    hb₂ (fun x => (abs_lindExp_le hδ (-δ) ht x).2.1) (fun x => (abs_lindExp_le hδ (-δ) ht x).2.2.1)
    (fun x => (abs_lindExp_le hδ (-δ) ht x).2.2.2)
  -- the Gaussian values
  have hG₁ := normCDF_le_integral_smoothstep_gaussianReal hδ μ₀ hv0
  have hG₂ := integral_lindExp_gaussianReal_le hδ (-δ) ht μ₀ hv0
  rw [hv] at hG₁ hG₂
  rw [show μ₀ - -δ - t * V₀ = μ₀ + δ - t * V₀ by ring] at hG₂
  have h1 := abs_le.1 hL₁
  have h2 := abs_le.1 hL₂
  have hE0 : 0 ≤ 105 * Real.exp (-(Real.exp 20 / 2)) := by positivity
  have hFe := mul_le_mul_of_nonneg_left (show ∫ ω, lindExp δ (-δ) t (halfBlock X k₁ σ 0 m₀ ω) ∂P
      ≤ Real.exp (-(t * μ₀) + t ^ 2 * V₀ / 2) * normCDF ((μ₀ + δ - t * V₀) / √V₀)
        + lindM δ (-δ) t 3 * (105 * Real.exp (-(Real.exp 20 / 2))) by linarith [h2.2]) hF
  have hlin : lindebergErr δ t F = 105 / 2 / δ / δ / δ * (105 * Real.exp (-(Real.exp 20 / 2)))
      + F * (lindM δ (-δ) t 3 * (105 * Real.exp (-(Real.exp 20 / 2)))) := by
    rw [lindebergErr]
    ring
  rw [hlin]
  linarith [h1.1]

end TopStep

/-! ### The ranges of the top block's moments over a `ϑ`-cell

For `h = e^{-k-ϑ}`, `ϑ ∈ [ϑ_lo, ϑ_hi]`, the top block (scale `k - 1`) has phases
`h log p ∈ (e^{-1-ϑ}, e^{-ϑ}]` and deficit `S₀ - C₀(h) ≈ 1 - blockCos(-1-ϑ, 0)`.
`blockCos(·, 0)` is antitone below `log π - 1` and within `10⁻⁶` of `RMF.cosExpAnti`'s increment
there (Taylor's regime of `cos`), so the cell's endpoints bound it.  The damping
`p^{-2σ} ∈ [e^{-2η}, 1]` is paid relatively on the deficit, and the cosine sum's error at `σ = 0`
is `RMF.blockCosErr ≤ 7.43·10⁻⁸`. -/

/-- `blockCos(·, 0)` is antitone on `(-∞, log π - 1]`. -/
theorem blockCos_antitoneOn_Iic :
    AntitoneOn (fun ξ => blockCos ξ 0) (Set.Iic (Real.log Real.pi - 1)) := by
  intro ξ _ ξ' hξ' hle
  have h := blockCos_sub_eq ξ ξ' 0
  simp only [Nat.cast_zero, zero_add] at h
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v))
      MeasureTheory.volume ξ ξ' :=
    (by fun_prop : Continuous fun v : ℝ =>
      Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v)).intervalIntegrable _ _
  have hpt : ∀ v ∈ Set.Icc ξ ξ',
      Real.cos (Real.exp (v + 1)) - Real.cos (Real.exp v) ≤ (fun _ : ℝ => (0 : ℝ)) v := by
    intro v hv
    have hv1 : v + 1 ≤ Real.log Real.pi := by linarith [hv.2, Set.mem_Iic.1 hξ']
    have he : Real.exp (v + 1) ≤ Real.pi := by
      calc Real.exp (v + 1) ≤ Real.exp (Real.log Real.pi) := Real.exp_le_exp.2 hv1
        _ = Real.pi := Real.exp_log Real.pi_pos
    have := Real.cos_le_cos_of_nonneg_of_le_pi (Real.exp_pos v).le he
      (Real.exp_le_exp.2 (by linarith))
    simp only
    linarith
  have hmono := intervalIntegral.integral_mono_on hle hint intervalIntegrable_const hpt
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hmono
  change blockCos ξ' 0 ≤ blockCos ξ 0
  linarith

/-- The lower end of `blockCos(-1-ϑ, 0)` at the cell's `ϑ_lo`, by Taylor's antiderivative. -/
noncomputable def topBlo (ϑ : ℝ) : ℝ := cosExpAnti (-ϑ) - cosExpAnti (-1 - ϑ) - 1 / 10 ^ 6

/-- The upper end of `blockCos(-1-ϑ, 0)` at the cell's `ϑ_hi`. -/
noncomputable def topBhi (ϑ : ℝ) : ℝ := cosExpAnti (-ϑ) - cosExpAnti (-1 - ϑ) + 1 / 10 ^ 6

/-- **The top block's cosine integral over a cell**: for `ξ ∈ [-1-ϑ_hi, -1-ϑ_lo]`, `ϑ_lo ≥ 0`,
`topBlo ϑ_lo ≤ blockCos ξ 0 ≤ topBhi ϑ_hi`. -/
theorem blockCos_zero_mem_cell {ξ ϑ_lo ϑ_hi : ℝ} (hϑ : 0 ≤ ϑ_lo) (h1 : -1 - ϑ_hi ≤ ξ)
    (h2 : ξ ≤ -1 - ϑ_lo) : topBlo ϑ_lo ≤ blockCos ξ 0 ∧ blockCos ξ 0 ≤ topBhi ϑ_hi := by
  have hpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlo : -1 - ϑ_lo ∈ Set.Iic (Real.log Real.pi - 1) := by
    rw [Set.mem_Iic]
    linarith
  have hξ : ξ ∈ Set.Iic (Real.log Real.pi - 1) := by
    rw [Set.mem_Iic]
    linarith
  have hhi : -1 - ϑ_hi ∈ Set.Iic (Real.log Real.pi - 1) := by
    rw [Set.mem_Iic]
    linarith
  have hA := abs_le.1 (abs_blockCos_zero_sub_anti_le (c := -1 - ϑ_lo) (d := -ϑ_lo) (by ring)
    (by linarith))
  have hB := abs_le.1 (abs_blockCos_zero_sub_anti_le (c := -1 - ϑ_hi) (d := -ϑ_hi) (by ring)
    (by linarith))
  have hm1 : blockCos (-1 - ϑ_lo) 0 ≤ blockCos ξ 0 := blockCos_antitoneOn_Iic hξ hlo h2
  have hm2 : blockCos ξ 0 ≤ blockCos (-1 - ϑ_hi) 0 := blockCos_antitoneOn_Iic hhi hξ h1
  rw [topBlo, topBhi]
  constructor <;> linarith [hA.1, hB.2]

/-- `e^{-e^{20}/2} ≤ 10⁻⁴⁰` (`10⁸⁰ ≤ e^{e^{20}}`). -/
lemma exp_neg_exp_twenty_half_le : Real.exp (-(Real.exp 20 / 2)) ≤ 1 / 10 ^ 40 := by
  have h := pow_eighty_le_exp_exp_20
  have hsq : Real.exp (-(Real.exp 20 / 2)) ^ 2 ≤ (1 / 10 ^ 40) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -(Real.exp 20 / 2) = -Real.exp 20 by
      push_cast; ring, Real.exp_neg, show ((1 : ℝ) / 10 ^ 40) ^ 2 = 1 / 10 ^ 80 by norm_num,
      inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by positivity) two_ne_zero).1 hsq

/-- The top block's cubic remainder bound, `S_hi e^{-e^{20}/2}`. -/
noncomputable def topEps : ℝ := c3Shi * Real.exp (-(Real.exp 20 / 2))

/-- The upper end of the top block's deficit `S₀ - C₀(h)`. -/
noncomputable def topDhi (ϑ_lo : ℝ) : ℝ := c3Shi - topBlo ϑ_lo + 7.43 / 10 ^ 8

/-- The lower end of the top block's deficit, damped by `e^{-2η}`. -/
noncomputable def topDlo (η ϑ_hi : ℝ) : ℝ :=
  Real.exp (-(2 * η)) * ((1 - 1 / 150000) - topBhi ϑ_hi - 7.43 / 10 ^ 8)

/-- **The lower end of the top block's twisted mean** over the cell:
`min((2q_lo - ½)S_lo, (2q_lo - ½)S_hi) - 2·topDhi - 14ε₀`. -/
noncomputable def topMuLo (q η ϑ_lo : ℝ) : ℝ :=
  min ((2 * q - 1 / 2) * c3Slo η) ((2 * q - 1 / 2) * c3Shi) - 2 * topDhi ϑ_lo - 14 * topEps

/-- **The upper end of the top block's twisted mean** over the cell. -/
noncomputable def topMuHi (q η ϑ_hi : ℝ) : ℝ :=
  max ((2 * q - 1 / 2) * c3Slo η) ((2 * q - 1 / 2) * c3Shi) - 2 * topDlo η ϑ_hi + 14 * topEps

/-- The lower end of the top block's twisted variance, `S_lo - ε₀`. -/
noncomputable def topVLo (η : ℝ) : ℝ := c3Slo η - topEps

/-- The upper end of the top block's twisted variance, `S_hi + ε₀`. -/
noncomputable def topVHi : ℝ := c3Shi + topEps

lemma topVLo_pos {η : ℝ} (hη : η ≤ 1) : 0 < topVLo η := by
  have h1 := exp_neg_exp_twenty_half_le
  have h2 : Real.exp (-2) ≤ Real.exp (-(2 * η)) := Real.exp_le_exp.2 (by linarith)
  have h3 : (1 : ℝ) / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (Real.exp_pos 2) ?_
    have h := Real.exp_one_lt_d9
    have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  rw [topVLo, topEps, c3Slo, c3Shi]
  nlinarith [Real.exp_pos (-(Real.exp 20 / 2))]

section Ranges

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **Item 5: the top block's moments over a cell.**  For the ladder `[k₁, k)`, `k₁ ≥ 20`,
`σ ≥ 0`, `σe^k ≤ η`, `q ∈ [q_lo, q_hi] ⊆ [0, 1]`, `e^{-(k+ϑ_hi)} ≤ h ≤ e^{-(k+ϑ_lo)}`, `ϑ_lo ≥ 0`:
`E_tw Y₀ ∈ [topMuLo q_lo η ϑ_lo, topMuHi q_hi η ϑ_hi]` and `Var_tw Y₀ ∈ [topVLo η, topVHi]`. -/
theorem topBlock_moments_mem (hX : IsRademacherPrimeValues X μ) {k₁ k : ℕ} (hk₁ : 20 ≤ k₁)
    (hk : k₁ < k) {σ η : ℝ} (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ η) {q q_lo q_hi : ℝ}
    (hqlo : q_lo ≤ q) (hqhi : q ≤ q_hi) (hq0 : 0 ≤ q_lo) (hq1 : q_hi ≤ 1)
    {h ϑ_lo ϑ_hi : ℝ} (hϑ : 0 ≤ ϑ_lo) (hh1 : Real.exp (-((k : ℝ) + ϑ_hi)) ≤ h)
    (hh2 : h ≤ Real.exp (-((k : ℝ) + ϑ_lo))) :
    topMuLo q_lo η ϑ_lo
        ≤ twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
      ∧ twistBlockMean X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
        ≤ topMuHi q_hi η ϑ_hi
      ∧ topVLo η
        ≤ twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
      ∧ twistBlockVar X μ (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) σ h q k₁ (k - k₁ - 1)
        ≤ topVHi := by
  set m₀ := k - k₁ - 1
  have hmk : (m₀ : ℝ) + 1 + k₁ = k := by
    have : m₀ + 1 + k₁ = k := by omega
    exact_mod_cast this
  have hk₁' : (20 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
  have hm20 : 20 ≤ (m₀ : ℝ) + k₁ := by linarith [Nat.cast_nonneg (α := ℝ) m₀]
  have hB : primeBlockSub (k₁ : ℝ) m₀ ⊆ primesIcoSub (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) :=
    primeBlockSub_subset_primesIcoSub_scaleCut (by omega)
  have hq0' : 0 ≤ q := by linarith
  have hq1' : q ≤ 1 := by linarith
  have hh0 : 0 < h := (Real.exp_pos _).trans_le hh1
  -- the block data
  set S := blockRpowSum (k₁ : ℝ) σ m₀
  set C := blockCosSum (k₁ : ℝ) σ h m₀
  set E₀ := ∑ p ∈ primeBlockSub (k₁ : ℝ) m₀, twistU σ p ^ 3
  have hη : σ * Real.exp ((m₀ : ℝ) + 1 + k₁) ≤ η := by rw [hmk]; exact hση
  obtain ⟨hSlo, hShi⟩ := blockRpowSum_bounds_of_mul_exp_le (by linarith) hσ hη
  have hE : E₀ ≤ topEps := by
    have h1 := sum_twistU_cube_le (θ := (k₁ : ℝ)) hσ m₀
    have h2 : Real.exp (-(Real.exp ((m₀ : ℝ) + k₁) / 2)) ≤ Real.exp (-(Real.exp 20 / 2)) :=
      Real.exp_le_exp.2 (by linarith [Real.exp_le_exp.2 hm20])
    have hS0 := blockRpowSum_nonneg (k₁ : ℝ) σ m₀
    refine h1.trans ?_
    rw [topEps, mul_comm c3Shi]
    exact mul_le_mul h2 hShi hS0 (Real.exp_pos _).le
  have hmean := abs_le.1 (abs_twistBlockMean_sub_le hX hσ h hq0' hq1' hm20 hB)
  have hvar := abs_le.1 (abs_twistBlockVar_sub_le hX hσ h hq0' hq1' hm20 hB)
  -- the deficit `S - C(h)`, against its undamped value
  obtain ⟨hDlo, hDhi⟩ := blockRpowSum_sub_blockCosSum_bounds_zero (θ := (k₁ : ℝ)) (h := h) hσ m₀
  have hU0 : 0 ≤ blockRpowSum (k₁ : ℝ) 0 m₀ - blockCosSum (k₁ : ℝ) 0 h m₀ :=
    sub_nonneg.2 (abs_le.1 (abs_blockCosSum_le_blockRpowSum (k₁ : ℝ) 0 h m₀)).2
  obtain ⟨hS0lo, hS0hi⟩ := blockRpowSum_bounds_of_mul_exp_le (θ := (k₁ : ℝ)) (σ := 0) (η := 0)
    (m := m₀) (by linarith) le_rfl (by simp)
  have hh2' : h ≤ 2 * Real.exp (-20) := by
    have : Real.exp (-((k : ℝ) + ϑ_lo)) ≤ Real.exp (-20) := by
      refine Real.exp_le_exp.2 ?_
      have : (20 : ℝ) < k := by exact_mod_cast (show 20 < k by omega)
      linarith
    linarith [Real.exp_pos (-20)]
  have hcos := abs_le.1 (abs_blockCosSum_sub_blockCos_le (k := k₁) (m := m₀) (σ := 0) (δ := 0)
    le_rfl hh0 (by simp))
  have herr := blockCosErr_le_numeral (θ := (k₁ : ℝ)) (m := m₀) hm20 hh2'
  -- the cell bounds on `blockCos`
  have hξ : blockCos (Real.log h + k₁) m₀ = blockCos (Real.log h + k - 1) 0 := by
    rw [blockCos_eq_zero]
    congr 1
    linarith
  have hlog1 : -((k : ℝ) + ϑ_hi) ≤ Real.log h := by
    have := Real.log_le_log (Real.exp_pos _) hh1
    rwa [Real.log_exp] at this
  have hlog2 : Real.log h ≤ -((k : ℝ) + ϑ_lo) := by
    have := Real.log_le_log hh0 hh2
    rwa [Real.log_exp] at this
  obtain ⟨hBlo, hBhi⟩ := blockCos_zero_mem_cell (ξ := Real.log h + k - 1) (ϑ_hi := ϑ_hi) hϑ
    (by linarith) (by linarith)
  rw [hξ] at hcos
  have hdamp : Real.exp (-(2 * η)) ≤ Real.exp (-(2 * σ * Real.exp ((m₀ : ℝ) + 1 + k₁))) :=
    Real.exp_le_exp.2 (by linarith)
  -- the deficit's two ends
  have hDup : S - C ≤ topDhi ϑ_lo := by
    rw [topDhi]
    have := blockRpowSum_le (θ := (k₁ : ℝ)) (σ := 0) (m := m₀) le_rfl (by linarith)
    rw [c3Shi]
    linarith [hcos.1]
  have hDdown : topDlo η ϑ_hi ≤ S - C := by
    rw [topDlo]
    have hU : (1 - 1 / 150000) - topBhi ϑ_hi - 7.43 / 10 ^ 8
        ≤ blockRpowSum (k₁ : ℝ) 0 m₀ - blockCosSum (k₁ : ℝ) 0 h m₀ := by
      rw [show Real.exp (-(2 * (0 : ℝ))) = 1 by simp] at hS0lo
      linarith [hcos.2]
    calc Real.exp (-(2 * η)) * ((1 - 1 / 150000) - topBhi ϑ_hi - 7.43 / 10 ^ 8)
        ≤ Real.exp (-(2 * η)) * (blockRpowSum (k₁ : ℝ) 0 m₀ - blockCosSum (k₁ : ℝ) 0 h m₀) :=
          mul_le_mul_of_nonneg_left hU (Real.exp_pos _).le
      _ ≤ Real.exp (-(2 * σ * Real.exp ((m₀ : ℝ) + 1 + k₁)))
            * (blockRpowSum (k₁ : ℝ) 0 m₀ - blockCosSum (k₁ : ℝ) 0 h m₀) :=
          mul_le_mul_of_nonneg_right hdamp hU0
      _ ≤ S - C := hDlo
  -- the `q`-dependence
  have hqS1 : min ((2 * q_lo - 1 / 2) * c3Slo η) ((2 * q_lo - 1 / 2) * c3Shi)
      ≤ (2 * q - 1 / 2) * S := by
    have h1 : (2 * q_lo - 1 / 2) * S ≤ (2 * q - 1 / 2) * S :=
      mul_le_mul_of_nonneg_right (by linarith) (blockRpowSum_nonneg _ _ _)
    refine le_trans ?_ h1
    rcases le_total 0 (2 * q_lo - 1 / 2) with hs | hs
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hSlo hs)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hShi hs)
  have hqS2 : (2 * q - 1 / 2) * S
      ≤ max ((2 * q_hi - 1 / 2) * c3Slo η) ((2 * q_hi - 1 / 2) * c3Shi) := by
    have h1 : (2 * q - 1 / 2) * S ≤ (2 * q_hi - 1 / 2) * S :=
      mul_le_mul_of_nonneg_right (by linarith) (blockRpowSum_nonneg _ _ _)
    refine h1.trans ?_
    rcases le_total 0 (2 * q_hi - 1 / 2) with hs | hs
    · exact (mul_le_mul_of_nonneg_left hShi hs).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hSlo hs).trans (le_max_left _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [topMuLo]
    linarith [hmean.1]
  · rw [topMuHi]
    linarith [hmean.2]
  · rw [topVLo, c3Slo]
    linarith [hvar.1]
  · rw [topVHi, c3Shi]
    linarith [hvar.2]

end Ranges

/-! ### The assembled statement (item 6)

The Gaussian value of the top step, `Φ((μ₀ - δ)/√V₀) - Fe^{-tμ₀+t²V₀/2}Φ((μ₀ + δ - tV₀)/√V₀)`,
is bounded below over the cell's ranges of `(μ₀, V₀)`: `x/√V` is monotone in `V` one way or the
other, so the two ends of `[V_lo, V_hi]` bound it. -/

/-- `Φ(x/√V)` between its values at the ends of `[V_lo, V_hi]`, `V_lo > 0`. -/
lemma normCDF_div_sqrt_bounds {x V Vlo Vhi : ℝ} (h0 : 0 < Vlo) (h1 : Vlo ≤ V) (h2 : V ≤ Vhi) :
    min (normCDF (x / √Vlo)) (normCDF (x / √Vhi)) ≤ normCDF (x / √V)
      ∧ normCDF (x / √V) ≤ max (normCDF (x / √Vlo)) (normCDF (x / √Vhi)) := by
  have hl : 0 < √Vlo := Real.sqrt_pos.2 h0
  have hs1 : √Vlo ≤ √V := Real.sqrt_le_sqrt h1
  have hs2 : √V ≤ √Vhi := Real.sqrt_le_sqrt h2
  have hv : 0 < √V := hl.trans_le hs1
  rcases le_total 0 x with hx | hx
  · have ha : x / √Vhi ≤ x / √V := div_le_div_of_nonneg_left hx hv hs2
    have hb : x / √V ≤ x / √Vlo := div_le_div_of_nonneg_left hx hl hs1
    exact ⟨(min_le_right _ _).trans (normCDF_mono ha), (normCDF_mono hb).trans (le_max_left _ _)⟩
  · have ha : (-x) / √Vhi ≤ (-x) / √V := div_le_div_of_nonneg_left (by linarith) hv hs2
    have hb : (-x) / √V ≤ (-x) / √Vlo := div_le_div_of_nonneg_left (by linarith) hl hs1
    rw [neg_div, neg_div] at ha hb
    exact ⟨(min_le_left _ _).trans (normCDF_mono (by linarith)),
      (normCDF_mono (by linarith)).trans (le_max_right _ _)⟩

/-- **`c₃`, explicit** (its numerals are in `RMF/UniformLower/C3Numerals.lean`): the top step's
Gaussian value at the cell's worst corner,
`min_V Φ((μ_lo - δ)/√V) - F e^{-tμ_lo + t²V_hi/2} max_V Φ((μ_hi + δ - tV_lo)/√V)`, less the
Lindeberg error; `μ_lo = topMuLo q_lo η ϑ_lo`, `μ_hi = topMuHi q_hi η ϑ_hi`,
`V ∈ {topVLo η, topVHi}`. -/
noncomputable def c3Val (q_lo q_hi η ϑ_lo ϑ_hi t δ F : ℝ) : ℝ :=
  min (normCDF ((topMuLo q_lo η ϑ_lo - δ) / √(topVLo η)))
      (normCDF ((topMuLo q_lo η ϑ_lo - δ) / √topVHi))
    - F * (Real.exp (-(t * topMuLo q_lo η ϑ_lo) + t ^ 2 * topVHi / 2)
      * max (normCDF ((topMuHi q_hi η ϑ_hi + δ - t * topVLo η) / √(topVLo η)))
          (normCDF ((topMuHi q_hi η ϑ_hi + δ - t * topVLo η) / √topVHi)))
    - lindebergErr δ t F

/-- `c3Val` is below the top step's Gaussian value at any `(μ₀, V₀)` in the cell's ranges. -/
lemma c3Val_le {q_lo q_hi η ϑ_lo ϑ_hi t δ F μ₀ V₀ : ℝ} (hη : η ≤ 1) (ht : 0 ≤ t) (hF : 0 ≤ F)
    (hμ1 : topMuLo q_lo η ϑ_lo ≤ μ₀) (hμ2 : μ₀ ≤ topMuHi q_hi η ϑ_hi) (hV1 : topVLo η ≤ V₀)
    (hV2 : V₀ ≤ topVHi) :
    c3Val q_lo q_hi η ϑ_lo ϑ_hi t δ F
      ≤ normCDF ((μ₀ - δ) / √V₀)
        - F * (Real.exp (-(t * μ₀) + t ^ 2 * V₀ / 2) * normCDF ((μ₀ + δ - t * V₀) / √V₀))
        - lindebergErr δ t F := by
  have hVlo := topVLo_pos hη
  have hV0 : 0 < √V₀ := Real.sqrt_pos.2 (hVlo.trans_le hV1)
  obtain ⟨hA, -⟩ := normCDF_div_sqrt_bounds (x := topMuLo q_lo η ϑ_lo - δ) hVlo hV1 hV2
  obtain ⟨-, hB⟩ := normCDF_div_sqrt_bounds (x := topMuHi q_hi η ϑ_hi + δ - t * topVLo η) hVlo
    hV1 hV2
  have h1 : normCDF ((topMuLo q_lo η ϑ_lo - δ) / √V₀) ≤ normCDF ((μ₀ - δ) / √V₀) :=
    normCDF_mono (div_le_div_of_nonneg_right (by linarith) hV0.le)
  have h2 : normCDF ((μ₀ + δ - t * V₀) / √V₀)
      ≤ normCDF ((topMuHi q_hi η ϑ_hi + δ - t * topVLo η) / √V₀) :=
    normCDF_mono (div_le_div_of_nonneg_right (by nlinarith) hV0.le)
  have h3 : Real.exp (-(t * μ₀) + t ^ 2 * V₀ / 2)
      ≤ Real.exp (-(t * topMuLo q_lo η ϑ_lo) + t ^ 2 * topVHi / 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h4 : Real.exp (-(t * μ₀) + t ^ 2 * V₀ / 2) * normCDF ((μ₀ + δ - t * V₀) / √V₀)
      ≤ Real.exp (-(t * topMuLo q_lo η ϑ_lo) + t ^ 2 * topVHi / 2)
        * max (normCDF ((topMuHi q_hi η ϑ_hi + δ - t * topVLo η) / √(topVLo η)))
          (normCDF ((topMuHi q_hi η ϑ_hi + δ - t * topVLo η) / √topVHi)) :=
    mul_le_mul h3 (h2.trans hB) (normCDF_nonneg _) (Real.exp_pos _).le
  rw [c3Val]
  have h5 := mul_le_mul_of_nonneg_left h4 hF
  linarith

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℂ} {μ : Measure Ω}

/-- **(C3)* at `m = 1`, explicit (item 6).**  For the ladder `[k₁, k)` with `k₁ ≥ 20`, `k₁ < k`,
`a ≤ scaleCut k₁`, `σ ≥ 0`, `σe^k ≤ η ≤ 1`, `q ∈ [q_lo, q_hi] ⊆ [0, 1]`, `t ≥ 0`, `δ > 0`, a
cell `e^{-(k+ϑ_hi)} ≤ h ≤ e^{-(k+ϑ_lo)}` (`ϑ_lo ≥ 0`; `[0, 1]` is `RMF.halfWindow k`) and any
`F ≥ RMF.villeFactor q_lo t η e^{-ϑ_lo} (k - k₁)`:
`c3Val·E‖F_{[a,k)}(σ)‖^{2q} ≤ E[1_{halfLadder X σ k₁ k}‖F_{[a,k)}(s_h)‖²‖F_{[a,k)}(σ)‖^{2q-2}]`. -/
theorem le_setIntegral_halfLadder_twistQ_explicit (hX : IsRademacherPrimeValues X μ)
    {a k₁ k : ℕ} (ha : a ≤ scaleCut (k₁ : ℝ)) (hk₁ : 20 ≤ k₁) (hk : k₁ < k) {σ η : ℝ}
    (hσ : 0 ≤ σ) (hση : σ * Real.exp k ≤ η) (hη : η ≤ 1) {q q_lo q_hi : ℝ} (hqlo : q_lo ≤ q)
    (hqhi : q ≤ q_hi) (hq0 : 0 ≤ q_lo) (hq1 : q_hi ≤ 1) {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ)
    {h ϑ_lo ϑ_hi : ℝ} (hϑ : 0 ≤ ϑ_lo) (hh1 : Real.exp (-((k : ℝ) + ϑ_hi)) ≤ h)
    (hh2 : h ≤ Real.exp (-((k : ℝ) + ϑ_lo))) {F : ℝ}
    (hF : villeFactor q_lo t η (Real.exp (-ϑ_lo)) (k - k₁) ≤ F) :
    c3Val q_lo q_hi η ϑ_lo ϑ_hi t δ F
        * ∫ ω, ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
            (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q) ∂μ
      ≤ ∫ ω in halfLadder X σ k₁ k,
          ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ h) ω‖ ^ 2
            * ‖randomEulerProductIco (fun ω => squarefreeExtension fun p => X p ω) a
              (scaleCut (k : ℝ)) (shiftLine σ 0) ω‖ ^ (2 * q - 2) ∂μ := by
  haveI := isProbabilityMeasure_twistMeasure hX (scaleCut (k₁ : ℝ)) (scaleCut (k : ℝ)) hσ h q
  have hq0' : 0 ≤ q := by linarith
  have hq1' : q ≤ 1 := by linarith
  have hh0 : 0 < h := (Real.exp_pos _).trans_le hh1
  have hhk : h ≤ Real.exp (-(k : ℝ)) := hh2.trans (Real.exp_le_exp.2 (by linarith))
  have hy0 : 0 ≤ h * Real.exp k := by positivity
  have hy : h * Real.exp k ≤ Real.exp (-ϑ_lo) := by
    calc h * Real.exp k ≤ Real.exp (-((k : ℝ) + ϑ_lo)) * Real.exp k :=
          mul_le_mul_of_nonneg_right hh2 (Real.exp_pos _).le
      _ = Real.exp (-ϑ_lo) := by rw [← Real.exp_add]; ring_nf
  have hF0 : 0 ≤ F := (Real.exp_pos _).le.trans hF
  have hYm : ∀ i, Measurable (halfLadderStep X σ k₁ k i) :=
    fun i => measurable_halfBlock hX _ σ 0 _
  refine le_setIntegral_halfLadder_twistQ_ville_of_le hX ha hk (m := 1) (by omega) hσ hq1' ht
    (f := fun i => Real.exp (max 0 (c3Step q t η (h * Real.exp k) i)
      + (14 * t + t ^ 2 / 2) * (c3Shi * Real.exp (-(Real.exp 20 / 2)))
        * Real.exp (-1) ^ (k - k₁ - 1 - i)))
    (fun i _ hi => integral_exp_neg_mul_halfLadderStep_le hX hk₁ hσ hση hh0 hhk hq0' hq1' ht hi)
    ?_
  -- the Ville factor
  have hprod := (prod_max_one_stepBound_le (k₁ := k₁) (k := k) (q := q) (η := η)
    (y := h * Real.exp k) ht).trans
    ((villeFactor_le_of_le (K := k - k₁) ht hqlo hy0 hy le_rfl).trans hF)
  -- the top step and its ranges
  obtain ⟨hμ1, hμ2, hV1, hV2⟩ := topBlock_moments_mem hX hk₁ hk hσ hση hqlo hqhi hq0 hq1 hϑ hh1
    hh2
  have htop := le_setIntegral_ladderEvent_one hX hk₁ hk hσ h q ht hδ hF0
    ((topVLo_pos hη).trans_le hV1)
  refine (c3Val_le hη ht hF0 hμ1 hμ2 hV1 hV2).trans (htop.trans ?_)
  exact setIntegral_mono_on (integrableOn_ladderEvent_one_sub_mul_exp hYm ht _ 1)
    (integrableOn_ladderEvent_one_sub_mul_exp hYm ht _ 1) (measurableSet_ladderEvent hYm 1)
    fun ω _ => sub_le_sub_left (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) 1

end Assembly

end RMF
