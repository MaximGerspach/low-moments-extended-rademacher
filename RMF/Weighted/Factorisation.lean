/-
Copyright (c) 2026 Christopher Atherfold, Maxim Gerspach, Jad Hamdan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Atherfold, Maxim Gerspach, Jad Hamdan
-/
import RMF.Weighted.Defs
import RMF.Weighted.Conditional

/-!
# The factorisation, for the range `½ < q < 1`

With `B_y(x) = ∑_{r ≤ x, r y-rough} X(r)/√r` (`RMF.roughWeightedRademacherSum`, which includes
`r = 1`) and

`T_y(x) = ∑_{n > x, r_y(n) ≤ x} X(n)/√n`,

the factorisation is `S(x) = F_y(½)·B_y(x) − T_y(x)`, and one level in
`B_y(x) = F_{y,z}(½)·B_z(x) − T_{y,z}(x)`.

The two are the same statement, so the combinatorics are carried once, by
`RMF.sum_blockSmooth_mul_sum_rough`: split the `y`-rough numbers at `z`.  The first identity is
its case `y = 0`, where every integer is `y`-rough.

## Why it is true, and what carries it

`F_y(½)·B_y(x)` is the sum of `X(n)/√n` over **all** `n` with `r_y(n) ≤ x` — the smooth factor is
unconstrained, which is exactly what distinguishes this from `RMF.sum_Icc_eq_sum_rough_smooth`,
where both factors are constrained by `n ≤ x`.  Since `n ≤ x` forces `r_y(n) ≤ n ≤ x`, the range
`{n ≤ x}` sits inside `{r_y(n) ≤ x}` and the difference is exactly the `n > x` part, i.e. `T_y(x)`.

The bijection is `n ↦ (roughPart y n, smoothPart y n)` with inverse `(r,m) ↦ r·m`
(`RMF.rough_smooth_unique`), and the two factors are coprime, so ordinary multiplicativity of the
squarefree extension suffices.

## The index set of `T_y(x)`

Written as a `Finset`, over `n ≤ primorial y · ⌊x⌋₊`: a squarefree `n` with `r_y(n) ≤ x` has
`n = r_y(n)·s_y(n)` with `s_y(n)` dividing `primorial y`.  The `Squarefree n` filter is what makes
that bound valid; it costs nothing here, since the Rademacher RMF vanishes off the squarefrees.
-/

open Finset

namespace RMF

variable {Ω : Type*}

/-! ### The block `[1, y)` is the whole range below `y` -/

/-- The primes in `[1, y)` are the primes below `y`: `1` is not prime. -/
lemma primesIco_one (y : ℕ) : primesIco 1 y = Nat.primesBelow y := by
  ext p
  simp only [mem_primesIco, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, -, hlt⟩
    exact ⟨hlt, hp⟩
  · rintro ⟨hlt, hp⟩
    exact ⟨hp, hp.one_lt.le, hlt⟩

/-- The random Euler product over the block `[1, y)` is the one over the primes below `y`. -/
lemma randomEulerProductIco_one (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (s : ℂ) (ω : Ω) :
    randomEulerProductIco f 1 y s ω = randomEulerProduct f y s ω := by
  rw [randomEulerProductIco, eulerProductIco, primesIco_one, randomEulerProduct, eulerProduct]

/-- `T_y(x) = ∑ X(n)/√n` over the squarefree `n > x` with `r_y(n) ≤ x`, the truncation tail of
the factorisation.  Such `n` are at most `y#·⌊x⌋`, the range written; for squarefree-supported
`f`, as at every use, the `Squarefree` filter restricts nothing. -/
noncomputable def truncationTail (f : Ω → ArithmeticFunction ℂ) (y : ℕ) (x : ℝ) (ω : Ω) : ℂ :=
  ∑ n ∈ {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
      ⌊x⌋₊ < n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n}, f ω n / (Real.sqrt n : ℂ)

/-- **The combinatorial core of the factorisation.**  For `g` supported on the squarefrees and
multiplicative on coprime arguments, `(∑ g(k))·(∑ g(r))` over the `z`-smooth `y`-rough `k ≤ z#`
and the `z`-rough `r ≤ x` is `∑_{n ≤ x, n y-rough} g(n)` plus the sum over the squarefree
`y`-rough `x < n ≤ z#·⌊x⌋` with `r_z(n) ≤ x`.  `hyz` makes a `z`-rough number `y`-rough (at
`y = 3`, `z = 2` the identity would read `B_3(x) = B_2(x)`); the `Squarefree` filter makes the
range `z#·⌊x⌋` correct and `hg0` makes dropping the other `n` free; nothing is assumed on `x`. -/
theorem sum_blockSmooth_mul_sum_rough {g : ℕ → ℂ} {y z : ℕ} (hyz : y ≤ z) (x : ℝ)
    (hg0 : ∀ n : ℕ, ¬ Squarefree n → g n = 0)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
    (∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
        k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k}, g k)
        * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r}, g r
      = (∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n}, g n)
        + ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
            ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n := by
  -- the one use of `y ≤ z`: a `z`-rough number is `y`-rough
  have hmono : ∀ n : ℕ, IsRough z n → IsRough y n := fun n hn =>
    isRough_iff.2 fun p hp hpd => lt_of_le_of_lt hyz (isRough_iff.1 hn p hp hpd)
  -- the block-smooth sum may be restricted to squarefree indices
  have hsm : ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
        k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k}, g k
      = ∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
          k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k}, g k := by
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · rw [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.1, hk.2.2.1⟩
    · rw [Finset.mem_filter] at hk hk'
      exact hg0 k fun hsf => hk' ⟨hk.1, hk.2.1, hk.2.2, hsf⟩
  -- and so may the rough sum
  have hrg : ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}, g r
      = ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r}, g r := by
    refine Finset.sum_subset (fun r hr => ?_) (fun r hr hr' => ?_)
    · rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, hr.2.1⟩
    · rw [Finset.mem_filter] at hr hr'
      exact hg0 r fun hsf => hr' ⟨hr.1, hr.2, hsf⟩
  -- and so may the `y`-rough sum over `[1, x]`
  have hall : ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}, g n
      = ∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n}, g n := by
    refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
    · rw [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.1⟩
    · rw [Finset.mem_filter] at hn hn'
      exact hg0 n fun hsf => hn' ⟨hn.1, hn.2, hsf⟩
  -- the product is the sum over the `y`-rough squarefree `n` with `r_z(n) ≤ x`
  have hbij : (∑ k ∈ {k ∈ Finset.Icc 1 (primorial z) |
        k ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y k ∧ Squarefree k}, g k)
      * (∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough z r ∧ Squarefree r}, g r)
      = ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
          IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_nbij' (fun p => p.1 * p.2) (fun n => (smoothPart z n, roughPart z n))
      ?_ ?_ ?_ ?_ ?_
    · -- the product of a block-smooth and a `z`-rough factor lands in the range
      rintro ⟨k, r⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hk1, hk2⟩, hks, hky, hksf⟩, ⟨hr1, hr2⟩, hrr, hrsf⟩ := hp
      have hcop : Nat.Coprime r k := hrr.coprime_of_mem_smoothNumbers hks
      obtain ⟨hrp, -⟩ := roughPart_smoothPart_mul hrr hks hr1
      change k * r ∈ _
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul hk2 hr2⟩, isRough_mul_iff.2 ⟨hky, hmono r hrr⟩, ?_,
        Nat.squarefree_mul_iff.2 ⟨hcop.symm, hksf, hrsf⟩⟩
      rw [mul_comm k r, hrp]
      exact hr2
    · -- and conversely the two parts land in the two ranges
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, -⟩, hny, hnr, hnsf⟩ := hn
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn1
      have hssf : Squarefree (smoothPart z n) := hnsf.squarefree_of_dvd (smoothPart_dvd z hn0)
      have hrsf : Squarefree (roughPart z n) := hnsf.squarefree_of_dvd (roughPart_dvd z hn0)
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨smoothPart_pos z n, Nat.le_of_dvd (primorial_pos z)
          (dvd_primorial_of_squarefree_of_mem_smoothNumbers hssf
            (smoothPart_mem_smoothNumbers z n))⟩, smoothPart_mem_smoothNumbers z n,
          hny.of_dvd (smoothPart_dvd z hn0), hssf⟩,
        ⟨roughPart_pos z n, hnr⟩, isRough_roughPart z n, hrsf⟩
    · -- the two parts of a product are its two factors
      rintro ⟨k, r⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨-, hks, -⟩, ⟨hr1, -⟩, hrr, -⟩ := hp
      obtain ⟨hrp, hsp⟩ := roughPart_smoothPart_mul hrr hks hr1
      change (smoothPart z (k * r), roughPart z (k * r)) = (k, r)
      rw [mul_comm k r, hrp, hsp]
    · -- and a number is the product of its two parts
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      change smoothPart z n * roughPart z n = n
      rw [mul_comm]
      exact roughPart_mul_smoothPart z (Nat.one_le_iff_ne_zero.1 hn.1.1)
    · -- multiplicativity on the coprime pair
      rintro ⟨k, r⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨-, hks, -⟩, -, hrr, -⟩ := hp
      change g k * g r = g (k * r)
      exact (hgmul k r (hrr.coprime_of_mem_smoothNumbers hks).symm).symm
  -- and that sum splits at `x`
  have hsplit : ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
        IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n
      = (∑ n ∈ {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y n ∧ Squarefree n}, g n)
        + ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
            ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n := by
    rw [← Finset.sum_filter_add_sum_filter_not
      {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
        IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n} (fun n => n ≤ ⌊x⌋₊) g]
    refine congrArg₂ (· + ·) (Finset.sum_congr (Finset.ext fun n => ?_) fun _ _ => rfl)
      (Finset.sum_congr (Finset.ext fun n => ?_) fun _ _ => rfl)
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hn1, -⟩, hny, -, hsf⟩, hle⟩
        exact ⟨⟨hn1, hle⟩, hny, hsf⟩
      · rintro ⟨⟨hn1, hle⟩, hny, hsf⟩
        have hpx : ⌊x⌋₊ ≤ primorial z * ⌊x⌋₊ := by
          have h1 : 1 * ⌊x⌋₊ ≤ primorial z * ⌊x⌋₊ := Nat.mul_le_mul (primorial_pos z) le_rfl
          omega
        have hrp : roughPart z n ≤ n :=
          Nat.le_of_dvd hn1 (roughPart_dvd z (Nat.one_le_iff_ne_zero.1 hn1))
        exact ⟨⟨⟨hn1, le_trans hle hpx⟩, hny, le_trans hrp hle, hsf⟩, hle⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc, not_le]
      tauto
  rw [← hsm, ← hrg, hbij, hsplit, hall]

/-- **The combinatorial core of the factorisation, absolute form.**  The case `y = 0` of
`RMF.sum_blockSmooth_mul_sum_rough`, every integer being `0`-rough: the smooth sum over *all*
squarefree `y`-smooth numbers (equivalently, over `[1, y#]`) times the rough sum over `[1, x]`
is the sum over `{r_y(n) ≤ x}`, which splits at `x` into `∑_{n ≤ x}` and the tail. -/
theorem sum_smooth_mul_sum_rough {g : ℕ → ℂ} (y : ℕ) (x : ℝ)
    (hg0 : ∀ n : ℕ, ¬ Squarefree n → g n = 0)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
    (∑ k ∈ {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)}, g k)
        * ∑ r ∈ {r ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough y r}, g r
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, g n)
        + ∑ n ∈ {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
            ⌊x⌋₊ < n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n}, g n := by
  have h0 : ∀ n : ℕ, IsRough 0 n := fun n => isRough_iff.2 fun p hp _ => hp.pos
  have hA : {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1) ∧ IsRough 0 k}
      = {k ∈ Finset.Icc 1 (primorial y) | k ∈ Nat.smoothNumbers (y + 1)} :=
    Finset.filter_congr fun k _ => by simp [h0 k]
  have hB : {n ∈ Finset.Icc 1 ⌊x⌋₊ | IsRough 0 n} = Finset.Icc 1 ⌊x⌋₊ :=
    Finset.filter_true_of_mem fun n _ => h0 n
  have hC : {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ IsRough 0 n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n}
      = {n ∈ Finset.Icc 1 (primorial y * ⌊x⌋₊) |
        ⌊x⌋₊ < n ∧ roughPart y n ≤ ⌊x⌋₊ ∧ Squarefree n} :=
    Finset.filter_congr fun n _ => by simp [h0 n]
  have key := sum_blockSmooth_mul_sum_rough (g := g) (y := 0) (z := y) (Nat.zero_le y) x hg0 hgmul
  rw [hA, hB, hC] at key
  exact key

/-- **The factorisation, first identity.**  `S(x) = F_y(½)·B_y(x) − T_y(x)`.  No hypothesis on
`x`: for `x < 1` the three sums `S`, `B` and `T` are empty. -/
theorem weightedRademacherSum_eq_mul_sub_truncationTail {X : ℕ → Ω → ℂ} (y : ℕ) (x : ℝ)
    (ω : Ω) :
    weightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) x ω
      = randomEulerProduct (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (1 / 2) ω
            * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω
          - truncationTail (fun ω => squarefreeExtension fun p => X p ω) y x ω := by
  rw [eq_sub_iff_add_eq,
    ← smoothWeightedSum_eq_randomEulerProduct y (le_refl (primorial y : ℝ)) ω]
  simp only [weightedRademacherSum, truncationTail, smoothWeightedSum,
    roughWeightedRademacherSum, Nat.floor_natCast]
  refine (sum_smooth_mul_sum_rough y x (fun n hn => ?_) fun m n hmn => ?_).symm
  · rw [squarefreeExtension_apply_of_not_squarefree _ hn, zero_div]
  · rw [(isMultiplicative_squarefreeExtension _).map_mul_of_coprime hmn, div_mul_div_comm,
      Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]

/-! ### The nested identity

The second identity, `B_y(x) = F_{y,z}(½)·B_z(x) − T_{y,z}(x)`, is the same statement one
level in: a `y`-rough `n` factors uniquely as `m·r` with `m` composed of primes in `(y,z]` and `r`
`z`-rough, so `F_{y,z}(½)·B_z(x)` runs over all `y`-rough `n` with `r_z(n) ≤ x`, and `n ≤ x` forces
`r_z(n) ≤ n ≤ x`.  `F_{y,z}(½)` is `randomEulerProductIco … (y+1) (z+1)`, the product over
`primesIco (y+1) (z+1)`, i.e. exactly the primes `y < p ≤ z`.

Here `m ∣ primorial z`, so the tail's index bound is `primorial z · ⌊x⌋₊`.

The combinatorics are `RMF.sum_blockSmooth_mul_sum_rough`, stated at this generality; the smooth
factor is `RMF.sum_blockWeighted_eq_randomEulerProductIco`, which turns `F_{y,z}(½)` into the
finite sum over the block through the powerset transport
`RMF.sum_blockSquarefree_eq_sum_powerset`. -/

/-- `T_{y,z}(x) = ∑ X(n)/√n` over the squarefree `y`-rough `n > x` with `r_z(n) ≤ x`, the block
truncation tail.  Such `n` are at most `z#·⌊x⌋`, the range written; for squarefree-supported `f`,
as at every use, the `Squarefree` filter restricts nothing. -/
noncomputable def blockTruncationTail (f : Ω → ArithmeticFunction ℂ) (y z : ℕ) (x : ℝ) (ω : Ω) :
    ℂ :=
  ∑ n ∈ {n ∈ Finset.Icc 1 (primorial z * ⌊x⌋₊) |
      ⌊x⌋₊ < n ∧ IsRough y n ∧ roughPart z n ≤ ⌊x⌋₊ ∧ Squarefree n}, f ω n / (Real.sqrt n : ℂ)

/-- **The squarefree numbers composed of primes in `(y, z]` are the subset products of the
block.**  A squarefree `m` is `z`-smooth and `y`-rough exactly when every prime dividing it lies
in `RMF.primesIco (y+1) (z+1)`, so a sum over that range, of any summand, is a sum over the
powerset of the block, via `m ↦ m.primeFactors` and `t ↦ ∏ p ∈ t, p`.  The case `y = 0` is the
whole smooth range. -/
theorem sum_blockSquarefree_eq_sum_powerset {M : Type*} [AddCommMonoid M] (y z : ℕ) (f : ℕ → M) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
        m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m}, f m
      = ∑ t ∈ (primesIco (y + 1) (z + 1)).powerset, f (∏ p ∈ t, p) := by
  have hprim : primorial z = ∏ p ∈ Nat.primesBelow (z + 1), p := primorial_eq_prod_primesLE z
  refine Finset.sum_nbij' (i := fun m => m.primeFactors) (j := fun t => ∏ p ∈ t, p)
    (fun m hm => ?_) (fun t ht => ?_) (fun m hm => ?_) (fun t ht => ?_) (fun m hm => ?_)
  · -- the prime factors of a squarefree `z`-smooth `y`-rough number lie in the block
    obtain ⟨-, hsm, hro, -⟩ := Finset.mem_filter.1 hm
    refine Finset.mem_powerset.2 fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    exact mem_primesIco.2 ⟨hpp, isRough_iff.1 hro p hpp hpd,
      Nat.lt_succ_of_le (mem_smoothNumbers_succ_iff.1 hsm p hpp hpd)⟩
  · -- and conversely a subset product of the block lands in the range
    have hsub : t ⊆ primesIco (y + 1) (z + 1) := Finset.mem_powerset.1 ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => prime_of_mem_primesIco (hsub hp)
    have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos fun p hp => (hprime p hp).pos
    have hsubB : t ⊆ Nat.primesBelow (z + 1) := fun p hp => (Finset.mem_sdiff.1 (hsub hp)).1
    have hdvd : (∏ p ∈ t, p) ∣ primorial z := by
      rw [hprim]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsubB
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpos, Nat.le_of_dvd (primorial_pos z) hdvd⟩,
      Nat.mem_smoothNumbers_iff_primeFactors_subset.2
        ⟨hpos.ne', by rw [Nat.primeFactors_prod hprime]; exact hsubB⟩, ?_,
      (squarefree_primorial z).squarefree_of_dvd hdvd⟩
    refine isRough_iff.2 fun p hp hpd => ?_
    rw [hp.prime.dvd_finsetProd_iff] at hpd
    obtain ⟨q, hq, hpq⟩ := hpd
    have hpe : p = q := (Nat.prime_dvd_prime_iff_eq hp (hprime q hq)).1 hpq
    have hqy : y < q := (mem_primesIco.1 (hsub hq)).2.1
    omega
  · exact Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.1 hm).2.2.2
  · exact Nat.primeFactors_prod fun p hp =>
      prime_of_mem_primesIco (Finset.mem_powerset.1 ht hp)
  · rw [Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.1 hm).2.2.2]

/-- `(∏_{p ∈ t} p)^s = ∏_{p ∈ t} p^s` in `ℂ`, for a finite set of natural numbers. -/
lemma natCast_prod_cpow (t : Finset ℕ) (s : ℂ) :
    (((∏ p ∈ t, p : ℕ) : ℂ)) ^ s = ∏ p ∈ t, ((p : ℕ) : ℂ) ^ s := by
  classical
  refine Finset.induction_on t (by simp) ?_
  intro a t ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, ih]

/-- **The block Euler product is a finite Dirichlet polynomial**, at every `s`:
`F_{y,z}(s) = ∑_m X(m)·m^{-s}` over the `y`-rough `z`-smooth `m`.

The powerset transport `RMF.sum_blockSquarefree_eq_sum_powerset` against the closed form
`RMF.randomEulerProductIco_sqfree_eq`, expanded by `Finset.prod_one_add`.  No hypothesis on `s`:
the sum is finite.  Tail Plancherel for a band reads it at `s = ½ - c - it`. -/
theorem sum_blockWeighted_cpow_eq_randomEulerProductIco {X : ℕ → Ω → ℂ} (y z : ℕ) (s : ℂ)
    (ω : Ω) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m},
        (squarefreeExtension fun p => X p ω) m * (m : ℂ) ^ (-s)
      = randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) s ω := by
  -- the sum may be restricted to squarefree indices, which is what the powerset transport needs
  have hsf : ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) |
        m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m ∧ Squarefree m},
        (squarefreeExtension fun p => X p ω) m * (m : ℂ) ^ (-s)
      = ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m},
        (squarefreeExtension fun p => X p ω) m * (m : ℂ) ^ (-s) := by
    refine Finset.sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
    · rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1, hm.2.2.1⟩
    · rw [Finset.mem_filter] at hm hm'
      rw [squarefreeExtension_apply_of_not_squarefree _
        fun hs => hm' ⟨hm.1, hm.2.1, hm.2.2, hs⟩, zero_mul]
  rw [← hsf, sum_blockSquarefree_eq_sum_powerset, randomEulerProductIco_sqfree_eq,
    Finset.prod_one_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hprime : ∀ p ∈ t, p.Prime := fun p hp =>
    prime_of_mem_primesIco (Finset.mem_powerset.1 ht hp)
  rw [(isMultiplicative_squarefreeExtension (fun p => X p ω)).map_prod_of_prime t hprime,
    natCast_prod_cpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [squarefreeExtension_apply_prime _ (hprime p hp)]

/-- **The block Euler product is a finite sum**: `F_{y,z}(½) = ∑_m X(m)/√m` over the `y`-rough
`z`-smooth `m ≤ z#`, the block analogue of `RMF.smoothWeightedSum_eq_randomEulerProduct`.

No truncation hypothesis appears: a squarefree `z`-smooth `m` divides `z#`, which is written into
the index set.  The case `s = ½` of `RMF.sum_blockWeighted_cpow_eq_randomEulerProductIco`. -/
theorem sum_blockWeighted_eq_randomEulerProductIco {X : ℕ → Ω → ℂ} (y z : ℕ) (ω : Ω) :
    ∑ m ∈ {m ∈ Finset.Icc 1 (primorial z) | m ∈ Nat.smoothNumbers (z + 1) ∧ IsRough y m},
        (squarefreeExtension fun p => X p ω) m / (Real.sqrt m : ℂ)
      = randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (1 / 2) ω := by
  rw [← sum_blockWeighted_cpow_eq_randomEulerProductIco y z (1 / 2) ω]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcast : ((m : ℂ)) ^ (-(1 / 2 : ℂ)) = (((Real.sqrt m : ℝ) : ℂ))⁻¹ := by
    rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg m)]
    norm_num
  rw [hcast, div_eq_mul_inv]

/-- **The factorisation, second identity.**  `B_y(x) = F_{y,z}(½)·B_z(x) − T_{y,z}(x)`.

`y ≤ z` is used, once, inside `RMF.sum_blockSmooth_mul_sum_rough`; nothing is assumed about `x`,
for the same reason as in the first identity. -/
theorem roughWeightedRademacherSum_eq_mul_sub_blockTruncationTail {X : ℕ → Ω → ℂ} {y z : ℕ}
    (hyz : y ≤ z) (x : ℝ) (ω : Ω) :
    roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) y x ω
      = randomEulerProductIco
          (fun ω => squarefreeExtension fun p => X p ω) (y + 1) (z + 1) (1 / 2) ω
            * roughWeightedRademacherSum (fun ω => squarefreeExtension fun p => X p ω) z x ω
          - blockTruncationTail (fun ω => squarefreeExtension fun p => X p ω) y z x ω := by
  rw [eq_sub_iff_add_eq, ← sum_blockWeighted_eq_randomEulerProductIco (X := X) y z ω]
  simp only [blockTruncationTail, roughWeightedRademacherSum]
  refine (sum_blockSmooth_mul_sum_rough hyz x (fun n hn => ?_) fun m n hmn => ?_).symm
  · rw [squarefreeExtension_apply_of_not_squarefree _ hn, zero_div]
  · rw [(isMultiplicative_squarefreeExtension _).map_mul_of_coprime hmn, div_mul_div_comm,
      Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]

end RMF
