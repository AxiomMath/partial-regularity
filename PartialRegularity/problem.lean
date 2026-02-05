import Mathlib

/-
# Problem Description

We define the notion of $m$-regular primes and a function $M_\alpha$ on primes.
The theorem states an asymptotic bound on primes that fail to be $M_\alpha(p)$-regular.

## Definitions

1. **Bernoulli numbers**: The $(2k)$-th Bernoulli number $B_{2k} \in \mathbb{Q}$ is defined via
   the exponential generating function $\frac{t}{e^t - 1} = \sum_{n=0}^{\infty} B_n \frac{t^n}{n!}$.

2. **$m$-regular prime**: For $m \in \mathbb{N}$, a prime $p$ is $m$-regular if:
   - $p$ is odd, and
   - $p$ does not divide the numerator of $B_{2k}$ for each $k$ with $1 \le 2k \le \min(m, p-3)$.

3. **The function $M_\alpha$**: For $\alpha > 1/2$ and prime $p$,
   $M_\alpha(p) := \lfloor \sqrt{p} / (\log p)^\alpha \rfloor$

## Main Theorem

For fixed $\alpha > 1/2$:
$\#\{ p \le X \text{ prime} : p \text{ is not } M_\alpha(p)\text{-regular} \} = O(X / (\log X)^{2\alpha})$
-/

-- Background: Bernoulli numbers are available in Mathlib as `bernoulli : ℕ → ℚ`.
-- The "numerator of B_{2k}" refers to the numerator when B_{2k} is written in lowest terms.

-- Main Definition 1: m-regular prime
/-- A prime `p` is `m`-regular if it is odd and does not divide the numerator of the
    Bernoulli number `B_{2k}` for each `k` with `1 ≤ 2k ≤ min(m, p - 3)`. -/
def IsRegularPrime (m : ℕ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ Odd p ∧
    ∀ k : ℕ, 1 ≤ 2 * k → 2 * k ≤ min m (p - 3) →
      ¬((p : ℤ) ∣ (bernoulli (2 * k)).num)

-- Decidable instance for IsRegularPrime using classical logic
noncomputable instance decidable_IsRegularPrime (m : ℕ) (p : ℕ) : Decidable (IsRegularPrime m p) :=
  Classical.propDecidable (IsRegularPrime m p)

-- Main Definition 2: The function M_α
/-- For a real number `α > 1/2` and a prime `p`, define
    `M_α(p) = ⌊√p / (log p)^α⌋`. -/
noncomputable def M_alpha (α : ℝ) (p : ℕ) : ℕ :=
  ⌊Real.sqrt p / (Real.log p) ^ α⌋₊

-- Auxiliary: counting function for primes p ≤ X that are NOT M_α(p)-regular
/-- Count of primes `p ≤ X` that are not `M_α(p)`-regular. -/
noncomputable def countNonRegularPrimes (α : ℝ) (X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
    Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p)).card

-- Main Statement
/-- For fixed `α > 1/2`, the number of primes `p ≤ X` that are not `M_α(p)`-regular is
    $O(X / (\log X)^{2α})$ as `X → +∞`. -/
theorem irregular_primes_asymptotic (α : ℝ) (hα : 1/2 < α) :
    (fun X : ℝ => (countNonRegularPrimes α X : ℝ)) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  sorry
