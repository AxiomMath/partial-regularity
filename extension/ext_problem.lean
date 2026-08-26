import Mathlib

/-
# Problem Description

The Bernoulli numbers $B_n \in \mathbb{Q}$ for $n \in \mathbb{N}$ are defined by the generating function
$\frac{x}{e^x - 1} = \sum_{n=0}^{\infty} \frac{B_n}{n!} x^n$.

An odd prime $p$ is called $m$-regular if $p$ does not divide the numerator of $B_{2k}$
(in lowest terms) for every integer $k$ satisfying $1 \le 2k \le \min(m, p-3)$.

For a real $\alpha > 1/2$ and a prime $p$, define
$M_\alpha(p) := \lfloor \frac{\sqrt{p}}{(\log p)^\alpha} \rfloor$.

Theorem: Let $\alpha > 1/2$. Then as $X \to +\infty$,
$\#\{p \le X : p \text{ is a prime that is not } M_\alpha(p)\text{-regular}\} = O(X/(\log X)^{2\alpha})$.
-/

-- Background and context
-- This concerns the distribution of irregular primes related to Bernoulli numbers.
-- The von Staudt-Clausen theorem describes the denominator structure of Bernoulli numbers,
-- while the numerators are more mysterious.

-- Main Definition(s)

/-- A prime p is m-regular if p is odd and p does not divide the numerator of B_{2k}
    for all positive integers k with 2k ≤ min(m, p-3).

    Note: When min(m, p-3) < 2, the condition is vacuously satisfied. -/
def isMRegular (m : ℕ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ Odd p ∧
    ∀ k : ℕ, 1 ≤ k → 2 * k ≤ min m (p - 3) →
      ¬((p : ℤ) ∣ (bernoulli (2 * k)).num)

/-- For α > 1/2 and a prime p, M_α(p) = ⌊√p / (log p)^α⌋. -/
noncomputable def M_alpha (α : ℝ) (p : ℕ) : ℕ :=
  ⌊Real.sqrt p / (Real.log p) ^ α⌋₊

/-- The set of odd primes p ≤ X that are not M_α(p)-regular.

    Note: The definition of m-regularity only applies to odd primes.
    Prime 2 is excluded from this set since m-regularity is not defined for it. -/
noncomputable def irregularPrimesUpTo (α : ℝ) (X : ℕ) : Set ℕ :=
  {p : ℕ | p ≤ X ∧ Nat.Prime p ∧ Odd p ∧ ¬isMRegular (M_alpha α p) p}

-- Main Statement(s)

/-- Main theorem: The count of odd primes p ≤ X that are not M_α(p)-regular is O(X/(log X)^{2α}). -/
theorem irregularPrimes_isBigO (α : ℝ) (hα : 1 / 2 < α) :
    (fun X : ℕ => ((irregularPrimesUpTo α X).ncard : ℝ)) =O[Filter.atTop]
      (fun X : ℕ => (X : ℝ) / (Real.log X) ^ (2 * α)) := by
  sorry
