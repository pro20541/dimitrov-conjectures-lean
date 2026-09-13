import FrontierMathLean.DimitrovConjecture1Equality
import FrontierMathLean.DimitrovConjecture3Equality

/-!
# Proved solutions to Dimitrov's Conjectures 1 and 3

This module gives proved declarations with the same names, definition value,
and theorem types as `Challenge`. It intentionally does not import that module:
Comparator elaborates the two environments separately and checks their exact
agreement.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace PalomarDimitrov

/-- The Dedekind psi function, identical to the definition in `Challenge`. -/
def dedekindPsi (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

/-- The ordinary sum-of-divisors function, identical to the wrapper in
`Challenge`. -/
def sigmaOne (n : ℕ) : ℕ :=
  ArithmeticFunction.sigma 1 n

/-- Proved full-range form of Dimitrov's Conjecture 1. -/
theorem conjecture1FullRange (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹) := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture1 k n hk hn

/-- Proved equality characterization for Dimitrov's Conjecture 1. -/
theorem conjecture1EqualityIffPrime (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ((5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) =
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹)) ↔
      n.Prime := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture1_eq_iff_prime k n hk hn

/-- Proved full-range form of Dimitrov's Conjecture 3. -/
theorem conjecture3FullRange (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k)
          + ((n : ℚ) - 1) ^ (2 * k)) /
        (2 * (((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℚ) ^ k /
          ((dedekindPsi n : ℚ) ^ k
            + (sigmaOne n : ℚ) ^ k) +
        (dedekindPsi n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k
            + (sigmaOne n : ℚ) ^ k) +
        (sigmaOne n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k) := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture3 k n hk hn

/-- Proved equality characterization for Dimitrov's Conjecture 3. -/
theorem conjecture3EqualityIffPrime (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (((4 * ((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k)
            + ((n : ℚ) - 1) ^ (2 * k)) /
          (2 * (((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k))) =
        (n.totient : ℚ) ^ k /
            ((dedekindPsi n : ℚ) ^ k
              + (sigmaOne n : ℚ) ^ k) +
          (dedekindPsi n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k
              + (sigmaOne n : ℚ) ^ k) +
          (sigmaOne n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k))) ↔
      n.Prime := by
  simpa only [dedekindPsi, FrontierMathLean.dedekindPsi, sigmaOne] using
    FrontierMathLean.dimitrovConjecture3_eq_iff_prime k n hk hn

end PalomarDimitrov
