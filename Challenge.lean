import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Full-range forms of Dimitrov's Conjectures 1 and 3

This is the small statement surface intended for independent inspection by the
Palomar Registry. It formalizes Conjectures 1 and 3 from S. I. Dimitrov,
*Lower bounds on expressions depending on the functions phi(n), psi(n) and
sigma(n), III* (arXiv:2606.12484v1).

For all natural numbers `k >= 1` and `n >= 2`, the first and third theorems
state the source's two rational inequalities involving Euler's totient,
Dedekind's psi function, and the sum-of-divisors function. The second and
fourth theorems give an additional sharpness result: equality holds exactly
when `n` is prime. The source proves the `k = 1` instances and remarks on
`k = 2, 3`; these formal results cover every `k >= 1`. Historical priority
for the full-range proofs has not been certified by Palomar or by this file.
By supplying the full parameter range and sharp equality cases beyond those
treated in the source, the project is relevant to researchers in elementary
and analytic number theory who study inequalities among multiplicative
arithmetic functions, and to formal-mathematics researchers studying the
verification of contemporary conjectures.

The deliberate `sorry` terms below state the claims to be compared. The
separate Solution module supplies proofs, and Comparator checks that its
definition and theorem types exactly match this module.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace PalomarDimitrov

/-- The Dedekind psi function, using its standard prime-factor formula for
positive `n` and the harmless convention `psi(0) = 0`. -/
def dedekindPsi (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

/-- The ordinary sum-of-divisors function `σ(n)`, exposed through a plain
function so Palomar's notation audit does not need Mathlib's bundled coercion. -/
def sigmaOne (n : ℕ) : ℕ :=
  ArithmeticFunction.sigma 1 n

/-- Dimitrov's Conjecture 1 for its entire stated range `k >= 1`, `n >= 2`. -/
theorem conjecture1FullRange (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹) := by
  sorry

/-- Equality in Dimitrov's Conjecture 1 holds if and only if `n` is prime. -/
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
  sorry

/-- Dimitrov's Conjecture 3 for its entire stated range `k >= 1`, `n >= 2`. -/
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
  sorry

/-- Equality in Dimitrov's Conjecture 3 holds if and only if `n` is prime. -/
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
  sorry

end PalomarDimitrov
