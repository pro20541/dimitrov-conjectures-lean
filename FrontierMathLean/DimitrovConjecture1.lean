import FrontierMathLean.ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Dimitrov's Conjecture 1

This file formalizes Conjecture 1 from S. I. Dimitrov,
"Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
(arXiv:2606.12484).

The preprint's conjecture is formalized over `ℚ`, equivalently to its usual interpretation over
`ℝ`. Its proof uses only the elementary bounds `φ(n) ≤ n - 1`, `n + 1 ≤ ψ(n)`, and
`n + 1 ≤ σ(n)`, together with the abstract inequality in
`FrontierMathLean.AbstractInequality`.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace FrontierMathLean

/-- The Dedekind psi function in its canonical prime-factor form:
`ψ(n) = ∏ p ∣ n, p ^ (vₚ(n) - 1) * (p + 1)` for positive `n`.

After casting to `ℚ`, this is equivalent to `(n : ℚ) * ∏ p ∣ n, (1 + 1 / p)`. The convention at
zero is `dedekindPsi 0 = 0`.
-/
def dedekindPsi (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

@[simp]
theorem dedekindPsi_zero : dedekindPsi 0 = 0 := by
  simp [dedekindPsi]

@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  simp [dedekindPsi]

/-- The Dedekind psi function takes the expected value on primes. -/
theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  simp [dedekindPsi, hp.ne_zero, hp.primeFactors, hp.factorization]

/-- Replacing the factor `p ^ a` by the corresponding Dedekind-psi prime-power factor
strictly increases it when `p` is prime and `a` is positive. -/
private theorem prime_power_factor_lt {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    p ^ a < p ^ (a - 1) * (p + 1) := by
  have hpow : 0 < p ^ (a - 1) := pow_pos hp.pos _
  have hexp : a - 1 + 1 = a := by omega
  calc
    p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, hexp]
    _ < p ^ (a - 1) * p + p ^ (a - 1) := Nat.lt_add_of_pos_right hpow
    _ = p ^ (a - 1) * (p + 1) := by rw [mul_add, mul_one]

/-- The elementary lower bound `n + 1 ≤ ψ(n)` for `n ≥ 2`. -/
theorem one_add_le_dedekindPsi {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ dedekindPsi n := by
  have hn0 : n ≠ 0 := by omega
  have hnonempty : n.primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr (by omega)
  have hlt :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) <
        ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro p hp
      exact pow_pos (Nat.pos_of_mem_primeFactors hp) _
    · intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hdiv := Nat.dvd_of_mem_primeFactors hp
      exact prime_power_factor_lt hprime (hprime.factorization_pos_of_dvd hn0 hdiv)
    · exact hnonempty
  have hlt_n :
      n < ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1) := by
    calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Nat.prod_primeFactors_pow_factorization hn0
      _ < _ := hlt
  simpa only [dedekindPsi, if_neg hn0, Nat.succ_le_iff] using hlt_n

/-- The elementary lower bound `n + 1 ≤ σ(n)` for the sum-of-divisors function. -/
theorem one_add_le_sigmaOne {n : ℕ} (hn : 2 ≤ n) :
    n + 1 ≤ ArithmeticFunction.sigma 1 n := by
  have hn0 : n ≠ 0 := by omega
  rw [ArithmeticFunction.sigma_one_apply]
  calc
    n + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d := by
      rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        omega
      · simp only [mem_singleton]
        omega
    _ ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro d hd
        simp only [mem_insert, mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Nat.one_mem_divisors.mpr hn0
        · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩) (by
          intro d _ _
          exact Nat.zero_le d)

/-- The elementary upper bound `φ(n) ≤ n - 1` for `n ≥ 2`. -/
theorem totient_le_sub_one {n : ℕ} (hn : 2 ≤ n) : n.totient ≤ n - 1 :=
  Nat.le_sub_one_of_lt (Nat.totient_lt n (by omega))

/-- Dimitrov's Conjecture 1, first expressed over `ℝ` to apply the abstract inequality. -/
theorem dimitrovConjecture1_real (k n : ℕ) (_hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℝ) ^ 2 - 1) ^ k
          + 2 * ((n : ℝ) + 1) ^ (2 * k)
          + 2 * ((n : ℝ) - 1) ^ (2 * k)) /
        (((n : ℝ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) *
        (((n.totient : ℝ) ^ k)⁻¹ + ((dedekindPsi n : ℝ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℝ) ^ k)⁻¹) := by
  have hnpos : 0 < n := by omega
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have htotient_pos_nat : 0 < n.totient := Nat.totient_pos.mpr hnpos
  have htotient_pos : (0 : ℝ) < n.totient := by exact_mod_cast htotient_pos_nat
  have htotient_le : (n.totient : ℝ) ≤ (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast totient_le_sub_one hn
  have hu : (0 : ℝ) < (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast (show 0 < n - 1 by omega)
  have huv : (n : ℝ) - 1 ≤ (n : ℝ) + 1 := by linarith
  have hpsi : (n : ℝ) + 1 ≤ dedekindPsi n := by
    exact_mod_cast one_add_le_dedekindPsi hn
  have hsigma : (n : ℝ) + 1 ≤ ArithmeticFunction.sigma 1 n := by
    exact_mod_cast one_add_le_sigmaOne hn
  have hfactor : (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) := by ring
  rw [hfactor, paper_bound_eq_normalized hu (by linarith : (0 : ℝ) < (n : ℝ) + 1) k]
  exact three_term_power_inequality htotient_pos hu htotient_le huv hpsi hsigma

/--
**Dimitrov's Conjecture 1** from arXiv:2606.12484, formalized over `ℚ` (and hence equivalently
over `ℝ`).
-/
theorem dimitrovConjecture1 (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℚ) ^ k)⁻¹) := by
  apply (Rat.cast_le (K := ℝ)).mp
  norm_num
  exact dimitrovConjecture1_real k n hk hn

#print axioms FrontierMathLean.dimitrovConjecture1

end FrontierMathLean
