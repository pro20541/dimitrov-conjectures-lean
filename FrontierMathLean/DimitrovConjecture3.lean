import FrontierMathLean.DimitrovConjecture1
import FrontierMathLean.NesbittRatioInequality

/-!
# Dimitrov's Conjecture 3

This file formalizes Conjecture 3 from S. I. Dimitrov,
"Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
(arXiv:2606.12484v1).

The conjecture is stated over `ℚ`, exactly matching the ordinary rational
interpretation of the displayed fractions in the source preprint.
-/

open scoped ArithmeticFunction.sigma

namespace FrontierMathLean

/-- Dimitrov's Conjecture 3, first expressed over `ℝ` to apply the abstract
ratio-constrained Nesbitt inequality. -/
theorem dimitrovConjecture3_real (k n : ℕ) (_hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℝ) + 1) ^ (2 * k)
          + (((n : ℝ) ^ 2 - 1) ^ k)
          + ((n : ℝ) - 1) ^ (2 * k)) /
        (2 * (((n : ℝ) + 1) ^ (2 * k)
          + (((n : ℝ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℝ) ^ k /
          ((dedekindPsi n : ℝ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
        (dedekindPsi n : ℝ) ^ k /
          ((n.totient : ℝ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
        (ArithmeticFunction.sigma 1 n : ℝ) ^ k /
          ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k) := by
  have hnpos : 0 < n := by omega
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have htotient_pos_nat : 0 < n.totient := Nat.totient_pos.mpr hnpos
  have htotient_pos : (0 : ℝ) < n.totient := by
    exact_mod_cast htotient_pos_nat
  have htotient_le : (n.totient : ℝ) ≤ (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast totient_le_sub_one hn
  have hu : (0 : ℝ) < (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast (show 0 < n - 1 by omega)
  have hv : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have huv : (n : ℝ) - 1 ≤ (n : ℝ) + 1 := by linarith
  have hpsi : (n : ℝ) + 1 ≤ dedekindPsi n := by
    exact_mod_cast one_add_le_dedekindPsi hn
  have hsigma : (n : ℝ) + 1 ≤ ArithmeticFunction.sigma 1 n := by
    exact_mod_cast one_add_le_sigmaOne hn
  have hfactor : (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) := by
    ring
  rw [hfactor, nesbitt_paper_bound_eq_normalized hu hv k]
  exact three_term_nesbitt_power_inequality
    htotient_pos hu htotient_le huv hpsi hsigma

/--
**Dimitrov's Conjecture 3** from arXiv:2606.12484v1, formalized over `ℚ`.
-/
theorem dimitrovConjecture3 (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k)
          + ((n : ℚ) - 1) ^ (2 * k)) /
        (2 * (((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℚ) ^ k /
          ((dedekindPsi n : ℚ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
        (dedekindPsi n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
        (ArithmeticFunction.sigma 1 n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k) := by
  apply (Rat.cast_le (K := ℝ)).mp
  norm_num
  exact dimitrovConjecture3_real k n hk hn

#print axioms FrontierMathLean.dimitrovConjecture3

end FrontierMathLean
