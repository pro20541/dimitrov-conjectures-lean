import FrontierMathLean.AbstractInequality
import Mathlib.Tactic.Ring

/-!
# Three-term reciprocal-product inequalities

This file packages the normalized inequality in the form used by the arithmetic
application.
-/

namespace FrontierMathLean

/-- If both `B / A` and `C / A` are at least `r ≥ 1`, the reciprocal-product
expression has the sharp lower bound attained when both ratios equal `r`. -/
theorem three_term_ratio_inequality
    {A B C r : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hr : 1 ≤ r) (hrB : r ≤ B / A) (hrC : r ≤ C / A) :
    5 + 2 * (r + r⁻¹) ≤
      (A + B + C) * (A⁻¹ + B⁻¹ + C⁻¹) := by
  have hnormalized := normalized_three_variable_inequality hr hrB hrC
  calc
    5 + 2 * (r + r⁻¹) ≤
        3 + (B / A + (B / A)⁻¹) + (C / A + (C / A)⁻¹) +
          ((B / A) / (C / A) + (C / A) / (B / A)) := hnormalized
    _ = (A + B + C) * (A⁻¹ + B⁻¹ + C⁻¹) := by
      field_simp [hA.ne', hB.ne', hC.ne']
      ring

/-- Power form of `three_term_ratio_inequality`. This is the exact abstract
shape needed after bounding the three arithmetic functions. -/
theorem three_term_power_inequality
    {a b c u v : ℝ} {k : ℕ}
    (ha : 0 < a) (hu : 0 < u)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) (hvc : v ≤ c) :
    5 + 2 * ((v / u) ^ k + ((v / u) ^ k)⁻¹) ≤
      (a ^ k + b ^ k + c ^ k) *
        ((a ^ k)⁻¹ + (b ^ k)⁻¹ + (c ^ k)⁻¹) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hb : 0 < b := lt_of_lt_of_le hv hvb
  have hc : 0 < c := lt_of_lt_of_le hv hvc
  have hA : 0 < a ^ k := pow_pos ha k
  have hB : 0 < b ^ k := pow_pos hb k
  have hC : 0 < c ^ k := pow_pos hc k
  have huv_ratio : 1 ≤ v / u := (one_le_div hu).2 huv
  have hratio_base_B : v / u ≤ b / a := by
    apply (div_le_div_iff₀ hu ha).2
    calc
      v * a ≤ b * a := mul_le_mul_of_nonneg_right hvb ha.le
      _ ≤ b * u := mul_le_mul_of_nonneg_left hau hb.le
  have hratio_base_C : v / u ≤ c / a := by
    apply (div_le_div_iff₀ hu ha).2
    calc
      v * a ≤ c * a := mul_le_mul_of_nonneg_right hvc ha.le
      _ ≤ c * u := mul_le_mul_of_nonneg_left hau hc.le
  have hratioB : (v / u) ^ k ≤ b ^ k / a ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_pos hv hu).le hratio_base_B k
  have hratioC : (v / u) ^ k ≤ c ^ k / a ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_pos hv hu).le hratio_base_C k
  exact three_term_ratio_inequality hA hB hC
    (one_le_pow₀ huv_ratio) hratioB hratioC

/-- Algebraic conversion between the normalized bound used in the proof and
the expanded rational expression used in Dimitrov's paper. -/
lemma paper_bound_eq_normalized
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k : ℕ) :
    (5 * (u * v) ^ k + 2 * v ^ (2 * k) + 2 * u ^ (2 * k)) /
        (u * v) ^ k =
      5 + 2 * ((v / u) ^ k + ((v / u) ^ k)⁻¹) := by
  have hpowv : v ^ (2 * k) = (v ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have hpowu : u ^ (2 * k) = (u ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  rw [hpowv, hpowu, mul_pow, div_pow]
  field_simp [hu.ne', hv.ne']
  ring

end FrontierMathLean
