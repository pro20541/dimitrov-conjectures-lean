import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A ratio-constrained Nesbitt inequality

This file isolates the analytic inequality used for Dimitrov's Conjecture 3.
-/

namespace FrontierMathLean

/-- Balancing two positive variables can only decrease the two asymmetric
fractions occurring in the normalized Nesbitt expression. -/
lemma balanced_pair_fraction_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * (x + y) / (x + y + 2) ≤ x / (1 + y) + y / (1 + x) := by
  have hxy2 : 0 < x + y + 2 := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1y : 0 < 1 + y := by linarith
  have hden : 0 < (1 + x) * (1 + y) * (x + y + 2) := by positivity
  have hid :
      x / (1 + y) + y / (1 + x) - 2 * (x + y) / (x + y + 2) =
        ((x + y + 1) * (x - y) ^ 2) /
          ((1 + x) * (1 + y) * (x + y + 2)) := by
    field_simp [h1x.ne', h1y.ne', hxy2.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

/-- The one-variable lower envelope is increasing from the point corresponding
to ratio one. -/
lemma nesbitt_envelope_mono
    {s t : ℝ} (ht : 2 ≤ t) (hts : t ≤ s) :
    1 / t + 2 * t / (t + 2) ≤ 1 / s + 2 * s / (s + 2) := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hspos : 0 < s := lt_of_lt_of_le htpos hts
  have ht2 : 0 < t + 2 := by linarith
  have hs2 : 0 < s + 2 := by linarith
  have hfactor : 0 ≤ 3 * s * t - 2 * s - 2 * t - 4 := by
    have hst : 0 ≤ (s - 2) * (t - 2) :=
      mul_nonneg (sub_nonneg.mpr (ht.trans hts)) (sub_nonneg.mpr ht)
    nlinarith
  have hid :
      (1 / s + 2 * s / (s + 2)) - (1 / t + 2 * t / (t + 2)) =
        ((s - t) * (3 * s * t - 2 * s - 2 * t - 4)) /
          (s * t * (s + 2) * (t + 2)) := by
    field_simp [hspos.ne', htpos.ne', hs2.ne', ht2.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

/-- Strict form of `nesbitt_envelope_mono` above the endpoint `2`. -/
lemma nesbitt_envelope_strict
    {s t : ℝ} (ht : 2 < t) (hts : t < s) :
    1 / t + 2 * t / (t + 2) < 1 / s + 2 * s / (s + 2) := by
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := lt_trans htpos hts
  have ht2 : 0 < t + 2 := by linarith
  have hs2 : 0 < s + 2 := by linarith
  have hfactor : 0 < 3 * s * t - 2 * s - 2 * t - 4 := by
    have hst : 0 < (s - 2) * (t - 2) :=
      mul_pos (sub_pos.mpr (lt_trans ht hts)) (sub_pos.mpr ht)
    nlinarith
  have hid :
      (1 / s + 2 * s / (s + 2)) - (1 / t + 2 * t / (t + 2)) =
        ((s - t) * (3 * s * t - 2 * s - 2 * t - 4)) /
          (s * t * (s + 2) * (t + 2)) := by
    field_simp [hspos.ne', htpos.ne', hs2.ne', ht2.ne']
    ring
  rw [← sub_pos, hid]
  positivity

/-- If `x` and `y` are both at least `r ≥ 1`, the normalized Nesbitt
expression has its sharp minimum at `x = y = r`. -/
theorem normalized_nesbitt_ratio_inequality
    {x y r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) (hry : r ≤ y) :
    (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) ≤
      1 / (x + y) + x / (1 + y) + y / (1 + x) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hxpos : 0 < x := lt_of_lt_of_le hrpos hrx
  have hypos : 0 < y := lt_of_lt_of_le hrpos hry
  have htwor : 2 ≤ 2 * r := by linarith
  have hsum : 2 * r ≤ x + y := by linarith
  have hmono := nesbitt_envelope_mono htwor hsum
  have hbalance := balanced_pair_fraction_le hxpos hypos
  have hnormalized :
      (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) =
        1 / (2 * r) + 2 * (2 * r) / (2 * r + 2) := by
    field_simp [hrpos.ne']
    ring
  rw [hnormalized]
  linarith

/-- Equality in the normalized ratio-constrained Nesbitt inequality occurs
exactly when both variables attain the common lower bound. -/
theorem normalized_nesbitt_ratio_eq_iff
    {x y r : ℝ} (hr : 1 < r) (hrx : r ≤ x) (hry : r ≤ y) :
    1 / (x + y) + x / (1 + y) + y / (1 + x) =
        (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) ↔
      x = r ∧ y = r := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hxpos : 0 < x := lt_of_lt_of_le hrpos hrx
  have hypos : 0 < y := lt_of_lt_of_le hrpos hry
  have htwor : 2 < 2 * r := by linarith
  have hsum : 2 * r ≤ x + y := by linarith
  have hnormalized :
      (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) =
        1 / (2 * r) + 2 * (2 * r) / (2 * r + 2) := by
    field_simp [hrpos.ne']
    ring
  constructor
  · intro hEq
    have hbalance := balanced_pair_fraction_le hxpos hypos
    have hsum_eq : x + y = 2 * r := by
      apply le_antisymm
      · by_contra hnot
        have hstrict_sum : 2 * r < x + y := lt_of_not_ge hnot
        have hstrict := nesbitt_envelope_strict htwor hstrict_sum
        rw [← hnormalized] at hstrict
        linarith
      · exact hsum
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    field_simp [hrpos.ne']
    ring

/-- Power form of `normalized_nesbitt_ratio_inequality`. This is the abstract
shape needed for the arithmetic-function application. -/
theorem three_term_nesbitt_power_inequality
    {a b c u v : ℝ} {k : ℕ}
    (ha : 0 < a) (hu : 0 < u)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) (hvc : v ≤ c) :
    (4 * ((v / u) ^ k) ^ 2 + (v / u) ^ k + 1) /
        (2 * (((v / u) ^ k) ^ 2 + (v / u) ^ k)) ≤
      a ^ k / (b ^ k + c ^ k) +
        b ^ k / (a ^ k + c ^ k) +
        c ^ k / (a ^ k + b ^ k) := by
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
  have hnormalized := normalized_nesbitt_ratio_inequality
    (one_le_pow₀ huv_ratio) hratioB hratioC
  calc
    (4 * ((v / u) ^ k) ^ 2 + (v / u) ^ k + 1) /
          (2 * (((v / u) ^ k) ^ 2 + (v / u) ^ k)) ≤
        1 / (b ^ k / a ^ k + c ^ k / a ^ k) +
          (b ^ k / a ^ k) / (1 + c ^ k / a ^ k) +
          (c ^ k / a ^ k) / (1 + b ^ k / a ^ k) := hnormalized
    _ = a ^ k / (b ^ k + c ^ k) +
          b ^ k / (a ^ k + c ^ k) +
          c ^ k / (a ^ k + b ^ k) := by
      field_simp [hA.ne', hB.ne', hC.ne']

/-- Algebraic conversion from the compact ratio bound to the exact expanded
form used in Dimitrov's Conjecture 3. -/
lemma nesbitt_paper_bound_eq_normalized
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k : ℕ) :
    (4 * v ^ (2 * k) + (u * v) ^ k + u ^ (2 * k)) /
        (2 * (v ^ (2 * k) + (u * v) ^ k)) =
      (4 * ((v / u) ^ k) ^ 2 + (v / u) ^ k + 1) /
        (2 * (((v / u) ^ k) ^ 2 + (v / u) ^ k)) := by
  have hpowv : v ^ (2 * k) = (v ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have hpowu : u ^ (2 * k) = (u ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  rw [hpowv, hpowu, mul_pow, div_pow]
  field_simp [hu.ne', hv.ne']

end FrontierMathLean
