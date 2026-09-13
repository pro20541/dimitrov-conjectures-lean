import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# An abstract inequality underlying Dimitrov's Conjecture 1

This file isolates the analytic core from the arithmetic-function bounds.
-/

namespace FrontierMathLean

/-- For positive `x` and `r`, if `1 ≤ r ≤ x`, then
`x + x⁻¹ ≥ r + r⁻¹`. -/
lemma add_inv_mono_on_one
    {x r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) :
    r + r⁻¹ ≤ x + x⁻¹ := by
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hx_pos : 0 < x := lt_of_lt_of_le hr_pos hrx
  have h₁ : 0 ≤ x - r := sub_nonneg.mpr hrx
  have h₂ : 0 ≤ 1 - (x * r)⁻¹ := by
    rw [sub_nonneg]
    apply (inv_le_one₀ (mul_pos hx_pos hr_pos)).2
    have hx_one : 1 ≤ x := le_trans hr hrx
    nlinarith [mul_nonneg (sub_nonneg.mpr hx_one) (sub_nonneg.mpr hr)]
  have hprod : 0 ≤ (x - r) * (1 - (x * r)⁻¹) := mul_nonneg h₁ h₂
  field_simp [hx_pos.ne', hr_pos.ne'] at hprod ⊢
  nlinarith

/-- The normalized three-variable inequality. Equality occurs at `x = y = r`. -/
theorem normalized_three_variable_inequality
    {x y r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) (hry : r ≤ y) :
    5 + 2 * (r + r⁻¹) ≤
      3 + (x + x⁻¹) + (y + y⁻¹) + (x / y + y / x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) hrx
  have hy_pos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) hry
  have hx := add_inv_mono_on_one hr hrx
  have hy := add_inv_mono_on_one hr hry
  have hxy : 2 ≤ x / y + y / x := by
    have hsquare : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    field_simp [hx_pos.ne', hy_pos.ne']
    nlinarith
  linarith

end FrontierMathLean
