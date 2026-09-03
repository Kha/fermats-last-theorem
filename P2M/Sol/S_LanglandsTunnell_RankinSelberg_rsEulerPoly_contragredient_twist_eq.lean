import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_contragredient_twist_eq

set_option autoImplicit false

open Polynomial LanglandsTunnell.RankinSelberg

theorem solution
    (a b t : ℂ) (hb : b ≠ 0) (ht : t ≠ 0) :
    rsEulerPoly ((t * a) / (t ^ 2 * b)) (t ^ 2 * b)⁻¹ (t * a) (t ^ 2 * b) 0 =
      rsEulerPoly (a / b) b⁻¹ a b 0 := by
  have hb2 : t ^ 2 * b ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht) hb
  unfold rsEulerPoly
  have h1 : -((t * a) / (t ^ 2 * b) * (t * a)) = -(a / b * a) := by
    congr 1; field_simp
  have h2 : ((t * a) / (t ^ 2 * b)) ^ 2 * (t ^ 2 * b) + (t ^ 2 * b)⁻¹ * (t * a) ^ 2 - 2 * (t ^ 2 * b)⁻¹ * (t ^ 2 * b) =
      (a / b) ^ 2 * b + b⁻¹ * a ^ 2 - 2 * b⁻¹ * b := by
    field_simp
  have h3 : -(((t * a) / (t ^ 2 * b)) ^ 3 * 0) - (t * a) / (t ^ 2 * b) * (t ^ 2 * b)⁻¹ * (t * a) * (t ^ 2 * b) +
        3 * ((t * a) / (t ^ 2 * b)) * (t ^ 2 * b)⁻¹ * 0 =
      -((a / b) ^ 3 * 0) - a / b * b⁻¹ * a * b + 3 * (a / b) * b⁻¹ * 0 := by
    simp only [mul_zero, neg_zero, zero_sub, add_zero]
    congr 1; field_simp
  have h4 : ((t * a) / (t ^ 2 * b)) ^ 2 * (t ^ 2 * b)⁻¹ * (t * a) * 0 - 2 * (t ^ 2 * b)⁻¹ ^ 2 * (t * a) * 0 +
        (t ^ 2 * b)⁻¹ ^ 2 * (t ^ 2 * b) ^ 2 =
      (a / b) ^ 2 * b⁻¹ * a * 0 - 2 * b⁻¹ ^ 2 * a * 0 + b⁻¹ ^ 2 * b ^ 2 := by
    simp only [mul_zero, sub_zero, zero_add]
    field_simp
  have h5 : -((t * a) / (t ^ 2 * b) * (t ^ 2 * b)⁻¹ ^ 2 * (t ^ 2 * b) * 0) = -(a / b * b⁻¹ ^ 2 * b * 0) := by
    simp
  have h6 : (t ^ 2 * b)⁻¹ ^ 3 * (0 : ℂ) ^ 2 = b⁻¹ ^ 3 * (0 : ℂ) ^ 2 := by simp
  rw [h1, h2, h3, h4, h5, h6]
