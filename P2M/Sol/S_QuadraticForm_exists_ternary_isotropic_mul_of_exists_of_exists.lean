import Mathlib
import P2M.Util
namespace P2MW.S_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] (t u u' : K)
    (h : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u * y ^ 2 = 0)
    (h' : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u' * y ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - (u * u') * y ^ 2 = 0 := by
  obtain ⟨z, x, y, hne, he⟩ := h
  obtain ⟨z', x', y', hne', he'⟩ := h'
  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨z, x, 0, ?_, ?_⟩
    · rintro ⟨hz, hx, -⟩; exact hne ⟨hz, hx, rfl⟩
    · linear_combination he
  by_cases hy0' : y' = 0
  · subst hy0'
    refine ⟨z', x', 0, ?_, ?_⟩
    · rintro ⟨hz, hx, -⟩; exact hne' ⟨hz, hx, rfl⟩
    · linear_combination he'
  refine ⟨z * z' + t * x * x', z * x' + x * z', y * y', ?_, ?_⟩
  · rintro ⟨-, -, hyy⟩
    exact (mul_ne_zero hy0 hy0') hyy
  · linear_combination (z' ^ 2 - t * x' ^ 2) * he + (u * y ^ 2) * he'
