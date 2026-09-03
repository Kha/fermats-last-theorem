import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_exists_finset_forall_eq_sum_mul_char_mul

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.exists_finset_forall_eq_sum_mul_char_mul
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (χ : p.adicCompletion ℚ → ℂ)
    (hχ : ∀ x y : p.adicCompletion ℚ, χ (x + y) = χ x * χ y)
    (hχ₁ : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : p.adicCompletion ℚ, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1)
    (hχ₂ : ∃ x₀ : p.adicCompletion ℚ, χ x₀ ≠ 1)
    (f : p.adicCompletion ℚ → ℂ) (δ : (WithZero (Multiplicative ℤ))ˣ)
    (hf : ∀ x y : p.adicCompletion ℚ, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → f x = f y)
    (β : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ (T : Finset (p.adicCompletion ℚ)) (c : p.adicCompletion ℚ → ℂ),
      ∀ x : p.adicCompletion ℚ, Valued.v x < (β : WithZero (Multiplicative ℤ)) → f x = ∑ y ∈ T, c y * χ (x * y) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_exists_finset_forall_eq_sum_mul_char_mul.solution
