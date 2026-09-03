import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_of_forall_exists_forall_sum_char_mul_eq_zero
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (f : p.adicCompletion ℚ → ℂ)
    (hf : ∃ δ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x y : p.adicCompletion ℚ, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → f x = f y)
    (χ : p.adicCompletion ℚ → ℂ)
    (hχ : ∀ x y : p.adicCompletion ℚ, χ (x + y) = χ x * χ y)
    (hχ₁ : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : p.adicCompletion ℚ, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1)
    (hχ₂ : ∃ x₀ : p.adicCompletion ℚ, χ x₀ ≠ 1)
    (hsum : ∀ a : p.adicCompletion ℚ, a ≠ 0 →
      ∃ β₀ : (WithZero (Multiplicative ℤ))ˣ, ∀ β : (WithZero (Multiplicative ℤ))ˣ, β₀ ≤ β →
      ∃ δ : (WithZero (Multiplicative ℤ))ˣ, ∀ T : Finset (p.adicCompletion ℚ),
        (∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) →
        (∀ x : p.adicCompletion ℚ, Valued.v x < (β : WithZero (Multiplicative ℤ)) →
          ∃! t, t ∈ T ∧ Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ))) →
        ∑ t ∈ T, χ (-(a * t)) * f t = 0) :
    ∀ x y : p.adicCompletion ℚ, f x = f y := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero.solution
