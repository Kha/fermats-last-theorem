import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem ModularForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : UpperHalfPlane,
        f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) =
          F τ * ModularForm.discriminant τ ^ m) ↔
      ((∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 3 = ModularForm.E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 2 = ModularForm.E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
          ((F ∘ (A • ·)) * ModularForm.discriminant ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.solution
