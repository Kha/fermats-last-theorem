import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp

universe u

theorem LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {r : ℕ}
    (F₁ F₂ φ : (Fin r → A) →ₗ[A] (Fin r → A))
    (hF₁ : Function.Injective F₁) (hφ : Function.Injective φ)
    (hcomm : φ ∘ₗ F₂ = F₁ ∘ₗ φ) :
    Module.length A ((Fin r → A) ⧸ LinearMap.range F₁) =
      Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp.solution
