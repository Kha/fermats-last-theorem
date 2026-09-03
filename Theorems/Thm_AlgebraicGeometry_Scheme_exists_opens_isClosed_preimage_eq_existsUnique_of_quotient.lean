import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
    {M X : Scheme.{u}} {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (π : M ⟶ X)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hcat : ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)
    (V : M.Opens) (hVcl : IsClosed (V : Set M)) (hV : ∀ h : H, (ρ h).hom ⁻¹ᵁ V = V) :
    ∃ (U : X.Opens) (hUV : π ⁻¹ᵁ U = V), IsClosed (U : Set X) ∧ Set.image π.base (V : Set M) = (U : Set X) ∧
      ∀ (T : Scheme.{u}) (f : (V : Scheme.{u}) ⟶ T),
        (∀ h : H, (ρ h).hom.resLE V V (by rw [hV h]) ≫ f = f) →
        ∃! f' : (U : Scheme.{u}) ⟶ T, π.resLE U V (by rw [hUV]) ≫ f' = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient.solution
