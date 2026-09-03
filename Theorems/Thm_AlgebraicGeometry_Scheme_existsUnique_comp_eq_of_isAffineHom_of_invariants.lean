import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.existsUnique_comp_eq_of_isAffineHom_of_invariants
    {M X : Scheme.{u}} (π : M ⟶ X) {H : Type v} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ h : H, (ρ h).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) :
    ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_comp_eq_of_isAffineHom_of_invariants.solution
