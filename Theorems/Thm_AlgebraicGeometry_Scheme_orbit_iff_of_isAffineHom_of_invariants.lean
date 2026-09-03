import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_orbit_iff_of_isAffineHom_of_invariants

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.orbit_iff_of_isAffineHom_of_invariants
    {M X : Scheme.{0}} (π : M ⟶ X)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) :
    ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_orbit_iff_of_isAffineHom_of_invariants.solution
