import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants
    {B₀ : Type} [CommRing B₀] [IsDedekindDomain B₀]
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hflat : Flat πM) (hlft : LocallyOfFiniteType πM) :
    Flat πX ∧ LocallyOfFiniteType πX := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_flat_and_locallyOfFiniteType_of_isAffineHom_of_invariants.solution
