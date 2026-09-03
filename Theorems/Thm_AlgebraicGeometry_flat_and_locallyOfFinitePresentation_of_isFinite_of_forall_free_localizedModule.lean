import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [IsLocallyNoetherian Y]
    (h : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hy : y ∈ U),
      letI := (π.app U).hom.toAlgebra
      Module.Free (Localization.AtPrime (hU.primeIdealOf ⟨y, hy⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl Γ(X, π ⁻¹ᵁ U))) :
    Flat π ∧ LocallyOfFinitePresentation π := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule.solution
