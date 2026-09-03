import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap
    {U S : Scheme.{u}} (f : U ⟶ S) [LocallyOfFiniteType f] [FormallyUnramified f]
    (x : U) (hx : ∀ y : U, f y = f x → y = x) [IsIso (f.residueFieldMap x)] :
    IsIso (f.fiberToSpecResidueField (f x)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_fiberToSpecResidueField_of_preimage_eq_singleton_of_isIso_residueFieldMap.solution
