import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyQuasiFinite f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one.solution
