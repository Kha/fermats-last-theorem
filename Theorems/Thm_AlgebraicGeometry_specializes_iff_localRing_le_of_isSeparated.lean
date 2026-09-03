import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve

theorem AlgebraicGeometry.specializes_iff_localRing_le_of_isSeparated
    (A₀ : Type) [CommRing A₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X] [IsSeparated toBase]
    {F : Type} [Field F] (φ : F ≃+* X.functionField) (x y : X) :
    x ⤳ y ↔ SemistableModel.localRing X φ y ≤ SemistableModel.localRing X φ x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated.solution
