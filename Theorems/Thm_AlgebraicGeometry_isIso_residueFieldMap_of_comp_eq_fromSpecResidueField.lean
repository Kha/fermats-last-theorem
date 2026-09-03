import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
    {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u₀ : Spec (Y.residueField y) ⟶ X)
    (hu₀ : u₀ ≫ f = Y.fromSpecResidueField y) :
    IsIso (f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField.solution
