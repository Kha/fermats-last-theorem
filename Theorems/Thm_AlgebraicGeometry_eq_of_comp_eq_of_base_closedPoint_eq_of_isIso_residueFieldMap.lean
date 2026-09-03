import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : X ⟶ Y) (u u' : Spec (CommRingCat.of K) ⟶ X) (h : u ≫ f = u' ≫ f)
    (hpt : u.base (IsLocalRing.closedPoint K) = u'.base (IsLocalRing.closedPoint K))
    (hκ : IsIso (f.residueFieldMap (u.base (IsLocalRing.closedPoint K)))) :
    u = u' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap.solution
