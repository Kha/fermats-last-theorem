import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_vanishingIdeal_closure_eq_branchIdeal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_vanishingIdeal_closure_eq_branchIdeal
    {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {ξ}, isClosed_closure⟩).ideal U) =
      Scheme.branchIdeal h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_vanishingIdeal_closure_eq_branchIdeal.solution
