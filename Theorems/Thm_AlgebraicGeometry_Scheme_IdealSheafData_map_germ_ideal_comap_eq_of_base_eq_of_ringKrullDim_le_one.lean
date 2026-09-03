import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one
    {X : Scheme.{u}} (I : X.IdealSheafData) (σ : X ≅ X) (x : X) (hx : σ.hom.base x = x)
    [IsNoetherianRing (X.presheaf.stalk x)] [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ U x hxU).hom ((I.comap σ.hom).ideal U) =
      Ideal.map (X.presheaf.germ U x hxU).hom (I.ideal U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one.solution
