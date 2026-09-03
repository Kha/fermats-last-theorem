import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.solution
