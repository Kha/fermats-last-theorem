import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
theorem AlgebraicCurve.nonempty_algEquiv_functionField_of_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (e : X ≅ Y) (he : e.hom ≫ cY = cX) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    Nonempty (X.functionField ≃ₐ[K] Y.functionField) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso.solution
