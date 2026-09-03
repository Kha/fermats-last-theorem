import Mathlib
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    (U : X.Opens) [Nonempty U]
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k])
    (v : letI := (baseToFunctionField c).toAlgebra; Place k X.functionField)
    (hv : letI := (baseToFunctionField c).toAlgebra; v ∈ placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ f ∈ v.toValuationSubring, kaehlerToFunctionField c U η = f • v.dCoord := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf.solution
