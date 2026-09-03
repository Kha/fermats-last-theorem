import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.nonempty_schemeHomOver_id_toBase_of_algHom
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (φ : ↥(chartAlgInf R F j) →ₐ[R] R) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (toBase R F j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom.solution
