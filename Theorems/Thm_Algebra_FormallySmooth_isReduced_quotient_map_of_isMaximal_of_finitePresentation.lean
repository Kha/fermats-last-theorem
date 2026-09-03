import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_isReduced_quotient_map_of_isMaximal_of_finitePresentation

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem Algebra.FormallySmooth.isReduced_quotient_map_of_isMaximal_of_finitePresentation
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B]
    (I : Ideal A) (hI : I.IsMaximal) :
    IsReduced (B ⧸ Ideal.map (algebraMap A B) I) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_isReduced_quotient_map_of_isMaximal_of_finitePresentation.solution
