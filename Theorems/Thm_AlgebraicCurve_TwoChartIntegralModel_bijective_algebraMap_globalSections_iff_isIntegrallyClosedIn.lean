import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    Function.Bijective (algebraMap R Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) ↔
      IsIntegrallyClosedIn R F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn.solution
