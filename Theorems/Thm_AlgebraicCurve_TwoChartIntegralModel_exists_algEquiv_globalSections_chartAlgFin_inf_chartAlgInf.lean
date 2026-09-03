import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    ∃ e : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) ≃ₐ[R]
        ↥(chartAlgFin R F j ⊓ chartAlgInf R F j),
      (∀ s, ((e s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
        ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R F j))).hom ((ιFin R F j).appTop s) :
          chartAlgFin R F j)) ∧
      (∀ s, ((e s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
        ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R F j))).hom ((ιInf R F j).appTop s) :
          chartAlgInf R F j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf.solution
