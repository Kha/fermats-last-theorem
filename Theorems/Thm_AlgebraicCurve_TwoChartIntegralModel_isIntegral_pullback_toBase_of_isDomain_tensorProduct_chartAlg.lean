import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicCurve.TwoChartIntegralModel.isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (k : Type u) [CommRing k] [Algebra R k]
    [IsDomain (k ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j))]
    [IsDomain (k ⊗[R] ↥(TwoChartIntegralModel.chartAlgInf R F j))]
    [Nontrivial (k ⊗[R] ↥(TwoChartIntegralModel.chartAlgMid R F j))] :
    IsIntegral ↑(pullback (TwoChartIntegralModel.toBase R F j)
      (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral_pullback_toBase_of_isDomain_tensorProduct_chartAlg.solution
