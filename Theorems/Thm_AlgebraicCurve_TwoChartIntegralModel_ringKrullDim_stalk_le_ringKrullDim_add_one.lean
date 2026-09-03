import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_le_ringKrullDim_add_one
    (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ≤ ringKrullDim R + 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one.solution
