import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_charZero
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [CharZero K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (j : F) [Fact (j ≠ 0)]
    (k : Type u) [Field k] [Algebra R k] [Algebra K₀ k] [IsScalarTower R K₀ k] :
    AlgebraicGeometry.IsReduced
      (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero.solution
