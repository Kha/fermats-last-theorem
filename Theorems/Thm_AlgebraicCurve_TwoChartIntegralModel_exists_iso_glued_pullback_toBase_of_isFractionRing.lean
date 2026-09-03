import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_isFractionRing
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] :
    ∃ (es : AlgebraicCurve.CurveModel.glued K₀ j ⟶
        pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K₀))))
      (_ : IsIso es),
      es ≫ pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase R F j)
          (Spec.map (CommRingCat.ofHom (algebraMap R K₀))) =
        AlgebraicCurve.CurveModel.gluedToBase K₀ j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_isFractionRing.solution
