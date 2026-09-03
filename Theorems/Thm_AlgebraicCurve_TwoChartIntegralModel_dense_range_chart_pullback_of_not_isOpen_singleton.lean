import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.dense_range_chart_pullback_of_not_isOpen_singleton
    (R : Type u) [CommRing R]
    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [Algebra.FiniteType R ↥(chartAlgInf R F j)]
    (κ : Type u) [Field κ] [Algebra R κ]

    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))

    (hniso : ∀ x : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))),
      ¬ IsOpen ({x} : Set ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))) :
    Dense (Set.range c.base) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton.solution
