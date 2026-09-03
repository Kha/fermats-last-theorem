import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_isPullback_toBase_specMap_and_iotaFin_comp_eq_of_isPushout_of_chartAlg_eq_span

set_option autoImplicit false

open Polynomial TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isPullback_toBase_specMap_and_iotaFin_comp_eq_of_isPushout_of_chartAlg_eq_span
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R'' : Type u) [CommRing R''] [Algebra R R''] [Module.Free R R''] [Module.Finite R R'']
    (F' : Type u) [Field F'] [Algebra R F'] [Algebra R'' F'] [Algebra F F']
    [IsScalarTower R R'' F'] [IsScalarTower R F F'] [Algebra.IsPushout R R'' F F']
    (j : F) [Fact (j ≠ 0)] [Fact (algebraMap F F' j ≠ 0)]
    (hchart : ∀ S : Set F, S = {j} ∨ S = {j⁻¹} ∨ S = {j, j⁻¹} →
      Subalgebra.toSubmodule (chartAlg R F' (algebraMap F F' '' S)) =
        (Submodule.span R'' (algebraMap F F' '' (chartAlg R F S : Set F))).restrictScalars R) :
    ∃ (t' : AlgebraicCurve.TwoChartIntegralModel R F' (algebraMap F F' j) ⟶ Spec (CommRingCat.of R''))
      (u : AlgebraicCurve.TwoChartIntegralModel R F' (algebraMap F F' j) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j),
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'')) = toBase R F' (algebraMap F F' j) ∧
      u ≫ toBase R F j = toBase R F' (algebraMap F F' j) ∧
      IsPullback u t' (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ∧
      u ⁻¹ᵁ chartFinOpen R F j = chartFinOpen R F' (algebraMap F F' j) ∧

      u ⁻¹ᵁ chartInfOpen R F j = chartInfOpen R F' (algebraMap F F' j) ∧

      (∃ c : ↥(chartAlgFin R F j) →+* ↥(chartAlgFin R F' (algebraMap F F' j)),
        (∀ a : ↥(chartAlgFin R F j), ((c a : ↥(chartAlgFin R F' (algebraMap F F' j))) : F') = algebraMap F F' (a : F)) ∧
        ιFin R F' (algebraMap F F' j) ≫ u = Spec.map (CommRingCat.ofHom c) ≫ ιFin R F j) ∧
      (∃ τ : R'' →+* ↥(chartAlgFin R F' (algebraMap F F' j)),
        (∀ r : R'', ((τ r : ↥(chartAlgFin R F' (algebraMap F F' j))) : F') = algebraMap R'' F' r) ∧
        ιFin R F' (algebraMap F F' j) ≫ t' = Spec.map (CommRingCat.ofHom τ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isPullback_toBase_specMap_and_iotaFin_comp_eq_of_isPushout_of_chartAlg_eq_span.solution
