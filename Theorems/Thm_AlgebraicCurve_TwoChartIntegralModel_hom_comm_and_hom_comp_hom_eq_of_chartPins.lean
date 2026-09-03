import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.hom_comm_and_hom_comp_hom_eq_of_chartPins
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsSeparated (toBase R F j)]
    (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hw : w.hom ≫ toBase R F j = toBase R F j)
    (θw : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F j))
    (hpw : ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom θw.toRingHom) ≫ ιFin R F j)
    (δ : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hδ : δ.hom ≫ toBase R F j = toBase R F j)
    (θδ : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F j))
    (hpδ : Spec.map (CommRingCat.ofHom θδ.toRingHom) ≫ ιFin R F j = ιFin R F j ≫ δ.inv) :
    ((∀ x, θw (θδ x) = θδ (θw x)) → w.hom ≫ δ.hom = δ.hom ≫ w.hom) ∧
    ((∀ x, θδ (θw (θw x)) = x) → w.hom ≫ w.hom = δ.hom) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_hom_comm_and_hom_comp_hom_eq_of_chartPins.solution
