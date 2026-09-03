import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel~exists_iso_of_algEquiv_apply_eq~exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem"
open scoped MatrixGroups
universe u in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (σ : F ≃ₐ[R] F) [Fact (σ j ≠ 0)]
    [IsSeparated (toBase R F j)] [IsSeparated (toBase R F (σ j))]
    [Algebra.FiniteType R ↥(chartAlgInf R F j)] [Algebra.FiniteType R ↥(chartAlgInf R F (σ j))]

    (hfin : σ j ∈ chartAlgFin R F j) (hfin' : j ∈ chartAlgFin R F (σ j))

    (hvis : ∀ y ∈ chartAlgInf R F (σ j), ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j)
    (hvis' : ∀ y ∈ chartAlgInf R F j, ∃ s ∈ chartAlgInf R F (σ j),
      (∃ a ∈ chartAlgInf R F (σ j), s = 1 + (σ j)⁻¹ * a) ∧ s * y ∈ chartAlgInf R F (σ j)) :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j)
      (θ : ↥(chartAlgFin R F j) ≃ₐ[R] ↥(chartAlgFin R F j)),

      w.hom ≫ toBase R F j = toBase R F j ∧

      (∀ b : ↥(chartAlgFin R F j), ((θ b : ↥(chartAlgFin R F j)) : F) = σ (b : F)) ∧

      ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) ≫ ιFin R F j ∧
      w.hom ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F j).opensRange := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv.solution
