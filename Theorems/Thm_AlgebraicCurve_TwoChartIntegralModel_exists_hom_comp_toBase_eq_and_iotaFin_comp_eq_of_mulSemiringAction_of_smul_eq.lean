import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

universe u v in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (Γ : Type v) [Group Γ] [MulSemiringAction Γ R] [MulSemiringAction Γ F]

    (hΓF : ∀ (s : Γ) (r : R), s • algebraMap R F r = algebraMap R F (s • r))
    (hΓj : ∀ s : Γ, s • j = j) :
    ∃ (w : Γ → (AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j))
      (θ : Γ → (↥(chartAlgFin R F j) ≃+* ↥(chartAlgFin R F j)))
      (θ' : Γ → (↥(chartAlgInf R F j) ≃+* ↥(chartAlgInf R F j))),

      (∀ s : Γ, w s ≫ toBase R F j = toBase R F j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom Γ R s))) ∧

      w 1 = 𝟙 (AlgebraicCurve.TwoChartIntegralModel R F j) ∧
      (∀ s s' : Γ, w (s * s') = w s ≫ w s') ∧

      (∀ (s : Γ) (b : ↥(chartAlgFin R F j)), ((θ s b : ↥(chartAlgFin R F j)) : F) = s • (b : F)) ∧
      (∀ (s : Γ) (b : ↥(chartAlgInf R F j)), ((θ' s b : ↥(chartAlgInf R F j)) : F) = s • (b : F)) ∧

      (∀ s : Γ, ιFin R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ s).toRingHom) ≫ ιFin R F j) ∧
      (∀ s : Γ, ιInf R F j ≫ w s = Spec.map (CommRingCat.ofHom (θ' s).toRingHom) ≫ ιInf R F j) ∧
      (∀ s : Γ, (w s) ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F j).opensRange) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq.solution
