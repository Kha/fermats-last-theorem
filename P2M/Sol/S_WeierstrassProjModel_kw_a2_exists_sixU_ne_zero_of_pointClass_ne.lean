import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_chartEval_equation_and_apply_self_eq_one
import Theorems.Thm_WeierstrassProjModel_kw_a2_productMap_sixU_inl_eq_neg_add
import Theorems.Thm_WeierstrassProjModel_kw_a2_add_ne_zero_of_pointClass_ne
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem solution (hΔ : algebraMap R F W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F)
    (hne : (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : WeierstrassCurve.Projective.PointClass F)
           ≠ ⟦kw_lrApt_chartEval W F j ψⱼ⟧) :
    ∃ l, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l) ≠ 0 := by

  have hPe := chartEval_equation_and_apply_self_eq_one W F i ψᵢ
  have hQe := chartEval_equation_and_apply_self_eq_one W F j ψⱼ
  have hP0 : kw_lrApt_chartEval W F i ψᵢ ≠ 0 := by
    intro h
    exact one_ne_zero (hPe.2.symm.trans (congrFun h i))
  have hQ0 : kw_lrApt_chartEval W F j ψⱼ ≠ 0 := by
    intro h
    exact one_ne_zero (hQe.2.symm.trans (congrFun h j))

  obtain ⟨hbX, hbY, hbZ⟩ := kw_a2_productMap_sixU_inl_eq_neg_add W F i j ψᵢ ψⱼ

  rcases kw_a2_add_ne_zero_of_pointClass_ne W F hΔ
      (kw_lrApt_chartEval W F i ψᵢ) (kw_lrApt_chartEval W F j ψⱼ)
      hPe.1 hQe.1 hP0 hQ0 hne with h | h | h
  · exact ⟨.inl 0, fun habs => h (neg_eq_zero.mp (hbX.symm.trans habs))⟩
  · exact ⟨.inl 1, fun habs => h (neg_eq_zero.mp (hbY.symm.trans habs))⟩
  · exact ⟨.inl 2, fun habs => h (neg_eq_zero.mp (hbZ.symm.trans habs))⟩

end
