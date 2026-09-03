import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_productMap_sixU_inl_eq_neg_add

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
theorem WeierstrassProjModel.kw_a2_productMap_sixU_inl_eq_neg_add
    (i j : Fin 3) (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    let P := kw_lrApt_chartEval W F i ψᵢ
    let Q := kw_lrApt_chartEval W F j ψⱼ
    (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl 0))
        = -(kw_lrApt_WF W F).addX P Q
    ∧ (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl 1))
        = -(kw_lrApt_WF W F).addY P Q
    ∧ (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl 2))
        = -(kw_lrApt_WF W F).addZ P Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_productMap_sixU_inl_eq_neg_add.solution
