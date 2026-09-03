import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Theorems.Thm_WeierstrassProjModel_kw_a2_checks
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_kw_a2_productMap_sixU_inl_eq_neg_add

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

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

theorem solution (i j : Fin 3) (ψᵢ : (𝒜 i) →ₐ[R] F) (ψⱼ : (𝒜 j) →ₐ[R] F) :
    let P := kw_lrApt_chartEval W F i ψᵢ
    let Q := kw_lrApt_chartEval W F j ψⱼ
    (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl 0))
        = -(kw_lrApt_WF W F).addX P Q
    ∧ (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl 1))
        = -(kw_lrApt_WF W F).addY P Q
    ∧ (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl 2))
        = -(kw_lrApt_WF W F).addZ P Q := by
  intro P Q

  have hkey : ∀ p, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrChart_ev W i j p)
      = MvPolynomial.aeval (R := R) (Sum.elim P Q) p := by
    suffices h : (Algebra.TensorProduct.productMap ψᵢ ψⱼ).comp (kw_lrChart_ev W i j)
        = MvPolynomial.aeval (R := R) (Sum.elim P Q) from DFunLike.congr_fun h
    refine MvPolynomial.algHom_ext fun s => ?_
    rcases s with m | m
    · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inl,
        kw_lrChart_inL, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.productMap_left_apply]
      rfl
    · simp only [AlgHom.comp_apply, kw_lrChart_ev, aeval_X, Sum.elim_inr,
        kw_lrChart_inR, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.productMap_right_apply]
      rfl

  have hev : ∀ k, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j (.inl k))
      = MvPolynomial.aeval (R := R) (Sum.elim P Q) (kw_lrAdd_vec W k) := by
    intro k
    show (Algebra.TensorProduct.productMap ψᵢ ψⱼ)
        (kw_lrChart_u W i j k) = _
    rw [kw_lrChart_u, kw_lrChart_ev', Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact hkey (kw_lrAdd_vec W k)
  obtain ⟨hX, hY, hZ, -, -⟩ := kw_a2_checks W F
  refine ⟨?_, ?_, ?_⟩
  · rw [hev 0]; exact hX P Q
  · rw [hev 1]; exact hY P Q
  · rw [hev 2]; exact hZ P Q

end
