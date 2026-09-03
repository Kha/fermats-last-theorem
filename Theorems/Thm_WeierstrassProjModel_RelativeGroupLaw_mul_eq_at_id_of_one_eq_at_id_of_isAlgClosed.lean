import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
  GoodReductionJacobian WeierstrassProjModel

universe u
theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced ↑(pullback x x)]
    (G₁ G₂ : WeierstrassProjModel.RelativeGroupLaw K x)
    (h : G₁.one (𝟙 _) = G₂.one (𝟙 _)) :
    ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) x,
      G₁.mul (𝟙 _) P Q = G₂.mul (𝟙 _) P Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed.solution
