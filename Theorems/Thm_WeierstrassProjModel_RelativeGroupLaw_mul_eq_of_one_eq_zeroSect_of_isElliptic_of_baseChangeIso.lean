import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
attribute [-simp] GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
    (G₀ G₁ : RelativeGroupLaw R (projModelStrCR V))
    (hone₀ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1)
    (hone₁ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        (G₁.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) :
    ∀ (F : Type u) [Field F] [Algebra R F],
      ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V),
        G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q
          = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso.solution
