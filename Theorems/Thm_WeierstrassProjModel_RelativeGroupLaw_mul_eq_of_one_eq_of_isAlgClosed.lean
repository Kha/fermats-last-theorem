import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
  GoodReductionJacobian WeierstrassProjModel

universe u
theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [IsReduced ↑(pullback
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))]
    (G₁ G₂ : WeierstrassProjModel.RelativeGroupLaw R f)
    (h : G₁.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        = G₂.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
        = G₂.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed.solution
