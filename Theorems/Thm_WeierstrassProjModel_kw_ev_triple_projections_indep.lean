import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_ev_triple_projections_indep

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
theorem WeierstrassProjModel.kw_ev_triple_projections_indep
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] :
    haveI : Smooth (projModelStrCR W.toProjective) :=
      (projModelStrCR_smoothOfRelativeDimension_one W.toProjective).smooth
    haveI : GeometricallyIntegral (projModelStrCR W.toProjective) :=
      kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)
    let X3 : Scheme.{u} :=
      pullback (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
    haveI : IsIntegral X3 := by
      haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
        LocallyOfFiniteType.isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : IsIntegral (projModelCR W.toProjective) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (projModelStrCR W.toProjective)
      haveI : GeometricallyIntegral (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      haveI : IsIntegral ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : IsLocallyNoetherian ↑(pullback (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
      haveI : GeometricallyIntegral (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)) :=
        MorphismProperty.pullback_fst _ _ ‹GeometricallyIntegral (projModelStrCR W.toProjective)›
      exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
    letI : Algebra R X3.functionField :=
      (Spec.preimage (X3.fromSpecStalk (genericPoint X3)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective)).hom.toAlgebra
    have hΔF : algebraMap R X3.functionField W.Δ ≠ 0 := (W.isUnit_Δ.map _).ne_zero
    have halg : X3.fromSpecStalk (genericPoint X3)
        ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R X3.functionField)) := by
      show X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective
        = Spec.map (CommRingCat.ofHom (algebraMap R X3.functionField))
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hpr1 : (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)
        ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        ≫ projModelStrCR W.toProjective
      = pullback.snd (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective :=
      (Category.assoc _ _ _).trans pullback.condition
    have hpr2 : (pullback.fst (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective)
        ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        ≫ projModelStrCR W.toProjective
      = pullback.snd (pullback.fst (projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
          (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective :=
      (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition)
    let e := (exists_pointEval W X3.functionField hΔF).2.2.choose
    let a : (kw_lrApt_WF W X3.functionField).Point :=
      e ⟨X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective),
        by rw [Category.assoc, hpr1]; exact halg⟩
    let b : (kw_lrApt_WF W X3.functionField).Point :=
      e ⟨X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective),
        by rw [Category.assoc, hpr2]; exact halg⟩
    let c : (kw_lrApt_WF W X3.functionField).Point :=
      e ⟨X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective),
        by rw [Category.assoc]; exact halg⟩
    a ≠ b ∧ b ≠ c ∧ a + b ≠ c ∧ a ≠ b + c := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_indep.solution
