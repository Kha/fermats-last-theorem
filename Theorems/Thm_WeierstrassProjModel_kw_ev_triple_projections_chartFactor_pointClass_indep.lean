import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_pointEval
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
theorem WeierstrassProjModel.kw_ev_triple_projections_chartFactor_pointClass_indep
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
    ∃ (ia : Fin 3) (ψa : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ia : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField)
      (ib : Fin 3) (ψb : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ib : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField)
      (ic : Fin 3) (ψc : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X ic : MvPolynomial (Fin 3) R)) →ₐ[R] X3.functionField),
      (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψa.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ia)
      ∧ (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.fst (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
          ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψb.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ib)
      ∧ (X3.fromSpecStalk (genericPoint X3)
          ≫ pullback.snd (pullback.fst (projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective) ≫ projModelStrCR W.toProjective)
              (projModelStrCR W.toProjective)
        = Spec.map (CommRingCat.ofHom ψc.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f ic)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧)
      ∧ ((kw_lrApt_WF W X3.functionField).addMap
            ⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
          ≠ ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧)
      ∧ ((⟦kw_lrApt_chartEval W X3.functionField ia ψa⟧
            : WeierstrassCurve.Projective.PointClass X3.functionField)
          ≠ (kw_lrApt_WF W X3.functionField).addMap
              ⟦kw_lrApt_chartEval W X3.functionField ib ψb⟧
              ⟦kw_lrApt_chartEval W X3.functionField ic ψc⟧) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_ev_triple_projections_chartFactor_pointClass_indep.solution
