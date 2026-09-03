import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_negMor_chartFactor

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.negMor_chartFactor.{u} {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F] :
    ∃ ν : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)))
        →ₐ[R] (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R))),
      (∀ (ψ : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R))) →ₐ[R] F)
        (φ : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)),
        φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) →
        φ.1 ≫ kw_lrAddNegDiag_negMor W
          = Spec.map (CommRingCat.ofHom (ψ.comp ν).toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3))
      ∧ ∀ (ψ : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R))) →ₐ[R] F),
        kw_lrApt_chartEval W F 2 (ψ.comp ν)
          = (kw_lrApt_WF W F).neg (kw_lrApt_chartEval W F 2 ψ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_negMor_chartFactor.solution
