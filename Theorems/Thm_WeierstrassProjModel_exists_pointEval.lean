import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_pointEval

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.exists_pointEval.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (hΔF : algebraMap R F W.Δ ≠ 0) :
    (∀ x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective),
        ∃ (i : Fin 3) (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F),
          x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
            (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    ∧ (∀ (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
        (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F),
        x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
          (projModelAffineOpenCoverCR R W.toProjective).openCover.f i →
        ∀ k : Fin 3, kw_lrApt_chartEval W F i ψ k ≠ 0 →
          ∃ ψ' : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F,
            x.1 = Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫
              (projModelAffineOpenCoverCR R W.toProjective).openCover.f k)
    ∧ ∃ e : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective) → (kw_lrApt_WF W F).Point,
        Function.Injective e ∧
        ∀ (x : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)) (i : Fin 3)
          (ψ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F),
          x.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
            (projModelAffineOpenCoverCR R W.toProjective).openCover.f i →
          (e x).point = (⟦kw_lrApt_chartEval W F i ψ⟧ : WeierstrassCurve.Projective.PointClass F) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_pointEval.solution
