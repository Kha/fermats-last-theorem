import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_liftAddMor_factor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.kw_a2_liftAddMor_factor.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F]
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
    (houter : KwLROuterCompat W) (i j : Fin 3)
    (ψᵢ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X i : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (ψⱼ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X j : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (x y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (hfacx : x.1 = Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hfacy : y.1 = Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f j) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm)
        ≫ kw_lrAddMorphism W hcov hcompat houter
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap ψᵢ ψⱼ).toRingHom)
          ≫ kw_lrPerChart_toE W hcov hcompat i j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_liftAddMor_factor.solution
