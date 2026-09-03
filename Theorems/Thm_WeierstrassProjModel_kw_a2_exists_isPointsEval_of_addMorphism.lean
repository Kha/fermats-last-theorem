import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_exists_isPointsEval_of_addMorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_a2_exists_isPointsEval_of_addMorphism
    {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
      (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
    (G : RelativeGroupLaw R (projModelStrCR W.toProjective))
    (hGmul : (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫
            kw_lrAddMorphism W hcov hcompat houter))
    (hGone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1) :
    ∃ ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR W.toProjective) ≃
            (W.toProjective.baseChange F).toAffine.Point,
        IsPointsEval W.toProjective G ev := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_exists_isPointsEval_of_addMorphism.solution
