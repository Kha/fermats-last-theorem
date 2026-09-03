import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_addMorphism_assoc

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel~addMorphism_over"

theorem WeierstrassProjModel.addMorphism_assoc.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
    (hm : kw_lrAddMorphism W hcov hcompat houter ≫ projModelStrCR W.toProjective
      = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective) :
    pullback.lift
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ kw_lrAddMorphism W hcov hcompat houter)
        (pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (by rw [Category.assoc, hm]; exact pullback.condition)
      ≫ kw_lrAddMorphism W hcov hcompat houter
    = pullback.lift
        (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
            ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (pullback.lift
            (pullback.fst (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
                ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
              ≫ pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
            (pullback.snd (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
                ≫ projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
            ((Category.assoc _ _ _).trans
              ((congrArg (_ ≫ ·) pullback.condition.symm).trans pullback.condition))
          ≫ kw_lrAddMorphism W hcov hcompat houter)
        (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc]
            exact congrArg (_ ≫ ·) pullback.condition)
      ≫ kw_lrAddMorphism W hcov hcompat houter := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_assoc.solution
