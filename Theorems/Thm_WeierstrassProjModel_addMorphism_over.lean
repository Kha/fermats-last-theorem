import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_addMorphism_over

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_over.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    kw_lrAddMorphism W hcov hcompat houter ≫ projModelStrCR W.toProjective
      = pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_over.solution
