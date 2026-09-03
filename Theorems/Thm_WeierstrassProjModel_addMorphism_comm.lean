import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_addMorphism_comm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_comm.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback.lift (pullback.snd (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective))
        pullback.condition.symm
      ≫ kw_lrAddMorphism W hcov hcompat houter = kw_lrAddMorphism W hcov hcompat houter := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_comm.solution
