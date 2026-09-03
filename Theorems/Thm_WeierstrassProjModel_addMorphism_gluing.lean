import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_addMorphism_gluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.addMorphism_gluing.{u} {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Invertible (2 : R)] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    KwLRSixUCoverage W ∧ KwLRPerChartCompat W ∧ KwLROuterCompat W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_gluing.solution
