import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_addMorphism_negMor_mul

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel~negMor_over"

theorem WeierstrassProjModel.addMorphism_negMor_mul.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ)
    (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
    (hnego : kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective = projModelStrCR W.toProjective) :
    pullback.lift (kw_lrAddNegDiag_negMor W) (𝟙 (projModelCR W.toProjective))
        (by rw [hnego, Category.id_comp])
      ≫ kw_lrAddMorphism W hcov hcompat houter
    = projModelStrCR W.toProjective ≫ (kwZeroSect R W).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_addMorphism_negMor_mul.solution
