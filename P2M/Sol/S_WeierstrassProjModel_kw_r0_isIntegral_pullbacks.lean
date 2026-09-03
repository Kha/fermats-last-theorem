import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_kw_r0_isIntegral_pullbacks

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem solution {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) :
    IsIntegral (projModelCR W.toProjective) ∧
    IsIntegral ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) ∧
    IsIntegral ↑(pullback
      (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫
        projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)) := by
  set q := projModelStrCR W.toProjective with hq
  haveI := hsm; haveI := hgi
  haveI hE : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian q
  haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  haveI hE2 : IsIntegral ↑(pullback q q) := by
    haveI : GeometricallyIntegral (pullback.fst q q) :=
      MorphismProperty.pullback_fst _ _ hgi
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst q q)
  haveI : IsLocallyNoetherian ↑(pullback q q) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst q q)
  haveI hE3 : IsIntegral ↑(pullback (pullback.fst q q ≫ q) q) := by
    haveI : GeometricallyIntegral (pullback.fst (pullback.fst q q ≫ q) q) :=
      MorphismProperty.pullback_fst _ _ hgi
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
      (pullback.fst (pullback.fst q q ≫ q) q)
  exact ⟨hE, hE2, hE3⟩
