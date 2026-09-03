import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
    {L : Type} [Field L] (A : ValuationSubring L)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀]
    (ι : A₀ →+* ↥A) (hι : Function.Injective ι)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hGI : GeometricallyIntegral
      (Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀)))))) :
    IsIntegral ↑(Limits.pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap ↥A L)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback.solution
