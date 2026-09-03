import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding isIntegral_of_smooth_of_preconnectedSpace

theorem AlgebraicGeometry.isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd
    {R K L : Type u} [CommRing R] [Field K] [Field L] (i : R →+* K) (j : K →+* L)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom i)))]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom i)))] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_pullback_of_geometricallyConnected_of_smooth_pullback_snd.solution
