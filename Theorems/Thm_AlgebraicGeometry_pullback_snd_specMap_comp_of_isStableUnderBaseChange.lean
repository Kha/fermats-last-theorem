import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.pullback_snd_specMap_comp_of_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (i : R →+* S) (j : S →+* T)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : P (pullback.snd f (Spec.map (CommRingCat.ofHom i)))) :
    P (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange.solution
