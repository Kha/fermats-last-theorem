import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (g : X ⟶ Y) (hg : g ≫ pY = pX)
    [Flat pX] [LocallyOfFinitePresentation pX] [LocallyOfFinitePresentation pY]
    (hfib : ∀ s : S, Flat (pullback.snd g (pY.fiberι s))) :
    Flat g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre.solution
