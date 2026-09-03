import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FormallyUnramified_of_forall_pullback_snd_localization_atPrime

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.FormallyUnramified.of_forall_pullback_snd_localization_atPrime
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    (H : ∀ (p : Ideal R) [p.IsPrime],
      FormallyUnramified (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
    FormallyUnramified g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FormallyUnramified_of_forall_pullback_snd_localization_atPrime.solution
