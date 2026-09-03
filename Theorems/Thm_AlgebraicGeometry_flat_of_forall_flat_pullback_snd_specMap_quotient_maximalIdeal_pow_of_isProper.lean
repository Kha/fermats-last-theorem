import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hflat : ∀ n : ℕ,
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))))) :
    Flat f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_of_forall_flat_pullback_snd_specMap_quotient_maximalIdeal_pow_of_isProper.solution
