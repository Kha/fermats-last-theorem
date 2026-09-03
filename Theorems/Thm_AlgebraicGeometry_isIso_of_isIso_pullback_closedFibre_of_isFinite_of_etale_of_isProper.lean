import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (hk : IsIso (pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))) :
    IsIso π := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper.solution
