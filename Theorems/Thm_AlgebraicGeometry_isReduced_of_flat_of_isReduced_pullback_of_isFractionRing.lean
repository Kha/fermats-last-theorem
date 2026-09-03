import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_of_flat_of_isReduced_pullback_of_isFractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsReduced X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing.solution
