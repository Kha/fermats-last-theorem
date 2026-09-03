import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsIntegral X] [Flat f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_pullback_specMap_algebraMap_of_isFractionRing_of_flat.solution
