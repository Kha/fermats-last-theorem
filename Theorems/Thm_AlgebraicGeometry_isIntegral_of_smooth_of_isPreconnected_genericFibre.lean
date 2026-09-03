import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_smooth_of_isPreconnected_genericFibre

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.isIntegral_of_smooth_of_isPreconnected_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [Smooth g] [QuasiCompact g]
    [Nonempty ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (hconn : _root_.IsPreconnected
      (Set.univ : Set ↑(pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K)))))) :
    IsIntegral G := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_isPreconnected_genericFibre.solution
