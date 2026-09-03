import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    LocallyQuasiFinite f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber.solution
