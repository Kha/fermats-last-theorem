import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_genericFibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd f (specGenericFibreInclusion R K))] :
    SmoothOfRelativeDimension d f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_genericFibre.solution
