import Mathlib
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import P2M.Util
import P2M.Sol.S_NeronModelInfra_smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (a : Spec (CommRingCat.of R') ⟶ X)
    (hgen : a (⊥ : PrimeSpectrum R') ∈ f.smoothLocus) :
    smoothnessDefect f a = 0 ↔ a (IsLocalRing.closedPoint R') ∈ f.smoothLocus := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus.solution
