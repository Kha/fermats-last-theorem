import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R K r ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.solution
