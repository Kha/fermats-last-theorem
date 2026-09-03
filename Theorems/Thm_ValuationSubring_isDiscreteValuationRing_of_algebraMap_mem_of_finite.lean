import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.solution
