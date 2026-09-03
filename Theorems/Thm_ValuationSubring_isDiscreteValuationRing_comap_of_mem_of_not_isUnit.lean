import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_comap_of_mem_of_not_isUnit
    (K F : Type) [Field K] [Field F] (W : ValuationSubring K) [IsDiscreteValuationRing ↥W]
    (ι : F →+* K) (t : F) (ht : ι t ∈ W) (ht' : ¬ IsUnit (⟨ι t, ht⟩ : ↥W)) (ht0 : t ≠ 0) :
    IsDiscreteValuationRing ↥(W.comap ι) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_mem_of_not_isUnit.solution
