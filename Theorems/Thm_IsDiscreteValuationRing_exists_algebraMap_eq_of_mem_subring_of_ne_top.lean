import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_algebraMap_eq_of_mem_subring_of_ne_top
    (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]
    (W : Subring K) (hVW : ∀ v : V, algebraMap V K v ∈ W) (hW : W ≠ ⊤) (x : K) (hx : x ∈ W) :
    ∃ v : V, algebraMap V K v = x := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top.solution
