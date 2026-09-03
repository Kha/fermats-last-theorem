import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical

set_option autoImplicit false

theorem ValuationSubring.eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical
    {K : Type*} [Field K] (V W : ValuationSubring K) (hVW : V ≤ W)
    (x : ↥V) (hxW : (x : K) ∈ W.nonunits)
    (hrad : IsLocalRing.maximalIdeal ↥V ≤ (Ideal.span {x}).radical) :
    V = W := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical.solution
