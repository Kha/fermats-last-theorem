import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff

theorem ValuationSubring.mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff
    (K K' : Type) [Field K] [Field K'] (ι : K →+* K')
    (W : ValuationSubring K) (W' : ValuationSubring K')
    (h : ∀ f : K, f ∈ W ↔ ι f ∈ W') (f : K) :
    f ∈ W.nonunits ↔ ι f ∈ W'.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff.solution
