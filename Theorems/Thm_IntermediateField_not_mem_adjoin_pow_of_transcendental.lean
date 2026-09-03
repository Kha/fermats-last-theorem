import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_not_mem_adjoin_pow_of_transcendental

set_option autoImplicit false

universe u v
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem IntermediateField.not_mem_adjoin_pow_of_transcendental
    (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] (y : L) (hy : Transcendental K y)
    (n : ℕ) (hn : 2 ≤ n) :
    y ∉ IntermediateField.adjoin K ({y ^ n} : Set L) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_not_mem_adjoin_pow_of_transcendental.solution
