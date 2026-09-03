import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
set_option autoImplicit false
universe u v
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
    (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] (x : L) (hx : Transcendental K x) :
    ∃ e : ↥(IntermediateField.adjoin K ({x} : Set L)) ≃ₐ[K] RatFunc K,
      e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ = RatFunc.X := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental.solution
