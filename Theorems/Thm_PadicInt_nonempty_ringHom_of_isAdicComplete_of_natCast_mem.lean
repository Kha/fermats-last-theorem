import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem PadicInt.nonempty_ringHom_of_isAdicComplete_of_natCast_mem
    (S : Type) [CommRing S] (I : Ideal S) [IsAdicComplete I S]
    (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ I) :
    Nonempty (ℤ_[p] →+* S) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem.solution
