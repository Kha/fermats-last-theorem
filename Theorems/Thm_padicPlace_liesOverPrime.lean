import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_padicPlace_liesOverPrime

set_option autoImplicit false
theorem padicPlace_liesOverPrime (p : ℕ) [Fact p.Prime] :
    (padicPlace p).LiesOverPrime p := by p2m_exact_reverting @_root_.P2MW.S_padicPlace_liesOverPrime.solution
