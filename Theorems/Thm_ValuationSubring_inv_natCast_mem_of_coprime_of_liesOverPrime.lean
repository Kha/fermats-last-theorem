import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime

set_option autoImplicit false

theorem ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime
    {L : Type*} [Field L] (A : ValuationSubring L) {p : ℕ} (hA : A.LiesOverPrime p) {n : ℕ} (hn : n.Coprime p) :
    ((n : L))⁻¹ ∈ A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime.solution
