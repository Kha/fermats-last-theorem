import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem

set_option autoImplicit false

theorem Ideal.eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem
    {B : Type*} [CommRing B] [IsNoetherianRing B] {π : B} {Q Q' : Ideal B}
    [Q.IsPrime] [Q'.IsPrime] (hle : Q' ≤ Q) (hπ : π ∈ Q')
    (h : ∀ p : Ideal B, p.IsPrime → p ≤ Q → (p ∈ minimalPrimes B ↔ π ∉ p)) : Q' = Q := by p2m_exact_reverting @_root_.P2MW.S_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem.solution
