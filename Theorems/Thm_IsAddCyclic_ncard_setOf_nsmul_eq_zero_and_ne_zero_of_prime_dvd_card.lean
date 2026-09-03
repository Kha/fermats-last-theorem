import Mathlib
import P2M.Util
import P2M.Sol.S_IsAddCyclic_ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card

set_option autoImplicit false

theorem IsAddCyclic.ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card
    (D : Type) [AddCommGroup D] [IsAddCyclic D] (m : ℕ) (hm : Nat.card D = m) (hm0 : m ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m) :
    {x : D | ℓ • x = 0 ∧ x ≠ 0}.ncard = ℓ - 1 := by p2m_exact_reverting @_root_.P2MW.S_IsAddCyclic_ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card.solution
