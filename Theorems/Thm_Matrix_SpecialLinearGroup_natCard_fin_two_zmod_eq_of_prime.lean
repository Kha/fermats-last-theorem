import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime

set_option autoImplicit false

theorem Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime.solution
