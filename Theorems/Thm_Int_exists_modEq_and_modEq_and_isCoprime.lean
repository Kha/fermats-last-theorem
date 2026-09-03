import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import P2M.Util
import P2M.Sol.S_Int_exists_modEq_and_modEq_and_isCoprime

theorem Int.exists_modEq_and_modEq_and_isCoprime {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by p2m_exact_reverting @_root_.P2MW.S_Int_exists_modEq_and_modEq_and_isCoprime.solution
