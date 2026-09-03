import Mathlib
import P2M.Util
import P2M.Sol.S_orderOf_unitOfCoprime_pow_sub_one

set_option autoImplicit false

open Polynomial
theorem orderOf_unitOfCoprime_pow_sub_one (Q n : ℕ) (hQ : 1 < Q) (hn : 0 < n)
    (h : Q.Coprime (Q ^ n - 1)) : orderOf (ZMod.unitOfCoprime Q h) = n := by p2m_exact_reverting @_root_.P2MW.S_orderOf_unitOfCoprime_pow_sub_one.solution
