import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
    (q : ℕ) [Fact q.Prime]
    (g : GL2 q) (x : ZMod q)
    (hx : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ h : GL2 q, ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly.solution
