import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq
    (q : ℕ) [Fact q.Prime]
    :
    Nat.card {g : GL2 q // g ∉ Subgroup.center (GL2 q) ∧
      ∃ z : ZMod q, (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = (X - C z) ^ 2} = (q - 1) * (q ^ 2 - 1) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_natCard_not_mem_center_and_charpoly_eq_X_sub_C_sq.solution
