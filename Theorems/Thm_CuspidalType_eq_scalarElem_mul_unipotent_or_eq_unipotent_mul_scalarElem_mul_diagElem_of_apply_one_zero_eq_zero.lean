import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
    (q : ℕ) [Fact q.Prime]
    (b : GL2 q) (hb : (b : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0) :
    (∃ (c : (ZMod q)ˣ) (t : ZMod q), b = scalarElem q c * unipotent q t) ∨
    (∃ (a d : (ZMod q)ˣ) (s : ZMod q), a ≠ d ∧ b = unipotent q s * (scalarElem q d * diagElem q (a * d⁻¹))) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero.solution
