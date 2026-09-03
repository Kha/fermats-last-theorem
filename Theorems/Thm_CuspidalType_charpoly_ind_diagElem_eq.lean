import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_charpoly_ind_diagElem_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_ind_diagElem_eq
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (a : (ZMod q)ˣ) (ha : a ≠ 1) :
    LinearMap.charpoly (ind q K (diagElem q a)) = (X - 1) ^ 2 * (X ^ orderOf a - 1) ^ ((q - 1) / orderOf a) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_charpoly_ind_diagElem_eq.solution
