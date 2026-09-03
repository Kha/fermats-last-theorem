import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_charpoly_ind_unipotent_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_ind_unipotent_eq
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (t : ZMod q) (ht : t ≠ 0) :
    LinearMap.charpoly (ind q K (unipotent q t)) = (X - 1) * (X ^ q - 1) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_charpoly_ind_unipotent_eq.solution
