import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (α : (GaloisField q 2)ˣ) :
    LinearMap.charpoly (ind q K (torus q α)) =
      (X ^ orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) - 1) ^
        ((q + 1) / orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α))) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.solution
