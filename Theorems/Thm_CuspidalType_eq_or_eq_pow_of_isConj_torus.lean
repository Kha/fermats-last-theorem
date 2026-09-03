import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_eq_or_eq_pow_of_isConj_torus

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.eq_or_eq_pow_of_isConj_torus (q : ℕ) [Fact q.Prime] {α α' : (GaloisField q 2)ˣ}
    (h : IsConj (torus q α) (torus q α')) : α' = α ∨ α' = α ^ q := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_eq_or_eq_pow_of_isConj_torus.solution
