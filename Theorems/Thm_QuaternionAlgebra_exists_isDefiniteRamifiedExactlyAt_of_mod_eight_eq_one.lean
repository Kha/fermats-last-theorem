import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one
    (q : ℕ) (hq : q.Prime) (h1 : q % 8 = 1) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one.solution
