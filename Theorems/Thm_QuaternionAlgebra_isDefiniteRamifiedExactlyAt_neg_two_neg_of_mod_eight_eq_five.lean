import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
    (q : ℕ) (hq : q.Prime) (h5 : q % 8 = 5) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-2 : ℚ) (-(q : ℚ)) q := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five.solution
