import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three
    (q : ℕ) (hq : q.Prime) (h3 : q % 4 = 3) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-(q : ℚ)) q := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three.solution
