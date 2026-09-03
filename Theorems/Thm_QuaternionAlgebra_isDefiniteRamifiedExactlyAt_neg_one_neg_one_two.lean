import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_one_two :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-1) 2 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two.solution
