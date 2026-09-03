import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt (q : ℕ) (hq : q.Prime) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt.solution
