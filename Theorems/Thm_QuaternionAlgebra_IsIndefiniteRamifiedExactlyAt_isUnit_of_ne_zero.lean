import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero {a b : ℚ} {q q' : ℕ}
    [Fact q.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (x : ℍ[ℚ, a, b]) (hx : x ≠ 0) : IsUnit x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero.solution
