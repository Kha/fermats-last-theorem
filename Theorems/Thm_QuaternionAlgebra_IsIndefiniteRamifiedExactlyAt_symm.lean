import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_symm

set_option autoImplicit false

open scoped Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.symm {a b : ℚ} {q q' : ℕ}
    (h : IsIndefiniteRamifiedExactlyAt a b q q') : IsIndefiniteRamifiedExactlyAt a b q' q := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_symm.solution
