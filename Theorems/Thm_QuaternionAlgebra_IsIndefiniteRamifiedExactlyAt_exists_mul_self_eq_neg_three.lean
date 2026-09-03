import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_mul_self_eq_neg_three
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_mul_self_eq_neg_three
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b 2 3) :
    ∃ ξ : ℍ[ℚ, a, b], ξ * ξ = algebraMap ℚ ℍ[ℚ, a, b] (-3) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_mul_self_eq_neg_three.solution
