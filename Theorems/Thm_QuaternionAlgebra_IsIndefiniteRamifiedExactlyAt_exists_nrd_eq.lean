import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_nrd_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion
p2m_open "QuaternionAlgebra~forall_isUnit_iff_forall_normForm_eq_zero"

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_nrd_eq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q') (t : ℚ) (ht : t ≠ 0) :
    ∃ γ : ℍ[ℚ, a, b], nrd γ = t := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_nrd_eq.solution
