import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra~forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero CerednikDrinfeld"

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {t s c' : ℚ} (hB : IsIndefiniteRamifiedExactlyAt t s r rbar)
    (hH' : IsDefiniteRamifiedExactlyAt t c' r) :
    IsDefiniteRamifiedExactlyAt t (s * c') rbar := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt.solution
