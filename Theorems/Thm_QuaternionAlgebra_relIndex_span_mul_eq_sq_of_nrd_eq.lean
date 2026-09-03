import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_relIndex_span_mul_eq_sq_of_nrd_eq

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.relIndex_span_mul_eq_sq_of_nrd_eq
    {a b : ℚ} (A : Submodule ℤ ℍ[ℚ, a, b]) (hAfg : A.FG) (hAspan : Submodule.span ℚ (A : Set ℍ[ℚ, a, b]) = ⊤)
    (x : ℍ[ℚ, a, b]) (hx : ∀ y ∈ A, y * x ∈ A) (n : ℕ) (hn : nrd x = (n : ℚ) ∨ nrd x = -(n : ℚ)) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => y * x) '' (A : Set ℍ[ℚ, a, b]))).toAddSubgroup.relIndex A.toAddSubgroup = n ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_relIndex_span_mul_eq_sq_of_nrd_eq.solution
