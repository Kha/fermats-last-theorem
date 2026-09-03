import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_comp_antipode_convMul_eq_one
set_option autoImplicit false
open scoped TensorProduct
theorem HopfAlgebra.exists_comp_antipode_convMul_eq_one
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : A →ₐ[K] L) :
    ∃ ν' : A →ₐ[K] L, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) ∧
      WithConv.toConv ν' * WithConv.toConv ν = 1 ∧ WithConv.toConv ν * WithConv.toConv ν' = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_comp_antipode_convMul_eq_one.solution
