import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isOrder_toIntSubmodule_range_comp_includeRight
    (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    {a b : ℚ} (e : ℚ ⊗[ℤ] O ≃ₐ[ℚ] ℍ[ℚ, a, b]) :
    Function.Injective
        ((e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
          (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom) ∧
      QuaternionAlgebra.IsOrder (AddSubgroup.toIntSubmodule
        ((e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
          (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom).range.toAddSubgroup) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight.solution
