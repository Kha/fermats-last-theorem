import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem {a b : ℚ}
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hT : ∀ u ∈ Submodule.finiteIdeleStabilizer R, ∀ h ∈ T, u * h ∈ T)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    QuaternionAlgebra.heckeKernel (Submodule.finiteIdeleStabilizer R) T
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) y) =
      Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (∃ h ∈ T, J = Submodule.ofFiniteIdele R (x * h)) ∧
          ∃ d : (ℍ[ℚ, a, b])ˣ, J = d • Submodule.ofFiniteIdele R y} := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_heckeKernel_mk_mk_eq_natCard_of_forall_mul_mem.solution
