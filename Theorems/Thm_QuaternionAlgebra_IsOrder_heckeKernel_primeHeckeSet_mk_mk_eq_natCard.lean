import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_heckeKernel_primeHeckeSet_mk_mk_eq_natCard

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.heckeKernel_primeHeckeSet_mk_mk_eq_natCard {a b : ℚ}
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (ℓ : ℕ)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    QuaternionAlgebra.heckeKernel (Submodule.finiteIdeleStabilizer R) (QuaternionAlgebra.primeHeckeSet R ℓ)
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) y) =
      Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (∃ h ∈ QuaternionAlgebra.primeHeckeSet R ℓ, J = Submodule.ofFiniteIdele R (x * h)) ∧
          ∃ d : (ℍ[ℚ, a, b])ˣ, J = d • Submodule.ofFiniteIdele R y} := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_heckeKernel_primeHeckeSet_mk_mk_eq_natCard.solution
