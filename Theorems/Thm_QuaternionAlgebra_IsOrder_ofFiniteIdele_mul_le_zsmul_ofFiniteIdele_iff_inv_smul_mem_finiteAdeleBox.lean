import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (n : ℕ) [NeZero n] :
    Submodule.ofFiniteIdele Λ (x * g) ≤ ((n : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ x ↔
      (n : ℚ)⁻¹ • ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox.solution
