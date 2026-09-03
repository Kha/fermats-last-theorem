import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ) (hnrd : nrd x = (ℓ : ℚ)) :
    ∃ h ∈ primeHeckeSet Λ ℓ,
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq.solution
