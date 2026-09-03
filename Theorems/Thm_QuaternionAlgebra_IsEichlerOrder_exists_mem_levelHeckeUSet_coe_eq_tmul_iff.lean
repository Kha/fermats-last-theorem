import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_levelHeckeUSet_coe_eq_tmul_iff

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.exists_mem_levelHeckeUSet_coe_eq_tmul_iff
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : (ℍ[ℚ, a, b])ˣ) (hxR : (x : ℍ[ℚ, a, b]) ∈ R) (hnx : nrd (x : ℍ[ℚ, a, b]) = (ℓ : ℚ)) :
    (∃ h ∈ levelHeckeUSet Λ R ℓ,
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ↔
      (¬ ∀ z : ℍ[ℚ, a, b], ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * (x : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
      (¬ ∀ r ∈ R, ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * (x : ℍ[ℚ, a, b]) ∈ Λ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_levelHeckeUSet_coe_eq_tmul_iff.solution
