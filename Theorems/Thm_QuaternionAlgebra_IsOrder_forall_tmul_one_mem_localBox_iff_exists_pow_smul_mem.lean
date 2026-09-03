import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
    {a₁ b₁ : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ : IsOrder Λ)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (y : ℍ[ℚ, a₁, b₁]) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w) ↔
      ∃ K : ℕ, ((r ^ K : ℕ) : ℚ) • y ∈ Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem.solution
