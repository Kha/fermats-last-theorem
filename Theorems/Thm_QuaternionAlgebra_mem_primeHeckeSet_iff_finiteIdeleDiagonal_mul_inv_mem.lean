import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ ↔
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * h⁻¹ ∈
        QuaternionAlgebra.primeHeckeSet Λ ℓ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem.solution
