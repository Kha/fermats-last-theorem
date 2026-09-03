import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
    {a b : ℚ} (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hO : QuaternionAlgebra.IsOrder O)
    (hOΛ : O ≤ Λ) (ℓ : ℕ)
    {u h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer O)
    (hh : h ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ) :
    u * h ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ ∧ h * u ∈ CerednikDrinfeld.levelHeckeUSet Λ O ℓ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer.solution
