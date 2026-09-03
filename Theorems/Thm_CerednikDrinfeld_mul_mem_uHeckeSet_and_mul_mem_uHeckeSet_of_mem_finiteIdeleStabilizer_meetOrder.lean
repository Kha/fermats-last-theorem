import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_mul_mem_uHeckeSet_and_mul_mem_uHeckeSet_of_mem_finiteIdeleStabilizer_meetOrder

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.mul_mem_uHeckeSet_and_mul_mem_uHeckeSet_of_mem_finiteIdeleStabilizer_meetOrder
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ)
    {u h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
    (hh : h ∈ CerednikDrinfeld.uHeckeSet R n q) :
    u * h ∈ CerednikDrinfeld.uHeckeSet R n q ∧ h * u ∈ CerednikDrinfeld.uHeckeSet R n q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_mul_mem_uHeckeSet_and_mul_mem_uHeckeSet_of_mem_finiteIdeleStabilizer_meetOrder.solution
