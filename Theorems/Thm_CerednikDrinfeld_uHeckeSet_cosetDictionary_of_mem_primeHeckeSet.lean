import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
    {a b : ℚ} (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ primeHeckeSet R q) :
    Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R ∧
    uHeckeSet R n q ⊆ primeHeckeSet R q ∧
    (∀ h ∈ uHeckeSet R n q, h⁻¹ * n ∉ Submodule.finiteIdeleStabilizer R) ∧
    (∀ h ∈ uHeckeSet R n q, ∀ h' ∈ uHeckeSet R n q,
      h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R →
        h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) ∧
    (∀ g ∈ primeHeckeSet R q, g⁻¹ * n ∉ Submodule.finiteIdeleStabilizer R →
      ∃ h ∈ uHeckeSet R n q, g⁻¹ * h ∈ Submodule.finiteIdeleStabilizer R) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet.solution
