import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_uHeckeSet_subset_primeHeckeSet

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.uHeckeSet_subset_primeHeckeSet
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hn : IsEichlerOrder (meetOrder R n) (N * q)) :
    uHeckeSet R n q ⊆ primeHeckeSet R q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_uHeckeSet_subset_primeHeckeSet.solution
