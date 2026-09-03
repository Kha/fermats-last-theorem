import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_Submodule_conjByFiniteIdele_inf_and_conjByFiniteIdele_mono
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion
attribute [-simp] Submodule.finiteAdeleEvalAt_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

theorem Submodule.conjByFiniteIdele_inf_and_conjByFiniteIdele_mono
    {a b : ℚ} (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hΛ' : IsOrder Λ')
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.conjByFiniteIdele (Λ ⊓ Λ') g = Submodule.conjByFiniteIdele Λ g ⊓ Submodule.conjByFiniteIdele Λ' g ∧
    (Λ ≤ Λ' → Submodule.conjByFiniteIdele Λ g ≤ Submodule.conjByFiniteIdele Λ' g) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_conjByFiniteIdele_inf_and_conjByFiniteIdele_mono.solution
