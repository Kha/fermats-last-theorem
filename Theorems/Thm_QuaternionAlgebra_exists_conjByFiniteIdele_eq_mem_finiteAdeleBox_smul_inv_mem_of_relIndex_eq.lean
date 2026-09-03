import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

theorem QuaternionAlgebra.exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁) (hΛ₂ : IsMaximalOrder Λ₂)
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (hN : (Λ₁ ⊓ Λ₂).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) :
    ∃ m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, Submodule.conjByFiniteIdele Λ₁ m = Λ₂ ∧
      ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ ∧
      ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq.solution
