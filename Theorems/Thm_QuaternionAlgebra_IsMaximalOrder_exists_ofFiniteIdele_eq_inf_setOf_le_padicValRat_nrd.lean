import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve

theorem QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : Submodule.ofFiniteIdele Λ x ≤ Λ) :
    ∃ (k : ℕ) (x₀ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      Submodule.ofFiniteIdele Λ x₀ ≤ Λ ∧
      (∃ h ∈ Submodule.ofFiniteIdele Λ x₀, padicValRat q' (QuaternionAlgebra.nrd h) = 0 ∧ h ≠ 0) ∧
      (Submodule.ofFiniteIdele Λ x : Set ℍ[ℚ, a, b]) =
        (Submodule.ofFiniteIdele Λ x₀ : Set ℍ[ℚ, a, b]) ∩
          {h | h ∈ Λ ∧ (h = 0 ∨ (k : ℤ) ≤ padicValRat q' (QuaternionAlgebra.nrd h))} := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd.solution
