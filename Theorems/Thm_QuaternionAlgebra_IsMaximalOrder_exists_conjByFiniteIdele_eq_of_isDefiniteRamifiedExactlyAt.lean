import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_conjByFiniteIdele_eq_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsMaximalOrder.exists_conjByFiniteIdele_eq_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    {Λ₀ Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₀ : QuaternionAlgebra.IsMaximalOrder Λ₀) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    ∃ y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, Submodule.conjByFiniteIdele Λ₀ y = Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_conjByFiniteIdele_eq_of_isDefiniteRamifiedExactlyAt.solution
