import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_isUnitOf_conjByFiniteIdele_iff

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.isUnitOf_conjByFiniteIdele_iff
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (u : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.IsUnitOf (Submodule.conjByFiniteIdele Λ β) u ↔
      ∃ μ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, μ ∈ Submodule.finiteIdeleStabilizer Λ ∧
        u ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = (β : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * μ * ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_isUnitOf_conjByFiniteIdele_iff.solution
