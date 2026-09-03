import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open IsDedekindDomain

theorem QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.finiteAdeleBox (Λ ⊓ Submodule.conjByFiniteIdele Λ m) =
        Submodule.finiteAdeleBox Λ ⊓
          (Submodule.finiteAdeleBox Λ).map
            ((AddMonoidHom.mulRight ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
                ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).comp
              (AddMonoidHom.mulLeft (m : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) ∧
      (∀ N : ℕ,
        ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
            Submodule.finiteAdeleBox Λ →
          ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ →
        ∀ w ∈ Submodule.finiteAdeleBox Λ,
          ((N : ℕ) : ℚ) • w ∈ Submodule.finiteAdeleBox (Λ ⊓ Submodule.conjByFiniteIdele Λ m)) ∧
      Submodule.finiteIdeleStabilizer (Λ ⊓ Submodule.conjByFiniteIdele Λ m) ≤ Submodule.finiteIdeleStabilizer Λ ∧
      (∀ u ∈ Submodule.finiteIdeleStabilizer (Λ ⊓ Submodule.conjByFiniteIdele Λ m),
        m⁻¹ * u * m ∈ Submodule.finiteIdeleStabilizer Λ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le.solution
