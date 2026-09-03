import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele
    {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsOrder Λ₁)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ e : {c : ClassSet (Submodule.finiteIdeleStabilizer R) //
            classSetForget (Submodule.finiteIdeleStabilizer R) (Submodule.finiteIdeleStabilizer Λ₁) c =
              ClassSet.mk (Submodule.finiteIdeleStabilizer Λ₁) x} ≃
          Quot (fun J J' : {J : Submodule ℤ ℍ[ℚ, a, b] //
              ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁, J = Submodule.ofFiniteIdele Λ₁ (x * u * m)} =>
            ∃ δ : (ℍ[ℚ, a, b])ˣ,
              x⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x ∈ Submodule.finiteIdeleStabilizer Λ₁ ∧
              (J' : Submodule ℤ ℍ[ℚ, a, b]) = δ • (J : Submodule ℤ ℍ[ℚ, a, b])),
      ∀ (u : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
        (hu : u ∈ Submodule.finiteIdeleStabilizer Λ₁)
        (hc : classSetForget (Submodule.finiteIdeleStabilizer R) (Submodule.finiteIdeleStabilizer Λ₁)
            (ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * u)) =
          ClassSet.mk (Submodule.finiteIdeleStabilizer Λ₁) x),
        e ⟨ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * u), hc⟩ =
          Quot.mk _ ⟨Submodule.ofFiniteIdele Λ₁ (x * u * m), u, hu, rfl⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_fibre_classSetForget_equiv_quot_ofFiniteIdele_mul_of_eq_inf_conjByFiniteIdele.solution
