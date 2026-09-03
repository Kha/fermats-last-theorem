import Mathlib
import Definitions.Def_QuaternionAlgebra_BaseChange
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv

open scoped TensorProduct Quaternion

theorem solution
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [Ring T] [Algebra S T]
    {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S}
    (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂) (h₃ : algebraMap R S c₃ = d₃)
    (ψ : ℍ[S,d₁,d₂,d₃] ≃ₐ[S] T) :
    ∃ φ : ℍ[R,c₁,c₂,c₃] ⊗[R] S ≃+* T,
      (∀ r : S, φ ((1 : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] r) = r • (1 : T)) ∧
      ∀ (x : ℍ[R,c₁,c₂,c₃]) (r : S), φ (x ⊗ₜ[R] r) =
        r • ψ ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ, algebraMap R S x.imK⟩ := by
  refine ⟨(QuaternionAlgebra.baseChangeRight h₁ h₂ h₃).toRingEquiv.trans ψ.toRingEquiv,
    fun r => ?_, fun x r => ?_⟩
  · show ψ (QuaternionAlgebra.baseChangeRight h₁ h₂ h₃ ((1 : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] r)) = r • (1 : T)
    rw [QuaternionAlgebra.baseChangeRight_one_tmul, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]
  · show ψ (QuaternionAlgebra.baseChangeRight h₁ h₂ h₃ (x ⊗ₜ[R] r)) = _
    rw [QuaternionAlgebra.baseChangeRight_tmul, ← map_smul]
    congr 1
