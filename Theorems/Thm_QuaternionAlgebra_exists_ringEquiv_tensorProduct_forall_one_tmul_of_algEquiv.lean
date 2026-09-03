import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

open scoped TensorProduct Quaternion

theorem QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [Ring T] [Algebra S T]
    {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S}
    (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂) (h₃ : algebraMap R S c₃ = d₃)
    (ψ : ℍ[S,d₁,d₂,d₃] ≃ₐ[S] T) :
    ∃ φ : ℍ[R,c₁,c₂,c₃] ⊗[R] S ≃+* T,
      (∀ r : S, φ ((1 : ℍ[R,c₁,c₂,c₃]) ⊗ₜ[R] r) = r • (1 : T)) ∧
      ∀ (x : ℍ[R,c₁,c₂,c₃]) (r : S), φ (x ⊗ₜ[R] r) =
        r • ψ ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ, algebraMap R S x.imK⟩ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv.solution
