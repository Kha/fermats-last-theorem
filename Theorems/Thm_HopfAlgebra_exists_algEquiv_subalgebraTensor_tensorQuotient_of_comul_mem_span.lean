import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span
    {k : Type u} [CommRing k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    ∃ β : (H ⊗[↥K] H) ≃ₐ[H]
        (H ⊗[k] (H ⧸ Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})),
      ∀ h₁ h₂ : H, β (h₁ ⊗ₜ[↥K] h₂) =
        (h₁ ⊗ₜ[k] (1 : H ⧸ Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0})) *
          Algebra.TensorProduct.map (AlgHom.id k H)
            (Ideal.Quotient.mkₐ k (Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}))
            (Coalgebra.comul (R := k) h₂) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span.solution
