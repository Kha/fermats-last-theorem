import Mathlib
import P2M.Util
import P2M.Sol.S_IsGalois_exists_basis_baseChange_forall_apply_eq_self

set_option autoImplicit false

open scoped TensorProduct

theorem IsGalois.exists_basis_baseChange_forall_apply_eq_self
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i := by p2m_exact_reverting @_root_.P2MW.S_IsGalois_exists_basis_baseChange_forall_apply_eq_self.solution
