import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem Module.exists_basis_forall_semilinear_apply_eq_of_isGalois
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v))
    (hopen : ∀ v : V, ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ : L ≃ₐ[K] L, σ ∈ E.fixingSubgroup → ρ σ v = v) :
    ∃ b : Module.Basis (Fin (Module.finrank L V)) L V, ∀ (i : Fin (Module.finrank L V)) (σ : L ≃ₐ[K] L),
      ρ σ (b i) = b i := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois.solution
