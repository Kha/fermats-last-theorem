import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_span_fixedPoints_semilinear_eq_top

set_option autoImplicit false

theorem Submodule.span_fixedPoints_semilinear_eq_top
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v)) :
    Submodule.span L {v : V | ∀ σ : L ≃ₐ[K] L, ρ σ v = v} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_span_fixedPoints_semilinear_eq_top.solution
