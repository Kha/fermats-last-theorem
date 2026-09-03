import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_MonoidHom_det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj
set_option autoImplicit false

theorem MonoidHom.det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj
    (p : ℕ) (hp2 : p ≠ 2) (F : Type) [Field F] [CharP F p]
    (ρ₁ ρ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (S : Finset ℕ)
    (hdense : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
        (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
          g * τ * g⁻¹ * σ⁻¹ ∈ ρ₁.ker ⊓ ρ₂.ker)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          (ρ₁ τ).trace = (ρ₂ τ).trace)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₁ σ).det = (ρ₂ σ).det := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_det_eq_of_trace_eq_of_exists_isFrobeniusAt_conj.solution
