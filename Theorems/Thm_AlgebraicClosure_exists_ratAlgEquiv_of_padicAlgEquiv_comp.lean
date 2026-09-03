import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_exists_ratAlgEquiv_of_padicAlgEquiv_comp

theorem AlgebraicClosure.exists_ratAlgEquiv_of_padicAlgEquiv_comp
    (p : ℕ) [Fact p.Prime]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p])
    (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) :
    ∃ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : AlgebraicClosure ℚ, σ (ι x) = ι (σ' x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_exists_ratAlgEquiv_of_padicAlgEquiv_comp.solution
