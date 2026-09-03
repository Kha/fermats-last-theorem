import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_exists_cycloChar_family

set_option autoImplicit false
theorem AlgebraicClosure.exists_cycloChar_family :
    ∃ cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ),
      ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
        μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_exists_cycloChar_family.solution
