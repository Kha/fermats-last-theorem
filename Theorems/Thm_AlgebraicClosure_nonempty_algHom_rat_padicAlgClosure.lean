import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure

theorem AlgebraicClosure.nonempty_algHom_rat_padicAlgClosure (p : ℕ) [Fact p.Prime] :
    Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure.solution
