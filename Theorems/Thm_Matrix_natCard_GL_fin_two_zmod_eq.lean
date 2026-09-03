import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_natCard_GL_fin_two_zmod_eq

set_option autoImplicit false

theorem Matrix.natCard_GL_fin_two_zmod_eq (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_natCard_GL_fin_two_zmod_eq.solution
