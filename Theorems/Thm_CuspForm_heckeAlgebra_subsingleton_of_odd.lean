import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_subsingleton_of_odd

set_option autoImplicit false

theorem CuspForm.heckeAlgebra.subsingleton_of_odd (N : ℕ) [NeZero N] (k : ℤ) (hk : Odd k)
    (S : Set ℕ) : Subsingleton (CuspForm.heckeAlgebra N k S) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_subsingleton_of_odd.solution
