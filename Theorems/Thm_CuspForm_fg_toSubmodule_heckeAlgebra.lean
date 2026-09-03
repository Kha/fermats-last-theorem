import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_fg_toSubmodule_heckeAlgebra
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem CuspForm.fg_toSubmodule_heckeAlgebra (N : ℕ) [NeZero N] (S : Set ℕ) :
    (Subalgebra.toSubmodule (CuspForm.heckeAlgebra N 2 S)).FG := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_fg_toSubmodule_heckeAlgebra.solution
