import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_intLattice_fg

theorem CuspForm.intLattice_fg (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.intLattice N k).FG := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_intLattice_fg.solution
