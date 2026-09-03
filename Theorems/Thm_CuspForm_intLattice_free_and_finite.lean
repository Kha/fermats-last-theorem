import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_intLattice_free_and_finite

theorem CuspForm.intLattice_free_and_finite (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Free ℤ (CuspForm.intLattice N k) ∧ Module.Finite ℤ (CuspForm.intLattice N k) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_intLattice_free_and_finite.solution
