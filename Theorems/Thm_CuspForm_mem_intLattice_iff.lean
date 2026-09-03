import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_mem_intLattice_iff

theorem CuspForm.mem_intLattice_iff {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f ∈ CuspForm.intLattice N k ↔ ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_mem_intLattice_iff.solution
