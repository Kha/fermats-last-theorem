import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_mem_intLattice_of_mem_heckeAlgebra

theorem CuspForm.mem_intLattice_of_mem_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ} (hk : 1 ≤ k) {S : Set ℕ} {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)} (ht : t ∈ CuspForm.heckeAlgebra N k S) {f : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hf : f ∈ CuspForm.intLattice N k) : t f ∈ CuspForm.intLattice N k := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_mem_intLattice_of_mem_heckeAlgebra.solution
