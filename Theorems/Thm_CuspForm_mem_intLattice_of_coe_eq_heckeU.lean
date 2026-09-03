import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_mem_intLattice_of_coe_eq_heckeU

theorem CuspForm.mem_intLattice_of_coe_eq_heckeU {N : ℕ} {k : ℤ} {p : ℕ} (hp : p ≠ 0) {f g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : ⇑g = ModularForm.heckeU k p ⇑f) (hf : f ∈ CuspForm.intLattice N k) : g ∈ CuspForm.intLattice N k := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_mem_intLattice_of_coe_eq_heckeU.solution
