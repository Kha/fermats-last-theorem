import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice

theorem CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice {N : ℕ} {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) (h : ∀ f ∈ CuspForm.intLattice N k, t f = 0) : t = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.solution
