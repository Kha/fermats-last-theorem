import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_linearIndependent_of_mem_intLattice

theorem CuspForm.linearIndependent_of_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ) (f : Fin n → CuspForm (CongruenceSubgroup.Gamma0 N) k) (hf : ∀ i, f i ∈ CuspForm.intLattice N k) (h : LinearIndependent ℤ f) : LinearIndependent ℂ f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_linearIndependent_of_mem_intLattice.solution
