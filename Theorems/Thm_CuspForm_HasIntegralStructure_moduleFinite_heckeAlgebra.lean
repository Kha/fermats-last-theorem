import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra

theorem CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) : Module.Finite ℤ (CuspForm.heckeAlgebra N k S) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.solution
