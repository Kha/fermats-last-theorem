import Mathlib
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two

theorem CuspForm.hasIntegralBasis_iff_hasIntegralStructure_two (N : ℕ) : CuspForm.HasIntegralBasis N ↔ CuspForm.HasIntegralStructure N 2 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two.solution
