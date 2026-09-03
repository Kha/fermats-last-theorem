import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_le_finrank_fixed_S_and_ST_binaryFormRepSL

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.le_finrank_fixed_S_and_ST_binaryFormRepSL (n : ℕ) (hn : Even n) :
    n + 1 - 2 * ((n + 2) / 4) ≤ Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n ModularGroup.S - 1)) ∧
    n + 1 - 2 * ((n + 2) / 3)
      ≤ Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.S * ModularGroup.T) - 1)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_le_finrank_fixed_S_and_ST_binaryFormRepSL.solution
