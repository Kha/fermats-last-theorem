import Definitions.Def_LocalNewvector_ConductorDatum
import P2M.Util
import P2M.Sol.S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1

theorem LocalNewvector.gl2CongruenceSubgroup_le_padicK1 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FLT.SmoothVectors.gl2CongruenceSubgroup p n ≤ LocalNewvector.padicK1 p n := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1.solution
