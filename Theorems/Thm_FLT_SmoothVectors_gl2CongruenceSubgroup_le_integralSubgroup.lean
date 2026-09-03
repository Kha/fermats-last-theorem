import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import P2M.Util
import P2M.Sol.S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup

open FLT.SmoothVectors
theorem FLT.SmoothVectors.gl2CongruenceSubgroup_le_integralSubgroup
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by p2m_exact_reverting @_root_.P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup.solution
