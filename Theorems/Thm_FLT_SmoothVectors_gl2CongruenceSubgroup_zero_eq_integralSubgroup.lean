import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import P2M.Util
import P2M.Sol.S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup

open FLT.SmoothVectors
theorem FLT.SmoothVectors.gl2CongruenceSubgroup_zero_eq_integralSubgroup
    (p : ℕ) [Fact p.Prime] :
    gl2CongruenceSubgroup p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by p2m_exact_reverting @_root_.P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.solution
