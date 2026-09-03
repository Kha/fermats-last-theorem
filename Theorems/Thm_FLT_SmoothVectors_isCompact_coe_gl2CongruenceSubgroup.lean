import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import P2M.Util
import P2M.Sol.S_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup

open FLT.SmoothVectors
theorem FLT.SmoothVectors.isCompact_coe_gl2CongruenceSubgroup
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCompact ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by p2m_exact_reverting @_root_.P2MW.S_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup.solution
