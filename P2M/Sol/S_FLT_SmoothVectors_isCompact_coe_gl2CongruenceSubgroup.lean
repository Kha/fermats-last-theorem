import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Theorems.Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup
import P2M.Util
namespace P2MW.S_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup

open FLT.SmoothVectors

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCompact ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  refine IsCompact.of_isClosed_subset
    (FLT.SpectralSide.isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val)
    (Subgroup.isClosed_of_isOpen _ (isOpen_coe_gl2CongruenceSubgroup p n)) ?_
  exact fun g hg => gl2CongruenceSubgroup_le_integralSubgroup p n hg
