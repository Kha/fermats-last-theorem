import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Theorems.Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup
import P2M.Util
namespace P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup

open FLT.SmoothVectors

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
  rw [← gl2CongruenceSubgroup_zero_eq_integralSubgroup p]
  exact gl2CongruenceSubgroup_antitone p (Nat.zero_le n)
