import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles (N : ℕ) [NeZero N] (n : ℕ)
    (z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
      (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (_ : HeckeEis.IsEichlerIntegral n f F)
      (hF : HeckeEis.IsEquivariantPrimitiveWith
        ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F),
      (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) - hF.cocycle ∈
        HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles.solution
