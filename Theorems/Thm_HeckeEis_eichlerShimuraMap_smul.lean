import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_eichlerShimuraMap_smul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_smul (n N : ℕ) [NeZero N] (c : ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(c • f) = c • HeckeEis.eichlerShimuraMap n N f := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_eichlerShimuraMap_smul.solution
