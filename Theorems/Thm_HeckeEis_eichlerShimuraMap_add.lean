import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_eichlerShimuraMap_add

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_add (n N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(f + g) = HeckeEis.eichlerShimuraMap n N f + HeckeEis.eichlerShimuraMap n N g := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_eichlerShimuraMap_add.solution
