import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_existsEichlerShimuraMapLinear

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.existsEichlerShimuraMapLinear (n N : ℕ) [NeZero N] :
    ∃ ES : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), ES f = HeckeEis.eichlerShimuraMap n N f := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_existsEichlerShimuraMapLinear.solution
