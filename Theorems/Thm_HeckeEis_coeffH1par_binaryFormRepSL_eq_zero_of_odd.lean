import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffH1par_binaryFormRepSL_eq_zero_of_odd (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (N n : ℕ) (hn : Odd n)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : x = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd.solution
