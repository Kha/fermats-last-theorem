import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero (n N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : m • x = 0) : x = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.solution
