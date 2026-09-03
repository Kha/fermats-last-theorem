import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_binaryFormRepSL_neg_one_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.binaryFormRepSL_neg_one_apply (K : Type*) [CommRing K] (n : ℕ) (P : ↥(HeckeEis.BinaryForm K n)) :
    HeckeEis.binaryFormRepSL K n (-1) P = ((-1 : K) ^ n) • P := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_binaryFormRepSL_neg_one_apply.solution
