import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (N a : ℕ) (ha : 0 < a) (hap : a < p) (hpN : ¬ p ∣ N)
    (P : ↥(HeckeEis.BinaryForm K a))
    (hP : ∀ g : CongruenceSubgroup.Gamma0 N,
      (HeckeEis.binaryFormRepSL K a).comp (CongruenceSubgroup.Gamma0 N).subtype g P = P) :
    P = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_eq_zero_of_forall_binaryFormRepSL_gamma0_eq_self.solution
