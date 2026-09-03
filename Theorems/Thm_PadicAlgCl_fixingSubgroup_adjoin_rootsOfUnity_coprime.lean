import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime

set_option autoImplicit false

theorem PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime (p : ℕ) [Fact p.Prime] :
    (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}).fixingSubgroup
      = (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime.solution
