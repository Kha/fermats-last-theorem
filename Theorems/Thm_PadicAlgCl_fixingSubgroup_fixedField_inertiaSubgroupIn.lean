import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn

set_option autoImplicit false

theorem PadicAlgCl.fixingSubgroup_fixedField_inertiaSubgroupIn (p : ℕ) [Fact p.Prime] :
    (IntermediateField.fixedField ((padicIntegers p).inertiaSubgroupIn ℚ_[p])).fixingSubgroup
      = (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn.solution
