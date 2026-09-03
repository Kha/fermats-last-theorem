import Mathlib
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField

set_option autoImplicit false

p2m_open "DrinfeldCurve~exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place"

theorem DrinfeldCurve.coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra (GaloisField q 2) κ]
    [IsDomain (CoordRing q κ)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (E : Type) [Field E] [Algebra κ E] (e : E ≃ₐ[κ] ↥(DrinfeldCurve.quotField q κ C)) (z : E)
    (hz : ∀ Q : AlgebraicCurve.Place κ E,
      (∀ (c : CoordRing q κ) (w : ↥(DrinfeldCurve.quotField q κ C)),
          (w : drinfeldFunctionField q κ) = algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) c →
          e.symm w ∈ Q.toValuationSubring) →
      z ∈ Q.toValuationSubring) :
    ((e z : ↥(DrinfeldCurve.quotField q κ C)) : drinfeldFunctionField q κ) ∈
      Set.range (algebraMap (CoordRing q κ) (drinfeldFunctionField q κ)) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField.solution
