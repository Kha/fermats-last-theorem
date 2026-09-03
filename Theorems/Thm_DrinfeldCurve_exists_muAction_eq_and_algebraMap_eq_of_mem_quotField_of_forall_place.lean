import Mathlib
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place

set_option autoImplicit false

p2m_open "DrinfeldCurve~algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField"

theorem DrinfeldCurve.exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra (GaloisField q 2) κ]
    [IsDomain (CoordRing q κ)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (z : drinfeldFunctionField q κ) (hzC : z ∈ DrinfeldCurve.quotField q κ C)
    (hz : ∀ v : AlgebraicCurve.Place κ (drinfeldFunctionField q κ),
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (x q κ) ∈ v.toValuationSubring →
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (y q κ) ∈ v.toValuationSubring →
      z ∈ v.toValuationSubring) :
    ∃ b : CoordRing q κ,
      (∀ ζ : ↥C, muAction q κ (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) b = b) ∧
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) b = z := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place.solution
