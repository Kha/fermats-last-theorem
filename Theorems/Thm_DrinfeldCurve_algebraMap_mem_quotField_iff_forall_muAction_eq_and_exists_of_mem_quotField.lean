import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField

set_option autoImplicit false
namespace DrinfeldCurve

theorem algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
    (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    (∀ b : CoordRing q k,
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) b ∈ quotField q k C ↔
        ∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) b = b) ∧
    (∀ z : drinfeldFunctionField q k, z ∈ quotField q k C →
      ∃ g h : CoordRing q k,
        (∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) g = g) ∧
        (∀ ζ : ↥C, muAction q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) h = h) ∧
        h ≠ 0 ∧ z * algebraMap (CoordRing q k) (drinfeldFunctionField q k) h =
          algebraMap (CoordRing q k) (drinfeldFunctionField q k) g) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField.solution

end DrinfeldCurve
