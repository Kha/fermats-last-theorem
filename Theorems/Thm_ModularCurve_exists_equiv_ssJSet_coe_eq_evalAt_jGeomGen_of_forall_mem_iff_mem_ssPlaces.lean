import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
    (p : ℕ) (k : Type*) [Field k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k) :
    ∃ τ : ↥W ≃ ↥(ssJSet p k),
      ∀ w : ↥W, ((τ w : k)) = (w : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces.solution
