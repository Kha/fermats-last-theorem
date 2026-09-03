import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S : Finset k) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q k) :
    ∃ (W : Finset (Place k (modularFunctionFieldC k 1))) (τ : ↥S ≃ ↥W),
      (∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) ∧
        ∀ a : ↥S, (τ a : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) = (a : k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq.solution
