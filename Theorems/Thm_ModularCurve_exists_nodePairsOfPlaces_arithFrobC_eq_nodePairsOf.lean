import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    ∃ W : Finset (Place k (modularFunctionFieldC k 1)),
      (∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) ∧
        nodePairsOfPlaces (arithFrobC q k 1) W = nodePairsOf q S₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf.solution
