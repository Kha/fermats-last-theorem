import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import P2M.Util
namespace P2MW.S_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    ∃ W : Finset (Place k (modularFunctionFieldC k 1)),
      (∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) ∧
        nodePairsOfPlaces (arithFrobC q k 1) W = nodePairsOf q S₀ := by
  refine ⟨S₀.map ⟨charLGeomPlaceOfPoint k, charLGeomPlaceOfPoint_injective k⟩, ?_, ?_⟩
  · intro w
    rw [ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hS₀ a).mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hS₀ a).mpr ha, rfl⟩
  · exact ModularCurve.nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf q (arithFrobC q k 1)
      (fun a => ModularCurve.arithFrobC_smul_charLGeomPlaceOfPoint q a) S₀
