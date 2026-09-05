import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_jqN_mem_modularFunctionField_sq
import Theorems.Thm_ModularCurve_full_sq_eq_adjoin
import Theorems.Thm_ModularCurve_relfinrank_full_sq
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionField
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq
import Mathlib.FieldTheory.Relrank
import P2M.Util
namespace P2MW.S_ModularCurve_functionFieldGeneration_sq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_functionFieldGeneration_sq.ModularCurve ModularCurve.PhiGen"
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem jqN_mem modularFunctionFieldFull modularFunctionField_le_full PhiIrreducible jqN_mem_modularFunctionField_sq full_sq_eq_adjoin relfinrank_full_sq relfinrank_modularFunctionField functionFieldGeneration_iff_full_eq exists_phiIrreducible_of_finrank_eq"
namespace W1
p2m_open "ModularCurve"

theorem modularFunctionField_sq_eq_full (p : ℕ) [hp : Fact (Nat.Prime p)] :
    modularFunctionField (p * p) = modularFunctionFieldFull (p * p) := by
  refine le_antisymm (modularFunctionField_le_full (p * p)) ?_
  rw [full_sq_eq_adjoin p, IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl | rfl)
  · exact jq_mem (p * p)
  · exact jqN_mem_modularFunctionField_sq p
  · exact jqN_mem (p * p)

end ModularCurve.W1

namespace ModularCurve p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem jqN_mem modularFunctionFieldFull modularFunctionField_le_full PhiIrreducible jqN_mem_modularFunctionField_sq full_sq_eq_adjoin relfinrank_full_sq relfinrank_modularFunctionField functionFieldGeneration_iff_full_eq exists_phiIrreducible_of_finrank_eq" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.finrank_adjoin_jqN_sq (p : ℕ) [hp : Fact (Nat.Prime p)] : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN (p * p)} : Set (LaurentSeries ℚ))) = dedekindPsi (p * p) := by
  rw [← relfinrank_modularFunctionField (p * p), modularFunctionField_sq_eq_full p]
  exact relfinrank_full_sq p

p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.functionFieldGeneration_sq (p : ℕ) [hp : Fact (Nat.Prime p)] : FunctionFieldGeneration (p * p) := by
  rw [functionFieldGeneration_iff_full_eq]
  exact (modularFunctionField_sq_eq_full p).symm

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.exists_phiIrreducible_sq (p : ℕ) [hp : Fact (Nat.Prime p)] : ∃ data : ModularPolynomialData (p * p), PhiIrreducible data :=
  exists_phiIrreducible_of_finrank_eq (p * p) (ModularCurve.finrank_adjoin_jqN_sq p)

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_functionFieldGeneration_sq.ModularCurve in

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] : FunctionFieldGeneration (p * p) :=
  ModularCurve.functionFieldGeneration_sq p

