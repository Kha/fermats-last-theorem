module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.FieldTheory.Relrank
public import P2M.Util
public import P2M.Sol.S_ModularCurve_relfinrank_modularFunctionField

@[expose] public section

open ModularCurve
theorem ModularCurve.relfinrank_modularFunctionField (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionField N) = Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_relfinrank_modularFunctionField.solution
