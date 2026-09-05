module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_phiIrreducible_of_finrank_eq

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.exists_phiIrreducible_of_finrank_eq (N : ℕ) [NeZero N] (h : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N) : ∃ data : ModularPolynomialData N, PhiIrreducible data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_phiIrreducible_of_finrank_eq.solution
