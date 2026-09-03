import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqN_eq

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.finrank_adjoin_jqN_eq {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (h : PhiIrreducible data) : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqN_eq.solution
