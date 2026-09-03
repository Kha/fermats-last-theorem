import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_jqNModC_of_modularPolynomialFamily

open ModularCurve
theorem ModularCurve.isSeparable_jqNModC_of_modularPolynomialFamily (K : Type*) [Field K] (hΦ : ModularPolynomialFamily) (N : ℕ) [Fact N.Prime]
    (hNK : (N : K) ≠ 0) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_jqNModC_of_modularPolynomialFamily.solution
