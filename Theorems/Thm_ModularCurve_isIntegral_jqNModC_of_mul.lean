import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_jqNModC_of_mul

theorem ModularCurve.isIntegral_jqNModC_of_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hsymm : ModularCurve.EvalSymm data.Φ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K (d * ℓ) ∈ F) : IsIntegral F (ModularCurve.jqNModC K d) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_jqNModC_of_mul.solution
