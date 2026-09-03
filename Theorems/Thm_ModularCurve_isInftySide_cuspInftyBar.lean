import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_isInftySide_cuspInftyBar

open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.isInftySide_cuspInftyBar {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : P.IsInftySide (cuspInftyBar (1 * q)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isInftySide_cuspInftyBar.solution
