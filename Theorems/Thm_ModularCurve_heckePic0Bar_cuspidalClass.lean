import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_heckePic0Bar_cuspidalClass

open AlgebraicCurve ModularCurve
theorem ModularCurve.heckePic0Bar_cuspidalClass (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ) (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfin) (hdiv : heckeDivBar hα hβ (cuspidalDivisor N) = (1 + ℓ : ℤ) • cuspidalDivisor N) : heckePic0Bar hα hβ hFI hfin hN (cuspidalClass N) = (1 + ℓ : ℤ) • cuspidalClass N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckePic0Bar_cuspidalClass.solution
