import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_heckePic0Bar_cuspidalClass_self

open AlgebraicCurve ModularCurve
theorem ModularCurve.heckePic0Bar_cuspidalClass_self (p : ℕ) [NeZero p] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))] (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ) (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p p)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p p) hfin) (hdiv : heckeDivBar hα hβ (cuspidalDivisor p) = cuspidalDivisor p) : heckePic0Bar hα hβ hFI hfin hN (cuspidalClass p) = cuspidalClass p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckePic0Bar_cuspidalClass_self.solution
