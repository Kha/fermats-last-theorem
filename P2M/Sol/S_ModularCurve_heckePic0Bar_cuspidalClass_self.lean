import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_heckePic0Bar_cuspidalClass_of_heckeDivBar
import P2M.Util
namespace P2MW.S_ModularCurve_heckePic0Bar_cuspidalClass_self

open AlgebraicCurve ModularCurve

noncomputable section

theorem solution (p : ℕ) [NeZero p] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))] (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ) (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p p)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) p p) hfin) (hdiv : heckeDivBar hα hβ (cuspidalDivisor p) = cuspidalDivisor p) : heckePic0Bar hα hβ hFI hfin hN (cuspidalClass p) = cuspidalClass p := by
  simpa using ModularCurve.heckePic0Bar_cuspidalClass_of_heckeDivBar p p hα hβ hFI hfin hN 1 (by simpa using hdiv)

end
