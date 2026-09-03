import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
namespace P2MW.S_ModularCurve_heckePic0Bar_cuspidalClass_of_heckeDivBar

open AlgebraicCurve ModularCurve

noncomputable section

theorem solution (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ) (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfin) (z : ℤ) (hdiv : heckeDivBar hα hβ (cuspidalDivisor N) = z • cuspidalDivisor N) : heckePic0Bar hα hβ hFI hfin hN (cuspidalClass N) = z • cuspidalClass N := by
  have hmk : ∀ (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)),
      Pic0.mk (z • D) = z • Pic0.mk D := fun D => map_zsmul (QuotientAddGroup.mk' _) z D
  rw [cuspidalClass_def, heckePic0Bar, Pic0.correspondence_mk, ← hmk]
  congr 1
  apply Subtype.ext
  rw [Pic0.coe_degZeroCorrespondence, coe_cuspidalDivisor₀]
  exact hdiv

end
