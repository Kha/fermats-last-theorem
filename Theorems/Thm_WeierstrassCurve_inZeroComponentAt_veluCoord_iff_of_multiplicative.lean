import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p)
    (W' : WeierstrassCurve ℤ) (u : (AlgebraicClosure ℚ)ˣ)
    (hW' : (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
      (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) •
        (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
         Wb.veluQuotient (Wb.oddOrderSummingSet Q (p / 2))))
    {q : ℕ} (hq : q.Prime) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (hqΔ' : (q : ℤ) ∣ W'.Δ) (hqc₄' : ¬ (q : ℤ) ∣ W'.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hu : A.valuation (u : AlgebraicClosure ℚ) = 1)
    (x y : AlgebraicClosure ℚ)
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hL : (.some x y h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      ∉ AddSubgroup.zmultiples Q)
    (h' : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular
      (((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 2 *
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluX
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x)
      (((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 *
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluY
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) x y)) :
    W'.InZeroComponentAt A (.some _ _ h') ↔
      ∃ k ∈ AddSubgroup.zmultiples Q,
        W.InZeroComponentAt A
          ((.some x y h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) - k) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.solution
