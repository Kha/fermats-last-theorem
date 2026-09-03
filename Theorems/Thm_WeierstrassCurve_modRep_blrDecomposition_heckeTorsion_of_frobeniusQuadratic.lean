import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FreyPackage_MazurAttachmentApparatus
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four
attribute [-simp] WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
set_option autoImplicit false
open ModularCurve WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (W : WeierstrassCurve ℤ) (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    {M : ℕ} (hM : 0 < M) (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p))
    (hcong : FreyPackage.IdealGoodPrimeCurveCongruence p M W 𝔪)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) M p J)
    (hcont : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪))
    (hfin : Finite (heckeTorsion J 𝔪))
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    ∃ (n : ℕ) (e : heckeTorsion J 𝔪 ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → (Fin 2 → HeckeAlg ⧸ 𝔪))),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : heckeTorsion J 𝔪) (i : Fin n),
        e (mTorsionGaloisRep J 𝔪 σ w) i
          = (((((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom).comp
                (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p)) σ).map
              (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).mulVec (e w i) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic.solution
