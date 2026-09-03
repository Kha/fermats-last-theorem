import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two
attribute [-simp] WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero
set_option autoImplicit false
open ModPForms

theorem WeierstrassCurve.exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k' : ℤ) (hk' : 2 ≤ k') (j : ℕ)
    (ψ : PowerSeries (AlgebraicClosure (ZMod p))) (mu : ℕ → AlgebraicClosure (ZMod p))
    (hψ : ψ ∈ modPMod N' k' (AlgebraicClosure (ZMod p))) (heig : IsModPEigen N' S₀ k' ψ mu)
    (hmu : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      mu ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p))) :
    ∃ (ψ' : PowerSeries (AlgebraicClosure (ZMod p))) (mu' : ℕ → AlgebraicClosure (ZMod p)),
      ψ' ∈ modPCusp N' k' (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k' ψ' mu' ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
          mu' ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible.solution
