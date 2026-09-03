import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂
attribute [-simp] Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.DrinfeldGlobal WeierstrassCurve.Affine

theorem ModularCurve.LevelModuliPackageAbs.weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow
    (A : Type) [CommRing A] (ℓ M' q : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) [NeZero M'] [Fact q.Prime]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (K : Type) [Field K] [Algebra A K] (ζ : A) (hζ : IsPrimitiveRoot (algebraMap A K ζ) ℓ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    (x₁ x₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw K)
    (hy₁ : (Quot.mk _ y₁ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt K) = x₁)
    (hy₂ : (Quot.mk _ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt K) = x₂) :
    letI z₁ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁
    letI z₂ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂
    letI _ : (z₁.curve).IsElliptic := ⟨z₁.isUnit_Δ⟩
    letI _ : (z₂.curve).IsElliptic := ⟨z₂.isUnit_Δ⟩
    ((weilPairing0 z₁.curve Ω (ℓ : ℤ)
        (toPoint ((z₁.curve).baseChange Ω) z₁.level.2.1.xP z₁.level.2.1.yP)
        (toPoint ((z₁.curve).baseChange Ω) z₁.level.2.1.xQ z₁.level.2.1.yQ) : Ωˣ) : Ω) =
      ((weilPairing0 z₂.curve Ω (ℓ : ℤ)
        (toPoint ((z₂.curve).baseChange Ω) z₂.level.2.1.xP z₂.level.2.1.yP)
        (toPoint ((z₂.curve).baseChange Ω) z₂.level.2.1.xQ z₂.level.2.1.yQ) : Ωˣ) : Ω) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow.solution
