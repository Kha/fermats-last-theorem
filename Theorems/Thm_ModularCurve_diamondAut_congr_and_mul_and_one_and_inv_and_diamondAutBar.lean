import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

theorem ModularCurve.diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar
    (N : ℕ) [NeZero N] :

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) = (d' : ZMod N)) →
      ModularCurve.diamondAut N d = ModularCurve.diamondAut N d') ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N →
      ∀ x : ↥(ModularCurve.x1FunctionField N),
        ModularCurve.diamondAut N (d * d') x = ModularCurve.diamondAut N d (ModularCurve.diamondAut N d' x)) ∧

    ModularCurve.diamondAut N 1 = AlgEquiv.refl ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      ∀ x : ↥(ModularCurve.x1FunctionField N),
        ModularCurve.diamondAut N d (ModularCurve.diamondAut N d' x) = x) ∧

    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) = (d' : ZMod N)) →
      ModularCurve.diamondAutBar N d = ModularCurve.diamondAutBar N d') ∧
    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N →
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar N),
        ModularCurve.diamondAutBar N (d * d') x = ModularCurve.diamondAutBar N d (ModularCurve.diamondAutBar N d' x)) ∧
    ModularCurve.diamondAutBar N 1 = AlgEquiv.refl ∧
    (∀ d d' : ℕ, d.Coprime N → d'.Coprime N → ((d : ZMod N) * (d' : ZMod N) = 1) →
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar N),
        ModularCurve.diamondAutBar N d (ModularCurve.diamondAutBar N d' x) = x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondAut_congr_and_mul_and_one_and_inv_and_diamondAutBar.solution
