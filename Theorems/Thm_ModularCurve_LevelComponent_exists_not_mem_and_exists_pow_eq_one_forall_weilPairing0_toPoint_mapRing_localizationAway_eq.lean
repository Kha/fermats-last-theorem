import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_KatzLevelP
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂
attribute [-simp] Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelComponent.exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
    (A₀ : Type u) [CommRing A₀] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A₀))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (L₁ L₃ : ModularCurve.LevelComponent.{u} A₀)
    (B : Type u) [CommRing B] [Algebra A₀ B]
    (w : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw B)
    (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ f : B, f ∉ 𝔭 ∧ ∃ ε : Localization.Away f, ε ^ ℓ = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
        (letI x := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.mapRing
            (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) w;
         letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩;
          ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) :
            Ω)) = φ ε := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq.solution
