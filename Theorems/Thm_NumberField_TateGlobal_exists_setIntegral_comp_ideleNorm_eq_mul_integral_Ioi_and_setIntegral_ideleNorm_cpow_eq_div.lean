import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
        (∀ g : ℝ → ℂ, Measurable g →
          (IntegrableOn (fun x => g (NumberField.TateGlobal.ideleNorm F x)) Ω ν ↔
              IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Set.Ioi (0 : ℝ))) ∧
          ∫ x in Ω, g (NumberField.TateGlobal.ideleNorm F x) ∂ν =
            C * ∫ r in Set.Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r) ∧
        (∀ w : ℂ, 0 < w.re →
          IntegrableOn (fun x => ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w)
              (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1}) ν ∧
          ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
              ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = C / w ∧
          IntegrableOn (fun x => ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w))
              (Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x}) ν ∧
          ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
              ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = C / w) ∧
        (∀ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ →
          AutomorphicForm.IsUnitaryChar (𝓞 F) F χ →
          Continuous (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) →
          ∀ w : ℂ, 0 < w.re →
            IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w)
                (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1}) ν ∧
            IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w))
                (Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x}) ν ∧
            ((∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ χ z ≠ 1) →
              ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
                  ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = 0 ∧
              ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
                  ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = 0) ∧
            ((∀ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 → χ z = 1) →
              ∃ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ ∧
                ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
                    ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν =
                  C / (w + (τ : ℂ) * Complex.I) ∧
                ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
                    ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν =
                  C / (w - (τ : ℂ) * Complex.I))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div.solution
