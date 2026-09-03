import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm Polynomial
open NumberField.TateGlobal LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.Converse.not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (hent : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
      IsUnitaryChar (𝓞 K) K χ →
      ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        Differentiable ℂ Λ ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((if IsUnramifiedCharAt χ v.1
              then C 1 - C (((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
                + C ((((χ (uniformizerIdele K v.1)) ^ 2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
              else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_h₁ : IsIdeleClassChar (𝓞 K) K μ₁) (_h₂ : IsIdeleClassChar (𝓞 K) K μ₂)
    (_hc₁ : Continuous μ₁) (_hc₂ : Continuous μ₂) :
    ¬ Pi.AgreesAwayFromFinite (eisensteinTableOf K N hN μ₁ μ₂) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.solution
