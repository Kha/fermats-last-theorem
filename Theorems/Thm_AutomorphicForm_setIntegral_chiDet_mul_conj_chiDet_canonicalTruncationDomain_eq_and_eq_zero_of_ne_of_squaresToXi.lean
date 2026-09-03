import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (χ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_hχ : SquaresToXi (𝓞 K) K ⊤ ξK χ) (_hχ' : SquaresToXi (𝓞 K) K ⊤ ξK χ')
    (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (_hχ'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ' z : ℂˣ) : ℂ))
    (_hχu : ∀ z, ‖((χ z : ℂˣ) : ℂ)‖ = 1) (_hχ'u : ∀ z, ‖((χ' z : ℂˣ) : ℂ)‖ = 1)
    (_hχt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1)
    (_hχ't : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ' z = 1) :
    (χ = χ' → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ)) ∧
    (χ ≠ χ' → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        chiDet (𝓞 K) K χ g * conj (chiDet (𝓞 K) K χ' g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setIntegral_chiDet_mul_conj_chiDet_canonicalTruncationDomain_eq_and_eq_zero_of_ne_of_squaresToXi.solution
