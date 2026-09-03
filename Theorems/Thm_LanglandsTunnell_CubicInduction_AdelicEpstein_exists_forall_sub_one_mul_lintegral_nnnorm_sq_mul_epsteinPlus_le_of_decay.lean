import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)) [IsFiniteMeasure du]
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ : ℝ) (hR₀ : 0 ≤ R₀) (N : ℕ) (hN : 0 < N)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (hfin : ∀ x, Φ x ≠ 0 → ∀ (i : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (x i).2) w ∈ w.adicCompletionIntegers ℚ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : SlabL2.IsSlabDomain a b Φ₀)
    (hgm : Measurable (gauge3 ℚ))
    (Sg : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hS : ∀ᵐ x ∂(SlabL2.slabMeasure a b), ∃ γ : GL (Fin 3) ℚ, globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Sg)
    (hSfin : SlabL2.slabMeasure a b Sg < ⊤)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hdecay : ∀ K : ℕ, ∃ C : ℝ, ∀ g ∈ Sg, ‖φ g‖ * gauge3 ℚ g ^ K ≤ C) :
    ∃ C₂ : ℝ≥0∞, C₂ ≠ ⊤ ∧ ∀ σ ∈ Set.Ioc (1 : ℝ) 2,
      ENNReal.ofReal (σ - 1) *
          ∫⁻ g, (‖φ g‖₊ : ℝ≥0∞) ^ 2 * AdelicEpstein.epsteinPlus du Φ σ g ∂(SlabL2.domainMeasure a b Φ₀) ≤ C₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay.solution
