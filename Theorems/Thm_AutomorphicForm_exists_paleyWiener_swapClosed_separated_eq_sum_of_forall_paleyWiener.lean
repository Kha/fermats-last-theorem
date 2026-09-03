import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.whittakerCoefficient_zero LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (a b : ℝ)
      (n : ℕ) (μ₀ ν₀ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ₀ : ∀ j, IsUnitaryChar (𝓞 F) F (μ₀ j)) (_hν₀ : ∀ j, IsUnitaryChar (𝓞 F) F (ν₀ j))
      (_hμ₀ic : ∀ j, IsIdeleClassChar (𝓞 F) F (μ₀ j)) (_hν₀ic : ∀ j, IsIdeleClassChar (𝓞 F) F (ν₀ j))
      (_hμ₀c : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ₀ j x : ℂˣ) : ℂ))
      (_hν₀c : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν₀ j x : ℂˣ) : ℂ))
      (_hμ₀ν₀ : ∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ₀ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν₀ j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (ψf₀ : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf₀ : ∀ j s, IsInducedSection (𝓞 F) F (etaFst (μ₀ j) α hα s) (etaSnd (ν₀ j) α hα s) (ψf₀ j s))
      (_hψ₀jc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf₀ j p.1 p.2))
      (_hψ₀hol : ∀ j g, Differentiable ℂ (fun s => ψf₀ j s g))
      (_hψ₀K : ∀ j s, IsArchKFinite F (ψf₀ j s)) (_hψ₀sm : ∀ j s, IsKfSmooth F (ψf₀ j s))
      (_hψ₀Ku : ∀ (j : Fin n) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ j s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψ₀dec : ∀ (j : Fin n) (m₀ : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ m₀ * ‖ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₀ : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ₀ : ∀ j, AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ (ψ₀ j))
      (_hψ₀rep : ∀ (j : Fin n) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ₀ j g = (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψ₀band : ∀ (j : Fin n) (g : AdelicGL2 (𝓞 F) F), ψ₀ j g ≠ 0 →
        NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b),
    ∃ (ι : Type) (_ : Fintype ι) (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (r : ι → ι)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ e, IsUnitaryChar (𝓞 F) F (μ e)) ∧ (∀ e, IsUnitaryChar (𝓞 F) F (ν e)) ∧
      (∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) ∧ (∀ e, IsIdeleClassChar (𝓞 F) F (ν e)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ)) ∧
      (∀ (e : ι) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ e, μ (r e) = ν e ∧ ν (r e) = μ e) ∧
      (∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x) ∧
      (∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s)) ∧
      (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)) ∧
      (∀ e g, Differentiable ℂ (fun s => ψf e s g)) ∧
      (∀ e s, IsArchKFinite F (ψf e s)) ∧ (∀ e s, IsKfSmooth F (ψf e s)) ∧
      (∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
      (ψ = fun g => ∑ j, ψ₀ j g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener.solution
