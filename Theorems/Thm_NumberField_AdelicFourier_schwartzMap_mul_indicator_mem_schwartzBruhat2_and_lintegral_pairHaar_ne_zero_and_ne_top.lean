import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

open scoped Classical in

theorem NumberField.AdelicFourier.schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
    (L : Type) [Field L] [NumberField L]
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (hg : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0) (hg0 : ∃ y, g y ≠ 0)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U) (hUn : U.Nonempty)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] :
    (fun x : Fin 2 → AdeleRing (𝓞 L) L =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)) ∈ schwartzBruhat2 L ∧
    (∀ x : Fin 2 → AdeleRing (𝓞 L) L,
      0 ≤ (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∧
      (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).im = 0) ∧
    (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top.solution
