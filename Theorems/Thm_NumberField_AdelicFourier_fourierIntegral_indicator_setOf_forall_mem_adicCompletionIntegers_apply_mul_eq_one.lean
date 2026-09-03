import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField NumberField.AdelicFourier IsDedekindDomain MeasureTheory

theorem NumberField.AdelicFourier.fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : Continuous ψ)
    (h0 : ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ z = 1)
    (h1 : ∃ z : v.adicCompletion F, ψ z ≠ 1) :
    IsOpen {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} ∧
    IsCompact {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} ∧
    ∀ w : v.adicCompletion F,
      fourierIntegral ψ μ
          ({y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1}.indicator
            fun _ => (1 : ℂ)) w =
        (μ.real {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} : ℂ) *
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one.solution
