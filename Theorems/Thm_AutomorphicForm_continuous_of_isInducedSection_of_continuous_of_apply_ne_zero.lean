import Definitions.Def_AutomorphicForm_InducedSection
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_of_isInducedSection_of_continuous_of_apply_ne_zero
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.continuous_of_isInducedSection_of_continuous_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (_hφc : Continuous φ)
    (_hne : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0) :
    Continuous χ₁ ∧ Continuous χ₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_of_isInducedSection_of_continuous_of_apply_ne_zero.solution
