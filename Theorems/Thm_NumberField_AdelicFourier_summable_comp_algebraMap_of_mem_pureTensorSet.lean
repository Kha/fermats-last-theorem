import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet
    {F : Type*} [Field F] [NumberField F]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    Summable fun ξ : F => f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet.solution
