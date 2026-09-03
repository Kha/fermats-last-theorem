import Mathlib
import Definitions.Def_HeckeCharacter_FiniteOrder
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_admitsModulus_of_continuous_of_isOfFinOrder
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center
attribute [-simp] AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain HeckeCharacter

theorem HeckeCharacter.exists_admitsModulus_of_continuous_of_isOfFinOrder
    (K : Type*) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hc : Continuous χ) (hfin : IsOfFinOrder χ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧ AdmitsModulus K χ 𝔣 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_admitsModulus_of_continuous_of_isOfFinOrder.solution
