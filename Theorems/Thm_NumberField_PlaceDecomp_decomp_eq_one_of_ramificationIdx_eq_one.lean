import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_decomp_eq_one_of_ramificationIdx_eq_one

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.decomp_eq_one_of_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    (hw : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (σ : NumberField.PlaceDecomp.decomp E K w)
    (hσ : ∀ a : w.adicCompletionIntegers K, σ • a - a ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) :
    σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_decomp_eq_one_of_ramificationIdx_eq_one.solution
