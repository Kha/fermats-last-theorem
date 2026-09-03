import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_subsingleton_tate_integerUnits_of_unramified

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)] [IsCyclic (NumberField.PlaceDecomp.decomp E K w)]
    (hur : ∀ σ : NumberField.PlaceDecomp.decomp E K w,
      (∀ a : w.adicCompletionIntegers K, σ • a - a ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) → σ = 1) :
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateH0 ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateHneg1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_subsingleton_tate_integerUnits_of_unramified.solution
